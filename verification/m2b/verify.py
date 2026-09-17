"""M2B local proof gates; never regenerates frozen M2 verification files."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / 'verification/m2b'
EVIDENCE = ROOT / 'audit-evidence/m2b'
FROZEN = 'a0ec51cf93326b6f8dbf22647cfeecf81a931bd8'
GLUE = 'P21.Symmetric.symmetric_three_generator_gluing'
FULL = 'P21.Symmetric.symmetric_tail_type_le_four'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


SCANNER = load_module('m2b_original_lexer', ROOT / 'verification/m2/debt_scan.py')
BANNED = SCANNER.FORBIDDEN | {'native_decide', 'run_tac'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, text):
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / name).write_text(text, encoding='utf-8', newline='\n')


def record(key, value):
    path = EVIDENCE / 'RESULTS.json'
    data = json.loads(path.read_text(encoding='utf-8')) if path.exists() else {}
    data[key] = value
    write('RESULTS.json', json.dumps(data, indent=2) + '\n')


def run(args, name, cwd=ROOT, append=False):
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    with (EVIDENCE / name).open('a' if append else 'w', encoding='utf-8') as out:
        out.write('$ ' + ' '.join(map(str, args)) + '\n')
        out.flush()
        proc = subprocess.Popen(list(map(str, args)), cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, encoding='utf-8', errors='strict')
        for line in proc.stdout:
            out.write(line)
            print(line, end='', flush=True)
        code = proc.wait()
        out.write(f'\nEXIT_CODE={code}\n')
    if code:
        raise RuntimeError(f'Exit {code}: {args}')
    return code


def lake(root=ROOT):
    return (['pwsh', '-NoProfile', '-File', str(root / 'verification/lake.ps1')]
            if os.name == 'nt' else ['lake'])


def protected():
    data = json.loads((HERE / 'FROZEN_SHA256.json').read_text(encoding='utf-8'))
    if data['commit'] != FROZEN or len(data['files']) != 57:
        raise ValueError('Expected immutable 57-file M2A baseline')
    return data['files']


def integrity():
    baseline = protected()
    failures = [p for p, digest in baseline.items()
                if not (ROOT / p).is_file() or sha((ROOT / p).read_bytes()) != digest]
    write('FROZEN_SOURCE_INTEGRITY.txt',
          f'Frozen commit: {FROZEN}\nProtected files: {len(baseline)}\n' +
          ('ALL PRE-M2B LEAN SOURCES BYTE-IDENTICAL\nFROZEN_SOURCE_CHANGED: NO\n'
           if not failures else 'FROZEN_SOURCE_CHANGED: YES\n' + '\n'.join(failures)))
    if failures:
        raise ValueError('Frozen source changed: ' + repr(failures))
    record('frozen_integrity', '57/57')


def lean_files():
    return [ROOT / 'P21.lean'] + sorted((ROOT / 'P21').rglob('*.lean')) + sorted(
        (ROOT / 'verification').rglob('*.lean'))


def new_modules():
    baseline = protected()
    return [p for p in sorted((ROOT / 'P21').rglob('*.lean'))
            if p.relative_to(ROOT).as_posix() not in baseline]


def module_name(path):
    return path.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.')


def inventory_source(source, filename):
    """Fail-closed inventory of explicit public declarations in new proof modules."""
    rows, scopes = [], []
    for number, line in enumerate(SCANNER.code_only(source).splitlines(), 1):
        line = line.strip()
        opening = re.fullmatch(r'(namespace|section)(?:\s+(\S+))?', line)
        if opening:
            scopes.append((opening[1], opening[2] or ''))
            continue
        if re.fullmatch(r'end(?:\s+\S+)?', line):
            if not scopes:
                raise ValueError(f'Unbalanced scope: {filename}:{number}')
            scopes.pop()
            continue
        if re.match(r'(private|protected|local)\s+(theorem|lemma|def|abbrev|structure|inductive)', line):
            raise ValueError(f'Unsupported declaration visibility: {filename}:{number}')
        match = re.match(r"(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|inductive)\s+([\w.'\u0080-\uffff]+)", line)
        if match:
            name = '.'.join([n for k, n in scopes if k == 'namespace'] + [match[2]])
            rows.append(dict(name=name, kind=match[1], file=filename, line=number))
    if scopes:
        raise ValueError('Unclosed scopes: ' + filename)
    return rows


def declarations(require_full=True):
    files = new_modules()
    if not files:
        raise ValueError('Empty new M2B module inventory')
    rows = [r for p in files for r in inventory_source(p.read_text(encoding='utf-8-sig'),
                                                      p.relative_to(ROOT).as_posix())]
    names = {r['name'] for r in rows}
    if len(names) != len(rows):
        raise ValueError('Duplicate declarations')
    ready = {GLUE, FULL} <= names
    record('full_success_theorems_present', ready)
    write('DECLARATIONS.json', json.dumps(rows, indent=2, ensure_ascii=False) + '\n')
    write('M2B_MODULE_LIST.txt', '\n'.join(map(module_name, files)) + '\n')
    if require_full and not ready:
        raise ValueError('Full-success gate missing: ' + repr({GLUE, FULL} - names))
    imports = ''.join('import ' + module_name(p) + '\n' for p in files)
    (HERE / 'GeneratedAxiomCheck.lean').write_text(imports + '\n' + '\n'.join(
        '#print axioms ' + r['name'] for r in rows) + '\n', encoding='utf-8', newline='\n')
    checks = '\n'.join('#check ' + r['name'] for r in rows)
    critical = ['SymmetricTail', 'SymmetricGlueData', 'SymmetricThreeGeneratorGluingStatement',
                'symmetric_tail_from_glue_data']
    checks += '\n' + '\n'.join('#print P21.Symmetric.' + n for n in critical)
    if ready:
        checks += '''
example : P21.Symmetric.SymmetricThreeGeneratorGluingStatement :=
  P21.Symmetric.symmetric_three_generator_gluing
example (g : P21.Generators) (s : g.Setting) (F : ℤ)
    (hF : s.semigroup.IsFrobenius F) (hcan : s.semigroup.Canonical F g.m)
    (hsym : P21.Symmetric.SymmetricTail g) : s.semigroup.type ≤ 4 :=
  P21.Symmetric.symmetric_tail_type_le_four g s F hF hcan hsym
'''
    (HERE / 'GeneratedStatementCheck.lean').write_text(
        imports + 'import P21.External.SymmetricThreeGenerator\nimport P21.Symmetric.Closure\n' + checks + '\n', encoding='utf-8', newline='\n')
    return files, rows


def debt():
    hits = []
    for p in lean_files():
        source = p.read_text(encoding='utf-8-sig')
        for match in re.finditer(r"[^\W\d][\w']*", SCANNER.code_only(source)):
            if match.group() in BANNED:
                hits.append(f'{p.relative_to(ROOT)}:{source[:match.start()].count(chr(10))+1}: {match.group()}')
    write('PROOF_DEBT_REPORT.txt', f'Project-owned Lean files: {len(lean_files())}\n'
          'Original frozen M2 lexer; comments/strings masked; ambiguous syntax fails closed.\n'
          'Forbidden: ' + ', '.join(sorted(BANNED)) + '\n' +
          f'FORBIDDEN CODE TOKENS: {len(hits)}\n' + '\n'.join(hits) + '\n')
    if hits:
        raise ValueError('Proof debt: ' + repr(hits))
    record('proof_debt_tokens', 0)


def parse_axioms(output, expected):
    if re.search(r'\berror:|\bwarning:|sorryAx', output):
        raise ValueError('Axiom output has warning/error/debt')
    found = {}
    for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output):
        deps = set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', m[2] or ''))
        if deps - ALLOWED or m[1] in found:
            raise ValueError('Unexpected axiom or duplicate root: ' + m[1])
        found[m[1]] = sorted(deps)
    if set(found) != set(expected):
        raise ValueError('Axiom coverage mismatch')
    return found


def dependency_check(rows):
    graph, sources = {}, {}
    for p in [ROOT / 'P21.lean'] + sorted((ROOT / 'P21').rglob('*.lean')):
        name = module_name(p)
        source = SCANNER.code_only(p.read_text(encoding='utf-8-sig'))
        sources[name] = source
        graph[name] = re.findall(r'^import\s+([\w.]+)', source, re.M)
    visiting, visited = set(), set()
    def walk(name):
        if name in visiting:
            raise ValueError('Import cycle: ' + name)
        if name in visited:
            return
        visiting.add(name)
        for child in graph.get(name, []):
            walk(child)
        visiting.remove(name)
        visited.add(name)
    for name in graph:
        walk(name)
    row = next(r for r in rows if r['name'] == GLUE)
    start = row['file'][:-5].replace('/', '.')
    ancestors = set()
    def collect(name):
        if name in ancestors:
            return
        ancestors.add(name)
        for child in graph.get(name, []):
            collect(child)
    collect(start)
    forbidden = {'symmetric_tail_from_glue_data', 'symmetric_tail_type_le_four', 'glue_data_symmetric_tail'}
    frozen_modules = {p[:-5].replace('/', '.') for p in protected() if p.endswith('.lean')}
    violations = [n for n in ancestors if n.endswith(('.FullClosure', '.Closure')) or
                  (n not in frozen_modules and any(re.search(r'\b' + x + r'\b', sources.get(n, ''))
                                                  for x in forbidden))]
    write('DEPENDENCY_DAG_CHECK.txt', json.dumps(graph, indent=2) + '\nIMPORT DAG: ACYCLIC\n')
    write('CIRCULARITY_CHECK.txt', 'Glue root module: ' + start + '\nTransitive imports:\n' +
          '\n'.join(sorted(ancestors)) + '\nForbidden reverse dependencies: ' + repr(violations) + '\n'
          'Conservative source/import check: no Closure/FullClosure import; every new source in\n'
          'the glue import closure excludes the three forbidden downstream/reverse theorem names.\n'
          'Frozen external module defines the reverse theorem, but no new proof references it.\n')
    if violations:
        raise ValueError('Circularity firewall: ' + repr(violations))
    record('circularity_check', 'PASS')


def scanner_tests():
    run([sys.executable, '-m', 'unittest', 'discover', '-s', 'verification/m2',
         '-p', 'test_debt_scan.py', '-v'], 'SCANNER_TEST_LOG.txt')
    run([sys.executable, '-m', 'unittest', 'discover', '-s', 'verification/m2b',
         '-p', 'test_*.py', '-v'], 'SCANNER_TEST_LOG.txt', append=True)
    record('scanner_tests_exit_code', 0)


def verify(prepare=False, fresh=False):
    integrity()
    files, rows = declarations(require_full=not prepare)
    debt()
    scanner_tests()
    if prepare:
        print('M2B preflight only; full theorem/build/axiom gates not claimed.')
        return
    if fresh and any((ROOT / '.lake/build').rglob('*.olean')):
        raise ValueError('Fresh build required: project .olean already exists')
    record('fresh_root_build', fresh)
    run(lake() + ['build'], 'ROOT_BUILD_LOG.txt')
    m2a = sorted(p[:-5].replace('/', '.') for p in protected()
                 if p.startswith(('P21/Symmetric/', 'P21/External/')) and p.endswith('.lean'))
    if len(m2a) != 16:
        raise ValueError('Expected exactly 16 frozen M2A modules')
    run(lake() + ['build'] + m2a, 'M2A_BUILD_LOG.txt')
    run(lake() + ['build'] + list(map(module_name, files)), 'M2B_BUILD_LOG.txt')
    run(lake() + ['env', 'lean', 'verification/m2b/GeneratedAxiomCheck.lean'], 'AXIOM_REPORT.txt')
    found = parse_axioms((EVIDENCE / 'AXIOM_REPORT.txt').read_text(encoding='utf-8'),
                         [r['name'] for r in rows])
    write('AXIOM_SUMMARY.json', json.dumps(dict(checked_declarations=len(found),
          project_specific_axioms=0, declarations=found), indent=2) + '\n')
    record('project_specific_axioms', 0)
    run(lake() + ['env', 'lean', 'verification/m2b/GeneratedStatementCheck.lean'], 'STATEMENT_INSPECTION.txt')
    regressions = sorted(HERE.glob('*Regression.lean'))
    if not regressions:
        raise ValueError('Missing M2B theorem regressions')
    for p in regressions:
        run(lake() + ['env', 'lean', str(p.relative_to(ROOT))], 'REGRESSION_LOG.txt', append=True)
    dependency_check(rows)
    debt()
    integrity()
    record('std_sym_glue', 'PROVED')
    record('full_s3', 'PROVED')
    record('m2b_verification_exit_code', 0)
    print('M2B local proof gates passed; independent TRUE AUDIT ruling remains external.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--prepare', action='store_true')
    parser.add_argument('--fresh', action='store_true')
    args = parser.parse_args()
    verify(args.prepare, args.fresh)

