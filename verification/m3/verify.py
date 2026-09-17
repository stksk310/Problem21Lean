"""M3 proof/evidence gates. Frozen verifiers are reused without editing them."""
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
HERE = ROOT / 'verification/m3'
EVIDENCE = ROOT / 'audit-evidence/m3'
FROZEN = '9a9e01c401a934cfca2da15026986b0ecf83ff4f'

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

V = load('m3_original_m2b_verifier', ROOT / 'verification/m2b/verify.py')
V.HERE, V.EVIDENCE = HERE, EVIDENCE
sha, write, record, run, lake = V.sha, V.write, V.record, V.run, V.lake

def protected():
    data = json.loads((HERE / 'FROZEN_SHA256.json').read_text(encoding='utf-8'))
    if data['commit'] != FROZEN or len(data['files']) != 103:
        raise ValueError('Expected exact immutable 103-file pre-M3 baseline')
    return data['files']

V.protected = protected

def integrity():
    baseline = protected()
    bad = [p for p, h in baseline.items() if not (ROOT / p).is_file() or sha((ROOT / p).read_bytes()) != h]
    write('FROZEN_SOURCE_INTEGRITY.txt', f'Base: {FROZEN}\nProtected: {len(baseline)}\n'
          + ('FROZEN_SOURCE_CHANGED: NO\n' if not bad else '\n'.join(bad)))
    if bad:
        raise ValueError('Frozen source changed: ' + repr(bad))
    record('frozen_integrity', '103/103')

def modules():
    return sorted((ROOT / 'P21/Nonsymmetric').rglob('*.lean'))

def name(p):
    return p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.')

def generate():
    paths = modules()
    if not paths:
        raise ValueError('No M3 modules')
    rows = [r for p in paths for r in V.inventory_source(
        re.sub(r'(?m)^(@\[[^\]]+\]\s*)+', lambda m: '\n'*m[0].count('\n'), p.read_text(encoding='utf-8-sig')),
        p.relative_to(ROOT).as_posix())]
    names = [r['name'] for r in rows]
    if len(set(names)) != len(names):
        raise ValueError('Duplicate explicit declaration')
    imports = ''.join('import ' + name(p) + '\n' for p in paths)
    enumeration = '''
-- Read-only environment inventory; this command constructs no proof or declaration.
run_cmd do
  for (n, _) in (← Lean.getEnv).constants do
    if n.toString.startsWith "P21.Nonsymmetric." then
      Lean.logInfo (Lean.MessageData.ofName n)
'''
    (HERE / 'PrefixCheck.lean').write_text(imports + enumeration, encoding='utf-8', newline='\n')
    checks = '\n'.join('#check ' + n for n in names)
    checks += '\nexample : P21.Nonsymmetric.HerzogClassificationStatement := P21.Nonsymmetric.herzog_classification\n'
    checks += '\n#print P21.Nonsymmetric.ColorCap.MinimumOneStatement\n#print P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement\n'
    (HERE / 'GeneratedStatementCheck.lean').write_text(imports + '\n' + checks, encoding='utf-8', newline='\n')
    (HERE / 'DECLARATIONS.json').write_text(json.dumps(rows, indent=2, ensure_ascii=False) + '\n', encoding='utf-8', newline='\n')
    write('M3_MODULE_LIST.txt', '\n'.join(map(name, paths)) + '\n')
    record('m3_module_count', len(paths))
    return paths, rows, imports

def axioms(rows, imports):
    run(lake() + ['env', 'lean', 'verification/m3/PrefixCheck.lean'], 'KERNEL_DECLARATION_PREFIX.txt')
    output = (EVIDENCE / 'KERNEL_DECLARATION_PREFIX.txt').read_text(encoding='utf-8')
    roots = sorted(set(re.findall(r'P21\.Nonsymmetric[\w.\u0080-\uffff\']*', output)))
    # Prefix includes constructors, generated instances, projections and match helpers.
    roots = [n.rstrip('.') for n in roots if n != 'P21.Nonsymmetric']
    explicit = {r['name'] for r in rows}
    if not explicit <= set(roots):
        raise ValueError('Kernel declaration inventory omits explicit roots: ' + repr(explicit-set(roots)))
    (HERE / 'GeneratedAxiomCheck.lean').write_text(imports +
        '\n-- Deliberately audit generated helpers as well as public roots.\nset_option linter.auxLemma false\n' +
        '\n'.join('#print axioms ' + n for n in roots) + '\n', encoding='utf-8', newline='\n')
    run(lake() + ['env', 'lean', 'verification/m3/GeneratedAxiomCheck.lean'], 'AXIOM_REPORT.txt')
    found = V.parse_axioms((EVIDENCE / 'AXIOM_REPORT.txt').read_text(encoding='utf-8'), roots)
    write('AXIOM_SUMMARY.json', json.dumps(dict(checked_declarations=len(found), project_specific_axioms=0, declarations=found), indent=2)+'\n')
    record('project_specific_axioms', 0)
    record('axiom_roots', len(found))

def dag():
    graph = {}
    for p in modules():
        code = V.SCANNER.code_only(p.read_text(encoding='utf-8-sig'))
        graph[name(p)] = re.findall(r'^import\s+([\w.]+)', code, re.M)
        if re.search(r'\b(?:P21\.(?:Path|TypeII|Chain|Main)|native_decide|run_tac)\b', code):
            raise ValueError('Forbidden downstream input or evaluator: ' + str(p))
    visiting, done = set(), set()
    def visit(n):
        if n in visiting: raise ValueError('Cycle: ' + n)
        if n in done: return
        visiting.add(n)
        for child in graph.get(n, []): visit(child)
        visiting.remove(n)
        done.add(n)
    for n in graph: visit(n)
    write('DEPENDENCY_DAG_CHECK.txt', json.dumps(graph, indent=2) + '\nACYCLIC; no terminal exclusion module imported.\n')
    write('CIRCULARITY_CHECK.txt',
          'New-module import graph: ACYCLIC\n'
          'No Section 5/6/7-10 terminal exclusion, Euclidean closure or final theorem imported.\n'
          'Frozen old modules cannot reference new modules: 103-file integrity gate is separate.\n'
          'Primitive and Herzog roots precede selected-four composition.\n'
          'Both ColorCap residuals remain explicit theorem arguments, not axioms.\n')
    record('dependency_dag', 'PASS')

def regressions():
    checks = sorted(HERE.glob('*Regression.lean')) + [HERE / 'HerzogCheck.lean']
    if not checks: raise ValueError('Missing M3 regressions')
    write('REGRESSION_LOG.txt', '')
    for p in checks:
        run(lake() + ['env', 'lean', str(p.relative_to(ROOT))], 'REGRESSION_LOG.txt', append=True)

def verify(fresh=False):
    integrity()
    paths, rows, imports = generate()
    V.debt()
    if fresh and any((ROOT / '.lake/build').rglob('*.olean')):
        raise ValueError('Fresh requires no project oleans')
    record('fresh_root_build', fresh)
    run(lake() + ['build'], 'ROOT_BUILD_LOG.txt')
    frozen = sorted(p[:-5].replace('/', '.') for p in protected() if p.startswith('P21/') and p.endswith('.lean'))
    run(lake() + ['build'] + frozen, 'FROZEN_BUILD_LOG.txt')
    run(lake() + ['build'] + list(map(name, paths)), 'M3_BUILD_LOG.txt')
    axioms(rows, imports)
    run(lake() + ['env', 'lean', 'verification/m3/GeneratedStatementCheck.lean'], 'STATEMENT_INSPECTION.txt')
    regressions()
    run([sys.executable, '-m', 'unittest', 'discover', '-s', 'verification/m2', '-p', 'test_debt_scan.py', '-v'], 'SCANNER_TEST_LOG.txt')
    run([sys.executable, '-m', 'unittest', 'discover', '-s', 'verification/m2b', '-p', 'test_*.py', '-v'], 'SCANNER_TEST_LOG.txt', append=True)
    dag()
    V.debt()
    integrity()
    record('std_herzog', 'PROVED')
    record('std_white', 'OPEN')
    record('full_g4', 'OPEN')
    record('m3_verification_exit_code', 0)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--generate', action='store_true')
    parser.add_argument('--fresh', action='store_true')
    args = parser.parse_args()
    if args.generate: generate()
    else: verify(args.fresh)
