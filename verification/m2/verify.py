"""Verify the M2 distribution without changing a frozen M1 source file."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from debt_scan import code_only, FORBIDDEN

def digest(data):
    return hashlib.sha256(data).hexdigest()

def run(args, path, append=False):
    with path.open('a' if append else 'w', encoding='utf-8') as out:
        out.write('$ ' + ' '.join(args) + '\n')
        out.flush()
        p = subprocess.Popen(args, cwd=ROOT, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, encoding='utf-8', errors='strict')
        for line in p.stdout:
            out.write(line)
            print(line, end='', flush=True)
        code = p.wait()
        out.write(f'\nEXIT_CODE={code}\n')
    if code:
        raise SystemExit(code)

def integrity():
    baseline = json.loads((HERE / 'M1_FROZEN_SHA256.json').read_text(encoding='utf-8'))
    failures = [p for p, h in baseline['files'].items()
                if digest((ROOT / p).read_bytes()) != h]
    report = ('ALL M1 PROTECTED FILES BYTE-IDENTICAL\n' if not failures else
              'M1 INTEGRITY FAILURE\n' + '\n'.join(failures) + '\n')
    report += f"Commit: {baseline['commit']}\nProtected files: {len(baseline['files'])}\n"
    report += 'M1_SOURCE_CHANGED: ' + ('YES' if failures else 'NO') + '\n'
    (ROOT / 'M1_FROZEN_INTEGRITY_REPORT.txt').write_text(report, encoding='utf-8')
    if failures:
        raise SystemExit(report)

def declarations():
    rows = []
    files = sorted((ROOT / 'P21/Symmetric').glob('*.lean'))
    files += sorted((ROOT / 'P21/External').glob('*.lean'))
    for p in files:
        stack = []
        for line_no, line in enumerate(p.read_text(encoding='utf-8').splitlines(), 1):
            ns = re.match(r'^namespace\s+(\S+)\s*$', line)
            if ns:
                stack.append(ns[1])
            elif re.match(r'^end(?:\s+\S+)?\s*$', line):
                if not stack:
                    raise ValueError(f'Unbalanced namespace: {p}:{line_no}')
                stack.pop()
            match = re.match(r'^(?:noncomputable\s+)?(theorem|def|abbrev|structure)\s+(\S+)', line)
            if match:
                rows.append(dict(name='.'.join(stack + [match[2]]), kind=match[1],
                                 file=p.relative_to(ROOT).as_posix(), line=line_no))
        if stack:
            raise ValueError('Unclosed namespaces: ' + str(p))
    if len({r['name'] for r in rows}) != len(rows):
        raise ValueError('Duplicate inventory declaration')
    (HERE / 'DECLARATIONS.json').write_text(json.dumps(rows, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
    inspect = [r for r in rows if r['kind'] != 'structure']
    imports = ''.join('import ' + p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.') + '\n' for p in files)
    (ROOT / 'verification/M2AxiomCheck.lean').write_text(imports + '\n' +
        '\n'.join('#print axioms ' + r['name'] for r in inspect)+'\n', encoding='utf-8')
    (ROOT / 'verification/M2StatementCheck.lean').write_text(imports + '\n' +
        '\n'.join('#check ' + r['name'] for r in rows) +
        '\n#print P21.Symmetric.SymmetricGlueData\n#print P21.Symmetric.SymmetricTail\n'
        '#print P21.Symmetric.SymmetricThreeGeneratorGluingStatement\n'
        '#check P21.Symmetric.symmetric_tail_from_glue_data\n', encoding='utf-8')
    return files, inspect

def debt():
    files = [ROOT / 'P21.lean'] + sorted((ROOT / 'P21').rglob('*.lean'))
    files += sorted((ROOT / 'verification').rglob('*.lean'))
    hits = []
    for p in files:
        source = p.read_text(encoding='utf-8-sig')
        masked = code_only(source)
        for m in re.finditer(r"[^\W\d][\w']*", masked):
            if m.group() in FORBIDDEN:
                hits.append(f'{p.relative_to(ROOT)}:{source[:m.start()].count(chr(10))+1}: {m.group()}')
    report = f'Project-owned Lean files scanned: {len(files)}\n'
    report += 'Method: lexical code scan; nested comments and ordinary/raw strings masked.\n'
    report += 'Ambiguous character/quotation/interpolation syntax fails closed.\n'
    report += 'Forbidden tokens: ' + ', '.join(sorted(FORBIDDEN)) + '\n'
    report += f'Forbidden code tokens: {len(hits)}\n' + '\n'.join(hits)
    (ROOT / 'PROOF_DEBT_REPORT.txt').write_text(report+'\n', encoding='utf-8')
    if hits:
        raise SystemExit(report)

def main():
    integrity()
    files, inspect = declarations()
    if '--prepare' in sys.argv:
        debt()
        print(f'Prepared {len(files)} M2 modules, {len(inspect)} axiom inspection roots.')
        return
    lake = (['pwsh', '-NoProfile', '-File', str(ROOT / 'verification/lake.ps1')]
            if os.name == 'nt' else ['lake'])
    run(lake+['build'], ROOT/'BUILD_LOG.txt')
    targets = [p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.') for p in files]
    run(lake+['build']+targets, ROOT/'BUILD_LOG.txt', append=True)
    run(lake+['env','lean','verification/M2StatementCheck.lean'], HERE/'STATEMENTS.txt')
    run(lake+['env','lean','verification/M2AxiomCheck.lean'], ROOT/'AXIOM_REPORT.txt')
    text = (ROOT/'AXIOM_REPORT.txt').read_text(encoding='utf-8')
    found = {}
    allowed = {'propext','Classical.choice','Quot.sound'}
    for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
        deps = set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', m[2] or ''))
        if deps - allowed:
            raise ValueError(f'Unexpected axioms: {m[1]} {deps-allowed}')
        found[m[1]] = sorted(deps)
    if set(found) != {r['name'] for r in inspect}:
        raise ValueError('Axiom coverage mismatch')
    if re.search(r'\berror:|\bwarning:|sorryAx', text):
        raise ValueError('Axiom report has a warning, error, or proof debt')
    (HERE/'AXIOM_SUMMARY.json').write_text(json.dumps(dict(checked_declarations=len(found),
        project_specific_axioms=0, standard_axioms_observed=sorted(set().union(*map(set,found.values()))),
        declarations=found),indent=2)+'\n',encoding='utf-8')
    tests = sorted(HERE.glob('*Regression.lean')) + [ROOT/'verification/M2BranchICheck.lean']
    for i, test in enumerate(tests):
        run(lake+['env','lean',test.relative_to(ROOT).as_posix()], HERE/'REGRESSION_LOG.txt',append=i>0)
    debt()
    integrity()
    print('M2 checks completed; this is not an independent audit ruling.')

if __name__ == '__main__':
    main()
