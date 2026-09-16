"""External reproducibility gates for the exact M2A candidate; stdlib only."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'audit-evidence/m2a'
ARCHIVE = ROOT / 'ci/candidate/P21_LEAN_M2A_INTERNAL_SYMMETRIC_CLOSURE_CANDIDATE_20260917.zip'
ZIP_SHA = '7bab9f713b64411e6d79b2dcd42ed15fc5d27b3a9a8307da0ce93bfa7e1bd665'
FROZEN = '9464b9cd3b6b070f9fa6d1c212f27065d1eb84b3'
M1 = ['P21.lean', 'P21/Factorization.lean', 'P21/NumericalSemigroup.lean',
      'P21/Basic.lean', 'P21/PseudoFrobenius.lean', 'P21/Apery.lean',
      'P21/CanonicalReduction.lean', 'P21/Tail.lean', 'P21/Selection.lean',
      'P21/Semantics.lean', 'lean-toolchain', 'lake-manifest.json', 'lakefile.toml']
REQUIRED = ['BUILD_ROOT_LOG.txt', 'BUILD_M2_MODULES_LOG.txt', 'M2_MODULE_LIST.txt',
            'ENVIRONMENT.txt', 'DEPENDENCY_STATE.txt', 'M1_FROZEN_INTEGRITY_REPORT_CI.txt',
            'M1_FROZEN_SHA256.txt', 'M2_SOURCE_INTEGRITY_REPORT.txt',
            'SOURCE_SHA256_CANDIDATE.txt', 'SOURCE_SHA256_GITHUB.txt',
            'PROOF_DEBT_REPORT_CI.txt', 'PROOF_DEBT_TEST_LOG.txt',
            'AXIOM_REPORT_M2_CI.txt', 'AXIOM_SUMMARY_M2_CI.json',
            'M2_STATEMENT_INSPECTION.txt', 'M2_SCOPE_REPORT.txt',
            'VERIFICATION_M2_LOG.txt', 'COMMIT_SHA.txt', 'RUN_CONTEXT.json']


def sha(data):
    return hashlib.sha256(data).hexdigest()


def write(name, value):
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    (EVIDENCE / name).write_text(value, encoding='utf-8', newline='\n')


def git_bytes(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def tracked():
    return git_bytes('ls-files', '-z').decode().rstrip('\0').split('\0')


def record(key, value):
    p = EVIDENCE / 'RESULTS.json'
    results = json.loads(p.read_text(encoding='utf-8')) if p.exists() else {}
    results[key] = value
    write('RESULTS.json', json.dumps(results, indent=2) + '\n')


def run(args, name, cwd=ROOT, append=False):
    log = EVIDENCE / name
    with log.open('a' if append else 'w', encoding='utf-8') as out:
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


def baseline():
    if sha(ARCHIVE.read_bytes()) != ZIP_SHA:
        raise ValueError('INPUT HASH MISMATCH')
    with zipfile.ZipFile(ARCHIVE) as z:
        if z.testzip() is not None:
            raise ValueError('ZIP CRC failure')
        prefix = ARCHIVE.stem + '/'
        data = {}
        for name in z.namelist():
            rel = name.removeprefix(prefix)
            if not name.startswith(prefix) or not rel or '..' in Path(rel).parts or Path(rel).is_absolute():
                raise ValueError('Invalid candidate path: ' + name)
            if rel in data:
                raise ValueError('Duplicate ZIP entry: ' + rel)
            data[rel] = z.read(name)
    manifest = json.loads(data['MANIFEST_SHA256.json'])['files']
    if set(manifest) != set(data) - {'MANIFEST_SHA256.json'}:
        raise ValueError('Manifest coverage mismatch')
    for name, digest in manifest.items():
        if sha(data[name]) != digest:
            raise ValueError('Manifest mismatch: ' + name)
    return data


def compare_sources(data, root, names):
    failures = []
    for p, original in sorted(data.items()):
        current = (root / p).read_bytes() if (root / p).is_file() else None
        valid = current == original
        if p == 'README.md':
            valid = current is not None and current.startswith(original)
        if not valid:
            failures.append(p)
    if {p for p in names if p.endswith('.lean')} != {p for p in data if p.endswith('.lean')}:
        failures.append('Unexpected added/missing project-owned Lean file')
    for p in names:
        if '.lake' in Path(p).parts or p.endswith(('.olean', '.ilean', '.o', '.a', '.so')):
            failures.append('Compiled project artifact tracked: ' + p)
    return failures


def module_names(data, frozen_paths):
    return sorted(p[:-5].replace('/', '.') for p in data
                  if p.startswith('P21/') and p.endswith('.lean') and p not in frozen_paths)


def init():
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    for name in REQUIRED:
        write(name, 'NOT RUN\n')
    write('RESULTS.json', '{}\n')
    head = git_bytes('rev-parse', 'HEAD').decode().strip()
    if os.environ.get('GITHUB_SHA', head) != head:
        raise ValueError('Checkout differs from event SHA')
    write('COMMIT_SHA.txt', head + '\n')
    context = {key: os.environ.get(key) for key in ['GITHUB_REPOSITORY', 'GITHUB_REF',
               'GITHUB_SHA', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_WORKFLOW',
               'RUNNER_OS', 'RUNNER_ARCH', 'RUNNER_NAME']}
    write('RUN_CONTEXT.json', json.dumps(context, indent=2) + '\n')


def integrity():
    data = baseline()
    failures = compare_sources(data, ROOT, tracked())
    frozen_hashes = []
    frozen_failures = []
    candidate_baseline = json.loads(data['verification/m2/M1_FROZEN_SHA256.json'])
    if set(candidate_baseline['files']) != set(M1) or candidate_baseline['commit'] != FROZEN:
        raise ValueError('Incorrect candidate M1 baseline')
    for p in M1:
        original = git_bytes('show', FROZEN + ':' + p)
        frozen_hashes.append(f'{sha(original)}  {p}\n')
        if original != data[p] or original != (ROOT / p).read_bytes() or sha(original) != candidate_baseline['files'][p]:
            frozen_failures.append(p)
    # Git blobs independently prove the candidate is actually committed, not only on disk.
    for p, original in data.items():
        committed = git_bytes('show', 'HEAD:' + p)
        valid = committed == original if p != 'README.md' else committed.startswith(original)
        if not valid:
            failures.append('Git blob differs: ' + p)
    protected = {p: b for p, b in data.items() if p != 'README.md'}
    write('SOURCE_SHA256_CANDIDATE.txt', ''.join(f'{sha(b)}  {p}\n' for p, b in sorted(protected.items())))
    write('SOURCE_SHA256_GITHUB.txt', ''.join(f'{sha((ROOT/p).read_bytes())}  {p}\n' for p in sorted(protected)))
    write('M1_FROZEN_SHA256.txt', ''.join(sorted(frozen_hashes)))
    write('M1_FROZEN_INTEGRITY_REPORT_CI.txt', f'Frozen commit: {FROZEN}\n'
          f'M1 PROTECTED FILES: {len(M1)-len(frozen_failures)} / {len(M1)} BYTE-IDENTICAL\n'
          + '\n'.join(frozen_failures) + '\n')
    write('M2_SOURCE_INTEGRITY_REPORT.txt', f'Candidate SHA256: {ZIP_SHA}\n'
          f'ZIP entries: {len(data)}\nCompared files excluding append-only README: {len(protected)}\n'
          'All candidate documents, scripts, source and metadata compared; CI additions excluded.\n'
          + ('M2 IMPLEMENTATION FILES IDENTICAL TO CANDIDATE\nSOURCE_CHANGED: NO\n' if not failures else
             'SOURCE_CHANGED: YES\n' + '\n'.join(failures) + '\n'))
    if failures or frozen_failures:
        raise ValueError('Source integrity failed: ' + repr(failures + frozen_failures))
    record('m1_integrity', f'{len(M1)}/{len(M1)}')
    record('source_changed', False)
    print('M1 13/13 and all candidate files identical; SOURCE_CHANGED: NO')


def environment():
    for i, args in enumerate([['uname', '-a'], ['elan', '--version'], ['lean', '--version'],
                              ['lake', '--version'], ['git', '--version'], [sys.executable, '--version']]):
        run(args, 'ENVIRONMENT.txt', append=i > 0)
    with (EVIDENCE / 'ENVIRONMENT.txt').open('a', encoding='utf-8') as out:
        out.write('\nlean-toolchain:\n' + (ROOT / 'lean-toolchain').read_text(encoding='utf-8'))
        out.write('\nlake-manifest.json:\n' + (ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))


def cache_modules():
    imports = set()
    for p, data in baseline().items():
        if p.endswith('.lean'):
            imports.update(re.findall(r'^import (Mathlib\.[\w.]+)', data.decode('utf-8-sig'), re.M))
    print('\n'.join(sorted(imports)))


def dependencies():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8-sig'))
    report = []
    for package in manifest['packages']:
        path = ROOT / manifest['packagesDir'] / package['name']
        actual = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
        if actual != package['rev'] or dirty:
            raise ValueError('Dependency revision/source differs: ' + package['name'])
        report.append(f'{package["name"]} {actual} {package["url"]}')
    write('DEPENDENCY_STATE.txt', '\n'.join(report) + '\nALL PINNED REVISIONS MATCH\n')
    record('pinned_dependencies', len(report))


def build_root():
    if list((ROOT / '.lake/build').rglob('*.olean')):
        raise ValueError('Project compiled cache exists before root build')
    write('PROJECT_CACHE_STATE.txt', 'No project .olean before mandatory root build.\nNo project cache restored.\n')
    record('root_build_exit_code', run(['lake', 'build'], 'BUILD_ROOT_LOG.txt'))


def build_m2():
    modules = module_names(baseline(), M1)
    if not modules:
        raise ValueError('No M2 modules')
    write('M2_MODULE_LIST.txt', f'M2 MODULE FILE COUNT: {len(modules)}\n' + '\n'.join(modules)
          + '\nEXPLICIT BUILD COMMAND: lake build ' + ' '.join(modules) + '\n')
    record('m2_explicit_build_exit_code', run(['lake', 'build', *modules], 'BUILD_M2_MODULES_LOG.txt'))
    record('m2_module_count', len(modules))
    record('m2_modules', modules)


def candidate_module(filename):
    spec = importlib.util.spec_from_file_location('candidate_' + filename, ROOT / 'verification/m2' / (filename + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def debt():
    scanner = candidate_module('debt_scan')
    banned = scanner.FORBIDDEN | {'native_decide', 'run_tac'}
    files = [p for p in tracked() if p.endswith('.lean')]
    hits = []
    for p in files:
        source = (ROOT / p).read_text(encoding='utf-8-sig')
        for m in re.finditer(r"[^\W\d][\w']*", scanner.code_only(source)):
            if m.group() in banned:
                hits.append(f'{p}:{source[:m.start()].count(chr(10))+1}: {m.group()}')
    write('PROOF_DEBT_REPORT_CI.txt', f'Project-owned Lean files: {len(files)}\n'
          'Original candidate lexer; nested comments and strings masked; ambiguous syntax fails closed.\n'
          f'Forbidden tokens: {", ".join(sorted(banned))}\nFORBIDDEN CODE TOKENS: {len(hits)}\n'
          + '\n'.join(hits) + '\n')
    if hits:
        raise ValueError('Forbidden Lean code tokens')
    record('proof_debt_tokens', len(hits))


def scanner_tests():
    run([sys.executable, '-m', 'unittest', 'discover', '-s', 'verification/m2',
         '-p', 'test_debt_scan.py', '-v'], 'PROOF_DEBT_TEST_LOG.txt')
    run([sys.executable, '-m', 'unittest', 'discover', '-s', 'ci',
         '-p', 'test_m2a_audit.py', '-v'], 'CI_GATE_TEST_LOG.txt')
    record('scanner_tests_exit_code', 0)


def parse_axioms(output, expected):
    if re.search(r'\berror:|\bwarning:|sorryAx', output):
        raise ValueError('Axiom output has errors/warnings/debt')
    found = {}
    for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", output):
        deps = set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*', m[2] or ''))
        if deps - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError('Project-specific axiom: ' + m[1])
        if m[1] in found:
            raise ValueError('Duplicate axiom root: ' + m[1])
        found[m[1]] = sorted(deps)
    if set(found) != expected:
        raise ValueError('Axiom coverage mismatch')
    return found


def axioms():
    inventory = json.loads(baseline()['verification/m2/DECLARATIONS.json'])
    expected = {r['name'] for r in inventory if r['kind'] != 'structure'}
    run(['lake', 'env', 'lean', 'verification/M2AxiomCheck.lean'], 'AXIOM_REPORT_M2_CI.txt')
    found = parse_axioms((EVIDENCE / 'AXIOM_REPORT_M2_CI.txt').read_text(encoding='utf-8'), expected)
    summary = dict(checked_declarations=len(found), new_m2_theorems=sum(r['kind']=='theorem' for r in inventory),
                   project_specific_axioms=0, declarations=found)
    write('AXIOM_SUMMARY_M2_CI.json', json.dumps(summary, indent=2) + '\n')
    record('axiom_roots', len(found))
    record('new_m2_theorems', summary['new_m2_theorems'])
    record('project_specific_axioms', 0)


def suite():
    data = baseline()
    with tempfile.TemporaryDirectory(prefix='p21-m2a-suite-') as tmp:
        scratch = Path(tmp)
        for p, b in data.items():
            dest = scratch / p
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(b)
        (scratch / '.lake').mkdir()
        (scratch / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(), target_is_directory=True)
        # Only dependency packages are shared. The original verifier builds this project afresh.
        run([sys.executable, 'verification/m2/verify.py'], 'VERIFICATION_M2_LOG.txt', cwd=scratch)
        for p, b in data.items():
            if p.startswith('P21/') and p.endswith('.lean') and (scratch / p).read_bytes() != b:
                raise ValueError('Verifier changed mathematical source: ' + p)
        if json.loads((scratch / 'verification/m2/DECLARATIONS.json').read_text(encoding='utf-8')) != json.loads(data['verification/m2/DECLARATIONS.json']):
            raise ValueError('Regenerated declaration inventory differs')
        # Reports/checker files can be regenerated by the original program only in scratch.
        for p in ['BUILD_LOG.txt', 'AXIOM_REPORT.txt', 'PROOF_DEBT_REPORT.txt',
                  'M1_FROZEN_INTEGRITY_REPORT.txt', 'verification/m2/STATEMENTS.txt',
                  'verification/m2/AXIOM_SUMMARY.json', 'verification/m2/REGRESSION_LOG.txt']:
            (EVIDENCE / ('ORIGINAL_SUITE_' + Path(p).name)).write_bytes((scratch / p).read_bytes())
    record('original_verification_suite_exit_code', 0)


def scope():
    data = baseline()
    scanner = candidate_module('debt_scan')
    external = scanner.code_only(data['P21/External/SymmetricThreeGenerator.lean'].decode())
    closure = scanner.code_only(data['P21/Symmetric/Closure.lean'].decode())
    branch = scanner.code_only(data['P21/Symmetric/BranchI.lean'].decode())
    if not re.search(r'def\s+SymmetricThreeGeneratorGluingStatement\s*:\s*Prop\s*:=', external):
        raise ValueError('External obligation is not an open Prop definition')
    occurrences = []
    for p, b in data.items():
        if p.startswith('P21/') and p.endswith('.lean'):
            for line in scanner.code_only(b.decode('utf-8-sig')).splitlines():
                if 'SymmetricThreeGeneratorGluingStatement' in line:
                    occurrences.append((p, line.strip()))
            if re.search(r'\b(?:theorem|def|abbrev)\s+symmetric_tail_type_le_four\b', scanner.code_only(b.decode())):
                raise ValueError('Unexpected full S3 alias')
    if len(occurrences) != 1 or 'SymmetricGlueData g' not in closure:
        raise ValueError('External proposition consumed or final theorem scope changed')
    lower = branch.split('theorem later_return_lower', 1)[1].split(':= by', 1)[0]
    if '(hn : 1 < n)' not in lower or 'theorem first_return_exception' not in branch:
        raise ValueError('N=1 firewall missing')
    run(['lake', 'env', 'lean', 'verification/M2StatementCheck.lean'], 'M2_STATEMENT_INSPECTION.txt')
    names = ['P21.Symmetric.symmetric_tail_from_glue_data',
             'P21.Symmetric.SymmetricGlueData', 'P21.Symmetric.SymmetricThreeGeneratorGluingStatement',
             'P21.Symmetric.BranchIData.later_return_lower', 'P21.Symmetric.BranchIData.first_return_exception',
             'P21.Symmetric.BranchIRealization.impossible', 'P21.Symmetric.Raw4Data.branchII_excluded']
    report = ('Final theorem requires explicit SymmetricGlueData.\n'
              'External obligation: one definition occurrence in project implementation, no proof dependency.\n'
              'Full symmetric-to-glue theorem/alias absent in the byte-identical source-audited candidate.\n'
              'N=1 PREDECESSOR FIREWALL: PRESENT\n'
              'later_return_lower statement requires (hn : 1 < n).\n'
              'Original verifier builds first-return regression in verification/M2BranchICheck.lean.\n'
              'Actual/signed firewall: all M1 implementations are independently Git-byte-identical.\n'
              'STD_SYM_GLUE: OPEN\nFULL S3: OPEN\nCritical inspected names:\n' + '\n'.join(names) + '\n')
    statements = (EVIDENCE / 'M2_STATEMENT_INSPECTION.txt').read_text(encoding='utf-8')
    if any(name not in statements for name in names):
        raise ValueError('Critical declaration absent from Lean statement output')
    write('M2_SCOPE_REPORT.txt', report)
    record('scope_check', 'PASS')
    record('std_sym_glue', 'OPEN')
    record('full_s3', 'OPEN')


def complete():
    for name in REQUIRED:
        if not (EVIDENCE / name).is_file() or (EVIDENCE / name).read_text(encoding='utf-8').startswith('NOT RUN'):
            raise ValueError('Missing evidence: ' + name)
    results = json.loads((EVIDENCE / 'RESULTS.json').read_text(encoding='utf-8'))
    expected = dict(root_build_exit_code=0, m2_explicit_build_exit_code=0,
                    scanner_tests_exit_code=0, original_verification_suite_exit_code=0,
                    source_changed=False, m1_integrity='13/13', proof_debt_tokens=0,
                    project_specific_axioms=0, scope_check='PASS', std_sym_glue='OPEN', full_s3='OPEN')
    for key, value in expected.items():
        if key not in results or results[key] != value:
            raise ValueError('Incomplete gate: ' + key)
    if results.get('m2_module_count', 0) == 0 or results.get('axiom_roots', 0) == 0:
        raise ValueError('Empty module/axiom coverage')
    record('status', 'M2A CI REPRODUCIBILITY EVIDENCE READY FOR TRUE AUDIT')
    hashes = {p.name: sha(p.read_bytes()) for p in EVIDENCE.iterdir() if p.is_file() and p.name != 'EVIDENCE_SHA256.json'}
    write('EVIDENCE_SHA256.json', json.dumps(hashes, indent=2) + '\n')


if __name__ == '__main__':
    commands = {'init': init, 'integrity': integrity, 'environment': environment,
                'cache-modules': cache_modules, 'dependencies': dependencies,
                'build-root': build_root, 'build-m2': build_m2, 'debt': debt,
                'scanner-tests': scanner_tests, 'axioms': axioms, 'suite': suite,
                'scope': scope, 'complete': complete}
    commands[sys.argv[1]]()
