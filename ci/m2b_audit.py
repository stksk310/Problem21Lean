"""Exact-source M2B CI wrapper. No network, publication, or source mutation."""
from pathlib import Path, PurePosixPath
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
import zipfile
import importlib.util

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


V = load('m2b_verify', ROOT / 'verification/m2b/verify.py')
OLD = load('m2b_frozen_m2a_audit', ROOT / 'ci/m2a_audit.py')
EVIDENCE = V.EVIDENCE
ARCHIVE = ROOT / 'ci/candidate/P21_LEAN_M2B_STD_SYM_GLUE_FULL_S3_CANDIDATE_20260917.zip'
REQUIRED = '''ENVIRONMENT.txt FROZEN_SOURCE_INTEGRITY.txt CANDIDATE_SOURCE_INTEGRITY.txt
ROOT_BUILD_LOG.txt M2A_BUILD_LOG.txt M2B_BUILD_LOG.txt M2B_MODULE_LIST.txt
PROOF_DEBT_REPORT.txt SCANNER_TEST_LOG.txt AXIOM_REPORT.txt AXIOM_SUMMARY.json
STATEMENT_INSPECTION.txt DEPENDENCY_DAG_CHECK.txt CIRCULARITY_CHECK.txt
M2_VERIFICATION_LOG.txt M2B_VERIFICATION_LOG.txt COMMIT_SHA.txt RUN_CONTEXT.json
DEPENDENCY_STATE.txt'''.split()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def init():
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    for name in REQUIRED:
        V.write(name, 'NOT RUN\n')
    V.write('RESULTS.json', '{}\n')
    head = git('rev-parse', 'HEAD').decode().strip()
    if os.environ.get('GITHUB_SHA', head) != head:
        raise ValueError('Checkout differs from event SHA')
    V.write('COMMIT_SHA.txt', head + '\n')
    V.write('RUN_CONTEXT.json', json.dumps({key: os.environ.get(key) for key in
            ['GITHUB_REPOSITORY', 'GITHUB_REF', 'GITHUB_SHA', 'GITHUB_RUN_ID',
             'GITHUB_RUN_ATTEMPT', 'GITHUB_WORKFLOW', 'RUNNER_OS', 'RUNNER_ARCH']}, indent=2) + '\n')


def archive_data(path, expected):
    if V.sha(path.read_bytes()) != expected:
        raise ValueError('Candidate ZIP SHA-256 mismatch')
    data = {}
    with zipfile.ZipFile(path) as z:
        if z.testzip() is not None:
            raise ValueError('ZIP CRC error')
        prefix = path.stem + '/'
        for info in z.infolist():
            name = info.filename
            if info.is_dir():
                continue
            if not name.startswith(prefix):
                raise ValueError('Invalid ZIP root: ' + name)
            rel = name[len(prefix):]
            parts = PurePosixPath(rel).parts
            if not rel or '..' in parts or '\\' in rel or ':' in rel or rel.startswith('/'):
                raise ValueError('Unsafe ZIP path: ' + rel)
            if rel in data:
                raise ValueError('Duplicate ZIP path: ' + rel)
            if '.lake' in parts or '.git' in parts or rel.endswith(('.olean', '.ilean', '.o', '.so')):
                raise ValueError('Build/VCS artifact in source candidate: ' + rel)
            data[rel] = z.read(info)
    manifest = json.loads(data['MANIFEST_SHA256.json'])['files']
    if set(manifest) != set(data) - {'MANIFEST_SHA256.json'}:
        raise ValueError('Manifest coverage mismatch')
    for name, digest in manifest.items():
        if V.sha(data[name]) != digest:
            raise ValueError('Manifest digest mismatch: ' + name)
    return data


def baseline():
    receipt = (ROOT / 'ci/M2B_CANDIDATE_SHA256.txt').read_text(encoding='utf-8').strip()
    expected = receipt.split()[0]
    if not re.fullmatch('[0-9a-f]{64}', expected):
        raise ValueError('Malformed candidate hash receipt')
    return archive_data(ARCHIVE, expected)


def integrity():
    V.integrity()
    frozen = V.protected()
    for p, digest in frozen.items():
        original = git('show', V.FROZEN + ':' + p)
        if V.sha(original) != digest or original != (ROOT / p).read_bytes():
            raise ValueError('Frozen Git-blob mismatch: ' + p)
    # Prevent a modified baseline from simply omitting a protected source.
    base_names = git('ls-tree', '-r', '--name-only', V.FROZEN).decode().splitlines()
    expected_frozen = {p for p in base_names if p.endswith('.lean') or p.startswith('verification/m2/')
                       or p in {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json'}}
    if set(frozen) != expected_frozen:
        raise ValueError('Frozen baseline file-set differs from Git tree')
    data = baseline()
    tracked = set(git('ls-files', '-z').decode().rstrip('\0').split('\0'))
    # Candidate artifact reports may be generated for the ZIP only. Every executable
    # source, verifier and build configuration must be committed byte-identically.
    def source(p):
        return p.endswith(('.lean', '.py', '.ps1', '.yml', '.yaml')) or p in frozen or p in {
            'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'verification/m2b/FROZEN_SHA256.json'}
    candidate_sources = {p for p in data if source(p)}
    checkout_sources = {p for p in tracked if source(p)}
    if candidate_sources != checkout_sources:
        raise ValueError('Candidate/committed source inventory mismatch: ' +
                         repr(sorted(candidate_sources ^ checkout_sources)))
    failures = []
    for p in sorted(candidate_sources):
        if not (ROOT / p).is_file() or (ROOT / p).read_bytes() != data[p] or git('show', 'HEAD:' + p) != data[p]:
            failures.append(p)
    for p in tracked:
        if '.lake' in PurePosixPath(p).parts or p.endswith(('.olean', '.ilean', '.o', '.so')):
            failures.append('Tracked build artifact: ' + p)
    V.write('CANDIDATE_SOURCE_INTEGRITY.txt', 'Candidate SHA-256: ' + V.sha(ARCHIVE.read_bytes()) +
            f'\nCommitted source files: {len(candidate_sources)}\n' +
            ('SOURCE_CHANGED: YES\n' + '\n'.join(failures) if failures else 'SOURCE_CHANGED: NO\n') +
            'All generated M2B Lean checker files are included in committed-source equality.\n')
    if failures:
        raise ValueError('Candidate source mismatch: ' + repr(failures))
    V.record('candidate_source_integrity', 'PASS')


def environment():
    V.write('ENVIRONMENT.txt', platform.platform() + '\nPython ' + sys.version + '\n')
    for args in [V.lake() + ['--version'], V.lake() + ['env', 'lean', '--version'], ['git', '--version']]:
        V.run(args, 'ENVIRONMENT.txt', append=True)
    with (EVIDENCE / 'ENVIRONMENT.txt').open('a', encoding='utf-8') as out:
        out.write('\nlean-toolchain:\n' + (ROOT / 'lean-toolchain').read_text(encoding='utf-8'))
        out.write('\nlake-manifest.json:\n' + (ROOT / 'lake-manifest.json').read_text(encoding='utf-8'))


def cache_modules():
    imports = set()
    for p in V.lean_files():
        imports.update(re.findall(r'^import (Mathlib\.[\w.]+)', p.read_text(encoding='utf-8-sig'), re.M))
    print('\n'.join(sorted(imports)))


def dependencies():
    OLD.EVIDENCE = EVIDENCE
    OLD.dependencies()


def suite():
    """Unmodified M2 verifier on its exact archived M2A source, never on M2B."""
    data = OLD.baseline()  # Uses the frozen hard-coded archive SHA-256.
    with tempfile.TemporaryDirectory(prefix='p21-m2b-original-suite-') as tmp:
        scratch = Path(tmp)
        for name, content in data.items():
            target = scratch / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(content)
        (scratch / '.lake').mkdir()
        deps = (ROOT / '.lake/packages').resolve()
        if os.name == 'nt':
            # Junction shares third-party dependency packages, never project builds.
            command = "New-Item -ItemType Junction -Path '" + str(scratch / '.lake/packages').replace("'", "''") + "' -Target '" + str(deps).replace("'", "''") + "' | Out-Null"
            subprocess.run(['pwsh', '-NoProfile', '-Command', command], check=True)
        else:
            (scratch / '.lake/packages').symlink_to(deps, target_is_directory=True)
        V.run([sys.executable, 'verification/m2/verify.py'], 'M2_VERIFICATION_LOG.txt', cwd=scratch)
        for name, content in data.items():
            if name.startswith('P21') and name.endswith('.lean') and (scratch / name).read_bytes() != content:
                raise ValueError('Original verifier mutated proof source: ' + name)
        expected = json.loads(data['verification/m2/DECLARATIONS.json'])
        actual = json.loads((scratch / 'verification/m2/DECLARATIONS.json').read_text(encoding='utf-8'))
        if actual != expected:
            raise ValueError('Original M2 declaration inventory changed')
        for name in ['BUILD_LOG.txt', 'AXIOM_REPORT.txt', 'PROOF_DEBT_REPORT.txt',
                     'M1_FROZEN_INTEGRITY_REPORT.txt', 'verification/m2/STATEMENTS.txt',
                     'verification/m2/AXIOM_SUMMARY.json', 'verification/m2/REGRESSION_LOG.txt']:
            (EVIDENCE / ('ORIGINAL_SUITE_' + Path(name).name)).write_bytes((scratch / name).read_bytes())
        if os.name == 'nt':
            # Remove only the junction before TemporaryDirectory recursively cleans scratch.
            os.rmdir(scratch / '.lake/packages')
    V.record('original_m2_verification_exit_code', 0)


def verify():
    V.run([sys.executable, 'verification/m2b/verify.py', '--fresh'], 'M2B_VERIFICATION_LOG.txt')


def complete():
    for name in REQUIRED:
        p = EVIDENCE / name
        if not p.is_file() or not p.stat().st_size or p.read_text(encoding='utf-8').startswith('NOT RUN'):
            raise ValueError('Missing required evidence: ' + name)
    results = json.loads((EVIDENCE / 'RESULTS.json').read_text(encoding='utf-8'))
    expected = dict(frozen_integrity='57/57', candidate_source_integrity='PASS',
                    fresh_root_build=True, full_success_theorems_present=True,
                    proof_debt_tokens=0, project_specific_axioms=0,
                    scanner_tests_exit_code=0, m2b_verification_exit_code=0,
                    original_m2_verification_exit_code=0, circularity_check='PASS',
                    std_sym_glue='PROVED', full_s3='PROVED')
    for key, value in expected.items():
        if results.get(key) != value:
            raise ValueError('Incomplete gate: ' + key)
    if not results.get('pinned_dependencies'):
        raise ValueError('Dependency integrity missing')
    V.record('status', 'M2B STD_SYM_GLUE + FULL S3 CANDIDATE FOR TRUE AUDIT')
    V.write('EVIDENCE_SHA256.json', json.dumps({p.name: V.sha(p.read_bytes()) for p in EVIDENCE.iterdir()
            if p.is_file() and p.name != 'EVIDENCE_SHA256.json'}, indent=2) + '\n')


if __name__ == '__main__':
    commands = {'init': init, 'integrity': integrity, 'environment': environment,
                'cache-modules': cache_modules, 'dependencies': dependencies,
                'verify': verify, 'suite': suite, 'complete': complete}
    commands[sys.argv[1]]()

