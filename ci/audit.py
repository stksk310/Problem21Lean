"""CI gates for the immutable P21 M1 candidate; Python standard library only."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

from debt_scan import code_only, FORBIDDEN

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'audit-evidence'
ARCHIVE = ROOT / 'ci/candidate/P21_LEAN_M1_FOUNDATION_C2_CANDIDATE_20260916.zip'
ZIP_SHA = '37f7a4163b70effbb294e65c39fa5a36e5ec8d9950769df9568047583335d0db'
REQUIRED_REPORTS = ['BUILD_LOG.txt', 'ENVIRONMENT.txt', 'AXIOM_REPORT_CI.txt',
                    'PROOF_DEBT_REPORT_CI.txt', 'SOURCE_SHA256_BEFORE_GITHUB.txt',
                    'SOURCE_SHA256_AFTER_GITHUB.txt', 'SOURCE_INTEGRITY_REPORT.txt',
                    'VERIFICATION_SUITE_LOG.txt', 'COMMIT_SHA.txt']

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write(name, data):
    EVIDENCE.mkdir(exist_ok=True)
    (EVIDENCE / name).write_text(data, encoding='utf-8')

def run(args, log, cwd=ROOT, append=False):
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open('a' if append else 'w', encoding='utf-8') as stream:
        stream.write('$ ' + ' '.join(map(str, args)) + '\n')
        stream.flush()
        proc = subprocess.Popen(list(map(str, args)), cwd=cwd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, encoding='utf-8', errors='strict')
        for line in proc.stdout:
            print(line, end='', flush=True)
            stream.write(line)
        code = proc.wait()
        stream.write(f'\nEXIT_CODE={code}\n')
    if code:
        raise RuntimeError(f'Command failed with exit {code}: {args}')

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, encoding='utf-8').strip()

def baseline():
    if sha(ARCHIVE.read_bytes()) != ZIP_SHA:
        raise ValueError('Authoritative candidate ZIP SHA-256 mismatch')
    with zipfile.ZipFile(ARCHIVE) as z:
        prefix = z.namelist()[0].split('/')[0] + '/'
        data = {p[len(prefix):]: z.read(p) for p in z.namelist() if p[len(prefix):]}
        manifest = json.loads(data['MANIFEST_SHA256.json'])
        for path, digest in manifest['files'].items():
            if sha(data[path]) != digest:
                raise ValueError('Embedded ZIP manifest mismatch: ' + path)
    hashes = {p: sha(b) for p, b in data.items()}
    if hashes != json.loads((ROOT / 'ci/CANDIDATE_FILES.json').read_text(encoding='utf-8')):
        raise ValueError('Candidate file index differs from authoritative ZIP')
    return data

def implementation(path):
    return path.endswith(('.lean', '.py', '.ps1')) or path in {
        'lean-toolchain', 'lakefile.toml', 'lakefile.lean', 'lake-manifest.json'}

def init():
    EVIDENCE.mkdir(exist_ok=True)
    for name in REQUIRED_REPORTS:
        write(name, 'NOT RUN: inspect the workflow steps if the job fails.\n')
    commit = git('rev-parse', 'HEAD')
    if os.environ.get('GITHUB_SHA', commit) != commit:
        raise ValueError('Checkout HEAD differs from GITHUB_SHA')
    write('COMMIT_SHA.txt', commit + '\n')
    write('RUN_CONTEXT.json', json.dumps({key: os.environ.get(key) for key in
          ['GITHUB_REPOSITORY', 'GITHUB_RUN_ID', 'GITHUB_RUN_ATTEMPT', 'GITHUB_SHA',
           'RUNNER_OS', 'RUNNER_ARCH', 'RUNNER_NAME']}, indent=2) + '\n')

def integrity():
    data = baseline()
    protected = {p: b for p, b in data.items() if implementation(p)}
    before = ''.join(f'{sha(b)}  {p}\n' for p, b in sorted(protected.items()))
    if (ROOT / 'SOURCE_SHA256_BEFORE_GITHUB.txt').read_bytes() != before.encode():
        raise ValueError('BEFORE manifest differs from the ZIP-derived manifest')
    write('SOURCE_SHA256_BEFORE_GITHUB.txt', before)
    failures = []
    after = []
    for path, original in sorted(data.items()):
        current = (ROOT / path).read_bytes() if (ROOT / path).is_file() else None
        valid = current == original
        if path == 'README.md':
            valid = current is not None and current.startswith(original)
        if not valid:
            failures.append(path)
        if path in protected:
            after.append(f'{sha(current) if current is not None else "MISSING"}  {path}\n')
    write('SOURCE_SHA256_AFTER_GITHUB.txt', ''.join(after))
    tracked = git('ls-files').splitlines()
    lean_files = {p for p in tracked if p.endswith('.lean')}
    if lean_files != {p for p in data if p.endswith('.lean')}:
        failures.append('Unexpected added/missing project-owned Lean file')
    for p in tracked:
        if '.lake' in Path(p).parts or p.endswith(('.olean', '.ilean', '.o', '.so', '.a')):
            failures.append('Compiled artifact tracked: ' + p)
    # Independently check the bytes in Git, not only in the working tree.
    for p, original in protected.items():
        committed = subprocess.check_output(['git', 'show', 'HEAD:' + p], cwd=ROOT)
        if committed != original:
            failures.append('Git blob differs: ' + p)
    message = ('ALL ORIGINAL IMPLEMENTATION FILES IDENTICAL\n' if not failures
               else 'SOURCE INTEGRITY FAILED\n' + '\n'.join(failures) + '\n')
    message += f'Candidate ZIP SHA256: {ZIP_SHA}\nOriginal files: {len(data)}\n'
    message += f'Protected implementation files: {len(protected)}\n'
    message += 'Original non-implementation files are also unchanged; README permits append only.\n'
    message += 'SOURCE_CHANGED: ' + ('YES' if failures else 'NO') + '\n'
    write('SOURCE_INTEGRITY_REPORT.txt', message)
    print(message)
    if failures:
        raise ValueError('Source integrity gate failed')

def environment():
    log = EVIDENCE / 'ENVIRONMENT.txt'
    for i, args in enumerate([['uname', '-a'], ['elan', '--version'], ['lean', '--version'],
                              ['lake', '--version'], ['git', '--version'], [sys.executable, '--version']]):
        run(args, log, append=i > 0)
    with log.open('a', encoding='utf-8') as out:
        out.write('\nlean-toolchain (unmodified):\n' + (ROOT / 'lean-toolchain').read_text())
        out.write('\nlake-manifest.json (unmodified):\n' + (ROOT / 'lake-manifest.json').read_text())

def dependencies():
    report = []
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text(encoding='utf-8-sig'))
    for package in manifest['packages']:
        path = ROOT / manifest['packagesDir'] / package['name']
        revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], encoding='utf-8').strip()
        status = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], encoding='utf-8')
        if revision != package['rev'] or status:
            raise ValueError('Dependency changed: ' + package['name'])
        report.append(f'{package["name"]} {revision} {package["url"]}')
    write('DEPENDENCY_STATE.txt', '\n'.join(report) + '\nALL PINNED REVISIONS MATCH\n')

def build():
    build_dir = ROOT / '.lake/build'
    if build_dir.exists() and any(build_dir.rglob('*.olean')):
        raise ValueError('Project compiled artifacts exist before the fresh lake build')
    write('PROJECT_CACHE_STATE.txt', 'No project .olean files before the mandatory lake build.\n'
          'No Actions build-cache restore. Optional third-party cache only; see DEPENDENCY_CACHE_LOG.txt.\n')
    run(['lake', 'build'], EVIDENCE / 'BUILD_LOG.txt')

def debt():
    files = [p for p in git('ls-files').splitlines() if p.endswith('.lean')]
    failures, ignored = [], 0
    for path in files:
        text = (ROOT / path).read_text(encoding='utf-8-sig')
        masked = code_only(text)
        raw = re.findall(r"[^\W\d][\w']*", text)
        code = list(re.finditer(r"[^\W\d][\w']*", masked))
        hits = [m for m in code if m.group() in FORBIDDEN]
        ignored += sum(token in FORBIDDEN for token in raw) - len(hits)
        for hit in hits:
            failures.append(f'{path}:{text[:hit.start()].count(chr(10)) + 1}: {hit.group()}')
    report = [f'Project-owned Lean files: {len(files)}',
              'Nested comments, line comments, and normal/raw strings lexically distinguished.',
              'Unterminated constructs, interpolated strings, and character/quotation literals fail closed for manual review.',
              f'Ignored non-code occurrences: {ignored}', f'Forbidden code tokens: {len(failures)}', *failures]
    write('PROOF_DEBT_REPORT_CI.txt', '\n'.join(report) + '\n')
    print('\n'.join(report))
    if failures:
        raise ValueError('Proof debt found')

def copy_originals(destination):
    for path in baseline():
        target = destination / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / path, target)

def axioms():
    run(['lake', 'env', 'lean', 'verification/AxiomCheck.lean'], EVIDENCE / 'AXIOM_REPORT_CI.txt')
    with tempfile.TemporaryDirectory(prefix='p21-axioms-') as tmp:
        scratch = Path(tmp)
        copy_originals(scratch)
        shutil.copyfile(EVIDENCE / 'AXIOM_REPORT_CI.txt', scratch / 'AXIOM_REPORT.txt')
        run([sys.executable, 'verification/check_axiom_report.py'], EVIDENCE / 'AXIOM_CHECKER_LOG.txt', scratch)
        shutil.copyfile(scratch / 'verification/AXIOM_SUMMARY.json', EVIDENCE / 'AXIOM_SUMMARY_CI.json')

def suite():
    log = EVIDENCE / 'VERIFICATION_SUITE_LOG.txt'
    run([sys.executable, '-m', 'unittest', 'discover', '-s', 'ci', '-p', 'test_*.py', '-v'], log)
    with log.open('a', encoding='utf-8') as out:
        out.write('\nOriginal suite inventory:\n'
                  'verify.py invokes prepare_reports.py and check_axiom_report.py and Lean statement/axiom checks.\n'
                  'package_candidate.py runs in both --stage and package modes in a separate pristine copy.\n'
                  'lake.ps1 is a Windows-specific toolchain path adapter, not a portable verification test; '
                  'the Linux job invokes the same lake commands directly.\n')
    with tempfile.TemporaryDirectory(prefix='p21-suite-') as tmp:
        scratch = Path(tmp)
        copy_originals(scratch)
        (scratch / '.lake').mkdir()
        (scratch / '.lake/packages').symlink_to((ROOT / '.lake/packages').resolve(), target_is_directory=True)
        run([sys.executable, 'verification/verify.py'], log, scratch, append=True)
        original = json.loads((ROOT / 'verification/DECLARATIONS.json').read_text())
        regenerated = json.loads((scratch / 'verification/DECLARATIONS.json').read_text())
        if original != regenerated:
            raise ValueError('Regenerated declaration inventory differs')
        statement_map = json.loads((ROOT / 'STATEMENT_MAP.json').read_text(encoding='utf-8'))
        if [{key: row[key] for key in ['name', 'kind', 'file', 'line']} for row in statement_map] != original:
            raise ValueError('Statement-map declaration/position consistency failed')
        anchor_map = json.loads((ROOT / 'source_excerpts/PUBLICATION_ANCHORS.json').read_text(encoding='utf-8'))
        for row in statement_map:
            node = row['milestone']
            if node.startswith('C2.') and ('fr-' + node) != anchor_map[node]['anchor']:
                raise ValueError('Publication anchor mapping failed')
        for filename in ['PROOF_DEBT_REPORT.txt', 'verification/STATEMENTS.txt', 'verification/CHECK_EXIT_CODES.json']:
            shutil.copyfile(scratch / filename, EVIDENCE / ('ORIGINAL_SUITE_' + Path(filename).name))
    with tempfile.TemporaryDirectory(prefix='p21-distribution-') as tmp:
        scratch = Path(tmp)
        copy_originals(scratch)
        run([sys.executable, 'verification/package_candidate.py', '--stage'], log, scratch, append=True)
        run([sys.executable, 'verification/package_candidate.py'], log, scratch, append=True)
        archive = next((scratch / 'delivery').glob('*.zip'))
        with zipfile.ZipFile(archive) as z:
            prefix = z.namelist()[0].split('/')[0] + '/'
            for path, original in baseline().items():
                if implementation(path) and z.read(prefix + path) != original:
                    raise ValueError('Distribution-copy implementation differs: ' + path)
    with log.open('a', encoding='utf-8') as out:
        out.write('\nALL ORIGINAL PORTABLE VERIFICATION SCRIPTS PASSED\n'
                  'STATEMENT MAP / DECLARATION INVENTORY / ANCHORS CONSISTENT\n'
                  'DISTRIBUTION COPY IMPLEMENTATION IDENTICAL\n')

if __name__ == '__main__':
    commands = {'init': init, 'integrity': integrity, 'environment': environment,
                'dependencies': dependencies, 'build': build, 'debt': debt,
                'axioms': axioms, 'suite': suite}
    commands[sys.argv[1]]()
