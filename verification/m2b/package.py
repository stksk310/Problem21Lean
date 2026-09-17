"""Create the immutable source candidate after the documented fresh local gates."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
NAME = 'P21_LEAN_M2B_STD_SYM_GLUE_FULL_S3_CANDIDATE_20260917'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    report = json.loads((ROOT / 'verification/m2b/LOCAL_VERIFICATION.json').read_text(encoding='utf-8'))
    for key in ['fresh_root_build', 'all_local_gates_passed', 'original_m2_suite_passed']:
        if report.get(key) is not True:
            raise ValueError('Local gate missing: ' + key)
    for name, digest in report['lean_source_sha256'].items():
        if sha((ROOT / name).read_bytes()) != digest:
            raise ValueError('Source changed since fresh verification: ' + name)
    frozen = json.loads((ROOT / 'verification/m2b/FROZEN_SHA256.json').read_text(encoding='utf-8'))
    for name, digest in frozen['files'].items():
        data = (ROOT / name).read_bytes()
        old = subprocess.check_output(['git', 'show', frozen['commit'] + ':' + name], cwd=ROOT)
        if sha(data) != digest or data != old:
            raise ValueError('Frozen Git baseline mismatch: ' + name)
    required = '''README_M2B.md SOURCE_OF_TRUTH_M2B.md M2B_DEPENDENCY_DAG.md
M2B_STATEMENT_MAP.md M2B_PROOF_ROUTE.md FROZEN_SOURCE_INTEGRITY_REPORT.txt
BUILD_LOCAL_LOG.txt AXIOM_REPORT_M2B.txt PROOF_DEBT_REPORT_M2B.txt
CODEX_SELF_CHECK_M2B.md NEXT_RESTART.md'''.split()
    for name in required:
        if not (ROOT / name).is_file() or not (ROOT / name).stat().st_size:
            raise ValueError('Required delivery file missing: ' + name)
    names = subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'], cwd=ROOT).decode().split('\0')
    excluded = {'MANIFEST_SHA256.json', 'ci/M2B_CANDIDATE_SHA256.txt', 'ci/candidate/' + NAME + '.zip'}
    files = {}
    for name in sorted(set(names) - excluded - {''}):
        path = ROOT / name
        if not path.is_file():
            raise ValueError('Missing snapshot file: ' + name)
        if any(part in {'.lake', '.git', '__pycache__', 'audit-evidence', 'delivery'} for part in Path(name).parts):
            raise ValueError('Generated cache in snapshot: ' + name)
        if path.suffix in {'.olean', '.ilean', '.o', '.so', '.pyc'}:
            raise ValueError('Compiled artifact in snapshot: ' + name)
        files[name] = path.read_bytes()
    if {name for name in files if name.endswith('.lean')} != set(report['lean_source_sha256']):
        raise ValueError('Lean inventory changed after fresh verification')
    files['MANIFEST_SHA256.json'] = (json.dumps({'files': {name: sha(data) for name, data in files.items()}}, indent=2) + '\n').encode()
    archive = ROOT / 'ci/candidate' / (NAME + '.zip')
    archive.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, data in sorted(files.items()):
            info = zipfile.ZipInfo(NAME + '/' + name, date_time=(2026, 9, 17, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            z.writestr(info, data)
    with zipfile.ZipFile(archive) as z:
        if z.testzip() is not None or len(z.namelist()) != len(files):
            raise ValueError('ZIP readback failed')
        for name, data in files.items():
            if z.read(NAME + '/' + name) != data:
                raise ValueError('ZIP byte mismatch: ' + name)
    digest = sha(archive.read_bytes())
    (ROOT / 'ci/M2B_CANDIDATE_SHA256.txt').write_text(digest + '  ' + archive.name + '\n', encoding='utf-8', newline='\n')
    print(json.dumps({'candidate': str(archive), 'sha256': digest, 'files': len(files), 'bytes': archive.stat().st_size}, indent=2))


if __name__ == '__main__':
    main()
