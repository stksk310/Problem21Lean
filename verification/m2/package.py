"""Package M2 sources and evidence without walking dependency/build directories."""
from pathlib import Path
import hashlib
import json
import os
import zipfile

ROOT = Path(__file__).resolve().parents[2]
NAME = 'P21_LEAN_M2A_INTERNAL_SYMMETRIC_CLOSURE_CANDIDATE_20260917'
SKIP_DIRS = {'.git', '.lake', '.github', 'ci', '__pycache__', 'delivery', 'audit-evidence'}
SKIP_FILES = {'.git', 'MANIFEST_SHA256.json', 'SOURCE_SHA256_BEFORE_GITHUB.txt'}
REQUIRED = ['README.md', 'SOURCE_OF_TRUTH.md', 'M2_DEPENDENCY_DAG.md',
            'M2_STATEMENT_MAP.md', 'MATHLIB_SYM_GLUE_SEARCH.md',
            'M1_FROZEN_INTEGRITY_REPORT.txt', 'BUILD_LOG.txt', 'AXIOM_REPORT.txt',
            'PROOF_DEBT_REPORT.txt', 'CODEX_SELF_CHECK.md', 'NEXT_RESTART.md',
            'STD_SYM_GLUE_OPEN.md', 'P21/Symmetric/Closure.lean',
            'verification/m2/FRESH_VERIFICATION_REPORT.json']

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    files = {}
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in SKIP_DIRS)
        for name in sorted(names):
            p = Path(directory) / name
            rel = p.relative_to(ROOT).as_posix()
            if rel in SKIP_FILES or name.endswith(('.pyc', '.olean', '.ilean', '.o', '.c', '.a', '.so')):
                continue
            files[rel] = p.read_bytes()
    for name in REQUIRED:
        if name not in files:
            raise ValueError('Missing required delivery: ' + name)
    baseline = json.loads(files['verification/m2/M1_FROZEN_SHA256.json'])
    for name, digest in baseline['files'].items():
        if sha(files[name]) != digest:
            raise ValueError('M1 source changed: ' + name)
    fresh = json.loads(files['verification/m2/FRESH_VERIFICATION_REPORT.json'])
    if fresh['exit_code'] != 0 or fresh['project_cache_present_before_build']:
        raise ValueError('Missing successful fresh verification')
    for name, digest in fresh['verified_lean_sha256'].items():
        if sha(files[name]) != digest:
            raise ValueError('Source differs from fresh verification: ' + name)
    manifest = {'format': 1, 'algorithm': 'SHA-256',
                'scope': 'Every ZIP file except MANIFEST_SHA256.json itself',
                'status': 'M2A INTERNAL SYMMETRIC CLOSURE CANDIDATE FOR TRUE AUDIT',
                'STD_SYM_GLUE': 'OPEN', 'files': {p: sha(b) for p,b in sorted(files.items())}}
    files['MANIFEST_SHA256.json'] = (json.dumps(manifest, indent=2)+'\n').encode('utf-8')
    out = ROOT / 'delivery' / (NAME + '.zip')
    out.parent.mkdir(exist_ok=True)
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for name, data in sorted(files.items()):
            z.writestr(NAME + '/' + name, data)
    with zipfile.ZipFile(out) as z:
        if z.testzip() is not None:
            raise ValueError('ZIP CRC failure')
        if len(z.namelist()) != len(files):
            raise ValueError('Entry count mismatch')
        for name, data in files.items():
            if z.read(NAME+'/'+name) != data:
                raise ValueError('ZIP byte mismatch: '+name)
    print(json.dumps({'zip': str(out), 'files': len(files), 'bytes': out.stat().st_size,
                      'sha256': sha(out.read_bytes()), 'zip_crc': 'ok',
                      'entry_sha256': 'all match', 'M1_source_changed': False}, indent=2))

if __name__ == '__main__':
    main()
