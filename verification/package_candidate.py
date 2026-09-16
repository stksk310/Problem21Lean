"""Stage and package the source project; never traverse the shared .lake cache."""
from pathlib import Path
import hashlib
import json
import shutil
import sys
import zipfile

root = Path(__file__).resolve().parents[1]
name = 'P21_LEAN_M1_FOUNDATION_C2_CANDIDATE_20260916'
stage = root / 'delivery' / name
required = ['P21.lean', 'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
            'README.md', 'SOURCE_OF_TRUTH.md', 'LEAN_DEPENDENCY_DAG.md',
            'STATEMENT_MAP.md', 'STATEMENT_MAP.json', 'CODEX_SELF_CHECK.md',
            'BUILD_LOG.txt', 'AXIOM_REPORT.txt', 'PROOF_DEBT_REPORT.txt', 'NEXT_RESTART.md']
verification = ['prepare_reports.py', 'check_axiom_report.py', 'verify.py', 'package_candidate.py',
                'lake.ps1', 'AxiomCheck.lean', 'StatementCheck.lean', 'DECLARATIONS.json',
                'AXIOM_SUMMARY.json', 'STATEMENTS.txt', 'CHECK_EXIT_CODES.json',
                'SELF_CHECK_RUN.txt', 'PUBLICATION_TEXT_DIFF.txt', 'SOURCE_COMPARISON.json']
if (root / 'verification/FRESH_PROJECT_BUILD_LOG.txt').exists():
    verification.append('FRESH_PROJECT_BUILD_LOG.txt')
files = [root / p for p in required] + [root / 'verification' / p for p in verification]
for folder in ['P21', 'reference_inputs', 'source_excerpts']:
    files.extend(p for p in (root / folder).rglob('*') if p.is_file())
for p in files:
    if not p.is_file():
        raise SystemExit(f'Missing required file: {p}')
    dest = stage / p.relative_to(root)
    dest.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(p, dest)
if '--stage' in sys.argv:
    print(stage)
    raise SystemExit(0)

hashes = {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
          for p in sorted(files)}
manifest = dict(format=1, algorithm='SHA-256', scope='Every ZIP file except this manifest itself',
                files=hashes)
manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode('utf-8')
(stage / 'MANIFEST_SHA256.json').write_bytes(manifest_bytes)
archive = root / 'delivery' / (name + '.zip')
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for rel in hashes:
        z.write(stage / rel, name + '/' + rel)
    z.writestr(name + '/MANIFEST_SHA256.json', manifest_bytes)
with zipfile.ZipFile(archive) as z:
    if z.testzip() is not None:
        raise SystemExit('ZIP CRC failure')
    if len(z.namelist()) != len(hashes) + 1:
        raise SystemExit('Unexpected ZIP entry count')
    for rel, digest in hashes.items():
        if hashlib.sha256(z.read(name + '/' + rel)).hexdigest() != digest:
            raise SystemExit(f'ZIP content hash mismatch: {rel}')
    for p in required:
        if name + '/' + p not in z.namelist():
            raise SystemExit(f'Missing required ZIP entry: {p}')
    if any('/.lake/' in p or '/.git/' in p for p in z.namelist()):
        raise SystemExit('Unexpected dependency or repository cache in ZIP')
print(json.dumps(dict(zip=str(archive), files=len(hashes)+1, bytes=archive.stat().st_size,
                     sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                     zip_crc='ok', all_entry_sha256='ok'), indent=2))
