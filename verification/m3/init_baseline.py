"""Record the authoritative source inputs and immutable pre-M3 files."""
from pathlib import Path
import hashlib
import json
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = '9a9e01c401a934cfca2da15026986b0ecf83ff4f'
def sha(data): return hashlib.sha256(data).hexdigest()
names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', BASE], cwd=ROOT).decode().splitlines()
files = {}
for name in names:
    if name.endswith('.lean') or name.startswith(('verification/m2/', 'verification/m2b/')) or name in {'lean-toolchain','lakefile.toml','lake-manifest.json'}:
        original = subprocess.check_output(['git','show',BASE + ':' + name], cwd=ROOT)
        if (ROOT / name).read_bytes() != original:
            raise ValueError('Baseline mismatch: ' + name)
        files[name] = sha(original)
out = ROOT / 'verification/m3'
(out / 'FROZEN_SHA256.json').write_text(json.dumps(dict(commit=BASE,files=files),indent=2)+'\n',encoding='utf-8',newline='\n')
inputs = ['P21_Journal_of_Algebra_Submission_Manuscript_FINAL_20260916.pdf','P21_FINAL_FROZEN_VERIFICATION_EDITION_20260907.zip']
(out / 'INPUT_SHA256.json').write_text(json.dumps({name:sha((ROOT.parent / 'reference_inputs' / name).read_bytes()) for name in inputs},indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'protected_files':len(files),'existing_lean_files':sum(n.endswith('.lean') for n in files)}))
