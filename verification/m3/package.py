"""Immutable reduced-scope M3A candidate, only after successful fresh local checks."""
from pathlib import Path
import json
import subprocess
import zipfile
import verify as V

ROOT=V.ROOT
NAME='P21_LEAN_M3A_NONSYMMETRIC_LOCAL_GEOMETRY_CANDIDATE_20260917'

def main():
    report=json.loads((V.HERE/'LOCAL_VERIFICATION.json').read_text(encoding='utf-8'))
    for k in ['fresh_root_build','all_local_gates_passed','original_m1_suite_passed','original_m2a_suite_passed','original_m2b_suite_passed']:
        if report.get(k) is not True: raise ValueError('Missing local gate: '+k)
    for p,h in report['lean_source_sha256'].items():
        if V.sha((ROOT/p).read_bytes())!=h: raise ValueError('Lean changed after fresh check: '+p)
    V.integrity()
    required='''README_M3.md SOURCE_OF_TRUTH_M3.md M3_DEPENDENCY_DAG.md M3_STATEMENT_MAP.md
M3_PROOF_ROUTE.md M3_EXTERNAL_INPUT_REPORT.md FROZEN_SOURCE_INTEGRITY_REPORT.txt BUILD_LOCAL_LOG.txt
AXIOM_REPORT_M3.txt PROOF_DEBT_REPORT_M3.txt CODEX_SELF_CHECK_M3.md NEXT_RESTART.md'''.split()
    for n in required:
        if not (ROOT/n).is_file() or not (ROOT/n).stat().st_size: raise ValueError('Missing delivery file: '+n)
    names=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=ROOT).decode().split('\0')
    excluded={'','MANIFEST_SHA256.json','ci/M3_CANDIDATE_SHA256.txt','ci/candidate/'+NAME+'.zip'}
    files={}
    for n in sorted(set(names)-excluded):
        p=ROOT/n
        if any(x in {'.lake','.git','__pycache__','audit-evidence','delivery'} for x in Path(n).parts):
            raise ValueError('Cache in source archive: '+n)
        if p.suffix in {'.olean','.ilean','.o','.so','.pyc'}: raise ValueError('Build artifact: '+n)
        files[n]=p.read_bytes()
    if {n for n in files if n.endswith('.lean')}!=set(report['lean_source_sha256']):
        raise ValueError('Lean source inventory changed')
    files['MANIFEST_SHA256.json']=(json.dumps({'files':{n:V.sha(b) for n,b in files.items()}},indent=2)+'\n').encode()
    archive=ROOT/'ci/candidate'/(NAME+'.zip')
    with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for n,b in sorted(files.items()):
            info=zipfile.ZipInfo(NAME+'/'+n,date_time=(2026,9,17,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o644<<16
            z.writestr(info,b)
    with zipfile.ZipFile(archive) as z:
        if z.testzip() or len(z.namelist())!=len(files): raise ValueError('ZIP readback error')
        for n,b in files.items():
            if z.read(NAME+'/'+n)!=b: raise ValueError('ZIP byte mismatch: '+n)
    digest=V.sha(archive.read_bytes())
    (ROOT/'ci/M3_CANDIDATE_SHA256.txt').write_text(digest+'  '+archive.name+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(dict(candidate=str(archive),sha256=digest,files=len(files),bytes=archive.stat().st_size),indent=2))

if __name__=='__main__': main()
