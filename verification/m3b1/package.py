"""One immutable complete-project candidate after the exact local proof gates."""
from pathlib import Path
import json
import zipfile
import verify as V
import finalize_local as F

def main():
    report=json.loads((V.HERE/'LOCAL_VERIFICATION.json').read_text(encoding='utf-8'))
    if report.get('all_local_gates_passed') is not True or report.get('minimum_one_proved') is not True:
        raise ValueError('Successful exact local theorem checks required')
    actual={n:V.sha((V.ROOT/n).read_bytes()) for n in F.source_files()}
    if actual!=report['executable_sha256']:raise ValueError('Executable source changed since local checks')
    V.integrity()
    status=V.milestone();name=status['candidate'];stem=name[:-4]
    required='''README_M3B1.md SOURCE_OF_TRUTH_M3B1.md M3B1_DEPENDENCY_DAG.md M3B1_STATEMENT_MAP.md
M3B1_PROOF_ROUTE.md MATHLIB_WHITE_SEARCH.md FROZEN_SOURCE_INTEGRITY_REPORT_M3B1.txt BUILD_LOG_M3B1.txt
AXIOM_REPORT_M3B1.txt PROOF_DEBT_REPORT_M3B1.txt REGRESSION_REPORT_M3B1.txt CODEX_SELF_CHECK_M3B1.md NEXT_RESTART.md'''.split()
    for n in required:
        if not (V.ROOT/n).is_file() or not (V.ROOT/n).stat().st_size:raise ValueError('Missing delivery file: '+n)
    names=V.git('ls-files','--cached','--others','--exclude-standard','-z').decode().split('\0')
    excluded={'','MANIFEST_SHA256.json','ci/M3B1_CANDIDATE_SHA256.txt','ci/candidate/'+name}
    files={}
    for n in sorted(set(names)-excluded):
        if any(x in {'.lake','.git','__pycache__','audit-evidence','delivery'} for x in Path(n).parts):
            raise ValueError('Cache in source archive: '+n)
        if Path(n).suffix in {'.olean','.ilean','.o','.so','.pyc'}:raise ValueError('Build artifact: '+n)
        files[n]=(V.ROOT/n).read_bytes()
    files['MANIFEST_SHA256.json']=(json.dumps({'files':{n:V.sha(b) for n,b in files.items()}},indent=2)+'\n').encode()
    archive=V.ROOT/'ci/candidate'/name
    if archive.exists():raise ValueError('Candidate already exists; preserve the immutable archive')
    with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for n,b in sorted(files.items()):
            info=zipfile.ZipInfo(stem+'/'+n,date_time=(2026,9,17,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o644<<16
            z.writestr(info,b)
    with zipfile.ZipFile(archive) as z:
        if z.testzip() or len(z.namelist())!=len(files):raise ValueError('ZIP readback error')
        for n,b in files.items():
            if z.read(stem+'/'+n)!=b:raise ValueError('ZIP byte mismatch: '+n)
    digest=V.sha(archive.read_bytes())
    (V.ROOT/'ci/M3B1_CANDIDATE_SHA256.txt').write_text(digest+'  '+name+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(dict(candidate=str(archive),sha256=digest,files=len(files),bytes=archive.stat().st_size),indent=2))

if __name__=='__main__':main()
