"""Combine completed independent local checks without shared result-file writes."""
import json
import re
import shutil
import verify as V

def main():
    fresh=V.ROOT/'audit-evidence/m3b1-local-fresh'
    a=json.loads((V.EVIDENCE/'RESULTS.json').read_text(encoding='utf-8'))
    b=json.loads((fresh/'RESULTS.json').read_text(encoding='utf-8'))
    for label in ['m1','m2a','m2b','m3a']:
        if a.get('original_'+label+'_suite')!=0:raise ValueError('Historical suite incomplete: '+label)
    if b.get('m3b1_verification_exit_code')!=0 or b.get('verified_source_integrity')!='PASS':
        raise ValueError('Fresh proof checks incomplete')
    log=(fresh/'M3B1_VERIFICATION_LOG.txt').read_text(encoding='utf-8')
    codes=re.findall(r'^EXIT_CODE=(-?\d+)$',log,re.M)
    if not codes or set(codes)!={'0'}:raise ValueError('Fresh command did not finish successfully')
    snapshot=json.loads((fresh/'VERIFIED_SOURCE_SHA256.json').read_text(encoding='utf-8'))
    if snapshot!=V.source_snapshot():raise ValueError('Executable source changed after verification')
    for p in fresh.iterdir():
        if p.is_file() and p.name!='RESULTS.json':shutil.copyfile(p,V.EVIDENCE/p.name)
    merged={**a,**b}
    V.write('RESULTS.json',json.dumps(merged,indent=2)+'\n')
    V.write('LOCAL_EXECUTION_CONTEXT.json',json.dumps(dict(
      baseline=V.FROZEN,fresh_evidence_root=str(fresh),
      historical_evidence_root=str(V.EVIDENCE),
      independent_project_build_directories=True,
      result_maps_combined_only_after_success=True),indent=2)+'\n')
    print(json.dumps(merged,indent=2))

if __name__=='__main__':main()
