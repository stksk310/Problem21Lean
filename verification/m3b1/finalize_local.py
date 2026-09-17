"""Freeze observed successful local checks and bind their exact executable sources."""
import json
import shutil
import verify as V

source_files=V.source_files

def main():
    result=json.loads((V.EVIDENCE/'RESULTS.json').read_text(encoding='utf-8'))
    required=dict(frozen_integrity='PASS',fresh_root_build=True,proof_debt_tokens=0,
      project_specific_axioms=0,m3b1_verification_exit_code=0,dependency_dag='PASS',
      kernel_inventory='PASS',frozen_lean_files=96,frozen_axiom_roots=1327,
      original_m1_suite=0,original_m2a_suite=0,original_m2b_suite=0,original_m3a_suite=0,
      minimum_one_proved=True,std_white='PROVED',pinned_dependencies=9,verified_source_integrity='PASS')
    for k,v in required.items():
        if result.get(k)!=v: raise ValueError('Local gate missing: '+k)
    verified=json.loads((V.EVIDENCE/'VERIFIED_SOURCE_SHA256.json').read_text(encoding='utf-8'))
    if V.source_snapshot()!=verified:raise ValueError('Executable sources changed after successful verification')
    V.integrity()
    snapshot=V.HERE/'local-evidence';snapshot.mkdir(exist_ok=True)
    excluded={'CANDIDATE_SOURCE_INTEGRITY.txt','EVIDENCE_SHA256.json'}
    for p in V.EVIDENCE.iterdir():
        if p.is_file() and p.name not in excluded and p.suffix in {'.txt','.json'}:
            if not p.read_text(encoding='utf-8').startswith('NOT RUN'):
                shutil.copyfile(p,snapshot/p.name)
    local_results={k:v for k,v in result.items() if not k.startswith('candidate_')}
    (snapshot/'RESULTS.json').write_text(json.dumps(local_results,indent=2)+'\n',encoding='utf-8',newline='\n')
    for n in ['FROZEN_SOURCE_INTEGRITY_REPORT_M3B1.txt','AXIOM_REPORT_M3B1.txt',
              'PROOF_DEBT_REPORT_M3B1.txt','REGRESSION_REPORT_M3B1.txt']:
        shutil.copyfile(V.EVIDENCE/n,V.ROOT/n)
    logs=['ROOT_BUILD_LOG.txt','FROZEN_BUILD_LOG.txt','BUILD_LOG_M3B1.txt','REGRESSION_REPORT_M3B1.txt']
    (V.ROOT/'BUILD_LOG_M3B1.txt').write_text('\n'.join('## '+n+'\n'+(V.EVIDENCE/n).read_text(encoding='utf-8') for n in logs),encoding='utf-8',newline='\n')
    report=dict(required,all_local_gates_passed=True,m3b1_module_count=result['m3b1_module_count'],
      axiom_roots=result['axiom_roots'],frozen_protected_files=result['frozen_protected_files'],
      baseline=V.FROZEN,remaining_frontier=['BoxPositiveExitStatement'],
      executable_sha256=verified)
    (V.HERE/'LOCAL_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='executable_sha256'},indent=2))

if __name__=='__main__':main()
