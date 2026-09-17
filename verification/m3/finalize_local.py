"""Bind successful local evidence to the complete final Lean source inventory."""
import json
import shutil
from pathlib import Path
import verify as V

result=json.loads((V.EVIDENCE/'RESULTS.json').read_text(encoding='utf-8'))
required=dict(frozen_integrity='103/103',fresh_root_build=True,proof_debt_tokens=0,
              project_specific_axioms=0,m3_verification_exit_code=0,dependency_dag='PASS',
              original_m1_suite=0,original_m2a_suite=0,original_m2b_suite=0)
for k,v in required.items():
    if result.get(k)!=v: raise ValueError('Local gate missing: '+k)
V.integrity()
snapshot=V.HERE/'local-evidence'
snapshot.mkdir(exist_ok=True)
for p in V.EVIDENCE.iterdir():
    if p.name == 'CANDIDATE_SOURCE_INTEGRITY.txt':
        continue  # This gate binds the later immutable ZIP to its exact commit.
    if p.is_file() and p.suffix in {'.txt','.json'} and not p.read_text(encoding='utf-8').startswith('NOT RUN'):
        shutil.copyfile(p,snapshot/p.name)
local_results = dict(result)
local_results.pop('candidate_source_integrity', None)
(snapshot/'RESULTS.json').write_text(json.dumps(local_results,indent=2)+'\n',encoding='utf-8',newline='\n')
for src,dst in [('FROZEN_SOURCE_INTEGRITY.txt','FROZEN_SOURCE_INTEGRITY_REPORT.txt'),
                ('AXIOM_REPORT.txt','AXIOM_REPORT_M3.txt'),('PROOF_DEBT_REPORT.txt','PROOF_DEBT_REPORT_M3.txt')]:
    shutil.copyfile(V.EVIDENCE/src,V.ROOT/dst)
logs=['ROOT_BUILD_LOG.txt','FROZEN_BUILD_LOG.txt','M3_BUILD_LOG.txt','REGRESSION_LOG.txt']
(V.ROOT/'BUILD_LOCAL_LOG.txt').write_text('\n'.join('## '+n+'\n'+(V.EVIDENCE/n).read_text(encoding='utf-8') for n in logs),encoding='utf-8',newline='\n')
report=dict(fresh_root_build=True,all_local_gates_passed=True,
  original_m1_suite_passed=True,original_m2a_suite_passed=True,original_m2b_suite_passed=True,
  proof_debt_tokens=0,project_specific_axioms=0,frozen_source_changed=False,
  m3_module_count=result['m3_module_count'],axiom_roots=result['axiom_roots'],
  std_herzog='PROVED',std_white='OPEN',full_g4='OPEN',
  lean_source_sha256={p.relative_to(V.ROOT).as_posix():V.sha(p.read_bytes()) for p in V.V.lean_files()})
(V.HERE/'LOCAL_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in report.items() if k!='lean_source_sha256'},indent=2))
