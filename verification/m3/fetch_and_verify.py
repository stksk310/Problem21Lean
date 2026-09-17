"""Download exact GitHub evidence and write the post-run handoff receipt."""
from pathlib import Path, PurePosixPath
import argparse
import json
import re
import shutil
import subprocess
import sys
import zipfile
import verify as V

ROOT=V.ROOT
sys.path.insert(0,str(ROOT/'ci'))
import m3_audit as audit
REPO='stksk310/Problem21Lean'
ARTIFACT='P21_M3_TRUE_AUDIT_EVIDENCE'

def api(path): return subprocess.check_output(['gh','api','repos/'+REPO+'/'+path])

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--run',type=int,required=True)
    parser.add_argument('--commit',required=True)
    args=parser.parse_args()
    delivery=ROOT/'delivery'
    delivery.mkdir(exist_ok=True)
    evidence=delivery/('ci-evidence-'+str(args.run))
    evidence.mkdir(exist_ok=True)
    def save(n,obj): (delivery/n).write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8',newline='\n')
    def read(n): return (evidence/n).read_text(encoding='utf-8')
    run=json.loads(api(f'actions/runs/{args.run}'))
    assert run['head_sha']==args.commit and run['status']=='completed' and run['conclusion']=='success'
    assert run['head_branch']=='m3-nonsym-g4' and run['name']=='P21 Lean M3 Audit'
    save('GITHUB_RUN_M3.json',run)
    jobs=json.loads(api(f'actions/runs/{args.run}/attempts/{run["run_attempt"]}/jobs'))
    assert len(jobs['jobs'])==1 and jobs['jobs'][0]['conclusion']=='success'
    assert all(s['conclusion']=='success' for s in jobs['jobs'][0]['steps'])
    save('GITHUB_JOBS_M3.json',jobs)
    artifacts=json.loads(api(f'actions/runs/{args.run}/artifacts'))
    save('GITHUB_ARTIFACTS_M3.json',artifacts)
    matches=[a for a in artifacts['artifacts'] if a['name']==ARTIFACT]
    assert len(matches)==1
    artifact=matches[0]
    assert not artifact['expired'] and artifact['workflow_run']['head_sha']==args.commit
    assert artifact['workflow_run']['id']==args.run
    content=api(f'actions/artifacts/{artifact["id"]}/zip')
    assert 'sha256:'+V.sha(content)==artifact['digest']
    archive=delivery/(ARTIFACT+'.zip');archive.write_bytes(content)
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None and len(z.namelist())==len(set(z.namelist()))
        for n in z.namelist():
            assert '..' not in PurePosixPath(n).parts and '\\' not in n and ':' not in n
            assert (evidence/n).resolve().is_relative_to(evidence.resolve())
        z.extractall(evidence)
    manifest=json.loads(read('EVIDENCE_SHA256.json'))
    assert set(manifest)=={p.name for p in evidence.iterdir() if p.is_file()}-{'EVIDENCE_SHA256.json'}
    for n,h in manifest.items(): assert V.sha((evidence/n).read_bytes())==h,n
    assert read('COMMIT_SHA.txt').strip()==args.commit
    context=json.loads(read('RUN_CONTEXT.json'))
    assert context['GITHUB_SHA']==args.commit and context['GITHUB_REPOSITORY']==REPO
    assert int(context['GITHUB_RUN_ID'])==args.run and int(context['GITHUB_RUN_ATTEMPT'])==run['run_attempt']
    assert context['RUNNER_OS']=='Linux'
    results=json.loads(read('RESULTS.json'))
    expected=dict(frozen_integrity='103/103',candidate_source_integrity='PASS',fresh_root_build=True,
      proof_debt_tokens=0,project_specific_axioms=0,m3_verification_exit_code=0,dependency_dag='PASS',
      original_m1_suite=0,original_m2a_suite=0,original_m2b_suite=0,std_herzog='PROVED',std_white='OPEN',full_g4='OPEN')
    for k,v in expected.items(): assert results.get(k)==v,k
    assert results['pinned_dependencies']==9
    for n in audit.REQUIRED: assert read(n).strip() and not read(n).startswith('NOT RUN'),n
    for n in ['ROOT_BUILD_LOG.txt','FROZEN_BUILD_LOG.txt','M3_BUILD_LOG.txt','AXIOM_REPORT.txt',
              'STATEMENT_INSPECTION.txt','REGRESSION_LOG.txt','SCANNER_TEST_LOG.txt',
              'M1_ORIGINAL_SUITE.txt','M2A_ORIGINAL_SUITE.txt','M2B_ORIGINAL_SUITE.txt','M3_VERIFICATION_LOG.txt']:
        codes=re.findall(r'^EXIT_CODE=(\d+)$',read(n),re.M)
        assert codes and set(codes)=={'0'},n
    candidate_sha=V.sha(audit.ARCHIVE.read_bytes())
    audit.baseline()
    assert candidate_sha in read('CANDIDATE_SOURCE_INTEGRITY.txt')
    assert 'SOURCE_CHANGED: NO' in read('CANDIDATE_SOURCE_INTEGRITY.txt')
    assert 'FROZEN_SOURCE_CHANGED: NO' in read('FROZEN_SOURCE_INTEGRITY.txt')
    summary=json.loads(read('AXIOM_SUMMARY.json'))
    found=V.V.parse_axioms(read('AXIOM_REPORT.txt'),summary['declarations'])
    assert found==summary['declarations'] and len(found)==results['axiom_roots']
    assert summary['project_specific_axioms']==0
    local=json.loads((V.HERE/'LOCAL_VERIFICATION.json').read_text())
    assert len(found)==local['axiom_roots'] and results['m3_module_count']==local['m3_module_count']
    branch=json.loads(api('branches/m3-nonsym-g4'))
    assert branch['commit']['sha']==args.commit
    main=json.loads(api('branches/main'))
    save('GITHUB_BRANCH_HEADS_M3.json',{'m3':args.commit,'main':main['commit']['sha']})
    candidate=delivery/audit.ARCHIVE.name
    shutil.copyfile(audit.ARCHIVE,candidate)
    assert V.sha(candidate.read_bytes())==candidate_sha
    receipt=dict(status='M3A NONSYMMETRIC LOCAL GEOMETRY CANDIDATE FOR TRUE AUDIT; CI REPRODUCIBILITY EVIDENCE READY',
      repository='https://github.com/'+REPO,branch='m3-nonsym-g4',audit_target_commit=args.commit,
      workflow_run=run['html_url'],workflow_run_id=args.run,attempt=run['run_attempt'],ci_conclusion=run['conclusion'],
      artifact_name=ARTIFACT,artifact_id=artifact['id'],artifact_digest=artifact['digest'],
      artifact_url=f'https://github.com/{REPO}/actions/runs/{args.run}/artifacts/{artifact["id"]}',
      artifact_download_sha256_verified=True,artifact_entry_manifest_verified=True,
      artifact_verified_entry_count=len(manifest),candidate_zip_sha256=candidate_sha,
      std_herzog='PROVED INCLUDING PRIMITIVE FORMULAS',std_white='OPEN: MinimumOneStatement',
      color_cap='CONDITIONAL ON MINBOX AND DPE',g4='CONDITIONAL SELECTED-FOUR CLASSIFICATION PROVED; UNCONDITIONAL FULL G4 OPEN',
      path_input='PROVED',typeii_input='PROVED',chain_input='PROVED',
      m3_module_count=results['m3_module_count'],axiom_declarations_checked=len(found),
      proof_debt=0,project_specific_axioms=0,frozen_files_verified=103,
      frozen_source_changed=False,source_changed=False,main_merge_performed=False,
      old_suites={'M1':0,'M2A':0,'M2B':0},local_candidate_zip=str(candidate),
      local_evidence_zip=str(archive),local_evidence_directory=str(evidence),
      remaining_open=['P21.Nonsymmetric.ColorCap.MinimumOneStatement',
        'P21.Nonsymmetric.ColorCap.BoxPositiveExitStatement','Unconditional COLOR-CAP and G4',
        'Independent external audit; terminal Sections 5–10 and later closure outside this milestone'])
    save('HANDOFF_RECEIPT_M3.json',receipt)
    print(json.dumps(receipt,indent=2))

if __name__=='__main__': main()
