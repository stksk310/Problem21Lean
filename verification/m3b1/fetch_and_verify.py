"""Bind the downloaded successful CI evidence to the exact final MINBOX candidate."""
from pathlib import PurePosixPath
import argparse
import json
import re
import shutil
import subprocess
import sys
import zipfile
import verify as V

REPO='stksk310/Problem21Lean'
ARTIFACT='P21_M3B1_TRUE_AUDIT_EVIDENCE'
audit=V.load('m3b1_delivery_ci',V.ROOT/'ci/m3b1_audit.py')

def api(path):return subprocess.check_output(['gh','api','repos/'+REPO+'/'+path])

def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Artifact verification requires enabled assertions; remove Python optimization flags')
    parser=argparse.ArgumentParser();parser.add_argument('--run',type=int,required=True);parser.add_argument('--commit',required=True)
    args=parser.parse_args()
    delivery=V.ROOT/'delivery';delivery.mkdir(exist_ok=True)
    evidence=delivery/('ci-evidence-'+str(args.run))
    if evidence.exists() and any(evidence.iterdir()):raise ValueError('Evidence extraction directory must be empty')
    evidence.mkdir(exist_ok=True)
    def save(n,obj):(delivery/n).write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8',newline='\n')
    def read(n):return (evidence/n).read_text(encoding='utf-8')
    run=json.loads(api(f'actions/runs/{args.run}'))
    assert run['head_sha']==args.commit and run['status']=='completed' and run['conclusion']=='success'
    assert run['head_branch']=='m3b1-minbox-white' and run['name']=='P21 Lean M3B1 Audit'
    save('GITHUB_RUN_M3B1.json',run)
    jobs=json.loads(api(f'actions/runs/{args.run}/attempts/{run["run_attempt"]}/jobs'))
    assert len(jobs['jobs'])==1 and jobs['jobs'][0]['conclusion']=='success'
    assert all(s['conclusion']=='success' for s in jobs['jobs'][0]['steps'])
    save('GITHUB_JOBS_M3B1.json',jobs)
    artifacts=json.loads(api(f'actions/runs/{args.run}/artifacts'));save('GITHUB_ARTIFACTS_M3B1.json',artifacts)
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
        archived_manifest=json.loads(z.read('EVIDENCE_SHA256.json'))
        archived_files={n.filename for n in z.infolist() if not n.is_dir()}
        assert set(archived_manifest)==archived_files-{'EVIDENCE_SHA256.json'}
        for n in z.namelist():
            assert '..' not in PurePosixPath(n).parts and '\\' not in n and ':' not in n
            assert (evidence/n).resolve().is_relative_to(evidence.resolve())
        z.extractall(evidence)
    manifest=json.loads(read('EVIDENCE_SHA256.json'))
    actual={p.relative_to(evidence).as_posix() for p in evidence.rglob('*') if p.is_file()}-{'EVIDENCE_SHA256.json'}
    assert set(manifest)==actual
    for n,h in manifest.items():assert V.sha((evidence/n).read_bytes())==h,n
    assert read('COMMIT_SHA.txt').strip()==args.commit
    context=json.loads(read('RUN_CONTEXT.json'))
    assert context['GITHUB_SHA']==args.commit and context['GITHUB_REPOSITORY']==REPO
    assert int(context['GITHUB_RUN_ID'])==args.run and int(context['GITHUB_RUN_ATTEMPT'])==run['run_attempt']
    assert context['RUNNER_OS']=='Linux'
    results=json.loads(read('RESULTS.json'))
    expected=dict(frozen_integrity='PASS',frozen_lean_files=96,candidate_source_integrity='PASS',fresh_root_build=True,
      proof_debt_tokens=0,project_specific_axioms=0,m3b1_verification_exit_code=0,dependency_dag='PASS',
      original_m1_suite=0,original_m2a_suite=0,original_m2b_suite=0,original_m3a_suite=0,
      minimum_one_proved=True,std_white='PROVED',kernel_inventory='PASS',frozen_axiom_roots=1327,
      all_required_checks_passed=True,pinned_dependencies=9,verified_source_integrity='PASS')
    for k,v in expected.items():assert results.get(k)==v,k
    for n in audit.REQUIRED:assert read(n).strip() and not read(n).startswith('NOT RUN'),n
    for n in ['ROOT_BUILD_LOG.txt','FROZEN_BUILD_LOG.txt','BUILD_LOG_M3B1.txt','AXIOM_REPORT_M3B1.txt',
              'STATEMENT_INSPECTION.txt','REGRESSION_REPORT_M3B1.txt','SCANNER_TEST_LOG.txt',
              'M1_ORIGINAL_SUITE.txt','M2A_ORIGINAL_SUITE.txt','M2B_ORIGINAL_SUITE.txt','M3A_ORIGINAL_SUITE.txt',
              'M3B1_VERIFICATION_LOG.txt']:
        codes=re.findall(r'^EXIT_CODE=(-?\d+)$',read(n),re.M)
        assert codes and set(codes)=={'0'},n
    candidate,_=audit.baseline();candidate_sha=V.sha(candidate.read_bytes())
    assert candidate_sha in read('CANDIDATE_SOURCE_INTEGRITY.txt') and results['candidate_zip_sha256']==candidate_sha
    assert 'SOURCE_CHANGED: NO' in read('CANDIDATE_SOURCE_INTEGRITY.txt')
    assert 'FROZEN_SOURCE_CHANGED: NO' in read('FROZEN_SOURCE_INTEGRITY_REPORT_M3B1.txt')
    V.integrity()
    summary=json.loads(read('AXIOM_SUMMARY.json'))
    found=V.V.parse_axioms(read('AXIOM_REPORT_M3B1.txt'),summary['declarations'])
    assert found==summary['declarations'] and len(found)==results['axiom_roots']
    frozen_prefix=V.prefix_names(V.git_protected()[V.PREFIX_FILE].decode('utf-8'))
    downloaded_prefix=V.prefix_names(read('KERNEL_DECLARATION_PREFIX.txt'))
    assert frozen_prefix<=downloaded_prefix
    assert set(found)==downloaded_prefix-frozen_prefix
    assert summary['project_specific_axioms']==0
    local=json.loads((V.HERE/'LOCAL_VERIFICATION.json').read_text(encoding='utf-8'))
    assert json.loads(read('VERIFIED_SOURCE_SHA256.json'))==local['executable_sha256']==V.source_snapshot()
    assert len(found)==local['axiom_roots'] and results['m3b1_module_count']==local['m3b1_module_count']
    assert results['frozen_protected_files']==local['frozen_protected_files']==len(V.protected())
    branch=json.loads(api('branches/m3b1-minbox-white'));assert branch['commit']['sha']==args.commit
    main=json.loads(api('branches/main'))
    save('GITHUB_BRANCH_HEADS_M3B1.json',{'m3b1':args.commit,'main':main['commit']['sha']})
    output=delivery/candidate.name;shutil.copyfile(candidate,output)
    assert V.sha(output.read_bytes())==candidate_sha
    receipt=dict(status='M3B1 MINBOX / WHITE CANDIDATE FOR TRUE AUDIT; CI REPRODUCIBILITY EVIDENCE READY',
      repository='https://github.com/'+REPO,branch='m3b1-minbox-white',baseline=V.FROZEN,audit_target_commit=args.commit,
      workflow_run=run['html_url'],workflow_run_id=args.run,attempt=run['run_attempt'],ci_conclusion=run['conclusion'],
      artifact_name=ARTIFACT,artifact_id=artifact['id'],artifact_digest=artifact['digest'],
      artifact_download_sha256_verified=True,artifact_entry_manifest_verified=True,
      artifact_verified_entry_count=len(manifest),candidate_zip_sha256=candidate_sha,
      minimum_one='PROVED: P21.Nonsymmetric.ColorCap.minimum_one_proved : MinimumOneStatement',
      std_white='REQUIRED SPECIALIZED ARITHMETIC CONSEQUENCE PROVED INTERNALLY',
      additional_mathematical_hypotheses=0,remaining_frontier=['BoxPositiveExitStatement'],
      unconditional_color_cap='OPEN',full_g4='OPEN',dpe_work_performed=False,
      m3b1_module_count=results['m3b1_module_count'],axiom_declarations_checked=len(found),
      proof_debt=0,project_specific_axioms=0,frozen_lean_files_verified=96,
      frozen_files_verified=results['frozen_protected_files'],frozen_source_changed=False,source_changed=False,
      main_merge_performed=False,old_suites={'M1':0,'M2A':0,'M2B':0,'M3A':0},
      local_candidate_zip=str(output),local_evidence_zip=str(archive),local_evidence_directory=str(evidence))
    save('HANDOFF_RECEIPT_M3B1.json',receipt);print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
