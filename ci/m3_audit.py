"""Exact M3A source reproduction, including isolated original M1/M2A/M2B suites."""
from pathlib import Path
import json
import os
import platform
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'verification/m3'))
import verify as V

OLD = V.load('m3_m2b_ci', ROOT / 'ci/m2b_audit.py')
ARCHIVE = ROOT / 'ci/candidate/P21_LEAN_M3A_NONSYMMETRIC_LOCAL_GEOMETRY_CANDIDATE_20260917.zip'
REQUIRED = '''COMMIT_SHA.txt RUN_CONTEXT.json ENVIRONMENT.txt FROZEN_SOURCE_INTEGRITY.txt
CANDIDATE_SOURCE_INTEGRITY.txt DEPENDENCY_STATE.txt ROOT_BUILD_LOG.txt FROZEN_BUILD_LOG.txt
M3_BUILD_LOG.txt M3_MODULE_LIST.txt AXIOM_REPORT.txt AXIOM_SUMMARY.json STATEMENT_INSPECTION.txt
PROOF_DEBT_REPORT.txt DEPENDENCY_DAG_CHECK.txt REGRESSION_LOG.txt SCANNER_TEST_LOG.txt
M1_ORIGINAL_SUITE.txt M2A_ORIGINAL_SUITE.txt M2B_ORIGINAL_SUITE.txt OLD_SUITE_LOG.txt
M3_VERIFICATION_LOG.txt CIRCULARITY_CHECK.txt RESULTS.json'''.split()

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def init():
    V.EVIDENCE.mkdir(parents=True, exist_ok=True)
    for n in REQUIRED: V.write(n, 'NOT RUN\n')
    V.write('RESULTS.json', '{}\n')
    head = git('rev-parse', 'HEAD').decode().strip()
    if os.environ.get('GITHUB_SHA', head) != head: raise ValueError('Event/HEAD mismatch')
    V.write('COMMIT_SHA.txt', head+'\n')
    V.write('RUN_CONTEXT.json', json.dumps({k:os.environ.get(k) for k in
      ['GITHUB_REPOSITORY','GITHUB_SHA','GITHUB_REF','GITHUB_RUN_ID','GITHUB_RUN_ATTEMPT','GITHUB_WORKFLOW','RUNNER_OS','RUNNER_ARCH']},indent=2)+'\n')

def baseline():
    digest = (ROOT / 'ci/M3_CANDIDATE_SHA256.txt').read_text(encoding='utf-8').split()[0]
    return OLD.archive_data(ARCHIVE, digest)

def integrity():
    V.integrity()
    frozen = V.protected()
    base_names = git('ls-tree','-r','--name-only',V.FROZEN).decode().splitlines()
    expected = {p for p in base_names if p.endswith('.lean') or p.startswith(('verification/m2/','verification/m2b/'))
                or p in {'lean-toolchain','lakefile.toml','lake-manifest.json'}}
    if set(frozen) != expected: raise ValueError('Omitted frozen baseline source')
    for p,h in frozen.items():
        old = git('show',V.FROZEN+':'+p)
        if V.sha(old) != h or old != (ROOT/p).read_bytes(): raise ValueError('Frozen Git mismatch: '+p)
    data = baseline()
    tracked = set(git('ls-files','-z').decode().rstrip('\0').split('\0'))
    def source(p): return p.endswith(('.lean','.py','.ps1','.yml','.yaml')) or p in frozen or p=='verification/m3/FROZEN_SHA256.json'
    cs, gs = {p for p in data if source(p)}, {p for p in tracked if source(p)}
    if cs != gs: raise ValueError('ZIP/Git inventory mismatch: '+repr(cs^gs))
    for p in cs:
        if data[p] != (ROOT/p).read_bytes() or data[p] != git('show','HEAD:'+p): raise ValueError('ZIP/Git byte mismatch: '+p)
    if any('.lake' in Path(p).parts or p.endswith(('.olean','.ilean','.o','.so')) for p in tracked):
        raise ValueError('Tracked build artifact')
    V.write('CANDIDATE_SOURCE_INTEGRITY.txt', f'Candidate SHA256: {V.sha(ARCHIVE.read_bytes())}\nExact committed source files: {len(cs)}\nSOURCE_CHANGED: NO\n')
    V.record('candidate_source_integrity','PASS')

def environment():
    V.write('ENVIRONMENT.txt', platform.platform()+'\nPython '+sys.version+'\n')
    for args in [V.lake()+['--version'],V.lake()+['env','lean','--version'],['git','--version']]:
        V.run(args,'ENVIRONMENT.txt',append=True)

def dependencies():
    windows_environment()
    OLD.OLD.EVIDENCE = V.EVIDENCE
    OLD.OLD.dependencies()

def cache_modules():
    imports=set()
    for p in V.V.lean_files(): imports.update(__import__('re').findall(r'^import (Mathlib\.[\w.]+)',p.read_text(encoding='utf-8-sig'),__import__('re').M))
    print('\n'.join(sorted(imports)))

def windows_environment():
    if os.name != 'nt': return
    elan = Path('C:/Users/stksk/.elan')
    toolchain = (ROOT/'lean-toolchain').read_text().strip().replace('/','--').replace(':','---')
    bindir=elan/'toolchains'/toolchain/'bin'
    if not (bindir/'lake.exe').is_file(): raise ValueError('Pinned Windows lake missing')
    os.environ['ELAN_HOME']=str(elan)
    os.environ['PATH']=str(bindir)+os.pathsep+os.environ['PATH']
    packages=sorted(p for p in (ROOT/'.lake/packages').resolve().iterdir() if p.is_dir() and (p/'.git').exists())
    os.environ['GIT_CONFIG_COUNT']=str(len(packages))
    for i,p in enumerate(packages):
        os.environ[f'GIT_CONFIG_KEY_{i}']='safe.directory'
        os.environ[f'GIT_CONFIG_VALUE_{i}']=p.as_posix()

def suite():
    windows_environment()
    V.run([sys.executable,'-m','unittest','discover','-s','ci','-p','test_*.py','-v'],
          'OLD_CI_REGRESSION_LOG.txt')
    sys.path.insert(0,str(ROOT/'ci'))
    m1=V.load('m3_m1_archive',ROOT/'ci/audit.py')
    archives=[('M1',m1.baseline(),'verification/verify.py'),
              ('M2A',OLD.OLD.baseline(),'verification/m2/verify.py'),
              ('M2B',OLD.baseline(),'verification/m2b/verify.py')]
    for label,data,script in archives:
        with tempfile.TemporaryDirectory(prefix='isolated-'+label+'-',dir=V.EVIDENCE) as tmp:
            scratch=Path(tmp).resolve()
            if not scratch.is_relative_to(V.EVIDENCE.resolve()): raise ValueError('Invalid scratch root')
            for n,b in data.items():
                p=scratch/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
            (scratch/'.lake').mkdir()
            link=scratch/'.lake/packages'
            deps=(ROOT/'.lake/packages').resolve()
            if os.name=='nt':
                command="New-Item -ItemType Junction -Path '"+str(link).replace("'","''")+"' -Target '"+str(deps).replace("'","''")+"' | Out-Null"
                subprocess.run(['pwsh','-NoProfile','-Command',command],check=True)
            else: link.symlink_to(deps,target_is_directory=True)
            try:
                log=label+'_ORIGINAL_SUITE.txt'
                V.run([sys.executable,script],log,cwd=scratch)
                if label=='M1':
                    V.run([sys.executable,'verification/package_candidate.py','--stage'],log,cwd=scratch,append=True)
                    V.run([sys.executable,'verification/package_candidate.py'],log,cwd=scratch,append=True)
                for n,b in data.items():
                    if n.startswith('P21') and n.endswith('.lean') and (scratch/n).read_bytes()!=b:
                        raise ValueError('Old suite changed mathematical source: '+n)
            finally:
                if os.name=='nt': os.rmdir(link)
                else: link.unlink()
        V.record('original_'+label.lower()+'_suite',0)
    old_suite_log()

def old_suite_log():
    V.write('OLD_SUITE_LOG.txt','\n'.join('## '+label+' unchanged original suite\n'+
      (V.EVIDENCE/(label+'_ORIGINAL_SUITE.txt')).read_text(encoding='utf-8') for label in ['M1','M2A','M2B']))

def verify(): V.run([sys.executable,'verification/m3/verify.py','--fresh'],'M3_VERIFICATION_LOG.txt')

def complete():
    for n in REQUIRED:
        p=V.EVIDENCE/n
        if not p.is_file() or not p.stat().st_size or p.read_text(encoding='utf-8').startswith('NOT RUN'):
            raise ValueError('Missing evidence: '+n)
    result=json.loads((V.EVIDENCE/'RESULTS.json').read_text())
    expected=dict(frozen_integrity='103/103',candidate_source_integrity='PASS',fresh_root_build=True,
      proof_debt_tokens=0,project_specific_axioms=0,m3_verification_exit_code=0,dependency_dag='PASS',
      original_m1_suite=0,original_m2a_suite=0,original_m2b_suite=0,std_herzog='PROVED',std_white='OPEN',full_g4='OPEN')
    for k,v in expected.items():
        if result.get(k)!=v: raise ValueError('Failed evidence gate: '+k)
    if not result.get('pinned_dependencies') or not result.get('axiom_roots'): raise ValueError('Empty dependency/axiom coverage')
    V.record('status','M3A NONSYMMETRIC LOCAL GEOMETRY CANDIDATE; STD_WHITE OPEN; FULL G4 OPEN')
    V.write('EVIDENCE_SHA256.json',json.dumps({p.name:V.sha(p.read_bytes()) for p in V.EVIDENCE.iterdir()
      if p.is_file() and p.name!='EVIDENCE_SHA256.json'},indent=2)+'\n')

if __name__=='__main__':
    {'init':init,'integrity':integrity,'environment':environment,'dependencies':dependencies,
     'cache-modules':cache_modules,'suite':suite,'old-suite-log':old_suite_log,'verify':verify,'complete':complete}[sys.argv[1]]()
