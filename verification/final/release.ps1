$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
Set-Location $root

& powershell -NoProfile -ExecutionPolicy Bypass -File verification/final/verify.ps1
if ($LASTEXITCODE -ne 0) { throw 'Full final verification failed' }

$python = if (Test-Path 'C:\Users\stksk\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe') {
  'C:\Users\stksk\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
} elseif (Get-Command python3 -ErrorAction SilentlyContinue) { (Get-Command python3).Source } else { 'python' }
$evidence = Join-Path $root 'delivery/P21_FINAL_TRUE_AUDIT_EVIDENCE'

$packageOutput = @(& $python verification/final/package_final.py 2>&1)
$packageCode = $LASTEXITCODE
$packageOutput | Set-Content -Encoding UTF8 (Join-Path $evidence 'PACKAGE_REPORT.txt')
if ($packageCode -ne 0) { throw 'Final candidate packaging failed' }
Copy-Item delivery/FINAL_CANDIDATE_SHA256.txt (Join-Path $evidence 'FINAL_CANDIDATE_SHA256.txt')

$extractOutput = @(& powershell -NoProfile -ExecutionPolicy Bypass -File verification/final/verify_candidate.ps1 2>&1)
$extractCode = $LASTEXITCODE
$extractOutput | Set-Content -Encoding UTF8 (Join-Path $evidence 'FRESH_EXTRACTION_LOG.txt')
if ($extractCode -ne 0) { throw 'Fresh candidate extraction verification failed' }

& $python verification/final/make_manifests.py
if ($LASTEXITCODE -ne 0) { throw 'Final evidence manifest generation failed' }
& $python verification/final/make_manifests.py --verify
if ($LASTEXITCODE -ne 0) { throw 'Final evidence manifest verification failed' }
Write-Output 'FINAL MAIN THEOREM RELEASE GATES PASS'
