$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
Set-Location $root
$evidence = Join-Path $root 'delivery/P21_FINAL_TRUE_AUDIT_EVIDENCE'
if (Test-Path -LiteralPath $evidence) { Remove-Item -Recurse -Force -LiteralPath $evidence }
New-Item -ItemType Directory -Path $evidence -Force | Out-Null

$userHome = if ($env:USERPROFILE) { $env:USERPROFILE } elseif ($env:HOME) { $env:HOME } else { [Environment]::GetFolderPath('UserProfile') }
$env:ELAN_HOME = Join-Path $userHome '.elan'
$env:GIT_CONFIG_COUNT = '1'; $env:GIT_CONFIG_KEY_0 = 'safe.directory'; $env:GIT_CONFIG_VALUE_0 = '*'
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
$lake = if ($lakeCommand) { $lakeCommand.Source } else { Join-Path $env:ELAN_HOME 'bin/lake.exe' }
$bundledPython = 'C:\Users\stksk\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$python3 = Get-Command python3 -ErrorAction SilentlyContinue
$python = if (Test-Path -LiteralPath $bundledPython) { $bundledPython } elseif ($python3) { $python3.Source } else { 'python' }

function Invoke-Logged([string]$name, [scriptblock]$command) {
  $path = Join-Path $evidence $name
  $previousErrorAction = $ErrorActionPreference
  $ErrorActionPreference = 'Continue'
  $output = @(& $command 2>&1)
  $code = $LASTEXITCODE
  $ErrorActionPreference = $previousErrorAction
  $text = @($output | ForEach-Object { $_.ToString() })
  $text += "EXIT=$code"
  [IO.File]::WriteAllLines($path, $text, [Text.UTF8Encoding]::new($false))
  $output | Write-Output
  if ($code -ne 0) { throw "$name failed with exit $code" }
}

$sha = git -c "safe.directory=$($root.Replace('\','/'))" rev-parse HEAD
if ($LASTEXITCODE -ne 0) { throw 'Unable to resolve HEAD' }
[IO.File]::WriteAllText((Join-Path $evidence 'COMMIT_SHA.txt'), "$sha`n", [Text.UTF8Encoding]::new($false))
@{ branch = (git branch --show-current); commit = $sha; utc = [DateTime]::UtcNow.ToString('o'); workflow = 'final-main-theorem-audit' } |
  ConvertTo-Json | Set-Content -Encoding UTF8 (Join-Path $evidence 'RUN_CONTEXT.json')
@("OS=$([Environment]::OSVersion)", "PowerShell=$($PSVersionTable.PSVersion)", "LeanToolchain=$((Get-Content lean-toolchain -Raw).Trim())", "Python=$(& $python --version 2>&1)") |
  Set-Content -Encoding UTF8 (Join-Path $evidence 'ENVIRONMENT.txt')

Invoke-Logged 'FROZEN_SOURCE_REPORT.txt' { & $python verification/final/check_frozen_sources.py }
Invoke-Logged 'PROOF_DEBT_REPORT.txt' { & powershell -NoProfile -ExecutionPolicy Bypass -File verification/final/ProofDebtGate.ps1 }
Invoke-Logged 'DEPENDENCY_REPORT.txt' { & powershell -NoProfile -ExecutionPolicy Bypass -File verification/final/DependencyGate.ps1 }
Invoke-Logged 'ROOT_BUILD_LOG.txt' { & $lake build }
Invoke-Logged 'FINAL_BUILD_LOG.txt' { & $lake build P21.MainTheorem }
Invoke-Logged 'FINAL_STATEMENT_LOG.txt' { & $lake env lean verification/final/MainStatementGate.lean }

$axiomOutput = @(& $lake env lean verification/final/audit_axioms.lean 2>&1)
$axiomCode = $LASTEXITCODE
@($axiomOutput | ForEach-Object { $_.ToString() }) + "EXIT=$axiomCode" |
  Set-Content -Encoding UTF8 (Join-Path $evidence 'AXIOM_REPORT.txt')
if ($axiomCode -ne 0) { throw 'Final axiom audit failed' }
$allowed = @('propext', 'Classical.choice', 'Quot.sound')
$found = [regex]::Matches(($axiomOutput -join "`n"), 'depends on axioms:\s*\[([^\]]*)\]') |
  ForEach-Object { $_.Groups[1].Value -split ',' } | ForEach-Object { $_.Trim() } | Where-Object { $_ } | Select-Object -Unique
$unexpected = @($found | Where-Object { $_ -notin $allowed })
if ($unexpected.Count -or ($axiomOutput -join "`n") -match 'sorryAx') { throw "Unexpected axioms: $($unexpected -join ', ')" }

Invoke-Logged 'C10_FULL_VERIFICATION_LOG.txt' { & powershell -NoProfile -ExecutionPolicy Bypass -File verification/c10/verify.ps1 }

$groups = [ordered]@{
  'M1_REGRESSION_LOG.txt' = @('verification/StatementCheck.lean')
  'M2A_REGRESSION_LOG.txt' = @('verification/m2/StableCoreRegression.lean', 'verification/m2/BranchIIRegression.lean', 'verification/m2/GlueRegression.lean')
  'M2B_REGRESSION_LOG.txt' = @('verification/m2b/Regression.lean')
  'M3A_REGRESSION_LOG.txt' = @('verification/m3/M3Regression.lean', 'verification/m3/ExtractionRegression.lean')
  'M3B1_REGRESSION_LOG.txt' = @('verification/m3b1/StatementRegression.lean')
  'M3B2_REGRESSION_LOG.txt' = @(Get-ChildItem verification/m3b2 -Filter '*Regression.lean' | Sort-Object Name | ForEach-Object { $_.FullName })
  'P5_REGRESSION_LOG.txt' = @('verification/p5/StatementGate.lean', 'verification/p5/Regression.lean')
  'T6_REGRESSION_LOG.txt' = @('verification/t6/StatementGate.lean', 'verification/t6/Regression.lean')
  'C7_REGRESSION_LOG.txt' = @('verification/c7/StatementGate.lean', 'verification/c7/Regression.lean')
  'C8_REGRESSION_LOG.txt' = @('verification/c8/StatementGate.lean', 'verification/c8/Regression.lean')
  'C9_REGRESSION_LOG.txt' = @('verification/c9/StatementGate.lean', 'verification/c9/Regression.lean')
  'C10_REGRESSION_LOG.txt' = @('verification/c10/IntegrationGate.lean')
}
foreach ($entry in $groups.GetEnumerator()) {
  $files = $entry.Value
  Invoke-Logged $entry.Key { foreach ($file in $files) { & $lake env lean $file; if ($LASTEXITCODE -ne 0) { return } } }
}

Invoke-Logged 'LINEAR_CERTIFICATE_REPORT.txt' { & $python verification/c9/generate_linear_certificate.py --check }
Invoke-Logged 'EUCLIDEAN_CERTIFICATE_REPORT.txt' { & $python verification/c10/generate_euclidean_certificate.py --check }

$pydeps = Join-Path $PSScriptRoot '.pydeps'
if (-not (Test-Path -LiteralPath (Join-Path $pydeps 'sympy'))) {
  & $python -m pip install --disable-pip-version-check --no-compile --target $pydeps sympy==1.14.0
  if ($LASTEXITCODE -ne 0) { throw 'SymPy 1.14.0 installation failed' }
}
$oldPythonPath = $env:PYTHONPATH
$env:PYTHONPATH = $pydeps
try { Invoke-Logged 'SYMBOLIC_VERIFIERS_LOG.txt' { & $python verification/final/run_symbolic_verifiers.py } }
finally { $env:PYTHONPATH = $oldPythonPath }

Copy-Item FINAL_SECTION11_STATEMENT_MAP.md (Join-Path $evidence 'FINAL_SECTION11_STATEMENT_MAP.md')
'Source and evidence manifests are generated after every other evidence file.' | Set-Content -Encoding UTF8 (Join-Path $evidence 'SOURCE_MANIFEST_BUILD_LOG.txt')
'Manifest verification is the final evidence gate.' | Set-Content -Encoding UTF8 (Join-Path $evidence 'MANIFEST_VERIFICATION_LOG.txt')
& $python verification/final/make_manifests.py
if ($LASTEXITCODE -ne 0) { throw 'Manifest generation failed' }
& $python verification/final/make_manifests.py --verify
if ($LASTEXITCODE -ne 0) { throw 'Manifest verification failed' }
Write-Output 'FINAL SECTION 11 FULL LOCAL VERIFICATION PASS'
