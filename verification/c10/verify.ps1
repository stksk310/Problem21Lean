$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
Set-Location $root
$env:ELAN_HOME = "$env:USERPROFILE\.elan"
$lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
$lake = if ($lakeCommand) { $lakeCommand.Source } else { 'C:\Users\stksk\.elan\bin\lake.exe' }
$bundledPython = 'C:\Users\stksk\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
$python3 = Get-Command python3 -ErrorAction SilentlyContinue
$python = if (Test-Path -LiteralPath $bundledPython) { $bundledPython } elseif ($python3) {
  $python3.Source
} else { 'python' }

function Invoke-Checked([string]$label, [scriptblock]$command) {
  Write-Output "== $label =="
  & $command
  if ($LASTEXITCODE -ne 0) { throw "$label failed with exit $LASTEXITCODE" }
}

function Get-Sha256([string]$path) {
  $stream = [System.IO.File]::OpenRead($path)
  try {
    $sha = [System.Security.Cryptography.SHA256]::Create()
    try { return ([BitConverter]::ToString($sha.ComputeHash($stream))).Replace('-', '').ToLowerInvariant() }
    finally { $sha.Dispose() }
  }
  finally { $stream.Dispose() }
}

$manifest = Get-Content verification/c10/SOURCE_INTEGRITY_SHA256.json -Raw | ConvertFrom-Json
$bad = @()
foreach ($entry in $manifest.files.PSObject.Properties) {
  $path = Join-Path $root $entry.Name
  if (-not (Test-Path -LiteralPath $path)) { $bad += $entry.Name; continue }
  $actual = Get-Sha256 $path
  if ($actual -ne $entry.Value) { $bad += $entry.Name }
}
if ($bad.Count) { throw "FROZEN source changed: $($bad -join ', ')" }
$sourceCount = @($manifest.files.PSObject.Properties).Count
Write-Output "SOURCE INTEGRITY PASS ($sourceCount files)"

Invoke-Checked 'certificate unit tests' { & $python -m unittest verification.c10.test_generate_euclidean_certificate -v }
Invoke-Checked 'certificate byte check' { & $python verification/c10/generate_euclidean_certificate.py --check }

$c10Sources = Get-ChildItem P21/Nonsymmetric/Chain/C10 -Filter '*.lean' -File
$forbidden = '\b(sorry|admit|axiom|sorryAx|native_decide|run_tac)\b|\bunsafe\s+(theorem|def)\b'
$debt = $c10Sources | Select-String -Pattern $forbidden
if ($debt) { $debt | ForEach-Object { Write-Error $_ }; throw 'proof debt detected' }
$oldSources = $manifest.files.PSObject.Properties.Name
$reverse = Select-String -Path $oldSources -Pattern '^import P21\.Nonsymmetric\.Chain\.C10' -ErrorAction Stop
if ($reverse) { throw 'reverse dependency into C10 detected' }
Write-Output 'PROOF DEBT / DEPENDENCY PASS'

Invoke-Checked 'root build' { & $lake build }
$gates = @(
  'verification/c10/CanonicalFreeGate.lean',
  'verification/c10/AlgebraGate.lean',
  'verification/c10/TerminalCertificateGate.lean',
  'verification/c10/TerminalActualityGate.lean',
  'verification/c10/ExchangeGate.lean',
  'verification/c10/DescentGate.lean',
  'verification/c10/IntegrationGate.lean'
)
foreach ($gate in $gates) { Invoke-Checked $gate { & $lake env lean $gate } }

Write-Output '== verification/c10/audit_axioms.lean =='
$axiomOutput = @(& $lake env lean verification/c10/audit_axioms.lean 2>&1)
if ($LASTEXITCODE -ne 0) { throw 'axiom audit failed' }
$axiomOutput | Write-Output
$allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
$joinedAxioms = $axiomOutput -join "`n"
$foundAxioms = [regex]::Matches($joinedAxioms, 'depends on axioms:\s*\[([^\]]*)\]') |
  ForEach-Object { $_.Groups[1].Value -split ',' } | ForEach-Object { $_.Trim() } |
  Where-Object { $_ } | Select-Object -Unique
$unexpected = @($foundAxioms | Where-Object { $_ -notin $allowedAxioms })
if ($unexpected.Count) { throw "unexpected axioms: $($unexpected -join ', ')" }
if ($joinedAxioms -match 'sorryAx') { throw 'sorryAx detected in axiom audit' }
Write-Output 'AXIOM AUDIT PASS'

$regressions = @(
  'verification/StatementCheck.lean',
  'verification/m2/GlueRegression.lean',
  'verification/m2b/Regression.lean',
  'verification/m3/M3Regression.lean',
  'verification/m3b1/StatementRegression.lean',
  'verification/m3b2/StatementRegression.lean',
  'verification/p5/Regression.lean',
  'verification/t6/Regression.lean',
  'verification/c7/Regression.lean',
  'verification/c8/Regression.lean',
  'verification/c9/Regression.lean'
)
foreach ($gate in $regressions) { Invoke-Checked $gate { & $lake env lean $gate } }
Write-Output 'C10 FULL LOCAL VERIFICATION PASS'
