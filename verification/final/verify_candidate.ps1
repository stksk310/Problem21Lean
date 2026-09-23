param([string]$Archive = 'delivery/P21_LEAN_FINAL_MAIN_THEOREM_CANDIDATE_20260923.zip')
$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
$archivePath = (Resolve-Path (Join-Path $root $Archive)).Path
$extract = Join-Path $root '.superpowers/sdd/2026-09-23-final-main-theorem/candidate_extract'
if (Test-Path -LiteralPath $extract) { Remove-Item -Recurse -Force -LiteralPath $extract }
New-Item -ItemType Directory -Path $extract -Force | Out-Null
Expand-Archive -LiteralPath $archivePath -DestinationPath $extract -Force

$manifest = Get-Content -LiteralPath (Join-Path $extract 'FINAL_CANDIDATE_SOURCE_SHA256.json') -Raw | ConvertFrom-Json
$bad = @()
foreach ($entry in $manifest.PSObject.Properties) {
  $path = Join-Path $extract $entry.Name
  if (-not (Test-Path -LiteralPath $path) -or (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash.ToLowerInvariant() -ne $entry.Value) { $bad += $entry.Name }
}
if ($bad.Count) { throw "Extracted source hash mismatch: $($bad -join ', ')" }

$sourcePackages = Join-Path $root '.lake/packages'
$targetLake = Join-Path $extract '.lake'
New-Item -ItemType Directory -Path $targetLake -Force | Out-Null
$targetPackages = Join-Path $targetLake 'packages'
if ($IsWindows -or $env:OS -eq 'Windows_NT') {
  New-Item -ItemType Junction -Path $targetPackages -Target $sourcePackages | Out-Null
} else {
  New-Item -ItemType SymbolicLink -Path $targetPackages -Target $sourcePackages | Out-Null
}

$userHome = if ($env:USERPROFILE) { $env:USERPROFILE } else { $env:HOME }
$env:ELAN_HOME = Join-Path $userHome '.elan'
$env:GIT_CONFIG_COUNT = '1'; $env:GIT_CONFIG_KEY_0 = 'safe.directory'; $env:GIT_CONFIG_VALUE_0 = '*'
$lake = (Get-Command lake -ErrorAction SilentlyContinue).Source
if (-not $lake) { $lake = Join-Path $env:ELAN_HOME 'bin/lake.exe' }
$python = if (Get-Command python3 -ErrorAction SilentlyContinue) { (Get-Command python3).Source } else { 'python' }

Push-Location $extract
try {
  & $python verification/c9/generate_linear_certificate.py --check
  if ($LASTEXITCODE -ne 0) { throw 'Extracted LINEAR regeneration failed' }
  & $python verification/c10/generate_euclidean_certificate.py --check
  if ($LASTEXITCODE -ne 0) { throw 'Extracted EUCLIDEAN regeneration failed' }
  & $lake build P21.MainTheorem
  if ($LASTEXITCODE -ne 0) { throw 'Extracted final theorem build failed' }
  & $lake env lean verification/final/MainStatementGate.lean
  if ($LASTEXITCODE -ne 0) { throw 'Extracted final statement gate failed' }
} finally { Pop-Location }
Write-Output "FRESH EXTRACTION PASS ($($manifest.PSObject.Properties.Count) source files)"
