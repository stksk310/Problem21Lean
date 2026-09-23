$ErrorActionPreference = 'Stop'
$root = (Resolve-Path (Join-Path $PSScriptRoot '../..')).Path
Set-Location $root

$oldLean = @(git ls-tree -r --name-only e4799d8044fd524a94b960ab19c333b08a8c93bb | Where-Object { $_ -like '*.lean' })
if ($LASTEXITCODE -ne 0) { throw 'Unable to enumerate frozen Lean sources.' }

$reverse = @()
foreach ($path in $oldLean) {
  if (Select-String -LiteralPath $path -Pattern '^\s*import\s+P21\.MainTheorem\s*$' -Quiet) {
    $reverse += $path
  }
}
if ($reverse.Count) { throw "Reverse dependency on P21.MainTheorem: $($reverse -join ', ')" }

$source = Get-Content -LiteralPath P21/MainTheorem.lean -Raw
foreach ($required in @(
  'import P21.Symmetric.FullClosure',
  'import P21.Nonsymmetric.Chain.C10.Integration',
  'P21.Symmetric.symmetric_tail_type_le_four',
  'P21.Nonsymmetric.nonsymmetric_Q_ge_four_impossible_after_chain',
  's.semigroup.type_eq_q_card_add_one')) {
  if (-not $source.Contains($required)) { throw "Missing final dependency: $required" }
}
if ($source -match 'ncard\s*=\s*4|4\s*=\s*\([^\r\n]*Q') {
  throw 'Cardinality firewall failed: equality-to-four assumption detected.'
}
Write-Output "DEPENDENCY PASS ($($oldLean.Count) frozen Lean sources; no reverse import)"
