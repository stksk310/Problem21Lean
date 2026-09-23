$ErrorActionPreference = 'Stop'
$source = Get-Content -LiteralPath (Join-Path $PSScriptRoot '../../P21/MainTheorem.lean') -Raw
$forbidden = @('\bsorry\b', '\badmit\b', '\baxiom\b', '\bunsafe\b', 'native_decide', 'run_tac')
foreach ($pattern in $forbidden) {
  if ($source -match $pattern) { throw "Proof-debt token found: $pattern" }
}
Write-Output 'PROOF DEBT PASS (no forbidden token in P21/MainTheorem.lean)'

