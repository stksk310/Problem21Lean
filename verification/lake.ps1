$env:ELAN_HOME = 'C:\Users\stksk\.elan'
$p21Packages = @('mathlib','plausible','LeanSearchClient','importGraph','proofwidgets','aesop','Qq','batteries','Cli')
$env:GIT_CONFIG_COUNT = [string]$p21Packages.Count
for ($p21Index = 0; $p21Index -lt $p21Packages.Count; $p21Index++) {
  [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$p21Index", 'safe.directory', 'Process')
  [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$p21Index", "C:/LeanProjects/MLRLean/.lake/packages/$($p21Packages[$p21Index])", 'Process')
}
& 'C:\Users\stksk\.elan\toolchains\leanprover--lean4---v4.34.0-rc1\bin\lake.exe' @args
exit $LASTEXITCODE
