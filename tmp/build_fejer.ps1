param([string]$LeanFile = "Problems/Juggler/PaperECompletion.lean", [switch]$Build)
$env:ELAN_HOME="C:/Users/phili/.elan"
$env:PATH="C:/Users/phili/.elan/bin;"+$env:PATH
$paperERoot="C:/Users/phili/Desktop/balanced_ternary"
$paperERepos=@($paperERoot)+@(Get-ChildItem -LiteralPath "$paperERoot/formal/.lake/packages" -Directory | ForEach-Object FullName)
$env:GIT_CONFIG_COUNT=[string]$paperERepos.Count
for($paperEIndex=0;$paperEIndex -lt $paperERepos.Count;$paperEIndex++){
 [Environment]::SetEnvironmentVariable("GIT_CONFIG_KEY_$paperEIndex","safe.directory","Process")
 [Environment]::SetEnvironmentVariable("GIT_CONFIG_VALUE_$paperEIndex",$paperERepos[$paperEIndex].Replace("\","/"),"Process")
}
Set-Location "$paperERoot/formal"
& lake build
exit $LASTEXITCODE
