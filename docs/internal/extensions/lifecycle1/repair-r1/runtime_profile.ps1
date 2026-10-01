function Assert-LifecycleRepairRuntime([string]$Shell,[string]$Profile) {
  $profiles=@{
    pwsh=@{path='C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe';
      sha256='362a356ce7f0940ec74f73a8fc2c990a2cc24a38a11c90bbd8eca947110ad139';version='7.6.5';dotnet='10.0.11';edition='Core'}
    winps=@{path='C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe';
      sha256='8bb6fa8c283b4d92120b1ef249a9b311b0f804d4cabbe9981159976c8be76a5e';version='5.1.26100.9444';dotnet='4.0.30319.42000';edition='Desktop'}
  }
  if(-not $profiles.ContainsKey($Profile)){throw 'L1R1-RUNTIME: unknown profile'}
  $expected=$profiles[$Profile]
  $actual=(Get-Process -Id $PID).Path
  if([IO.Path]::GetFullPath($Shell) -ine [IO.Path]::GetFullPath($expected.path) -or
     [IO.Path]::GetFullPath($actual) -ine [IO.Path]::GetFullPath($expected.path)) {
    throw 'L1R1-RUNTIME: profile executable path mismatch'
  }
  if((Get-FileHash -LiteralPath $actual).Hash.ToLowerInvariant() -cne $expected.sha256 -or
     $PSVersionTable.PSVersion.ToString() -cne $expected.version -or
     [Environment]::Version.ToString() -cne $expected.dotnet -or $PSVersionTable.PSEdition -cne $expected.edition) {
    throw 'L1R1-RUNTIME: profile executable hash or runtime version mismatch'
  }
  return [ordered]@{profile=$Profile;path=$actual;sha256=$expected.sha256;version=$expected.version;dotnet=$expected.dotnet;edition=$expected.edition}
}
