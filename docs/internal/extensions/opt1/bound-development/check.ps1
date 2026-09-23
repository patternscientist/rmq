# BranchBound development verification only. Not an OPT-1 acceptance replay.
param([string[]]$Modules = @('Primitive','Calculus','Structured','Compiler'))
$ErrorActionPreference = 'Stop'
$repo = (Get-Location).Path
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$lean = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
$cache = Join-Path $repo '.lake/build/lib/lean'
$evidence = Join-Path $repo 'docs/internal/extensions/opt1/bound-development'
foreach ($module in $Modules) {
  $relative = if ($module -eq 'BranchBound') { 'RMQ/Core/WordRAM/Optimization/BranchBound' } elseif ($module -eq 'Axioms') { 'docs/internal/extensions/opt1/bound-development/Axioms' } else { 'RMQ/Core/WordRAM/Packed/' + $module }
  $source = Join-Path $repo ($relative + '.lean')
  $artifact = Join-Path $cache ($relative + '.olean')
  [void](New-Item -ItemType Directory -Path ([IO.Path]::GetDirectoryName($artifact)) -Force)
  $result = Invoke-RMQOwnedBoundedProcess -FilePath $lean -Arguments @('-j1','-o',$artifact,$source) -WorkingDirectory $repo -Stage ('bound-' + $module) -DeadlineSeconds 180 -OutputLimitBytes 1048576 -TempRoot (Join-Path $evidence 'process-temp') -Environment @{ LEAN_PATH = $cache }
  $record = [ordered]@{ Command = @($lean,'-j1','-o',$artifact,$source); SourceSHA256 = (Get-FileHash -Algorithm SHA256 -LiteralPath $source).Hash; Base = '0e6a00f654abc64f8b68988fa9675b9a839dca2f'; Platform = [Environment]::OSVersion.VersionString; Result = $result }
  $stamp = [DateTime]::UtcNow.ToString('yyyyMMdd-HHmmss-fff')
  $record | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath (Join-Path $evidence ($stamp + '-' + $module + '.json')) -Encoding utf8
  $result | ConvertTo-Json -Depth 4
  if ($result.ExitCode -ne 0 -or $result.TimedOut -or $result.OutputLimitExceeded) { exit 1 }
}
