$ErrorActionPreference='Stop'
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
Set-Location -LiteralPath $repo
$base='9519b2c1af5e2cf59536b311db5e8dc81376a32f'
$out=Join-Path $repo ('.lake/repair-r1/final-checks-'+[Guid]::NewGuid().ToString('N'))
[void][IO.Directory]::CreateDirectory($out)
$checks=[Collections.Generic.List[object]]::new()
function Check([string]$Name,[string]$File,[string[]]$Arguments,[int]$Expected=0,[switch]$Empty) {
  $watch=[Diagnostics.Stopwatch]::StartNew()
  $lines=@(& $File @Arguments 2>&1|ForEach-Object {"$_"});$code=$LASTEXITCODE
  $watch.Stop()
  [IO.File]::WriteAllLines((Join-Path $out ($Name+'.log')),[string[]]$lines,[Text.UTF8Encoding]::new($false))
  $checks.Add(@{name=$Name;file=$File;arguments=$Arguments;exit=$code;expected=$Expected;seconds=$watch.Elapsed.TotalSeconds;log=(Join-Path $out ($Name+'.log'))})
  if($code -ne $Expected -or ($Empty -and $lines.Count)){throw "check failed $Name exit=$code; $($lines -join ' | ')"}
  Write-Output ('CHECK PASS '+$Name)
}
Check 'contract' 'python' @((Join-Path $PSScriptRoot '../repair-r3/verify_contract.py'),'--output',(Join-Path $out 'CONTRACT.json'))
Check 'hygiene' 'rg' @('-n','\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib','RMQ','lakefile.toml') 1 -Empty
Check 'native-decision' 'rg' @('-n','native_decide|Lean\.ofReduceBool','RMQ') 1 -Empty
Check 'working-whitespace' 'git' @('diff','--check')
Check 'range-whitespace' 'git' @('diff','--check',($base+'..HEAD'))
$shell=(Get-Process -Id $PID).Path
Check 'design-whole' $shell @('-NoProfile','-File','scripts/design_decision_check.ps1','-Strict','-Base',$base)
$commits=@(& git rev-list --reverse ($base+'..HEAD'))
foreach($commit in $commits) {
  $parent=(& git rev-parse ($commit+'^')).Trim()
  Check ('design-'+$commit.Substring(0,12)) $shell @('-NoProfile','-File','scripts/design_decision_check.ps1','-Strict','-Base',$parent,'-Head',$commit)
}
Check 'clean' 'git' @('-c','core.excludesfile=','status','--porcelain=v1','--untracked-files=all') 0 -Empty
$pins=@(Get-ChildItem -LiteralPath $out -File|ForEach-Object {@{path=$_.FullName;bytes=$_.Length;sha256=(Get-FileHash $_.FullName).Hash}})
$record=@{head=(& git rev-parse HEAD).Trim();base=$base;checks=@($checks.ToArray());pins=$pins}
[IO.File]::WriteAllText((Join-Path $out 'RESULTS.json'),($record|ConvertTo-Json -Depth 12),[Text.UTF8Encoding]::new($false))
Write-Output ('FINAL CHECKS evidence='+$out)
