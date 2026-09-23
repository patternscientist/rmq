[CmdletBinding()]
param(
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{40}$')][string]$CandidateRef,
 [Parameter(Mandatory=$true)][string]$ArtifactDirectory,
 [Parameter(Mandatory=$true)][ValidatePattern('^[0-9a-f]{64}$')][string]$BuildReceiptSHA256,
 [string]$Name='final',
 [string]$LeanPath='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repo=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../..'))
if($Name -cnotmatch '^[a-z0-9-]{1,20}$'){throw 'OPT1-R1-PREPARE: invalid private name'}
$out=Join-Path $repo ('.lake/r1/prepare-'+$Name)
if(Test-Path -LiteralPath $out){throw 'OPT1-R1-PREPARE: output already exists'}
[void][IO.Directory]::CreateDirectory($out)
$utf8=[Text.UTF8Encoding]::new($false,$true)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$git=Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application) 'git'
$shell=(Get-Process -Id $PID).Path
$results=[Collections.Generic.List[object]]::new()
function Run-Prepare([string]$Stage,[string]$Exe,[string[]]$Arguments,[string]$Directory,[int]$Deadline=180){
 $r=Invoke-RMQOwnedBoundedProcess -FilePath $Exe -Arguments $Arguments -WorkingDirectory $Directory -Stage $Stage `
  -DeadlineSeconds $Deadline -OutputLimitBytes 8388608 -TempRoot (Join-Path $out 'process') -Environment @{GIT_OPTIONAL_LOCKS='0'}
 $row=[ordered]@{Stage=$Stage;Executable=$Exe;Arguments=$Arguments;Directory=$Directory;Result=$r}
 $results.Add($row)
 [IO.File]::WriteAllText((Join-Path $out ($Stage+'.json')),($row|ConvertTo-Json -Depth 12),$utf8)
 if($r.ExitCode -ne 0 -or $r.TimedOut -or $r.OutputLimitExceeded){throw "OPT1-R1-PREPARE: $Stage failed"}
 return $r
}
$checkouts=[ordered]@{}
foreach($profile in @('lf','windows')){
 $root=Join-Path $repo ('.lake/r1/'+$Name+'-'+$profile)
 if(Test-Path -LiteralPath $root){throw 'OPT1-R1-PREPARE: private checkout already exists; choose a fresh Name'}
 [void][IO.Directory]::CreateDirectory($root)
 $null=Run-Prepare ($profile+'-init') $git @('init',$root) $repo
 $null=Run-Prepare ($profile+'-fetch') $git @('-C',$root,'fetch','--depth=1','--no-tags',$repo,$CandidateRef) $repo
 $crlf=if($profile -ceq 'lf'){'false'}else{'true'}
 $null=Run-Prepare ($profile+'-config') $git @('-C',$root,'config','core.autocrlf',$crlf) $repo
 $null=Run-Prepare ($profile+'-checkout') $git @('-C',$root,'-c','core.excludesfile=','checkout','--detach',$CandidateRef) $repo
 $wrapper=Join-Path $out ($profile+'-install.ps1')
 [IO.File]::WriteAllText($wrapper,@'
param([string]$Root,[string]$Artifacts,[string]$Pin,[string]$Lean)
$ErrorActionPreference='Stop'
. (Join-Path $Root 'scripts/packed_optimized_replay_profile.ps1')
$result=Install-OPT1ReplayArtifacts -RepoRoot $Root -LeanPath $Lean -ExpectedReceiptSHA256 $Pin -ArtifactDirectory $Artifacts
$result|ConvertTo-Json -Depth 10
'@,$utf8)
 $install=Run-Prepare ($profile+'-install') $shell @('-NoProfile','-File',$wrapper,'-Root',$root,'-Artifacts',$ArtifactDirectory,'-Pin',$BuildReceiptSHA256,'-Lean',$LeanPath) $root 1200
 $status=Run-Prepare ($profile+'-status') $git @('-c','core.excludesfile=','status','--porcelain') $root
 if(@($status.StandardOutput).Count -ne 0){throw 'OPT1-R1-PREPARE: installed checkout is dirty'}
 $sample=[IO.File]::ReadAllBytes((Join-Path $root 'RMQ/Core/WordRAM/Optimization/BranchBound.lean'))
 $sampleText=$utf8.GetString($sample)
 $crlfCount=[regex]::Matches($sampleText,"`r`n").Count
 $lfCount=[regex]::Matches($sampleText,"(?<!`r)`n").Count
 if(($profile -ceq 'lf' -and ($crlfCount -ne 0 -or $lfCount -ne 338)) -or
   ($profile -ceq 'windows' -and ($crlfCount -ne 338 -or $lfCount -ne 0))){throw 'OPT1-R1-PREPARE: actual checkout serialization differs'}
 $checkouts[$profile]=[ordered]@{Root=$root;CandidateRef=$CandidateRef;CoreAutocrlf=$crlf;BranchBoundCRLF=$crlfCount;BranchBoundLF=$lfCount;BuildReceiptSHA256=$BuildReceiptSHA256;IndependentArtifactCopies=$true;Clean=$true}
}
$summary=[ordered]@{CandidateRef=$CandidateRef;SourceCommit='aecf4a580c591e8f694a3699e19e843198089194';
 BuildReceiptSHA256=$BuildReceiptSHA256;ArtifactDirectory=$ArtifactDirectory;Checkouts=$checkouts;
 Stages=@($results);Mode='Independent private installation of the versioned actual canonical compilation artifacts';POSIX='UNEXECUTED'}
[IO.File]::WriteAllText((Join-Path $out 'RESULT.json'),($summary|ConvertTo-Json -Depth 16),$utf8)
Write-Host "OPT1-R1-PREPARE PASS LF=$($checkouts.lf.Root) WINDOWS=$($checkouts.windows.Root)"
