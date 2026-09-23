#!/usr/bin/env pwsh
[CmdletBinding()]
param(
  [AllowEmptyString()][string]$OnlyCase,
  [switch]$SelectorProbeOnly,
  [string]$RawCheckout,
  [string]$WindowsCheckout,
  [string]$ArtifactDirectory,
  [ValidateRange(30,21600)][int]$CampaignDeadlineSeconds=14400
)
$ErrorActionPreference='Stop'
Set-StrictMode -Version Latest
$repoRoot=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$utf8=[Text.UTF8Encoding]::new($false,$true)
$registryPath='docs/internal/extensions/opt1/repair-r1/REGISTRY.json'
$version='opt1-r1-production-v4'
$registrySHA256='59db124f0a3b42057977e2613bc0fb841ec62c8cebd2e0e5bfd5003cfe4f9c0e'
# Independent exact literals. Registry corruption cannot redefine expectations.
$ids=@(
 'P01-LIBRARY-LF','P02-LIBRARY-WINDOWS','P03-WEAKEN-LF','P04-WEAKEN-WINDOWS',
 'P05-SOURCE-TOKEN','P06-ARTIFACT-TOKEN','P07-ARTIFACT-MISSING','P08-ARTIFACT-STALE',
 'P09-SOURCE-PROFILE','P10-BUILD-RECEIPT','P11-TOOLCHAIN-TEXT','P12-IMPORT-OMITTED',
 'P13-IMPORT-DUPLICATE','P14-SOURCE-SPACE','P15-SOURCE-UTF8','P16-SOURCE-BOM',
 'P17-SOURCE-BARE-CR','P18-LEAN-EXECUTABLE',
 'P19-EXTRA-ARTIFACT','P20-SHADOW-DIRECTORY','P21-ARTIFACT-SIDECAR',
 'C01-OMITTED','C02-VALID','C03-EMPTY','C04-WHITESPACE','C05-PADDED',
 'C06-MALFORMED','C07-UNKNOWN','C08-CONTRADICTORY','C09-MIDDLE-OMITTED','C10-MIDDLE-DUPLICATE',
 'R01-OMITTED','R02-VALID','R03-EMPTY','R04-WHITESPACE','R05-PADDED',
 'R06-MALFORMED','R07-UNKNOWN','R08-MIDDLE-OMITTED','R09-MIDDLE-DUPLICATE',
 'V01-SOLE-SETUP','V02-MIXED-STDOUT','V03-SUCCESS-STDOUT','V04-WRONG-STDERR',
 'V05-ALLOWED-PROGRESS','V06-DUPLICATE-PROGRESS','V07-REORDERED-PROGRESS',
 'V08-EXTRA-STDERR','V09-PREFIX-HOLDOUT'
)
$onlyBound=$PSBoundParameters.ContainsKey('OnlyCase')
$stages=[Collections.Generic.List[object]]::new()
$executed=[Collections.Generic.List[string]]::new()
$clock=[Diagnostics.Stopwatch]::StartNew()
$out=$null
$exitCode=0

function Assert-R1Exact([string[]]$Actual,[string[]]$Expected,[string]$Label) {
 if($Expected.Count -eq 0 -or $Actual.Count -ne $Expected.Count -or
   @($Actual|Select-Object -Unique).Count -ne $Actual.Count -or
   ($Actual -join "`n") -cne ($Expected -join "`n")){throw "OPT1-R1-REGISTRY: $Label missing/duplicate/changed/reordered"}
}
function Get-R1Selection {
 if(-not $onlyBound){return $ids}
 if([string]::IsNullOrWhiteSpace($OnlyCase)){throw 'OPT1-R1-SELECTOR: explicitly empty selector'}
 if($OnlyCase -cnotmatch '^[PCRV][0-9]{2}-[A-Z][A-Z0-9-]*$'){throw 'OPT1-R1-SELECTOR: malformed selector'}
 if($ids -cnotcontains $OnlyCase){throw "OPT1-R1-SELECTOR: unknown selector $OnlyCase"}
 return @($OnlyCase)
}
function Write-R1Json([string]$Name,[object]$Value) {
 [IO.File]::WriteAllText((Join-Path $out $Name),($Value|ConvertTo-Json -Depth 24),$utf8)
}
function Invoke-R1Tool([string]$Name,[string]$File,[string[]]$Arguments,[string]$Directory,[int]$Deadline=900) {
 $remaining=$CampaignDeadlineSeconds-[int][Math]::Ceiling($clock.Elapsed.TotalSeconds)
 if($remaining -le 0){throw 'OPT1-R1-PROCESS: campaign deadline exhausted before launch'}
 $result=Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments -WorkingDirectory $Directory `
   -Stage $Name -DeadlineSeconds ([Math]::Min($remaining,$Deadline)) -OutputLimitBytes 8388608 `
   -TempRoot (Join-Path $out 'owned') -Environment @{GIT_OPTIONAL_LOCKS='0'}
 $record=[ordered]@{Name=$Name;Executable=$File;Arguments=$Arguments;Directory=$Directory;Result=$result}
 $stages.Add($record)
 Write-R1Json ($Name+'.json') $record
 [IO.File]::WriteAllLines((Join-Path $out ($Name+'.stdout.log')),[string[]]$result.StandardOutput,$utf8)
 [IO.File]::WriteAllLines((Join-Path $out ($Name+'.stderr.log')),[string[]]$result.StandardError,$utf8)
 if($result.TimedOut -or $result.OutputLimitExceeded){throw "OPT1-R1-PROCESS: $Name timeout/output ceiling; no verdict credited"}
 return $result
}
function Assert-R1Verdict([object]$Result,[int]$Exit,[string]$Token,[switch]$Boundary) {
 if($Result.ExitCode -ne $Exit){throw "OPT1-R1-VERDICT: $($Result.Stage) wrong exit=$($Result.ExitCode) expected=$Exit"}
 $lines=if($Exit -eq 0){@($Result.StandardOutput)}else{@($Result.StandardError)}
 $matches=@($lines|Where-Object {$_.StartsWith($Token,[StringComparison]::Ordinal)})
 if($matches.Count -ne 1){throw "OPT1-R1-VERDICT: $($Result.Stage) expected one diagnostic/receipt '$Token'"}
 if($Exit -eq 0 -and @($Result.StandardError).Count -ne 0){throw 'OPT1-R1-VERDICT: positive stderr'}
 if($Exit -ne 0){
  if(@($Result.StandardError).Count -ne 1 -or $Result.StandardError[0] -cne $Token){
   throw 'OPT1-R1-VERDICT: wrong or unrelated failure diagnostic'
  }
  # The complete stdout grammar for a failed library setup contains only these
  # ordered progress/restoration records. No diagnostic or semantic success is
  # allowed to hide beside the exact stderr failure. Empty transport lines are
  # already removed by the unchanged owned-process reader.
  $last=-2
  foreach($line in @($Result.StandardOutput)){
   $position=if($line -cmatch '^OPT1-CERT-ARTIFACTS [^\r\n]+[\\/]\.lake[\\/]oc[\\/][0-9a-f]{12}$'){-1}
    elseif($line -cmatch '^OPT1-CERT-STAGE tracked-source-status-before deadline=[1-9][0-9]*s$'){0}
    elseif($line -cmatch '^OPT1-CERT-STAGE import-freshness deadline=[1-9][0-9]*s$'){1}
    elseif($line -cmatch '^OPT1-CERT-STAGE tracked-source-status-after deadline=[1-9][0-9]*s$'){2}
    elseif($line -ceq 'OPT1-CERT-ORIGINALS PASS source SHA256 unchanged; mutations applied/restored only in isolated copies'){3}
    else{throw 'OPT1-R1-VERDICT: unrelated stdout on rejected setup'}
   if($position -le $last){throw 'OPT1-R1-VERDICT: duplicate or reordered setup progress'}
   $last=$position
  }
 }
 if($Boundary -and (@($Result.StandardOutput).Count -ne $(if($Exit -eq 0){1}else{0}))){
  throw 'OPT1-R1-VERDICT: extra selector/registry output'
 }
 if($Boundary -and (($Result.Output -join "`n") -match 'OPT1-(CERT-)?STAGE|OPT1-CERT CASE|OPT1-R1 CASE')){
  throw 'OPT1-R1-VERDICT: selector/registry control reached execution'
 }
}
function Get-R1Fixture([bool]$Raw) {
 $candidate=if($Raw){$RawCheckout}else{$WindowsCheckout}
 if([string]::IsNullOrWhiteSpace($candidate)){throw 'OPT1-R1-FIXTURE: provide both documented private checkout paths for production controls'}
 $full=[IO.Path]::GetFullPath($candidate)
 $prefix=[IO.Path]::GetFullPath((Join-Path $repoRoot '.lake')).TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar
 if(-not $full.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase) -or -not (Test-Path -LiteralPath (Join-Path $full '.git') -PathType Container)){
  throw 'OPT1-R1-FIXTURE: expected an owned private checkout below this task .lake'
 }
 return $full
}
function Get-R1Tracked([string]$Name,[string]$Root) {
 $r=Invoke-R1Tool $Name $git @('-c','core.excludesfile=','status','--porcelain=v1','--untracked-files=no') $Root 60
 if($r.ExitCode -ne 0 -or @($r.StandardError).Count -ne 0){throw 'OPT1-R1-RESTORATION: git inventory failure'}
 $index=Join-Path $Root '.git/index'
 return [pscustomobject]@{Status=($r.StandardOutput -join "`n");IndexSHA256=(Get-FileHash -LiteralPath $index).Hash}
}
function Invoke-R1Library([string]$Name,[string]$Root,[string[]]$Extra=@()) {
 return Invoke-R1Tool $Name $shell (@('-NoProfile','-File',(Join-Path $Root 'scripts/packed_optimized_certificate_replay.ps1'),
   '-LibrarySelfTestOnly','-StageDeadlineSeconds','600','-CampaignDeadlineSeconds','850')+$Extra) $Root
}
function Invoke-R1Mutation([string]$ID,[string]$Root,[string]$Relative,[scriptblock]$Mutate,[scriptblock]$Check) {
 $path=[IO.Path]::GetFullPath((Join-Path $Root $Relative))
 if(-not $path.StartsWith($Root.TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase)){throw 'OPT1-R1-FIXTURE: mutation path escape'}
 $bytes=[IO.File]::ReadAllBytes($path)
 $stamp=[IO.File]::GetLastWriteTimeUtc($path)
 $hash=(Get-FileHash -LiteralPath $path).Hash
 $before=Get-R1Tracked ($ID+'-before') $Root
 try { & $Mutate $path $bytes $stamp; & $Check }
 finally {
  [IO.File]::WriteAllBytes($path,$bytes)
  [IO.File]::SetLastWriteTimeUtc($path,$stamp)
  $after=Get-R1Tracked ($ID+'-after') $Root
  $restored=(Get-FileHash -LiteralPath $path).Hash -ceq $hash -and
    $after.Status -ceq $before.Status -and $after.IndexSHA256 -ceq $before.IndexSHA256
  Write-R1Json ($ID+'-restoration.json') @{Path=$Relative;BeforeSHA256=$hash;AfterSHA256=(Get-FileHash -LiteralPath $path).Hash;Before=$before;After=$after;Restored=$restored}
  if(-not $restored){throw "OPT1-R1-RESTORATION: $ID did not restore exact source/index"}
 }
}
function Get-R1CacheSnapshot([string]$Root) {
 $cache=[IO.Path]::GetFullPath((Join-Path $Root '.lake/build/lib/lean'))
 $files=[ordered]@{}
 foreach($path in @([IO.Directory]::EnumerateFiles($cache,'*',[IO.SearchOption]::AllDirectories)|Sort-Object)) {
  $files[$path.Substring($cache.Length+1).Replace('\','/')]=(Get-FileHash -LiteralPath $path).Hash
 }
 $directories=@([IO.Directory]::EnumerateDirectories($cache,'*',[IO.SearchOption]::AllDirectories)|ForEach-Object {$_.Substring($cache.Length+1).Replace('\','/')}|Sort-Object)
 return [ordered]@{Files=$files;Directories=$directories}
}
function Invoke-R1Shadow([string]$ID,[string]$Root) {
 $relative=switch($ID){'P19-EXTRA-ARTIFACT' {'Init.olean'} 'P20-SHADOW-DIRECTORY' {'Init'} default {'RMQ/Core/Backend.olean.server'}}
 $cache=[IO.Path]::GetFullPath((Join-Path $Root '.lake/build/lib/lean'))
 $path=[IO.Path]::GetFullPath((Join-Path $cache $relative))
 if(-not $path.StartsWith($cache.TrimEnd('\','/')+[IO.Path]::DirectorySeparatorChar,[StringComparison]::OrdinalIgnoreCase) -or (Test-Path -LiteralPath $path)){
  throw 'OPT1-R1-FIXTURE: shadow path must be absent and inside the private cache'
 }
 $before=Get-R1Tracked ($ID+'-before') $Root
 $cacheBefore=Get-R1CacheSnapshot $Root
 try {
  if($ID -ceq 'P20-SHADOW-DIRECTORY'){[void][IO.Directory]::CreateDirectory($path)}
  else{[IO.File]::WriteAllBytes($path,[byte[]]@(79,80,84,49))}
  Assert-R1Verdict (Invoke-R1Library $ID $Root) 1 'OPT1-CERT-IMPORT: OPT1-PROFILE: changed complete compiled artifact inventory'
 } finally {
  # These are exactly the previously checked, newly created private paths.
  # Directory removal is nonrecursive and therefore fails on unexpected content.
  if($ID -ceq 'P20-SHADOW-DIRECTORY'){[IO.Directory]::Delete($path,$false)}
  else{[IO.File]::Delete($path)}
  $after=Get-R1Tracked ($ID+'-after') $Root
  $cacheAfter=Get-R1CacheSnapshot $Root
  $restored=(-not (Test-Path -LiteralPath $path)) -and
   $before.Status -ceq $after.Status -and $before.IndexSHA256 -ceq $after.IndexSHA256 -and
   ($cacheBefore|ConvertTo-Json -Depth 5 -Compress) -ceq ($cacheAfter|ConvertTo-Json -Depth 5 -Compress)
  Write-R1Json ($ID+'-restoration.json') @{AddedPath=$relative;Before=$before;After=$after;CacheBefore=$cacheBefore;CacheAfter=$cacheAfter;Restored=$restored;NotASemanticRejection=$true}
  if(-not $restored){throw "OPT1-R1-RESTORATION: $ID changed the source/index/cache"}
 }
}
function Invoke-R1Boundary([string]$ID,[string]$Root,[bool]$Repair,[string]$Mode) {
 $target=Join-Path $Root $(if($Repair){'scripts/packed_optimized_replay_regression.ps1'}else{'scripts/packed_optimized_certificate_replay.ps1'})
 $prefix=if($Repair){'OPT1-R1'}else{'OPT1-CERT'}
 $valid=if($Repair){'P01-LIBRARY-LF'}else{'A01-UNCHANGED'}
 $unknown=if($Repair){'P99-UNKNOWN'}else{'D99-unknown'}
 $total=if($Repair){$ids.Count}else{80}
 $body=switch($Mode){
  'omitted' {"& `$Target -SelectorProbeOnly"}
  'valid' {"& `$Target -SelectorProbeOnly -OnlyCase '$valid'"}
  'empty' {"& `$Target -OnlyCase ''"}
  'whitespace' {"& `$Target -OnlyCase ' '"}
  'padded' {"& `$Target -OnlyCase ' $valid '"}
  'malformed' {"& `$Target -OnlyCase '$valid,$valid'"}
  'unknown' {"& `$Target -OnlyCase '$unknown'"}
  'contradictory' {"& `$Target -SelectorProbeOnly -LibrarySelfTestOnly"}
 }
 $wrapper=Join-Path $out ($ID+'-boundary.ps1')
 [IO.File]::WriteAllText($wrapper,"param([string]`$Target)`n$body`nexit ([int]`$LASTEXITCODE)`n",$utf8)
 $r=Invoke-R1Tool $ID $shell @('-NoProfile','-File',$wrapper,'-Target',$target) $Root 120
 $exit=if($Mode -in @('omitted','valid')){0}else{1}
 $token=switch($Mode){
  'omitted' {"$prefix-SELECTOR PROBE PASS bound=False selected=$total"}
  'valid' {"$prefix-SELECTOR PROBE PASS bound=True selected=1 ids=$valid"}
  'empty' {"${prefix}-SELECTOR: explicitly empty selector"}
  'whitespace' {"${prefix}-SELECTOR: explicitly empty selector"}
  'padded' {"${prefix}-SELECTOR: malformed selector"}
  'malformed' {"${prefix}-SELECTOR: malformed selector"}
  'unknown' {"${prefix}-SELECTOR: unknown selector $unknown"}
  'contradictory' {'OPT1-CERT-SELECTOR: incompatible modes'}
 }
 Assert-R1Verdict $r $exit $token -Boundary
}

try {
 $selected=@(Get-R1Selection)
 if((Get-FileHash -LiteralPath (Join-Path $repoRoot $registryPath)).Hash.ToLowerInvariant() -cne $registrySHA256){
  throw 'OPT1-R1-REGISTRY: frozen registry bytes changed'
 }
 $registry=[IO.File]::ReadAllText((Join-Path $repoRoot $registryPath),$utf8)|ConvertFrom-Json
 if($registry.Version -cne $version -or $registry.Count -ne 49){throw 'OPT1-R1-REGISTRY: version/count mismatch'}
 Assert-R1Exact @($registry.Cases.Id) $ids 'versioned case registry'
 if($SelectorProbeOnly){
  Write-Host "OPT1-R1-SELECTOR PROBE PASS bound=$onlyBound selected=$($selected.Count) ids=$($selected -join ',')"
 }else{
  . (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
  $shell=(Get-Process -Id $PID).Path
  $git=Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application) 'git'
  $out=if([string]::IsNullOrWhiteSpace($ArtifactDirectory)){Join-Path $repoRoot ('.lake/r1/rr/'+[guid]::NewGuid().ToString('N').Substring(0,12))}else{[IO.Path]::GetFullPath($ArtifactDirectory)}
  if(Test-Path -LiteralPath $out){throw 'OPT1-R1-OUTPUT: evidence directory already exists'}
  [void][IO.Directory]::CreateDirectory($out)
  Write-Host "OPT1-R1-ARTIFACTS $out"
  Write-R1Json 'identity.json' @{SourceCommit='aecf4a580c591e8f694a3699e19e843198089194';RunnerSHA256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;RegistrySHA256=(Get-FileHash -LiteralPath (Join-Path $repoRoot $registryPath)).Hash;RawCheckout=$RawCheckout;WindowsCheckout=$WindowsCheckout;Mode='Production script/function regression, not a native machine performance claim';POSIX='UNEXECUTED'}
  foreach($id in $selected){
   if($id.StartsWith('V')){
    $intended='OPT1-CERT-IMPORT: OPT1-R1 controlled setup rejection'
    $stdout=switch($id){
     'V02-MIXED-STDOUT' {@('uncaught exception: unrelated filesystem failure')}
     'V03-SUCCESS-STDOUT' {@('OPT1-CERT-REPLAY PASS executed=80 expected=80 registry=opt1-certificate-replay-v3')}
     'V05-ALLOWED-PROGRESS' {@('OPT1-CERT-ARTIFACTS C:/private/.lake/oc/012345abcdef','OPT1-CERT-STAGE tracked-source-status-before deadline=60s','OPT1-CERT-STAGE import-freshness deadline=600s','OPT1-CERT-STAGE tracked-source-status-after deadline=60s','OPT1-CERT-ORIGINALS PASS source SHA256 unchanged; mutations applied/restored only in isolated copies')}
     'V06-DUPLICATE-PROGRESS' {@('OPT1-CERT-STAGE import-freshness deadline=600s','OPT1-CERT-STAGE import-freshness deadline=600s')}
     'V07-REORDERED-PROGRESS' {@('OPT1-CERT-STAGE tracked-source-status-after deadline=60s','OPT1-CERT-STAGE import-freshness deadline=600s')}
     'V09-PREFIX-HOLDOUT' {@(' OPT1-CERT-STAGE import-freshness deadline=600s')}
     default {@()}
    }
    $stderr=if($id -ceq 'V04-WRONG-STDERR'){@($intended+' extra diagnostic detail')}
     elseif($id -ceq 'V08-EXTRA-STDERR'){@($intended,'uncaught exception: unrelated stderr')}
     else{@($intended)}
    $fixture=Join-Path $out ($id+'-child.ps1')
    $original=$utf8.GetBytes("# original private fixture for $id`n")
    [IO.File]::WriteAllBytes($fixture,$original)
    try {
     $body=@($stdout|ForEach-Object {"[Console]::Out.WriteLine('"+$_.Replace("'","''")+"')"})+
       @($stderr|ForEach-Object {"[Console]::Error.WriteLine('"+$_.Replace("'","''")+"')"})+@('exit 1')
     [IO.File]::WriteAllText($fixture,($body -join "`n"),$utf8)
     $r=Invoke-R1Tool $id $shell @('-NoProfile','-File',$fixture) $repoRoot 60
     if($r.ExitCode -ne 1){throw 'OPT1-R1-FIXTURE: verdict child did not establish intended exit'}
     $accepted=$false;$reason=$null
     try {Assert-R1Verdict $r 1 $intended;$accepted=$true}catch{
      $reason=$_.Exception.Message
      if(-not $reason.StartsWith('OPT1-R1-VERDICT:',[StringComparison]::Ordinal)){throw}
     }
     $expectedAccept=$id -in @('V01-SOLE-SETUP','V05-ALLOWED-PROGRESS')
     if($accepted -ne $expectedAccept){throw "OPT1-R1-VERDICT: $id classifier expectation differs"}
     Write-R1Json ($id+'-verdict.json') @{Id=$id;ExpectedAccept=$expectedAccept;ActualAccept=$accepted;Reason=$reason;ProductionFunction='Assert-R1Verdict';ActualOwnedChild=$true}
    }finally{
     [IO.File]::WriteAllBytes($fixture,$original)
     if([Convert]::ToBase64String([IO.File]::ReadAllBytes($fixture)) -cne [Convert]::ToBase64String($original)){throw 'OPT1-R1-RESTORATION: verdict child fixture differs'}
    }
   }elseif($id -cmatch '^[CR]0[1-8]-' -and $id -notin @('R08-MIDDLE-OMITTED')){
    $mode=switch($id.Substring(3)){
     '-OMITTED' {'omitted'} '-VALID' {'valid'} '-EMPTY' {'empty'} '-WHITESPACE' {'whitespace'}
     '-PADDED' {'padded'} '-MALFORMED' {'malformed'} '-UNKNOWN' {'unknown'} '-CONTRADICTORY' {'contradictory'}
    }
    Invoke-R1Boundary $id $repoRoot ($id.StartsWith('R')) $mode
   }elseif($id -cmatch '^[CR][0-9]{2}-MIDDLE-'){
    $root=Get-R1Fixture $false
    $isRepair=$id.StartsWith('R')
    $relative=if($isRepair){$registryPath}else{'docs/internal/extensions/opt1/certificate-replay/REGISTRY.md'}
    Invoke-R1Mutation $id $root $relative {
     param($path,$bytes,$stamp)
     $text=$utf8.GetString($bytes)
     if($isRepair){
      $data=$text|ConvertFrom-Json
      $items=@($data.Cases)
      if($id.EndsWith('OMITTED')){$data.Cases=@($items[0..23])+@($items[25..($items.Count-1)])}
      else{$data.Cases=@($items[0..24])+@($items[24])+@($items[25..($items.Count-1)])}
      $text=$data|ConvertTo-Json -Depth 8
     }else{
      $rows=@([regex]::Matches($text,'(?m)^\| D[0-9]{2}-[^\r\n]+\r?$'))
      if($rows.Count -ne 39){throw 'OPT1-R1-FIXTURE: exact39 field rows required'}
      $line=$rows[19].Value
      $text=$text.Replace($line,$(if($id.EndsWith('OMITTED')){''}else{$line+"`n"+$line}))
     }
     [IO.File]::WriteAllText($path,$text,$utf8)
    } {
     $target=Join-Path $root $(if($isRepair){'scripts/packed_optimized_replay_regression.ps1'}else{'scripts/packed_optimized_certificate_replay.ps1'})
     $r=Invoke-R1Tool $id $shell @('-NoProfile','-File',$target,'-SelectorProbeOnly') $root 120
     Assert-R1Verdict $r 1 $(if($isRepair){'OPT1-R1-REGISTRY: frozen registry bytes changed'}else{'OPT1-CERT-REGISTRY: Markdown cases missing, duplicate, extra, reordered or changed'}) -Boundary
    }
   }else{
    $root=Get-R1Fixture ($id -in @('P01-LIBRARY-LF','P03-WEAKEN-LF','P19-EXTRA-ARTIFACT','P20-SHADOW-DIRECTORY','P21-ARTIFACT-SIDECAR'))
    if($id -in @('P01-LIBRARY-LF','P02-LIBRARY-WINDOWS')){
     Assert-R1Verdict (Invoke-R1Library $id $root) 0 'OPT1-CERT-LIBRARY SELF-TEST PASS dependencies=259 private=3'
    }elseif($id -in @('P03-WEAKEN-LF','P04-WEAKEN-WINDOWS')){
     $r=Invoke-R1Tool $id $shell @('-NoProfile','-File',(Join-Path $root 'scripts/packed_optimized_certificate_replay.ps1'),'-OnlyCase','W28-stepBound','-StageDeadlineSeconds','300','-CampaignDeadlineSeconds','1400') $root 1500
     Assert-R1Verdict $r 0 'OPT1-CERT-REPLAY PASS executed=1 expected=1 registry=opt1-certificate-replay-v3'
     if(@($r.StandardOutput|Where-Object {$_ -ceq 'OPT1-CERT CASE W28-stepBound REJECT restored=True'}).Count -ne 1){throw 'OPT1-R1-VERDICT: missing actual intended typed rejection'}
    }elseif($id -ceq 'P18-LEAN-EXECUTABLE'){
     Assert-R1Verdict (Invoke-R1Library $id $root @('-LeanPath',$shell)) 1 'OPT1-CERT-IMPORT: OPT1-PROFILE: wrong Lean executable/profile path'
    }elseif($id -in @('P19-EXTRA-ARTIFACT','P20-SHADOW-DIRECTORY','P21-ARTIFACT-SIDECAR')){
     Invoke-R1Shadow $id $root
    }else{
     $relative=switch($id){
      {$_ -in @('P06-ARTIFACT-TOKEN','P07-ARTIFACT-MISSING','P08-ARTIFACT-STALE')} {'.lake/build/lib/lean/RMQ/Core/Backend.olean'}
      'P09-SOURCE-PROFILE' {'docs/internal/extensions/opt1/repair-r1/profile/SOURCE_PROFILE.json'}
      'P10-BUILD-RECEIPT' {'docs/internal/extensions/opt1/repair-r1/profile/BUILD_RECEIPT.json'}
      'P11-TOOLCHAIN-TEXT' {'lean-toolchain'}
      {$_ -in @('P12-IMPORT-OMITTED','P13-IMPORT-DUPLICATE')} {'scripts/packed_optimized_runtime.ps1'}
      default {'RMQ/Core/Backend.lean'}
     }
     Invoke-R1Mutation $id $root $relative {
      param($path,$bytes,$stamp)
      switch($id){
       'P06-ARTIFACT-TOKEN' {$changed=$bytes.Clone();$changed[64]=$changed[64] -bxor 1;[IO.File]::WriteAllBytes($path,$changed)}
       'P07-ARTIFACT-MISSING' {[IO.File]::Delete($path)}
       'P08-ARTIFACT-STALE' {[IO.File]::SetLastWriteTimeUtc($path,[datetime]'2000-01-01T00:00:00Z')}
       'P09-SOURCE-PROFILE' {[IO.File]::WriteAllText($path,$utf8.GetString($bytes)+" `n",$utf8)}
       'P10-BUILD-RECEIPT' {[IO.File]::WriteAllText($path,$utf8.GetString($bytes)+" `n",$utf8)}
       'P11-TOOLCHAIN-TEXT' {[IO.File]::WriteAllText($path,"leanprover/lean4:v4.21.0`n",$utf8)}
       {$_ -in @('P12-IMPORT-OMITTED','P13-IMPORT-DUPLICATE')} {
        $text=$utf8.GetString($bytes)
        $needle="Write-OPT1Json 'imports-check.json' `$imports"
        if([regex]::Matches($text,[regex]::Escape($needle)).Count -ne 1){throw 'OPT1-R1-FIXTURE: unique actual import publication required'}
        $replacement=if($id -ceq 'P12-IMPORT-OMITTED'){
         "`$imports = @(`$imports[0..129]) + @(`$imports[131..260]); $needle"
        }else{"`$imports = @(`$imports[0..130]) + @(`$imports[130]) + @(`$imports[131..260]); $needle"}
        [IO.File]::WriteAllText($path,$text.Replace($needle,$replacement),$utf8)
       }
       'P14-SOURCE-SPACE' {[IO.File]::WriteAllText($path,$utf8.GetString($bytes)+" `n",$utf8)}
       'P15-SOURCE-UTF8' {[IO.File]::WriteAllBytes($path,([byte[]]@(255)+$bytes))}
       'P16-SOURCE-BOM' {[IO.File]::WriteAllBytes($path,([byte[]]@(239,187,191)+$bytes))}
       'P17-SOURCE-BARE-CR' {[IO.File]::WriteAllBytes($path,($bytes+[byte[]]@(13)))}
       default {[IO.File]::WriteAllText($path,$utf8.GetString($bytes)+"`ndef opt1R1SourceTokenHoldout : Nat := 17`n",$utf8)}
      }
      if($id -notin @('P07-ARTIFACT-MISSING','P08-ARTIFACT-STALE')){[IO.File]::SetLastWriteTimeUtc($path,$stamp)}
     } {
      $r=Invoke-R1Library $id $root
      $diagnostic=switch($id){
       {$_ -in @('P05-SOURCE-TOKEN','P14-SOURCE-SPACE')} {'OPT1-CERT-IMPORT: OPT1-PROFILE: source/configuration differs from versioned Git identity: RMQ/Core/Backend.lean'}
       'P06-ARTIFACT-TOKEN' {'OPT1-CERT-IMPORT: OPT1-PROFILE: missing/changed/stale compiled artifact or receipt: RMQ.Core.Backend'}
       {$_ -in @('P07-ARTIFACT-MISSING','P08-ARTIFACT-STALE','P15-SOURCE-UTF8')} {'OPT1-CERT-VERDICT: producer/accept control failed at import-freshness exit=1'}
       'P09-SOURCE-PROFILE' {'OPT1-CERT-IMPORT: OPT1-PROFILE: pinned source manifest bytes changed'}
       'P10-BUILD-RECEIPT' {'OPT1-CERT-IMPORT: OPT1-PROFILE: pinned build receipt bytes changed'}
       'P11-TOOLCHAIN-TEXT' {'OPT1-CERT-IMPORT: OPT1-PROFILE: source/configuration differs from versioned Git identity: lean-toolchain'}
       'P12-IMPORT-OMITTED' {'OPT1-CERT-REGISTRY: checked import provenance inventory missing, duplicate, extra, reordered or changed'}
       'P13-IMPORT-DUPLICATE' {'OPT1-CERT-IMPORT: duplicate production import record'}
       {$_ -in @('P16-SOURCE-BOM','P17-SOURCE-BARE-CR')} {'OPT1-CERT-IMPORT: OPT1-PROFILE: BOM or bare CR outside serialization: RMQ/Core/Backend.lean'}
      }
      Assert-R1Verdict $r 1 $diagnostic
      if($id -in @('P07-ARTIFACT-MISSING','P08-ARTIFACT-STALE','P15-SOURCE-UTF8')){
       $artifactLines=@($r.StandardOutput|Where-Object {$_.StartsWith('OPT1-CERT-ARTIFACTS ',[StringComparison]::Ordinal)})
       if($artifactLines.Count -ne 1){throw 'OPT1-R1-VERDICT: nested failure receipt unavailable'}
       $nestedPath=Join-Path $artifactLines[0].Substring('OPT1-CERT-ARTIFACTS '.Length) 'import-freshness.json'
       $nested=([IO.File]::ReadAllText($nestedPath,$utf8)|ConvertFrom-Json).Result
       if($nested.ExitCode -ne 1 -or $nested.TimedOut -or $nested.OutputLimitExceeded -or @($nested.StandardError).Count -ne 1){throw 'OPT1-R1-VERDICT: nested setup failure not ordinary and exclusive'}
       $message=$nested.StandardError[0]
       $intended=switch($id){
        'P07-ARTIFACT-MISSING' {$message -ceq ("Cannot find path '"+(Join-Path $root '.lake/build/lib/lean/RMQ/Core/Backend.olean')+"' because it does not exist.")}
        'P08-ARTIFACT-STALE' {$message -ceq 'OPT1-IMPORT: stale artifact for RMQ.Core.Backend; rebuild the affected import closure before replay'}
        'P15-SOURCE-UTF8' {$message -cmatch '^Exception calling "ReadAllText" with "2" argument\(s\): "Unable to translate bytes \[FF\] at index 0 from specified code page to Unicode\."$'}
       }
       if(-not $intended){throw "OPT1-R1-VERDICT: wrong nested setup diagnostic for $id"}
       if(@($nested.StandardOutput).Count -ne 1 -or $nested.StandardOutput[0] -cnotmatch '^OPT1-ARTIFACTS [^\r\n]+[\\/]\.lake[\\/]opt1-runtime-replay[\\/][0-9]{8}T[0-9]{6}Z-[0-9a-f]{32}$'){throw 'OPT1-R1-VERDICT: unrelated nested stdout'}
       Write-R1Json ($id+'-nested-failure.json') @{ExpectedCase=$id;Intended=$true;RawResult=$nested;NotASemanticRejection=$true}
      }
     }
    }
   }
   $executed.Add($id)
   Write-Host "OPT1-R1 CASE $id PASS"
  }
  Assert-R1Exact @($executed) $selected 'executed/expected cases'
 }
}catch{$exitCode=1;[Console]::Error.WriteLine($_.Exception.Message)}
finally{
 if($null -ne $out -and (Test-Path -LiteralPath $out)){
  Write-R1Json 'RESULT.json' @{Version=$version;Expected=@($selected);Executed=@($executed);ExitCode=$exitCode;Stages=@($stages);DurationSeconds=$clock.Elapsed.TotalSeconds;DeadlineSeconds=$CampaignDeadlineSeconds;POSIX='UNEXECUTED'}
 }
}
if($exitCode -eq 0 -and -not $SelectorProbeOnly){Write-Host "OPT1-R1-REPLAY PASS executed=$($executed.Count) expected=$($selected.Count) registry=$version"}
exit $exitCode
