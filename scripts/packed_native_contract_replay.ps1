param([AllowEmptyString()][string]$Case,[switch]$Controls)
$ErrorActionPreference='Stop'
$contractRoot=Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$contractRegistryPath=Join-Path $PSScriptRoot 'packed_native_contract_cases.json'
$contractRegistryHash='6E0C8E5A73F7DE47D14F7298435E7F72F2AC82A5881AEBF3EFFE0388CBF48E2C'
if((Get-FileHash -LiteralPath $contractRegistryPath).Hash -cne $contractRegistryHash){throw 'exact contract semantic registry mismatch'}
$contractRegistry=Get-Content -LiteralPath $contractRegistryPath -Raw | ConvertFrom-Json
$contractExactIds=@('baseline')+@(1..42 | ForEach-Object {'field-n'+$_.ToString('00')})+@('public-type-collapse')
$contractControlIds=@('empty','whitespace','malformed','unknown','valid-baseline','omitted-full',
  'registry-missing-case','registry-kind-downgrade','registry-consumer-change')
if($contractRegistry.schema -cne 'native1-contract-cases-v1' -or $contractRegistry.status -cne 'FROZEN' -or
   $contractRegistry.fieldCount -ne 42 -or ($contractRegistry.cases.id -join ',') -cne ($contractExactIds -join ',') -or
   ($contractRegistry.controls.id -join ',') -cne ($contractControlIds -join ',')){throw 'exact nonempty contract registry mismatch'}
$contractRoster=if($Controls){@($contractRegistry.controls)}else{@($contractRegistry.cases)}
if($PSBoundParameters.ContainsKey('Case')){
  if([string]::IsNullOrWhiteSpace($Case) -or $Case -cnotmatch '^[a-z0-9-]+$' -or $contractRoster.id -cnotcontains $Case){throw 'invalid exact contract selector'}
  $contractSelected=@($contractRoster | Where-Object id -CEQ $Case)
}else{$contractSelected=@($contractRoster)}
if($contractSelected.Count -eq 0){throw 'empty contract selection'}
$contractProducer='RMQ/Core/WordRAM/Native/Capstone.lean'
$contractConsumer='RMQ/Core/WordRAM/Native/Contract.lean'
if(($contractRegistry.sources.path -join ',') -cne ($contractProducer+','+$contractConsumer)){throw 'contract source inventory mismatch'}
$contractLean='C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
$contractShell=(Get-Process -Id $PID).Path
$contractLibrary=Join-Path $contractRoot '.lake/build/lib/lean'
$contractRunId=[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$contractScratch=Join-Path $contractRoot ('.lake/native1/contract-replay/'+$contractRunId)
$contractImportTree=Join-Path $contractScratch 'imports'
$contractDependencyCopy=$null
$contractLogs=Join-Path $contractRoot 'docs/internal/extensions/native1/binary-commands'
[void](New-Item -ItemType Directory -Force -Path $contractScratch,$contractLogs)
$contractResults=[Collections.Generic.List[object]]::new()
$contractCommands=[Collections.Generic.List[object]]::new()
$contractStarted=[DateTime]::UtcNow.ToString('o')
$contractSuccess=$false
$contractFailure=$null
$contractCompiler=$null
function Assert-ContractSources{
  foreach($pin in $contractRegistry.sources){
    if((Get-FileHash -LiteralPath (Join-Path $contractRoot $pin.path)).Hash -cne $pin.sha256){throw ('contract source byte pin mismatch: '+$pin.path)}
  }
}
function Get-ContractGitState([string]$Path){
  $state=@(& git diff --binary -- $Path)
  if($LASTEXITCODE -ne 0){throw 'contract Git restoration-state read failed'}
  return ($state -join "`n")
}
function Get-ContractCaseSpan([string]$Text,[string]$Id){
  $ids=[regex]::Matches($Text,'"id"\s*:\s*"'+[regex]::Escape($Id)+'"')
  if($ids.Count -ne 1){throw 'contract case mutation ID anchor not unique'}
  $start=$Text.LastIndexOf('{',$ids[0].Index)
  if($start -lt 0){throw 'contract case object start missing'}
  $depth=0;$quoted=$false;$escaped=$false
  for($i=$start;$i -lt $Text.Length;$i++){
    $ch=$Text[$i]
    if($quoted){
      if($escaped){$escaped=$false}
      elseif($ch -ceq '\'){$escaped=$true}
      elseif($ch -ceq '"'){$quoted=$false}
    }elseif($ch -ceq '"'){$quoted=$true}
    elseif($ch -ceq '{'){$depth++}
    elseif($ch -ceq '}'){
      $depth--
      if($depth -eq 0){return @{index=$start;length=$i-$start+1;text=$Text.Substring($start,$i-$start+1)}}
    }
  }
  throw 'contract case object end missing'
}
function Invoke-ContractOwned([string]$Stage,[string]$Exe,[string[]]$Arguments,[int]$Deadline){
  $started=[DateTime]::UtcNow.ToString('o')
  $r=Invoke-RMQOwnedBoundedProcess -FilePath $Exe -Arguments $Arguments -WorkingDirectory $contractRoot `
    -Stage $Stage -DeadlineSeconds $Deadline -OutputLimitBytes 8388608 -TempRoot (Join-Path $contractScratch 'process')
  $r | Add-Member -NotePropertyName StartedUtc -NotePropertyValue $started
  $r | Add-Member -NotePropertyName CompletedUtc -NotePropertyValue ([DateTime]::UtcNow.ToString('o'))
  $r | Add-Member -NotePropertyName InvokedFilePath -NotePropertyValue $Exe
  $r | Add-Member -NotePropertyName InvokedArguments -NotePropertyValue @($Arguments)
  $contractCommands.Add($r)
  if($r.TimedOut -or $r.OutputLimitExceeded){throw ('bounded contract process incomplete: '+$Stage)}
  return $r
}
function Invoke-ContractChild($Entry){
  $arguments=@('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$PSCommandPath)
  if($Entry.selectorBound){$arguments+=@('-Case',[string]$Entry.selector)}
  return Invoke-ContractOwned $Entry.id $contractShell $arguments $Entry.deadlineSeconds
}
function Initialize-ContractImports{
  if($null -ne $script:contractDependencyCopy){return}
  if(Test-Path -LiteralPath $contractImportTree){throw 'contract private import tree is not fresh'}
  $watch=[Diagnostics.Stopwatch]::StartNew()
  $libraryPrefix=[IO.Path]::GetFullPath($contractLibrary).TrimEnd([IO.Path]::DirectorySeparatorChar)+[IO.Path]::DirectorySeparatorChar
  $files=@(Get-ChildItem -LiteralPath $contractLibrary -Recurse -File -Filter '*.olean')
  if($files.Count -eq 0){throw 'contract checked dependency tree is empty'}
  $pins=[Collections.Generic.List[object]]::new()
  [long]$totalBytes=0
  foreach($file in $files){
    if(-not $file.FullName.StartsWith($libraryPrefix,[StringComparison]::OrdinalIgnoreCase)){
      throw 'contract dependency path escaped its declared library'
    }
    $relative=$file.FullName.Substring($libraryPrefix.Length)
    $destination=Join-Path $contractImportTree $relative
    [void](New-Item -ItemType Directory -Force -Path (Split-Path $destination))
    $sourceHash=(Get-FileHash -LiteralPath $file.FullName).Hash
    # A physical byte copy gives the private RMQ package all of its imports.
    # No link is created and the shared checked artifact is never an output.
    [IO.File]::Copy($file.FullName,$destination,$false)
    $privateHash=(Get-FileHash -LiteralPath $destination).Hash
    if($privateHash -cne $sourceHash){throw ('contract dependency copy mismatch: '+$relative)}
    $pins.Add(@{path=$relative;bytes=$file.Length;sourceSha256=$sourceHash;privateSha256=$privateHash})
    $totalBytes+=$file.Length
  }
  $watch.Stop()
  $script:contractDependencyCopy=@{sourceRoot=$contractLibrary;privateRoot=$contractImportTree;
    fileCount=$pins.Count;bytes=$totalBytes;durationSeconds=$watch.Elapsed.TotalSeconds;
    physicalCopies=$true;files=@($pins.ToArray())}
}
function Invoke-ContractField($Entry){
  Assert-ContractSources
  $producerPath=Join-Path $contractRoot $contractProducer
  $consumerPath=Join-Path $contractRoot $contractConsumer
  $saved=[IO.File]::ReadAllBytes($producerPath)
  $before=(Get-FileHash -LiteralPath $producerPath).Hash
  $state=Get-ContractGitState $contractProducer
  $consumerState=Get-ContractGitState $contractConsumer
  $globalOleans=@($contractProducer,$contractConsumer | ForEach-Object {
    $path=Join-Path $contractLibrary ($_.Substring(0,$_.Length-5)+'.olean')
    if(-not(Test-Path -LiteralPath $path -PathType Leaf)){throw ('required checked baseline olean missing: '+$path)}
    @{path=$path;sha256=(Get-FileHash -LiteralPath $path).Hash}
  })
  Initialize-ContractImports
  Assert-ContractSources
  $overlay=Join-Path $contractScratch ('overlay-'+$Entry.id)
  if(Test-Path -LiteralPath $overlay){throw 'contract overlay is not fresh'}
  $producerOlean=Join-Path $overlay ($contractProducer.Substring(0,$contractProducer.Length-5)+'.olean')
  $consumerOlean=Join-Path $overlay ($contractConsumer.Substring(0,$contractConsumer.Length-5)+'.olean')
  [void](New-Item -ItemType Directory -Force -Path (Split-Path $producerOlean))
  $previousLeanPath=$env:LEAN_PATH
  $details=$null
  try{
    $text=[Text.UTF8Encoding]::new($false,$true).GetString($saved)
    if($Entry.kind -ceq 'field-weaken'){
      if($Entry.operation -cne 'weaken-proposition-and-initializer' -or
         $Entry.replacementDeclaration -cne ('  '+$Entry.field+" : True`n") -or
         $Entry.replacementInitializer -cne ('  '+$Entry.field+" := True.intro`n")){throw 'contract field mutation operation mismatch'}
      foreach($anchor in @($Entry.declaration,$Entry.initializer)){
        if([regex]::Matches($text,[regex]::Escape($anchor)).Count -ne 1){throw 'contract field/initializer anchor not unique'}
      }
      $consumerText=[IO.File]::ReadAllText($consumerPath)
      if([regex]::Matches($consumerText,[regex]::Escape($Entry.consumerBlock)).Count -ne 1){throw 'independent exact consumer block changed'}
      $changed=$text.Replace($Entry.declaration,$Entry.replacementDeclaration).Replace($Entry.initializer,$Entry.replacementInitializer)
    }elseif($Entry.kind -ceq 'public-weaken'){
      if($Entry.operation -cne 'replace-public-theorem-with-true' -or
         $Entry.replacement -cne 'theorem nativeExecutionCapstone_holds : True := True.intro'){throw 'public contract collapse operation mismatch'}
      if([regex]::Matches($text,[regex]::Escape($Entry.anchor)).Count -ne 1){throw 'public contract collapse anchor not unique'}
      $changed=$text.Replace($Entry.anchor,$Entry.replacement)
    }elseif($Entry.kind -ceq 'expected-accept'){
      if($Entry.operation -cne 'compile-producer-and-consumer' -or $Entry.expectedConsumerExit -ne 0){throw 'contract positive operation mismatch'}
      $changed=$text
    }else{throw 'unknown contract mutation kind'}
    if($Entry.kind -cne 'expected-accept' -and $changed -ceq $text){throw 'vacuous contract source mutation'}
    [IO.File]::WriteAllText($producerPath,$changed,[Text.UTF8Encoding]::new($false))
    $mutatedSource=(Get-FileHash -LiteralPath $producerPath).Hash
    # Lean resolves an entire root package from its first matching search path.
    # The complete physical copy avoids a partial RMQ package shadowing imports.
    $env:LEAN_PATH=$contractImportTree+';'+$contractLibrary
    $producer=Invoke-ContractOwned ($Entry.id+'-producer') $contractLean @('-j','1','-o',$producerOlean,$contractProducer) $Entry.deadlineSeconds
    if($producer.ExitCode -ne $Entry.expectedProducerExit -or $producer.ExitCode -ne 0 -or -not(Test-Path -LiteralPath $producerOlean)){
      throw ('weakened contract producer did not compile: '+$Entry.id)
    }
    $freshProducerHash=(Get-FileHash -LiteralPath $producerOlean).Hash
    $boundProducerOlean=Join-Path $contractImportTree ($contractProducer.Substring(0,$contractProducer.Length-5)+'.olean')
    $previousPrivateHash=(Get-FileHash -LiteralPath $boundProducerOlean).Hash
    [IO.File]::Copy($producerOlean,$boundProducerOlean,$true)
    $boundProducerHash=(Get-FileHash -LiteralPath $boundProducerOlean).Hash
    if($boundProducerHash -cne $freshProducerHash){throw 'fresh contract producer binding mismatch'}
    $sharedProducerHash=(Get-FileHash -LiteralPath (Join-Path $contractLibrary ($contractProducer.Substring(0,$contractProducer.Length-5)+'.olean'))).Hash
    if($Entry.kind -cne 'expected-accept' -and $freshProducerHash -ceq $sharedProducerHash){
      throw 'mutated contract producer artifact matches the unchanged shared artifact'
    }
    $consumer=Invoke-ContractOwned ($Entry.id+'-consumer') $contractLean @('-j','1','-o',$consumerOlean,$contractConsumer) $Entry.deadlineSeconds
    if((Get-FileHash -LiteralPath $boundProducerOlean).Hash -cne $freshProducerHash){
      throw 'fresh contract producer binding changed during consumer compilation'
    }
    $line=$null;$matched=@()
    if($Entry.kind -ceq 'expected-accept'){
      if($consumer.ExitCode -ne 0 -or -not(Test-Path -LiteralPath $consumerOlean)){throw 'unchanged exact contract consumer failed'}
    }else{
      if($Entry.expectedConsumerExit -cne 'nonzero'){throw 'contract negative expected exit mismatch'}
      $lines=@([regex]::Split([IO.File]::ReadAllText($consumerPath),'\r?\n'))
      $line=[Array]::IndexOf($lines,[string]$Entry.proofLine)+1
      if($line -le 0 -or @($lines | Where-Object {$_ -ceq $Entry.proofLine}).Count -ne 1){throw 'contract exact consumer proof line not unique'}
      $pattern='^'+[regex]::Escape($contractConsumer)+':'+$line+':\d+: error: (?i:'+ [regex]::Escape($Entry.expectedDiagnostic)+')'
      $matched=@($consumer.Output | Where-Object {$_ -match $pattern})
      if($consumer.ExitCode -eq 0 -or $matched.Count -ne 1){throw ('contract mutation missed exact expected-type consumer: '+$Entry.id)}
    }
    $details=@{producer=$producer;consumer=$consumer;consumerName=$Entry.consumer;expectedLine=$line;matchedDiagnostics=$matched;
      originalSourceSha256=$before;mutatedSourceSha256=$mutatedSource;overlay=$overlay;
      producerOleanSha256=$freshProducerHash;sharedOleans=$globalOleans;
      producerBinding=@{path=$boundProducerOlean;previousPrivateSha256=$previousPrivateHash;
        freshOutputPath=$producerOlean;freshOutputSha256=$freshProducerHash;
        beforeConsumerSha256=$boundProducerHash;afterConsumerSha256=(Get-FileHash -LiteralPath $boundProducerOlean).Hash;
        sharedOriginalSha256=$sharedProducerHash;exactFreshBinding=$true}}
  }finally{
    [IO.File]::WriteAllBytes($producerPath,$saved)
    $env:LEAN_PATH=$previousLeanPath
    if((Get-FileHash -LiteralPath $producerPath).Hash -cne $before -or
       (Get-ContractGitState $contractProducer) -cne $state -or
       (Get-ContractGitState $contractConsumer) -cne $consumerState){throw 'contract source/diff restoration mismatch'}
    foreach($pin in $globalOleans){
      if((Get-FileHash -LiteralPath $pin.path).Hash -cne $pin.sha256){throw 'contract shared olean restoration mismatch'}
    }
    Assert-ContractSources
  }
  $details.restoredSourceSha256=$before;$details.exactGitRestoration=$true;$details.sharedOleansUnchanged=$true
  return $details
}
try{
  Assert-ContractSources
  if(-not $Controls){
    $probe=Invoke-ContractOwned 'contract-compiler-identity' $contractLean @('--version') 30
    $version=($probe.StandardOutput -join "`n").Trim()
    if($probe.ExitCode -ne 0 -or $version -cne 'Lean (version 4.22.0, x86_64-w64-windows-gnu, commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05, Release)'){
      throw 'contract compiler pin mismatch'
    }
    $contractCompiler=@{path=$contractLean;version=$version;sha256=(Get-FileHash -LiteralPath $contractLean).Hash;process=$probe}
  }
  foreach($entry in $contractSelected){
    if(-not $Controls){$details=Invoke-ContractField $entry}
    elseif($entry.operation -cin @('selector-rejection','selector-accept')){
      $child=Invoke-ContractChild $entry
      $executed=@($child.StandardOutput | Where-Object {$_ -clike 'NATIVE1-CONTRACT PASS *'} | ForEach-Object {$_.Substring('NATIVE1-CONTRACT PASS '.Length)})
      if($entry.operation -ceq 'selector-rejection'){
        if($child.ExitCode -eq 0 -or $executed.Count -ne 0 -or ($child.Output -join "`n") -notmatch [regex]::Escape($entry.expectedMessage)){
          throw ('contract selector missed exact rejection: '+$entry.id)
        }
      }elseif($child.ExitCode -ne 0 -or $entry.expectedIds.Count -eq 0 -or ($executed -join ',') -cne ($entry.expectedIds -join ',')){
        throw ('contract positive selector inventory mismatch: '+$entry.id)
      }
      $details=@{process=$child;executed=$executed}
    }elseif($entry.operation -ceq 'registry-rejection'){
      $saved=[IO.File]::ReadAllBytes($contractRegistryPath)
      $state=Get-ContractGitState 'scripts/packed_native_contract_cases.json'
      try{
        $originalText=[Text.UTF8Encoding]::new($false,$true).GetString($saved)
        $mutation=$originalText | ConvertFrom-Json
        $changedText=$null
        if($entry.mutation -ceq 'remove-final-case'){$mutation.cases=@($mutation.cases | Select-Object -SkipLast 1)}
        elseif($entry.mutation -ceq 'field-to-complete-baseline'){
          $donor=$mutation.cases[0] | ConvertTo-Json -Depth 12 | ConvertFrom-Json
          $donor.id='field-n01';$mutation.cases[1]=$donor
          $span=Get-ContractCaseSpan $originalText 'field-n01'
          $replacement=ConvertTo-Json -InputObject $donor -Depth 12 -Compress
          $changedText=$originalText.Substring(0,$span.index)+$replacement+$originalText.Substring($span.index+$span.length)
        }elseif($entry.mutation -ceq 'change-consumer-line'){
          $mutation.cases[1].proofLine='  True.intro'
          $span=Get-ContractCaseSpan $originalText 'field-n01'
          $matches=[regex]::Matches($span.text,'"proofLine"\s*:\s*"(?:[^"\\]|\\.)*"')
          if($matches.Count -ne 1){throw 'contract proofLine property span not unique'}
          $m=$matches[0];$offset=$span.index+$m.Index
          $changedText=$originalText.Substring(0,$offset)+'"proofLine": "  True.intro"'+$originalText.Substring($offset+$m.Length)
        }
        else{throw 'unknown contract registry mutation'}
        if($null -ne $changedText){
          $changedObject=$changedText | ConvertFrom-Json
          if((ConvertTo-Json -InputObject $changedObject -Depth 14 -Compress) -cne
             (ConvertTo-Json -InputObject $mutation -Depth 14 -Compress)){throw 'contract minimal mutation changed unrelated fields'}
          [IO.File]::WriteAllText($contractRegistryPath,$changedText,[Text.UTF8Encoding]::new($false))
        }else{$mutation | ConvertTo-Json -Depth 14 | Set-Content -LiteralPath $contractRegistryPath -Encoding utf8}
        $child=Invoke-ContractOwned $entry.id $contractShell @('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$PSCommandPath,'-Case','field-n01') $entry.deadlineSeconds
        if($child.ExitCode -eq 0 -or ($child.Output -join "`n") -notmatch [regex]::Escape($entry.expectedMessage)){
          throw ('contract registry mutation missed expected boundary: '+$entry.id)
        }
        $details=@{process=$child;mutatedRegistrySha256=(Get-FileHash -LiteralPath $contractRegistryPath).Hash}
      }finally{
        [IO.File]::WriteAllBytes($contractRegistryPath,$saved)
        if((Get-FileHash -LiteralPath $contractRegistryPath).Hash -cne $contractRegistryHash -or
           (Get-ContractGitState 'scripts/packed_native_contract_cases.json') -cne $state){throw 'contract registry restoration mismatch'}
      }
      $details.restoredRegistrySha256=$contractRegistryHash;$details.exactGitRestoration=$true
    }else{throw 'unknown contract control operation'}
    $contractResults.Add(@{id=$entry.id;pass=$true;details=$details})
    $prefix=if($Controls){'NATIVE1-CONTRACT-CONTROL PASS '}else{'NATIVE1-CONTRACT PASS '}
    Write-Output ($prefix+$entry.id)
  }
  if(($contractResults.id -join ',') -cne ($contractSelected.id -join ',')){throw 'contract executed/expected roster mismatch'}
  $contractSuccess=$true
}catch{$contractFailure=$_.Exception.Message;throw}
finally{
  [ordered]@{schema='native1-contract-replay-v1';startedUtc=$contractStarted;completedUtc=[DateTime]::UtcNow.ToString('o');
    pass=$contractSuccess;failure=$contractFailure;controls=[bool]$Controls;selectorBound=$PSBoundParameters.ContainsKey('Case');selector=$Case;
    registrySha256=$contractRegistryHash;runnerSha256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;
    sources=$contractRegistry.sources;compiler=$contractCompiler;dependencyCopy=$contractDependencyCopy;
    expected=@($contractSelected.id);executed=@($contractResults | ForEach-Object {$_.id});
    results=@($contractResults.ToArray());commands=@($contractCommands.ToArray())} | ConvertTo-Json -Depth 28 |
    Set-Content -LiteralPath (Join-Path $contractLogs ('contract-replay-'+$contractRunId+'.json')) -Encoding utf8
}
