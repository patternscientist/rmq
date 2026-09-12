param([AllowEmptyString()][string]$Case,[switch]$Selectors)
$ErrorActionPreference='Stop'
$v3Root=Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
$v3Helper=Join-Path $PSScriptRoot 'packed_native_identity.ps1'
$v3HelperHash='A21F67E2EDF49C8E218C657E73967E920EFB85FF025476E01BD04A83CA50B17A'
if((Get-FileHash -LiteralPath $v3Helper).Hash -cne $v3HelperHash){throw 'identity v3 production helper pin mismatch'}
. $v3Helper
# Versioned exact semantic registry. The whole UTF-8 literal is independently
# pinned below; modifying an ID, operation or expected diagnostic is rejected.
$v3RegistryText='{"schema":"native1-identity-v3-cases-v1","cases":[{"id":"ordinal-order","operation":"ordinal"},{"id":"canonical-maps","operation":"canonical"},{"id":"cross-shell","operation":"cross-shell"},{"id":"unchanged","operation":"accept"},{"id":"command-text","operation":"mutate","message":"native toolchain retained command mismatch: 0/text"},{"id":"command-argument","operation":"mutate","message":"native toolchain retained command mismatch: 0/arguments"},{"id":"command-file","operation":"mutate","message":"native toolchain retained command mismatch: 0/file"},{"id":"cpp-missing-key","operation":"mutate","message":"native toolchain C++ dependency shape"},{"id":"cpp-extra-key","operation":"mutate","message":"native toolchain C++ dependency shape"},{"id":"cpp-root","operation":"mutate","message":"native toolchain retained C++ roots mismatch: resourceRoot"},{"id":"include-order","operation":"mutate","message":"native toolchain retained C++ roots mismatch: includeSearch"},{"id":"library-order","operation":"mutate","message":"native toolchain retained C++ roots mismatch: librarySearch"},{"id":"file-row","operation":"mutate","message":"native toolchain retained inventory mismatch: leanFiles"},{"id":"sort-policy","operation":"mutate","message":"native toolchain manifest shape"},{"id":"missing-command","operation":"mutate","message":"native toolchain command roster shape"},{"id":"command-extra-key","operation":"mutate","message":"native toolchain command shape"},{"id":"digest-change","operation":"mutate","message":"native compiler/import/runtime identity changed"},{"id":"unknown-top-key","operation":"mutate","message":"native toolchain manifest shape"},{"id":"root-pin","operation":"mutate","message":"native toolchain retained inventory mismatch: leanRoot"},{"id":"restored","operation":"accept"}],"selectors":[{"id":"empty","bound":true,"selector":"","reject":true,"expectedCount":0},{"id":"whitespace","bound":true,"selector":" ","reject":true,"expectedCount":0},{"id":"malformed","bound":true,"selector":"unchanged,","reject":true,"expectedCount":0},{"id":"unknown","bound":true,"selector":"unknown-case","reject":true,"expectedCount":0},{"id":"valid","bound":true,"selector":"unchanged","reject":false,"expectedCount":1},{"id":"omitted","bound":false,"selector":"","reject":false,"expectedCount":20}]}'
$v3RegistryHash='4CB180BB0380215D14AC80058652120AA877488BDF4A231C39BF6017CD99DA14'
if((Get-NativeDigest @($v3RegistryText)) -cne $v3RegistryHash){throw 'exact identity v3 semantic registry mismatch'}
$v3Registry=$v3RegistryText|ConvertFrom-Json
if($v3Registry.schema -cne 'native1-identity-v3-cases-v1' -or $v3Registry.cases.Count -ne 20 -or
   @($v3Registry.cases.id|Select-Object -Unique).Count -ne 20 -or $v3Registry.selectors.Count -ne 6){throw 'identity v3 exact nonempty roster mismatch'}
$v3Roster=if($Selectors){@($v3Registry.selectors)}else{@($v3Registry.cases)}
if($PSBoundParameters.ContainsKey('Case')){
  if([string]::IsNullOrWhiteSpace($Case) -or $Case -cnotmatch '^[a-z0-9-]+$' -or $v3Roster.id -cnotcontains $Case){throw 'invalid exact identity v3 selector'}
  $v3Selected=@($v3Roster|Where-Object id -CEQ $Case)
}else{$v3Selected=@($v3Roster)}
if($v3Selected.Count -eq 0){throw 'empty identity v3 selection'}
$v3Pins=@(
  @{path='docs/internal/extensions/native1/commands/binary-build-20260912T111100924.json';sha256='8486C0C039365DE086E651FBC1686531D1DCA4F000C75C62BE6A65E70E6C53EB';property='toolchainIdentity'},
  @{path='docs/internal/extensions/native1/binary-commands/toolchain-mismatch-actual-v2.json';sha256='AF8459AC7377D3353E5EA96D362A16EF4309D8A2F2A93B9EB1820ED9594BDA11';property=''})
$v3Shells=@('C:/Windows/System32/WindowsPowerShell/v1.0/powershell.exe',
  'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe')
$v3Run=[DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfff')
$v3Scratch=Join-Path $v3Root ('.lake/native1/identity-v3-controls/'+$v3Run)
$v3Logs=Join-Path $v3Root 'docs/internal/extensions/native1/binary-commands'
[void](New-Item -ItemType Directory -Force -Path $v3Scratch,$v3Logs)
$v3Results=[Collections.Generic.List[object]]::new()
$v3Commands=[Collections.Generic.List[object]]::new()
$v3Started=[DateTime]::UtcNow.ToString('o')
$v3Success=$false;$v3Failure=$null
function Assert-V3Pins{
  if((Get-FileHash -LiteralPath $v3Helper).Hash -cne $v3HelperHash){throw 'identity v3 helper restoration mismatch'}
  foreach($pin in $v3Pins){if((Get-FileHash -LiteralPath (Join-Path $v3Root $pin.path)).Hash -cne $pin.sha256){throw 'identity v3 captured input pin mismatch'}}
}
function Get-V3OrderedRows($Rows,[bool]$Relative){
  $map=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  foreach($row in $Rows){
    $key=if($Relative){$row.path.Replace('/','\')}else{[string]$row.path}
    if($map.ContainsKey($key)){throw 'duplicate captured identity path'}
    $map.Add($key,$row)
  }
  return @(Get-NativeOrdinalUnique @($map.Keys)|ForEach-Object {$map[$_]})
}
function Convert-V3Captured($Value){
  if($Value.schema -cne 'native1-toolchain-v2'){throw 'expected original v2 capture'}
  $Value.schema='native1-toolchain-v3'
  $Value|Add-Member -NotePropertyName sortPolicy -NotePropertyValue 'ordinal-case-sensitive-utf16'
  foreach($field in @('leanRoot','rustRoot','cppCompiler','importLibrarian','rustLinker')){$Value.$field=[IO.Path]::GetFullPath($Value.$field)}
  foreach($command in $Value.commands){$command.file=[IO.Path]::GetFullPath($command.file)}
  $Value.leanFiles=@(Get-V3OrderedRows $Value.leanFiles $true)
  $Value.rustFiles=@(Get-V3OrderedRows $Value.rustFiles $true)
  $Value.cppDependencies.inventoryRoots=@(Get-NativeOrdinalUnique @($Value.cppDependencies.inventoryRoots))
  $cppRows=[Collections.Generic.List[object]]::new()
  foreach($directory in $Value.cppDependencies.inventoryRoots){
    $group=@($Value.cppFiles|Where-Object root -CEQ $directory)
    foreach($row in @(Get-V3OrderedRows $group $true)){$cppRows.Add($row)}
  }
  if($cppRows.Count -ne $Value.cppFiles.Count){throw 'captured C++ root/group mismatch'}
  $Value.cppFiles=@($cppRows.ToArray())
  $Value.toolRuntimeRoots=@(Get-NativeOrdinalUnique @($Value.toolRuntimeRoots))
  $Value.toolRuntimeFiles=@(Get-V3OrderedRows $Value.toolRuntimeFiles $false)
  $Value.externalFiles=@(Get-V3OrderedRows $Value.externalFiles $false)
  $Value.digest=Get-NativeToolchainDigest $Value
  return $Value
}
function Invoke-V3Child([string]$Stage,[string]$Shell,[bool]$Bound,[AllowEmptyString()][string]$Selector){
  $arguments=@('-NoLogo','-NoProfile','-ExecutionPolicy','Bypass','-File',$PSCommandPath)
  if($Bound){$arguments+=@('-Case',$Selector)}
  $started=[DateTime]::UtcNow.ToString('o')
  $deadline=if($Bound){180}else{360}
  $r=Invoke-RMQOwnedBoundedProcess -FilePath $Shell -Arguments $arguments -WorkingDirectory $v3Root `
    -Stage $Stage -DeadlineSeconds $deadline -OutputLimitBytes 8388608 -TempRoot $v3Scratch
  $r|Add-Member -NotePropertyName StartedUtc -NotePropertyValue $started
  $r|Add-Member -NotePropertyName CompletedUtc -NotePropertyValue ([DateTime]::UtcNow.ToString('o'))
  $r|Add-Member -NotePropertyName InvokedFilePath -NotePropertyValue $Shell
  $r|Add-Member -NotePropertyName InvokedArguments -NotePropertyValue $arguments
  $v3Commands.Add($r)
  if($r.TimedOut -or $r.OutputLimitExceeded){throw 'identity v3 child incomplete'}
  return $r
}
try{
  Assert-V3Pins
  $captures=@(foreach($pin in $v3Pins){
    $value=Get-Content -LiteralPath (Join-Path $v3Root $pin.path) -Raw|ConvertFrom-Json
    if($pin.property){$value=$value.($pin.property)}
    Convert-V3Captured $value
  })
  Assert-NativeRetainedIdentity $captures[0] $captures[1]
  $canonical=$captures[0]
  foreach($entry in $v3Selected){
    if($Selectors){
      $r=Invoke-V3Child $entry.id $v3Shells[1] $entry.bound $entry.selector
      $executed=@($r.StandardOutput|Where-Object {$_ -clike 'NATIVE1-IDENTITY-V3 PASS *'}|ForEach-Object {$_.Substring('NATIVE1-IDENTITY-V3 PASS '.Length)})
      if($entry.reject){
        if($r.ExitCode -eq 0 -or $executed.Count -ne 0 -or ($r.Output -join "`n") -notmatch 'invalid exact identity v3 selector'){throw 'identity v3 selector rejection mismatch'}
      }else{
        $expected=if($entry.bound){@($entry.selector)}else{@($v3Registry.cases.id)}
        if($r.ExitCode -ne 0 -or $executed.Count -ne $entry.expectedCount -or ($executed -join ',') -cne ($expected -join ',')){throw 'identity v3 positive selector mismatch'}
      }
      $details=@{process=$r;executed=$executed}
    }elseif($entry.operation -ceq 'ordinal'){
      $astral=[char]::ConvertFromUtf32(0x1F600)
      $inputValues=@('a_b','a.b','a-b','A','a','a',([string][char]0xE000),$astral)
      $expected=@('A','a','a-b','a.b','a_b',$astral,([string][char]0xE000))
      $actual=@(Get-NativeOrdinalUnique $inputValues)
      if(($actual -join '|') -cne ($expected -join '|')){throw 'ordinal UTF-16 case/punctuation/control mismatch'}
      $details=@{input=$inputValues;expected=$expected;actual=$actual}
    }elseif($entry.operation -ceq 'canonical'){
      Assert-NativeRetainedIdentity $captures[0] $captures[1]
      $details=@{digest=$canonical.digest;counts=@($canonical.leanFiles.Count,$canonical.rustFiles.Count,$canonical.cppFiles.Count,$canonical.toolRuntimeFiles.Count,$canonical.externalFiles.Count)}
      Write-Output ('NATIVE1-IDENTITY-V3 CANONICAL '+$canonical.digest)
    }elseif($entry.operation -ceq 'cross-shell'){
      $processes=@(foreach($shell in $v3Shells){
        $r=Invoke-V3Child ('canonical-'+[IO.Path]::GetFileName($shell)) $shell $true 'canonical-maps'
        $markers=@($r.StandardOutput|Where-Object {$_ -clike 'NATIVE1-IDENTITY-V3 CANONICAL *'})
        if($r.ExitCode -ne 0 -or $markers.Count -ne 1 -or $markers[0] -cne ('NATIVE1-IDENTITY-V3 CANONICAL '+$canonical.digest)){throw 'actual cross-shell canonical identity mismatch'}
        $r
      })
      $details=@{digest=$canonical.digest;processes=$processes}
    }elseif($entry.operation -ceq 'accept'){
      Assert-NativeRetainedIdentity $canonical $captures[1]
      $details=@{expectedAccept=$true;digest=$canonical.digest}
    }elseif($entry.operation -ceq 'mutate'){
      $changed=$canonical|ConvertTo-Json -Depth 20|ConvertFrom-Json
      switch -CaseSensitive($entry.id){
        'command-text' {$changed.commands[0].text+=' changed'}
        'command-argument' {$changed.commands[0].arguments=@('--help')}
        'command-file' {$changed.commands[0].file+='-changed'}
        'cpp-missing-key' {$changed.cppDependencies.PSObject.Properties.Remove('librarySearch')}
        'cpp-extra-key' {$changed.cppDependencies|Add-Member -NotePropertyName bypass -NotePropertyValue $true}
        'cpp-root' {$changed.cppDependencies.resourceRoot+='-changed'}
        'include-order' {$items=@($changed.cppDependencies.includeSearch);[Array]::Reverse($items);$changed.cppDependencies.includeSearch=$items}
        'library-order' {$items=@($changed.cppDependencies.librarySearch);[Array]::Reverse($items);$changed.cppDependencies.librarySearch=$items}
        'file-row' {$changed.leanFiles[0].sha256='0'*64}
        'sort-policy' {$changed.sortPolicy='culture-dependent'}
        'missing-command' {$changed.commands=@($changed.commands|Select-Object -SkipLast 1)}
        'command-extra-key' {$changed.commands[0]|Add-Member -NotePropertyName bypass -NotePropertyValue $true}
        'digest-change' {$changed.digest+='0'}
        'unknown-top-key' {$changed|Add-Member -NotePropertyName bypass -NotePropertyValue $true}
        'root-pin' {$changed.leanRoot+='-changed'}
        default {throw 'unknown identity v3 mutation'}
      }
      $rejected=$false;$diagnostic=$null
      try{Assert-NativeRetainedIdentity $changed $captures[1]}catch{$diagnostic=$_.Exception.Message;$rejected=$diagnostic -ceq $entry.message}
      if(-not $rejected){throw ('identity v3 mutation missed exact production surface: '+$entry.id+'; '+$diagnostic)}
      $details=@{diagnostic=$diagnostic;unchangedDigest=$canonical.digest;mutatedDigest=$changed.digest;actualProductionPredicate='Assert-NativeRetainedIdentity'}
    }else{throw 'unknown identity v3 operation'}
    $v3Results.Add(@{id=$entry.id;pass=$true;details=$details})
    $prefix=if($Selectors){'NATIVE1-IDENTITY-V3-SELECTOR PASS '}else{'NATIVE1-IDENTITY-V3 PASS '}
    Write-Output ($prefix+$entry.id)
  }
  if(($v3Results.id -join ',') -cne ($v3Selected.id -join ',')){throw 'identity v3 executed/expected inventory mismatch'}
  $v3Success=$true
}catch{$v3Failure=$_.Exception.Message;throw}
finally{
  Assert-V3Pins
  [ordered]@{schema='native1-identity-v3-control-receipt-v1';startedUtc=$v3Started;completedUtc=[DateTime]::UtcNow.ToString('o');
    pass=$v3Success;failure=$v3Failure;selectors=[bool]$Selectors;selectorBound=$PSBoundParameters.ContainsKey('Case');selector=$Case;
    registrySha256=$v3RegistryHash;helperSha256=$v3HelperHash;runnerSha256=(Get-FileHash -LiteralPath $PSCommandPath).Hash;
    shellVersion=$PSVersionTable.PSVersion.ToString();inputPins=$v3Pins;expected=@($v3Selected.id);executed=@($v3Results.id);
    results=@($v3Results.ToArray());commands=@($v3Commands.ToArray());restored=$true;
    scope='Actual production sorting/digest/retained predicates on pinned captured inventories; fresh compiler byte discovery remains required by build/startup.'}|
    ConvertTo-Json -Depth 28|Set-Content -LiteralPath (Join-Path $v3Logs ('identity-v3-controls-'+$v3Run+'.json')) -Encoding utf8
}
