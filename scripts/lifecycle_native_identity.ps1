# LIFE-NATIVE-1: exact byte captures and source identity for the owned route.
# Dot-source only. This file adds no policy to the protected predecessor helpers.
$script:LN1Root = Split-Path $PSScriptRoot -Parent
. (Join-Path $PSScriptRoot 'owned_process_tree.ps1')
. (Join-Path $PSScriptRoot 'packed_native_lifecycle_stream_check.ps1')
. (Join-Path $PSScriptRoot 'packed_native_lifecycle_integrity_check.ps1')

function Get-LN1Pin([string]$Path) {
  $full = [IO.Path]::GetFullPath($Path)
  [ordered]@{ path=$full; bytes=([IO.FileInfo]$full).Length;
    sha256=(Get-FileHash -LiteralPath $full -Algorithm SHA256).Hash }
}

function Invoke-LN1Stage {
  param([Parameter(Mandatory)][string]$File,
    [string[]]$Arguments=@(), [Parameter(Mandatory)][string]$Stage,
    [Parameter(Mandatory)][int]$DeadlineSeconds,
    [Parameter(Mandatory)][string]$OutputRoot,
    [string]$WorkingDirectory=$script:LN1Root)
  if ($DeadlineSeconds -le 0) { throw 'LIFECYCLE-STAGE: positive deadline required' }
  $capture = Invoke-LNStreamCapture $script:LN1Root $File $Arguments `
    $WorkingDirectory $OutputRoot $DeadlineSeconds $Stage
  $r = $capture.launcher
  if ($null -eq $r -or $r.TimedOut -or $r.OutputLimitExceeded -or
      $null -eq $capture.actual -or
      [IO.File]::Exists($capture.spec.error) -or [IO.File]::Exists($capture.spec.overflow)) {
    throw ('LIFECYCLE-STAGE: incomplete capture ' + $Stage + ' at ' + $OutputRoot)
  }
  # Build output is not a fixed language. Preserve every byte and validate the
  # transport separately; semantic replay supplies its exact expected streams.
  $stdout = Read-LNExactStream $capture.spec.stdout
  $stderr = Read-LNExactStream $capture.spec.stderr
  Assert-LNOuterCapture $capture $stdout $stderr $capture.actual.exitCode $Stage
  if ($capture.actual.exitCode -ne 0) {
    throw ('LIFECYCLE-STAGE: ordinary exit ' + $capture.actual.exitCode + ' ' + $Stage + ' at ' + $OutputRoot)
  }
  return $capture
}

function Get-LN1ImportClosure([string[]]$Roots) {
  $seen = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $ordered = [Collections.Generic.List[string]]::new()
  function Visit-LN1Module([string]$Module) {
    if (-not $seen.Add($Module)) { return }
    $path = Join-Path $script:LN1Root ($Module.Replace('.', '/') + '.lean')
    if (-not [IO.File]::Exists($path)) { throw ('LIFECYCLE-CLOSURE: missing ' + $Module) }
    $source = [IO.File]::ReadAllText($path, [Text.UTF8Encoding]::new($false,$true))
    foreach ($match in [regex]::Matches($source, '(?m)^import\s+(RMQ(?:\.[A-Za-z0-9_]+)+)\s*$')) {
      Visit-LN1Module $match.Groups[1].Value
    }
    $ordered.Add($Module)
  }
  foreach ($root in $Roots) { Visit-LN1Module $root }
  return @($ordered.ToArray())
}

function Get-LN1BytesHash([byte[]]$Bytes) {
  $sha=[Security.Cryptography.SHA256]::Create()
  try{return ([BitConverter]::ToString($sha.ComputeHash($Bytes))).Replace('-','').ToLowerInvariant()}
  finally{$sha.Dispose()}
}

function Assert-LN1FrozenContract([string]$Root=$script:LN1Root) {
  $utf8=[Text.UTF8Encoding]::new($false,$true)
  $directory=Join-Path $Root 'docs/internal/extensions/lifecycle-native1'
  $contractPath=Join-Path $directory 'CONTRACT_REQUIREMENTS.json'
  $contractBytes=[IO.File]::ReadAllBytes($contractPath)
  if((Get-LN1BytesHash $contractBytes) -cne '736ff55b84516d1b0c7e45f5dbf8193df98846ea259f0ef5b3caefbe7cd6bc5f'){
    throw 'LIFECYCLE-CONTRACT: frozen requirement source changed'
  }
  $contract=$utf8.GetString($contractBytes)|ConvertFrom-Json
  $matrixBytes=[IO.File]::ReadAllBytes((Join-Path $Root $contract.frozen_matrix.path))
  if($matrixBytes.Length -ne $contract.frozen_matrix.bytes -or
      (Get-LN1BytesHash $matrixBytes) -cne $contract.frozen_matrix.sha256){
    throw 'LIFECYCLE-CONTRACT: frozen matrix bytes changed'
  }
  $matrix=$utf8.GetString($matrixBytes)
  $ids=[Collections.Generic.List[string]]::new()
  $rows=@{}
  # Include the exact original newline in the row byte hash.
  foreach($match in [regex]::Matches($matrix,'(?m)^\| ([A-Z][A-Z0-9-]+) \|[^\r\n]*(?:\r?\n|$)')){
    $id=$match.Groups[1].Value
    if($id -ceq 'ID'){continue}
    if($rows.ContainsKey($id)){throw ('LIFECYCLE-CONTRACT: duplicate row '+$id)}
    $rows[$id]=$utf8.GetBytes($match.Value);$ids.Add($id)
  }
  if($ids.Count -ne 55 -or ($ids -join '|') -cne ($contract.ordered_ids -join '|')){
    throw 'LIFECYCLE-CONTRACT: ordered row registry differs'
  }
  foreach($row in $contract.rows){
    $bytes=$rows[$row.id]
    if($bytes.Length -ne $row.frozen_matrix_row_bytes -or
        (Get-LN1BytesHash $bytes) -cne $row.frozen_matrix_row_sha256){
      throw ('LIFECYCLE-CONTRACT: complete row bytes differ '+$row.id)
    }
    if((Get-LN1BytesHash ($utf8.GetBytes($row.exact_requirement))) -cne $row.requirement_utf8_sha256){
      throw ('LIFECYCLE-CONTRACT: requirement bytes differ '+$row.id)
    }
  }
  [ordered]@{success=$true;count=$ids.Count;orderedIds=@($ids.ToArray());
    contract=(Get-LN1Pin $contractPath);matrix=(Get-LN1Pin (Join-Path $Root $contract.frozen_matrix.path));
    changedIds=@();comparison='strict UTF-8, complete row bytes including original newline'}
}

function Assert-LN1FixtureRegistry([object]$Registry,[bool]$SelectorBound,[object]$Selector) {
  if($Registry.schema -cne 'lifecycle-native1-case-registry-v1'){
    throw 'LIFECYCLE-SELECTOR: registry schema differs'
  }
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($case in $Registry.cases){
    if([string]::IsNullOrWhiteSpace($case.id) -or -not $seen.Add($case.id)){
      throw 'LIFECYCLE-SELECTOR: missing or duplicate registry ID'
    }
    if($case.handler -cne 'native-fixture' -or $case.expectedVerdict -cne 'accept' -or
      $case.expectedExit -ne 0 -or $case.expectedStderr -cne '' -or
      $case.expectedStdout -cne ('LIFE-NATIVE1 PASS '+$case.id+"`n")){
      throw ('LIFECYCLE-SELECTOR: handler/verdict/stream mapping differs '+$case.id)
    }
  }
  if(($Registry.orderedIds -join '|') -cne ($Registry.cases.id -join '|')){
    throw 'LIFECYCLE-SELECTOR: ordered registry differs'
  }
  if(-not $SelectorBound){return @($Registry.orderedIds)}
  if($null -eq $Selector -or @($Selector).Count -eq 0){throw 'LIFECYCLE-SELECTOR: explicitly empty selector'}
  $selected=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($id in @($Selector)){
    if($id -isnot [string] -or [string]::IsNullOrWhiteSpace($id)){
      throw 'LIFECYCLE-SELECTOR: empty or whitespace selector'
    }
    if(-not $seen.Contains($id)){throw ('LIFECYCLE-SELECTOR: unknown ID '+$id)}
    if(-not $selected.Add($id)){throw ('LIFECYCLE-SELECTOR: duplicate ID '+$id)}
  }
  return @($Selector)
}

function Assert-LN1StartupWitnesses([string]$Root=$script:LN1Root) {
  $utf8=[Text.UTF8Encoding]::new($false,$true)
  $base=[IO.File]::ReadAllText((Join-Path $Root 'docs/internal/extensions/lifecycle-native1/BASE_IDENTITY.json'),$utf8)|ConvertFrom-Json
  $groups=@(
    @{module='RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory/SparseLevelWidth';
      definitions=@('def canonicalRelativeRmmInteriorCost33WitnessShape',
        'def canonicalRelativeRmmInteriorCost33WitnessInput')},
    @{module='RMQ/Core/SuccinctFinal/RAM/ReviewerReachabilitySmall';
      definitions=@('private def reviewerSingletonBeforeLCAState',
        'private def reviewerSingletonBeforeRankState',
        'private def reviewerIncreasingSixteenBeforeLCAState')})
  $checked=[Collections.Generic.List[object]]::new()
  foreach($group in $groups){
    $sourcePath=Join-Path $Root ($group.module+'.lean')
    $source=$utf8.GetString([IO.File]::ReadAllBytes($sourcePath))
    foreach($declaration in $group.definitions){
      $pattern='(?m)^@\[macro_inline\](\r?\n)('+[regex]::Escape($declaration)+')(?=\s|:)'
      if([regex]::Matches($source,$pattern).Count -ne 1){throw ('LIFECYCLE-STARTUP: exact annotation missing '+$declaration)}
      $source=[regex]::Replace($source,$pattern,'$2')
    }
    $pin=@($base.files|Where-Object{$_.path -ceq ($group.module+'.lean')})
    if($pin.Count -ne 1 -or (Get-LN1BytesHash ($utf8.GetBytes($source))) -cne $pin[0].rawSHA256){
      throw ('LIFECYCLE-STARTUP: amendment exceeds exact five insertions '+$group.module)
    }
    $generated=Join-Path $Root ('.lake/build/ir/'+$group.module+'.c')
    $emitted=$utf8.GetString([IO.File]::ReadAllBytes($generated))
    foreach($declaration in $group.definitions){
      $name=($declaration -split ' ')[-1]
      if($emitted.Contains($name,[StringComparison]::Ordinal)){
        throw ('LIFECYCLE-STARTUP: witness still present in generated C '+$name)
      }
    }
    $checked.Add(@{source=(Get-LN1Pin $sourcePath);generated=(Get-LN1Pin $generated);
      erasedDefinitions=$group.definitions;originalRawSHA256=$pin[0].rawSHA256})
  }
  [ordered]@{success=$true;exactInsertions=5;checked=@($checked.ToArray());
    boundary='Absence of these five proof-witness definitions in fresh emitted C; full startup and fixed-code measurements are separate required checks.'}
}
