# LIFE-1-R4 durable-result predicates shared by the failure-control runner
# (repair-r3/failure_controls.ps1) and the synthetic predicate controls in
# repair-r4/aux_controls.ps1. Dot-source only; nothing runs at load time.
# Every function is total over parsed JSON (PSCustomObject) input and returns a
# [pscustomobject] with `ok` and a `reason` naming the first violated clause.

# Pin coverage (audit P3-2 (b), V1 REQ-EH1). A pin is "captured" only when its
# entrySha256 is a 64-hex string. The historical K2 receipt also stores its Git
# commit identity in that legacy field; the V1 roster marks that one row as
# git-sha1 and checks exactly 40 hex digits instead. V1 registries supply an
# independently written, ordered per-harness roster and a named capture stage.
# Dynamic roster rows are resolved from trusted parent context before comparison;
# the receipt never supplies its own expected root, shell or pinned input path.
# That resolved roster, not the receipt's entryPinCount, determines which path
# identities must occur and which rows must have entry captures. The receipt
# count remains a consistency check.
# Historical registries without a roster retain their count-based predicate.
# With -AllVerified (expected-accept shapes) every captured pin must be verified
# and every uncaptured row must be a verified absence, as R3 required of P.
function Get-R4ContextField([AllowNull()][object]$Context,[string]$Name) {
  if($null -eq $Context){return $null}
  if($Context -is [Collections.IDictionary] -and $Context.Contains($Name)){return $Context[$Name]}
  $property=$Context.PSObject.Properties[$Name]
  if($null -ne $property){return $property.Value}
  return $null
}

function Get-R4CanonicalPathIdentity([string]$Path) {
  if([string]::IsNullOrWhiteSpace($Path)){return $null}
  try {
    if([IO.Path]::IsPathRooted($Path)){
      return [IO.Path]::GetFullPath($Path).TrimEnd('\','/').Replace('/','\').ToLowerInvariant()
    }
    return $Path.Replace('\','/').ToLowerInvariant()
  } catch {return $null}
}

function Resolve-R4RosterPath([string]$Rule,[AllowNull()][object]$Context) {
  if([string]::IsNullOrWhiteSpace($Rule)){return [pscustomobject]@{ok=$false;path=$null;reason='empty roster path rule'}}
  $contextName=$null;$tail=$null
  if($Rule.StartsWith('fixture:',[StringComparison]::Ordinal)){
    $contextName='fixtureRoot';$tail=$Rule.Substring(8)
    if([string]::IsNullOrWhiteSpace($tail) -or [IO.Path]::IsPathRooted($tail)){
      return [pscustomobject]@{ok=$false;path=$null;reason=('invalid fixture-relative roster path '+$Rule)}
    }
    $root=[string](Get-R4ContextField $Context $contextName)
    if([string]::IsNullOrWhiteSpace($root)){
      return [pscustomobject]@{ok=$false;path=$null;reason=('missing trusted path context '+$contextName+' for '+$Rule)}
    }
    try {
      $rootFull=[IO.Path]::GetFullPath($root).TrimEnd('\','/')
      $path=[IO.Path]::GetFullPath((Join-Path $rootFull $tail))
      $prefix=$rootFull+[IO.Path]::DirectorySeparatorChar
      if(-not $path.StartsWith($prefix,[StringComparison]::OrdinalIgnoreCase)){
        return [pscustomobject]@{ok=$false;path=$null;reason=('fixture roster path escaped trusted root '+$Rule)}
      }
      return [pscustomobject]@{ok=$true;path=$path;reason='resolved fixture path'}
    } catch {return [pscustomobject]@{ok=$false;path=$null;reason=('invalid trusted fixture path '+$Rule)}}
  }
  if($Rule.StartsWith('shell:',[StringComparison]::Ordinal)){
    $role=$Rule.Substring(6)
    $contextName=if($role -ceq 'child'){'childShell'}elseif($role -ceq 'host'){'hostShell'}else{$null}
    if($null -eq $contextName){return [pscustomobject]@{ok=$false;path=$null;reason=('unknown shell roster role '+$role)}}
    $path=[string](Get-R4ContextField $Context $contextName)
    if([string]::IsNullOrWhiteSpace($path) -or -not [IO.Path]::IsPathRooted($path)){
      return [pscustomobject]@{ok=$false;path=$null;reason=('missing trusted path context '+$contextName+' for '+$Rule)}
    }
    try{return [pscustomobject]@{ok=$true;path=[IO.Path]::GetFullPath($path);reason=('resolved shell role '+$role)}}
    catch{return [pscustomobject]@{ok=$false;path=$null;reason=('invalid trusted shell path '+$role)}}
  }
  if($Rule.StartsWith('toolchain:',[StringComparison]::Ordinal)){
    $tail=$Rule.Substring(10);$contextName='toolchainBin'
    if([string]::IsNullOrWhiteSpace($tail) -or $tail -cne [IO.Path]::GetFileName($tail)){
      return [pscustomobject]@{ok=$false;path=$null;reason=('invalid toolchain roster leaf '+$Rule)}
    }
    $root=[string](Get-R4ContextField $Context $contextName)
    if([string]::IsNullOrWhiteSpace($root) -or -not [IO.Path]::IsPathRooted($root)){
      return [pscustomobject]@{ok=$false;path=$null;reason=('missing trusted path context '+$contextName+' for '+$Rule)}
    }
    try{return [pscustomobject]@{ok=$true;path=[IO.Path]::GetFullPath((Join-Path $root $tail));reason='resolved toolchain path'}}
    catch{return [pscustomobject]@{ok=$false;path=$null;reason=('invalid trusted toolchain path '+$Rule)}}
  }
  if($Rule.StartsWith('history:',[StringComparison]::Ordinal)){
    $role=$Rule.Substring(8);$contextName='historicalSummary'
    if($role -cne 'raw-summary'){return [pscustomobject]@{ok=$false;path=$null;reason=('unknown history roster role '+$role)}}
    $path=[string](Get-R4ContextField $Context $contextName)
    if([string]::IsNullOrWhiteSpace($path) -or -not [IO.Path]::IsPathRooted($path)){
      return [pscustomobject]@{ok=$false;path=$null;reason=('missing trusted path context '+$contextName+' for '+$Rule)}
    }
    try{return [pscustomobject]@{ok=$true;path=[IO.Path]::GetFullPath($path);reason='resolved historical summary'}}
    catch{return [pscustomobject]@{ok=$false;path=$null;reason='invalid trusted historical summary path'}}
  }
  if($Rule.StartsWith('suffix:',[StringComparison]::Ordinal) -or $Rule.StartsWith('regex:',[StringComparison]::Ordinal)){
    return [pscustomobject]@{ok=$false;path=$null;reason=('broad roster path rule is unsupported: '+$Rule)}
  }
  return [pscustomobject]@{ok=$true;path=$Rule;reason='exact static path'}
}

function Test-R4RosterPath([string]$Path,[string]$Expected) {
  $actualCanonical=Get-R4CanonicalPathIdentity $Path
  $expectedCanonical=Get-R4CanonicalPathIdentity $Expected
  return $null -ne $actualCanonical -and $null -ne $expectedCanonical -and $actualCanonical.Equals($expectedCanonical,[StringComparison]::Ordinal)
}

function Test-R4PinCoverage([object]$Finalization,[AllowNull()][object]$CapturedBeforeFailure,[bool]$AllVerified,
    [AllowNull()][object]$Roster=$null,[AllowNull()][string]$CaptureStage=$null,[AllowNull()][object]$TrustedContext=$null) {
  if($null -eq $Finalization){return [pscustomobject]@{ok=$false;reason='no finalization'}}
  $prop=$Finalization.PSObject.Properties['pinChecks']
  if($null -eq $prop){return [pscustomobject]@{ok=$false;reason='no pinChecks'}}
  $checks=@($prop.Value)
  if($checks.Count -eq 0){return [pscustomobject]@{ok=$false;reason='empty pinChecks'}}
  $expectedRows=$null
  $expectedCaptured=$null
  $expectedKinds=$null
  if($null -ne $Roster){
    if([string]::IsNullOrWhiteSpace($CaptureStage)){return [pscustomobject]@{ok=$false;reason='no capture stage'}}
    $stagesProp=$Roster.PSObject.Properties['stages']
    $rowsProp=$Roster.PSObject.Properties['rows']
    if($null -eq $stagesProp -or $null -eq $rowsProp){return [pscustomobject]@{ok=$false;reason='malformed pin roster'}}
    $stageProp=$stagesProp.Value.PSObject.Properties[$CaptureStage]
    if($null -eq $stageProp){return [pscustomobject]@{ok=$false;reason=('unknown capture stage '+$CaptureStage)}}
    $stage=$stageProp.Value
    $baseRosterRules=@($rowsProp.Value)
    if($baseRosterRules.Count -eq 0){return [pscustomobject]@{ok=$false;reason='empty base pin roster'}}
    $baseKinds=@(for($i=0;$i -lt $baseRosterRules.Count;$i++){'sha256'})
    $kindsProp=$Roster.PSObject.Properties['identityKinds']
    if($null -ne $kindsProp){
      foreach($kindProperty in $kindsProp.Value.PSObject.Properties){
        $kindIndex=0
        if(-not [int]::TryParse($kindProperty.Name,[ref]$kindIndex) -or $kindIndex -lt 0 -or $kindIndex -ge $baseKinds.Count){
          return [pscustomobject]@{ok=$false;reason=('invalid identity-kind index '+$kindProperty.Name)}
        }
        if([string]$kindProperty.Value -cne 'git-sha1'){return [pscustomobject]@{ok=$false;reason=('unknown identity kind '+$kindProperty.Value)}}
        $baseKinds[$kindIndex]='git-sha1'
      }
    }
    $stageRows=$stage.PSObject.Properties['rows']
    if($null -ne $stageRows){
      $rosterRules=@($stageRows.Value)
      $projectedKinds=[Collections.Generic.List[string]]::new()
      $baseCursor=0
      foreach($stageRule in $rosterRules){
        $baseIndex=-1
        for($j=$baseCursor;$j -lt $baseRosterRules.Count;$j++){
          if([string]$baseRosterRules[$j] -ceq [string]$stageRule){$baseIndex=$j;break}
        }
        if($baseIndex -lt 0){return [pscustomobject]@{ok=$false;reason=('stage roster row is not an ordered base-roster projection: '+$stageRule)}}
        $projectedKinds.Add([string]$baseKinds[$baseIndex])
        $baseCursor=$baseIndex+1
      }
      $expectedKinds=@($projectedKinds.ToArray())
    } else {
      $rosterRules=$baseRosterRules
      $expectedKinds=@($baseKinds)
    }
    $resolvedRows=[Collections.Generic.List[string]]::new()
    foreach($rawRule in $rosterRules){
      $resolution=Resolve-R4RosterPath ([string]$rawRule) $TrustedContext
      if(-not $resolution.ok){return [pscustomobject]@{ok=$false;reason=$resolution.reason}}
      $resolvedRows.Add([string]$resolution.path)
    }
    $expectedRows=@($resolvedRows.ToArray())
    $capturedProp=$stage.PSObject.Properties['capturedIndexes']
    if($null -eq $capturedProp){return [pscustomobject]@{ok=$false;reason=('capture stage '+$CaptureStage+' has no capturedIndexes')}}
    $expectedCaptured=[Collections.Generic.HashSet[int]]::new()
    foreach($raw in @($capturedProp.Value)){
      if($raw -isnot [ValueType]){return [pscustomobject]@{ok=$false;reason=('non-numeric captured index in stage '+$CaptureStage)}}
      $index=[int]$raw
      if($index -lt 0 -or $index -ge $expectedRows.Count -or -not $expectedCaptured.Add($index)){
        return [pscustomobject]@{ok=$false;reason=('invalid captured index '+$index+' in stage '+$CaptureStage)}
      }
    }
    if($checks.Count -ne $expectedRows.Count){
      return [pscustomobject]@{ok=$false;reason=('pinCheck roster count '+$checks.Count+' differs from expected '+$expectedRows.Count)}
    }
  }
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $captured=0
  for($i=0;$i -lt $checks.Count;$i++){
    $c=$checks[$i]
    if($null -eq $c -or $null -eq $c.PSObject.Properties['path'] -or $null -eq $c.PSObject.Properties['status'] -or $null -eq $c.PSObject.Properties['entrySha256'] -or $null -eq $c.PSObject.Properties['finalSha256']){
      return [pscustomobject]@{ok=$false;reason='malformed pinCheck row'}
    }
    if($null -eq $expectedRows -and -not $seen.Add([string]$c.path)){return [pscustomobject]@{ok=$false;reason=('duplicate pinCheck path '+$c.path)}}
    if($null -ne $expectedRows -and -not (Test-R4RosterPath ([string]$c.path) ([string]$expectedRows[$i]))){
      return [pscustomobject]@{ok=$false;reason=('pinCheck path at roster index '+$i+' differs from trusted expected path: '+$c.path)}
    }
    $status=[string]$c.status
    if($null -ne $c.entrySha256){
      # v1/v2 have no roster metadata, but K2 historically recorded its exact
      # commit under the literal git:HEAD pseudo-path. Preserve that one typed
      # legacy identity while every other unrostered row remains file SHA-256.
      $identityKind=if($null -ne $expectedKinds){$expectedKinds[$i]}elseif([string]$c.path -ceq 'git:HEAD'){'git-sha1'}else{'sha256'}
      $identityPattern=if($identityKind -ceq 'git-sha1'){'^[0-9A-Fa-f]{40}$'}else{'^[0-9A-Fa-f]{64}$'}
      if($c.entrySha256 -isnot [string] -or [string]$c.entrySha256 -cnotmatch $identityPattern){
        $identityLabel=if($identityKind -ceq 'git-sha1'){'Git SHA1'}else{'SHA256'}
        return [pscustomobject]@{ok=$false;reason=('malformed captured '+$identityLabel+': '+$c.path)}
      }
      $captured++
      if($null -ne $expectedCaptured -and -not $expectedCaptured.Contains($i)){
        return [pscustomobject]@{ok=$false;reason=('unexpected captured pin at roster index '+$i+': '+$c.path)}
      }
      if(@('verified','changed','unreadable-final') -cnotcontains $status){return [pscustomobject]@{ok=$false;reason=('captured pin not re-verified: '+$c.path+' status '+$status)}}
      $final=$c.finalSha256
      if($status -ceq 'unreadable-final'){
        if($null -ne $final){return [pscustomobject]@{ok=$false;reason=('unreadable-final pin has a final identity: '+$c.path)}}
      } else {
        if($null -eq $final){return [pscustomobject]@{ok=$false;reason=('missing final identity for '+$status+' pin: '+$c.path)}}
        if($final -isnot [string] -or [string]$final -cnotmatch $identityPattern){
          $identityLabel=if($identityKind -ceq 'git-sha1'){'Git SHA1'}else{'SHA256'}
          return [pscustomobject]@{ok=$false;reason=('malformed final '+$identityLabel+' for '+$status+' pin: '+$c.path)}
        }
        $same=([string]$final).Equals([string]$c.entrySha256,[StringComparison]::OrdinalIgnoreCase)
        if($status -ceq 'verified' -and -not $same){return [pscustomobject]@{ok=$false;reason=('verified final identity differs from entry: '+$c.path)}}
        if($status -ceq 'changed' -and $same){return [pscustomobject]@{ok=$false;reason=('changed final identity equals entry: '+$c.path)}}
      }
      if($AllVerified -and $status -cne 'verified'){return [pscustomobject]@{ok=$false;reason=('captured pin not verified: '+$c.path+' status '+$status)}}
    } else {
      if($null -ne $expectedCaptured -and $expectedCaptured.Contains($i)){
        return [pscustomobject]@{ok=$false;reason=('required pin not captured at roster index '+$i+': '+$c.path)}
      }
      if(@('not-captured','absent-verified','appeared') -cnotcontains $status){return [pscustomobject]@{ok=$false;reason=('uncaptured pin with status '+$status+': '+$c.path)}}
      if($null -ne $c.finalSha256){return [pscustomobject]@{ok=$false;reason=('uncaptured pin has a final identity: '+$c.path)}}
      if($AllVerified -and $status -cne 'absent-verified'){return [pscustomobject]@{ok=$false;reason=('uncaptured pin not absent-verified: '+$c.path+' status '+$status)}}
    }
  }
  $countProp=$Finalization.PSObject.Properties['entryPinCount']
  if($null -eq $countProp -or $countProp.Value -isnot [ValueType]){return [pscustomobject]@{ok=$false;reason='no entryPinCount'}}
  if([int]$countProp.Value -ne $captured){return [pscustomobject]@{ok=$false;reason=('captured rows '+$captured+' differ from entryPinCount '+$countProp.Value)}}
  if($null -ne $CapturedBeforeFailure -and [int]$CapturedBeforeFailure -ne $captured){
    return [pscustomobject]@{ok=$false;reason=('captured rows '+$captured+' differ from the registry count '+$CapturedBeforeFailure)}
  }
  $rosterReason=if($null -ne $expectedRows){', exact roster stage '+$CaptureStage}else{''}
  $relation=if($AllVerified){'all verified'}else{'status/final identities consistent'}
  return [pscustomobject]@{ok=$true;reason=('captured '+$captured+' of '+$checks.Count+' rows, '+$relation+$rosterReason)}
}

# Entry-pin labels (audit P3-5). For each declared label the durable document
# must carry the entry pin under entryKey (equal to the pinCheck entry value),
# the pinCheck row must have the declared status, and the plain key must be null
# or the post-run value (equal to the pinCheck final value); when the pin
# changed, the plain key must not present the entry value.
function Test-R4Labels([object]$Document,[object[]]$Labels) {
  if($null -eq $Document){return [pscustomobject]@{ok=$false;reason='no durable document'}}
  $fin=$null;if($null -ne $Document.PSObject.Properties['finalization']){$fin=$Document.finalization}
  if($null -eq $fin -or $null -eq $fin.PSObject.Properties['pinChecks']){return [pscustomobject]@{ok=$false;reason='no pinChecks'}}
  foreach($l in @($Labels)){
    $row=@(@($fin.pinChecks)|Where-Object {[string]$_.path -ceq [string]$l.path})
    if($row.Count -ne 1){return [pscustomobject]@{ok=$false;reason=('no unique pinCheck for '+$l.path)}}
    if([string]$row[0].status -cne [string]$l.status){return [pscustomobject]@{ok=$false;reason=('pin '+$l.path+' status '+$row[0].status+', expected '+$l.status)}}
    $entryProp=$Document.PSObject.Properties[[string]$l.entryKey]
    if($null -eq $entryProp -or $null -eq $entryProp.Value -or $null -eq $entryProp.Value.PSObject.Properties['sha256']){return [pscustomobject]@{ok=$false;reason=('no entry label '+$l.entryKey)}}
    if([string]$entryProp.Value.sha256 -cne [string]$row[0].entrySha256){return [pscustomobject]@{ok=$false;reason=($l.entryKey+' differs from the entry pin')}}
    $plainProp=$Document.PSObject.Properties[[string]$l.key]
    if($null -eq $plainProp){return [pscustomobject]@{ok=$false;reason=('no key '+$l.key)}}
    if($null -ne $plainProp.Value){
      if($null -eq $plainProp.Value.PSObject.Properties['sha256']){return [pscustomobject]@{ok=$false;reason=($l.key+' is not a pin')}}
      if([string]$plainProp.Value.sha256 -cne [string]$row[0].finalSha256){return [pscustomobject]@{ok=$false;reason=($l.key+' is not the post-run pin')}}
    }
    if([string]$l.status -ceq 'changed' -and $null -ne $plainProp.Value -and [string]$plainProp.Value.sha256 -ceq [string]$entryProp.Value.sha256){
      return [pscustomobject]@{ok=$false;reason=($l.key+' presents the entry value for a changed pin')}
    }
  }
  return [pscustomobject]@{ok=$true;reason=('labels '+(@($Labels|ForEach-Object {$_.key}) -join ',')+' consistent')}
}

# Exact typed value witnesses: some property with the given name anywhere in the
# durable document (collected by the runner, pinChecks excluded) equals the
# expected JSON value with the same JSON type.
function Test-R4Values([object[]]$Collected,[object[]]$Expected) {
  foreach($e in @($Expected)){
    $want=$e.value
    $hit=@($Collected|Where-Object {
      $_.name -ceq [string]$e.name -and $(
        if($want -is [bool]){$_.value -is [bool] -and $_.value -eq $want}
        elseif($want -is [string]){$_.value -is [string] -and $_.value -ceq $want}
        else{$_.value -is [ValueType] -and $_.value -isnot [bool] -and [double]$_.value -eq [double]$want})
    }).Count
    if($hit -eq 0){return [pscustomobject]@{ok=$false;reason=('no value '+$e.name+'='+$want)}}
  }
  return [pscustomobject]@{ok=$true;reason='all values present'}
}
