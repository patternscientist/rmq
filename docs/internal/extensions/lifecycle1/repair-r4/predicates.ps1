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
# That roster, not the receipt's entryPinCount, determines which path identities
# must occur and which rows must have entry captures. The receipt count remains a consistency check.
# Historical registries without a roster retain their count-based predicate.
# With -AllVerified (expected-accept shapes) every captured pin must be verified
# and every uncaptured row must be a verified absence, as R3 required of P.
function Test-R4RosterPath([string]$Path,[string]$Rule) {
  if([string]::IsNullOrWhiteSpace($Path) -or [string]::IsNullOrWhiteSpace($Rule)){return $false}
  $normalized=$Path.Replace('\','/')
  if($Rule.StartsWith('suffix:',[StringComparison]::Ordinal)){
    return $normalized.EndsWith($Rule.Substring(7),[StringComparison]::OrdinalIgnoreCase)
  }
  if($Rule.StartsWith('regex:',[StringComparison]::Ordinal)){
    return [regex]::IsMatch($normalized,$Rule.Substring(6),[Text.RegularExpressions.RegexOptions]::CultureInvariant)
  }
  return $normalized.Equals($Rule,[StringComparison]::Ordinal)
}

function Test-R4PinCoverage([object]$Finalization,[AllowNull()][object]$CapturedBeforeFailure,[bool]$AllVerified,
    [AllowNull()][object]$Roster=$null,[AllowNull()][string]$CaptureStage=$null) {
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
    $stageRows=$stage.PSObject.Properties['rows']
    $expectedRows=@($(if($null -ne $stageRows){$stageRows.Value}else{$rowsProp.Value}))
    $expectedKinds=@(for($i=0;$i -lt $expectedRows.Count;$i++){'sha256'})
    $kindsProp=$Roster.PSObject.Properties['identityKinds']
    if($null -ne $kindsProp){
      foreach($kindProperty in $kindsProp.Value.PSObject.Properties){
        $kindIndex=0
        if(-not [int]::TryParse($kindProperty.Name,[ref]$kindIndex) -or $kindIndex -lt 0){
          return [pscustomobject]@{ok=$false;reason=('invalid identity-kind index '+$kindProperty.Name)}
        }
        if($kindIndex -lt $expectedKinds.Count){
          if([string]$kindProperty.Value -cne 'git-sha1'){return [pscustomobject]@{ok=$false;reason=('unknown identity kind '+$kindProperty.Value)}}
          $expectedKinds[$kindIndex]='git-sha1'
        }
      }
    }
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
    if($null -eq $c -or $null -eq $c.PSObject.Properties['path'] -or $null -eq $c.PSObject.Properties['status'] -or $null -eq $c.PSObject.Properties['entrySha256']){
      return [pscustomobject]@{ok=$false;reason='malformed pinCheck row'}
    }
    if(-not $seen.Add([string]$c.path)){return [pscustomobject]@{ok=$false;reason=('duplicate pinCheck path '+$c.path)}}
    if($null -ne $expectedRows -and -not (Test-R4RosterPath ([string]$c.path) ([string]$expectedRows[$i]))){
      return [pscustomobject]@{ok=$false;reason=('pinCheck path at roster index '+$i+' differs: '+$c.path)}
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
      if($AllVerified -and $status -cne 'verified'){return [pscustomobject]@{ok=$false;reason=('captured pin not verified: '+$c.path+' status '+$status)}}
    } else {
      if($null -ne $expectedCaptured -and $expectedCaptured.Contains($i)){
        return [pscustomobject]@{ok=$false;reason=('required pin not captured at roster index '+$i+': '+$c.path)}
      }
      if(@('not-captured','absent-verified','appeared') -cnotcontains $status){return [pscustomobject]@{ok=$false;reason=('uncaptured pin with status '+$status+': '+$c.path)}}
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
  return [pscustomobject]@{ok=$true;reason=('captured '+$captured+' of '+$checks.Count+' rows, all re-verified'+$rosterReason)}
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
