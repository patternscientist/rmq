# LIFE-1-R4 durable-result predicates shared by the failure-control runner
# (repair-r3/failure_controls.ps1) and the synthetic predicate controls in
# repair-r4/aux_controls.ps1. Dot-source only; nothing runs at load time.
# Every function is total over parsed JSON (PSCustomObject) input and returns a
# [pscustomobject] with `ok` and a `reason` naming the first violated clause.

# Pin coverage (audit P3-2 (b)). A pin is "captured" when its pinCheck row has a
# non-null entrySha256. Every captured pin must have been re-verified in
# finalization (status verified, changed or unreadable-final, never
# not-captured or silently absent); every uncaptured row must say so; rows are
# unique by path; the number of captured rows must equal the harness's own
# entryPinCount (a captured pin missing from pinChecks makes these differ); and
# when the registry states how many pins the harness captures before the
# injected failure, the captured count must equal that independent number.
# With -AllVerified (expected-accept shapes) every captured pin must be verified
# and every uncaptured row must be a verified absence, as R3 required of P.
function Test-R4PinCoverage([object]$Finalization,[AllowNull()][object]$CapturedBeforeFailure,[bool]$AllVerified) {
  if($null -eq $Finalization){return [pscustomobject]@{ok=$false;reason='no finalization'}}
  $prop=$Finalization.PSObject.Properties['pinChecks']
  if($null -eq $prop){return [pscustomobject]@{ok=$false;reason='no pinChecks'}}
  $checks=@($prop.Value)
  if($checks.Count -eq 0){return [pscustomobject]@{ok=$false;reason='empty pinChecks'}}
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $captured=0
  foreach($c in $checks){
    if($null -eq $c -or $null -eq $c.PSObject.Properties['path'] -or $null -eq $c.PSObject.Properties['status'] -or $null -eq $c.PSObject.Properties['entrySha256']){
      return [pscustomobject]@{ok=$false;reason='malformed pinCheck row'}
    }
    if(-not $seen.Add([string]$c.path)){return [pscustomobject]@{ok=$false;reason=('duplicate pinCheck path '+$c.path)}}
    $status=[string]$c.status
    if($null -ne $c.entrySha256){
      $captured++
      if(@('verified','changed','unreadable-final') -cnotcontains $status){return [pscustomobject]@{ok=$false;reason=('captured pin not re-verified: '+$c.path+' status '+$status)}}
      if($AllVerified -and $status -cne 'verified'){return [pscustomobject]@{ok=$false;reason=('captured pin not verified: '+$c.path+' status '+$status)}}
    } else {
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
  return [pscustomobject]@{ok=$true;reason=('captured '+$captured+' of '+$checks.Count+' rows, all re-verified')}
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
