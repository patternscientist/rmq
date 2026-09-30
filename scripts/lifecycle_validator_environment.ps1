# Lifecycle-local adapter. The shared helper string-casts environment overrides,
# so omission must be represented by an absent inherited process key instead.
function Invoke-LifecycleValidatorProcess {
  [CmdletBinding()]
  param(
    [Parameter(Mandatory=$true)][string]$FilePath,
    [string[]]$Arguments=@(),
    [Parameter(Mandatory=$true)][string]$WorkingDirectory,
    [Parameter(Mandatory=$true)][string]$Stage,
    [ValidateRange(1,7200)][int]$DeadlineSeconds=30,
    [Parameter(Mandatory=$true)][string]$TempRoot,
    [AllowNull()][AllowEmptyString()][object]$Selector=$null
  )
  if($null -ne $Selector -and $Selector -isnot [string]) {
    throw 'LIFE1-ENVIRONMENT: selector must be absent or an exact string'
  }
  $key='LIFE1_VALIDATE_SELECTOR'
  $prior=[Environment]::GetEnvironmentVariables('Process')
  $wasPresent=$prior.Contains($key)
  $priorValue=if($wasPresent){[string]$prior[$key]}else{$null}
  try {
    if($null -eq $Selector) {
      [Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')
    } else {
      [Environment]::SetEnvironmentVariable($key,[string]$Selector,'Process')
    }
    # The unchanged helper inherits the exact process key state. Never put a
    # null or empty "omission" override into its serialized environment map.
    return Invoke-RMQOwnedBoundedProcess -FilePath $FilePath -Arguments $Arguments `
      -WorkingDirectory $WorkingDirectory -Stage $Stage -DeadlineSeconds $DeadlineSeconds `
      -OutputLimitBytes 1048576 -TempRoot $TempRoot -Environment @{LEAN_NUM_THREADS='1'}
  } finally {
    if($wasPresent) {
      [Environment]::SetEnvironmentVariable($key,$priorValue,'Process')
    } else {
      [Environment]::SetEnvironmentVariable($key,[NullString]::Value,'Process')
    }
    $after=[Environment]::GetEnvironmentVariables('Process')
    if($after.Contains($key) -ne $wasPresent -or
       ($wasPresent -and [string]$after[$key] -cne $priorValue)) {
      throw 'LIFE1-ENVIRONMENT: caller process environment restoration failed'
    }
  }
}
