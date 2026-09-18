# PRE-1-R1: run the cheap, non-campaign modes of the unchanged PRE-1 checkers
# and record their pinned registry and surface hashes.
#
# No mode here builds Lean or runs a mutation campaign. The modes are the two
# firewalls and, for both replay runners, -SelectorProbeOnly,
# -RegistrySelfTestOnly, -SelectorBoundarySelfTestOnly and -DeadlineSelfTestOnly.
# The aggregate checkers scripts/preprocessing_builder_gate.ps1 (full builder
# replay) and scripts/preprocessing_contract_gate.ps1 (contract lake build) are
# campaigns or Lean builds and are not run here.
#
# Every mode runs as one owned bounded child of -ShellPath with the repository
# root as working directory; replay evidence goes under -OutDir, which must lie
# outside the repository and must not exist yet, so the repository's ignored
# .lake tree is not written either. The repository must be clean before, and
# HEAD, status, worktree and index diffs must be identical after.
# Exit codes: 0 every mode passed with its exact marker; 1 a mode failed or the
# repository state changed; 3 a mode timed out or overflowed, or the start was dirty.
[CmdletBinding()]
param(
  [string]$RepoRoot = '',
  [string]$OutDir = '',
  [string]$ReceiptPath = '',
  [string]$ShellPath = '',
  [ValidateRange(1, 7200)][int]$ModeDeadlineSeconds = 1200
)
$ErrorActionPreference = 'Stop'
if ([string]::IsNullOrWhiteSpace($RepoRoot)) { $RepoRoot = Join-Path $PSScriptRoot '../../../../..' }
$repo = [IO.Path]::GetFullPath($RepoRoot)
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
if ([string]::IsNullOrWhiteSpace($OutDir)) {
  $OutDir = Join-Path ([IO.Path]::GetTempPath()) ('pre1-r1-checker-modes-' + [Guid]::NewGuid().ToString('N'))
}
$out = [IO.Path]::GetFullPath($OutDir)
$repoPrefix = $repo.TrimEnd('\', '/') + [IO.Path]::DirectorySeparatorChar
if ($out.StartsWith($repoPrefix, [StringComparison]::OrdinalIgnoreCase) -or $out -eq $repo) {
  Write-Output "CHECKER-MODES: ERROR -OutDir $out lies inside the repository"; exit 3
}
if (Test-Path -LiteralPath $out) { Write-Output "CHECKER-MODES: ERROR -OutDir $out already exists"; exit 3 }
if ([string]::IsNullOrWhiteSpace($ReceiptPath)) { $ReceiptPath = Join-Path $out 'receipt.json' }
$receiptFull = [IO.Path]::GetFullPath($ReceiptPath)
if ([string]::IsNullOrWhiteSpace($ShellPath)) { $ShellPath = (Get-Process -Id $PID).Path }
$gitPath = Resolve-RMQScalarApplicationPath @(Get-Command git -CommandType Application -ErrorAction Stop) 'git'
$utf8 = [Text.UTF8Encoding]::new($false)
$utf8Strict = [Text.UTF8Encoding]::new($false, $true)
[void](New-Item -ItemType Directory -Path $out)
$owned = Join-Path $out 'owned'

function Get-TextSha256([string]$Text) {
  return [BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash($utf8.GetBytes($Text))).Replace('-', '')
}
function Get-NormalizedSha256([string]$Rel) {
  $text = $utf8Strict.GetString([IO.File]::ReadAllBytes((Join-Path $repo $Rel))).Replace("`r`n", "`n")
  return [BitConverter]::ToString([Security.Cryptography.SHA256]::Create().ComputeHash($utf8Strict.GetBytes($text))).Replace('-', '').ToLowerInvariant()
}
function Get-State([string]$Label) {
  $head = (@(Invoke-RMQCheckedGit $gitPath $repo @('rev-parse', 'HEAD') "$Label-head" 120 1048576 $owned) -join '').Trim()
  $state = Get-RMQRepositoryStateBounded -RepositoryRoot $repo -GitPath $gitPath -DeadlineSeconds 600 `
    -OutputLimitBytes 67108864 -TempRoot $owned -StagePrefix "$Label-state"
  return [pscustomobject]@{ Head = $head; State = [string]$state }
}
function Get-Pin([string]$Rel, [string]$Pattern) {
  $m = [regex]::Match([IO.File]::ReadAllText((Join-Path $repo $Rel)), $Pattern)
  if (-not $m.Success) { return $null }
  return $m.Groups[1].Value
}

$before = Get-State 'before'
$stateLines = @($before.State -split "`r?`n" | Where-Object { $_ -ne '' })
$clean = ($stateLines.Count -eq 2 -and $stateLines[0] -eq '---WORKTREE---' -and $stateLines[1] -eq '---INDEX---')
$shellVersion = (@(& $ShellPath -NoLogo -NoProfile -Command '$PSVersionTable.PSVersion.ToString()') -join '').Trim()
$receipt = [ordered]@{
  version = 'PRE1-R1-CHECKER-MODES-RECEIPT-V1'; head = $before.Head; cleanBefore = $clean
  host = [Environment]::MachineName; os = [Environment]::OSVersion.VersionString; shell = $ShellPath; shellVersion = $shellVersion
  mutex = 'not taken by this runner (no Lean build and no campaign)'
  pins = [ordered]@{
    builderReplayExpectedRegistrySha256 = Get-Pin 'scripts/preprocessing_builder_replay.ps1' "ExpectedRegistrySha256 = '([0-9a-f]{64})'"
    contractReplayExpectedRegistrySha256 = Get-Pin 'scripts/preprocessing_contract_replay.ps1' "ExpectedRegistrySha256 = '([0-9a-f]{64})'"
    builderCasesNormalizedSha256 = Get-NormalizedSha256 'docs/internal/extensions/pre1/builder_cases.json'
    contractCasesNormalizedSha256 = Get-NormalizedSha256 'docs/internal/extensions/pre1/contract_cases.json'
    builderManifestNormalizedSha256 = Get-NormalizedSha256 'docs/internal/extensions/pre1/builder_manifest.json'
    primitiveManifestNormalizedSha256 = Get-NormalizedSha256 'docs/internal/extensions/pre1/primitive_manifest.json'
    contractFirewallNormalizedSha256 = Get-NormalizedSha256 'scripts/preprocessing_contract_firewall.ps1'
    contractReplayNormalizedSha256 = Get-NormalizedSha256 'scripts/preprocessing_contract_replay.ps1'
  }
  modes = @(); stateUnchanged = $false; result = 'INCONCLUSIVE'
}
if (-not $clean) {
  Write-Output 'CHECKER-MODES: ERROR the repository is not clean before the modes'
  [IO.File]::WriteAllText($receiptFull, ($receipt | ConvertTo-Json -Depth 12), $utf8)
  exit 3
}

$plan = @(
  @{ Name = 'builder-firewall'; Script = 'scripts/preprocessing_builder_firewall.ps1'; Args = @(); Evidence = $false
     Marker = 'PRE1-BUILDER-FIREWALL PASS: layered closure over the contract guard, 17 modules' },
  @{ Name = 'contract-firewall'; Script = 'scripts/preprocessing_contract_firewall.ps1'; Args = @(); Evidence = $false
     Marker = 'PRE1-FIREWALL PASS: exact Std-only primitive closure and frozen evaluator bytes' },
  @{ Name = 'builder-selector-probe'; Script = 'scripts/preprocessing_builder_replay.ps1'; Args = @('-SelectorProbeOnly'); Evidence = $false
     Marker = 'PRE-BUILDER-SELECTOR-PROBE: selected=52 ids=' },
  @{ Name = 'builder-registry-selftest'; Script = 'scripts/preprocessing_builder_replay.ps1'; Args = @('-RegistrySelfTestOnly'); Evidence = $true
     Marker = 'PRE-BUILDER-REPLAY: PASS mode=registry-selftest executed=0 registry=52 evidence=' },
  @{ Name = 'builder-selector-selftest'; Script = 'scripts/preprocessing_builder_replay.ps1'; Args = @('-SelectorBoundarySelfTestOnly'); Evidence = $true
     Marker = 'PRE-BUILDER-REPLAY: PASS mode=selector-selftest executed=0 registry=52 evidence=' },
  @{ Name = 'builder-deadline-selftest'; Script = 'scripts/preprocessing_builder_replay.ps1'; Args = @('-DeadlineSelfTestOnly'); Evidence = $true
     Marker = 'PRE-BUILDER-REPLAY: PASS mode=deadline-selftest executed=0 registry=52 evidence=' },
  @{ Name = 'contract-selector-probe'; Script = 'scripts/preprocessing_contract_replay.ps1'; Args = @('-SelectorProbeOnly'); Evidence = $false
     Marker = 'PRE-SELECTOR-PROBE: selected=18 ids=' },
  @{ Name = 'contract-registry-selftest'; Script = 'scripts/preprocessing_contract_replay.ps1'; Args = @('-RegistrySelfTestOnly'); Evidence = $true
     Marker = 'PRE-CONTRACT-REPLAY: PASS mode=registry-selftest executed=0 registry=18 evidence=' },
  @{ Name = 'contract-selector-selftest'; Script = 'scripts/preprocessing_contract_replay.ps1'; Args = @('-SelectorBoundarySelfTestOnly'); Evidence = $true
     Marker = 'PRE-CONTRACT-REPLAY: PASS mode=selector-selftest executed=0 registry=18 evidence=' },
  # The contract runner's 12 s sleeper default failed on this host (shell startup
  # measured 8.997 s; BUILDER replay parameter note); 45 s is the PRE-1-A1 value.
  @{ Name = 'contract-deadline-selftest'; Script = 'scripts/preprocessing_contract_replay.ps1'; Args = @('-DeadlineSelfTestOnly', '-SleeperDeadlineSeconds', '45'); Evidence = $true
     Marker = 'PRE-CONTRACT-REPLAY: PASS mode=deadline-selftest executed=0 registry=18 evidence=' }
)
$overall = 'PASS'
foreach ($step in $plan) {
  $arguments = @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', $step.Script) + $step.Args
  $evidence = $null
  if ($step.Evidence) {
    $evidence = Join-Path $out ('evidence-' + $step.Name)
    $arguments += @('-EvidenceDirectory', $evidence)
  }
  $started = [DateTime]::UtcNow
  $run = Invoke-RMQOwnedBoundedProcess -FilePath $ShellPath -Arguments $arguments -WorkingDirectory $repo `
    -Stage $step.Name -DeadlineSeconds $ModeDeadlineSeconds -OutputLimitBytes 67108864 -TempRoot $owned
  $markerLines = @($run.StandardOutput | Where-Object { ([string]$_).StartsWith($step.Marker, [StringComparison]::Ordinal) })
  $record = [ordered]@{
    name = $step.Name; command = ($step.Script + ' ' + ($step.Args -join ' ')).Trim(); startedUtc = $started.ToString('o')
    exit = $run.ExitCode; seconds = $run.DurationSeconds; deadline = $run.DeadlineSeconds; timedOut = $run.TimedOut
    outputLimitExceeded = $run.OutputLimitExceeded; ownership = $run.Ownership; marker = $step.Marker
    markerLines = $markerLines.Count; stdoutLines = @($run.StandardOutput).Count; stderrLines = @($run.StandardError).Count
    stdout = @($run.StandardOutput | ForEach-Object { ([string]$_) -replace [regex]::Escape($out), '<OutDir>' })
    stderr = @($run.StandardError)
  }
  if ($step.Evidence) {
    $reports = @(Get-ChildItem -LiteralPath $evidence -Filter 'report.json' -Recurse -File -ErrorAction SilentlyContinue)
    if ($reports.Count -eq 1) {
      $r = Get-Content -LiteralPath $reports[0].FullName -Raw -Encoding UTF8 | ConvertFrom-Json
      $record.report = [ordered]@{ verdict = $r.verdict; mode = $r.mode; registrySha256 = $r.registrySha256
        registryContentSha256 = $r.registryContentSha256; runnerSha256 = $r.runnerSha256
        registryExpectedCount = @($r.registryExpected).Count; selectedExpectedCount = @($r.selectedExpected).Count
        executedCount = @($r.executed).Count; selfTests = @($r.selfTests).Count
        selfTestCategories = @($r.selfTests | ForEach-Object { [string]$_.category } | Sort-Object -Unique)
        platform = $r.platform; powershell = $r.powershell }
    } else { $record.report = $null }
  }
  $ok = (-not $run.TimedOut) -and (-not $run.OutputLimitExceeded) -and ($run.ExitCode -eq 0) -and ($markerLines.Count -eq 1)
  if ($step.Evidence) { $ok = $ok -and ($null -ne $record.report) -and ($record.report.verdict -ceq 'PASS') }
  $record.verdict = if ($ok) { 'PASS' } elseif ($run.TimedOut -or $run.OutputLimitExceeded) { 'INCONCLUSIVE' } else { 'FAIL' }
  if ($record.verdict -eq 'FAIL') { $overall = 'FAIL' } elseif ($record.verdict -eq 'INCONCLUSIVE' -and $overall -eq 'PASS') { $overall = 'INCONCLUSIVE' }
  $receipt.modes += $record
  Write-Output ("CHECKER-MODES: {0} [{1}] exit {2} in {3} s (deadline {4} s){5}" -f $record.verdict, $step.Name, $run.ExitCode,
      $run.DurationSeconds, $run.DeadlineSeconds, $(if ($step.Evidence -and $record.report) { " registry content sha256 $($record.report.registryContentSha256) self-tests $($record.report.selfTests)" } else { '' }))
}
$after = Get-State 'after'
$receipt.stateUnchanged = ($before.Head -ceq $after.Head) -and ($before.State -ceq $after.State)
if (-not $receipt.stateUnchanged) { $overall = 'FAIL' }
$receipt.result = $overall
Remove-Item -LiteralPath $owned -Recurse -Force -ErrorAction SilentlyContinue
[IO.File]::WriteAllText($receiptFull, ($receipt | ConvertTo-Json -Depth 12), $utf8)
Write-Output ("CHECKER-MODES: RESULT: {0} head {1} shell {2} state unchanged {3}" -f $overall, $before.Head, $shellVersion, $receipt.stateUnchanged)
if ($overall -eq 'PASS') { exit 0 }
if ($overall -eq 'INCONCLUSIVE') { exit 3 }
exit 1
