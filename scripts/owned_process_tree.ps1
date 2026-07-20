#!/usr/bin/env pwsh

# Shared bounded-process and clean-baseline support for the M1 replay and
# topology harnesses.  The caller owns policy (deadlines, output limits, and
# verdicts); this file owns the operating-system process tree.

if (-not ('RMQOwnedWindowsJob' -as [type])) {
  Add-Type -TypeDefinition @'
using System;
using System.ComponentModel;
using System.Runtime.InteropServices;

public static class RMQOwnedWindowsJob {
  private const int JobObjectExtendedLimitInformation = 9;
  private const uint JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000;

  [StructLayout(LayoutKind.Sequential)]
  private struct IO_COUNTERS {
    public ulong ReadOperationCount, WriteOperationCount, OtherOperationCount;
    public ulong ReadTransferCount, WriteTransferCount, OtherTransferCount;
  }

  [StructLayout(LayoutKind.Sequential)]
  private struct JOBOBJECT_BASIC_LIMIT_INFORMATION {
    public long PerProcessUserTimeLimit, PerJobUserTimeLimit;
    public uint LimitFlags;
    public UIntPtr MinimumWorkingSetSize, MaximumWorkingSetSize;
    public uint ActiveProcessLimit;
    public UIntPtr Affinity;
    public uint PriorityClass, SchedulingClass;
  }

  [StructLayout(LayoutKind.Sequential)]
  private struct JOBOBJECT_EXTENDED_LIMIT_INFORMATION {
    public JOBOBJECT_BASIC_LIMIT_INFORMATION BasicLimitInformation;
    public IO_COUNTERS IoInfo;
    public UIntPtr ProcessMemoryLimit, JobMemoryLimit, PeakProcessMemoryUsed;
    public UIntPtr PeakJobMemoryUsed;
  }

  [DllImport("kernel32.dll", CharSet = CharSet.Unicode, SetLastError = true)]
  private static extern IntPtr CreateJobObject(IntPtr attributes, string name);

  [DllImport("kernel32.dll", SetLastError = true)]
  private static extern bool SetInformationJobObject(
    IntPtr job, int infoClass,
    ref JOBOBJECT_EXTENDED_LIMIT_INFORMATION info, uint length);

  [DllImport("kernel32.dll", SetLastError = true)]
  private static extern bool AssignProcessToJobObject(IntPtr job, IntPtr process);

  [DllImport("kernel32.dll", SetLastError = true)]
  private static extern bool CloseHandle(IntPtr handle);

  public static IntPtr CreateKillOnClose() {
    IntPtr job = CreateJobObject(IntPtr.Zero, null);
    if (job == IntPtr.Zero) throw new Win32Exception(Marshal.GetLastWin32Error());
    var info = new JOBOBJECT_EXTENDED_LIMIT_INFORMATION();
    info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
    if (!SetInformationJobObject(
        job, JobObjectExtendedLimitInformation, ref info,
        (uint)Marshal.SizeOf(typeof(JOBOBJECT_EXTENDED_LIMIT_INFORMATION)))) {
      int error = Marshal.GetLastWin32Error();
      CloseHandle(job);
      throw new Win32Exception(error);
    }
    return job;
  }

  public static void Assign(IntPtr job, IntPtr process) {
    if (!AssignProcessToJobObject(job, process))
      throw new Win32Exception(Marshal.GetLastWin32Error());
  }

  public static void Close(IntPtr job) {
    if (job != IntPtr.Zero && !CloseHandle(job))
      throw new Win32Exception(Marshal.GetLastWin32Error());
  }
}

public static class RMQOwnedPosixProcessGroup {
  private const int ESRCH = 3;
  private const int EPERM = 1;

  [DllImport("libc", SetLastError = true)]
  private static extern int kill(int pid, int signal);

  public static bool Exists(int groupId) {
    int result = kill(-groupId, 0);
    if (result == 0) return true;
    int error = Marshal.GetLastWin32Error();
    if (error == ESRCH) return false;
    if (error == EPERM) return true;
    throw new Win32Exception(error);
  }

  public static void Signal(int groupId, int signal) {
    if (kill(-groupId, signal) == 0) return;
    int error = Marshal.GetLastWin32Error();
    if (error != ESRCH) throw new Win32Exception(error);
  }
}
'@
}

function Test-RMQOwnedProcessWindows {
  return [Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT
}

function Get-RMQPosixProcessGroupTarget([int]$RootProcessId) {
  if ($RootProcessId -le 0) {
    throw 'POSIX process-group root ID must be positive'
  }
  return -1 * $RootProcessId
}

function Get-RMQOwnedLaunchPlan(
    [string]$FilePath,
    [string[]]$Arguments,
    [ValidateSet('Auto', 'Windows', 'Posix')]
    [string]$Platform = 'Auto',
    [string]$SetsidPathOverride = '') {
  $resolvedPlatform = $Platform
  if ($resolvedPlatform -ceq 'Auto') {
    $resolvedPlatform = if (Test-RMQOwnedProcessWindows) {
      'Windows'
    } else {
      'Posix'
    }
  }
  if ($resolvedPlatform -ceq 'Windows') {
    return [pscustomobject]@{
      Platform = 'Windows'
      Launcher = $FilePath
      Arguments = @($Arguments)
      Ownership = 'kill-on-close-job'
      GroupIdFromRoot = $false
    }
  }
  $setsidPath = $SetsidPathOverride
  if ([string]::IsNullOrWhiteSpace($setsidPath)) {
    $setsid = Get-Command setsid -CommandType Application -ErrorAction Stop
    $setsidPath = $setsid.Source
  }
  return [pscustomobject]@{
    Platform = 'Posix'
    Launcher = $setsidPath
    Arguments = @('--', $FilePath) + @($Arguments)
    Ownership = 'setsid-process-group'
    GroupIdFromRoot = $true
  }
}

function Read-RMQBoundedProcessOutput(
    [string]$StdoutPath,
    [string]$StderrPath) {
  $lines = [Collections.Generic.List[string]]::new()
  foreach ($path in @($StdoutPath, $StderrPath)) {
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
      continue
    }
    $text = $null
    for ($attempt = 0; $attempt -lt 100; $attempt += 1) {
      try {
        $text = [IO.File]::ReadAllText($path)
        break
      } catch [IO.IOException] {
        Start-Sleep -Milliseconds 100
      }
    }
    if ($null -eq $text) {
      throw "redirected output remained locked after owned process exit: $path"
    }
    foreach ($line in [regex]::Split($text, '\r?\n')) {
      if ($line -ne '') {
        $lines.Add($line)
      }
    }
  }
  return @($lines)
}

function Stop-RMQPosixOwnedProcessGroup(
    [int]$GroupId,
    [int]$GraceMilliseconds = 2000) {
  if ($GroupId -le 0) { return }
  if (-not [RMQOwnedPosixProcessGroup]::Exists($GroupId)) { return }
  [RMQOwnedPosixProcessGroup]::Signal($GroupId, 15)
  $watch = [Diagnostics.Stopwatch]::StartNew()
  while ($watch.ElapsedMilliseconds -lt $GraceMilliseconds -and
      [RMQOwnedPosixProcessGroup]::Exists($GroupId)) {
    Start-Sleep -Milliseconds 50
  }
  if ([RMQOwnedPosixProcessGroup]::Exists($GroupId)) {
    [RMQOwnedPosixProcessGroup]::Signal($GroupId, 9)
  }
  $watch.Restart()
  while ($watch.ElapsedMilliseconds -lt 5000 -and
      [RMQOwnedPosixProcessGroup]::Exists($GroupId)) {
    Start-Sleep -Milliseconds 50
  }
  if ([RMQOwnedPosixProcessGroup]::Exists($GroupId)) {
    throw "owned POSIX process group $GroupId survived cleanup"
  }
}

function Invoke-RMQOwnedBoundedProcess(
    [string]$FilePath,
    [string[]]$Arguments,
    [string]$WorkingDirectory,
    [string]$Stage,
    [int]$DeadlineSeconds,
    [int]$OutputLimitBytes,
    [string]$TempRoot,
    [hashtable]$Environment = @{},
    [switch]$ReleaseGatedScript) {
  if ($DeadlineSeconds -le 0) {
    throw "$Stage deadline must be positive"
  }
  if ($OutputLimitBytes -le 0) {
    throw "$Stage output limit must be positive"
  }
  $fullTempRoot = [IO.Path]::GetFullPath($TempRoot)
  if (-not (Test-Path -LiteralPath $fullTempRoot -PathType Container)) {
    [void](New-Item -ItemType Directory -Path $fullTempRoot -Force)
  }
  $encoding = [Text.UTF8Encoding]::new($false)
  $safeStage = [regex]::Replace($Stage, '[^A-Za-z0-9_-]', '-')
  $logStem = Join-Path $fullTempRoot (
    $safeStage + '-' + [Guid]::NewGuid().ToString('N'))
  $stdoutPath = $logStem + '.stdout.log'
  $stderrPath = $logStem + '.stderr.log'
  $specPath = $logStem + '.launch.json'
  $releasePath = $logStem + '.release'
  $bootstrapPath = $logStem + '.bootstrap.ps1'
  $process = $null
  $jobHandle = [IntPtr]::Zero
  $posixGroupId = 0
  $timedOut = $false
  $outputLimitExceeded = $false
  $terminatedIds = @()
  $output = @()
  $exitCode = -1
  $ownership = ''
  $stopwatch = [Diagnostics.Stopwatch]::StartNew()
  try {
    if (-not $ReleaseGatedScript) {
      $launchSpec = [ordered]@{
        FilePath = $FilePath
        Arguments = @($Arguments)
        Environment = $Environment
      }
      [IO.File]::WriteAllText(
        $specPath, ($launchSpec | ConvertTo-Json -Depth 5), $encoding)
      [IO.File]::WriteAllText($bootstrapPath, @'
param([string]$SpecPath, [string]$ReleasePath)
$ErrorActionPreference = 'Stop'
while (-not (Test-Path -LiteralPath $ReleasePath -PathType Leaf)) {
  Start-Sleep -Milliseconds 10
}
$spec = Get-Content -LiteralPath $SpecPath -Raw | ConvertFrom-Json
foreach ($property in $spec.Environment.PSObject.Properties) {
  [Environment]::SetEnvironmentVariable(
    $property.Name, [string]$property.Value, 'Process')
}
& ([string]$spec.FilePath) @([string[]]$spec.Arguments)
if ($null -eq $LASTEXITCODE) { exit 0 }
exit ([int]$LASTEXITCODE)
'@, $encoding)
    } elseif ($Environment.Count -ne 0) {
      throw "$Stage release-gated scripts cannot receive an environment override"
    }

    $startFilePath = if ($ReleaseGatedScript) {
      $FilePath
    } else {
      (Get-Process -Id $PID).Path
    }
    $startArguments = if ($ReleaseGatedScript) {
      @($Arguments) + @('-LaunchReleasePath', $releasePath)
    } else {
      @('-NoLogo', '-NoProfile', '-ExecutionPolicy', 'Bypass',
        '-File', $bootstrapPath, '-SpecPath', $specPath,
        '-ReleasePath', $releasePath)
    }
    $plan = Get-RMQOwnedLaunchPlan $startFilePath $startArguments
    $ownership = $plan.Ownership
    if ($plan.Platform -ceq 'Windows') {
      $jobHandle = [RMQOwnedWindowsJob]::CreateKillOnClose()
    }
    $process = Start-Process -FilePath $plan.Launcher `
      -ArgumentList @($plan.Arguments) -WorkingDirectory $WorkingDirectory `
      -PassThru -NoNewWindow -RedirectStandardOutput $stdoutPath `
      -RedirectStandardError $stderrPath
    if ($plan.Platform -ceq 'Windows') {
      [RMQOwnedWindowsJob]::Assign($jobHandle, $process.Handle)
    } else {
      $posixGroupId = $process.Id
    }
    # The bootstrap cannot launch the requested tool until its root has been
    # assigned to the Windows job or established as the POSIX session leader.
    [IO.File]::WriteAllText($releasePath, 'owned', $encoding)

    while (-not $process.WaitForExit(100)) {
      $bytes = 0L
      foreach ($path in @($stdoutPath, $stderrPath)) {
        if (Test-Path -LiteralPath $path -PathType Leaf) {
          $bytes += (Get-Item -LiteralPath $path).Length
        }
      }
      if ($bytes -gt $OutputLimitBytes) {
        $outputLimitExceeded = $true
        break
      }
      if ($stopwatch.Elapsed.TotalSeconds -ge $DeadlineSeconds) {
        $timedOut = $true
        break
      }
    }

    if ($timedOut -or $outputLimitExceeded) {
      $terminatedIds = @($process.Id)
      if ($jobHandle -ne [IntPtr]::Zero) {
        [RMQOwnedWindowsJob]::Close($jobHandle)
        $jobHandle = [IntPtr]::Zero
      } elseif ($posixGroupId -gt 0) {
        Stop-RMQPosixOwnedProcessGroup $posixGroupId
        $posixGroupId = 0
      }
      [void]$process.WaitForExit(10000)
    } else {
      $process.WaitForExit()
      $exitCode = [int]$process.ExitCode
      if ($jobHandle -ne [IntPtr]::Zero) {
        # Closing a completed root's job also removes any residual descendant.
        [RMQOwnedWindowsJob]::Close($jobHandle)
        $jobHandle = [IntPtr]::Zero
      } elseif ($posixGroupId -gt 0) {
        # A root may exit after spawning an inherited-output child.  The owned
        # group remains the cleanup unit even when the root is already gone.
        Stop-RMQPosixOwnedProcessGroup $posixGroupId
        $posixGroupId = 0
      }
    }

    $finalBytes = 0L
    foreach ($path in @($stdoutPath, $stderrPath)) {
      if (Test-Path -LiteralPath $path -PathType Leaf) {
        $finalBytes += (Get-Item -LiteralPath $path).Length
      }
    }
    if ($finalBytes -gt $OutputLimitBytes) {
      $outputLimitExceeded = $true
    }
    $output = if ($outputLimitExceeded) {
      @("redirected output exceeded $OutputLimitBytes bytes")
    } else {
      @(Read-RMQBoundedProcessOutput $stdoutPath $stderrPath)
    }
  } finally {
    $stopwatch.Stop()
    if ($jobHandle -ne [IntPtr]::Zero) {
      [RMQOwnedWindowsJob]::Close($jobHandle)
      $jobHandle = [IntPtr]::Zero
    }
    if ($posixGroupId -gt 0) {
      Stop-RMQPosixOwnedProcessGroup $posixGroupId
      $posixGroupId = 0
    }
    if ($null -ne $process -and -not $process.HasExited) {
      # This is a root-only fallback after the ownership cleanup, never the
      # descendant-cleanup mechanism.
      Stop-Process -Id $process.Id -Force -ErrorAction SilentlyContinue
      [void]$process.WaitForExit(10000)
    }
    if ($null -ne $process -and
        $null -ne (Get-Process -Id $process.Id -ErrorAction SilentlyContinue)) {
      throw "$Stage owned root process $($process.Id) survived cleanup"
    }
    Remove-Item -LiteralPath $stdoutPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $stderrPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $specPath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $releasePath -Force -ErrorAction SilentlyContinue
    Remove-Item -LiteralPath $bootstrapPath -Force -ErrorAction SilentlyContinue
  }
  return [pscustomobject]@{
    Stage = $Stage
    ExitCode = $exitCode
    Output = @($output)
    TimedOut = $timedOut
    OutputLimitExceeded = $outputLimitExceeded
    TerminatedIds = @($terminatedIds)
    DurationSeconds = [Math]::Round($stopwatch.Elapsed.TotalSeconds, 3)
    DeadlineSeconds = $DeadlineSeconds
    Ownership = $ownership
  }
}

function Invoke-RMQOwnedProcessDeterministicTests {
  $posix = Get-RMQOwnedLaunchPlan '/tmp/tool' @('one', 'two') `
    -Platform Posix -SetsidPathOverride '/usr/bin/setsid'
  if ($posix.Launcher -cne '/usr/bin/setsid' -or
      $posix.Ownership -cne 'setsid-process-group' -or
      -not $posix.GroupIdFromRoot -or
      $posix.Arguments.Count -ne 4 -or
      $posix.Arguments[0] -cne '--' -or
      $posix.Arguments[1] -cne '/tmp/tool' -or
      (Get-RMQPosixProcessGroupTarget 41) -ne -41) {
    throw 'deterministic POSIX process-group production plan failed'
  }
  $windows = Get-RMQOwnedLaunchPlan 'tool.exe' @('one') -Platform Windows
  if ($windows.Launcher -cne 'tool.exe' -or
      $windows.Ownership -cne 'kill-on-close-job' -or
      $windows.GroupIdFromRoot) {
    throw 'deterministic Windows job production plan failed'
  }
  Write-Host (
    'OWNED-PROCESS deterministic production-plan PASS ' +
    '(Windows kill-on-close job; POSIX setsid/negative-pgid termination)')
}

function Assert-RMQCleanRepositoryStateText(
    [string]$State,
    [string]$Label = 'repository baseline') {
  $lines = @([regex]::Split($State, '\r?\n') |
    Where-Object { $_ -ne '' })
  $worktreeMarker = [Array]::IndexOf($lines, '---WORKTREE---')
  $indexMarker = [Array]::IndexOf($lines, '---INDEX---')
  if ($worktreeMarker -lt 0 -or $indexMarker -lt 0 -or
      $worktreeMarker -ge $indexMarker) {
    throw "$Label state markers are missing or out of order"
  }
  $dirty = @($lines | Where-Object {
    $_ -cne '---WORKTREE---' -and $_ -cne '---INDEX---' })
  if ($dirty.Count -ne 0) {
    throw "$Label is not clean: $($dirty -join ' | ')"
  }
}

function Invoke-RMQCheckedGit(
    [string]$GitPath,
    [string]$RepositoryRoot,
    [string[]]$Arguments,
    [string]$Stage,
    [int]$DeadlineSeconds,
    [int]$OutputLimitBytes,
    [string]$TempRoot) {
  $result = Invoke-RMQOwnedBoundedProcess `
    -FilePath $GitPath `
    -Arguments (@(
      '-c', 'core.excludesfile=', '-c', 'core.autocrlf=false') +
      @($Arguments)) `
    -WorkingDirectory $RepositoryRoot `
    -Stage $Stage `
    -DeadlineSeconds $DeadlineSeconds `
    -OutputLimitBytes $OutputLimitBytes `
    -TempRoot $TempRoot
  if ($result.TimedOut) {
    throw "$Stage timed out after $DeadlineSeconds seconds"
  }
  if ($result.OutputLimitExceeded) {
    throw "$Stage exceeded $OutputLimitBytes bytes"
  }
  if ($result.ExitCode -ne 0) {
    throw "$Stage exited $($result.ExitCode): $($result.Output -join ' | ')"
  }
  return @($result.Output)
}

function Get-RMQRepositoryStateBounded(
    [string]$RepositoryRoot,
    [string]$GitPath,
    [int]$DeadlineSeconds,
    [int]$OutputLimitBytes,
    [string]$TempRoot,
    [string]$StagePrefix = 'git-state') {
  $status = @(Invoke-RMQCheckedGit $GitPath $RepositoryRoot `
    @('status', '--short', '--untracked-files=all') "$StagePrefix-status" `
    $DeadlineSeconds $OutputLimitBytes $TempRoot)
  $worktree = @(Invoke-RMQCheckedGit $GitPath $RepositoryRoot `
    @('diff', '--raw', '--no-ext-diff', '--') "$StagePrefix-worktree" `
    $DeadlineSeconds $OutputLimitBytes $TempRoot)
  $index = @(Invoke-RMQCheckedGit $GitPath $RepositoryRoot `
    @('diff', '--cached', '--raw', '--no-ext-diff', '--') `
    "$StagePrefix-index" $DeadlineSeconds $OutputLimitBytes $TempRoot)
  return (@($status) + @('---WORKTREE---') + @($worktree) +
    @('---INDEX---') + @($index)) -join [Environment]::NewLine
}

function Assert-RMQExpectedDirtyState(
    [string]$State,
    [string]$Label) {
  $message = $null
  try {
    Assert-RMQCleanRepositoryStateText $State $Label
  } catch {
    $message = $_.Exception.Message
  }
  if ($null -eq $message) {
    throw "$Label dirty fixture unexpectedly passed"
  }
  Write-Host "CLEAN-BASELINE fixture PASS [$Label] $message"
}

function Invoke-RMQCleanBaselineFixtureTests(
    [string]$GitPath,
    [int]$DeadlineSeconds,
    [int]$OutputLimitBytes,
    [string]$TempRoot) {
  $fullTempRoot = [IO.Path]::GetFullPath($TempRoot)
  $fixtureRoot = [IO.Path]::GetFullPath((Join-Path $fullTempRoot (
    'clean-baseline-' + [Guid]::NewGuid().ToString('N'))))
  $allowedPrefix = $fullTempRoot.TrimEnd(
    [IO.Path]::DirectorySeparatorChar,
    [IO.Path]::AltDirectorySeparatorChar) +
      [IO.Path]::DirectorySeparatorChar
  if (-not $fixtureRoot.StartsWith(
      $allowedPrefix, [StringComparison]::OrdinalIgnoreCase)) {
    throw "clean-baseline fixture escaped temp root: $fixtureRoot"
  }
  [void](New-Item -ItemType Directory -Path $fixtureRoot)
  $trackedPath = Join-Path $fixtureRoot 'tracked.txt'
  $untrackedPath = Join-Path $fixtureRoot 'untracked.txt'
  $utf8 = [Text.UTF8Encoding]::new($false)
  try {
    [void](Invoke-RMQCheckedGit $GitPath $fixtureRoot @('init', '--quiet') `
      'fixture-git-init' $DeadlineSeconds $OutputLimitBytes $fullTempRoot)
    [void](Invoke-RMQCheckedGit $GitPath $fixtureRoot `
      @('config', 'user.email', 'rmq-fixture@example.invalid') `
      'fixture-git-email' $DeadlineSeconds $OutputLimitBytes $fullTempRoot)
    [void](Invoke-RMQCheckedGit $GitPath $fixtureRoot `
      @('config', 'user.name', 'RMQ Fixture') `
      'fixture-git-name' $DeadlineSeconds $OutputLimitBytes $fullTempRoot)
    [IO.File]::WriteAllText($trackedPath, 'base', $utf8)
    [void](Invoke-RMQCheckedGit $GitPath $fixtureRoot @('add', 'tracked.txt') `
      'fixture-git-add-initial' $DeadlineSeconds $OutputLimitBytes $fullTempRoot)
    [void](Invoke-RMQCheckedGit $GitPath $fixtureRoot `
      @('commit', '--quiet', '-m', 'baseline') 'fixture-git-commit' `
      $DeadlineSeconds $OutputLimitBytes $fullTempRoot)

    $clean = Get-RMQRepositoryStateBounded $fixtureRoot $GitPath `
      $DeadlineSeconds $OutputLimitBytes $fullTempRoot 'fixture-clean'
    Assert-RMQCleanRepositoryStateText $clean 'clean fixture'
    Write-Host 'CLEAN-BASELINE fixture PASS [clean]'

    [IO.File]::WriteAllText($trackedPath, 'dirty tracked', $utf8)
    $dirtyTracked = Get-RMQRepositoryStateBounded $fixtureRoot $GitPath `
      $DeadlineSeconds $OutputLimitBytes $fullTempRoot 'fixture-dirty-tracked'
    Assert-RMQExpectedDirtyState $dirtyTracked 'dirty tracked'
    [IO.File]::WriteAllText($trackedPath, 'base', $utf8)

    [IO.File]::WriteAllText($untrackedPath, 'dirty untracked', $utf8)
    $dirtyUntracked = Get-RMQRepositoryStateBounded $fixtureRoot $GitPath `
      $DeadlineSeconds $OutputLimitBytes $fullTempRoot 'fixture-dirty-untracked'
    Assert-RMQExpectedDirtyState $dirtyUntracked 'dirty untracked'
    Remove-Item -LiteralPath $untrackedPath -Force

    [IO.File]::WriteAllText($trackedPath, 'dirty staged', $utf8)
    [void](Invoke-RMQCheckedGit $GitPath $fixtureRoot @('add', 'tracked.txt') `
      'fixture-git-add-staged' $DeadlineSeconds $OutputLimitBytes $fullTempRoot)
    $dirtyIndex = Get-RMQRepositoryStateBounded $fixtureRoot $GitPath `
      $DeadlineSeconds $OutputLimitBytes $fullTempRoot 'fixture-dirty-index'
    Assert-RMQExpectedDirtyState $dirtyIndex 'dirty staged/index'
  } finally {
    if (Test-Path -LiteralPath $fixtureRoot) {
      $resolved = [IO.Path]::GetFullPath($fixtureRoot)
      if (-not $resolved.StartsWith(
          $allowedPrefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "refusing to remove fixture outside temp root: $resolved"
      }
      Remove-Item -LiteralPath $resolved -Recurse -Force
    }
  }
}
