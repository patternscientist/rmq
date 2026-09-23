#!/usr/bin/env pwsh

# Which PowerShell executable is THIS process running?
#
# Answered here once, because getting it wrong is silent under one host and
# fatal under another. Until 2026-09-08 both EG-CP replay harnesses chose the
# shell to spawn with
#
#     if ($onWindows) { Join-Path $PSHOME 'powershell.exe' }
#     else            { Join-Path $PSHOME 'pwsh' }
#
# Test-OnWindows keys on $IsWindows -- the OPERATING SYSTEM. That is the right
# question for taskkill-versus-setsid and the wrong question here, because
# $PSHOME is the RUNNING HOST's own directory. Under pwsh on Windows it is the
# pwsh install directory, which holds pwsh.exe and NO powershell.exe, so the
# expression produced a path that cannot exist, Start-Process threw, and the
# mandatory descendant self-test failed the whole gate -- on the pwsh route
# artifact/README.md:16 advertises.
#
# Reproduced 2026-09-08 under PowerShell 7.6.5 on Windows: the replay exits 1 at
# `REPLAY: descendant-termination self-test`. It was invisible for the life of
# the project because every recorded local GATE PASS ran under Windows
# PowerShell 5.1, whose $PSHOME does contain powershell.exe, and CI's gate leg is
# ubuntu, where the else-branch is taken. Nobody had ever run the advertised
# Windows-Core route.
#
# scripts/owned_process_tree.ps1 already answers this correctly with
# (Get-Process -Id $PID).Path; this file is that answer, named and shared.

function Get-HostShellPath {
  # 1. The running process's own image. A measurement of what is executing,
  #    correct by construction under Windows PowerShell, under pwsh on Windows
  #    and under pwsh on POSIX -- rather than an inference from the OS.
  $selfPath = $null
  try { $selfPath = (Get-Process -Id $PID).Path } catch { }
  if ([string]::IsNullOrWhiteSpace($selfPath)) {
    # .Path is a PowerShell-added view over MainModule.FileName and yields $null
    # when MainModule cannot be read; ask .NET directly before giving up.
    try { $selfPath = [System.Diagnostics.Process]::GetCurrentProcess().MainModule.FileName } catch { }
  }

  # The leaf guard rejects an engine hosted inside a non-shell process, whose
  # image would not accept -NoProfile -Command.
  $shellNames = @('pwsh.exe', 'powershell.exe', 'pwsh', 'powershell')
  if (-not [string]::IsNullOrWhiteSpace($selfPath)) {
    $leaf = [System.IO.Path]::GetFileName($selfPath)
    if (($shellNames -contains $leaf) -and (Test-Path -LiteralPath $selfPath -PathType Leaf)) {
      return $selfPath
    }
  }

  # 2. Fall back to $PSHOME plus the name THIS EDITION uses. Edition, not OS: a
  #    Core host is pwsh wherever it runs. On POSIX pwsh.exe never exists, so
  #    this lands on $PSHOME/pwsh -- the value the pre-fix else-branch produced,
  #    which is why the ubuntu leg cannot regress.
  $edition = 'Desktop'
  if ($PSVersionTable.ContainsKey('PSEdition')) { $edition = [string] $PSVersionTable.PSEdition }
  $names = if ($edition -eq 'Core') { @('pwsh.exe', 'pwsh') } else { @('powershell.exe', 'powershell') }
  foreach ($n in $names) {
    $candidate = Join-Path $PSHOME $n
    if (Test-Path -LiteralPath $candidate -PathType Leaf) { return $candidate }
  }

  # 3. No third guess. A wrong shell that happens to start is worse than a named
  #    failure: the self-test would certify termination of something other than
  #    the host it claims to have spawned.
  return $null
}
