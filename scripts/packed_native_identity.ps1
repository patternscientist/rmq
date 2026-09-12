# Shared production predicates for native compiler provenance and cache reuse.
# Dot-source this file; callers own subprocess deadlines through the same helper.

function Get-NativeDigest([string[]]$Parts) {
  $bytes = [Text.UTF8Encoding]::new($false).GetBytes(($Parts -join "`n"))
  $sha = [Security.Cryptography.SHA256]::Create()
  try { return ([BitConverter]::ToString($sha.ComputeHash($bytes))).Replace('-', '') }
  finally { $sha.Dispose() }
}

function Assert-NativeLeanPin([string]$Pin, [string]$Version) {
  if ($Pin -cne 'leanprover/lean4:v4.22.0' -or
      $Version -cnotmatch '^Lean \(version 4\.22\.0, x86_64-w64-windows-gnu, commit ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05, Release\)$') {
    throw 'native Lean compiler does not match the repository toolchain pin'
  }
}

function Get-NativeCommandIdentity([string]$Root, [string]$File, [string[]]$Arguments,
    [string]$Stage) {
  $r = Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments `
    -WorkingDirectory $Root -Stage $Stage -DeadlineSeconds 60 `
    -OutputLimitBytes 1048576 -TempRoot (Join-Path $Root '.lake/native1/identity-process')
  if ($r.ExitCode -ne 0 -or $r.TimedOut -or $r.OutputLimitExceeded) {
    throw ('native tool identity command failed: ' + $Stage + ' ' + ($r | ConvertTo-Json -Depth 8 -Compress))
  }
  return [ordered]@{ file=$File; arguments=$Arguments; process=$r; text=($r.Output -join "`n").Trim() }
}

function Get-NativeFileInventory([string]$Root, [string[]]$Directories) {
  $rootPath = [IO.Path]::GetFullPath($Root).TrimEnd('/', '\')
  $paths = @($Directories | ForEach-Object {
    Get-ChildItem -LiteralPath (Join-Path $rootPath $_) -File -Recurse -ErrorAction Stop
  } | ForEach-Object { $_.FullName } | Sort-Object -Unique)
  if ($paths.Count -eq 0) { throw 'empty compiler/import/runtime inventory' }
  return @($paths | ForEach-Object {
    [ordered]@{ path=$_.Substring($rootPath.Length + 1).Replace('\','/');
      bytes=(Get-Item -LiteralPath $_).Length; sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash }
  })
}

function Get-NativeToolchainIdentity([string]$Root, [string]$LeanRoot,
    [string]$RustRoot, [string]$CppCompiler, [string]$ImportLibrarian, [string]$RustLinker) {
  $pin = [IO.File]::ReadAllText((Join-Path $Root 'lean-toolchain')).Trim()
  $lean = Get-NativeCommandIdentity $Root (Join-Path $LeanRoot 'bin/lean.exe') @('--version') 'lean-identity'
  Assert-NativeLeanPin $pin $lean.text
  $c = Get-NativeCommandIdentity $Root (Join-Path $LeanRoot 'bin/clang.exe') @('--version') 'c-identity'
  $rust = Get-NativeCommandIdentity $Root (Join-Path $RustRoot 'bin/rustc.exe') @('-vV') 'rust-identity'
  if ($rust.text -cnotmatch '(?m)^host: x86_64-pc-windows-msvc$') { throw 'unsupported native Rust host' }
  $cargo = Get-NativeCommandIdentity $Root (Join-Path $RustRoot 'bin/cargo.exe') @('-vV') 'cargo-identity'
  $cpp = Get-NativeCommandIdentity $Root $CppCompiler @('--version') 'cpp-identity'
  # Include actual imported .olean files, compiler binaries, headers, archives,
  # dynamic runtimes and clang resources. No source-only version label can stand
  # in for these bytes, and no timestamp-only inventory permits cache reuse.
  $leanFiles = @(Get-NativeFileInventory $LeanRoot @('bin','include','lib'))
  $rustFiles = @(Get-NativeFileInventory $RustRoot @('bin','lib/rustlib/x86_64-pc-windows-msvc/lib'))
  $externalFiles = @(@($CppCompiler,$ImportLibrarian,$RustLinker) | ForEach-Object {
    [ordered]@{path=[IO.Path]::GetFullPath($_); bytes=(Get-Item -LiteralPath $_).Length;
      sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash;
      fileVersion=(Get-Item -LiteralPath $_).VersionInfo.FileVersion}
  })
  $parts = @('native1-toolchain-v1', $pin, $lean.text, $c.text, $rust.text, $cargo.text, $cpp.text)
  $parts += @($leanFiles | ForEach-Object { 'lean/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  $parts += @($rustFiles | ForEach-Object { 'rust/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  $parts += @($externalFiles | ForEach-Object { 'external/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  return [ordered]@{schema='native1-toolchain-v1'; digest=(Get-NativeDigest $parts); repositoryPin=$pin;
    leanRoot=[IO.Path]::GetFullPath($LeanRoot); rustRoot=[IO.Path]::GetFullPath($RustRoot);
    cppCompiler=$CppCompiler; importLibrarian=$ImportLibrarian; rustLinker=$RustLinker;
    commands=@($lean,$c,$rust,$cargo,$cpp); leanFiles=$leanFiles; rustFiles=$rustFiles; externalFiles=$externalFiles}
}

function Test-NativeModuleCache($Cache, [string]$Signature, [string]$ToolchainDigest,
    [string]$OleanPath, [string]$CPath) {
  if ($null -eq $Cache -or -not (Test-Path -LiteralPath $OleanPath -PathType Leaf) -or
      -not (Test-Path -LiteralPath $CPath -PathType Leaf)) { return $false }
  return $Cache.schema -ceq 'native1-module-v2' -and
    $Cache.toolchainDigest -ceq $ToolchainDigest -and $Cache.signature -ceq $Signature -and
    $Cache.olean -ceq (Get-FileHash -LiteralPath $OleanPath -Algorithm SHA256).Hash -and
    $Cache.c -ceq (Get-FileHash -LiteralPath $CPath -Algorithm SHA256).Hash
}

function Assert-NativeToolchainIdentity([string]$Root, $Expected) {
  if ($Expected.schema -cne 'native1-toolchain-v1') { throw 'native toolchain manifest shape' }
  $actual = Get-NativeToolchainIdentity $Root $Expected.leanRoot $Expected.rustRoot `
    $Expected.cppCompiler $Expected.importLibrarian $Expected.rustLinker
  if ($actual.digest -cne $Expected.digest) { throw 'native compiler/import/runtime identity changed' }
  return $actual
}
