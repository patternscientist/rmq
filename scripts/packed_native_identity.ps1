# Shared production predicates for native compiler provenance and cache reuse.
# Dot-source this file; callers own subprocess deadlines through the same helper.

function Get-NativeOrdinalUnique([string[]]$Values) {
  # StringComparer.Ordinal compares UTF-16 code units, independent of culture,
  # OS collation tables and the PowerShell/.NET generation. Ordered compiler
  # include/library search sequences must not pass through this helper.
  $unique = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach ($value in $Values) { [void]$unique.Add($value) }
  [string[]]$items = @($unique)
  [Array]::Sort($items,[StringComparer]::Ordinal)
  return $items
}

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
  $startedUtc = [DateTime]::UtcNow.ToString('o')
  $r = Invoke-RMQOwnedBoundedProcess -FilePath $File -Arguments $Arguments `
    -WorkingDirectory $Root -Stage $Stage -DeadlineSeconds 60 `
    -OutputLimitBytes 1048576 -TempRoot (Join-Path $Root '.lake/native1/identity-process')
  if ($r.ExitCode -ne 0 -or $r.TimedOut -or $r.OutputLimitExceeded) {
    throw ('native tool identity command failed: ' + $Stage + ' ' + ($r | ConvertTo-Json -Depth 8 -Compress))
  }
  return [ordered]@{ file=[IO.Path]::GetFullPath($File); arguments=$Arguments; process=$r;
    startedUtc=$startedUtc; completedUtc=[DateTime]::UtcNow.ToString('o'); text=($r.Output -join "`n").Trim() }
}

function Get-NativeCppDependencyRoots([string]$Root,[string]$CppCompiler,
    [string]$ImportLibrarian,[string]$RustLinker) {
  # -### prints the actual selected cc1/link commands without executing either.
  # Compiler defaults select a newer installed MSVC toolset on this host than
  # the configured Rust linker, so deriving everything from clang.exe is wrong.
  $probe = Get-NativeCommandIdentity $Root $CppCompiler `
    @('-###','-std=c++17','native/packed-rmq/examples/native.cpp','-o',
      '.lake/native1/binary-build/identity-discovery-only.exe') 'cpp-effective-dependencies'
  $commands = @($probe.process.StandardError | ForEach-Object {
    if ($_ -match '^\s*"') {
      $tokens = @([regex]::Matches($_,'"(?:\\.|[^"\\])*"') | ForEach-Object { $_.Value | ConvertFrom-Json })
      if ($tokens.Count -gt 1) { [pscustomobject]@{tokens=$tokens} }
    }
  })
  $compiler = @($commands | Where-Object { $_.tokens -ccontains '-cc1' })
  $linker = @($commands | Where-Object { [IO.Path]::GetFileName($_.tokens[0]) -ieq 'link.exe' })
  if ($compiler.Count -ne 1 -or $linker.Count -ne 1) { throw 'missing or ambiguous effective C++ command' }
  $tokens = $compiler[0].tokens
  $resource = @()
  $includes = @()
  for ($i=0;$i -lt $tokens.Count - 1;$i++) {
    if ($tokens[$i] -ceq '-resource-dir') { $resource += @([IO.Path]::GetFullPath($tokens[$i+1])) }
    if ($tokens[$i] -cin @('-internal-isystem','-internal-externc-isystem','-isystem','-I')) {
      $includes += @([IO.Path]::GetFullPath($tokens[$i+1]))
    }
  }
  $libraries = @($linker[0].tokens | Where-Object { $_ -imatch '^-libpath:' } | ForEach-Object {
    [IO.Path]::GetFullPath($_.Substring('-libpath:'.Length))
  })
  if ($resource.Count -ne 1 -or $includes.Count -eq 0 -or $libraries.Count -eq 0) {
    throw 'empty or ambiguous effective C++ dependency roots'
  }
  $msvcRoots = @(Get-NativeOrdinalUnique @($includes | Where-Object { $_ -match '[\\/]VC[\\/]Tools[\\/]MSVC[\\/][0-9.]+[\\/]include$' } |
    ForEach-Object { Split-Path $_ -Parent }))
  $sdkRoots = @(Get-NativeOrdinalUnique @($includes | Where-Object { $_ -match '[\\/]Windows Kits[\\/]10[\\/]Include[\\/][0-9.]+[\\/]ucrt$' } |
    ForEach-Object { Split-Path $_ -Parent }))
  if ($msvcRoots.Count -ne 1 -or $sdkRoots.Count -ne 1) { throw 'missing or ambiguous effective MSVC/SDK version' }
  $sdkVersion = Split-Path $sdkRoots[0] -Leaf
  $sdkBase = Split-Path (Split-Path $sdkRoots[0] -Parent) -Parent
  $configuredToolsets = @(Get-NativeOrdinalUnique @(@($ImportLibrarian,$RustLinker) | ForEach-Object {
    $path = [IO.Path]::GetFullPath($_)
    if ($path -notmatch '^(.*[\\/]VC[\\/]Tools[\\/]MSVC[\\/][0-9.]+)[\\/]bin[\\/]Hostx64[\\/]x64[\\/](?:lib|link)\.exe$') {
      throw 'configured MSVC tool does not identify one x64 toolset'
    }
    $Matches[1]
  }))
  if ($configuredToolsets.Count -ne 1) { throw 'configured librarian/Rust linker toolsets disagree' }
  $effectiveLinker = [IO.Path]::GetFullPath($linker[0].tokens[0])
  if ($effectiveLinker -ine (Join-Path $msvcRoots[0] 'bin/Hostx64/x64/link.exe')) {
    throw 'effective C++ linker/toolset mismatch'
  }
  # Reject unexpected injected include/library roots rather than silently
  # blessing any path the environment happens to add to the compiler command.
  $expectedIncludes = @((Join-Path $resource[0] 'include'),(Join-Path $msvcRoots[0] 'include'),
    (Join-Path $msvcRoots[0] 'atlmfc/include')) +
    @('ucrt','shared','um','winrt','cppwinrt' | ForEach-Object { Join-Path $sdkRoots[0] $_ })
  $expectedLibraries = @((Join-Path $msvcRoots[0] 'lib/x64'),(Join-Path $msvcRoots[0] 'atlmfc/lib/x64'),
    (Join-Path $sdkBase ('Lib/' + $sdkVersion + '/ucrt/x64')),
    (Join-Path $sdkBase ('Lib/' + $sdkVersion + '/um/x64')),(Join-Path $resource[0] 'lib/windows'))
  if (($includes -join '|') -ine ($expectedIncludes -join '|') -or
      ($libraries -join '|') -ine ($expectedLibraries -join '|')) { throw 'unsupported effective C++ include/library search path' }
  # clang advertises ATL/MFC even on an installation without that optional
  # component. Pin absence explicitly: installing it changes the identity.
  $optionalDirectories = @('atlmfc/include','atlmfc/lib/x64' | ForEach-Object {
    $optionalPath = [IO.Path]::GetFullPath((Join-Path $msvcRoots[0] $_))
    [ordered]@{path=$optionalPath;present=(Test-Path -LiteralPath $optionalPath -PathType Container)}
  })
  $inventoryRootCandidates = @($resource[0],(Join-Path $msvcRoots[0] 'include'),
    (Join-Path $msvcRoots[0] 'lib/x64'),$sdkRoots[0],
    (Join-Path $sdkBase ('Lib/' + $sdkVersion + '/ucrt/x64')),
    (Join-Path $sdkBase ('Lib/' + $sdkVersion + '/um/x64')),
    (Join-Path $configuredToolsets[0] 'include'),(Join-Path $configuredToolsets[0] 'lib/x64')) +
    @($optionalDirectories | Where-Object present | ForEach-Object path) |
      ForEach-Object { [IO.Path]::GetFullPath($_).TrimEnd('/','\') }
  $inventoryRoots = @(Get-NativeOrdinalUnique @($inventoryRootCandidates))
  foreach ($directory in $inventoryRoots) {
    if (-not (Test-Path -LiteralPath $directory -PathType Container)) { throw ('missing effective native dependency root: ' + $directory) }
  }
  if (-not (Test-Path -LiteralPath $effectiveLinker -PathType Leaf)) { throw 'missing effective C++ linker' }
  return [ordered]@{schema='native1-cpp-dependencies-v1';probe=$probe;resourceRoot=$resource[0];
    effectiveMsvcRoot=$msvcRoots[0];configuredMsvcRoot=$configuredToolsets[0];sdkIncludeRoot=$sdkRoots[0];
    sdkVersion=$sdkVersion;includeSearch=$includes;librarySearch=$libraries;linker=$effectiveLinker;
    inventoryRoots=@($inventoryRoots);optionalDirectories=$optionalDirectories}
}

function Get-NativeFileInventory([string]$Root, [string[]]$Directories) {
  $rootPath = [IO.Path]::GetFullPath($Root).TrimEnd('/', '\')
  $paths = @(Get-NativeOrdinalUnique @($Directories | ForEach-Object {
    Get-ChildItem -LiteralPath (Join-Path $rootPath $_) -File -Recurse -Force -ErrorAction Stop
  } | ForEach-Object { $_.FullName }))
  if ($paths.Count -eq 0) { throw 'empty compiler/import/runtime inventory' }
  return @($paths | ForEach-Object {
    [ordered]@{ path=$_.Substring($rootPath.Length + 1).Replace('\','/');
      bytes=(Get-Item -LiteralPath $_).Length; sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash }
  })
}

function Get-NativeToolchainIdentity([string]$Root, [string]$LeanRoot,
    [string]$RustRoot, [string]$CppCompiler, [string]$ImportLibrarian, [string]$RustLinker) {
  $LeanRoot = [IO.Path]::GetFullPath($LeanRoot)
  $RustRoot = [IO.Path]::GetFullPath($RustRoot)
  $CppCompiler = [IO.Path]::GetFullPath($CppCompiler)
  $ImportLibrarian = [IO.Path]::GetFullPath($ImportLibrarian)
  $RustLinker = [IO.Path]::GetFullPath($RustLinker)
  $pin = [IO.File]::ReadAllText((Join-Path $Root 'lean-toolchain')).Trim()
  $lean = Get-NativeCommandIdentity $Root (Join-Path $LeanRoot 'bin/lean.exe') @('--version') 'lean-identity'
  Assert-NativeLeanPin $pin $lean.text
  $c = Get-NativeCommandIdentity $Root (Join-Path $LeanRoot 'bin/clang.exe') @('--version') 'c-identity'
  $rust = Get-NativeCommandIdentity $Root (Join-Path $RustRoot 'bin/rustc.exe') @('-vV') 'rust-identity'
  if ($rust.text -cnotmatch '(?m)^host: x86_64-pc-windows-msvc$') { throw 'unsupported native Rust host' }
  $cargo = Get-NativeCommandIdentity $Root (Join-Path $RustRoot 'bin/cargo.exe') @('-vV') 'cargo-identity'
  $cpp = Get-NativeCommandIdentity $Root $CppCompiler @('--version') 'cpp-identity'
  $cppDependencies = Get-NativeCppDependencyRoots $Root $CppCompiler $ImportLibrarian $RustLinker
  # Include actual imported .olean files, compiler binaries, headers, archives,
  # dynamic runtimes and clang resources. No source-only version label can stand
  # in for these bytes, and no timestamp-only inventory permits cache reuse.
  $leanFiles = @(Get-NativeFileInventory $LeanRoot @('bin','include','lib'))
  $rustFiles = @(Get-NativeFileInventory $RustRoot @('bin','lib/rustlib/x86_64-pc-windows-msvc/lib'))
  $cppFiles = @($cppDependencies.inventoryRoots | ForEach-Object {
    $dependencyRoot = $_
    Get-NativeFileInventory $dependencyRoot @('.') | ForEach-Object {
      [ordered]@{root=$dependencyRoot;path=$_.path;bytes=$_.bytes;sha256=$_.sha256}
    }
  })
  $toolRuntimeRoots = @(Get-NativeOrdinalUnique @(@($CppCompiler,$ImportLibrarian,$RustLinker,$cppDependencies.linker) |
    ForEach-Object { [IO.Path]::GetFullPath((Split-Path $_ -Parent)) }))
  $toolRuntimePaths = @(Get-NativeOrdinalUnique @($toolRuntimeRoots | ForEach-Object {
    Get-ChildItem -LiteralPath $_ -File -Filter '*.dll' -Force -ErrorAction Stop
  } | ForEach-Object { $_.FullName }))
  $toolRuntimeFiles = @($toolRuntimePaths | ForEach-Object {
    [ordered]@{path=$_;bytes=(Get-Item -LiteralPath $_).Length;sha256=(Get-FileHash -LiteralPath $_).Hash}
  })
  $externalPaths = @(Get-NativeOrdinalUnique @($CppCompiler,$ImportLibrarian,$RustLinker,$cppDependencies.linker))
  $externalFiles = @($externalPaths | ForEach-Object {
    [ordered]@{path=[IO.Path]::GetFullPath($_); bytes=(Get-Item -LiteralPath $_).Length;
      sha256=(Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash;
      fileVersion=(Get-Item -LiteralPath $_).VersionInfo.FileVersion}
  })
  $identity = [ordered]@{schema='native1-toolchain-v3';sortPolicy='ordinal-case-sensitive-utf16'; digest=''; repositoryPin=$pin;
    leanRoot=[IO.Path]::GetFullPath($LeanRoot); rustRoot=[IO.Path]::GetFullPath($RustRoot);
    cppCompiler=$CppCompiler; importLibrarian=$ImportLibrarian; rustLinker=$RustLinker;
    commands=@($lean,$c,$rust,$cargo,$cpp); leanFiles=$leanFiles; rustFiles=$rustFiles;
    cppDependencies=$cppDependencies;cppFiles=$cppFiles;toolRuntimeRoots=$toolRuntimeRoots;
    toolRuntimeFiles=$toolRuntimeFiles;externalFiles=$externalFiles}
  $identity.digest = Get-NativeToolchainDigest $identity
  return $identity
}

function Get-NativeToolchainDigest($Identity) {
  $dependencies = $Identity.cppDependencies
  $parts = @($Identity.schema,$Identity.sortPolicy,$Identity.repositoryPin,
    $Identity.leanRoot,$Identity.rustRoot,$Identity.cppCompiler,$Identity.importLibrarian,$Identity.rustLinker)
  foreach ($command in $Identity.commands) {
    $parts += @('command/' + $command.file)
    $parts += @($command.arguments | ForEach-Object { 'argument/' + $_ })
    $parts += @('version/' + $command.text)
  }
  $parts += @($dependencies.resourceRoot,$dependencies.effectiveMsvcRoot,$dependencies.configuredMsvcRoot,
    $dependencies.sdkIncludeRoot,$dependencies.sdkVersion,$dependencies.linker)
  $parts += @($dependencies.includeSearch | ForEach-Object { 'cpp-include/' + $_ })
  $parts += @($dependencies.librarySearch | ForEach-Object { 'cpp-library/' + $_ })
  $parts += @($dependencies.optionalDirectories | ForEach-Object { 'cpp-optional/' + $_.path + ':' + $_.present })
  $parts += @($Identity.leanFiles | ForEach-Object { 'lean/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  $parts += @($Identity.rustFiles | ForEach-Object { 'rust/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  $parts += @($Identity.cppFiles | ForEach-Object { 'cpp/' + $_.root + '/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  $parts += @($Identity.toolRuntimeRoots | ForEach-Object { 'tool-runtime-root/' + $_ })
  $parts += @($Identity.toolRuntimeFiles | ForEach-Object { 'tool-runtime/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  $parts += @($Identity.externalFiles | ForEach-Object { 'external/' + $_.path + ':' + $_.bytes + ':' + $_.sha256 })
  return Get-NativeDigest $parts
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

function Assert-NativeIdentityShape($Expected) {
  $expectedNames = @(Get-NativeOrdinalUnique @('schema','sortPolicy','digest','repositoryPin','leanRoot','rustRoot','cppCompiler',
    'importLibrarian','rustLinker','commands','leanFiles','rustFiles','cppDependencies',
    'cppFiles','toolRuntimeRoots','toolRuntimeFiles','externalFiles'))
  $actualNames = if ($Expected -is [Collections.IDictionary]) { @(Get-NativeOrdinalUnique @($Expected.Keys)) }
    else { @(Get-NativeOrdinalUnique @($Expected.PSObject.Properties.Name)) }
  if ($Expected.schema -cne 'native1-toolchain-v3' -or $Expected.sortPolicy -cne 'ordinal-case-sensitive-utf16' -or
      ($actualNames -join ',') -cne ($expectedNames -join ',')) {
    throw 'native toolchain manifest shape'
  }
  $expectedCppNames = @(Get-NativeOrdinalUnique @('schema','probe','resourceRoot','effectiveMsvcRoot','configuredMsvcRoot',
    'sdkIncludeRoot','sdkVersion','includeSearch','librarySearch','linker','inventoryRoots','optionalDirectories'))
  $actualCppNames = if ($Expected.cppDependencies -is [Collections.IDictionary]) {
    @(Get-NativeOrdinalUnique @($Expected.cppDependencies.Keys))
  } else { @(Get-NativeOrdinalUnique @($Expected.cppDependencies.PSObject.Properties.Name)) }
  if (($actualCppNames -join ',') -cne ($expectedCppNames -join ',')) { throw 'native toolchain C++ dependency shape' }
  if ($Expected.commands.Count -ne 5) { throw 'native toolchain command roster shape' }
  $expectedCommandNames = @(Get-NativeOrdinalUnique @('file','arguments','process','startedUtc','completedUtc','text'))
  foreach ($command in $Expected.commands) {
    $actualCommandNames = if ($command -is [Collections.IDictionary]) { @(Get-NativeOrdinalUnique @($command.Keys)) }
      else { @(Get-NativeOrdinalUnique @($command.PSObject.Properties.Name)) }
    if (($actualCommandNames -join ',') -cne ($expectedCommandNames -join ',')) { throw 'native toolchain command shape' }
  }
}

function Assert-NativeRetainedIdentity($Expected,$Actual) {
  Assert-NativeIdentityShape $Expected
  Assert-NativeIdentityShape $Actual
  if ($Actual.digest -cne $Expected.digest) { throw 'native compiler/import/runtime identity changed' }
  # The digest remains the byte provenance pin, but the retained full inventory
  # must also faithfully describe it. Removing/changing inventory rows while
  # leaving the digest untouched is not an accepted manifest representation.
  foreach ($field in @('repositoryPin','leanRoot','rustRoot','cppCompiler','importLibrarian','rustLinker',
      'leanFiles','rustFiles','cppFiles','toolRuntimeRoots','toolRuntimeFiles','externalFiles')) {
    $left = ConvertTo-Json -InputObject $Expected.$field -Compress -Depth 8
    $right = ConvertTo-Json -InputObject $Actual.$field -Compress -Depth 8
    if ($left -cne $right) { throw ('native toolchain retained inventory mismatch: ' + $field) }
  }
  foreach ($field in @('schema','resourceRoot','effectiveMsvcRoot','configuredMsvcRoot','sdkIncludeRoot',
      'sdkVersion','includeSearch','librarySearch','linker','inventoryRoots','optionalDirectories')) {
    $left = ConvertTo-Json -InputObject $Expected.cppDependencies.$field -Compress -Depth 8
    $right = ConvertTo-Json -InputObject $Actual.cppDependencies.$field -Compress -Depth 8
    if ($left -cne $right) { throw ('native toolchain retained C++ roots mismatch: ' + $field) }
  }
  for ($i=0;$i -lt 5;$i++) {
    foreach ($field in @('file','arguments','text')) {
      $left = ConvertTo-Json -InputObject $Expected.commands[$i].$field -Compress -Depth 4
      $right = ConvertTo-Json -InputObject $Actual.commands[$i].$field -Compress -Depth 4
      if ($left -cne $right) { throw ('native toolchain retained command mismatch: ' + $i + '/' + $field) }
    }
  }
}

function Assert-NativeToolchainIdentity([string]$Root, $Expected) {
  Assert-NativeIdentityShape $Expected
  $actual = Get-NativeToolchainIdentity $Root $Expected.leanRoot $Expected.rustRoot `
    $Expected.cppCompiler $Expected.importLibrarian $Expected.rustLinker
  Assert-NativeRetainedIdentity $Expected $actual
  return $actual
}
