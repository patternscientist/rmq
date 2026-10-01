# Focused support for the native lifecycle runner. No restoration writes occur here.
function Get-LNRawPin([string]$Path) {
  $p=[IO.Path]::GetFullPath($Path)
  if (-not [IO.File]::Exists($p)) { throw "INTEGRITY: missing file $p" }
  [ordered]@{path=$p;bytes=([IO.FileInfo]$p).Length;sha256=(Get-FileHash -LiteralPath $p -Algorithm SHA256).Hash}
}

function Get-LNTreeSnapshot([string]$Root,[string]$TempRoot) {
  $git=(Get-Command git -CommandType Application | Select-Object -First 1).Source
  $parts=@{}
  foreach($query in @(
    @{name='head';args=@('rev-parse','HEAD')},
    @{name='index';args=@('ls-files','--stage','-z')},
    @{name='paths';args=@('ls-files','--cached','--others','--exclude-standard','-z')})) {
    $queryRoot=Join-Path $TempRoot ([Guid]::NewGuid().ToString('N'))
    $r=Invoke-RMQOwnedBoundedProcess -FilePath $git -Arguments (@('-c','core.excludesfile=')+$query.args) `
      -WorkingDirectory $Root -Stage ('integrity-'+$query.name) -DeadlineSeconds 30 `
      -OutputLimitBytes 8388608 -TempRoot $queryRoot
    if($r.TimedOut -or $r.OutputLimitExceeded -or $r.ExitCode -ne 0 -or @($r.StandardError).Count) {
      throw ('INTEGRITY: Git snapshot failed: '+$query.name)
    }
    # Shared helper returns text lines. NUL-delimited Windows paths must have no
    # CR/LF; reject multi-line output instead of silently normalizing such names.
    if(@($r.StandardOutput).Count -gt 1){throw 'INTEGRITY: UNCOVERED multiline Git path output'}
    $parts[$query.name]=@($r.StandardOutput) -join ''
  }
  $files=@(foreach($relative in @($parts.paths.Split([char]0) | Where-Object {$_} | Sort-Object -Unique)) {
    $p=Join-Path $Root $relative
    if([IO.File]::Exists($p)) {
      $pin=Get-LNRawPin $p
      [ordered]@{path=$relative;bytes=$pin.bytes;sha256=$pin.sha256}
    } elseif([IO.Directory]::Exists($p)) {throw "INTEGRITY: unsupported directory/submodule $relative"}
    else {[ordered]@{path=$relative;missing=$true}}
  })
  [ordered]@{head=$parts.head;index=$parts.index;files=$files;
    boundary='All tracked working bytes, semantic index entries and nonignored untracked paths/bytes; user-global excludes disabled. Ignored outputs excluded from tree snapshot; explicitly captured artifacts verified separately.'}
}

function Complete-LNIntegrity([object]$State) {
  # Check every pin even after one fails, then independently check the tree.
  $errors=[Collections.Generic.List[string]]::new()
  foreach($message in $State.captureErrors){$errors.Add($message)}
  $checked=0
  foreach($pin in $State.pins.ToArray()) {
    try {
      $now=Get-LNRawPin $pin.path
      if($now.bytes -ne $pin.bytes -or $now.sha256 -cne $pin.sha256) {
        throw ('INTEGRITY: changed captured pin: '+$pin.path)
      }
    } catch {$errors.Add($_.Exception.Message)}
    $checked++
  }
  $treeChecked=$false
  if($null -eq $State.baseline) {$errors.Add('INTEGRITY: UNCOVERED; initial tree inventory unavailable')}
  else {
    try {
      $current=Get-LNTreeSnapshot $State.root $State.temp
      $treeChecked=$true
      if(($current | ConvertTo-Json -Depth 8 -Compress) -cne ($State.baseline | ConvertTo-Json -Depth 8 -Compress)) {
        $errors.Add('INTEGRITY: live tracked/index/untracked baseline changed')
      }
    } catch {$errors.Add($_.Exception.Message)}
  }
  if($checked -eq 0) {$errors.Add('INTEGRITY: UNCOVERED; no captured pins')}
  [ordered]@{attempted=$true;success=($errors.Count -eq 0);checkedPins=$checked;treeChecked=$treeChecked;
    errors=@($errors.ToArray());restorationWrites=0}
}

function Get-LNPeImports([string]$Path) {
  # Bounds-checked normal-import inventory of the pinned local PE files.
  # This is not a Windows loader or a compiler-correctness argument.
  $b=[IO.File]::ReadAllBytes($Path)
  function U16([long]$at) {if($at -lt 0 -or $at+2 -gt $b.Length){throw 'DEPENDENCY: truncated PE'};[BitConverter]::ToUInt16($b,[int]$at)}
  function U32([long]$at) {if($at -lt 0 -or $at+4 -gt $b.Length){throw 'DEPENDENCY: truncated PE'};[BitConverter]::ToUInt32($b,[int]$at)}
  if((U16 0) -ne 0x5a4d){throw 'DEPENDENCY: missing MZ signature'}
  $pe=U32 60
  if((U32 $pe) -ne 0x4550){throw 'DEPENDENCY: missing PE signature'}
  $n=U16 ($pe+6);$opt=$pe+24;$os=U16 ($pe+20);$magic=U16 $opt
  $dir=switch($magic){523 {$opt+112} 267 {$opt+96} default {throw 'DEPENDENCY: unsupported PE format'}}
  if($dir+112 -gt $opt+$os){throw 'DEPENDENCY: insufficient PE directories'}
  $sections=@(for($i=0;$i -lt $n;$i++) {
    $s=$opt+$os+40*$i
    @{va=(U32 ($s+12));size=(U32 ($s+16));raw=(U32 ($s+20))}
  })
  function Offset([long]$rva) {
    foreach($s in $sections){if($rva -ge $s.va -and $rva -lt ([long]$s.va+$s.size)) {
      $at=[long]$s.raw+$rva-$s.va
      if($at -ge $b.Length){throw 'DEPENDENCY: RVA beyond file'}
      return $at
    }}
    throw 'DEPENDENCY: unmapped RVA'
  }
  $names=[Collections.Generic.List[string]]::new()
  $rva=U32 ($dir+8);$size=U32 ($dir+12)
  if($rva -ne 0) {
    $at=Offset $rva;$end=$at+$size;$terminated=$false
    while($at+20 -le $end) {
      $nr=U32 ($at+12)
      if($nr -eq 0){$terminated=$true;break}
      $start=Offset $nr;$stop=$start
      while($stop -lt $b.Length -and $b[$stop] -ne 0){$stop++}
      if($stop -eq $b.Length){throw 'DEPENDENCY: unterminated import name'}
      $name=[Text.Encoding]::ASCII.GetString($b,[int]$start,[int]($stop-$start))
      if($name -notmatch '^[A-Za-z0-9_.+-]+\.dll$'){throw 'DEPENDENCY: unsupported import name'}
      $names.Add($name);$at+=20
    }
    if(-not $terminated){throw 'DEPENDENCY: unterminated import directory'}
  }
  [ordered]@{path=[IO.Path]::GetFullPath($Path);imports=@($names.ToArray());
    delayRva=(U32 ($dir+104));delaySize=(U32 ($dir+108))}
}

function Get-LNDependencyClosure([string[]]$Roots,[string]$BinRoot) {
  $queue=[Collections.Generic.Queue[string]]::new()
  foreach($p in $Roots){$queue.Enqueue([IO.Path]::GetFullPath($p))}
  $seen=@{};$nodes=[Collections.Generic.List[object]]::new();$external=[Collections.Generic.List[object]]::new()
  while($queue.Count) {
    $p=$queue.Dequeue()
    if($seen.ContainsKey($p)){continue};$seen[$p]=$true
    # Capture immediately, before reading. Partial inventories retain every pin.
    $pin=Get-LNPin $p
    $node=Get-LNPeImports $p
    if($node.delayRva -ne 0 -or $node.delaySize -ne 0){throw "DEPENDENCY: UNCOVERED delay imports: $p"}
    $nodes.Add($node)
    foreach($name in $node.imports) {
      $local=Join-Path (Split-Path $p -Parent) $name
      if(-not [IO.File]::Exists($local)){$local=Join-Path $BinRoot $name}
      if([IO.File]::Exists($local)){$queue.Enqueue([IO.Path]::GetFullPath($local));continue}
      $system=Join-Path ([Environment]::GetFolderPath('System')) $name
      if($name -match '^(api-ms-win-|ext-ms-win-)' -or [IO.File]::Exists($system)) {
        $external.Add(@{from=$p;name=$name;boundary='OS system library/API-set resolution, not pinned'})
      } else {throw "DEPENDENCY: unresolved non-system import $name from $p"}
    }
  }
  [ordered]@{roots=$Roots;nodes=@($nodes.ToArray());external=@($external.ToArray());
    boundary='Normal imports resolved beside each binary then Lean bin; nonzero delay imports reject. OS/API sets, runtime LoadLibrary/plugin/configuration behavior, Windows search/forwarder semantics, PowerShell/.NET and compiler correctness are external assumptions, not universally verified.'}
}

function Assert-LNDependencyCoverage([object]$Closure,[object[]]$Pins) {
  $missing=@(foreach($node in $Closure.nodes) {
    if(-not @($Pins | Where-Object {[string]::Equals($_.path,$node.path,[StringComparison]::OrdinalIgnoreCase)}).Count){$node.path}
  })
  if($missing.Count){throw ('DEPENDENCY: incomplete local inventory: '+($missing -join '; '))}
}
