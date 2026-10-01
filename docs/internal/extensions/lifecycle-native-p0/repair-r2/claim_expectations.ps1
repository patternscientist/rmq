param([switch]$Produce,[string]$RepositoryRoot,[string]$EvidenceRoot)

# This expectation enumerates protected policy/input facts; it never consumes
# claim_drift_scan.ps1 stdout. Only the fixed run_owned claims profile is covered.
$script:LNClaimExpectationSource=$PSCommandPath

function Assert-LNClaimStreamExpectation([string]$Actual,[object]$Expectation) {
  if($null -eq $Expectation -or $Expectation.Profile -cne 'claims-strict-subtree-ledgers' -or
     $Expectation.ExpectedExit -ne 0 -or $Expectation.Stderr -cne ''){throw 'STREAM: invalid claim expectation'}
  $footer=[string]$Expectation.Footer
  if($footer.Length -eq 0 -or -not $Actual.EndsWith($footer,[StringComparison]::Ordinal)){
    throw 'STREAM: claim footer differs'
  }
  $remaining=[Collections.Generic.Dictionary[string,int]]::new([StringComparer]::Ordinal)
  foreach($item in @($Expectation.Records)) {
    $record=[string]$item
    if(-not $record.StartsWith('CLAIM-DRIFT[',[StringComparison]::Ordinal) -or
       -not $record.EndsWith([Environment]::NewLine,[StringComparison]::Ordinal)){
      throw 'STREAM: malformed expected claim record'
    }
    if($remaining.ContainsKey($record)){$remaining[$record]++}else{$remaining.Add($record,1)}
  }
  [string[]]$keys=@($remaining.Keys)
  [Array]::Sort($keys,[StringComparer]::Ordinal)
  # Prefix-free whole records make tokenization unique, even when source prose
  # contains newlines or marker-like text. Ambiguity fails rather than allowing
  # arbitrary splitting, trimming, blank suppression or substring matching.
  # In ordinal order a proper-prefix pair must have adjacent representatives.
  for($i=1;$i -lt $keys.Count;$i++) {
    if($keys[$i].StartsWith($keys[$i-1],[StringComparison]::Ordinal)){
      throw 'STREAM: ambiguous expected claim record boundaries'
    }
  }
  $bodyLength=$Actual.Length-$footer.Length
  $offset=0
  # Every alternative is Regex.Escape of a complete known record; \G requires
  # the next character, so no search can skip unexpected intervening text.
  $tokens=if($keys.Count){[regex]::new('\G(?:'+(($keys|ForEach-Object {[regex]::Escape($_)})-join '|')+')',
    [Text.RegularExpressions.RegexOptions]::CultureInvariant,[TimeSpan]::FromSeconds(30))}else{$null}
  while($offset -lt $bodyLength) {
    if($null -eq $tokens){throw 'STREAM: unexpected claim output with empty record roster'}
    $match=$tokens.Match($Actual,$offset)
    if(-not $match.Success -or $match.Index -ne $offset -or $match.Length -gt ($bodyLength-$offset) -or
       $remaining[$match.Value] -le 0){throw ('STREAM: unexpected or duplicate claim record/text at character '+$offset)}
    $remaining[$match.Value]--
    $offset+=$match.Length
  }
  foreach($record in $keys){if($remaining[$record] -ne 0){throw 'STREAM: missing claim record'}}
}

function Get-LNClaimStreamExpectation([string]$RepositoryRoot) {
  $root=[IO.Path]::GetFullPath($RepositoryRoot)
  $out=Join-Path $root ('.lake/repair-r2/claim-expectation-'+[Guid]::NewGuid().ToString('N'))
  [void][IO.Directory]::CreateDirectory($out)
  . (Join-Path $root 'scripts/owned_process_tree.ps1')
  . (Join-Path $root 'scripts/packed_native_lifecycle_stream_check.ps1')
  $shell=(Get-Process -Id $PID).Path
  # The historical scanner subtree pass took 11 s. One 1200 s owned deadline
  # bounds all expectation rg children, including initialization and capture.
  $capture=Invoke-LNStreamCapture $root $shell @('-NoProfile','-File',$script:LNClaimExpectationSource,
    '-Produce','-RepositoryRoot',$root,'-EvidenceRoot',$out) $root (Join-Path $out 'producer') 1200 'claim-expectation'
  Assert-LNOuterCapture $capture '' '' 0 'claim-expectation-producer'
  $path=Join-Path $out 'EXPECTATION.json'
  if(-not [IO.File]::Exists($path)){throw 'STREAM: claim expectation artifact missing'}
  $expectation=Read-LNExactStream $path|ConvertFrom-Json
  # Validate the expectation's own full-record grammar before caller use.
  Assert-LNClaimStreamExpectation ((@($expectation.Records)-join '')+$expectation.Footer) $expectation
  $expectation|Add-Member -NotePropertyName EvidencePath -NotePropertyValue $path
  $expectation|Add-Member -NotePropertyName EvidenceSha256 -NotePropertyValue (Get-FileHash -LiteralPath $path).Hash
  return $expectation
}

function New-LNClaimStreamExpectation([string]$RepositoryRoot,[string]$EvidenceRoot) {
  $ErrorActionPreference='Stop'
  $root=[IO.Path]::GetFullPath($RepositoryRoot)
  Set-Location -LiteralPath $root
  $encoding=[Text.UTF8Encoding]::new($false,$true)
  $newline=[Environment]::NewLine
  $roots=@('docs/internal/extensions/lifecycle-native-p0','docs/internal/DESIGN_DECISIONS.md','docs/internal/WORKFLOW_DESIGN_DECISIONS.md')
  foreach($path in $roots){if(-not (Test-Path -LiteralPath $path)){throw ('claim expectation root missing: '+$path)}}
  $policyPath=Join-Path $root 'docs/internal/CLAIM_DRIFT_POLICY.json'
  # Match the scanner's host-dependent Get-Content decoding for its policy and
  # attribution pass; rg's JSON preserves complete UTF-8 source match records.
  $policy=Get-Content -LiteralPath $policyPath -Raw|ConvertFrom-Json
  $currentSurface=[string]$policy.currentFactSurfacePathRegex
  $termIds=@($policy.terms|ForEach-Object {[string]$_.id})
  if(@($termIds|Sort-Object -Unique).Count -ne $termIds.Count){throw 'duplicate claim policy term IDs'}
  foreach($term in @($policy.terms)) {
    $scope=[string]$term.scope
    if(-not [string]::IsNullOrWhiteSpace($scope) -and
       ($scope -cne 'current-fact-surface' -or [string]::IsNullOrWhiteSpace($currentSurface))){throw 'unsupported claim policy scope'}
  }
  foreach($attribution in @($policy.requiredAttributions)) {
    foreach($field in @('id','pathRegex','claimPattern','requiredPattern','status')) {
      if([string]::IsNullOrWhiteSpace([string]$attribution.$field)){throw ('claim attribution missing '+$field)}
    }
    foreach($field in @('pathRegex','claimPattern','requiredPattern')){$null=[regex]::new([string]$attribution.$field)}
  }
  function Get-ClaimText($Value) {
    if($null -ne $Value.text){return [string]$Value.text}
    if($null -ne $Value.bytes){return [Text.Encoding]::UTF8.GetString([Convert]::FromBase64String([string]$Value.bytes))}
    return ''
  }
  function Get-ClaimPolicyPath([string]$Path) {
    $comparison=if($env:OS -eq 'Windows_NT'){[StringComparison]::OrdinalIgnoreCase}else{[StringComparison]::Ordinal}
    try {
      $full=if([IO.Path]::IsPathRooted($Path)){[IO.Path]::GetFullPath($Path)}else{[IO.Path]::GetFullPath([IO.Path]::Combine($root,$Path))}
      $prefix=$root.TrimEnd([IO.Path]::DirectorySeparatorChar,[IO.Path]::AltDirectorySeparatorChar)+[IO.Path]::DirectorySeparatorChar
      if($full.StartsWith($prefix,$comparison)){return ($full.Substring($prefix.Length)-replace '\\','/')}
    } catch {}
    return ($Path-replace '\\','/')
  }
  $rg=@(Get-Command rg -CommandType Application -ErrorAction Stop)
  if($rg.Count -ne 1){throw 'claim expectation requires one resolved rg executable'}
  $rgPath=[string]$rg[0].Source
  $runner=Join-Path $root 'scripts/packed_native_lifecycle_storage_replay.ps1'
  $runnerSource=[IO.File]::ReadAllText($runner,$encoding)
  $rawChildMatch=[regex]::Match($runnerSource,"(?s)\`$taskChildScript = @'\r?\n(.*?)\r?\n'@")
  if(-not $rawChildMatch.Success){throw 'claim expectation raw child missing'}
  $rawChild=Join-Path $EvidenceRoot 'rg-raw-child.ps1'
  [IO.File]::WriteAllText($rawChild,$rawChildMatch.Groups[1].Value,$encoding)
  $release=Join-Path $EvidenceRoot 'rg.release'
  [IO.File]::WriteAllText($release,'released inside already owned producer',$encoding)
  $records=[Collections.Generic.List[string]]::new()
  $captures=[Collections.Generic.List[object]]::new()
  $hits=0;$failures=0;$ordinal=0
  foreach($term in @($policy.terms)) {
    $ordinal++
    $arguments=@('--json','--pcre2')
    if($term.multiline -eq $true){$arguments+='--multiline'}
    $arguments+=@('--glob','!**/audit_reports/**','--glob','!**/*WORKLOG.md','--',[string]$term.pattern)+$roots
    $stage=Join-Path $EvidenceRoot ('rg-'+$ordinal.ToString('00'))
    [void][IO.Directory]::CreateDirectory($stage)
    $spec=@{file=$rgPath;arguments=$arguments;cwd=$root;environment=@{};stdout=(Join-Path $stage 'stdout.log');
      stderr=(Join-Path $stage 'stderr.log');exit=(Join-Path $stage 'exit.json');pid=(Join-Path $stage 'pid');
      error=(Join-Path $stage 'error');overflow=(Join-Path $stage 'overflow');outputLimit=16777216}
    $specPath=Join-Path $stage 'spec.json'
    [IO.File]::WriteAllText($specPath,($spec|ConvertTo-Json -Depth 8),$encoding)
    # The producer is already inside the outer bounded job. Reuse the protected
    # byte-copy child inline so all rg descendants inherit that same ownership.
    & $rawChild -SpecPath $specPath -LaunchReleasePath $release
    $code=$LASTEXITCODE
    if([IO.File]::Exists($spec.error) -or [IO.File]::Exists($spec.overflow) -or -not [IO.File]::Exists($spec.exit)){
      throw ('claim expectation incomplete rg capture for '+$term.id)
    }
    $actual=[IO.File]::ReadAllText($spec.exit,$encoding)|ConvertFrom-Json
    $stdout=[IO.File]::ReadAllText($spec.stdout,$encoding)
    $stderr=[IO.File]::ReadAllText($spec.stderr,$encoding)
    if($code -notin @(0,1) -or $actual.exitCode -ne $code -or $stderr -cne ''){throw ('claim expectation rg diagnostic/exit for '+$term.id)}
    $pins=@($spec.stdout,$spec.stderr,$spec.exit,$specPath)|ForEach-Object {@{path=$_;bytes=([IO.FileInfo]$_).Length;sha256=(Get-FileHash -LiteralPath $_).Hash}}
    $captures.Add(@{id=$term.id;actual=$actual;raw=@($pins)})
    # rg JSONL has one terminal LF and no blank records. Do not silently remove
    # interior blank lines, malformed JSON, or unrelated output.
    if(-not $stdout.EndsWith("`n",[StringComparison]::Ordinal)){throw ('claim expectation missing rg JSON terminator for '+$term.id)}
    foreach($jsonLine in [regex]::Split($stdout.Substring(0,$stdout.Length-1),'\r?\n')) {
      if($jsonLine.Length -eq 0){throw 'claim expectation empty rg JSON record'}
      $record=$jsonLine|ConvertFrom-Json -ErrorAction Stop
      if($record.type -notin @('begin','match','end','summary')){throw 'claim expectation unknown rg JSON record'}
      if($record.type -ne 'match'){continue}
      $file=Get-ClaimText $record.data.path
      $fileNorm=Get-ClaimPolicyPath $file
      $line=Get-ClaimText $record.data.lines
      $policyLine=$line.TrimEnd([char[]]"`r`n")
      $hits++
      $allowed=([string]$term.scope -eq 'current-fact-surface' -and $fileNorm -notmatch $currentSurface) -or
        ($term.allowedPathRegex -and $fileNorm -match [string]$term.allowedPathRegex) -or
        ($term.allowedLineRegex -and $policyLine -match [string]$term.allowedLineRegex) -or
        ($term.allowedPathLinePathRegex -and $term.allowedPathLineRegex -and
          $fileNorm -match [string]$term.allowedPathLinePathRegex -and $policyLine -match [string]$term.allowedPathLineRegex)
      foreach($pair in @($term.allowedPathLinePairs)) {
        if($pair.pathRegex -and $pair.lineRegex -and $fileNorm -match [string]$pair.pathRegex -and $policyLine -match [string]$pair.lineRegex){$allowed=$true;break}
      }
      $label=if($allowed){'allowed'}elseif($term.strict -eq $true){$failures++;'fail'}else{'review'}
      if($label -cne 'allowed') {
        $records.Add(('CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}' -f $term.id,$term.status,$label,$file,[string]$record.data.line_number,$line.Trim())+$newline)
      }
    }
  }
  $files=@(foreach($path in $roots){$item=Get-Item -LiteralPath $path;if($item.PSIsContainer){Get-ChildItem -LiteralPath $item.FullName -Recurse -File}else{$item}})
  $files=@($files|Where-Object {$_.FullName -notmatch '[\\/]audit_reports[\\/]' -and $_.Name -notmatch 'WORKLOG\.md$'}|Sort-Object FullName -Unique)
  foreach($attribution in @($policy.requiredAttributions)) {
    foreach($file in $files) {
      $fileNorm=Get-ClaimPolicyPath $file.FullName
      if($fileNorm -notmatch [string]$attribution.pathRegex){continue}
      $content=Get-Content -LiteralPath $file.FullName -Raw
      $claim=[regex]::Match($content,[string]$attribution.claimPattern)
      if(-not $claim.Success){continue}
      $hits++
      $present=[regex]::IsMatch($content,[string]$attribution.requiredPattern)
      $label=if($present){'allowed'}elseif($attribution.strict -eq $true){$failures++;'fail'}else{'review'}
      $lineNo=if($claim.Index -le 0){1}else{1+([regex]::Matches($content.Substring(0,$claim.Index),"`n")).Count}
      $summary=if($present){'strong claim has its required theorem identity'}else{'strong claim is missing required theorem identity'}
      $records.Add(('CLAIM-DRIFT[{0}][{1}][{2}] {3}:{4}: {5}' -f $attribution.id,$attribution.status,$label,$fileNorm,$lineNo,$summary)+$newline)
    }
  }
  if($failures -ne 0){throw ('claim expectation strict failures: '+$failures)}
  $footer=if($hits -eq 0){'CLAIM-DRIFT: no sensitive terms found'+$newline}else{''}
  $footer+='CLAIM-DRIFT: scan complete ('+$hits+' hits, 0 strict failures)'+$newline
  $sourcePins=@($script:LNClaimExpectationSource,(Join-Path $root 'scripts/claim_drift_scan.ps1'),$policyPath,$runner,$rgPath)|ForEach-Object {@{path=$_;bytes=([IO.FileInfo]$_).Length;sha256=(Get-FileHash -LiteralPath $_).Hash}}
  return [ordered]@{Profile='claims-strict-subtree-ledgers';Records=@($records.ToArray());Footer=$footer;Stderr='';ExpectedExit=0;
    Hits=$hits;StrictFailures=$failures;Roots=$roots;PolicyVersion=$policy.version;SourcePins=@($sourcePins);RipgrepConfigPath=$env:RIPGREP_CONFIG_PATH;
    Captures=@($captures.ToArray());Ordering='Exact prefix-free whole-record multiset; no byte normalization within records; exact final footer.'}
}

if($Produce) {
  $ErrorActionPreference='Stop'
  $value=New-LNClaimStreamExpectation $RepositoryRoot $EvidenceRoot
  [IO.File]::WriteAllText((Join-Path $EvidenceRoot 'EXPECTATION.json'),($value|ConvertTo-Json -Depth 16),[Text.UTF8Encoding]::new($false,$true))
  exit 0
}
