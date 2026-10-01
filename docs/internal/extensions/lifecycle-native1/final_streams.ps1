# Dot-source after lifecycle_native_identity.ps1. The caller pins this helper,
# the unchanged checkers/policy and every selected input before and in finally.
# These functions validate the checkers' output language and its source/receipt
# bindings. The unchanged production checkers remain the policy authorities.

function Get-LNFinalLines([string]$Text) {
  $eol=[Environment]::NewLine
  if(-not $Text.EndsWith($eol,[StringComparison]::Ordinal)){throw 'FINAL-STREAM: missing final host newline'}
  $lines=$Text.Split([string[]]@($eol),[StringSplitOptions]::None)
  if($lines.Count -lt 2 -or $lines[-1] -cne ''){throw 'FINAL-STREAM: invalid line framing'}
  foreach($line in $lines[0..($lines.Count-2)]){
    if($line.Length -eq 0 -or $line.Contains("`r") -or $line.Contains("`n")){
      throw 'FINAL-STREAM: empty line or non-host newline'
    }
    $line
  }
}

function Get-LNFinalPathSet([string[]]$Paths) {
  $set=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $hostSet=[Collections.Generic.HashSet[string]]::new([StringComparer]::OrdinalIgnoreCase)
  foreach($path in $Paths){
    if([string]::IsNullOrWhiteSpace($path) -or $path -match '[\\:\r\n\x00]' -or
        [IO.Path]::IsPathRooted($path) -or @($path.Split('/')|Where-Object{$_ -in @('','.', '..')}).Count){
      throw ('FINAL-STREAM: unsupported relative input path '+$path)
    }
    if(-not $set.Add($path) -or -not $hostSet.Add($path)){throw ('FINAL-STREAM: duplicate input path '+$path)}
  }
  if($set.Count -eq 0){throw 'FINAL-STREAM: empty input roster'}
  return ,$set
}

function Assert-LNFinalPin($Pin,[string]$Path) {
  $full=[IO.Path]::GetFullPath($Path)
  if(-not [StringComparer]::OrdinalIgnoreCase.Equals([string]$Pin.path,$full) -or
      [string]$Pin.sha256 -cnotmatch '\A[0-9a-fA-F]{64}\z'){
    throw ('FINAL-STREAM: malformed or misplaced receipt pin '+$full)
  }
  $now=Get-LN1Pin $full
  if($now.bytes -ne $Pin.bytes -or $now.sha256 -ine [string]$Pin.sha256){
    throw ('FINAL-STREAM: receipt input changed '+$full)
  }
  return $now
}

function Get-LNFinalCheckerAst([string]$Path) {
  $tokens=$null;$errors=$null
  $ast=[Management.Automation.Language.Parser]::ParseFile($Path,[ref]$tokens,[ref]$errors)
  if(@($errors).Count){throw ('FINAL-STREAM: checker parse failure '+$Path)}
  return $ast
}

function Get-LNFinalLiteral($Ast,[string]$Name) {
  $nodes=@($Ast.FindAll({param($node)
    $node -is [Management.Automation.Language.AssignmentStatementAst] -and
    $node.Left -is [Management.Automation.Language.VariableExpressionAst] -and
    $node.Left.VariablePath.UserPath -ceq $Name
  },$true))
  if($nodes.Count -ne 1 -or $nodes[0].Right -isnot [Management.Automation.Language.CommandExpressionAst]){
    throw ('FINAL-STREAM: ambiguous checker literal '+$Name)
  }
  # SafeGetValue accepts literals; it does not execute the checker or a command.
  return $nodes[0].Right.Expression.SafeGetValue()
}

function Assert-LNFinalScope($Capture,[string]$Root,[string]$Base,[string]$Head,[string[]]$Paths) {
  $stdout=Read-LNExactStream $Capture.spec.stdout
  Assert-LNOuterCapture $Capture $stdout '' 0 'final-scope'
  $lines=@(Get-LNFinalLines $stdout)
  if($lines.Count -ne 1){throw 'FINAL-SCOPE: expected exactly one success line'}
  $match=[regex]::Match($lines[0],'\ALIFECYCLE-SCOPE success=True receipt=(?<run>[^\r\n\x00]+)\z')
  if(-not $match.Success){throw 'FINAL-SCOPE: unexpected diagnostic'}
  $scopeRoot=Join-Path $Root '.lake/lifecycle-native1/scope'
  $stamp=[IO.Path]::GetFileName($match.Groups['run'].Value)
  if($stamp -cnotmatch '\A[0-9]{8}T[0-9]{9}\z'){throw 'FINAL-SCOPE: invalid receipt directory'}
  $directory=Join-Path $scopeRoot $stamp
  $expected='LIFECYCLE-SCOPE success=True receipt='+$directory+[Environment]::NewLine
  Assert-LNOuterCapture $Capture $expected '' 0 'final-scope'
  $receiptPath=Join-Path $directory 'RESULT.json'
  $receiptPin=Get-LN1Pin $receiptPath
  $receipt=(Read-LNExactStream $receiptPath)|ConvertFrom-Json -ErrorAction Stop
  if($receipt.schema -cne 'lifecycle-native1-scope-v1' -or $receipt.success -cne $true -or
      $receipt.base -cne $Base -or $receipt.head -cne $Head -or
      $receipt.branch -cne 'codex/life-native-1-consuming-owner' -or
      $receipt.checkedBaseFiles -ne 3844 -or $null -ne $receipt.failure){
    throw 'FINAL-SCOPE: unsuccessful or differently bound scope receipt'
  }
  $pins=[Collections.Generic.List[object]]::new();$pins.Add($receiptPin)
  $baselinePath=Join-Path $Root 'docs/internal/extensions/lifecycle-native1/BASE_IDENTITY.json'
  $baselinePin=Get-LN1Pin $baselinePath
  if($baselinePin.sha256 -ine 'cfeb23f578e9ec014f2302220de4c08960f2c96892f8be5c60608ff8c4cb6997'){
    throw 'FINAL-SCOPE: frozen baseline changed'
  }
  $pins.Add($baselinePin)
  $baseline=(Read-LNExactStream $baselinePath)|ConvertFrom-Json -ErrorAction Stop
  if($baseline.base -cne $Base -or @($baseline.files).Count -ne 3844){throw 'FINAL-SCOPE: baseline domain differs'}
  $known=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($file in $baseline.files){if(-not $known.Add([string]$file.path)){throw 'FINAL-SCOPE: duplicate baseline path'}}
  $scopeAst=Get-LNFinalCheckerAst (Join-Path $Root 'docs/internal/extensions/lifecycle-native1/scope_check.ps1')
  $allowedExisting=@(Get-LNFinalLiteral $scopeAst 'allowedExisting')
  $allowedNew=@(Get-LNFinalLiteral $scopeAst 'allowedNew')
  $requested=Get-LNFinalPathSet $Paths
  $reported=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  foreach($change in @($receipt.changes)){
    $path=[string]$change.path
    if(-not $known.Contains($path) -or $allowedExisting -cnotcontains $path -or -not $reported.Add($path)){
      throw ('FINAL-SCOPE: unexpected changed original '+$path)
    }
    $full=Join-Path $Root $path
    $pin=@{path=$full;bytes=$change.bytes;sha256=$change.sha256}
    $pins.Add((Assert-LNFinalPin $pin $full))
  }
  foreach($file in @($receipt.newFiles)){
    $path=[string]$file.path
    if($known.Contains($path) -or -not $requested.Contains($path) -or -not $reported.Add($path) -or
        ($allowedNew -cnotcontains $path -and
         $path -cnotmatch '\ARMQ/Core/WordRAM/Native/Lifecycle/(?:[A-Za-z0-9_]+/)*[A-Za-z0-9_]+\.lean\z' -and
         $path -cnotmatch '\Adocs/internal/extensions/lifecycle-native1/[^\r\n]+\z') -or
        $path -match '\.(?:log|zip|7z|tar|gz)$'){
      throw ('FINAL-SCOPE: unexpected new path '+$path)
    }
    $pins.Add((Assert-LNFinalPin $file.pin (Join-Path $Root $path)))
  }
  if(-not $requested.SetEquals($reported)){throw 'FINAL-SCOPE: current path roster differs from scope receipt'}
  $contract=Assert-LN1FrozenContract $Root
  if($receipt.contract.success -cne $true -or $receipt.contract.count -ne 55 -or
      @($receipt.contract.changedIds).Count -ne 0 -or @($receipt.contract.orderedIds).Count -ne 55){
    throw 'FINAL-SCOPE: incomplete frozen contract receipt'
  }
  for($i=0;$i -lt 55;$i++){
    if($receipt.contract.orderedIds[$i] -cne $contract.orderedIds[$i]){throw 'FINAL-SCOPE: contract ID order differs'}
  }
  foreach($name in @('contract','matrix')){
    $pins.Add((Assert-LNFinalPin $receipt.contract.$name $contract.$name.path))
  }
  $startup=Assert-LN1StartupWitnesses $Root
  if($receipt.startupAmendment.success -cne $true -or $receipt.startupAmendment.exactInsertions -ne 5 -or
      @($receipt.startupAmendment.checked).Count -ne 2){throw 'FINAL-SCOPE: incomplete startup amendment receipt'}
  for($i=0;$i -lt 2;$i++){
    $actual=$receipt.startupAmendment.checked[$i];$current=$startup.checked[$i]
    if($actual.originalRawSHA256 -ine $current.originalRawSHA256 -or
        @($actual.erasedDefinitions).Count -ne @($current.erasedDefinitions).Count){
      throw 'FINAL-SCOPE: startup witness identity differs'
    }
    for($j=0;$j -lt @($current.erasedDefinitions).Count;$j++){
      if($actual.erasedDefinitions[$j] -cne $current.erasedDefinitions[$j]){throw 'FINAL-SCOPE: startup witness order differs'}
    }
    foreach($name in @('source','generated')){$pins.Add((Assert-LNFinalPin $actual.$name $current.$name.path))}
  }
  [void](Assert-LNFinalPin $receiptPin $receiptPath)
  return [ordered]@{pin=$receiptPin;pins=@($pins.ToArray());summary=[ordered]@{
    schema=$receipt.schema;base=$Base;head=$Head;branch=$receipt.branch;checkedBaseFiles=3844;
    contractRows=55;changedOriginals=@($receipt.changes).Count;newFiles=@($receipt.newFiles).Count;
    coveredPaths=$reported.Count;startupInsertions=5;
    boundary='Pinned scope checker supplies the outside-scope classification; this check binds its complete current roster and receipt inputs.'}}
}

function Assert-LNFinalDesign($Capture,[string[]]$Paths) {
  $requested=Get-LNFinalPathSet $Paths
  $checker=[IO.Path]::GetFullPath((Join-Path $PSScriptRoot '../../../../scripts/design_decision_check.ps1'))
  $checkerPin=Get-LN1Pin $checker
  $ast=Get-LNFinalCheckerAst $checker
  foreach($name in @('neutralEvidencePatterns','workflowRootPatterns','codeRootPatterns','proofCodePattern',
      'workflowCodePattern','nativeSourcePattern','nativeCodePatterns','nativeWorkflowPatterns')){
    Set-Variable -Name $name -Value (Get-LNFinalLiteral $ast $name) -Scope Local
  }
  $definitions=[Collections.Generic.List[string]]::new()
  foreach($name in @('Test-AnyPattern','Get-PathDisposition')){
    $nodes=@($ast.FindAll({param($node)
      $node -is [Management.Automation.Language.FunctionDefinitionAst] -and $node.Name -ceq $name
    },$true))
    if($nodes.Count -ne 1){throw ('FINAL-DESIGN: ambiguous pure classifier '+$name)}
    $definitions.Add($nodes[0].Extent.Text)
  }
  # Reuse only the pinned checker's two pure functions and literal tables. Its
  # Git/process/report code is neither dot-sourced nor executed here.
  $classifier=[scriptblock]::Create("param([string]`$ClassifiedPath)`n"+
    ($definitions.ToArray() -join "`n")+"`nGet-PathDisposition -Path `$ClassifiedPath")
  $code=0;$workflow=0;$neutral=0
  foreach($path in $Paths){
    $rows=@(& $classifier $path)
    if($rows.Count -ne 1 -or $rows[0].Unclassified){throw ('FINAL-DESIGN: unclassified selected path '+$path)}
    if($rows[0].NeedsCode){$code++};if($rows[0].NeedsWorkflow){$workflow++};if($rows[0].Neutral){$neutral++}
  }
  if($code -le 0 -or $workflow -le 0 -or -not $requested.Contains('docs/internal/DESIGN_DECISIONS.md') -or
      -not $requested.Contains('docs/internal/WORKFLOW_DESIGN_DECISIONS.md')){
    throw 'FINAL-DESIGN: candidate code/workflow ledger coverage is incomplete'
  }
  $expected='DESIGN-CHECK: checked '+$Paths.Count+' changed files ('+$code+' code, '+$workflow+
    ' workflow, '+$neutral+' neutral)'+[Environment]::NewLine
  Assert-LNOuterCapture $Capture $expected '' 0 'final-design'
  [void](Assert-LNFinalPin $checkerPin $checker)
  return [ordered]@{checkerPin=$checkerPin;summary=@{paths=$Paths.Count;code=$code;workflow=$workflow;neutral=$neutral;
    boundary='Exact counts from the unchanged checker literal tables and pure path classifier; both ledgers are in the selected roster.'}}
}

function Assert-LNFinalClaims($Capture,[string]$Root,[string]$PolicyPath,[string[]]$Paths) {
  $stdout=Read-LNExactStream $Capture.spec.stdout
  Assert-LNOuterCapture $Capture $stdout '' 0 'final-claims'
  $lines=@(Get-LNFinalLines $stdout)
  $requested=Get-LNFinalPathSet $Paths
  if(-not [IO.Path]::IsPathRooted($PolicyPath)){$PolicyPath=Join-Path $Root $PolicyPath}
  $policyPin=Get-LN1Pin $PolicyPath
  $policy=(Read-LNExactStream $PolicyPath)|ConvertFrom-Json -ErrorAction Stop
  $terms=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  $attributions=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  $index=0;$reviewTermCount=0
  foreach($term in $policy.terms){
    if($terms.ContainsKey([string]$term.id)){throw 'FINAL-CLAIMS: duplicate policy term'}
    $terms.Add([string]$term.id,@{term=$term;index=$index});$index++
    if(-not $term.strict){
      $reviewTermCount++
      if($term.multiline){throw 'FINAL-CLAIMS: unsupported non-strict multiline output'}
      # The current policy's non-strict terms use only optional path allowances.
      foreach($property in $term.PSObject.Properties){
        if($property.Name -like 'allowed*' -and $property.Name -cne 'allowedPathRegex' -and $property.Value){
          throw 'FINAL-CLAIMS: non-strict allowance shape changed'
        }
      }
      if($term.scope){throw 'FINAL-CLAIMS: non-strict term scope changed'}
    }
  }
  if($reviewTermCount -ne 16){throw 'FINAL-CLAIMS: current non-strict term roster changed'}
  foreach($attribution in @($policy.requiredAttributions)){
    if($attribution.strict -cne $true -or $attributions.ContainsKey([string]$attribution.id) -or
        $terms.ContainsKey([string]$attribution.id)){throw 'FINAL-CLAIMS: attribution output shape changed'}
    $attributions.Add([string]$attribution.id,$attribution)
  }
  $summary=[regex]::Match($lines[-1],'\ACLAIM-DRIFT: scan complete \((?<hits>0|[1-9][0-9]*) hits, 0 strict failures\)\z')
  $hits=0L
  if(-not $summary.Success -or -not [long]::TryParse($summary.Groups['hits'].Value,[ref]$hits)){
    throw 'FINAL-CLAIMS: missing exact zero-failure terminal summary'
  }
  $expected=[Text.StringBuilder]::new();$eol=[Environment]::NewLine
  $sourceCache=[Collections.Generic.Dictionary[string,object]]::new([StringComparer]::Ordinal)
  $seen=[Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
  $lastTerm=-1;$attributionStarted=$false;$reviewRecords=0;$attributionRecords=0
  if($hits -eq 0){
    if($lines.Count -ne 2 -or $lines[0] -cne 'CLAIM-DRIFT: no sensitive terms found'){
      throw 'FINAL-CLAIMS: invalid zero-hit output'
    }
    [void]$expected.Append('CLAIM-DRIFT: no sensitive terms found').Append($eol)
  }else{
    for($i=0;$i -lt $lines.Count-1;$i++){
      $record=[regex]::Match($lines[$i],
        '\ACLAIM-DRIFT\[(?<id>[^\]\r\n]+)\]\[(?<status>[^\]\r\n]+)\]\[(?<label>review|allowed)\] (?<path>[^:\r\n]+):(?<line>[1-9][0-9]*): (?<body>[^\r\n]*)\z')
      if(-not $record.Success){throw ('FINAL-CLAIMS: unrelated diagnostic at record '+$i)}
      $id=$record.Groups['id'].Value;$displayPath=$record.Groups['path'].Value
      $path=$displayPath.Replace('\','/');$lineNumber=0L
      if(-not $requested.Contains($path) -or -not [long]::TryParse($record.Groups['line'].Value,[ref]$lineNumber)){
        throw 'FINAL-CLAIMS: finding outside selected input or invalid line number'
      }
      if(-not $sourceCache.ContainsKey($path)){
        $content=Read-LNExactStream (Join-Path $Root $path)
        # Scanner input readers recognize a source-file UTF-8 BOM. Captured
        # diagnostic bytes are never trimmed or otherwise normalized.
        if($content.Length -gt 0 -and $content[0] -eq [char]0xfeff){$content=$content.Substring(1)}
        $sourceCache.Add($path,@{content=$content;lines=$content.Split([char]10)})
      }
      $source=$sourceCache[$path]
      if($lineNumber -le 0 -or $lineNumber -gt $source.lines.Count){throw 'FINAL-CLAIMS: finding line outside source'}
      $key=$id+"`0"+$path+"`0"+$lineNumber
      if(-not $seen.Add($key)){throw 'FINAL-CLAIMS: duplicate finding'}
      if($terms.ContainsKey($id)){
        $entry=$terms[$id];$term=$entry.term
        if($term.strict -or $attributionStarted -or $entry.index -lt $lastTerm -or
            $record.Groups['label'].Value -cne 'review' -or $record.Groups['status'].Value -cne [string]$term.status){
          throw 'FINAL-CLAIMS: unexpected term/status/order'
        }
        $lastTerm=$entry.index;$sourceLine=[string]$source.lines[$lineNumber-1]
        if(-not [regex]::IsMatch($sourceLine,[string]$term.pattern) -or
            ($term.allowedPathRegex -and $path -match [string]$term.allowedPathRegex)){
          throw 'FINAL-CLAIMS: finding does not match its source/policy role'
        }
        $body=$sourceLine.Trim();$label='review';$status=[string]$term.status;$reviewRecords++
      }elseif($attributions.ContainsKey($id)){
        $attributionStarted=$true;$attribution=$attributions[$id]
        $claim=[regex]::Match([string]$source.content,[string]$attribution.claimPattern)
        if($displayPath -cne $path -or $path -notmatch [string]$attribution.pathRegex -or
            $record.Groups['label'].Value -cne 'allowed' -or
            $record.Groups['status'].Value -cne [string]$attribution.status -or -not $claim.Success -or
            -not [regex]::IsMatch([string]$source.content,[string]$attribution.requiredPattern)){
          throw 'FINAL-CLAIMS: invalid required-attribution finding'
        }
        $actualLine=1+[regex]::Matches($source.content.Substring(0,$claim.Index),"`n").Count
        if($lineNumber -ne $actualLine){throw 'FINAL-CLAIMS: attribution line differs'}
        $body='strong claim has its required theorem identity';$label='allowed';$status=[string]$attribution.status
        $attributionRecords++
      }else{throw 'FINAL-CLAIMS: unknown finding ID'}
      $expectedLine='CLAIM-DRIFT['+$id+']['+$status+']['+$label+'] '+$displayPath+':'+$lineNumber+': '+$body
      if(-not [StringComparer]::Ordinal.Equals($lines[$i],$expectedLine)){throw 'FINAL-CLAIMS: finding payload differs from source'}
      [void]$expected.Append($expectedLine).Append($eol)
    }
  }
  if($reviewRecords+$attributionRecords -gt $hits){throw 'FINAL-CLAIMS: visible findings exceed total hits'}
  [void]$expected.Append('CLAIM-DRIFT: scan complete (').Append($hits).Append(' hits, 0 strict failures)').Append($eol)
  Assert-LNOuterCapture $Capture $expected.ToString() '' 0 'final-claims'
  [void](Assert-LNFinalPin $policyPin $PolicyPath)
  return [ordered]@{policyPin=$policyPin;summary=@{hits=$hits;reviewRecords=$reviewRecords;
    attributionRecords=$attributionRecords;visibleRecords=$reviewRecords+$attributionRecords;
    selectedPaths=$Paths.Count;strictFailures=0;
    boundary='Source-authenticated output language; unchanged production scanner classifies all hits, including suppressed allowed terms. No independent strict-detector claim.'}}
}
