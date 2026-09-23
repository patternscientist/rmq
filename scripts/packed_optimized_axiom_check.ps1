# Explicit inventory of the new capstone, generic producers and every field consumer.
[CmdletBinding()]
param()
$ErrorActionPreference = 'Stop'
$repo = (Get-Location).Path
. (Join-Path $repo 'scripts/owned_process_tree.ps1')
$lean = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
$source = Join-Path $repo 'scripts/packed_optimized_axiom_union.lean'
$manifest = Join-Path $repo 'docs/internal/extensions/opt1/AXIOM_ROOTS.json'
$cache = Join-Path $repo '.lake/build/lib/lean'
$evidence = Join-Path $repo 'docs/internal/extensions/opt1/composition-development'
[void](New-Item -ItemType Directory -Force -Path $evidence)
$inventory = Get-Content -LiteralPath $manifest -Raw | ConvertFrom-Json
$expected = @($inventory.Names)
if ($expected.Count -ne 93 -or @($expected | Select-Object -Unique).Count -ne 93) {
  throw 'The frozen public/producer/consumer inventory must contain exactly 93 distinct declarations.'
}
$arguments = @('-j1',$source)
$result = Invoke-RMQOwnedBoundedProcess -FilePath $lean -Arguments $arguments `
  -WorkingDirectory $repo -Stage 'optimized-axiom-inventory' -DeadlineSeconds 180 `
  -OutputLimitBytes 2097152 -TempRoot (Join-Path $repo '.lake/opt1-axioms') `
  -Environment @{ LEAN_PATH=$cache }
$output = @($result.StandardOutput) -join "`n"
$found = @([regex]::Matches($output, 'OPT1-AXIOM-ROOT ([^\s]+)') |
  ForEach-Object { $_.Groups[1].Value })
$uncovered = @($expected | Where-Object { $found -cnotcontains $_ })
$unexpected = @($found | Where-Object { $expected -cnotcontains $_ })
$unions = @([regex]::Matches($output, 'OPT1-AXIOM-UNION ([^\r\n]*)'))
$axioms = @($unions | ForEach-Object { $_.Groups[1].Value -split '[,\s]+' } |
  Where-Object { -not [string]::IsNullOrWhiteSpace($_) } | Sort-Object -Unique)
$printed = @([regex]::Matches($output, "'([^']+)' (?:depends on axioms:|does not depend on any axioms)") |
  ForEach-Object { $_.Groups[1].Value })
$publicPrints = @('RMQ.SuccinctFinal.PackedWordRAM.Optimization.branchSensitiveQueryBound',
  'RMQ.SuccinctFinal.PackedWordRAM.Optimization.compactPackedQueryCapstone_holds')
$printMissing = @($publicPrints | Where-Object { $printed -cnotcontains $_ })
$printAxioms = @([regex]::Matches($output, 'depends on axioms:\s*\[([^\]]*)\]') |
  ForEach-Object { $_.Groups[1].Value -split '[,\s]+' } |
  Where-Object { -not [string]::IsNullOrWhiteSpace($_) } | Sort-Object -Unique)
$unionMissingPrinted = @($printAxioms | Where-Object { $axioms -cnotcontains $_ })
$extraAxioms = @($axioms | Where-Object { @('propext','Classical.choice','Quot.sound') -cnotcontains $_ })
$pass = $result.ExitCode -eq 0 -and -not $result.TimedOut -and -not $result.OutputLimitExceeded -and
  $found.Count -eq 93 -and @($found | Select-Object -Unique).Count -eq 93 -and
  $uncovered.Count -eq 0 -and $unexpected.Count -eq 0 -and $extraAxioms.Count -eq 0 -and
  $unions.Count -eq 1 -and $printed.Count -eq 2 -and $printMissing.Count -eq 0 -and
  $unionMissingPrinted.Count -eq 0
$record = [ordered]@{
  Command=@($lean)+$arguments; SourceSHA256=(Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash;
  ManifestSHA256=(Get-FileHash -LiteralPath $manifest -Algorithm SHA256).Hash;
  Base='0e6a00f654abc64f8b68988fa9675b9a839dca2f'; Platform=[Environment]::OSVersion.VersionString;
  Expected=$expected; Found=$found; Uncovered=$uncovered; Unexpected=$unexpected;
  InventorySemantics='Exact union for all covered roots via shared builtin collector state; not individual distributions';
  Axioms=$axioms; UnexpectedAxioms=$extraAxioms; StandardPrintedRoots=$printed;
  StandardPrintAxioms=$printAxioms; UnionMissingPrinted=$unionMissingPrinted; Passed=$pass; Result=$result
}
$stamp = [DateTime]::UtcNow.ToString('yyyyMMddTHHmmssfffffffZ')
$record | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath (Join-Path $evidence ($stamp+'-axioms.json')) -Encoding utf8
Write-Output "OPT1-AXIOMS: expected=$($expected.Count) found=$($found.Count) pass=$pass"
Write-Output ("OPT1-AXIOMS: dependencies=" + ($axioms -join ','))
if (-not $pass) { $result.StandardOutput; $result.StandardError; exit 1 }
