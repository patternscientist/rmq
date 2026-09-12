param(
  [AllowEmptyString()][string]$Case,
  [switch]$Startup,
  [switch]$ListRegistry,
  [string]$Stage = 'select-probe',
  [int]$DeadlineSeconds = 120
)
$ErrorActionPreference = 'Stop'
$caseNames = @(
  'empty-false', 'empty-true', 'singleton-zero', 'singleton-one', 'singleton-missing',
  'size-two-false', 'size-two-true', 'size-two-invalid', 'zeros-last', 'zeros-missing-true',
  'ones-last', 'ones-missing-false', 'alternating-false', 'alternating-true',
  'mixed-false', 'mixed-true', 'threshold-minus-one', 'threshold'
)
if ($caseNames.Count -ne 18 -or @($caseNames | Select-Object -Unique).Count -ne 18) {
  Write-Error 'BV1-REGISTRY FAIL version=1'
  exit 2
}
$boundCase = $PSBoundParameters.ContainsKey('Case')
if (($Startup -and $ListRegistry) -or ($boundCase -and ($Startup -or $ListRegistry))) {
  [Console]::Error.WriteLine('BV1-SELECTOR FAIL: incompatible selectors')
  exit 2
}
if ($boundCase -and ([string]::IsNullOrWhiteSpace($Case) -or
    $Case -cne $Case.Trim() -or -not ($caseNames -ccontains $Case))) {
  [Console]::Error.WriteLine('BV1-SELECTOR FAIL: Case must be one exact nonempty registry name')
  exit 2
}
$repo = (Resolve-Path (Join-Path $PSScriptRoot '..')).Path
$arguments = @('env', 'lean', '--run', 'RMQ/Validation/PackedBitvector.lean')
if ($Startup) { $arguments += '--startup' }
elseif ($ListRegistry) { $arguments += '--list' }
elseif ($boundCase) { $arguments += @('--case', $Case) }
$runner = Join-Path $repo 'docs/internal/extensions/bv1/run_command.ps1'
& $runner -Stage $Stage -Executable 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe' `
  -CommandArguments $arguments -DeadlineSeconds $DeadlineSeconds
exit $LASTEXITCODE
