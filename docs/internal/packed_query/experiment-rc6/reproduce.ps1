param(
  [string]$Candidate = (Join-Path $PSScriptRoot '..\audit-rc6-20260910'),
  [string]$Lean = 'C:\Users\poin\.elan\toolchains\leanprover--lean4---v4.22.0\bin\lean.exe',
  [string]$Python = 'C:\Users\poin\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe',
  [switch]$RegenerateFixtures
)
$ErrorActionPreference = 'Stop'
$candidatePath = (Resolve-Path -LiteralPath $Candidate).Path
$identity = & git -C $candidatePath rev-parse HEAD
if ($identity -ne '4639223bc8130b0ef752270b5cbdd74325abcd60') { throw 'Wrong candidate identity' }
$dirty = & git -C $candidatePath -c core.excludesFile= status --porcelain --untracked-files=no
if ($dirty) { throw 'Tracked candidate source is dirty' }
$env:LEAN_PATH = Join-Path $candidatePath '.lake\build\lib\lean'
Push-Location -LiteralPath $PSScriptRoot
try {
  if ($RegenerateFixtures) {
    $cases = @(@(9,'balanced'),@(9,'ascending'),@(9,'descending'),@(9,'ties'),
      @(15,'zigzag'),@(16,'balanced'),@(29,'zigzag'),@(15,'comb'))
    foreach ($case in $cases) {
      $output = 'fixture-n' + $case[0] + '-' + $case[1] + '.json'
      & $Lean --run ExportFixture.lean $output $case[0] $case[1]
      if ($LASTEXITCODE -ne 0) { throw "Exporter failed: $output" }
    }
    & $Lean --run ExportFixture.lean fixture-n9-invalid.json 9 balanced 4 4
    if ($LASTEXITCODE -ne 0) { throw 'Invalid fixture export failed' }
  }
  & $Python compiler_checks.py
  if ($LASTEXITCODE -ne 0) { throw 'Compiler edge checks failed' }
  $fixtures = Get-ChildItem -LiteralPath . -Filter 'fixture-*.json' |
    Where-Object { $_.Name -notlike '*-vm.json' } | Sort-Object Name
  foreach ($fixture in $fixtures) {
    & $Python run_experiment.py $fixture.Name
    if ($LASTEXITCODE -ne 0) { throw "VM/reference check failed: $($fixture.Name)" }
    $n = (Get-Content -LiteralPath $fixture.FullName -Raw | ConvertFrom-Json).n
    & $Lean --run CheckMachine.lean ('program-n' + $n + '.json') $fixture.Name ($fixture.BaseName + '-vm.json')
    if ($LASTEXITCODE -ne 0) { throw "Lean cross-check failed: $($fixture.Name)" }
  }
  & $Python validate.py
  if ($LASTEXITCODE -ne 0) { throw 'Query/mutation validation failed' }
} finally {
  Pop-Location
}
