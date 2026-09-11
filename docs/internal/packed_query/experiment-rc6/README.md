# Whole-path experiment

Read [ASSESSMENT.md](ASSESSMENT.md) for the result, recommendation, measurements and limits.

The complete different-block query executes as primitive register instructions on RC6's exact packed memory. Python and Lean interpreters agree with the canonical controller's ordered physical reads. This is a finite feasibility experiment, not a universal instruction theorem.

Run `./reproduce.ps1` for the saved fixtures, or `./reproduce.ps1 -RegenerateFixtures` to regenerate canonical reference data first. The default tool and candidate paths are recorded in the script and can be overridden. The candidate must be built at commit `4639223bc8130b0ef752270b5cbdd74325abcd60` using Lean 4.22.0.

The `*_program.py` and generated `program-n*-source.py` files are restricted source for compilation; they are not host-language query implementations. `machine.py` supplies the compiler and primitive VM. `CheckMachine.lean` is the independent primitive interpreter. Only `ExportFixture.lean` uses the RMQ reference library.

`reproduction.log` records the final successful saved-fixture reproduction. `validation-results.json` includes all query counts and mutation outcomes. `manifest.json` hashes the files in this package except itself.
