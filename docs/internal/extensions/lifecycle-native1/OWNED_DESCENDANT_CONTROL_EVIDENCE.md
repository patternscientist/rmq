# Owned descendant and partial-setup controls

`owned_descendant_control.ps1` exercises the unchanged owned-process and retained
raw-capture helpers on Windows. Its worker has an outer thirty-second bound.
Inside it, an eight-second owned stage starts a PowerShell root that starts one
intentional PowerShell descendant with `Start-Process -WindowStyle Hidden`.
The root and descendant each write their own PID; the root also records the
PID returned by `Start-Process`. Both then sleep for 120 seconds. The recorded
PID agreement and ready output precede the deliberately induced timeout.

The final complete command returned ordinary exit zero with three ordered
controls passing. Evidence:
`.lake/lifecycle-native1/owned-controls/20260923T091922860-5b5f618f/RESULT.json`
and its pinned `WORKER.json`.

- The inner helper timed out after 8.093 seconds. Its `ExitCode=-1` is preserved
  as the helper's sentinel; the actual producer ordinary-exit receipt is null.
  The production stream predicate rejects this as an incomplete bounded capture.
- Root PID 36368 and descendant PID 36440 occur in `TerminatedIds` and were
  absent immediately after the inner barrier and again after the outer barrier.
  The job receipt also includes helper/OS-created processes; this does not claim
  the complete job contains exactly two processes.
- Raw root stdout is exactly `OWNED-DESCENDANT ROOT READY\n`; stderr and launcher
  streams are empty. The enclosing worker's exact success stream and ordinary
  exit zero passed the production outer-capture predicate. It took 11.1426326
  seconds, within the thirty-second outer bound.
- Both forced partial-setup cases throw after creating an owned temporary
  fixture and before launching any semantic child. Their independent `finally`
  blocks both attempt integrity and cleanup. The intact case reports intact
  pins; the deliberately changed owned-file pin is rejected, while cleanup still
  succeeds. No live source file is mutated by either control.
- Outer and worker source/tool integrity checks pass; disposable directories
  are removed; neither recorded PID remains alive. Source, shell executable,
  generated caller scripts, PID files, captures, deadlines and actual statuses
  are retained in the evidence. No global process cleanup or heavy mutex is used.

The first attempt at `20260923T091817660-e38f2410` preserved a genuine outer
failure: the report reader assigned a JSON object to a variable whose name
collided with the typed `Worker` switch. Inner controls and cleanup succeeded.
The variable was renamed and the entire bounded command was rerun; the final
result above certifies the corrected script.

This is Windows evidence for the existing job barrier and these specific
partial-setup finalizers. It does not certify POSIX behavior, all possible child
escape mechanisms, or every other replay's early-error finalization path.
