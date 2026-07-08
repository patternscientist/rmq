# RMQ Extraction Frontier

This is a planning note only; this branch does not start an extraction
implementation.

The next executable-artifact ladder should move in this order:

1. A runnable Lean executable around the existing public functions, especially
   `SuccinctClassic.buildPayload` and `SuccinctClassic.queryCosted`, with
   small input/output fixtures for reviewer replay.
2. A compiled interpreter for the existing first-order WordRAM/register-program
   controller, preserving the current distinction between modeled cost ticks
   and Lean runtime.
3. A small C or Rust code generator from the first-order WordRAM language,
   paired with Lean-checked translation-validation certificates for each
   generated query program.
4. Only after those layers are stable, a verified backend or full compiler
   story.

The current theorems are model-soundness statements for payload bits,
read-store traces, and WordRAM/register programs. They are not claims that Lean
execution time, generated C/Rust hardware time, or a future compiler backend
already satisfies the modeled constant-query bound.
