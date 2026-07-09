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
3. A verified reference Word-RAM machine with a small-step semantics for the
   fragment used by the query controller, plus a theorem that machine execution
   simulates the existing trace/register-program semantics with matching result
   and step/cost accounting.
4. A small C or Rust code generator from the first-order WordRAM language,
   paired with Lean-checked translation-validation certificates for each
   generated query program.
5. Only after those layers are stable, a verified backend or full compiler
   story.

The current theorems are model-soundness statements for payload bits,
read-store traces, and WordRAM/register programs. They are not claims that Lean
execution time, generated C/Rust hardware time, or a future compiler backend
already satisfies the modeled constant-query bound.

The final RMQ roadmap refines the ordering: first lift the strongest final
store/footprint model theorem to the list-facing interface, then clean the
all-size cost surface, then build the runnable Lean validation path. The later
reference-machine and code-generation layers should wait until those public
theorem surfaces are settled.
