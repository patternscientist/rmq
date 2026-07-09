# RMQ Extraction Frontier

This is primarily a planning note. The first runnable Lean validation rung now
has reviewer-facing executables, but the later interpreter, reference-machine,
code-generation, and compiler-validation rungs remain future work.

The next executable-artifact ladder should move in this order:

1. A runnable Lean executable around the existing public functions, especially
   `SuccinctClassic.buildPayload` and `SuccinctClassic.queryCosted`, with
   small input/output fixtures for reviewer replay. This rung is represented by
   `lake exe rmq_succinct_classic_validate` and
   `lake exe rmq_succinct_classic_cost_harness`.
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

The current cost harness reports `queryCosted.cost`, which is the checked
WordRAM trace/event count produced by the model-facing path. It does not report
Lean wall-clock runtime, CPU cost, extracted-code performance, or compiler
behavior. Its default deterministic examples exercise the small-input
zero-block route and a generated `1024`-element active-not-Ready route-split
fixture. The report now also prints whether the fast-regime theorem premise is
applicable before comparing a window against the `118` fast-regime bound.

The same executable has an opt-in construction profile:

```powershell
lake exe rmq_succinct_classic_cost_harness -- --profile-size N
```

The profile mode runs one deterministic balanced fixture through the current
public `List Int` `SuccinctClassic.buildPayload` / `queryCosted` path and emits
phase markers around `cartesianShape`, `buildPayload`, and each `queryCosted`
call. Use `N = 32768` only as an explicit ready-threshold experiment, not as
part of the default artifact gate. Current profiling evidence shows that
`N = 1024` completes but `N = 2048` is already beyond a five-minute local
review budget on the worker machine, before any `32768` ready-regime fixture is
reasonable. The bottleneck is construction, not the checked model-cost theorem:
the public list-facing path repeatedly rebuilds `Cartesian.shape xs`, whose
reference builder uses `shapeRange`, `scanWindow`, and indexed `List Int`
accesses.

The next executable-strengthening target is therefore an Array-backed
Cartesian-shape builder and a prepared/builder-mirror `SuccinctClassic` path:
prove the Array builder produces the same shape as `Cartesian.shape xs`, then
prove the prepared payload/query mirror agrees with `buildPayload xs` and
`queryCosted xs` while reusing the built shape. That would let a ready-threshold
fixture strengthen reviewer evidence without changing theorem-level
model-cost claims.

The final RMQ roadmap refines the ordering: first lift the strongest final
store/footprint model theorem to the list-facing interface, then clean the
all-size cost surface, then build the runnable Lean validation path. The later
reference-machine and code-generation layers should wait until those public
theorem surfaces are settled.
