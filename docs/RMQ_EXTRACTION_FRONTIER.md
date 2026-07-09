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

The profile mode now runs one deterministic balanced fixture through the
theorem-backed prepared mirror in `SuccinctClassic.PreparedInput`. The prepared
wrapper computes the canonical `cartesianShape` once per fixture, stores an
`Array Int` copy of the input for executable consumers, and reuses the prepared
shape through `preparedBuildPayload`, `preparedRouteSplitQueryCost`, and
`preparedQueryCosted`. The central agreement theorems are
`preparedInput_shape_eq_cartesianShape`,
`preparedBuildPayload_eq_buildPayload`, and
`preparedQueryCosted_eq_queryCosted`, with explicit result and model-cost
corollaries for the prepared query.

Use `N = 32768` only as an explicit ready-threshold experiment, not as part of
the default artifact gate. Current prepared-path profiling evidence shows that
`N = 1024` and `N = 1280` complete locally, while `N = 2048` still exceeded a
15-minute worker timeout. The bottleneck is therefore narrower but still
construction-side: the prepared layer removes repeated shape rebuilding across
payload and query calls, but `prepareInput` intentionally still computes the
canonical `Cartesian.shape xs`, whose reference builder uses `shapeRange`,
`scanWindow`, and indexed `List Int` accesses. A genuinely faster
array/stack-based Cartesian builder remains future work and must be proved
extensionally equal to `Cartesian.shape xs` before the executable harness uses
it.

The final RMQ roadmap refines the ordering: first lift the strongest final
store/footprint model theorem to the list-facing interface, then clean the
all-size cost surface, then build the runnable Lean validation path. The later
reference-machine and code-generation layers should wait until those public
theorem surfaces are settled.
