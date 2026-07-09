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
wrapper builds the shape with `Cartesian.stackCartesianShape`, stores an
`Array Int` copy of the input for executable consumers, and reuses the prepared
shape through `preparedBuildPayload`, `preparedRouteSplitQueryCost`, and
`preparedQueryCosted`. The central agreement theorems are
`Cartesian.stackCartesianShape_eq_shape`,
`SuccinctClassic.stackCartesianShape_eq_cartesianShape`,
`preparedInput_shape_eq_cartesianShape`,
`preparedBuildPayload_eq_buildPayload`, and
`preparedQueryCosted_eq_queryCosted`, with explicit result and model-cost
corollaries for the prepared query.

Use `N = 32768` only as an explicit ready-threshold experiment, not as part of
the default artifact gate. The stack/right-spine builder is theorem-backed
against the canonical `Cartesian.shape xs` semantics, but this remains runtime
engineering evidence rather than a Lean runtime-complexity theorem or a change
to model-cost claims. Remaining profiling bottlenecks should be reported from
the harness output: after the prepared shape step, payload construction and the
final query path can still dominate larger executable runs. For bottleneck
diagnosis, `--shape-profile-size N` runs only the prepared shape-construction
step and reports the resulting shape metadata.

The final RMQ roadmap refines the ordering: first lift the strongest final
store/footprint model theorem to the list-facing interface, then clean the
all-size cost surface, then build the runnable Lean validation path. The later
reference-machine and code-generation layers should wait until those public
theorem surfaces are settled.
