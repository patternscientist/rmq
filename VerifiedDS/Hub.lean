import RMQHub

/-!
# VerifiedDS hub facade

Neutral import root for the reusable model layer currently exposed by `RMQHub`:
costed computations, RAM/WordRAM traces, representation refinement, table
models, payload accounting, lower bounds, and amortized-analysis scaffolding.

The implementation still lives under the historical `RMQ.Core` namespace while
the spoke APIs settle.
-/
