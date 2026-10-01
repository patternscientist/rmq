# Checked V1 client examples

`RMQExamples.V1Clients` is a downstream proof-maintenance example.  It imports
only `RMQ.Headlines.RMQ` and shows how a client can consume the current named
theorem surfaces without adding aliases or changing the public library.

The packed and earlier paper clients use different models:

| Goal | Checked declaration | Exact model/object chain |
| --- | --- | --- |
| Uniform primitive bound plus valid-query halting and correct packet | `RMQExamples.V1Clients.packedQuery_uniformPrimitiveBound_halts_and_isCorrect` | `RMQ.Headlines.succinctRMQFullyChargedPackedQuery` -> `buildMemory` / fixed `queryProgram` / `run` |
| Returned packed query index is the leftmost minimum | `RMQExamples.V1Clients.packedQuery_returnedIndex_isLeftmost` | The same packed capstone's `queryNat` and `leftmost` field |
| Eventual complete capacity at most `3*n` bits | `RMQExamples.V1Clients.packedQuery_eventuallyCompleteCapacity_le_threeN` | The same packed capstone's `completeCapacity` and `completeResidualLittleO`; the expression includes data, encoded code, scratch registers and control words |
| Earlier paper payload capacity | `RMQExamples.V1Clients.paperQuery_payloadCapacity` | Named `SuccinctClassic.buildPayload_length` -> public `SuccinctClassic.buildPayload` |
| Earlier paper exact answer | `RMQExamples.V1Clients.paperQuery_exact` | Named `SuccinctClassic.queryCosted_exact` -> guarded `SuccinctClassic.queryCosted` -> independent `scanWindow` |
| Earlier paper cost at most `210` | `RMQExamples.V1Clients.paperQuery_cost_le_210` | Named `SuccinctClassic.queryCosted_cost_le`, then `SuccinctClassic.queryCost_eq` |
| Trace-to-costed correspondence | `RMQExamples.V1Clients.paperQuery_trace_toCosted` | Existing definition `queryCosted = queryTraceResult.toCosted` |
| Cost equals guarded trace length | `RMQExamples.V1Clients.paperQuery_cost_eq_trace_length` | Named `WordRAM.TraceResult.toCosted_cost_eq_trace_length` applied to this same `SuccinctClassic.queryTraceResult` |
| Supplied-store result and cost reuse | `RMQExamples.V1Clients.suppliedStore_orderedAgreement_reusesExecution` | `RMQ.Headlines.listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint` gives equality of the exact two guarded executions; value and `toCosted` equality are projections |

The packed primitive result encodes a successful zero-based index as `index + 1`,
reserving packet `0` for rejection. The value-level `queryNat` wrapper decodes
that packet to `some index`. The uniform step bound alone follows from the
fixed fuel; the first client also proves that the same fixed-budget run halts
and returns the correct packet for every valid query. Its halting and answer
conclusions are the substantive completion guarantee.

The module also checks `[4,1,1,3]` on `[0,4)`, where the leftmost minimum is
index `1`.  That example first applies `paperQuery_exact` and reduces only the
small independent `scanWindow` specification.  Empty, reversed, and
out-of-bounds examples use the three public invalid-range theorems.  None of
these examples evaluates the large packed machine, uses `native_decide`, or
treats an implementation result as its own oracle.

The number `210` belongs to the earlier paper query's charged-trace `Costed`
model.  The packed theorem separately bounds actual primitive transitions by
its fixed program budget and accounts for data, encoded code, and scratch in
its complete bit-capacity theorem.  Neither statement measures compiler or
build wall-clock performance, nor preprocessing time.

Build the direct client and its aggregate consumer with:

```powershell
lake build RMQExamples.V1Clients
lake build RMQExamples
```

The durable requirement-to-declaration and verification ledger is
`docs/internal/v1/V1_CLIENT_MATRIX.md`.  This client leaf is input to the V1
integration and independent-audit process; it does not itself accept or release
V1.
