import RMQ.Headlines.RMQ

/-!
# Checked V1 downstream clients

These examples deliberately keep the two public query models separate.  The
packed client talks about primitive execution and complete numeric-memory
capacity.  The earlier paper client talks about the charged `TraceResult` /
`Costed` model and the public succinct bit payload.  Neither model is a claim
about Lean execution time.
-/

namespace RMQExamples.V1Clients

open RMQ
open RMQ.SuccinctFinal.PackedWordRAM

/-! ## Fully charged packed-query client -/

/-- One budget bounds every primitive run, and every valid query both halts and
returns the independently specified leftmost scan result. -/
theorem packedQuery_uniformPrimitiveBound_halts_and_isCorrect :
    ∃ budget : Nat, ∀ (xs : List Int) left right,
      (run (buildMemory xs) queryProgram queryBudget
        (initialState xs.length left right)).steps ≤ budget ∧
      (ValidRange xs left right →
        (∃ packet,
          (run (buildMemory xs) queryProgram queryBudget
            (initialState xs.length left right)).final.status = .halted packet) ∧
        (run (buildMemory xs) queryProgram queryBudget
          (initialState xs.length left right)).result =
            some (scanWindow xs left (right - left) + 1)) := by
  let contract := RMQ.Headlines.succinctRMQFullyChargedPackedQuery
  refine ⟨queryBudget, ?_⟩
  intro xs left right
  refine ⟨contract.stepBound xs left right, ?_⟩
  intro hvalid
  have hinputs := contract.validInputs xs left right hvalid
  exact
    ⟨⟨_, contract.halt xs left right hinputs.2.1 hinputs.2.2⟩,
      contract.specResult xs left right hvalid⟩

/-- The zero-based index returned by the packed value-level query satisfies the
leftmost-tie RMQ specification. -/
theorem packedQuery_returnedIndex_isLeftmost
    (xs : List Int) (left right index : Nat)
    (hanswer : queryNat (buildMemory xs) xs.length left right = some index) :
    LeftmostArgMin xs left right index :=
  RMQ.Headlines.succinctRMQFullyChargedPackedQuery.leftmost
    xs left right index hanswer

/-- Eventually the complete packed allocation -- data, encoded fixed program,
and scratch registers and control words -- occupies at most `3 * n` bits. -/
theorem packedQuery_eventuallyCompleteCapacity_le_threeN :
    ∃ threshold : Nat, ∀ xs : List Int, threshold ≤ xs.length →
      ((buildMemory xs).length +
          (queryProgram.map Instruction.encoding).flatten.length +
          (queryRegisterCount + 3)) * wordWidth xs.length ≤
        3 * xs.length := by
  let contract := RMQ.Headlines.succinctRMQFullyChargedPackedQuery
  obtain ⟨threshold, hresidual⟩ := contract.completeResidualLittleO 1 (by decide)
  refine ⟨threshold, ?_⟩
  intro xs hlarge
  have hrho : queryCompleteRho xs.length ≤ xs.length := by
    simpa using hresidual xs.length hlarge
  have hcapacity := contract.completeCapacity xs
  omega

/-! ## Earlier paper-model client -/

/-- The public bit payload has the advertised `2*n + overhead n` capacity. -/
theorem paperQuery_payloadCapacity (xs : List Int) :
    (RMQ.SuccinctClassic.buildPayload xs).length ≤
      2 * xs.length + RMQ.SuccinctClassic.overhead xs.length :=
  RMQ.SuccinctClassic.buildPayload_length xs

/-- A valid half-open query in the earlier paper model returns the independent
`scanWindow` specification. -/
theorem paperQuery_exact
    (xs : List Int) {left len : Nat}
    (hlen : 0 < len) (hbound : left + len ≤ xs.length) :
    (RMQ.SuccinctClassic.queryCosted xs left (left + len)).erase =
      some (scanWindow xs left len) :=
  RMQ.SuccinctClassic.queryCosted_exact xs hlen hbound

/-- The earlier paper query's own charged-trace cost is at most `210`. -/
theorem paperQuery_cost_le_210
    (xs : List Int) (left right : Nat) :
    (RMQ.SuccinctClassic.queryCosted xs left right).cost ≤ 210 := by
  have hcost := RMQ.SuccinctClassic.queryCosted_cost_le xs left right
  calc
    (RMQ.SuccinctClassic.queryCosted xs left right).cost ≤
        RMQ.SuccinctClassic.queryCost := hcost
    _ = 210 := RMQ.Headlines.succinctRMQQueryCostEq

/-- `queryCosted` is exactly the costed projection of the guarded public trace,
so its modeled cost counts that trace rather than packed primitive steps. -/
theorem paperQuery_trace_toCosted
    (xs : List Int) (left right : Nat) :
    (RMQ.SuccinctClassic.queryTraceResult xs left right).toCosted =
      RMQ.SuccinctClassic.queryCosted xs left right :=
  rfl

/-! ## Supplied-store theorem reuse -/

/-- Agreement on the first execution's ordered read footprint determines the
entire guarded supplied-store execution, hence also its answer and modeled
cost.  No query result is reproved here. -/
theorem suppliedStore_orderedAgreement_reusesExecution
    (xs : List Int) (storeA storeB : RMQ.WordRAM.ReadStore)
    (left right : Nat)
    (hagree :
      RMQ.SuccinctClassic.storesAgreeOnOrderedReadFootprint
        xs storeA storeB left right) :
    RMQ.SuccinctClassic.queryTraceResultWithStore xs storeA left right =
        RMQ.SuccinctClassic.queryTraceResultWithStore xs storeB left right ∧
      (RMQ.SuccinctClassic.queryTraceResultWithStore
          xs storeA left right).value =
        (RMQ.SuccinctClassic.queryTraceResultWithStore
          xs storeB left right).value ∧
      (RMQ.SuccinctClassic.queryTraceResultWithStore
          xs storeA left right).toCosted =
        (RMQ.SuccinctClassic.queryTraceResultWithStore
          xs storeB left right).toCosted := by
  have htrace :=
    RMQ.Headlines.listIntSuccinctRMQQueryTraceResultWithStoreEqOfOrderedReadFootprint
      xs storeA storeB left right hagree
  exact
    ⟨htrace, congrArg (fun result => result.value) htrace,
      congrArg (fun result => result.toCosted) htrace⟩

/-! ## Small specification-backed examples -/

example :
    (RMQ.SuccinctClassic.queryCosted
      ([4, 1, 1, 3] : List Int) 0 4).erase = some 1 := by
  have hexact :=
    paperQuery_exact ([4, 1, 1, 3] : List Int)
      (left := 0) (len := 4) (by decide) (by decide)
  simpa [scanWindow, betterIndex] using hexact

example :
    (RMQ.SuccinctClassic.queryCosted
      ([4, 1, 1, 3] : List Int) 2 2).erase = none :=
  RMQ.Headlines.listIntSuccinctRMQQueryCostedEmptyRange
    ([4, 1, 1, 3] : List Int) 2

example :
    (RMQ.SuccinctClassic.queryCosted
      ([4, 1, 1, 3] : List Int) 3 1).erase = none :=
  RMQ.Headlines.listIntSuccinctRMQQueryCostedReversedRange
    ([4, 1, 1, 3] : List Int) (by decide)

example :
    (RMQ.SuccinctClassic.queryCosted
      ([4, 1, 1, 3] : List Int) 0 5).erase = none :=
  RMQ.Headlines.listIntSuccinctRMQQueryCostedOutOfBounds
    ([4, 1, 1, 3] : List Int) (by decide)

end RMQExamples.V1Clients
