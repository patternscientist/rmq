import RMQ.Core.WordRAM.Packed.QueryObservations
import RMQ.Core.WordRAM.Packed.ArrayRun

/-! Semantic call-site traces and exact physical occurrence correspondence for
the canonical query. Stage names are assigned at actual reference calls. -/

namespace RMQ.SuccinctFinal.PackedNative.Witnesses

open PackedWordRAM Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

inductive Stage where
  | selectLeft | selectRight
  | sameFringeSeed | sameFringeWindow
  | leftFringeSeed | leftFringeWindow | interior
  | rightFringeSeed | rightFringeWindow | finalRank
deriving Repr, DecidableEq, BEq

def Stage.name : Stage → String
  | .selectLeft => "select-left"
  | .selectRight => "select-right"
  | .sameFringeSeed => "same-fringe-seed"
  | .sameFringeWindow => "same-fringe-window"
  | .leftFringeSeed => "left-fringe-seed"
  | .leftFringeWindow => "left-fringe-window"
  | .interior => "interior"
  | .rightFringeSeed => "right-fringe-seed"
  | .rightFringeWindow => "right-fringe-window"
  | .finalRank => "final-rank"

structure StageTrace where
  stage : Stage
  trace : List WordRAM.TraceEvent
deriving Repr, DecidableEq

def flatten (stages : List StageTrace) : List WordRAM.TraceEvent := stages.flatMap (·.trace)

@[simp] theorem flatten_nil : flatten [] = [] := rfl

@[simp] theorem flatten_cons (stage : StageTrace) (stages : List StageTrace) :
    flatten (stage :: stages) = stage.trace ++ flatten stages := rfl

@[simp] theorem flatten_append (a b : List StageTrace) :
    flatten (a ++ b) = flatten a ++ flatten b := List.flatMap_append

def fringeStages (seedStage windowStage : Stage) (store : WordRAM.ReadStore)
    (n close start span : Nat) : List StageTrace :=
  let seed := packedLocalBPSeed n (packedRankCloseLeaf store n) (packedInteriorLayout n).blockSize close
  [⟨seedStage, seed.trace⟩,
   ⟨windowStage, (fringeWindowReference store n close start span seed.value).trace⟩]

theorem fringeStages_trace (seedStage windowStage : Stage) (store : WordRAM.ReadStore)
    (n close start span : Nat) :
    flatten (fringeStages seedStage windowStage store n close start span) =
      (fringeReference store n close start span).trace := by
  simp [fringeStages, fringeReference, WordRAM.TraceResult.bind]

def lcaStages (store : WordRAM.ReadStore) (n left right : Nat) : List StageTrace :=
  let b := (packedInteriorLayout n).blockSize
  let leftBlock := left / b
  let rightBlock := right / b
  if leftBlock = rightBlock then
    fringeStages .sameFringeSeed .sameFringeWindow store n left (left + 1) (right - left + 1)
  else
    fringeStages .leftFringeSeed .leftFringeWindow store n left (left + 1)
        (leftBlock * b + b - left) ++
      [⟨.interior, (lcaMiddleReference store n leftBlock rightBlock).trace⟩] ++
      fringeStages .rightFringeSeed .rightFringeWindow store n right (rightBlock * b)
        (right - rightBlock * b + 2)

theorem lcaStages_trace (store : WordRAM.ReadStore) (n left right : Nat) :
    flatten (lcaStages store n left right) = (packedLcaCloseLeaf store n left right).trace := by
  have hc : (lcaCandidateReference store n left right).trace =
      (packedLcaCloseLeaf store n left right).trace := by
    simpa only [WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure, List.append_nil] using
      congrArg (fun result => result.trace) (lcaCandidateReference_close store n left right)
  rw [← hc]
  by_cases he : left / (packedInteriorLayout n).blockSize = right / (packedInteriorLayout n).blockSize
  · simp [lcaStages, lcaCandidateReference, he, fringeStages_trace]
  · simp [lcaStages, lcaCandidateReference, he, fringeStages_trace,
      lcaCrossCandidateReference, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, List.append_assoc]

def afterSelectStages (store : WordRAM.ReadStore) (n : Nat) :
    Option Nat → Option Nat → List StageTrace
  | some left, some right =>
      lcaStages store n left right ++
        match (packedLcaCloseLeaf store n left right).value with
        | some close => [⟨.finalRank, (packedRankCloseLeaf store n (close + 1)).trace⟩]
        | none => []
  | _, _ => []

theorem afterSelectStages_trace (store : WordRAM.ReadStore) (n : Nat)
    (left right : Option Nat) :
    flatten (afterSelectStages store n left right) =
      (queryAfterSelectsReference store n left right).trace := by
  cases left with
  | none => cases right <;> rfl
  | some left =>
      cases right with
      | none => rfl
      | some right =>
          cases hc : (packedLcaCloseLeaf store n left right).value <;>
            simp [afterSelectStages, queryAfterSelectsReference, queryAfterLCAReference,
              hc, lcaStages_trace, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
              WordRAM.TraceResult.pure]

def queryStages (store : WordRAM.ReadStore) (n left right : Nat) : List StageTrace :=
  let first := packedSelectCloseLeaf store n left
  let second := packedSelectCloseLeaf store n (right - 1)
  [⟨.selectLeft, first.trace⟩, ⟨.selectRight, second.trace⟩] ++
    afterSelectStages store n first.value second.value

theorem queryStages_trace (store : WordRAM.ReadStore) (n left right : Nat) :
    flatten (queryStages store n left right) = (packedWholeQueryRun store n left right).trace := by
  rw [← queryReadyReference_eq_packedWholeQueryRun]
  simp [queryStages, afterSelectStages_trace, queryReadyReference,
    WordRAM.TraceResult.bind, List.append_assoc]

def stages (xs : List Int) (left right : Nat) : List StageTrace :=
  if ValidRange xs left right then
    let shape := SuccinctClassic.cartesianShape xs
    queryStages (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size left right
  else []

theorem stages_trace (xs : List Int) (left right : Nat) :
    flatten (stages xs left right) = (SuccinctClassic.queryTraceResult xs left right).trace := by
  by_cases hv : ValidRange xs left right
  · simp only [stages, if_pos hv, queryStages_trace]
    exact congrArg (fun result => result.trace) (packedReviewerPackedReference_eq_public xs left right hv)
  · rw [stages, if_neg hv, SuccinctClassic.queryTraceResult_invalid xs left right hv]
    rfl

theorem stages_readOnly (xs : List Int) (left right : Nat) :
    ReadOnlyTrace (flatten (stages xs left right)) := by
  rw [stages_trace]
  exact queryTraceResult_readOnly xs left right

theorem stages_reads (xs : List Int) (left right : Nat) :
    (queryRun (buildMemory xs) xs.length left right).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          (stages xs left right).flatMap (fun stage =>
            logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs) stage.trace)
      else [] := by
  rw [queryRun_reference_reads, ← stages_trace]
  by_cases hv : ValidRange xs left right
  · simp [hv, flatten, logicalTraceReads, List.flatMap_assoc]
  · simp [hv]

theorem staged_occurrence_reads (xs : List Int) (left right : Nat) (hv : ValidRange xs left right)
    (prior after : List WordRAM.TraceEvent) (segment index : Nat) (word : Option WordRAM.Word)
    (hs : flatten (stages xs left right) = prior ++ .readWord segment index word :: after) :
    (queryRun (buildMemory xs) xs.length left right).reads =
      (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
        (logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs) prior ++
          (readerReceipts (SuccinctClassic.cartesianShape xs) (buildMemory xs) segment index ++
            logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs) after)) := by
  rw [queryRun_reference_reads, if_pos hv, ← stages_trace, hs]
  simp [logicalTraceReads, List.flatMap_append, List.append_assoc]

/-- The offset counts occurrences, including earlier repetitions and the exact
174-entry metadata prefix. It is not an address-based membership lookup. -/
theorem staged_receipt_at (xs : List Int) (left right : Nat) (hv : ValidRange xs left right)
    (prior after : List WordRAM.TraceEvent) (segment index : Nat) (word : Option WordRAM.Word)
    (hs : flatten (stages xs left right) = prior ++ .readWord segment index word :: after)
    (offset : Nat) (receipt : Receipt)
    (hr : (readerReceipts (SuccinctClassic.cartesianShape xs) (buildMemory xs) segment index)[offset]? =
      some receipt) :
    (queryRun (buildMemory xs) xs.length left right).reads[
      174 + (logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs) prior).length + offset]? =
        some receipt := by
  rw [staged_occurrence_reads xs left right hv prior after segment index word hs]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_map, List.length_range, Nat.add_assoc, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_right (Nat.le_add_right ..)]
  simp only [Nat.add_sub_cancel_left]
  obtain ⟨hb, _⟩ := List.getElem?_eq_some_iff.1 hr
  rw [List.getElem?_append_left hb]
  exact hr

/-- The exported occurrence is an actual transition, retaining its exact prefix.
No stage classifier replaces these execution and address/value facts. -/
theorem occurrence_source (xs : List Int) (left right index : Nat)
    (transition : Transition) (receipt : Receipt)
    (ht : (queryRun (buildMemory xs) xs.length left right).transitions[index]? = some transition)
    (hr : transition.receipt = some receipt) :
    transition.before = (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final ∧
      transition.before.status = .running ∧ queryProgram[transition.before.pc]? = some transition.instruction ∧
      execute (buildMemory xs) transition.instruction transition.before = (transition.after, transition.receipt) ∧
      ∃ dst addrReg, transition.instruction = .load dst addrReg ∧
        receipt.address = transition.before.regs addrReg ∧
        receipt.reply = (buildMemory xs)[receipt.address]? := queryRun_read_at xs left right index transition receipt ht hr

theorem arrayRun_exact (xs : List Int) (left right : Nat) :
    runArray (buildMemory xs) queryProgram.toArray queryBudget (initialState xs.length left right) =
      queryRun (buildMemory xs) xs.length left right := runArray_toArray _ _ _ _

#print axioms stages_trace
#print axioms stages_reads
#print axioms staged_receipt_at
#print axioms occurrence_source
#print axioms arrayRun_exact

end RMQ.SuccinctFinal.PackedNative.Witnesses
