import RMQ.Core.Window
import RMQ.Core.Succinct
import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.UnionFind

/-!
# Tiny executable examples

These examples are intentionally small. They give downstream readers concrete
terms to build before they inspect the larger theorem aliases.
-/

namespace RMQ.Examples.Concrete

example : RMQ.scanWindow ([5, 2, 7, 1, 3] : List Int) 1 3 = 3 := by
  rfl

example : RMQ.Succinct.rankPrefix true [true, false, true, true] 3 = 2 := by
  rfl

example : RMQ.Succinct.select false [true, false, true, false] 1 = some 3 := by
  rfl

def tinyRMQInput : List Int := [3, 1, 4, 1, 5]

inductive CanonicalQueryRoute where
  | invalid
  | sameBlock
  | crossBlock
deriving Repr, DecidableEq, BEq

/-- Executable inspection of the actual canonical close/LCA branch. -/
def canonicalQueryRoute
    (xs : List Int) (left right : Nat) : CanonicalQueryRoute :=
  if _hvalid : RMQ.ValidRange xs left right then
    let shape := RMQ.SuccinctClassic.cartesianShape xs
    match RMQ.SuccinctSpace.bpCloseOfInorder? shape left,
        RMQ.SuccinctSpace.bpCloseOfInorder? shape (right - 1) with
    | some leftClose, some rightClose =>
        let blockSize :=
          RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
        if RMQ.SuccinctClose.blockOfClose blockSize leftClose =
            RMQ.SuccinctClose.blockOfClose blockSize rightClose then
          .sameBlock
        else
          .crossBlock
    | _, _ => .invalid
  else
    .invalid

/-- Canonical physical store with the first actually consumed word removed. -/
def dropFirstConsumedPhysicalWord
    (xs : List Int) (left right : Nat) : RMQ.WordRAM.ReadStore :=
  let canonical := RMQ.SuccinctClassic.reviewerPhysicalReadStore xs
  let first? :=
    (RMQ.SuccinctClassic.reviewerPhysicalFootprint xs left right).head?
  { readWord? := fun segment address =>
      if segment == 0 && some address == first? then none
      else canonical.readWord? segment address }

/-- Executable positional backing check for every physical read, including
failed reads at the checked dead address. -/
def physicalReadsMatchCanonicalStore
    (xs : List Int) (left right : Nat) : Bool :=
  let result :=
    RMQ.SuccinctClassic.reviewerPhysicalTraceResult xs left right
  let words := RMQ.SuccinctClassic.reviewerPhysicalWords xs
  result.trace.all fun event =>
    match event with
    | RMQ.WordRAM.TraceEvent.readWord segment address word? =>
        segment == 0 && words[address]? == word?
    | _ => true

#guard
  (RMQ.SuccinctClassic.buildPayload tinyRMQInput).length <=
    2 * tinyRMQInput.length +
      RMQ.SuccinctClassic.overhead tinyRMQInput.length

#guard
  RMQ.SuccinctSpace.flattenPayloadWords
      (RMQ.SuccinctClassic.reviewerPhysicalWords tinyRMQInput) ==
    RMQ.SuccinctClassic.buildPayload tinyRMQInput

#guard RMQ.SuccinctClassic.queryCost == 210
#guard RMQ.SuccinctClassic.canonicalSilentSparseLevelQueryCost == 207
#guard RMQ.SuccinctClassic.canonicalSilentWordRankSelectQueryCost == 142
#guard RMQ.SuccinctClassic.canonicalSilentFringeQueryCost == 76

#guard RMQ.SuccinctClassic.canonicalTransitionalQueryCost == 328
#guard RMQ.SuccinctClassic.liveCompatibilityQueryCost == 352

#guard canonicalQueryRoute tinyRMQInput 2 4 == .sameBlock

#guard canonicalQueryRoute tinyRMQInput 0 5 == .crossBlock

#guard canonicalQueryRoute tinyRMQInput 1 1 == .invalid

#guard (RMQ.SuccinctClassic.queryCosted tinyRMQInput 0 5).erase == some 1

#guard (RMQ.SuccinctClassic.queryCosted tinyRMQInput 2 4).erase == some 3

#guard (RMQ.SuccinctClassic.queryCosted ([4, 4, 5] : List Int) 0 2).erase ==
  some 0

#guard (RMQ.SuccinctClassic.queryCosted ([5, 4, 4] : List Int) 0 3).erase ==
  some 1

#guard (RMQ.SuccinctClassic.queryCosted ([8, 6, 7, 6, 9] : List Int) 1 4).erase ==
  some 1

#guard (RMQ.SuccinctClassic.queryCosted ([8, 6, 7, 6, 9] : List Int) 2 5).erase ==
  some 3

#guard (RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 1 1).erase ==
  none

#guard (RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 2 1).erase ==
  none

#guard (RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 0 4).erase ==
  none

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([9, 8, 7] : List Int) 1 1).value == none

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([9, 8, 7] : List Int) 1 1).trace == []

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResult
    ([7] : List Int) 0 1).value == some 0

#guard
  (RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
    ([7] : List Int)
    (dropFirstConsumedPhysicalWord ([7] : List Int) 0 1) 0 1).value == none

#guard physicalReadsMatchCanonicalStore ([7] : List Int) 0 1

/- The one guarded story supplies the same none/empty/zero packet for each
public invalid-range shape, including every caller-supplied physical store. -/
example :
    RMQ.SuccinctClassic.queryTraceResult ([9, 8, 7] : List Int) 1 1 =
        RMQ.WordRAM.TraceResult.pure none /\
      RMQ.SuccinctClassic.reviewerPhysicalTraceResult
          ([9, 8, 7] : List Int) 1 1 = RMQ.WordRAM.TraceResult.pure none /\
      RMQ.SuccinctClassic.queryCosted ([9, 8, 7] : List Int) 1 1 =
        RMQ.Costed.pure none /\
      RMQ.SuccinctClassic.reviewerPhysicalFootprint
          ([9, 8, 7] : List Int) 1 1 = [] /\
      forall store : RMQ.WordRAM.ReadStore,
        RMQ.SuccinctClassic.reviewerPhysicalTraceResultWithStore
            ([9, 8, 7] : List Int) store 1 1 =
          RMQ.WordRAM.TraceResult.pure none := by
  exact RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
    ([9, 8, 7] : List Int) 1 1 (by decide)

example :
    RMQ.SuccinctClassic.reviewerPhysicalTraceResult
        ([9, 8, 7] : List Int) 2 1 =
      RMQ.WordRAM.TraceResult.pure none := by
  exact
    (RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
      ([9, 8, 7] : List Int) 2 1 (by decide)).2.1

example :
    RMQ.SuccinctClassic.reviewerPhysicalFootprint
        ([9, 8, 7] : List Int) 0 4 = [] := by
  exact
    (RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
      ([9, 8, 7] : List Int) 0 4 (by decide)).2.2.2.1

example :
    (RMQ.SuccinctClassic.buildPayload tinyRMQInput).length <=
      2 * tinyRMQInput.length +
        RMQ.SuccinctClassic.overhead tinyRMQInput.length := by
  exact RMQ.SuccinctClassic.buildPayload_length tinyRMQInput

example :
    (RMQ.SuccinctClassic.queryCosted tinyRMQInput 0 5).erase =
      some (RMQ.scanWindow tinyRMQInput 0 5) := by
  simpa using
    (RMQ.SuccinctClassic.queryCosted_exact
      tinyRMQInput (left := 0) (len := 5)
      (by decide) (by decide))

example :
    RMQ.SuccinctClassic.FlatPayloadStoreNoSyntheticExecutionStory
      tinyRMQInput 0 5 := by
  exact
    RMQ.SuccinctClassic.flatPayloadStoreNoSyntheticExecutionStory
      tinyRMQInput 0 5

/- Exact-use consumer: the guarded canonical B7 query contains the identical
cost-33 interior trace, not merely an independently evaluated component. -/
example :
    let shape :=
      RMQ.SuccinctClose.canonicalRelativeRmmInteriorCost33WitnessShape
    let interior :=
      RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
        shape RMQ.SuccinctFinal.concreteBPNativeInteriorTraceSegments 143 146
    ∃ prefixTrace suffixTrace,
      RMQ.SuccinctClassic.queryTraceResult
          RMQ.SuccinctClose.canonicalRelativeRmmInteriorCost33WitnessInput
          1704 3469 =
        RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape 1704 3469 ∧
      (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape 1704 3469).trace =
          prefixTrace ++ interior.trace ++ suffixTrace ∧
      interior.toCosted.cost = 33 ∧
      Not (interior.toCosted.cost <= 30) := by
  have hpublic :=
    RMQ.SuccinctClassic.b7Cost33WholeQuery_reaches_interiorTrace
  unfold RMQ.SuccinctClassic.B7Cost33WholeQueryReachability at hpublic
  rcases hpublic with ⟨hquery, hsource⟩
  unfold RMQ.SuccinctFinal.ConcreteBPNativeB7Cost33WholeQueryReachability
    at hsource
  rcases hsource with
    ⟨_hvalid, _hshape, _hleft, _hright, _hbeforeLength,
      _hpreLeft, _hpreRight, _hprogram, _hlcaEval, _hmiddle,
      _hlcaContains, hwholeContains, hcost, _hlength, hnotLeThirty⟩
  rcases hwholeContains with ⟨prefixTrace, suffixTrace, hcontains⟩
  exact ⟨prefixTrace, suffixTrace, hquery, hcontains, hcost, hnotLeThirty⟩

/- Exact-use consumer: global position `15` comes from instruction position
`1`, at the actual folded state and local position `0`, with its receipt. -/
example :
    ∃ word : RMQ.WordRAM.Word,
      RMQ.SuccinctClassic.queryTraceResult ([7] : List Int) 0 1 =
        RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          (RMQ.Cartesian.shape ([7] : List Int)) 0 1 ∧
      (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1).trace[15]? =
          some (.readWord 1 0 (some word)) ∧
      RMQ.SuccinctFinal.WholeQueryProgram.ProducesEventAt
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1
        (.readWord 1 0 (some word))
        RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram
        RMQ.SuccinctFinal.WholeQueryState.empty 15 1
        (RMQ.SuccinctFinal.WholeQueryInstr.selectClose .rightClose
          (.sub .inputRight (.const 1)))
        (RMQ.SuccinctFinal.WholeQueryProgram.evalGlobalWordTrace
          (RMQ.Cartesian.shape ([7] : List Int)) 0 1
          [RMQ.SuccinctFinal.WholeQueryInstr.selectClose .leftClose .inputLeft]
          RMQ.SuccinctFinal.WholeQueryState.empty).value 0 ∧
      RMQ.SuccinctFinal.ReviewerReadOccurrenceReceipt
        (RMQ.Cartesian.shape ([7] : List Int)) 0 1 15 1 0 (some word) := by
  have hpublic :=
    RMQ.SuccinctClassic.b7Singleton_repeated_read_exact_positions
  unfold RMQ.SuccinctClassic.B7SingletonRepeatedReadExactPositions at hpublic
  rcases hpublic with ⟨hquery, hsource⟩
  unfold
    RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQSingletonRepeatedReadExactPositions
    at hsource
  rcases hsource with
    ⟨word, _hvalid, _hlength, _hinstrNe, _hget0, hget15,
      _hproducer0, hproducer15, _hreceipt0, hreceipt15⟩
  exact ⟨word, hquery, hget15, hproducer15, hreceipt15⟩

def tinyUnionFind : RMQ.UnionFind.State where
  size := 3
  repr := fun x => x
  repr_lt := by
    intro x hx
    exact hx

example : tinyUnionFind.find? 1 = some 1 := by
  simp [tinyUnionFind, RMQ.UnionFind.State.find?]

example : tinyUnionFind.find? 4 = none := by
  simp [tinyUnionFind, RMQ.UnionFind.State.find?]

end RMQ.Examples.Concrete
