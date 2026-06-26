import RMQ.Core.SuccinctSelect.CloseSelect.SparseExceptionCloseData

/-!
# Finite-block-table false-select obstruction

Split implementation layer for the select-side close-select proposal.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal

/-!
### Concrete charged replacement surface

The older rectangular relative-split record and generated rectangular entry
rows were pruned after the compact sparse-exception path superseded them. The
surface below remains as the checked full-width two-level
obstruction/replacement checkpoint for the finite-block-table route.
It consumes concrete two-level stored-word select tables built from
`shape.bpCode`; no close-select function or branch exactness theorem is
supplied externally.
-/

def builtTwoLevelFalseSelectWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits shape.bpCode.length

def builtTwoLevelFalseSelectOccurrencesPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtTwoLevelFalseSelectWordSize shape

theorem builtTwoLevelFalseSelectWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtTwoLevelFalseSelectWordSize shape := by
  simp [builtTwoLevelFalseSelectWordSize,
    SuccinctRankProposal.machineWordBits_pos]

theorem builtTwoLevelFalseSelectOccurrencesPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtTwoLevelFalseSelectOccurrencesPerSuper shape := by
  simpa [builtTwoLevelFalseSelectOccurrencesPerSuper] using
    builtTwoLevelFalseSelectWordSize_pos shape

theorem builtTwoLevelFalseSelect_bpCode_length_lt_word_pow
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      2 ^ builtTwoLevelFalseSelectWordSize shape := by
  simpa [builtTwoLevelFalseSelectWordSize,
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self (n := shape.bpCode.length))

def builtTwoLevelFalseSelectSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (canonicalSelectSuperTablesFinite
      shape.bpCode
      (builtTwoLevelFalseSelectWordSize shape)
      (builtTwoLevelFalseSelectOccurrencesPerSuper shape)
      (builtTwoLevelFalseSelectWordSize shape)
      (builtTwoLevelFalseSelect_bpCode_length_lt_word_pow
        shape)).payload.length

def builtTwoLevelFalseSelectBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (canonicalSelectBlockTablesFinite
      shape.bpCode
      (builtTwoLevelFalseSelectWordSize shape)
      (builtTwoLevelFalseSelectOccurrencesPerSuper shape)
      (builtTwoLevelFalseSelectWordSize shape)
      (builtTwoLevelFalseSelect_bpCode_length_lt_word_pow
        shape)).payload.length

theorem builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length + 1 <=
      builtTwoLevelFalseSelectBlockOverhead shape := by
  exact
    canonicalSelectBlockTablesFinite_payload_length_ge_succ
      (bits := shape.bpCode)
      (wordSize := builtTwoLevelFalseSelectWordSize shape)
      (occurrencesPerSuper :=
        builtTwoLevelFalseSelectOccurrencesPerSuper shape)
      (fieldWidth := builtTwoLevelFalseSelectWordSize shape)
      (builtTwoLevelFalseSelect_bpCode_length_lt_word_pow shape)

def builtTwoLevelFalseSelectSelectData
    (shape : Cartesian.CartesianShape) :
    TwoLevelPayloadLiveStoredWordSelectData shape.bpCode
      (builtTwoLevelFalseSelectSuperOverhead shape)
      (builtTwoLevelFalseSelectBlockOverhead shape)
      sparseDenseFalseSelectQueryCost :=
  canonicalTwoLevelSelectDataOfChunksExact
    shape.bpCode
    (builtTwoLevelFalseSelectWordSize_pos shape)
    (by
      simp [builtTwoLevelFalseSelectWordSize])
    (builtTwoLevelFalseSelectOccurrencesPerSuper_pos shape)
    (builtTwoLevelFalseSelect_bpCode_length_lt_word_pow shape)
    (builtTwoLevelFalseSelect_bpCode_length_lt_word_pow shape)
    (by
      unfold sparseDenseFalseSelectQueryCost
      omega)

/--
Concrete finite-block-table two-level stored-word false-select close accessor.

This is intentionally retained as the checked full-width obstruction route:
the data are executable and exact, but the finite block table payload is proven
too large for the final `o(n)` select witness.
-/
structure TwoLevelFalseSelectCloseData
    (shape : Cartesian.CartesianShape)
    (superOverhead blockOverhead queryCost : Nat) where
  selectData :
    TwoLevelPayloadLiveStoredWordSelectData
      shape.bpCode superOverhead blockOverhead queryCost

namespace TwoLevelFalseSelectCloseData

def payload
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) : List Bool :=
  data.selectData.auxPayload

def locatorReadWords
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) : List (List Bool) :=
  (((data.selectData.superTables.trueTable.store.words.toList ++
      data.selectData.superTables.falseTable.store.words.toList) ++
    data.selectData.blockTables.trueTable.store.words.toList) ++
      data.selectData.blockTables.falseTable.store.words.toList)

def readWords
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) : List (List Bool) :=
  data.locatorReadWords ++ data.selectData.bitWords.store.words.toList

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    (idx : Nat) : Costed (Option Nat) :=
  data.selectData.selectCosted false idx

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) :
    data.payload.length = superOverhead + blockOverhead := by
  exact data.selectData.auxPayload_length

theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    (idx : Nat) :
    (data.selectCloseCosted idx).cost <= queryCost := by
  exact data.selectData.selectCosted_cost_le false idx

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    (idx : Nat) :
    (data.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  calc
    (data.selectCloseCosted idx).erase =
        RMQ.Succinct.select false shape.bpCode idx := by
      exact data.selectData.selectCosted_exact false idx
    _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
      exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?
        shape idx

theorem payload_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    {word : List Bool}
    (hmem :
      List.Mem word data.selectData.bitWords.store.words.toList) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact data.selectData.payload_word_length_le_machine hmem

theorem profile
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) :
    data.payload.length = superOverhead + blockOverhead /\
      (forall idx, (data.selectCloseCosted idx).cost <= queryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word data.selectData.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    ⟨data.payload_length, data.selectCloseCosted_cost_le,
      data.selectCloseCosted_exact,
      fun {word} hmem => data.payload_word_length_le_machine hmem⟩

end TwoLevelFalseSelectCloseData

def builtTwoLevelFalseSelectCloseData
    (shape : Cartesian.CartesianShape) :
    TwoLevelFalseSelectCloseData shape
      (builtTwoLevelFalseSelectSuperOverhead shape)
      (builtTwoLevelFalseSelectBlockOverhead shape)
      sparseDenseFalseSelectQueryCost where
  selectData := builtTwoLevelFalseSelectSelectData shape

theorem builtTwoLevelFalseSelectCloseData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtTwoLevelFalseSelectCloseData shape
    data.payload.length =
        builtTwoLevelFalseSelectSuperOverhead shape +
          builtTwoLevelFalseSelectBlockOverhead shape /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word
            data.selectData.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact (builtTwoLevelFalseSelectCloseData shape).profile

def builtTwoLevelFalseSelectRightSpineBlockOverhead (n : Nat) : Nat :=
  builtTwoLevelFalseSelectBlockOverhead (falseSelectRightSpine n)

theorem builtTwoLevelFalseSelectRightSpineBlockOverhead_ge_two_n_plus_one
    (n : Nat) :
    2 * n + 1 <=
      builtTwoLevelFalseSelectRightSpineBlockOverhead n := by
  let shape := falseSelectRightSpine n
  have hshape : Cartesian.ShapeOfSize n shape :=
    falseSelectRightSpine_shapeOfSize n
  have hbp : shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshape
  have hblock := builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ
    shape
  simpa [builtTwoLevelFalseSelectRightSpineBlockOverhead, shape, hbp] using
    hblock

theorem builtTwoLevelFalseSelect_current_finite_block_tables_not_littleO :
    Not
      (SuccinctSpace.LittleOLinear
        builtTwoLevelFalseSelectRightSpineBlockOverhead) := by
  apply not_littleOLinear_of_self_le
  intro n
  have hlinear :
      n <= 2 * n + 1 := by
    omega
  exact Nat.le_trans hlinear
    (builtTwoLevelFalseSelectRightSpineBlockOverhead_ge_two_n_plus_one n)


end SuccinctSelectProposal
end RMQ
