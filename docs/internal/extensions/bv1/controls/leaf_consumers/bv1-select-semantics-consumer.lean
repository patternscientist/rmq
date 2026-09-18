import RMQ.Core.WordRAM.Bitvector.SelectSemantics
open RMQ RMQ.PackedBitvector RMQ.GenericSelect RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedCellProbe
example (bits : List Bool) (target : Bool) :
  (sparseExceptionSelectData bits target).bitWords.store.words =
    (sparseExceptionSelectData bits false).bitWords.store.words :=
  canonical_bitWords_target_eq bits target
example (bits : List Bool) (target : Bool) :
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  0 < c ∧ d.wordSize ≤ 8 * c ∧ d.longFlagRankData.wordSize ≤ 8 * c ∧
    d.sparseDirectory.rankData.wordSize ≤ 8 * c :=
  canonical_select_chunk_geometry bits target
example (bits : List Bool) (target : Bool) (idx : Nat) :
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
    21 22 (genericReadStore bits target) c false (occurrenceCount bits target)
    d.superStride d.wordSize d.localSlotsPerSuper d.localStride d.longFlagBits.length
    d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
    d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
    Succinct.select target bits idx := canonicalSelectRead_value bits target idx
example (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore)
  (hagree : ∀ segment index, segment < 17 ∨ segment = 21 ∨ segment = 22 →
    store.readWord? segment index = (genericReadStore bits target).readWord? segment index)
  (idx : Nat) :
  let d := sparseExceptionSelectData bits target
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
    21 22 store c false (occurrenceCount bits target)
    d.superStride d.wordSize d.localSlotsPerSuper d.localStride d.longFlagBits.length
    d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
    d.sparseDirectory.rankData.wordSize 1 d.localStride idx).value =
    Succinct.select target bits idx := selectRead_value_of_agree bits target store hagree idx
example : (canonicalSelectRead [true] true 0).value = some 0 := by
  rw [canonicalSelectRead_value]
  rfl
example : (canonicalSelectRead [true] true 1).value = none := by
  rw [canonicalSelectRead_value]
  rfl
example : ¬ (∀ (bits : List Bool) (target : Bool) (idx : Nat),
  (WordRAM.TraceResult.pure (none : Option Nat)).value = Succinct.select target bits idx) :=
  constant_none_select_rejected
#print axioms canonical_bitWords_target_eq
#print axioms canonical_select_chunk_geometry
#print axioms normalized_dense_value
#print axioms selectRead_value_eq_of_agree
#print axioms selectRead_value_of_agree
#print axioms canonicalSelectRead_value_eq
#print axioms canonicalSelectRead_value
#print axioms constant_none_select_rejected
