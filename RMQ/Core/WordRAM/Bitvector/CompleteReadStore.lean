import RMQ.Core.WordRAM.Bitvector.AllocationLayout
import RMQ.Core.WordRAM.Bitvector.DescriptorReader
import RMQ.Core.WordRAM.Bitvector.SelectSemantics
import RMQ.Core.WordRAM.Bitvector.RankSemantics

/-! # The logical specification of the one shared allocation

These arrays and the read store are proof-side specifications of the allocated
segments. The fixed executable reader receives numerical memory and registers.
Its equality to this specification is a separate physical refinement theorem.
-/

namespace RMQ.PackedBitvector.Allocation

open SuccinctSpace SuccinctRank GenericSelect SuccinctFinal SuccinctFinal.PackedCellProbe

def logicalWords (bits : List Bool) (target : Bool) (segment : Nat) : Array (List Bool) :=
  let d := jacobsonRankData bits
  if segment = 17 then d.superSampleWords target
  else if segment = 18 then d.blockSampleWords target
  else if segment = 19 then d.bitWords.store.words
  else selectedWords bits target segment

def logicalWord (bits : List Bool) (target : Bool) (segment index : Nat) : Option (List Bool) :=
  normalizedSegmentWord target segment ((logicalWords bits target segment)[index]?)

def readStore (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? := logicalWord bits target

theorem readStore_select_agrees (bits : List Bool) (target : Bool) :
    SelectStoreAgrees bits target (readStore bits target) := by
  intro segment index hs
  have h17 : segment ≠ 17 := by omega
  have h18 : segment ≠ 18 := by omega
  have h19 : segment ≠ 19 := by omega
  change normalizedSegmentWord target segment ((logicalWords bits target segment)[index]?) =
    genericLogicalWord bits target segment index
  rw [genericLogicalWord_selected]
  simp only [logicalWords, if_neg h17, if_neg h18, if_neg h19, normalizedSegmentWord]

theorem readStore_rank_agrees (bits : List Bool) (target : Bool) :
    RankStoreAgrees bits target (readStore bits target) := by
  intro segment index hs
  rcases hs with rfl | rfl | rfl | rfl <;>
    simp [readStore, logicalWord, logicalWords, normalizedSegmentWord,
      canonicalRankReadStore, selectedWords_rankTable]

theorem readStore_select_value (bits : List Bool) (target : Bool) (index : Nat) :
    let d := sparseExceptionSelectData bits target
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedSelectCloseRead concreteBPNativeSelectCloseTraceSegmentLayout
      21 22 (readStore bits target) c false (occurrenceCount bits target)
      d.superStride d.wordSize d.localSlotsPerSuper d.localStride d.longFlagBits.length
      d.longFlagRankData.wordSize 1 d.sparseDirectory.flagBits.length
      d.sparseDirectory.rankData.wordSize 1 d.localStride index).value =
        Succinct.select target bits index :=
  selectRead_value_of_agree bits target (readStore bits target)
    (readStore_select_agrees bits target) index

theorem readStore_rank_value (bits : List Bool) (target : Bool) (limit : Nat) :
    let d := jacobsonRankData bits
    let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
    (packedRankRead 17 18 19 21 c target (readStore bits target)
      bits.length d.wordSize d.blocksPerSuper limit).value =
        Succinct.rankPrefix target bits limit :=
  rankRead_value_of_agree bits target (readStore bits target)
    (readStore_rank_agrees bits target) limit

end RMQ.PackedBitvector.Allocation
