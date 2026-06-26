import RMQ.Core.GenericSelect.DenseEntryTable

/-!
# Generic select dense-word helpers

Aligned payload-word helpers for the dense local two-word select path.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank

structure SelectAlignedBitWords
    (bits : List Bool) (wordSize : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize) :
    Prop where
  get_eq_take_drop :
    forall {i : Nat} {word : List Bool},
      bitWords.store.words[i]? = some word ->
        word = (bits.drop (i * wordSize)).take wordSize
  get_some_of_mul_lt :
    forall {i : Nat},
      i * wordSize < bits.length ->
        exists word, bitWords.store.words[i]? = some word

theorem selectAlignedBitWords_ofChunks
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    SelectAlignedBitWords bits wordSize
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hword) := by
  exact {
    get_eq_take_drop := by
      intro i word hget
      have hchunk :
          (SuccinctSpace.chunkPayloadWords wordSize bits)[i]? =
            some word := by
        simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
          Array.getElem?_toList] using hget
      exact SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
    get_some_of_mul_lt := by
      intro i hi
      have h :=
        SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
          (wordSize := wordSize) hword (payload := bits) (i := i) hi
      cases h with
      | intro word hchunk =>
          exact Exists.intro word (by
            simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
              Array.getElem?_toList] using hchunk) }

def selectDenseLocalFirstStart
    (wordSize baseWordIndex : Nat) : Nat :=
  baseWordIndex * wordSize

def selectDenseLocalSecondStart
    (wordSize baseWordIndex : Nat) : Nat :=
  (baseWordIndex + 1) * wordSize

def selectDenseLocalSpanEnd
    (wordSize baseWordIndex : Nat) : Nat :=
  (baseWordIndex + 2) * wordSize

def selectDenseLocalFirstWord
    (bits : List Bool) (wordSize baseWordIndex : Nat) : List Bool :=
  (bits.drop (selectDenseLocalFirstStart wordSize baseWordIndex)).take
    wordSize

def selectDenseLocalFirstCount
    (target : Bool) (bits : List Bool)
    (wordSize baseWordIndex firstOffset : Nat) : Nat :=
  RMQ.RAM.boolRankPrefix target
      (selectDenseLocalFirstWord bits wordSize baseWordIndex)
      (selectDenseLocalFirstWord bits wordSize baseWordIndex).length -
    RMQ.RAM.boolRankPrefix target
      (selectDenseLocalFirstWord bits wordSize baseWordIndex)
      firstOffset

def sparseDenseSelectDenseLocalEntryBasePosition
    (wordSize : Nat)
    (entry : SparseDenseSelectDenseLocalEntry) : Nat :=
  entry.baseWordIndex * wordSize + entry.firstOffset

end RMQ.GenericSelect
