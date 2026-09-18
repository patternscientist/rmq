import RMQ.Core.WordRAM.Bitvector.RegularLayout
open RMQ.PackedBitvector RMQ.PackedBitvector.Experiment RMQ.GenericSelect
example {words : Array (List Bool)} (h : RegularWords words) (i : Nat) :
    words[i]? = if i < words.size then
      some (((segmentBits words).drop (i * firstLength words)).take (firstLength words))
      else none := h.getElem?_eq i
example {words : Array (List Bool)} (h : RegularWords words)
    (i : Nat) (hi : i < words.size) :
    words[i].length = min (firstLength words)
      ((segmentBits words).length - i * firstLength words) := h.length_eq i hi
example {words : Array (List Bool)} (h : RegularWords words)
    (i : Nat) (hi : i < words.size) :
    words[i] = ((segmentBits words).drop (i * firstLength words)).take
      (min (firstLength words) ((segmentBits words).length - i * firstLength words)) :=
  h.min_slice_eq i hi
example (bits : List Bool) :
    let df := sparseExceptionSelectData bits false
    let dt := sparseExceptionSelectData bits true
    let c := RMQ.SuccinctClose.bpFringeChunkBits (2 * bits.length)
    forall words, words ∈ [df.bitWords.store.words] ++
      directorySegments df ++ directorySegments dt ++
      [(RMQ.SuccinctClose.bpFringeChunkTable c).store.words,
       (RMQ.SuccinctClose.bpChunkSelectTable c false).store.words] -> RegularWords words :=
  canonical_allSegments_regular bits
example (bits : List Bool) (words : Array (List Bool)) (i : Nat) (hi : i < words.size)
    (hmem : words ∈ [(sparseExceptionSelectData bits false).bitWords.store.words] ++
      directorySegments (sparseExceptionSelectData bits false) ++
      directorySegments (sparseExceptionSelectData bits true) ++
      [(RMQ.SuccinctClose.bpFringeChunkTable
        (RMQ.SuccinctClose.bpFringeChunkBits (2 * bits.length))).store.words,
       (RMQ.SuccinctClose.bpChunkSelectTable
        (RMQ.SuccinctClose.bpFringeChunkBits (2 * bits.length)) false).store.words]) :
    words[i] = ((segmentBits words).drop (i * firstLength words)).take
      (min (firstLength words) ((segmentBits words).length - i * firstLength words)) :=
  (canonical_allSegments_regular bits words hmem).min_slice_eq i hi
example : ¬ RegularWords #[[], [true]] := irregular_empty_head_rejected
example : RegularWords (RMQ.SuccinctSpace.BoundedPayloadWordStore.ofChunks
    [true, false, true] (by decide : 0 < 2)).store.words := regularWords_ofChunks _ _
example : RegularWords (RMQ.SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel
    [] (by decide : 0 < 8)).store.words := regularWords_ofChunksWithSentinel _ _
#print axioms RMQ.PackedBitvector.RegularWords.getElem?_eq
#print axioms RMQ.PackedBitvector.RegularWords.length_eq
#print axioms RMQ.PackedBitvector.RegularWords.min_slice_eq
#print axioms RMQ.PackedBitvector.regularWords_of_slices
#print axioms RMQ.PackedBitvector.regularWords_of_uniform
#print axioms RMQ.PackedBitvector.regularWords_fixedWidthTable
#print axioms RMQ.PackedBitvector.regularWords_chunks_with_empty_tail
#print axioms RMQ.PackedBitvector.regularWords_ofChunks
#print axioms RMQ.PackedBitvector.regularWords_ofChunksWithSentinel
#print axioms RMQ.PackedBitvector.directorySegments_regular
#print axioms RMQ.PackedBitvector.canonical_bitWords_regular
#print axioms RMQ.PackedBitvector.canonical_directorySegments_regular
#print axioms RMQ.PackedBitvector.canonical_allSegments_regular
#print axioms RMQ.PackedBitvector.irregular_empty_head_rejected