import RMQ.Core.WordRAM.Bitvector.AllocationFacts
open RMQ.PackedBitvector RMQ.PackedBitvector.Experiment RMQ.GenericSelect
example {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    ((directorySegments d).flatMap segmentBits).length +
      d.longFlagRankData.superTables.falseTable.payload.length +
      d.longFlagRankData.blockTables.falseTable.payload.length +
      d.sparseDirectory.rankData.superTables.falseTable.payload.length +
      d.sparseDirectory.rankData.blockTables.falseTable.payload.length =
      d.payload.length :=
  (directoryAllocationFacts d).1
example {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    ((directorySegments d).flatMap segmentBits).length <= d.payload.length :=
  (directoryAllocationFacts d).2.1
example {bits : List Bool} {target : Bool} {rs rb : Nat}
    (d : SparseExceptionSelectData bits target rs rb) :
    ((directorySegments d).flatMap segmentBits).length <=
      canonicalSparseExceptionSelectOverhead bits.length :=
  (directoryAllocationFacts d).2.2
example (bits : List Bool) (target : Bool) :
    ((directorySegments (sparseExceptionSelectData bits target)).flatMap segmentBits).length <=
      canonicalSparseExceptionSelectOverhead bits.length :=
  directorySegments_length_le_canonical (sparseExceptionSelectData bits target)
example {bits : List Bool} {rfs rfb rts rtb : Nat}
    (df : SparseExceptionSelectData bits false rfs rfb)
    (dt : SparseExceptionSelectData bits true rts rtb) :
    ((directorySegments df ++ directorySegments dt).flatMap segmentBits).length <=
      canonicalSparseExceptionSelectOverhead bits.length +
        canonicalSparseExceptionSelectOverhead bits.length :=
  directorySegments_both_length_le df dt
#print axioms RMQ.PackedBitvector.segmentBits_payload
#print axioms RMQ.PackedBitvector.directorySegments_bits_eq
#print axioms RMQ.PackedBitvector.directorySegments_length_add_omitted
#print axioms RMQ.PackedBitvector.directorySegments_length_le_payload
#print axioms RMQ.PackedBitvector.directorySegments_length_le_canonical
#print axioms RMQ.PackedBitvector.directorySegments_both_length_le
#print axioms RMQ.PackedBitvector.directorySegments_positive_extra_breaks_exact_count
#print axioms RMQ.PackedBitvector.directoryAllocationFacts