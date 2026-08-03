import RMQ.Core.SuccinctFinal.RAM.GeometryClosure
import RMQ.Core.SuccinctFinal.RAM.SourceInventory

open RMQ
open RMQ.SuccinctFinal

/-! Adversarial all-size instantiation of the three theorems the f02-scope lane
leans on.  The lane wrote no Lean; these instantiate its load-bearing citations
at n = 0 and n = 1 to check for a hidden positivity or validity hypothesis. -/

-- 1. GeometryClosure.lean:1429 -- the factorisation, at the empty and singleton
--    input.  No hypothesis of any kind is discharged here.
theorem av_factors_at_zero (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctClassic.queryTraceResultWithStore ([] : List Int) store l r =
      GeometryClosure.publicQueryOfLength 0 store l r :=
  GeometryClosure.queryTraceResultWithStore_factors [] store l r

theorem av_factors_at_one (x : Int) (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctClassic.queryTraceResultWithStore [x] store l r =
      GeometryClosure.publicQueryOfLength 1 store l r :=
  GeometryClosure.queryTraceResultWithStore_factors [x] store l r

-- 2. `publicQueryOfLength` mentions no shape and no list argument other than
--    the canonical `List.replicate n 0` witness: the representative at a given
--    `n` is literally independent of the two inputs above.
theorem av_zero_one_share_no_content (x y : Int)
    (store : WordRAM.ReadStore) (l r : Nat) :
    SuccinctClassic.queryTraceResultWithStore [x] store l r =
      SuccinctClassic.queryTraceResultWithStore [y] store l r := by
  rw [GeometryClosure.queryTraceResultWithStore_factors [x] store l r,
    GeometryClosure.queryTraceResultWithStore_factors [y] store l r]
  simp

-- 3. SourceInventory.lean:469 -- no header segment is readable, at every size
--    including 0 and 1, under EVERY supplied store.  Segment 23 stands for a
--    hypothetical header segment appended past the inventory.
theorem av_no_header_segment_read_at_any_size
    (xs : List Int) (store : WordRAM.ReadStore) (left right index : Nat)
    (word? : Option WordRAM.Word) :
    WordRAM.TraceEvent.readWord 23 index word? ∉
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape xs) store left right).trace := by
  refine SourceInventory.unlistedSegment_never_read _ store left right ?_ index word?
  simp [SourceInventory.mem_reviewerInventorySegments_iff]

-- 4. Same statement specialised to the empty and singleton input, to make the
--    small-size coverage explicit rather than implied.
theorem av_no_header_segment_read_at_zero
    (store : WordRAM.ReadStore) (left right index : Nat)
    (word? : Option WordRAM.Word) :
    WordRAM.TraceEvent.readWord 23 index word? ∉
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape ([] : List Int)) store left right).trace :=
  av_no_header_segment_read_at_any_size [] store left right index word?

theorem av_no_header_segment_read_at_one (x : Int)
    (store : WordRAM.ReadStore) (left right index : Nat)
    (word? : Option WordRAM.Word) :
    WordRAM.TraceEvent.readWord 23 index word? ∉
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (Cartesian.shape [x]) store left right).trace :=
  av_no_header_segment_read_at_any_size [x] store left right index word?

#print axioms av_factors_at_zero
#print axioms av_factors_at_one
#print axioms av_zero_one_share_no_content
#print axioms av_no_header_segment_read_at_any_size
#print axioms av_no_header_segment_read_at_zero
#print axioms av_no_header_segment_read_at_one
