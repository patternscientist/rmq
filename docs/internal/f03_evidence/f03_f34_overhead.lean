import RMQ.Core.SuccinctFinal
import RMQ.Core.Shape

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

/-! ## F3/F4 experiment: are the two overheads constant across same-size shapes? -/

def f34pair (s : CartesianShape) : Nat × Nat :=
  (builtRelativeSplitBPCloseRankSuperOverhead s,
   builtRelativeSplitBPCloseRankBlockOverhead s)

def dedupPairs : List (Nat × Nat) -> List (Nat × Nat)
  | [] => []
  | p :: rest =>
      let r := dedupPairs rest
      if r.any (fun q => q.1 == p.1 && q.2 == p.2) then r else p :: r

/-- (n, #shapes of size n, DISTINCT (super,block) pairs over ALL shapes of size n) -/
def f34report (n : Nat) : Nat × Nat × List (Nat × Nat) :=
  let shapes := Cartesian.shapesOfSize n
  let pairs := shapes.map f34pair
  (n, shapes.length, dedupPairs pairs)

-- EXHAUSTIVE over every shape of each listed size.
#eval f34report 0
#eval f34report 1
#eval f34report 2
#eval f34report 3
#eval f34report 4
#eval f34report 5
#eval f34report 6
#eval f34report 7
#eval f34report 8

-- Sanity: bpCode CONTENTS really do differ across same-size shapes (anti-vacuity).
#eval ((Cartesian.shapesOfSize 4).map (fun s => s.bpCode)).length
#eval (Cartesian.shapesOfSize 4).map (fun s => s.bpCode.map (fun b => if b then 1 else 0))

/-! ## CHECKED universal statement: both overheads factor through `shape.size`. -/

theorem f3_super_size_only (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankSuperOverhead shape =
      (2 * shape.size /
            SuccinctRank.machineWordBits (2 * shape.size) /
            SuccinctRank.machineWordBits (2 * shape.size) + 1) *
          SuccinctRank.machineWordBits (2 * shape.size) +
        (2 * shape.size /
              SuccinctRank.machineWordBits (2 * shape.size) /
              SuccinctRank.machineWordBits (2 * shape.size) + 1) *
          SuccinctRank.machineWordBits (2 * shape.size) := by
  rw [builtRelativeSplitBPCloseRankSuperOverhead,
    SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    canonicalSuperRankEntries_length, canonicalSuperRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    CartesianShape.bpCode_length]

theorem f4_block_size_only (shape : CartesianShape) :
    builtRelativeSplitBPCloseRankBlockOverhead shape =
      (2 * shape.size /
            SuccinctRank.machineWordBits (2 * shape.size) + 1) *
          SuccinctRank.machineWordBits
            (SuccinctRank.machineWordBits (2 * shape.size) *
              SuccinctRank.machineWordBits (2 * shape.size)) +
        (2 * shape.size /
              SuccinctRank.machineWordBits (2 * shape.size) + 1) *
          SuccinctRank.machineWordBits
            (SuccinctRank.machineWordBits (2 * shape.size) *
              SuccinctRank.machineWordBits (2 * shape.size)) := by
  rw [builtRelativeSplitBPCloseRankBlockOverhead,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    canonicalBlockRankEntries_length, canonicalBlockRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    builtRelativeSplitBPCloseRankBlockWidth,
    CartesianShape.bpCode_length]

/-- Universally quantified over ALL pairs of shapes, not representative rows. -/
theorem f3_f4_same_size_same_value (s t : CartesianShape) (h : s.size = t.size) :
    builtRelativeSplitBPCloseRankSuperOverhead s =
        builtRelativeSplitBPCloseRankSuperOverhead t /\
      builtRelativeSplitBPCloseRankBlockOverhead s =
        builtRelativeSplitBPCloseRankBlockOverhead t := by
  constructor
  · rw [f3_super_size_only, f3_super_size_only, h]
  · rw [f4_block_size_only, f4_block_size_only, h]

/-- On the PUBLIC entry's shape both overheads are functions of `xs.length` = n alone. -/
theorem f3_f4_of_public_entry_are_functions_of_n (xs ys : List Int)
    (h : xs.length = ys.length) :
    builtRelativeSplitBPCloseRankSuperOverhead (Cartesian.shape xs) =
        builtRelativeSplitBPCloseRankSuperOverhead (Cartesian.shape ys) /\
      builtRelativeSplitBPCloseRankBlockOverhead (Cartesian.shape xs) =
        builtRelativeSplitBPCloseRankBlockOverhead (Cartesian.shape ys) := by
  refine f3_f4_same_size_same_value _ _ ?_
  rw [Cartesian.shape_size, Cartesian.shape_size, h]

#print axioms f3_super_size_only
#print axioms f4_block_size_only
#print axioms f3_f4_same_size_same_value
#print axioms f3_f4_of_public_entry_are_functions_of_n
