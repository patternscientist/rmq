import RMQ.Core.SuccinctFinal
import RMQ.Core.Shape

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

/-! # ADVERSARIAL ATTACK on the S verdict for
      builtRelativeSplitBPCloseRankSuperOverhead  (brief's "F4")
      builtRelativeSplitBPCloseRankBlockOverhead  (brief's "F3")

    I do NOT reuse the defender's enumerator, their lemma route, or their
    #eval harness.  Everything below is built from scratch. -/

/-- My own shape constructors: maximally-different same-size shapes. -/
def advLeftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (advLeftSpine n) CartesianShape.empty

def advRightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node CartesianShape.empty (advRightSpine n)

def advBalanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | n + 1 => CartesianShape.node (advBalanced (n / 2)) (advBalanced (n - n / 2))
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.div_le_self n 2)
  · exact Nat.lt_succ_of_le (Nat.sub_le n (n / 2))

/-- Zigzag: alternate which side the spine descends on. -/
def advZigzag : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | 1 => CartesianShape.node CartesianShape.empty CartesianShape.empty
  | n + 2 =>
      CartesianShape.node
        (CartesianShape.node CartesianShape.empty CartesianShape.empty)
        (advZigzag n)

/-- My own exhaustive enumerator (independent of Cartesian.shapesOfSize). -/
def advAllShapes : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
      (List.range (n + 1)).flatMap (fun k =>
        (advAllShapes k).flatMap (fun l =>
          (advAllShapes (n - k)).map (fun r => CartesianShape.node l r)))
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.le_of_lt_succ (List.mem_range.mp (by assumption)))
  · exact Nat.lt_succ_of_le (Nat.sub_le n _)

def advSuper (s : CartesianShape) : Nat :=
  builtRelativeSplitBPCloseRankSuperOverhead s
def advBlock (s : CartesianShape) : Nat :=
  builtRelativeSplitBPCloseRankBlockOverhead s

/-- Closed form claimed by the defender, as a function of n = size ALONE.
    I recompute it here independently from their theorem RHS. -/
def advSuperClosed (n : Nat) : Nat :=
  let m := 2 * n
  let w := SuccinctRank.machineWordBits m
  (m / w / w + 1) * w + (m / w / w + 1) * w

def advBlockClosed (n : Nat) : Nat :=
  let m := 2 * n
  let w := SuccinctRank.machineWordBits m
  let bw := SuccinctRank.machineWordBits (w * w)
  (m / w + 1) * bw + (m / w + 1) * bw

/-! ## ATTACK 1: exhaustive sweep with MY enumerator, sizes 0..9.
    Print (n, #shapes, #distinct super values, #distinct block values,
           closed-form prediction).  Any n with >1 distinct value REFUTES S. -/

def advDedup (l : List Nat) : List Nat :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def advSweep (n : Nat) : Nat × Nat × List Nat × List Nat × (Nat × Nat) :=
  let ss := advAllShapes n
  (n, ss.length,
   advDedup (ss.map advSuper),
   advDedup (ss.map advBlock),
   (advSuperClosed n, advBlockClosed n))

#eval advSweep 0
#eval advSweep 1
#eval advSweep 2
#eval advSweep 3
#eval advSweep 4
#eval advSweep 5
#eval advSweep 6
#eval advSweep 7
#eval advSweep 8
#eval advSweep 9

/-- Anti-vacuity for MY enumerator: sizes really are all n, and the bpCodes
    really are pairwise distinct.  (count, all-sizes-eq-n, #distinct bpCodes) -/
def advAntiVacuity (n : Nat) : Nat × Bool × Nat :=
  let ss := advAllShapes n
  let codes := ss.map CartesianShape.bpCode
  let dedupCodes :=
    codes.foldl (fun acc c => if acc.contains c then acc else acc ++ [c]) []
  (ss.length, ss.all (fun s => s.size == n), dedupCodes.length)

#eval advAntiVacuity 4
#eval advAntiVacuity 5
#eval advAntiVacuity 6
#eval advAntiVacuity 7

/-! ## ATTACK 2: LARGE n, maximally-different shapes.
    If size-only ever breaks it is most likely at a division boundary
    (m / w, m / w / w) where a wordSize change interacts with contents. -/

def advBigRow (n : Nat) : Nat × (Nat × Nat) × (Nat × Nat) × (Nat × Nat) × (Nat × Nat) × Bool :=
  let a := advLeftSpine n
  let b := advRightSpine n
  let c := advBalanced n
  let d := advZigzag n
  let pa := (advSuper a, advBlock a)
  let pb := (advSuper b, advBlock b)
  let pc := (advSuper c, advBlock c)
  let pd := (advSuper d, advBlock d)
  -- last flag: do all four agree with the size-only closed form?
  (n, pa, pb, pc, pd,
   (pa == (advSuperClosed n, advBlockClosed n) &&
    pb == (advSuperClosed n, advBlockClosed n) &&
    pc == (advSuperClosed n, advBlockClosed n) &&
    pd == (advSuperClosed n, advBlockClosed n)))

#eval advBigRow 15
#eval advBigRow 16
#eval advBigRow 17
#eval advBigRow 31
#eval advBigRow 32
#eval advBigRow 33
#eval advBigRow 63
#eval advBigRow 64
#eval advBigRow 65
#eval advBigRow 100
#eval advBigRow 127
#eval advBigRow 128

/-- Sanity: the four big shapes really do differ (bpCode contents differ). -/
#eval (let n := 64
       let cs := [advLeftSpine n, advRightSpine n, advBalanced n, advZigzag n]
       (cs.map (fun s => s.size),
        cs.map (fun s => s.bpCode.length),
        ((cs.map CartesianShape.bpCode).foldl
          (fun acc c => if acc.contains c then acc else acc ++ [c]) []).length))

/-! ## ATTACK 3: the crisp factoring statement, proved MY way.
    "Factors through size" == there exists a function of n alone.
    I avoid the defender's rewrite chain: I go through `bpCode_length`
    generalisation instead. -/

theorem adv_factors_through_size :
    exists f : Nat -> Nat × Nat,
      forall s : CartesianShape, (advSuper s, advBlock s) = f s.size := by
  refine ⟨fun n => (advSuperClosed n, advBlockClosed n), ?_⟩
  intro s
  have hlen : s.bpCode.length = 2 * s.size := CartesianShape.bpCode_length s
  have hsuper : advSuper s = advSuperClosed s.size := by
    unfold advSuper advSuperClosed builtRelativeSplitBPCloseRankSuperOverhead
    rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
      SuccinctRank.canonicalSuperRankEntries_length,
      SuccinctRank.canonicalSuperRankEntries_length]
    simp only [builtRelativeSplitBPCloseRankWordSize,
      builtRelativeSplitBPCloseRankBlocksPerSuper, hlen]
  have hblock : advBlock s = advBlockClosed s.size := by
    unfold advBlock advBlockClosed builtRelativeSplitBPCloseRankBlockOverhead
    rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
      SuccinctRank.canonicalBlockRankEntries_length,
      SuccinctRank.canonicalBlockRankEntries_length]
    simp only [builtRelativeSplitBPCloseRankWordSize,
      builtRelativeSplitBPCloseRankBlocksPerSuper,
      builtRelativeSplitBPCloseRankBlockWidth, hlen]
  rw [hsuper, hblock]

#print axioms adv_factors_through_size
