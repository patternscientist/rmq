import RMQ.Core.RankSelectSpec

/-!
# Compressed/FID rank-select specification surface

This module adds the fixed-weight bitvector counting layer and the public
compressed rank/select theorem shape.  It is deliberately a spec/profile layer:
the concrete enumerative codec that realizes the `fixedWeightPayloadBudget`
will live below this interface.
-/

namespace RMQ

namespace RankSelectSpec

/--
Mathlib-free binomial-count recurrence.

`binomialCount n k` counts the number of length-`n` bitvectors with exactly
`k` true bits.  It intentionally avoids depending on `Nat.choose`, which is not
part of the repository's Lean/Std footprint.
-/
def binomialCount : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => binomialCount n 0
  | n + 1, k + 1 => binomialCount n (k + 1) + binomialCount n k

/-- Bitvectors of length `n` with exactly `k` true bits. -/
def fixedWeightBitstrings : Nat -> Nat -> List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 =>
      (fixedWeightBitstrings n 0).map fun bits => false :: bits
  | n + 1, k + 1 =>
      ((fixedWeightBitstrings n (k + 1)).map fun bits => false :: bits) ++
        ((fixedWeightBitstrings n k).map fun bits => true :: bits)

theorem fixedWeightBitstrings_length
    (n k : Nat) :
    (fixedWeightBitstrings n k).length = binomialCount n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [fixedWeightBitstrings, binomialCount]
  | succ n ih =>
      cases k with
      | zero =>
          simp [fixedWeightBitstrings, binomialCount, ih]
      | succ k =>
          simp [fixedWeightBitstrings, binomialCount, ih, Nat.add_comm]

/-- Number of true bits in a bitvector. -/
def trueCount (bits : List Bool) : Nat :=
  Succinct.rankPrefix true bits bits.length

@[simp] theorem trueCount_nil : trueCount [] = 0 := by
  rfl

@[simp] theorem trueCount_cons_false (bits : List Bool) :
    trueCount (false :: bits) = trueCount bits := by
  simp [trueCount, Succinct.rankPrefix]

@[simp] theorem trueCount_cons_true (bits : List Bool) :
    trueCount (true :: bits) = trueCount bits + 1 := by
  simp [trueCount, Succinct.rankPrefix, Nat.add_comm]

theorem fixedWeightBitstrings_mem_length_trueCount
    {bits : List Bool} {n k : Nat}
    (hmem : List.Mem bits (fixedWeightBitstrings n k)) :
    bits.length = n /\ trueCount bits = k := by
  induction n generalizing bits k with
  | zero =>
      cases k with
      | zero =>
          cases hmem with
          | head =>
              simp
          | tail _ htail =>
              cases htail
      | succ k =>
          cases hmem
  | succ n ih =>
      cases k with
      | zero =>
          rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
          have htailFacts := ih htail
          simp [htailFacts.1, htailFacts.2]
      | succ k =>
          rcases List.mem_append.mp hmem with hmem | hmem
          · rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
            have htailFacts := ih htail
            simp [htailFacts.1, htailFacts.2]
          · rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
            have htailFacts := ih htail
            simp [htailFacts.1, htailFacts.2]

theorem fixedWeightBitstrings_mem_of_length_trueCount
    {bits : List Bool} {n k : Nat}
    (hlen : bits.length = n) (hcount : trueCount bits = k) :
    List.Mem bits (fixedWeightBitstrings n k) := by
  induction n generalizing bits k with
  | zero =>
      cases bits with
      | nil =>
          cases k with
          | zero =>
              exact List.Mem.head []
          | succ k =>
              simp at hcount
      | cons bit rest =>
          simp at hlen
  | succ n ih =>
      cases bits with
      | nil =>
          simp at hlen
      | cons bit rest =>
          have hrestLen : rest.length = n := by
            simp at hlen
            exact hlen
          cases bit
          case false =>
            cases k with
            | zero =>
                exact
                  List.mem_map.mpr
                    ⟨rest, ih hrestLen (by simpa using hcount), rfl⟩
            | succ k =>
                exact
                  List.mem_append.mpr
                    (Or.inl
                      (List.mem_map.mpr
                        ⟨rest, ih hrestLen (by simpa using hcount), rfl⟩))
          case true =>
            cases k with
            | zero =>
                simp at hcount
            | succ k =>
                have htailCount : trueCount rest = k := by
                  simpa using hcount
                exact
                  List.mem_append.mpr
                    (Or.inr
                      (List.mem_map.mpr
                        ⟨rest, ih hrestLen htailCount, rfl⟩))

theorem fixedWeightBitstrings_mem_iff
    {bits : List Bool} {n k : Nat} :
    List.Mem bits (fixedWeightBitstrings n k) <->
      bits.length = n /\ trueCount bits = k := by
  constructor
  · exact fixedWeightBitstrings_mem_length_trueCount
  · intro h
    exact fixedWeightBitstrings_mem_of_length_trueCount h.1 h.2

/--
The information-theoretic fixed-weight payload budget used by the compressed
rank/select profile.  The `+ 1` is the usual whole-number ceiling slack for a
binary code over `binomialCount n m` states.
-/
def fixedWeightPayloadBudget (bits : List Bool) : Nat :=
  Nat.log2 (binomialCount bits.length (trueCount bits)) + 1

/--
Compressed rank/select directory profile for one bitvector.

Unlike `BitVectorRankSelectDirectory`, this surface does not charge the raw
`bits.length` stored-bit prefix.  Its payload is bounded by the fixed-weight
universe budget plus `overhead bits.length` auxiliary bits.
-/
structure CompressedBitVectorRankSelectDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  payload : List Bool
  payload_length_le :
    payload.length <= fixedWeightPayloadBudget bits + overhead
  accessCosted : Nat -> Costed (Option Bool)
  rankCosted : Bool -> Nat -> Costed Nat
  selectCosted : Bool -> Nat -> Costed (Option Nat)
  access_cost_le : forall i, (accessCosted i).cost <= queryCost
  rank_cost_le :
    forall target pos, (rankCosted target pos).cost <= queryCost
  select_cost_le :
    forall target occurrence,
      (selectCosted target occurrence).cost <= queryCost
  access_exact : forall i, (accessCosted i).erase = bits[i]?
  rank_exact :
    forall target pos,
      (rankCosted target pos).erase =
        Succinct.rankPrefix target bits pos
  select_exact :
    forall target occurrence,
      (selectCosted target occurrence).erase =
        Succinct.select target bits occurrence

namespace CompressedBitVectorRankSelectDirectory

def accessQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (i : Nat) : Costed (Option Bool) :=
  directory.accessCosted i

def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankCosted target pos

def selectQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  directory.selectCosted target occurrence

theorem profile
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost) :
    directory.payload.length <=
        fixedWeightPayloadBudget bits + overhead /\
      (forall i,
        (directory.accessQueryCosted i).cost <= queryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= queryCost /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <= queryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact directory.payload_length_le
  · constructor
    · intro i
      exact ⟨directory.access_cost_le i, directory.access_exact i⟩
    · constructor
      · intro target pos
        exact
          ⟨directory.rank_cost_le target pos,
            directory.rank_exact target pos⟩
      · intro target occurrence
        exact
          ⟨directory.select_cost_le target occurrence,
            directory.select_exact target occurrence⟩

end CompressedBitVectorRankSelectDirectory

/--
Family-level compressed/FID rank-select theorem surface.

The target profile is
`log2 (binomialCount n m) + 1 + o(n)` payload bits, where
`m = trueCount bits`, and constant modeled `access`, `rank`, and `select`.
-/
structure CompressedBitVectorRankSelectFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall bits : List Bool,
      CompressedBitVectorRankSelectDirectory
        bits (overhead bits.length) queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace CompressedBitVectorRankSelectFamily

theorem fixed_weight_constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : CompressedBitVectorRankSelectFamily overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            ((family.directory bits).accessQueryCosted i).cost <=
                queryCost /\
              ((family.directory bits).accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              ((family.directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((family.directory bits).selectQueryCosted
                target occurrence).cost <= queryCost /\
              ((family.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact (family.directory bits).profile

end CompressedBitVectorRankSelectFamily

end RankSelectSpec

end RMQ
