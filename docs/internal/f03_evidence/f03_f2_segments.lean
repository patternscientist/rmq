import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 / F2 supplement: the CARDINALITIES of the three segments that carry F2's
contents (17 = super samples, 18 = block samples, 19 = packed BP words).
Not consumed by the current query path (addressing is by an abstract
`(segment, index)` pair with literal segment constants), but they become
address offsets under the packed target, so they must be size-only too.
-/

namespace F03F2Seg

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian
open RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData

/-- A fixed-width table stores exactly one word per entry. -/
theorem fwnt_words_size {entries : List Nat} {width : Nat}
    (t : SuccinctSpace.FixedWidthNatTable entries width) :
    t.store.words.size = entries.length := by
  have key : forall i : Nat,
      t.store.words[i]? = none <-> entries[i]? = none := by
    intro i
    have h := t.read_exact i
    constructor
    · intro hw
      rw [hw] at h
      simpa using h.symm
    · intro he
      rw [he] at h
      cases hw : t.store.words[i]? with
      | none => rfl
      | some w => rw [hw] at h; simp at h
  have h1 : entries[t.store.words.size]? = none := (key _).mp (by simp)
  have h2 : t.store.words[entries.length]? = none := (key _).mpr (by simp)
  have g1 : entries.length <= t.store.words.size := by
    simpa using List.getElem?_eq_none_iff.mp h1
  have g2 : t.store.words.size <= entries.length := by
    simpa using Array.getElem?_eq_none_iff.mp h2
  omega

-- ### Executed check: equal size => equal segment cardinalities

def E : CartesianShape := .empty
def N (l r : CartesianShape) : CartesianShape := .node l r

def size3 : List CartesianShape :=
  [ N (N (N E E) E) E, N (N E (N E E)) E, N (N E E) (N E E),
    N E (N (N E E) E), N E (N E (N E E)) ]

def size5 : List CartesianShape :=
  [ N (N (N (N (N E E) E) E) E) E,
    N (N (N E E) E) (N E E),
    N (N E E) (N (N E E) (N E E)),
    N E (N E (N E (N E (N E E)))) ]

def counts (s : CartesianShape) : Nat × Nat × Nat :=
  let d := builtRelativeSplitBPCloseRankData s
  ((d.superSampleWords false).size,
   (d.blockSampleWords false).size,
   d.bitWords.store.words.size)

def geom (s : CartesianShape) : Nat × Nat × Nat × Nat :=
  let d := builtRelativeSplitBPCloseRankData s
  (d.wordSize, d.blocksPerSuper, d.superWidth, d.blockWidth)

-- segment 17/18/19 word counts, all five shapes of size 3
#eval size3.map CartesianShape.size
#eval size3.map counts
#eval (size3.map counts).eraseDups.length
#eval size3.map geom

-- four structurally distinct shapes of size 5
#eval size5.map CartesianShape.size
#eval size5.map counts
#eval (size5.map counts).eraseDups.length
#eval size5.map geom

-- counts are NOT constant across sizes
#eval counts (N (N (N E E) E) E) == counts (N (N (N (N (N E E) E) E) E) E)

end F03F2Seg
