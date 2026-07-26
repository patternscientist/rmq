import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
QZ-F03 QUANTIFIER ATTACK on the "UNRESOLVED" branch-cone verdict.

The prior agent's cross-shape determinism evidence was n <= 7 only, and they
flagged (correctly) that `canonicalBPRelativeMinMaxArgSummaryTableActive` is
false below n = 512.  This file asks the sharper regime question -- what about
`concreteBPRelativeRmmInteriorReady`, the OTHER guard -- and re-runs the
cross-shape comparison on EXTREME shapes (spines vs balanced vs combs) rather
than on the enumeration order of tiny Catalan shapes.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace QZOffsets

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

/-! ### Nat-only mirrors, so the regime scan is cheap. -/

def baseN (n : Nat) : Nat := Nat.log2 n + 1
def blockSizeRawN (n : Nat) : Nat := 2 * baseN n
def blocksPerSuperRawN (n : Nat) : Nat := baseN n
def blockCountRawN (n : Nat) : Nat := n / baseN n
def superCountRawN (n : Nat) : Nat := blockCountRawN n / blocksPerSuperRawN n + 1
def superWidthN (n : Nat) : Nat := SuccinctRank.machineWordBits (2 * n)
def relativeWidthRawN (n : Nat) : Nat := 2 * (Nat.log2 (baseN n) + 1) + 3

def activeN (n : Nat) : Prop :=
  blockCountRawN n * blockSizeRawN n <= 2 * n /\
    2 * bpSuperblockSpan (blockSizeRawN n) (blocksPerSuperRawN n) <
        2 ^ relativeWidthRawN n /\
    blockSizeRawN n < 2 ^ relativeWidthRawN n /\
    superCountRawN n * superWidthN n <=
      SuccinctSpace.sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots n /\
    3 * (blockCountRawN n * relativeWidthRawN n) <=
      SuccinctSpace.logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots n /\
    relativeWidthRawN n <= SuccinctRank.machineWordBits (2 * n)

instance activeN_decidable (n : Nat) : Decidable (activeN n) := by
  unfold activeN; infer_instance

def blockCountN (n : Nat) : Nat := if activeN n then blockCountRawN n else 0
def macroSizeN (n : Nat) : Nat := baseN n * baseN n
def readyN (n : Nat) : Prop := activeN n /\ macroSizeN n <= blockCountN n

instance readyN_decidable (n : Nat) : Decidable (readyN n) := by
  unfold readyN; infer_instance

/-- Cross-check the mirrors against the real shape-taking predicates. -/
theorem activeN_mirror (s : CartesianShape) :
    canonicalBPRelativeMinMaxArgSummaryTableActive s <-> activeN s.size := by
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive activeN
  show _ <-> _
  rw [show canonicalBPRelativeSummaryBlockSizeRaw s = blockSizeRawN s.size from rfl,
    show canonicalBPRelativeSummaryBlocksPerSuperRaw s = blocksPerSuperRawN s.size from rfl,
    show canonicalBPRelativeSummaryBlockCountRaw s = blockCountRawN s.size from rfl,
    show canonicalBPRelativeSummarySuperCountRaw s = superCountRawN s.size from rfl,
    show canonicalBPRelativeSummaryRelativeWidthRaw s = relativeWidthRawN s.size from rfl,
    show canonicalBPRelativeSummarySuperWidth s
        = SuccinctRank.machineWordBits s.bpCode.length from rfl,
    CartesianShape.bpCode_length]

/-! ### WHERE DO THE TWO REGIME GUARDS FLIP? -/

#eval show IO Unit from do
  let mut actFirst : Option Nat := none
  let mut readyFirst : Option Nat := none
  for n in List.range 40000 do
    if actFirst.isNone && decide (activeN n) then actFirst := some n
    if readyFirst.isNone && decide (readyN n) then readyFirst := some n
  IO.println s!"FLIP ACTIVE first true at n = {actFirst}"
  IO.println s!"FLIP READY  first true at n = {readyFirst}"

#eval show IO Unit from do
  IO.println "n | ACTIVE | READY | macroSize | blockCountRaw"
  for n in [7, 64, 512, 1024, 2048, 4096, 8192, 20000] do
    IO.println s!"{n} | {decide (activeN n)} | {decide (readyN n)} | {macroSizeN n} | {blockCountRawN n}"

/-! ### Extreme-shape families of a common size. -/

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

partial def comb : Nat -> Bool -> CartesianShape
  | 0, _ => CartesianShape.empty
  | Nat.succ n, true => CartesianShape.node (comb n false) CartesianShape.empty
  | Nat.succ n, false => CartesianShape.node CartesianShape.empty (comb n true)

partial def third : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (third (n / 3)) (third (n - n / 3))

def family (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine", leftSpine n)
  , ("rightSpine", rightSpine n)
  , ("balanced", balanced n)
  , ("combT", comb n true)
  , ("combF", comb n false)
  , ("third", third n) ]

/-! ANTI-VACUITY: same size, genuinely different bpCode. -/
#eval show IO Unit from do
  for n in [7, 16, 32, 64] do
    let fam := family n
    let sizes := fam.map (fun p => p.2.size)
    let mut distinct : List (List Bool) := []
    for (_, s) in fam do
      let c := s.bpCode
      if !(distinct.contains c) then distinct := c :: distinct
    IO.println s!"SANITY n={n} sizes={sizes} distinctBPCodes={distinct.length}/{fam.length}"

/-! THE ADDRESS RECORD: equal across extreme shapes of the same size? -/
#eval show IO Unit from do
  for n in [7, 16, 24, 32] do
    let fam := family n
    match fam with
    | [] => pure ()
    | (nm0, s0) :: _ =>
      let o0 := canonicalRelativeRmmInteriorComponentOffsets s0
      let mut diffs : List String := []
      for (nm, s) in fam do
        if canonicalRelativeRmmInteriorComponentOffsets s != o0 then
          diffs := nm :: diffs
      IO.println s!"OFFSETS n={n} ref={nm0} offs={repr o0} differingShapes={diffs}"

end QZOffsets
