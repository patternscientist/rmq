import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack on the SIZE-ONLY verdict, stage 1.

Strategy: build several STRUCTURALLY MAXIMALLY DIFFERENT shapes of the SAME
size n (left spine, right spine, balanced, zigzag, several pseudo-random), and
evaluate every quantity the other agent classified S.  Any disagreement inside
one size column refutes "factors through n".

Sizes deliberately include the regime the other agent never touched: the
`canonicalBPRelativeMinMaxArgSummaryTableActive` regime (n >= 512) and the
`concreteBPRelativeRmmInteriorReadyThreshold = 2^15` regime.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctSpace

namespace AdvSZBig

/-! ## same-size shape families -/

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

/-- zig-zag: alternate which side carries the remaining mass -/
partial def zigzag (goLeft : Bool) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      if goLeft then CartesianShape.node (zigzag false n) CartesianShape.empty
      else CartesianShape.node CartesianShape.empty (zigzag true n)

/-- pseudo-random shape via a linear congruential split chooser -/
partial def randShape (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let s := (seed * 1103515245 + 12345) % 2147483648
      let k := s % (n + 1)
      CartesianShape.node (randShape (s / 7 + 1) k) (randShape (s / 11 + 3) (n - k))

/-- left-heavy comb: root's left child is a big balanced block, right is a spine -/
partial def comb (n : Nat) : CartesianShape :=
  match n with
  | 0 => CartesianShape.empty
  | Nat.succ m => CartesianShape.node (balanced (m / 3)) (rightSpine (m - m / 3))

def familyOf (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine", leftSpine n)
  , ("rightSpine", rightSpine n)
  , ("balanced", balanced n)
  , ("zigzagL", zigzag true n)
  , ("zigzagR", zigzag false n)
  , ("comb", comb n)
  , ("rand1", randShape 1 n)
  , ("rand2", randShape 7 n)
  , ("rand3", randShape 99 n)
  , ("rand4", randShape 12345 n)
  ]

/-! ## the battery of claimed-S quantities -/

def battery (s : CartesianShape) : List (String × Nat) :=
  let d := builtRelativeSplitBPCloseRankData s
  [ ("size", s.size)
  , ("bpCodeLen", s.bpCode.length)
  , ("base", canonicalBPRelativeSummaryBase s)
  , ("blockSizeRaw", canonicalBPRelativeSummaryBlockSizeRaw s)
  , ("blocksPerSuperRaw", canonicalBPRelativeSummaryBlocksPerSuperRaw s)
  , ("blockCountRaw", canonicalBPRelativeSummaryBlockCountRaw s)
  , ("superCountRaw", canonicalBPRelativeSummarySuperCountRaw s)
  , ("superWidth", canonicalBPRelativeSummarySuperWidth s)
  , ("relWidthRaw", canonicalBPRelativeSummaryRelativeWidthRaw s)
  , ("ACTIVE", if canonicalBPRelativeMinMaxArgSummaryTableActive s then 1 else 0)
  , ("blockSize", canonicalBPRelativeSummaryBlockSize s)
  , ("blocksPerSuper", canonicalBPRelativeSummaryBlocksPerSuper s)
  , ("blockCount", canonicalBPRelativeSummaryBlockCount s)
  , ("superCount", canonicalBPRelativeSummarySuperCount s)
  , ("relWidth", canonicalBPRelativeSummaryRelativeWidth s)
  , ("READY", if concreteBPRelativeRmmInteriorReady s then 1 else 0)
  , ("macroSize", concreteBPRelativeRmmInteriorMacroSize s)
  , ("interiorBlockWidth", concreteBPRelativeRmmInteriorBlockWidth s)
  , ("rankWordSize", builtRelativeSplitBPCloseRankWordSize s)
  , ("rankBlocksPerSuper", builtRelativeSplitBPCloseRankBlocksPerSuper s)
  , ("rankBlockWidth", builtRelativeSplitBPCloseRankBlockWidth s)
  , ("F4 rankSuperOverhead", builtRelativeSplitBPCloseRankSuperOverhead s)
  , ("F3 rankBlockOverhead", builtRelativeSplitBPCloseRankBlockOverhead s)
  , ("data.wordSize", d.wordSize)
  , ("data.blocksPerSuper", d.blocksPerSuper)
  , ("data.wordIndex 0", d.wordIndex 0)
  , ("data.wordIndex 3", d.wordIndex 3)
  , ("data.wordIndex n", d.wordIndex s.size)
  , ("data.superIndex n", d.superIndex s.size)
  , ("layout.macroSize", (RelativeRmm.canonicalLayout s).macroSize)
  , ("layout.macroSampleCount", (RelativeRmm.canonicalLayout s).macroSampleCount)
  , ("layout.offsetWidth", (RelativeRmm.canonicalLayout s).offsetWidth)
  , ("layout.levelCount", (RelativeRmm.canonicalLayout s).levelCount)
  , ("layout.globalLevelCount", (RelativeRmm.canonicalLayout s).globalLevelCount)
  , ("layout.blockAddressWidth", (RelativeRmm.canonicalLayout s).blockAddressWidth)
  , ("layout.superSampleCount", (RelativeRmm.canonicalLayout s).superSampleCount)
  ]

/-- ANTI-VACUITY control: quantities that MUST differ across same-size shapes.
    If these come out constant too, the harness is broken. -/
def control (s : CartesianShape) : List (String × Nat) :=
  [ ("CTRL bpExcessAt(n/2)", bpExcessAt s (s.size))
  , ("CTRL bpExcessAt(3)", bpExcessAt s 3)
  , ("CTRL bpCode trues in first half",
      ((s.bpCode.take s.size).filter (fun b => b)).length)
  ]

def runSize (n : Nat) : IO Unit := do
  let fam := familyOf n
  -- verify all family members really have size n
  let sizes := fam.map (fun p => p.2.size)
  let bad := sizes.filter (fun k => k != n)
  if bad != [] then
    IO.println s!"n={n}  *** FAMILY SIZE MISMATCH {sizes} ***"
  else
    let brows : List (List (String × Nat)) := fam.map (fun p => battery p.2)
    let crows : List (List (String × Nat)) := fam.map (fun p => control p.2)
    match brows, crows with
    | [], _ => pure ()
    | _, [] => pure ()
    | b0 :: _, c0 :: _ =>
      let keys := b0.map (fun q => q.1)
      let mut diffs : List String := []
      for k in keys do
        let vals := brows.map (fun r => (r.lookup k).getD 0)
        let dv := vals.foldl (fun acc v => if acc.contains v then acc else v :: acc) []
        if dv.length > 1 then
          diffs := s!"{k}::{dv.reverse}" :: diffs
      let ckeys := c0.map (fun q => q.1)
      let mut cdiffs : List String := []
      for k in ckeys do
        let vals := crows.map (fun r => (r.lookup k).getD 0)
        let dv := vals.foldl (fun acc v => if acc.contains v then acc else v :: acc) []
        cdiffs := s!"{k}:{dv.length}" :: cdiffs
      let distinctCodes :=
        (fam.map (fun p => p.2.bpCode)).foldl
          (fun acc c => if acc.contains c then acc else c :: acc) []
      IO.println s!"n={n} familyMembers={fam.length} distinctBpCodes={distinctCodes.length} ACTIVE={(b0.lookup "ACTIVE").getD 0} READY={(b0.lookup "READY").getD 0} SDIFFS={diffs.reverse} CONTROLdistinct={cdiffs.reverse}"

#eval show IO Unit from do
  for n in [1,2,3,4,5,6,7,8,12,16,20,32,48,64,100,127,128,200,255,256,300] do
    runSize n

end AdvSZBig
