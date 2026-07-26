import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack, stage 2: the LARGE-n regime the other agent never entered.
`canonicalBPRelativeMinMaxArgSummaryTableActive` is claimed to flip on at
n = 512, and `concreteBPRelativeRmmInteriorReadyThreshold = 2^15`.  If the
size-only story is going to break, it breaks where the ite guards are live.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctSpace

namespace AdvSZHuge

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

partial def randShape (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let s := (seed * 1103515245 + 12345) % 2147483648
      let k := s % (n + 1)
      CartesianShape.node (randShape (s / 7 + 1) k) (randShape (s / 11 + 3) (n - k))

partial def comb (n : Nat) : CartesianShape :=
  match n with
  | 0 => CartesianShape.empty
  | Nat.succ m => CartesianShape.node (balanced (m / 3)) (rightSpine (m - m / 3))

def familyOf (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine", leftSpine n)
  , ("rightSpine", rightSpine n)
  , ("balanced", balanced n)
  , ("comb", comb n)
  , ("rand1", randShape 1 n)
  , ("rand2", randShape 7 n)
  , ("rand3", randShape 99 n)
  ]

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

def control (s : CartesianShape) : List (String × Nat) :=
  [ ("CTRL bpExcessAt(n)", bpExcessAt s s.size)
  , ("CTRL bpExcessAt(7)", bpExcessAt s 7)
  ]

def runSize (n : Nat) : IO Unit := do
  let fam := familyOf n
  let sizes := fam.map (fun p => p.2.size)
  if (sizes.filter (fun k => k != n)) != [] then
    IO.println s!"n={n} *** FAMILY SIZE MISMATCH {sizes} ***"
  else
    let brows := fam.map (fun p => battery p.2)
    let crows := fam.map (fun p => control p.2)
    match brows, crows with
    | [], _ => pure ()
    | _, [] => pure ()
    | b0 :: _, c0 :: _ =>
      let mut diffs : List String := []
      for k in b0.map (fun q => q.1) do
        let vals := brows.map (fun r => (r.lookup k).getD 0)
        let dv := vals.foldl (fun acc v => if acc.contains v then acc else v :: acc) []
        if dv.length > 1 then diffs := s!"{k}::{dv.reverse}" :: diffs
      let mut cdiffs : List String := []
      for k in c0.map (fun q => q.1) do
        let vals := crows.map (fun r => (r.lookup k).getD 0)
        let dv := vals.foldl (fun acc v => if acc.contains v then acc else v :: acc) []
        cdiffs := s!"{k}:{dv.length}" :: cdiffs
      let distinctCodes :=
        (fam.map (fun p => p.2.bpCode)).foldl
          (fun acc c => if acc.contains c then acc else c :: acc) []
      IO.println s!"n={n} members={fam.length} distinctBpCodes={distinctCodes.length} ACTIVE={(b0.lookup "ACTIVE").getD 0} READY={(b0.lookup "READY").getD 0} blockSize={(b0.lookup "blockSize").getD 0} SDIFFS={diffs.reverse} CTRLdistinct={cdiffs.reverse}"

#eval show IO Unit from do
  for n in [400, 500, 511, 512, 513, 600, 700, 1000, 1024, 1025, 2000, 2048] do
    runSize n

end AdvSZHuge
