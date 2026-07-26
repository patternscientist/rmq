import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! HEADER-SCHEMA part A: the cheap scalar geometry fields, swept wide. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace HdrA

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def cliff (n : Nat) : CartesianShape :=
  .node (leftSpine (n / 2)) (rightSpine (n - n / 2 - 1))

def variants (n : Nat) : List (String × CartesianShape) :=
  [ ("L", leftSpine n), ("R", rightSpine n), ("B", balanced n)
  , ("p1", pseudo 1 n), ("p31", pseudo 31 n), ("cliff", cliff n) ]

def fields (s : CartesianShape) : List (String × Nat) :=
  [ ("00 size",                s.size)
  , ("01 bpLen",               s.bpCode.length)
  , ("02 summaryBase",         canonicalBPRelativeSummaryBase s)
  , ("03 summaryBlockSizeRaw", canonicalBPRelativeSummaryBlockSizeRaw s)
  , ("04 blocksPerSuperRaw",   canonicalBPRelativeSummaryBlocksPerSuperRaw s)
  , ("05 blockCountRaw",       canonicalBPRelativeSummaryBlockCountRaw s)
  , ("06 superCountRaw",       canonicalBPRelativeSummarySuperCountRaw s)
  , ("07 summarySuperWidth",   canonicalBPRelativeSummarySuperWidth s)
  , ("08 relativeWidthRaw",    canonicalBPRelativeSummaryRelativeWidthRaw s)
  , ("09 active?",             if canonicalBPRelativeMinMaxArgSummaryTableActive s then 1 else 0)
  , ("10 summaryBlockSize",    canonicalBPRelativeSummaryBlockSize s)
  , ("11 blocksPerSuper",      canonicalBPRelativeSummaryBlocksPerSuper s)
  , ("12 blockCount",          canonicalBPRelativeSummaryBlockCount s)
  , ("13 rankWordSize",        builtRelativeSplitBPCloseRankWordSize s)
  , ("14 rankBlocksPerSuper",  builtRelativeSplitBPCloseRankBlocksPerSuper s)
  , ("15 rankBlockWidth",      builtRelativeSplitBPCloseRankBlockWidth s)
  , ("16 rankSuperOverhead",   builtRelativeSplitBPCloseRankSuperOverhead s)
  , ("17 rankBlockOverhead",   builtRelativeSplitBPCloseRankBlockOverhead s)
  , ("18 fringeChunkBits",     bpFringeChunkBits s.bpCode.length)
  ]

def report (n : Nat) : String :=
  match (variants n).map (fun p => fields p.2) with
  | [] => "none"
  | base :: rest =>
      String.intercalate "\n"
        (base.map (fun (nm, v) =>
          let agree := rest.all (fun r =>
            match r.find? (fun q => q.1 = nm) with
            | some q => q.2 = v | none => false)
          s!"  {nm} = {v}  agree={agree}"))

#eval IO.println s!"== n=384 (inactive control) ==\n{report 384}"
#eval IO.println s!"== n=512 (ACTIVE) ==\n{report 512}"
#eval IO.println s!"== n=1024 (ACTIVE) ==\n{report 1024}"
#eval IO.println s!"== n=2048 (ACTIVE) ==\n{report 2048}"

end HdrA
