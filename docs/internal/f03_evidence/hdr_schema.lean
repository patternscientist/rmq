import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
HEADER-SCHEMA experiment.

Enumerates EVERY candidate header field the route's query-time geometry consumes,
evaluates it on structurally extreme same-size shapes, and reports (a) whether the
field is shape-invariant at equal size (=> S, computable from n, NOT a header field)
and (b) its exact numeric value and bit width (=> width bound for EG-CP-F01).
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace HdrSchema

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

/-- cliff: opens packed then a long run of closes -- maximises superblock spans. -/
def cliff (k m : Nat) : CartesianShape := .node (leftSpine k) (rightSpine m)

def variants (n : Nat) : List (String × CartesianShape) :=
  [ ("L", leftSpine n), ("R", rightSpine n), ("B", balanced n)
  , ("p1", pseudo 1 n), ("p31", pseudo 31 n)
  , ("cliff", cliff (n / 2) (n - n / 2 - 1)) ]

/-- Every geometry scalar the query-time route consumes. -/
def fields (s : CartesianShape) : List (String × Nat) :=
  let o := canonicalRelativeRmmInteriorComponentOffsets s
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
  , ("19 off.baseline",        o.baseline)
  , ("20 off.minRel",          o.minRel)
  , ("21 off.maxRel",          o.maxRel)
  , ("22 off.argOffset",       o.argOffset)
  , ("23 off.localOffset",     o.localOffset)
  , ("24 off.globalBlock",     o.globalBlock)
  , ("25 off.localLevel",      o.localLevel)
  , ("26 off.globalLevel",     o.globalLevel)
  , ("27 off.deadAddress",     o.deadAddress)
  ]

/-- Report, per field: the value on the FIRST variant, and whether all variants agree. -/
def report (n : Nat) : String :=
  let vs := variants n
  let rows := (vs.map (fun p => fields p.2))
  match rows with
  | [] => "no variants"
  | base :: rest =>
      String.intercalate "\n"
        (base.map (fun (nm, v) =>
          let agree := rest.all (fun r =>
            match r.find? (fun q => q.1 = nm) with
            | some q => q.2 = v
            | none => false)
          s!"  {nm} = {v}   agree={agree}"))

def sizesOK (n : Nat) : String :=
  s!"sizes={(variants n).map (fun p => p.2.size)}"

#eval IO.println s!"===== n = 384 (INACTIVE control) =====\n{sizesOK 384}\n{report 384}"
#eval IO.println s!"===== n = 512 (ACTIVE) =====\n{sizesOK 512}\n{report 512}"
#eval IO.println s!"===== n = 1024 (ACTIVE) =====\n{sizesOK 1024}\n{report 1024}"

end HdrSchema
