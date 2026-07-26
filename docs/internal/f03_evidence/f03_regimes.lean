import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Regime map for the F03 empirical evidence.

Any cross-shape experiment is only as good as the regimes it exercises. This
file evaluates the route's geometry and branch predicates as functions of shape
size, on structurally EXTREME same-size shapes, so we can say exactly (a) where
each regime turns on and (b) whether any of these geometry values differs
between two shapes of equal size -- which is the F03 question itself, asked one
function at a time instead of through the whole query.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace F03Reg

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

def variants (n : Nat) : List (String × CartesianShape) :=
  [ ("L", leftSpine n), ("R", rightSpine n), ("B", balanced n)
  , ("p1", pseudo 1 n), ("p7", pseudo 7 n) ]

/-- Every geometry value we can name, as a Nat, for one shape. -/
def geom (s : CartesianShape) : List (String × Nat) :=
  [ ("summaryBase",            canonicalBPRelativeSummaryBase s)
  , ("summaryBlockCountRaw",   canonicalBPRelativeSummaryBlockCountRaw s)
  , ("summaryBlockSize",       canonicalBPRelativeSummaryBlockSize s)
  , ("summaryBlockCount",      canonicalBPRelativeSummaryBlockCount s)
  , ("summaryBlocksPerSuper",  canonicalBPRelativeSummaryBlocksPerSuper s)
  , ("rankWordSize",           builtRelativeSplitBPCloseRankWordSize s)
  , ("rankBlockOverhead",      builtRelativeSplitBPCloseRankBlockOverhead s)
  , ("rankSuperOverhead",      builtRelativeSplitBPCloseRankSuperOverhead s)
  , ("rankBlockWidth",         builtRelativeSplitBPCloseRankBlockWidth s)
  , ("fringeChunkBits",        bpFringeChunkBits s.bpCode.length)
  , ("bpLen",                  s.bpCode.length)
  ]

def flags (s : CartesianShape) : List (String × Bool) :=
  [ ("summaryTableActive", canonicalBPRelativeMinMaxArgSummaryTableActive s) ]

#eval show IO Unit from do
  IO.println "size | variant | flags | geometry"
  for n in [0,1,2,3,4,5,6,7,8,12,16,20,24,32,48,64,96,128,192,256,384,512,1024] do
    let vs := variants n
    -- collect per-name values across the variants and report any disagreement
    let base := vs.head!
    let baseG := geom base.2
    let baseF := flags base.2
    let mut disagree : List String := []
    for (nm, s) in vs.tail! do
      if s.size != n then
        disagree := s!"GENBUG:{nm}:size={s.size}" :: disagree
      for (gname, gval) in geom s do
        match baseG.find? (fun p => p.1 == gname) with
        | some (_, bval) =>
            if gval != bval then
              disagree := s!"{gname}[{base.1}={bval} vs {nm}={gval}]" :: disagree
        | none => pure ()
      for (fname, fval) in flags s do
        match baseF.find? (fun p => p.1 == fname) with
        | some (_, bval) =>
            if fval != bval then
              disagree := s!"{fname}[{base.1}={bval} vs {nm}={fval}]" :: disagree
        | none => pure ()
    let gstr := String.intercalate " " (baseG.map (fun p => s!"{p.1}={p.2}"))
    let fstr := String.intercalate " " (baseF.map (fun p => s!"{p.1}={p.2}"))
    let dstr := if disagree.isEmpty then "SAME-ACROSS-SHAPES" else s!"DIFFER: {disagree}"
    IO.println s!"n={n} | {fstr} | {dstr}"
    IO.println s!"      {gstr}"

end F03Reg
