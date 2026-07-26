import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Active-regime evidence for the INTERIOR addressing geometry.

Evaluating the whole L2 (LCA-close) leaf is superlinear in the interpreter --
~1.7 s per evaluation at n=32 but ~180 s at n=128 -- so its full transcript
cannot be sampled at n >= 512 this way. That is a harness limit, not a
mathematical obstruction.

The addressing geometry it consumes CAN be evaluated directly and cheaply. This
file sweeps every interior/summary offset and width the interior directory uses
to form addresses, across structurally extreme same-size shapes, deep into the
ACTIVE regime (the summary table switches on between n=384 and n=512).

An address the controller forms is closed iff it factors through n. So if every
one of these offsets agrees across same-size shapes at n = 512, 1024, 2048, the
interior addressing is size-derived even though the leaf transcript itself has
not been sampled there.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace F03Int

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
  , ("p1", pseudo 1 n), ("p7", pseudo 7 n), ("p31", pseudo 31 n) ]

/-- The interior component offsets: every field of the offsets record the
    interior directory uses to place its components in the flat store. -/
def offsetFields (s : CartesianShape) : List (String × Nat) :=
  let o := canonicalRelativeRmmInteriorComponentOffsets s
  [ ("summaryBase",           canonicalBPRelativeSummaryBase s)
  , ("summaryBlockSize",      canonicalBPRelativeSummaryBlockSize s)
  , ("summaryBlockCount",     canonicalBPRelativeSummaryBlockCount s)
  , ("summaryBlocksPerSuper", canonicalBPRelativeSummaryBlocksPerSuper s)
  , ("fringeChunkBits",       bpFringeChunkBits s.bpCode.length)
  , ("localWindowBase",       localBPWindowBase s.bpCode.length)
  , ("offsets.repr.len",      (toString (repr o)).length)
  ]

#eval show IO Unit from do
  IO.println "n | active | agreement across 6 structurally extreme same-size shapes"
  let mut totalCmp := 0
  let mut totalDiff := 0
  for n in [64, 128, 256, 384, 512, 640, 1024, 2048, 4096] do
    let vs := variants n
    let (bn, b) := vs.head!
    let active : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive b)
    let baseF := offsetFields b
    let mut bad : List String := []
    for (nm, s) in vs.tail! do
      if s.size != n then bad := s!"GENBUG:{nm}" :: bad
      for (fn, fv) in offsetFields s do
        totalCmp := totalCmp + 1
        match baseF.find? (fun p => p.1 == fn) with
        | some (_, bv) =>
            if fv != bv then
              totalDiff := totalDiff + 1
              bad := s!"{fn}[{bn}={bv} vs {nm}={fv}]" :: bad
        | none => pure ()
    let status := if bad.isEmpty then "ALL AGREE" else s!"DIFFER: {bad}"
    IO.println s!"n={n} | active={active} | {status}"
    IO.println s!"     {String.intercalate "  " (baseF.map (fun p => s!"{p.1}={p.2}"))}"
  IO.println s!"INTERIOR-GEOMETRY comparisons={totalCmp} disagreements={totalDiff}"

/-- The interior offsets record itself, printed at two active-regime sizes for
    two maximally different shapes, so the comparison is visible and not just
    counted. -/
#eval show IO Unit from do
  for n in [512, 1024] do
    IO.println s!"--- interior component offsets at n={n}"
    IO.println s!"  L: {repr (canonicalRelativeRmmInteriorComponentOffsets (leftSpine n))}"
    IO.println s!"  R: {repr (canonicalRelativeRmmInteriorComponentOffsets (rightSpine n))}"
    IO.println s!"  equal={(repr (canonicalRelativeRmmInteriorComponentOffsets (leftSpine n))).pretty == (repr (canonicalRelativeRmmInteriorComponentOffsets (rightSpine n))).pretty}"

end F03Int
