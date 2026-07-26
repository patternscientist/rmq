import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! QZ-F03: minimal, timed interior-cone cross-shape test that forces the
macro-crossing branches B3/B4/B5 which n <= 7 whole-query runs can never reach. -/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctSpace

namespace QZInt2

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

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

def family (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine", leftSpine n)
  , ("rightSpine", rightSpine n)
  , ("balanced", balanced n)
  , ("combT", comb n true)
  , ("combF", comb n false) ]

def addrStore (k : Nat) : FlatWordStore :=
  fun a => some ((List.range 24).map fun j => ((a * 7 + j * 5 + k) % 3 == 0))

def run (s : CartesianShape) (store : FlatWordStore) (startBlock count : Nat) :
    List Nat × Option (Prod Nat Nat) :=
  let e := (canonicalRelativeRmmInteriorRangeMinComputation s startBlock count).run store
  (e.footprint, e.value)

def branchOf (s : CartesianShape) (startBlock count : Nat) : String :=
  let layout := RelativeRmm.canonicalLayout s
  let localStart := startBlock % layout.macroSize
  if count = 0 then "B1-zero"
  else if count <= layout.macroSize - localStart then "B2-localTwoSpan"
  else
    let leftCount := layout.macroSize - localStart
    let remaining := count - leftCount
    if remaining / layout.macroSize = 0 then "B3-adjacentMacro"
    else if remaining % layout.macroSize = 0 then "B4-leftMiddleMacro"
    else "B5-crossMacro"

#eval show IO Unit from do
  let n := 7
  let s := leftSpine n
  let ms := (RelativeRmm.canonicalLayout s).macroSize
  let t0 <- IO.monoMsNow
  let (fp, v) := run s (addrStore 1) 0 (ms + 1)
  let t1 <- IO.monoMsNow
  IO.println s!"TIMING n={n} ms={ms} branch={branchOf s 0 (ms+1)} fpLen={fp.length} value={v} elapsedMs={t1 - t0}"

#eval show IO Unit from do
  for n in [7, 12] do
    let fam := family n
    let s0 := (fam.headD ("", CartesianShape.empty)).2
    let ms := (RelativeRmm.canonicalLayout s0).macroSize
    let probes : List (Nat × Nat) :=
      [ (0, 2), (0, ms), (0, ms + 1), (1, ms + 1)
      , (0, 2 * ms), (0, 2 * ms + 2), (ms, ms + 3) ]
    for (sb, c) in probes do
      let br := branchOf s0 sb c
      let r0 := run s0 (addrStore 1) sb c
      let mut diffs : List String := []
      for (nm, s) in fam do
        if run s (addrStore 1) sb c != r0 then diffs := nm :: diffs
      IO.println s!"n={n} sb={sb} c={c} branch={br} fpLen={r0.1.length} value={r0.2} DIFFERING={diffs}"

end QZInt2
