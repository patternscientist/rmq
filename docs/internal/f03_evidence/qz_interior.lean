import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
QZ-F03: exercise the F5 cone (`canonicalRelativeRmmInteriorRangeMinComputation`,
the constant whose sub-cone contains `bpExcessAt` and `bpBetterArgMinBlock`)
DIRECTLY, on a fixed shape-free flat store, across extreme shapes of a common
size, and forcing ALL FOUR of its top-level branches.

The prior agent's whole-query experiment at n <= 7 can only ever take branch 2
(`count <= layout.macroSize - localStart`), because at n <= 7
layout.macroSize = 9 while blockCount = 2.  That is the quantifier hole.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctSpace

namespace QZInterior

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

/-! A SHAPE-FREE flat store: contents depend on the address only. -/
def addrStore (k : Nat) : FlatWordStore :=
  fun a => some ((List.range 24).map fun j => ((a * 7 + j * 5 + k) % 3 == 0))

def constStore : FlatWordStore :=
  fun _ => some [true, false, true, false, true, false, true, false]

def run (s : CartesianShape) (store : FlatWordStore) (startBlock count : Nat) :
    List Nat × Option (Prod Nat Nat) :=
  let e := (canonicalRelativeRmmInteriorRangeMinComputation s startBlock count).run store
  (e.footprint, e.value)

/-! Which of the four top-level branches does (startBlock, count) select? -/
def branchOf (s : CartesianShape) (startBlock count : Nat) : String :=
  let layout := RelativeRmm.canonicalLayout s
  let localStart := startBlock % layout.macroSize
  if count = 0 then "B1-zero"
  else if count <= layout.macroSize - localStart then "B2-localTwoSpan"
  else
    let leftCount := layout.macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / layout.macroSize
    let rightCount := remaining % layout.macroSize
    if middleMacroCount = 0 then "B3-adjacentMacro"
    else if rightCount = 0 then "B4-leftMiddleMacro"
    else "B5-crossMacro"

/-! What the prior agent's n<=7 whole-query experiment can reach. -/
#eval show IO Unit from do
  IO.println "-- branch reachable at tiny n (blockCount is the whole legal range) --"
  for n in [3, 5, 7] do
    let s := leftSpine n
    let layout := RelativeRmm.canonicalLayout s
    let mut br : List String := []
    for sb in List.range (layout.blockCount + 1) do
      for c in List.range (layout.blockCount + 1) do
        let b := branchOf s sb c
        if !(br.contains b) then br := b :: br
    IO.println s!"n={n} macroSize={layout.macroSize} blockCount={layout.blockCount} branchesReachableInRange={br}"

/-! THE TEST: same size, six distinct bpCodes, one fixed shape-free store,
    all four branches forced. -/
#eval show IO Unit from do
  for n in [7, 16, 32] do
    let fam := family n
    let layout := RelativeRmm.canonicalLayout ((fam.headD ("", CartesianShape.empty)).2)
    let ms := layout.macroSize
    let probes : List (Nat × Nat) :=
      [ (0, 0), (0, 1), (0, 2)
      , (0, ms), (1, ms - 1)
      , (0, ms + 1), (2, ms + 1)
      , (0, 2 * ms), (0, 2 * ms + 3)
      , (ms, ms + 2), (ms + 1, 3 * ms + 5) ]
    for store in [constStore, addrStore 1, addrStore 2] do
      for (sb, c) in probes do
        match fam with
        | [] => pure ()
        | (nm0, s0) :: _ =>
          let r0 := run s0 store sb c
          let br := branchOf s0 sb c
          let mut diffs : List String := []
          for (nm, s) in fam do
            if run s store sb c != r0 then diffs := nm :: diffs
          if diffs != [] then
            IO.println s!"DIVERGE n={n} sb={sb} c={c} branch={br} shapes={diffs}"
    IO.println s!"DONE n={n} macroSize={ms} probes={probes.length} stores=3 shapes={fam.length}"

/-! ANTI-VACUITY: the interior transcript really does move with store, startBlock
    and count -- so an all-equal result above is not a vacuous "no reads". -/
#eval show IO Unit from do
  let n := 16
  let s := leftSpine n
  let ms := (RelativeRmm.canonicalLayout s).macroSize
  let mut fps : List (List Nat) := []
  let mut vals : List (Option (Prod Nat Nat)) := []
  for k in List.range 8 do
    let (fp, v) := run s (addrStore k) 0 (ms + 1)
    if !(fps.contains fp) then fps := fp :: fps
    if !(vals.contains v) then vals := v :: vals
  IO.println s!"ANTIVAC store: distinctFootprints={fps.length} distinctValues={vals.length} (8 stores)"
  let mut fps2 : List (List Nat) := []
  for c in [0, 1, 2, ms, ms + 1, 2 * ms, 2 * ms + 3] do
    let (fp, _) := run s constStore 0 c
    if !(fps2.contains fp) then fps2 := fp :: fps2
  IO.println s!"ANTIVAC count: distinctFootprints={fps2.length} (7 counts)"
  let (fp0, v0) := run s constStore 0 (ms + 1)
  IO.println s!"SAMPLE n=16 sb=0 c={ms+1} fpLen={fp0.length} fp={fp0.take 12} value={v0}"

end QZInterior
