import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack, stage 3: the STORE LAYOUT.

The other agent only ever ran the controller against a FIXED SHAPE-FREE store,
so its experiment can say nothing about whether the real store's segment
geometry factors through n.  For the packed target
(`header ++ buildPayload ++ padding`, exact-width w(n) cells) the segment word
COUNTS and the cell WIDTHS are exactly the offsets the controller must be able
to compute from n.  If two same-size shapes give different segment lengths or
different cell widths, the packing offsets are content-dependent.

Here I measure, for the REAL store `concreteBPCloseNavigationGlobalReadStore`,
for every one of the 26 segments:
  - the number of live words (first index returning `none`)
  - the set of word bit-widths that occur
and diff those across all shapes of the same size.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.BPNavigation

namespace AdvSZStore

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def shapesN : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesN k).flatMap fun l =>
          (shapesN (n - k)).map fun r => CartesianShape.node l r

/-- live word count of one segment, capped -/
def segCount (st : WordRAM.ReadStore) (seg cap : Nat) : Nat :=
  let rec go (i : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => i
    | Nat.succ f => match st.readWord? seg i with
                    | none => i
                    | some _ => go (i + 1) f
  go 0 cap

/-- the multiset (as sorted-ish distinct list) of word widths in one segment -/
def segWidths (st : WordRAM.ReadStore) (seg cap : Nat) : List Nat :=
  let rec go (i : Nat) (fuel : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0 => acc.reverse
    | Nat.succ f => match st.readWord? seg i with
                    | none => acc.reverse
                    | some w => go (i + 1) f (w.length :: acc)
  go 0 cap []

def profile (s : CartesianShape) (cap : Nat) : List (Nat × Nat × List Nat) :=
  let st := concreteBPCloseNavigationGlobalReadStore s
  (List.range 26).map fun seg =>
    let c := segCount st seg cap
    let ws := segWidths st seg cap
    let dws := ws.foldl (fun acc v => if acc.contains v then acc else v :: acc) []
    (seg, c, dws.reverse)

def runExhaustive (n : Nat) (cap : Nat) : IO Unit := do
  let ss := shapesN n
  match ss with
  | [] => pure ()
  | s0 :: _ =>
    let p0 := profile s0 cap
    let mut countDiffSegs : List Nat := []
    let mut widthDiffSegs : List Nat := []
    let mut anyDiff := 0
    for s in ss do
      let p := profile s cap
      for (a, b) in p0.zip p do
        if a.2.1 != b.2.1 && !(countDiffSegs.contains a.1) then
          countDiffSegs := a.1 :: countDiffSegs
        if a.2.2 != b.2.2 && !(widthDiffSegs.contains a.1) then
          widthDiffSegs := a.1 :: widthDiffSegs
      if p != p0 then anyDiff := anyDiff + 1
    IO.println s!"EXH n={n} shapes={ss.length} profileDiffers={anyDiff} segsWithDifferingWordCount={countDiffSegs.reverse} segsWithDifferingWidths={widthDiffSegs.reverse}"
    IO.println s!"      baseline profile (seg,count,widths) = {p0}"

#eval show IO Unit from do
  for n in [1,2,3,4] do
    runExhaustive n 64

end AdvSZStore
