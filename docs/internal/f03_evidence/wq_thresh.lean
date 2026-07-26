import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
THRESHOLD MAP, by EVALUATION of the predicates (not by reading theorem names).

Three regime families gate the executed route:
  (A) `canonicalBPRelativeMinMaxArgSummaryTableActive` -- summary/interior arm
  (B) `GenericSelect.superIsLong`      -- select long/sparse super arm
  (C) `GenericSelect.localIsSparse` / `localIsSparseException` -- sparse local arm

(B) and (C) are the only genuinely CONTENT-dependent predicates in the select
layer.  Both are of the form `threshold(bits.length) < span(bits,...)`, so they
are bounded by pure length arithmetic:
  * `superIsLong` can fire only if `superLongSpan m < m` (a span never exceeds m).
  * `localIsSparse` compares against a span of a block holding `localStride m`
    occurrences; if `localStride m = 1` the span is identically 1, so the
    predicate is identically false whatever the content.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose
open RMQ.GenericSelect

namespace WQThresh

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

/-- (B)/(C): pure length arithmetic controlling the select regimes. -/
#eval show IO Unit from do
  IO.println "== (B)/(C) select-layer length arithmetic =="
  IO.println "m | wordBits | ell | localStride | superStride | superLongSpan | superIsLong-CAN-FIRE(m>superLongSpan) | localIsSparse-CAN-FIRE(localStride>=2)"
  let mut firstLong : Option Nat := none
  let mut firstSparse : Option Nat := none
  for e in List.range 41 do
    let m := 2 ^ e
    let w := wordBits m
    let l := ell m
    let ls := localStride m
    let ss := superStride m
    let sls := superLongSpan m
    let canLong := sls < m
    let canSparse := 2 <= ls
    if canLong && firstLong.isNone then firstLong := some m
    if canSparse && firstSparse.isNone then firstSparse := some m
    if e <= 20 || canLong || canSparse || e % 5 == 0 then
      IO.println s!"m=2^{e}={m} w={w} ell={l} localStride={ls} superStride={ss} superLongSpan={sls} canLong={canLong} canSparse={canSparse}"
  IO.println s!"FIRST bp-length m at which superIsLong CAN fire (power of 2 scan): {firstLong}"
  IO.println s!"FIRST bp-length m at which localIsSparse CAN fire (power of 2 scan, up to 2^40): {firstSparse}"

/-- (C) executed check: the sparse predicates on real shapes, all slots. -/
#eval show IO Unit from do
  IO.println "== (C) localIsSparse / localIsSparseException, EXECUTED on real bpCodes =="
  for n in [4, 8, 16, 32, 64, 128, 256, 384, 512, 1024] do
    for (nm, s) in [("L", leftSpine n), ("R", rightSpine n), ("B", balanced n)] do
      let bits := s.bpCode
      for tgt in [true, false] do
        let cnt := localSlotCount bits tgt
        let sparseTrue := (List.range cnt).filter (fun i => localIsSparse bits tgt i)
        let excTrue := (List.range cnt).filter (fun i => localIsSparseException bits tgt i)
        let scnt := superSlotCount bits tgt
        let longTrue := (List.range scnt).filter (fun i => superIsLong bits tgt i)
        if !sparseTrue.isEmpty || !excTrue.isEmpty || !longTrue.isEmpty then
          IO.println s!"  n={n} {nm} tgt={tgt}: FIRES sparse={sparseTrue.length} exc={excTrue.length} long={longTrue.length}"
    IO.println s!"  n={n}: localSlotCount(L,true)={localSlotCount (leftSpine n).bpCode true} localStride={localStride (2*n)} -- all three shapes, both targets, ALL slots: no firing unless printed above"

/-- (A) exact threshold for the summary/interior arm, by linear scan. -/
#eval show IO Unit from do
  IO.println "== (A) canonicalBPRelativeMinMaxArgSummaryTableActive: exact turn-on size =="
  -- linear scan for the exact first active size, and check monotone-ish behaviour
  let mut firstActive : Option Nat := none
  let mut flips : List (Nat × Bool) := []
  let mut prev : Bool := false
  for n in List.range 700 do
    let a : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive (leftSpine n))
    if a && firstActive.isNone then firstActive := some n
    if n > 0 && a != prev then flips := (n, a) :: flips
    prev := a
  IO.println s!"  firstActive(leftSpine, scan 0..699) = {firstActive}"
  IO.println s!"  ALL flips in 0..699 = {flips.reverse}"

/-- (A) is the active flag shape-invariant at equal size?  Checked at every size. -/
#eval show IO Unit from do
  IO.println "== (A) shape-invariance of the active flag, every size 0..600, 3 shapes =="
  let mut disagreements := 0
  let mut cmps := 0
  for n in List.range 601 do
    let a : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive (leftSpine n))
    for s in [rightSpine n, balanced n] do
      cmps := cmps + 1
      let b : Bool := decide (canonicalBPRelativeMinMaxArgSummaryTableActive s)
      if a != b then
        disagreements := disagreements + 1
        IO.println s!"  !! ACTIVE-FLAG DISAGREE at n={n}: L={a} other={b}"
  IO.println s!"  activeFlag comparisons={cmps} disagreements={disagreements}"

end WQThresh
