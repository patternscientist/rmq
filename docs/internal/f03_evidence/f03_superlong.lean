import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
The last open F03 frontier: the select-layer span predicates.

After the interior cone was closed (the flat-store table adapter binds its table
as `_table`, so table CONTENTS reach neither addresses nor values), the only
content-reading branches left in the controller's computational core are in the
select layer:

  `superIsLong bits target slot = decide (superLongSpan bits.length < superSpan bits target slot)`
      RMQ/Core/GenericSelect/Slots.lean:103
  `localIsSparseException`  Slots.lean:859
  `compactLocalEntryIsLive` Entries.lean:47

`superSpan` is a POSITION DIFFERENCE between occurrences, not a popcount, so
unlike `occurrenceCount` it is not forced by `bits.length`. Two questions:

  Q1. Is `superIsLong` ever actually TRUE for a Cartesian-tree BP code, and does
      it differ between two shapes of the same size?
  Q2. If it does differ, does that difference reach the select leaf's TRANSCRIPT
      under a supplied store -- or is the regime learned by PROBING the long-flag
      directory (segments 9/10/11 of the read store, `longFlagRankData`) rather
      than computed from free bits?

A shape family that should force sparsity: `node (leftSpine K) (rightSpine M)`
has bpCode `true^(K+1) ++ false^(K+1) ++ (true false)^M`. The ones are packed at
the front, then a run of K+1 closes with NO ones, then evenly spread ones. The
superblock spanning that transition has span ~K while carrying only ~(log n)^2
occurrences, so it should exceed `superLongSpan = wordBits^3 * ell` once K is
large. Uniform families (left spine, right spine, balanced) have locally uniform
density and should stay dense everywhere -- which is why they alone were never
enough evidence.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace F03Long

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

/-- `true^(K+1) false^(K+1) (true false)^M`, size K+1+M. -/
def cliff (K M : Nat) : CartesianShape := .node (leftSpine K) (rightSpine M)

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

/-- Scan every super slot and report which are long. -/
def longSlots (s : CartesianShape) (target : Bool) : List Nat :=
  let bits := s.bpCode
  let n := bits.length
  let cnt := occurrenceCount bits target
  let stride := superStride n
  let slots := if stride = 0 then 0 else cnt / stride + 1
  (List.range slots).filter (fun i => superIsLong bits target i)

def maxSuperSpan (s : CartesianShape) (target : Bool) : Nat :=
  let bits := s.bpCode
  let n := bits.length
  let cnt := occurrenceCount bits target
  let stride := superStride n
  let slots := if stride = 0 then 0 else cnt / stride + 1
  ((List.range slots).map (fun i => superSpan bits target i)).foldl Nat.max 0

def selLeaf (s : CartesianShape) (st : WordRAM.ReadStore) (idx : Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s st idx

/-- Q1: does the long/dense regime ever differ across same-size shapes? -/
#eval show IO Unit from do
  IO.println "Q1: superIsLong across same-size shapes (target=false, the close bit the route selects on)"
  for n in [16, 32, 64, 128, 256] do
    let fams : List (String × CartesianShape) :=
      [ ("leftSpine", leftSpine n)
      , ("rightSpine", rightSpine n)
      , ("balanced", balanced n)
      , ("cliff(n-1,0)", cliff (n - 1) 0)
      , ("cliff(3n/4,n/4-1)", cliff (3 * n / 4) (n - 1 - 3 * n / 4))
      , ("cliff(n/2,n/2-1)", cliff (n / 2) (n - 1 - n / 2)) ]
    IO.println s!"-- n={n} superLongSpan={superLongSpan (2*n)} superStride={superStride (2*n)} wordBits={wordBits (2*n)} ell={ell (2*n)}"
    for (nm, s) in fams do
      if s.size != n then
        IO.println s!"   {nm}: SIZE MISMATCH {s.size}"
      else
        IO.println s!"   {nm}: maxSuperSpan(false)={maxSuperSpan s false} longSlots(false)={longSlots s false} maxSuperSpan(true)={maxSuperSpan s true} longSlots(true)={longSlots s true}"

/-- Q2: if the regime differs, does the select leaf's transcript differ? -/
#eval show IO Unit from do
  IO.println "Q2: select-leaf transcript across same-size shapes including the cliff family"
  let st := addrStore 5
  let mut cmp := 0
  let mut div := 0
  for n in [16, 32, 64, 128, 256] do
    let fams : List (String × CartesianShape) :=
      [ ("leftSpine", leftSpine n)
      , ("rightSpine", rightSpine n)
      , ("cliff(n-1,0)", cliff (n - 1) 0)
      , ("cliff(3n/4,..)", cliff (3 * n / 4) (n - 1 - 3 * n / 4))
      , ("cliff(n/2,..)", cliff (n / 2) (n - 1 - n / 2)) ]
    let (bn, b) := fams.head!
    for idx in [0, 1, n / 2, n - 1] do
      let br := selLeaf b st idx
      for (nm, s) in fams.tail! do
        cmp := cmp + 1
        let x := selLeaf s st idx
        if x.trace != br.trace || x.value != br.value then
          div := div + 1
          IO.println s!"  *** SELECT DIVERGENCE n={n} idx={idx} {bn} vs {nm}: len {br.trace.length} vs {x.trace.length}, value {br.value} vs {x.value}"
          let z := (br.trace.zip x.trace).findIdx? (fun p => p.1 != p.2)
          IO.println s!"      firstDiff={z}"
          match z with
          | some i =>
              IO.println s!"      base[{i}]={repr (br.trace[i]?)}"
              IO.println s!"      this[{i}]={repr (x.trace[i]?)}"
          | none => IO.println s!"      (prefix agrees; lengths differ)"
    IO.println s!"  n={n} done (cumulative comparisons={cmp} divergences={div})"
  IO.println s!"F03-SUPERLONG-SELECT comparisons={cmp} divergences={div}"

end F03Long
