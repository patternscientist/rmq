import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION of the S verdict on
`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore` (leaf L1 / F6).

Attack plan (targets holes in the prior agent's coverage):

A. ANTI-VACUITY of the internals.  The prior sweep grouped bitvectors by
   (length, occurrenceCount) and found ONE outcome per group.  That is worthless
   if the `sparseExceptionSelectData` internals are themselves constant inside a
   group.  Measure how many DISTINCT internals a group actually contains.

B. COVERAGE GAP.  The exhaustive-bitvector sweep used only NOISE stores (regimes
   reached: unknown / unreported).  The regime-forcing experiment used only BP
   codes of shapes.  Nobody ran   forced regime  x  all bitvectors.  Do it.

C. CORRECTNESS anti-vacuity.  Under the REAL store the leaf must actually answer
   selectClose.  If it returns garbage or `none`, shape-independence is trivial.
   Check leaf X (realStore A) idx  ==  true (idx+1)-th `false` position of A.bpCode,
   and check that the true answers DIFFER across same-size shapes.

D. The two "dead Nat" overhead type indices B2/B3: are they content-dependent at
   all?  If they are constant across every bitvector of a given length, the
   consumption question is moot.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace Adv6

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

/-- The leaf with `bits` in place of `shape.bpCode`. -/
def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

theorem L1raw_eq (shape : CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    L1raw shape.bpCode store idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape store idx := rfl

def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

/-! ## stores -/

def zeroW : List Bool := List.replicate 16 false
def noiseW (salt seg idx : Nat) : List Bool :=
  (List.range 16).map fun k =>
    (salt + seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index := some (noiseW salt segment index)

/-- Force the two regime bits: segment 3 = super `rankBefore`,
segment 7 = local `rankBefore`. -/
def craft (salt : Nat) (superMark localMark : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then
      some (if superMark then noiseW salt 3 index else zeroW)
    else if segment == 7 then
      some (if localMark then noiseW salt 7 index else zeroW)
    else
      some (noiseW salt segment index)

def missingSuper : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 1 then none else some (noiseW 0 segment index)

/-! ## keys -/

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some w => String.mk (w.map fun b => if b then '1' else '0')

def bstr (w : List Bool) : String := String.mk (w.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i w? => s!"R({s},{i})->{wordStr w?}"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def key (r : WordRAM.TraceResult (Option Nat)) : String :=
  s!"{repr r.value}|" ++ String.intercalate ";" (r.trace.map evKey)

def segsOf (r : WordRAM.TraceResult (Option Nat)) : List Nat :=
  r.trace.filterMap fun ev =>
    match ev with
    | WordRAM.TraceEvent.readWord s _ _ => some s
    | _ => none

def regime (r : WordRAM.TraceResult (Option Nat)) : String :=
  let ss := segsOf r
  let has (a b : Nat) := ss.any (fun s => a <= s && s <= b)
  let l := has 9 12
  let sp := has 13 16
  let d := ss.any (fun s => s == 0)
  s!"{if l then "LONG" else ""}{if sp then "SPARSE" else ""}{if d then "DENSE" else ""}{if !l && !sp && !d then "NONE" else ""}"

def allBits : Nat -> List (List Bool)
  | 0 => [[]]
  | Nat.succ n => (allBits n).flatMap fun t => [false :: t, true :: t]

def falses (bits : List Bool) : Nat := (bits.filter (fun b => !b)).length

/-! ## A. anti-vacuity of the internals -/

def entStr (e : RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry) : String :=
  s!"({e.baseOccurrence},{e.baseWordIndex},{e.rankBefore},{e.firstOffset})"

def internalsKey (bits : List Bool) : String :=
  let d := GenericSelect.sparseExceptionSelectData bits false
  let se := (GenericSelect.superEntries bits false).map entStr
  let le := (GenericSelect.localEntries bits false).map entStr
  let lf := GenericSelect.longSuperFlagBits bits false
  let ef := GenericSelect.sparseExceptionEffectiveFlagBits bits false
  let pay := GenericSelect.SparseExceptionSelectData.payload d
  s!"SE[{String.intercalate ";" se}]LE[{String.intercalate ";" le}]LF={bstr lf}EF={bstr ef}PAY={bstr pay}"

def ovhKey (bits : List Bool) : String :=
  let a := GenericSelect.sparseExceptionEffectiveFlagRankSuperOverhead bits false
  let b := GenericSelect.sparseExceptionEffectiveFlagRankBlockOverhead bits false
  let c := GenericSelect.longFlagRankSuperOverhead bits false
  let e := GenericSelect.longFlagRankBlockOverhead bits false
  s!"{a}/{b}/{c}/{e}"

#eval show IO Unit from do
  IO.println "== A. ANTI-VACUITY: distinct internals vs distinct leaf outcomes, per (len,falseCount) =="
  for len in [8, 10] do
    let bs := allBits len
    for k in List.range (len + 1) do
      let g := bs.filter (fun b => falses b == k)
      if g.length >= 2 then
        let ints := (g.map internalsKey).eraseDups
        let ovhs := (g.map ovhKey).eraseDups
        let outs := (g.map (fun b => key (L1raw b (noiseStore 11) 2))).eraseDups
        IO.println s!"  len={len} k={k} members={g.length} distinctInternals={ints.length} distinctOverheads={ovhs.length} distinctLeafOutcomes={outs.length}"

/-! ## D. are the overhead type indices content-dependent at all? -/

#eval show IO Unit from do
  IO.println "== D. overheads across EVERY bitvector of a length (not grouped) =="
  for len in [6, 8, 10] do
    let bs := allBits len
    let ovhs := (bs.map ovhKey).eraseDups
    IO.println s!"  len={len} bitvectors={bs.length} distinct(effSuper/effBlock/longSuper/longBlock)={ovhs.length} values={ovhs}"

/-! ## B. COVERAGE GAP: forced regime x ALL bitvectors -/

def sweepForced (label : String) (store : WordRAM.ReadStore) (len : Nat)
    (idxs : List Nat) : IO Unit := do
  let bs := allBits len
  let mut worst := 0
  let mut worstWitness := ""
  let mut regs : List String := []
  for k in List.range (len + 1) do
    let g := bs.filter (fun b => falses b == k)
    if g.length != 0 then
      for idx in idxs do
        let ks := (g.map (fun b => key (L1raw b store idx))).eraseDups
        regs := (regs ++ g.map (fun b => regime (L1raw b store idx))).eraseDups
        if ks.length > worst then
          worst := ks.length
          worstWitness := s!"k={k} idx={idx} distinct={ks.length}"
  IO.println s!"  {label} len={len} maxDistinctOutcomesInAnyGroup={worst} {worstWitness} regimes={regs}"

#eval show IO Unit from do
  IO.println "== B. forced regime x ALL bitvectors (the uncovered cell) =="
  for len in [8, 10] do
    sweepForced "LONG   (super.rankBefore!=0)" (craft 11 true true) len (List.range 5)
    sweepForced "SPARSE (super=0, local!=0)  " (craft 11 false true) len (List.range 5)
    sweepForced "DENSE  (super=0, local=0)   " (craft 11 false false) len (List.range 5)
    sweepForced "NONE   (super absent)       " missingSuper len (List.range 5)
    sweepForced "noise(11)                   " (noiseStore 11) len (List.range 5)
    sweepForced "noise(3)                    " (noiseStore 3) len (List.range 5)

end Adv6
