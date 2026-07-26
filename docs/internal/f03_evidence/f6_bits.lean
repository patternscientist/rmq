import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F6 / L1: the STRONG quantifier.

`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx`
is definitionally

  (sparseExceptionSelectData shape.bpCode false).bpChunkedSelectTraceResultWithStore
    LAYOUT 21 22 store (bpFringeChunkBits shape.bpCode.length) idx

so it is the composite `L1raw ∘ CartesianShape.bpCode`.  Instead of sweeping
the 1/(n+1) C(2n,n) BP codes only, sweep EVERY bitvector of a given length.
Claim under test: `L1raw bits store idx` depends on `bits` only through the
pair `(bits.length, occurrenceCount bits false)`.

For BP codes those two are `2 * shape.size` (`CartesianShape.bpCode_length`)
and `shape.size` (`SuccinctSpace.bpCode_rankFalse_full`), i.e. both are
functions of `n` alone.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F6Bits

/-- The raw leaf, as a function of the bit list rather than the shape. -/
def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

/-- `L1raw` really is the leaf, definitionally. -/
theorem L1raw_eq (shape : CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    L1raw shape.bpCode store idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape store idx := rfl

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 16).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some w => String.mk (w.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i w? => s!"R({s},{i})->{wordStr w?}"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def key (r : WordRAM.TraceResult (Option Nat)) : String :=
  s!"{repr r.value}|" ++ String.intercalate ";" (r.trace.map evKey)

/-- Every bitvector of a given length. -/
def allBits : Nat -> List (List Bool)
  | 0 => [[]]
  | Nat.succ n => (allBits n).flatMap fun t => [false :: t, true :: t]

def falses (bits : List Bool) : Nat := (bits.filter (fun b => !b)).length

/-- Ordered regime of the trace, from the segments it touches. -/
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

/-- Group all bitvectors of length `len` by `occurrenceCount bits false` and
report, per group, how many DISTINCT (value, trace) keys the leaf produces. -/
def sweep (len : Nat) (store : WordRAM.ReadStore) (idxs : List Nat) :
    IO Unit := do
  let bs := allBits len
  IO.println s!"== length={len} bitvectors={bs.length} =="
  for k in List.range (len + 1) do
    let group := bs.filter (fun b => falses b == k)
    if group.length != 0 then
      let mut worst := 0
      let mut regs : List String := []
      for idx in idxs do
        let ks := (group.map (fun b => key (L1raw b store idx))).eraseDups
        regs := (regs ++ group.map (fun b => regime (L1raw b store idx))).eraseDups
        if ks.length > worst then worst := ks.length
      IO.println s!"  falseCount={k} members={group.length} maxDistinctLeafOutcomesOverIdx={worst} regimes={regs}"

#eval show IO Unit from do
  sweep 4 (noiseStore 11) (List.range 4)
  sweep 6 (noiseStore 11) (List.range 5)
  sweep 8 (noiseStore 11) (List.range 6)

#eval show IO Unit from do
  sweep 8 (noiseStore 3) (List.range 6)
  sweep 10 (noiseStore 11) (List.range 7)

-- Control: does the leaf depend on the length at all?
#eval show IO Unit from do
  let store := noiseStore 11
  let a : List Bool := (List.range 8).map (fun i => i % 2 == 0)
  let b : List Bool := (List.range 10).map (fun i => i % 2 == 0)
  IO.println s!"len8 falses={falses a} vs len10 falses={falses b}"
  IO.println s!"  same key? {key (L1raw a store 2) == key (L1raw b store 2)}"
  let c : List Bool := [true, true, true, true, false, false, false, false]
  let d : List Bool := [true, false, true, false, true, false, true, false]
  IO.println s!"len8 k=4 two very different bitvectors, same key? {key (L1raw c store 2) == key (L1raw d store 2)}"
  IO.println s!"  c: {key (L1raw c store 2)}"
  IO.println s!"  d: {key (L1raw d store 2)}"

end F6Bits
