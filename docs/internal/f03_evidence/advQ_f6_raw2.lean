import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL / QUANTIFIER attack on F6 (leaf L1), verdict S.  Cost-trimmed:
the `sparseExceptionSelectData` structure is built ONCE per bit family and
reused across every (store, idx) pair.

Thresholds the defender never crossed (advQ_f6_thresh.lean, executed):
  bpFringeChunkBits(len) = 1 for len <= 254, = 2 from len 256
  selectSuperSlot(q, superStride len) = 0 for every q < len/2 when len <= 128
Defender swept lengths 4,6,8,10 and shape sizes 1..5 only.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace AdvQF6R2

/-- Exactly the shipped leaf's body with `bits` in place of `shape.bpCode`,
with the data structure supplied so it can be shared. -/
def leafOf (bits : List Bool)
    (data : GenericSelect.SparseExceptionSelectData bits false
      (GenericSelect.sparseExceptionEffectiveFlagRankSuperOverhead bits false)
      (GenericSelect.sparseExceptionEffectiveFlagRankBlockOverhead bits false))
    (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  data.bpChunkedSelectTraceResultWithStore
    concreteBPNativeSelectCloseTraceSegmentLayout
    concreteBPNativeFringeChunkTraceSegment
    concreteBPNativeSelectChunkTraceSegment store
    (SuccinctClose.bpFringeChunkBits bits.length) idx

/-- This really is the shipped leaf: at `bits := shape.bpCode` and the canonical
data, `leafOf` is definitionally `concreteBPNativeSelectCloseGlobalWordTraceResultWithStore`. -/
theorem leafOf_eq (s : CartesianShape) (st : WordRAM.ReadStore) (i : Nat) :
    leafOf s.bpCode (GenericSelect.sparseExceptionSelectData s.bpCode false) st i =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s st i := rfl

def zeroW (w : Nat) : List Bool := List.replicate w false
def noiseW (w seg idx : Nat) : List Bool :=
  (List.range w).map fun k => (seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

def craft (w : Nat) (superMark localMark : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then some (if superMark then noiseW w 3 index else zeroW w)
    else if segment == 7 then some (if localMark then noiseW w 7 index else zeroW w)
    else some (noiseW w segment index)

def missingSuper (w : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 1 then none else some (noiseW w segment index)

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some x => String.mk (x.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i x? => s!"R({s},{i})->{wordStr x?}"
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

/-! families of length 2k with exactly k falses -/
def famBlockTF (k : Nat) : List Bool := List.replicate k true ++ List.replicate k false
def famAlt (k : Nat) : List Bool := (List.range (2 * k)).map fun i => i % 2 == 0
def famMid (k : Nat) : List Bool :=
  List.replicate (k / 2) true ++ List.replicate k false ++
    List.replicate (k - k / 2) true

def famsAt (k : Nat) : List (String × List Bool) :=
  [("blockTF", famBlockTF k), ("alt", famAlt k), ("mid", famMid k)]

def runRaw (k : Nat) (w : Nat) : IO Unit := do
  let len := 2 * k
  let ss := GenericSelect.superStride len
  IO.println s!"-- len={len} c={SuccinctClose.bpFringeChunkBits len} wordBits={GenericSelect.wordBits len} superStride={ss}"
  let idxs := ([0, ss, k - 1].filter (fun i => i < k)).eraseDups
  IO.println s!"   idxs={idxs} superSlots={idxs.map (fun i => GenericSelect.selectSuperSlot i ss)}"
  -- build each family's directory ONCE
  let mut built : List (String × String) := []   -- name, per-(store,idx) key blob
  for (nm, b) in famsAt k do
    let data := GenericSelect.sparseExceptionSelectData b false
    IO.println s!"   fam {nm}: len={b.length} falseCount={GenericSelect.occurrenceCount b false} first16={String.mk ((b.take 16).map fun x => if x then '1' else '0')}"
    let mut blob := ""
    let mut regs : List String := []
    for (lbl, st) in [("LONG", craft w true true), ("SPARSE", craft w false true),
                      ("DENSE", craft w false false), ("NONE", missingSuper w)] do
      for idx in idxs do
        let r := leafOf b data st idx
        blob := blob ++ s!"[{lbl}/{idx}]" ++ key r
        regs := (regs ++ [regime r]).eraseDups
    IO.println s!"        regimes reached = {regs}"
    built := built ++ [(nm, blob)]
  let b0 := (built.headD ("", "")).2
  let mut mism := 0
  for (nm, blob) in built do
    if blob != b0 then
      mism := mism + 1
      IO.println s!"   *** CONTENT DIVERGENCE fam={nm}"
  IO.println s!"   CONTENT-MISMATCHES={mism} (families compared: {built.map (fun p => p.1)})"

#eval show IO Unit from do
  IO.println "== RAW bitvectors, equal length + equal falseCount =="
  runRaw 64 16    -- len 128: c=1, single super slot  (defender's regime, control)

#eval show IO Unit from do
  runRaw 128 16   -- len 256: c=2 AND 2 super slots  (NEVER tested by defender)

end AdvQF6R2
