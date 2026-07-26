import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL B: the uncovered cell.

The prior agent's exhaustive-bitvector sweep used only NOISE stores, and the
regime-forcing experiment used only BP codes of shapes.  Nobody ran
   forced regime  x  every bitvector.
If any content field reaches the executed path only inside the LONG, SPARSE or
DENSE branch, that is exactly where it would hide.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace Adv6F

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

def zeroW : List Bool := List.replicate 16 false
def noiseW (salt seg idx : Nat) : List Bool :=
  (List.range 16).map fun k =>
    (salt + seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index := some (noiseW salt segment index)

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

def sweepForced (label : String) (store : WordRAM.ReadStore) (len : Nat)
    (idxs : List Nat) : IO Unit := do
  let bs := allBits len
  let mut worst := 0
  let mut witness := ""
  let mut regs : List String := []
  for k in List.range (len + 1) do
    let g := bs.filter (fun b => falses b == k)
    if g.length != 0 then
      for idx in idxs do
        let ks := (g.map (fun b => key (L1raw b store idx))).eraseDups
        regs := (regs ++ g.map (fun b => regime (L1raw b store idx))).eraseDups
        if ks.length > worst then
          worst := ks.length
          witness := s!"(witness k={k} idx={idx})"
  IO.println s!"  {label} len={len} MAXDISTINCT={worst} {witness} regimes={regs}"

#eval show IO Unit from do
  IO.println "== B. forced regime x ALL bitvectors of length 8 =="
  sweepForced "LONG   super!=0        " (craft 11 true true) 8 (List.range 5)
  sweepForced "SPARSE super=0 local!=0" (craft 11 false true) 8 (List.range 5)
  sweepForced "DENSE  super=0 local=0 " (craft 11 false false) 8 (List.range 5)
  sweepForced "NONE   super absent    " missingSuper 8 (List.range 5)
  sweepForced "noise(11)              " (noiseStore 11) 8 (List.range 5)
  sweepForced "noise(3)               " (noiseStore 3) 8 (List.range 5)
  sweepForced "noise(7)               " (noiseStore 7) 8 (List.range 5)

#eval show IO Unit from do
  IO.println "== B'. same, length 10, DENSE and SPARSE only (the deep branches) =="
  sweepForced "SPARSE super=0 local!=0" (craft 11 false true) 10 (List.range 4)
  sweepForced "DENSE  super=0 local=0 " (craft 11 false false) 10 (List.range 4)

end Adv6F
