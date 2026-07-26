import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL C1/C3 (trimmed) + REACHABILITY.

C1: fix the REAL store to shape A; vary the shape argument X over every shape of
    the same size.  Does the answer track the STORE (A) or the SHAPE ARGUMENT (X)?
C3: same, address traces.
R : is L1 actually on the executed whole-query path at all?
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace Adv6C

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

def selFalse : List Bool -> Nat -> Nat -> Option Nat
  | [], _, _ => none
  | b :: t, i, pos =>
      if b then selFalse t i (pos + 1)
      else if i == 0 then some pos else selFalse t (i - 1) (pos + 1)

def trueSel (bits : List Bool) (i : Nat) : Option Nat := selFalse bits i 0

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i _ => s!"({s},{i})"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def addrTrace {a : Type} (r : WordRAM.TraceResult a) : String :=
  String.intercalate ";" (r.trace.map evKey)

def segsOf {a : Type} (r : WordRAM.TraceResult a) : List Nat :=
  r.trace.filterMap fun ev =>
    match ev with
    | WordRAM.TraceEvent.readWord s _ _ => some s
    | _ => none

def crossOne (n : Nat) (storeIdxs : List Nat) : IO Unit := do
  let shapes := shapesOfSize n
  for ai in storeIdxs do
    let a := shapes.getD ai CartesianShape.empty
    let store := concreteBPNativeSuccinctRMQGlobalReadStore a
    let mut tracksStore := 0
    let mut tracksArg := 0
    let mut neither := 0
    let mut disagreeing := 0
    for idx in List.range n do
      let wantA := trueSel a.bpCode idx
      for x in shapes do
        let got := (leaf x store idx).value
        let wantX := trueSel x.bpCode idx
        if wantX != wantA then disagreeing := disagreeing + 1
        if got == wantA then tracksStore := tracksStore + 1
        else if got == wantX then tracksArg := tracksArg + 1
        else neither := neither + 1
    IO.println s!"  n={n} store=shape#{ai} bp={a.bpCode} : tracks-STORE={tracksStore} tracks-SHAPE-ARG={tracksArg} neither={neither} | pairs where the two answers DIFFER={disagreeing}"

#eval show IO Unit from do
  IO.println "== C1. leaf X (realStore A) : does the answer follow A (store) or X (shape arg)? =="
  crossOne 3 (List.range 5)
  crossOne 4 [0, 6, 13]
  crossOne 5 [0, 20, 41]

#eval show IO Unit from do
  IO.println "== C3. address traces under realStore(A), shape argument varied =="
  for n in [3, 4, 5] do
    let shapes := shapesOfSize n
    let a := shapes.headD CartesianShape.empty
    let store := concreteBPNativeSuccinctRMQGlobalReadStore a
    let mut mism := 0
    for idx in List.range n do
      let ts := (shapes.map (fun x => addrTrace (leaf x store idx))).eraseDups
      if ts.length != 1 then mism := mism + 1
    IO.println s!"  n={n} shapes={shapes.length} idxs-with-differing-address-traces={mism}"
  let sh := (shapesOfSize 4).headD CartesianShape.empty
  IO.println s!"  sample n=4 idx=1 trace: {addrTrace (leaf sh (concreteBPNativeSuccinctRMQGlobalReadStore sh) 1)}"

#eval show IO Unit from do
  IO.println "== R. is L1 on the executed whole-query path? (segments 1..8 = select entry tables) =="
  for n in [4, 5] do
    let shapes := shapesOfSize n
    let a := shapes.headD CartesianShape.empty
    let store := concreteBPNativeSuccinctRMQGlobalReadStore a
    let r := concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore a store 0 n
    let ss := segsOf r
    let selectSegs := ss.filter (fun s => 1 <= s && s <= 8)
    IO.println s!"  n={n} wholeQuery(0,{n}) value={r.value} events={r.trace.length} select-entry-table reads(segs 1..8)={selectSegs.length} distinctSegs={ss.eraseDups}"

end Adv6C
