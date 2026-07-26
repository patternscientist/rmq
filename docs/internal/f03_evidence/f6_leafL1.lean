import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F03 / F6 experiment: isolate controller leaf L1
`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore`.

Fix a store that does NOT depend on the varying shape; vary the shape over
every Cartesian shape of a given size; compare this leaf's trace AND value.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F6L1

set_option pp.explicit true in
#print concreteBPNativeSelectCloseGlobalWordTraceResultWithStore

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

/-- Deterministic, shape-free pseudo-random store. -/
def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 16).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

/-- Leaf L1 under a supplied store. -/
def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some w => String.mk (w.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i w? => s!"R({s},{i})->{wordStr w?}"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def addrKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i _ => s!"({s},{i})"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def traceKey (r : WordRAM.TraceResult (Option Nat)) : String :=
  String.intercalate ";" (r.trace.map evKey)

def addrTrace (r : WordRAM.TraceResult (Option Nat)) : String :=
  String.intercalate ";" (r.trace.map addrKey)

def segs (r : WordRAM.TraceResult (Option Nat)) : List Nat :=
  r.trace.filterMap fun ev =>
    match ev with
    | WordRAM.TraceEvent.readWord s _ _ => some s
    | _ => none

/-- Which route the trace took, read off the segments it touched.
Segments 9-12 = long-super exception route; 13-16 = sparse-exception
directory route; 0/21/22 = dense packed-word route; 1-8 only = entry
lookup returned `none` (short). -/
def regime (r : WordRAM.TraceResult (Option Nat)) : String :=
  let ss := segs r
  let has (a b : Nat) := ss.any (fun s => a <= s && s <= b)
  let long := has 9 12
  let sparse := has 13 16
  let dense := ss.any (fun s => s == 0)
  s!"{if long then "LONG" else ""}{if sparse then "SPARSE" else ""}{if dense then "DENSE" else ""}{if !long && !sparse && !dense then "NONE" else ""}"

def report (label : String) (n : Nat) (store : WordRAM.ReadStore)
    (idxs : List Nat) : IO Unit := do
  let shapes := shapesOfSize n
  let mut mismatchTrace := 0
  let mut mismatchValue := 0
  let mut total := 0
  let mut regs : List String := []
  for idx in idxs do
    let results := shapes.map (fun s => leaf s store idx)
    let keys := results.map traceKey
    let vals := results.map (fun r => r.value)
    regs := (regs ++ results.map regime).eraseDups
    let k0 := keys.headD ""
    let v0 := vals.headD none
    for k in keys do
      total := total + 1
      if k != k0 then mismatchTrace := mismatchTrace + 1
    for v in vals do
      if v != v0 then mismatchValue := mismatchValue + 1
  IO.println s!"{label} n={n} shapes={shapes.length} idxs={idxs.length} comparisons={total} TRACE-MISMATCHES={mismatchTrace} VALUE-MISMATCHES={mismatchValue} regimesReached={regs}"

#eval show IO Unit from do
  IO.println "== shape-free noise stores =="
  for n in [1, 2, 3, 4, 5] do
    for salt in [0, 3, 11] do
      report s!"noise(salt={salt})" n (noiseStore salt) (List.range (n + 2))

#eval show IO Unit from do
  IO.println "== fixed REAL store built from ONE shape, shape argument varied =="
  for n in [1, 2, 3, 4, 5] do
    let shapes := shapesOfSize n
    let first := shapes.headD CartesianShape.empty
    let last := shapes.getLastD CartesianShape.empty
    report "realStore(first)" n
      (concreteBPNativeSuccinctRMQGlobalReadStore first) (List.range (n + 2))
    report "realStore(last)" n
      (concreteBPNativeSuccinctRMQGlobalReadStore last) (List.range (n + 2))

-- Per-shape detail at n=4 under one fixed real store: full address trace.
#eval show IO Unit from do
  let n := 4
  let shapes := shapesOfSize n
  let store := concreteBPNativeSuccinctRMQGlobalReadStore
    (shapes.headD CartesianShape.empty)
  IO.println s!"== n={n} detail, shapeCount={shapes.length} =="
  for s in shapes, i in List.range shapes.length do
    let r := leaf s store 2
    IO.println s!"  shape[{i}] bp={s.bpCode} value={r.value} regime={regime r} addr={addrTrace r}"

-- Regime sweep: does the LONG/SPARSE/DENSE route ever flip as a function of
-- the PROBE REPLIES (the store) alone, with the shape held at a fixed size?
#eval show IO Unit from do
  let n := 3
  let shapes := shapesOfSize n
  IO.println s!"== regime sweep n={n} shapes={shapes.length} =="
  let mut seen : List String := []
  let mut flips := 0
  for salt in List.range 30 do
    let store := noiseStore salt
    for idx in List.range 3 do
      let rs := (shapes.map (fun s => regime (leaf s store idx))).eraseDups
      if rs.length != 1 then
        flips := flips + 1
        IO.println s!"  !! salt={salt} idx={idx} REGIME DIFFERS ACROSS SAME-SIZE SHAPES: {rs}"
      seen := (seen ++ rs).eraseDups
  IO.println s!"  regimes reachable by varying the STORE only: {seen}"
  IO.println s!"  regime differences caused by the SHAPE: {flips}"

-- Negative control: different sizes are allowed to differ.
def sA : CartesianShape :=
  CartesianShape.node CartesianShape.empty
    (CartesianShape.node CartesianShape.empty
      (CartesianShape.node CartesianShape.empty CartesianShape.empty))
def sB : CartesianShape :=
  CartesianShape.node
    (CartesianShape.node (CartesianShape.node CartesianShape.empty
      CartesianShape.empty) CartesianShape.empty) CartesianShape.empty
def sC : CartesianShape :=
  CartesianShape.node
    (CartesianShape.node CartesianShape.empty CartesianShape.empty)
    CartesianShape.empty

#eval show IO Unit from do
  let store := noiseStore 11
  IO.println s!"sA.size={sA.size} sB.size={sB.size} sC.size={sC.size}"
  IO.println s!"same size (3 vs 3) traces equal? {traceKey (leaf sA store 1) == traceKey (leaf sB store 1)}"
  IO.println s!"diff size (3 vs 2) traces equal? {traceKey (leaf sA store 1) == traceKey (leaf sC store 1)}"
  IO.println s!"  sA: {traceKey (leaf sA store 1)}"
  IO.println s!"  sC: {traceKey (leaf sC store 1)}"

end F6L1
