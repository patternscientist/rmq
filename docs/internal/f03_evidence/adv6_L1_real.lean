import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL C: correctness anti-vacuity of the "shape argument is inert" claim.

If leaf X (realStore A) idx returns the CORRECT selectClose answer for A while
X ranges over every shape of the same size, and the correct answers genuinely
DIFFER across those shapes, then the answer provably tracks the STORE (probe
replies), not the shape argument.  If instead the leaf returns `none`, or all
same-size shapes share the same answer, the prior agent's whole sweep is vacuous.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace Adv6R

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

/-- Position (0-based) of the `(i+1)`-st `false` in `bits`, computed directly. -/
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

def addrTrace (r : WordRAM.TraceResult (Option Nat)) : String :=
  String.intercalate ";" (r.trace.map evKey)

/-! C0 -/
#eval show IO Unit from do
  IO.println "== C0. self-consistency: leaf S (realStore S) idx  vs  true selectClose =="
  for n in [1, 2, 3, 4, 5] do
    let shapes := shapesOfSize n
    let mut bad := 0
    let mut good := 0
    let mut nones := 0
    for s in shapes do
      for idx in List.range n do
        let got := (leaf s (concreteBPNativeSuccinctRMQGlobalReadStore s) idx).value
        let want := trueSel s.bpCode idx
        if got == want then good := good + 1
        else
          bad := bad + 1
          if bad <= 3 then
            IO.println s!"    MISMATCH n={n} bp={s.bpCode} idx={idx} got={got} want={want}"
        if got == none then nones := nones + 1
    IO.println s!"  n={n} shapes={shapes.length} CORRECT={good} WRONG={bad} (of which value=none: {nones})"

/-! C1 -/
#eval show IO Unit from do
  IO.println "== C1. cross: leaf X (realStore A) idx  ==  trueSel A.bpCode idx  for ALL X of |A| =="
  for n in [3, 4, 5] do
    let shapes := shapesOfSize n
    for ai in List.range shapes.length do
      let a := shapes.getD ai CartesianShape.empty
      let store := concreteBPNativeSuccinctRMQGlobalReadStore a
      let mut tracksStore := 0
      let mut tracksShapeArg := 0
      let mut other := 0
      let mut distinctTrueAnswers : List (Option Nat) := []
      for idx in List.range n do
        let wantA := trueSel a.bpCode idx
        for x in shapes do
          let got := (leaf x store idx).value
          let wantX := trueSel x.bpCode idx
          distinctTrueAnswers := (distinctTrueAnswers ++ [wantX]).eraseDups
          if got == wantA then tracksStore := tracksStore + 1
          else if got == wantX then tracksShapeArg := tracksShapeArg + 1
          else other := other + 1
      if ai == 0 || ai + 1 == shapes.length then
        IO.println s!"  n={n} storeShape#{ai} bp={a.bpCode}: answers-track-STORE={tracksStore} track-SHAPE-ARG-instead={tracksShapeArg} neither={other} distinctTrueAnswersAcrossShapes={distinctTrueAnswers.length}"

/-! C2 -/
#eval show IO Unit from do
  IO.println "== C2. anti-vacuity: do same-size shapes disagree on selectClose? =="
  for n in [3, 4, 5] do
    let shapes := shapesOfSize n
    for idx in List.range n do
      let answers := (shapes.map (fun s => trueSel s.bpCode idx)).eraseDups
      IO.println s!"  n={n} idx={idx} distinct TRUE selectClose answers over {shapes.length} shapes = {answers.length} : {answers}"

/-! C3 -/
#eval show IO Unit from do
  IO.println "== C3. address traces under realStore(A), shape argument varied =="
  for n in [4, 5] do
    let shapes := shapesOfSize n
    let a := shapes.headD CartesianShape.empty
    let store := concreteBPNativeSuccinctRMQGlobalReadStore a
    let mut mism := 0
    for idx in List.range n do
      let ts := (shapes.map (fun x => addrTrace (leaf x store idx))).eraseDups
      if ts.length != 1 then mism := mism + 1
    IO.println s!"  n={n} idxs={n} idxs-with-differing-address-traces={mism}"
    IO.println s!"    sample trace n={n} idx=1: {addrTrace (leaf a store 1)}"

end Adv6R
