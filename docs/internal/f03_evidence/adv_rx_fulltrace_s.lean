import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION, attack #2: the defender's behavioural evidence is a
PROJECTION that throws away exactly the channel where a shape-content leak
would appear.

`concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore`
(RMQ/Core/SuccinctFinalStoreParam.lean:2441-2450) is

    trace.filterMap fun event => match event with
      | readWord segment index _ => some (segment, index)
      | _ => none

so it DISCARDS
  * the `word?` payload of every readWord event,
  * every `WordRAM.TraceEvent.wordRank target limit result` event,
  * every `WordRAM.TraceEvent.wordSelect target occurrence result` event,
  * every `syntheticCostOnlyPrimitive` marker.

`bpExcessAt` (RangeSummary.lean:25-27) is literally
  `Succinct.rankPrefix true shape.bpCode pos - Succinct.rankPrefix false shape.bpCode pos`,
i.e. a RANK over shape CONTENT.  If any such rank is emitted as a counted
`wordRank` event, the full trace differs across shapes of equal size while the
defender's footprint stays byte-identical.  `.value` would also stay equal if the
leak only moves the cost.

Here I compare the FULL `TraceResult` -- every event with all its fields, plus
the step count -- across shapes of equal size and maximally different bpCode.
TraceEvent derives DecidableEq, so this is an exact comparison.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvRxFullS

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

partial def zigzag (goLeft : Bool) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      if goLeft then CartesianShape.node (zigzag false n) CartesianShape.empty
      else CartesianShape.node CartesianShape.empty (zigzag true n)

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      CartesianShape.node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def flatStore (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun _ _ => some w

def addrStore (k : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 16).map fun j => ((seg * 7 + idx * 13 + j * 5 + k) % 3 == 0))

/-- store whose replies are wrong-length / missing at some addresses -/
def partialStore : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    if (seg + idx) % 5 == 0 then none
    else some ((List.range ((seg + idx) % 9 + 1)).map fun j => (j % 2 == 0))

def word0 : List Bool := [true, false, true, false, true, false, true, false]

def res (shape : CartesianShape) (store : WordRAM.ReadStore) (l r : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore shape store l r

def fullTrace (shape : CartesianShape) (store : WordRAM.ReadStore) (l r : Nat) :
    List WordRAM.TraceEvent := (res shape store l r).trace

def footprint (shape : CartesianShape) (store : WordRAM.ReadStore) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore shape store l r

/-- census of event kinds actually present in a trace -/
def kindCensus (t : List WordRAM.TraceEvent) : Nat × Nat × Nat × Nat :=
  t.foldl (fun (a : Nat × Nat × Nat × Nat) e =>
    match e with
    | WordRAM.TraceEvent.readWord _ _ _ => (a.1 + 1, a.2.1, a.2.2.1, a.2.2.2)
    | WordRAM.TraceEvent.wordRank _ _ _ => (a.1, a.2.1 + 1, a.2.2.1, a.2.2.2)
    | WordRAM.TraceEvent.wordSelect _ _ _ => (a.1, a.2.1, a.2.2.1 + 1, a.2.2.2)
    | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => (a.1, a.2.1, a.2.2.1, a.2.2.2 + 1))
    (0, 0, 0, 0)

def family (n : Nat) : List (String × CartesianShape) :=
  [("leftSpine", leftSpine n),
   ("rightSpine", rightSpine n),
   ("balanced", balanced n),
   ("zigzagL", zigzag true n),
   ("pseudo3", pseudo 3 n),
   ("pseudo11", pseudo 11 n)]

def report (label : String) (n : Nat) (store : WordRAM.ReadStore) (l r : Nat) :
    IO Unit := do
  let fam := family n
  match fam with
  | [] => pure ()
  | (lbl0, s0) :: _ =>
    let t0 := fullTrace s0 store l r
    let f0 := footprint s0 store l r
    let v0 := (res s0 store l r).value
    let mut fullD := 0
    let mut fpD := 0
    let mut vD := 0
    let mut costD := 0
    let mut msgs : List String := []
    for (lbl, s) in fam do
      let t := fullTrace s store l r
      if t != t0 then
        fullD := fullD + 1
        -- locate the first differing event
        let z := (t.zip t0).findIdx? (fun p => p.1 != p.2)
        msgs := s!"FULLTRACE_DIFF {lbl} vs {lbl0} firstDiffIdx={z} len={t.length}/{t0.length}" :: msgs
      if footprint s store l r != f0 then fpD := fpD + 1
      if (res s store l r).value != v0 then vD := vD + 1
      if t.length != t0.length then costD := costD + 1
    let (rw, wr, ws, sy) := kindCensus t0
    IO.println s!"{label} n={n} l={l} r={r} | events={t0.length} (readWord={rw} wordRank={wr} wordSelect={ws} synth={sy}) fpLen={f0.length} | FULLTRACE_DIFFERS={fullD} footprintDiffers={fpD} valueDiffers={vD} costDiffers={costD}"
    for m in msgs.reverse do IO.println s!"    {m}"

#eval show IO Unit from do
  IO.println "=== attack #2: FULL trace comparison (not the read-only projection) ==="
  for n in [4, 8, 16, 32] do
    report "FLAT " n (flatStore word0) 0 n
    report "ADDR " n (addrStore 1) 0 n
    report "PART " n partialStore 0 n
    report "MID  " n (addrStore 5) (n / 3) (2 * n / 3)

end AdvRxFullS
