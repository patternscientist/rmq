import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.SuccinctFinal
import RMQ.Core.Shape
import Lean

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

/-! # ADVERSARIAL ATTACK part 2
    (a) exhaustive sweep with MY OWN enumerator (fuel-structural, no sorry)
    (b) independent value-only reachability BFS from the PUBLIC ENTRY -/

/-! ## (a) exhaustive sweep -/

def advShapesF : Nat -> Nat -> List CartesianShape
  | 0, _ => []
  | _ + 1, 0 => [CartesianShape.empty]
  | fuel + 1, n + 1 =>
      (List.range (n + 1)).flatMap (fun k =>
        (advShapesF fuel k).flatMap (fun l =>
          (advShapesF fuel (n - k)).map (fun r => CartesianShape.node l r)))

def advShapes (n : Nat) : List CartesianShape := advShapesF (n + 1) n

def advSuper (s : CartesianShape) : Nat :=
  builtRelativeSplitBPCloseRankSuperOverhead s
def advBlock (s : CartesianShape) : Nat :=
  builtRelativeSplitBPCloseRankBlockOverhead s

def advSuperClosed (n : Nat) : Nat :=
  let m := 2 * n
  let w := SuccinctRank.machineWordBits m
  (m / w / w + 1) * w + (m / w / w + 1) * w

def advBlockClosed (n : Nat) : Nat :=
  let m := 2 * n
  let w := SuccinctRank.machineWordBits m
  let bw := SuccinctRank.machineWordBits (w * w)
  (m / w + 1) * bw + (m / w + 1) * bw

def advDedup {a : Type} [BEq a] (l : List a) : List a :=
  l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- (n, #shapes, #distinct bpCodes, distinct super vals, distinct block vals,
     closed-form (super,block), ALL-MATCH-CLOSED-FORM?) -/
def advSweep (n : Nat) :
    Nat × Nat × Nat × List Nat × List Nat × (Nat × Nat) × Bool :=
  let ss := advShapes n
  let ok := ss.all (fun s =>
    s.size == n && advSuper s == advSuperClosed n && advBlock s == advBlockClosed n)
  (n, ss.length, (advDedup (ss.map CartesianShape.bpCode)).length,
   advDedup (ss.map advSuper), advDedup (ss.map advBlock),
   (advSuperClosed n, advBlockClosed n), ok)

#eval advSweep 0
#eval advSweep 1
#eval advSweep 2
#eval advSweep 3
#eval advSweep 4
#eval advSweep 5
#eval advSweep 6
#eval advSweep 7
#eval advSweep 8
#eval advSweep 9
#eval advSweep 10

/-! ## (b) independent reachability BFS, value-only, parent-tracked. -/

open Lean

/-- Constants appearing in the definitional VALUE of `n`.
    Theorems are skipped entirely (proof terms cannot influence an address). -/
def advValueDeps (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | some (.thmInfo _) => #[]
  | some ci =>
      match ci.value? with
      | some e => e.getUsedConstants
      | none => #[]
  | none => #[]

/-- BFS with parent map; returns shortest chain start -> target, or none. -/
partial def advPath (env : Environment) (start : Name) (target : Name) :
    Option (List Name) :=
  let rec go (frontier : List Name) (seen : Std.HashSet Name)
      (parent : Std.HashMap Name Name) (fuel : Nat) :
      Option (Std.HashMap Name Name) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      if frontier.isEmpty then none
      else
        let (next, seen, parent) :=
          frontier.foldl
            (fun (acc : List Name × Std.HashSet Name × Std.HashMap Name Name) c =>
              let (nx, sn, pr) := acc
              (advValueDeps env c).foldl
                (fun (acc2 : List Name × Std.HashSet Name × Std.HashMap Name Name) d =>
                  let (nx2, sn2, pr2) := acc2
                  if sn2.contains d then acc2
                  else (d :: nx2, sn2.insert d, pr2.insert d c))
                (nx, sn, pr))
            ([], seen, parent)
        if seen.contains target then some parent
        else go next seen parent fuel
  match go [start] (Std.HashSet.emptyWithCapacity.insert start)
      (Std.HashMap.emptyWithCapacity) 200 with
  | none => none
  | some parent =>
      let rec build (cur : Name) (acc : List Name) (fuel : Nat) : List Name :=
        match fuel with
        | 0 => acc
        | fuel + 1 =>
            if cur == start then start :: acc
            else match parent[cur]? with
              | some p => build p (cur :: acc) fuel
              | none => cur :: acc
      some (build target [] 200)

def advTargets : List Name :=
  [``RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead,
   ``RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead]

def advStarts : List Name :=
  [``RMQ.SuccinctRMQClassic.queryTraceResultWithStore,
   ``RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore,
   ``RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram,
   ``RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
   ``RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore]

elab "adv_reach" : command => do
  let env <- Lean.getEnv
  for s in advStarts do
    for t in advTargets do
      match advPath env s t with
      | none => logInfo m!"UNREACHABLE: {s}  -/->  {t}"
      | some p =>
          logInfo m!"REACHABLE (depth {p.length - 1}): {s}\n  chain: {p}"

adv_reach
