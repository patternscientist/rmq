import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import RMQ.Core.SuccinctRMQClassic
import Lean

/-!
ATTACK 3b: RAW `Expr.proj` scan.

A named-projection scan can miss compiler-generated raw structure projections.
This walks every expression in the value-only closure and reports every
`Expr.proj` whose structure is `TwoLevelPayloadLiveStoredWordRankData`, by field
INDEX, together with the constant it occurs in.

Field order (RMQ/Core/SuccinctRank.lean:761-810):
  0 wordSize            1 wordSize_pos        2 wordSize_le_machine
  3 blocksPerSuper      4 blocksPerSuper_pos  5 superWidth
  6 blockWidth          7 superTrueEntries    8 superFalseEntries
  9 blockTrueEntries   10 blockFalseEntries  11 superTables
 12 blockTables        13 bitWords           14.. proofs
-/

open Lean

namespace DPF2D

def isThm (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def valOf (env : Environment) (n : Name) : Option Expr :=
  if isThm env n then none
  else match env.find? n with
    | none => none
    | some ci => ci.value?

def valDeps (env : Environment) (n : Name) : List Name :=
  match valOf env n with
  | some v => v.foldConsts [] (fun c a => c :: a)
  | none => []

partial def clo (env : Environment) (seen : Std.HashSet Name) (acc : Array Name)
    : List Name -> Std.HashSet Name × Array Name
  | [] => (seen, acc)
  | n :: rest =>
      if seen.contains n then clo env seen acc rest
      else clo env (seen.insert n) (acc.push n) (valDeps env n ++ rest)

def structName : Name := `RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
def shapeName : Name := `RMQ.Cartesian.CartesianShape

/-- Collect raw projection field indices for a given structure inside `e`. -/
partial def projIdxs (target : Name) (e : Expr) (acc : Array Nat) : Array Nat :=
  match e with
  | .proj s i b =>
      let acc := if s == target then acc.push i else acc
      projIdxs target b acc
  | .app f a => projIdxs target a (projIdxs target f acc)
  | .lam _ t b _ => projIdxs target b (projIdxs target t acc)
  | .forallE _ t b _ => projIdxs target b (projIdxs target t acc)
  | .letE _ t v b _ => projIdxs target b (projIdxs target v (projIdxs target t acc))
  | .mdata _ b => projIdxs target b acc
  | _ => acc

def roots : List (String × Name) :=
  [ ("PUBLIC SuccinctClassic.queryTraceResultWithStore",
     `RMQ.SuccinctClassic.queryTraceResultWithStore),
    ("PUBLIC SuccinctClassic.queryTraceResult",
     `RMQ.SuccinctClassic.queryTraceResult),
    ("CONTROLLER store-param root",
     `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore),
    ("L3 rankClose",
     `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore) ]

run_cmd do
  let env <- Lean.getEnv
  for (label, r) in roots do
    match env.find? r with
    | none => Lean.logInfo m!"{label}: ROOT NOT FOUND ({r})"
    | some _ =>
      let cl := (clo env {} #[] [r]).2
      let mut hits : Array (Name × Nat) := #[]
      let mut shapeHits : Array Name := #[]
      for n in cl do
        match valOf env n with
        | none => pure ()
        | some v =>
            for i in projIdxs structName v #[] do
              hits := hits.push (n, i)
            if (projIdxs shapeName v #[]).size > 0 then
              shapeHits := shapeHits.push n
      Lean.logInfo m!"{label}: closure={cl.size} rawRankProjs={hits.size} rawShapeProjs={shapeHits.size}"
      for (n, i) in hits do Lean.logInfo m!"      rawproj field#{i} in {n}"

/-- Also: every constant in the store-param controller closure whose value
mentions `CartesianShape.bpCode` or `CartesianShape.size`. -/
run_cmd do
  let env <- Lean.getEnv
  let r := `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  let cl := (clo env {} #[] [r]).2
  let mut bp : Array Name := #[]
  let mut sz : Array Name := #[]
  for n in cl do
    let ds := valDeps env n
    if ds.contains `RMQ.Cartesian.CartesianShape.bpCode then bp := bp.push n
    if ds.contains `RMQ.Cartesian.CartesianShape.size then sz := sz.push n
  Lean.logInfo m!"controller closure={cl.size}  bpCode-users={bp.size}  size-users={sz.size}"
  for n in bp do Lean.logInfo m!"      bpCode <- {n}"
  for n in sz do Lean.logInfo m!"      size   <- {n}"

end DPF2D
