import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 / F2 anti-vacuity + reachability.

(1) Reachability of `builtRelativeSplitBPCloseRankData` from each controller
    leaf L1 / L2 / L3 and from the whole-query root, by value-only closure.
(2) The L3 leaf is a genuine probing computation: non-empty trace, and its
    ADDRESS STREAM does change with `shape.size` (so `L3_leaf_size_only` is not
    the trivial "leaf ignores shape" statement), while it does NOT change
    across distinct shapes of the same size.
(3) Axiom audit of the decisive theorem.
-/

open Lean

namespace F03F2AV

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

/-! ## (1) reachability -/

def isTheorem (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => true
  | _ => false

def compDeps (env : Environment) (n : Name) : List Name :=
  if isTheorem env n then []
  else
    match env.find? n with
    | none => []
    | some ci =>
        match ci.value? with
        | some v => v.foldConsts [] (fun c a => c :: a)
        | none => []

partial def closureAux (env : Environment) (seen : Std.HashSet Name)
    : List Name -> Std.HashSet Name
  | [] => seen
  | n :: rest =>
      if seen.contains n then closureAux env seen rest
      else closureAux env (seen.insert n) (compDeps env n ++ rest)

def target : Name := `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData

run_cmd do
  let env <- Lean.getEnv
  let roots : List (String × Name) :=
    [ ("L1-selectClose",
       `RMQ.SuccinctFinal.concreteBPNativeSelectCloseGlobalWordTraceResultWithStore),
      ("L2-lcaClose",
       `RMQ.SuccinctFinal.concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore),
      ("L3-rankClose",
       `RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore),
      ("WHOLE-QUERY-ROOT",
       `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore) ]
  for (label, r) in roots do
    let cl := closureAux env {} [r]
    Lean.logInfo m!"{label}: closure={cl.size} containsF2={cl.contains target}"

/-! ## (2) anti-vacuity -/

def E : CartesianShape := .empty
def N (l r : CartesianShape) : CartesianShape := .node l r

/-- All five shapes of size 3. -/
def size3 : List CartesianShape :=
  [ N (N (N E E) E) E,
    N (N E (N E E)) E,
    N (N E E) (N E E),
    N E (N (N E E) E),
    N E (N E (N E E)) ]

def size4 : CartesianShape := N (N (N (N E E) E) E) E

/-- A fixed, shape-free read store. -/
def fixedStore : WordRAM.ReadStore where
  readWord? seg i :=
    some (List.replicate 6 (decide ((seg * 7 + i * 3) % 5 < 2)))

def addrStream (t : WordRAM.TraceResult Nat) : List (Nat × Nat) :=
  t.trace.filterMap fun ev =>
    match ev with
    | .readWord seg i _ => some (seg, i)
    | _ => none

def leaf (s : CartesianShape) (pos : Nat) : WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    s fixedStore 17 pos

-- sizes: sanity
#eval size3.map CartesianShape.size
#eval size3.map (fun s => s.bpCode)
#eval size4.size

-- all five size-3 shapes: identical value, identical address stream
#eval size3.map (fun s => (leaf s 5).value)
#eval size3.map (fun s => (leaf s 5).trace.length)
#eval size3.map (fun s => addrStream (leaf s 5))
#eval (size3.map (fun s => addrStream (leaf s 5))).eraseDups.length

-- the leaf is NOT shape-blind: a different SIZE gives a different address stream
#eval addrStream (leaf (N (N (N E E) E) E) 5)
#eval addrStream (leaf size4 5)
#eval addrStream (leaf (N (N (N E E) E) E) 5) == addrStream (leaf size4 5)

-- the leaf is NOT store-blind either: it really reads the supplied store
def otherStore : WordRAM.ReadStore where
  readWord? _ _ := some [true, true, true, false, false, false]

#eval (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        (N (N (N E E) E) E) fixedStore 17 5).value
#eval (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        (N (N (N E E) E) E) otherStore 17 5).value

end F03F2AV
