import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 precision measurement, corrected.

`dpw_diff_c/d.lean` compared the two instantiations with `Lean.Meta.isDefEq`.
That was WRONG in the differing direction: `isDefEq` may answer `false`
without deciding the question (approximation, recursion depth), and it did --
it reported `builtRelativeSplitBPCloseRankSuperOverhead` and
`builtRelativeSplitBPCloseRankBlockOverhead` as differing when both sides in
fact normalise to the same literal.

Here both sides are fully normalised with `Lean.Meta.reduce` and the normal
forms are compared, each probe under its own heartbeat budget (heartbeat
exhaustion is a runtime exception, so `Core.tryCatchRuntimeEx` is needed to
survive it).  A DIFFER verdict now rests on two literal normal forms that are
textually different.
-/

open Lean Lean.Meta

namespace DPWDiffG

open RMQ.Cartesian

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node (leftSpine k) CartesianShape.empty

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | k + 1 => CartesianShape.node CartesianShape.empty (rightSpine k)

partial def reify : CartesianShape -> Expr
  | CartesianShape.empty => mkConst `RMQ.Cartesian.CartesianShape.empty
  | CartesianShape.node l r =>
      mkApp2 (mkConst `RMQ.Cartesian.CartesianShape.node) (reify l) (reify r)

def taintedNames : List Name := [
  `RMQ.SuccinctClose.bpExcessAt,
  `RMQ.SuccinctClose.bpBlockExcessSamples,
  `RMQ.SuccinctClose.bpBlockMinExcess,
  `RMQ.SuccinctClose.bpBlockMaxExcess,
  `RMQ.SuccinctClose.bpBlockRelativeMinExcess,
  `RMQ.SuccinctClose.bpBlockRelativeMaxExcess,
  `RMQ.SuccinctClose.bpRelativeExcessEntry,
  `RMQ.SuccinctClose.bpBlockArgMinPrefixPos,
  `RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom,
  `RMQ.SuccinctClose.bpBlockArgMinLocalOffset,
  `RMQ.SuccinctClose.bpBetterArgMinBlock,
  `RMQ.SuccinctClose.bpRangeArgMinBlockFrom,
  `RMQ.SuccinctClose.bpRangeArgMinBlock,
  `RMQ.SuccinctClose.bpSuperblockBaselineEntries,
  `RMQ.SuccinctClose.bpBlockRelativeMinExcessEntries,
  `RMQ.SuccinctClose.bpBlockRelativeMaxExcessEntries,
  `RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangeMinComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineMinCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineAdjacentMacroCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineGlobalSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineCrossMacroCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets,
  `RMQ.SuccinctClose.canonicalRelativeRmmSummaryTable,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorLocalTable,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorGlobalTable,
  `RMQ.SuccinctClose.canonicalRelativeRmmLocalMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmGlobalMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmSummaryMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentStore
]

def grids : Nat -> List (List Nat)
  | 0 => [[]]
  | 1 => [[0],[1],[2],[3],[4],[5]]
  | 2 => [[2,0],[2,1],[4,0],[4,1],[1,0],[1,1],[1,2],[1,3],[2,2],[3,0],[3,1]]
  | 3 => [[2,0,1],[2,0,2],[4,0,1],[2,1,2],[1,0,1],[2,0,3],[0,1,2],[1,1,2],[2,1,0],[1,4,2],[2,1,4]]
  | 4 => [[2,0,1,1],[4,0,1,2],[2,0,2,1],[1,0,1,1],[2,1,1,2],[1,0,4,2],[2,0,4,1]]
  | _ => []

def isNatTy (e : Expr) : Bool := e.isConstOf `Nat

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/dpw_diff_g_out.txt"

def guarded {α : Type} (x : MetaM α) (fallback : MetaM α) : MetaM α :=
  controlAt CoreM fun runInBase =>
    Core.tryCatchRuntimeEx (runInBase x) (fun _ => runInBase fallback)

def norm (e : Expr) : MetaM (Option String) :=
  withCurrHeartbeats <|
    guarded (do
      let v <- Lean.Meta.reduce e (explicitOnly := true) (skipTypes := true) (skipProofs := true)
      pure (some (toString v)))
      (pure none)

set_option maxHeartbeats 200000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env <- getEnv
  let sz := 5
  let s1 := reify (leftSpine sz)
  let s2 := reify (rightSpine sz)
  let mut lines : Array String := #[]
  lines := lines.push s!"s1 = leftSpine {sz}, s2 = rightSpine {sz}; equal bpCode length, different bpCode"
  IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
  let mut nDiff := 0
  let mut nSame := 0
  let mut nBudget := 0
  let mut nSkip := 0
  for nm in taintedNames do
    match env.find? nm with
    | none => lines := lines.push s!"MISSING {nm}"
    | some ci =>
      let rec peel : Expr -> List Expr -> List Expr
        | .forallE _ t b _, acc => peel b (t :: acc)
        | _, acc => acc.reverse
      let binders := peel ci.type []
      match binders with
      | [] => nSkip := nSkip + 1; lines := lines.push s!"SKIP(nullary) {nm}"
      | hd :: tl =>
        if !hd.isConstOf `RMQ.Cartesian.CartesianShape then
          nSkip := nSkip + 1
          lines := lines.push s!"SKIP(first-arg-not-shape) {nm}"
        else if !(tl.all isNatTy) then
          nSkip := nSkip + 1
          lines := lines.push s!"SKIP(non-Nat-args) {nm} arity={tl.length}"
        else
          let g := grids tl.length
          if g.isEmpty then
            nSkip := nSkip + 1
            lines := lines.push s!"SKIP(high-arity) {nm} arity={tl.length}"
          else
            let f := mkConst nm (ci.levelParams.map (fun _ => Level.zero))
            let mut verdict : Option (List Nat × String × String) := none
            let mut anyDecided := false
            let mut misses := 0
            for args in g do
              if verdict.isSome then continue
              let a := (args.map (fun k => mkNatLit k)).toArray
              let r1 <- norm (mkAppN f (#[s1] ++ a))
              let r2 <- norm (mkAppN f (#[s2] ++ a))
              match r1, r2 with
              | some v1, some v2 =>
                  anyDecided := true
                  if v1 != v2 then verdict := some (args, v1, v2)
              | _, _ => misses := misses + 1
            match verdict with
            | some (args, v1, v2) =>
                nDiff := nDiff + 1
                let cap (s : String) := if s.length > 200 then s.take 200 ++ " ..." else s
                lines := lines.push s!"DIFFER {nm}  args={args}"
                lines := lines.push s!"    s1 = {cap v1}"
                lines := lines.push s!"    s2 = {cap v2}"
            | none =>
                if anyDecided then
                  nSame := nSame + 1
                  lines := lines.push s!"SAME   {nm} arity={tl.length} budgetMisses={misses}"
                else
                  nBudget := nBudget + 1
                  lines := lines.push s!"BUDGET {nm} arity={tl.length}"
    IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
  lines := lines.push ""
  lines := lines.push s!"DIFFER={nDiff} SAME={nSame} BUDGET={nBudget} SKIP={nSkip}"
  IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"differ={nDiff} same={nSame} budget={nBudget} skip={nSkip}"

end DPWDiffG
