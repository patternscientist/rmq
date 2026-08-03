import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
F03 precision measurement, budgeted.

Same probe as `dpw_diff_c.lean`, but each probe gets its own heartbeat budget
AND the budget exception is caught (heartbeat exhaustion is a runtime
exception, so plain `try`/`catch` rethrows it; `Core.tryCatchRuntimeEx` is
needed).  Results are flushed after every candidate so a hang still leaves a
usable transcript.
-/

open Lean Lean.Meta

namespace DPWDiffD

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
  `RMQ.SuccinctClose.bpLocalSparseCellOffset,
  `RMQ.SuccinctClose.bpGlobalSparseCellBlock,
  `RMQ.SuccinctClose.bpBetterArgMinBlock,
  `RMQ.SuccinctClose.bpRangeArgMinBlockFrom,
  `RMQ.SuccinctClose.bpRangeArgMinBlock,
  `RMQ.SuccinctClose.bpSuperblockBaselineEntries,
  `RMQ.SuccinctClose.bpBlockRelativeMinExcessEntries,
  `RMQ.SuccinctClose.bpBlockRelativeMaxExcessEntries,
  `RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries,
  `RMQ.SuccinctClose.bpLocalSparseOffsetEntries,
  `RMQ.SuccinctClose.bpGlobalSparseBlockEntries,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead,
  `RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData,
  `RMQ.SuccinctClose.concreteBPLocalSparseOffsetTable,
  `RMQ.SuccinctClose.concreteBPGlobalSparseBlockTable,
  `RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable,
  `RMQ.SuccinctClose.canonicalRelativeRmmSummaryTable,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorLocalTable,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorGlobalTable,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets,
  `RMQ.SuccinctClose.canonicalRelativeRmmLocalMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmGlobalMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmSummaryMachineStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentStore,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineReadNatComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangeMinComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineMinCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineAdjacentMacroCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineGlobalSpanCandidateComputation,
  `RMQ.SuccinctClose.canonicalRelativeRmmMachineCrossMacroCandidateComputation
]

def grids : Nat -> List (List Nat)
  | 0 => [[]]
  | 1 => [[0],[1],[2],[3],[4],[5]]
  | 2 => [[2,0],[2,1],[4,0],[4,1],[1,0],[3,0],[1,1],[2,2]]
  | 3 => [[2,0,1],[2,0,2],[4,0,1],[2,1,2],[1,0,1],[2,0,3]]
  | 4 => [[2,0,1,1],[4,0,1,2],[2,0,2,1],[1,0,1,1],[2,1,1,2]]
  | _ => []

def isNatTy (e : Expr) : Bool := e.isConstOf `Nat

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/dpw_diff_d_out.txt"

def guarded {α : Type} (x : MetaM α) (fallback : MetaM α) : MetaM α :=
  controlAt CoreM fun runInBase =>
    Core.tryCatchRuntimeEx (runInBase x) (fun _ => runInBase fallback)

/-- `some true` = definitely different, `some false` = definitely the same,
    `none` = out of budget. -/
def probe (e1 e2 : Expr) : MetaM (Option Bool) :=
  withCurrHeartbeats <|
    guarded (do
      let same <- Lean.Meta.isDefEq e1 e2
      pure (some (! same)))
      (pure none)

set_option maxHeartbeats 60000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env <- getEnv
  let sz := 5
  let s1 := reify (leftSpine sz)
  let s2 := reify (rightSpine sz)
  let mut lines : Array String := #[]
  lines := lines.push s!"s1 = leftSpine {sz}, s2 = rightSpine {sz}"
  let bp (s : Expr) := mkApp (mkConst `RMQ.Cartesian.CartesianShape.bpCode) s
  let b1 <- Lean.Meta.reduce (bp s1) true true true
  let b2 <- Lean.Meta.reduce (bp s2) true true true
  lines := lines.push s!"bpCode s1 = {b1}"
  lines := lines.push s!"bpCode s2 = {b2}"
  lines := lines.push ""
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
            let mut verdict : Option (List Nat) := none
            let mut anyDecided := false
            let mut nBudgetHere := 0
            for args in g do
              if verdict.isSome then continue
              let a := (args.map (fun k => mkNatLit k)).toArray
              let r <- probe (mkAppN f (#[s1] ++ a)) (mkAppN f (#[s2] ++ a))
              match r with
              | some true  => anyDecided := true; verdict := some args
              | some false => anyDecided := true
              | none => nBudgetHere := nBudgetHere + 1
            match verdict with
            | some args =>
                nDiff := nDiff + 1
                lines := lines.push s!"NOTDEFEQ {nm}  witness args={args}"
            | none =>
                if anyDecided then
                  nSame := nSame + 1
                  lines := lines.push s!"DEFEQ    {nm} arity={tl.length} budgetMisses={nBudgetHere}"
                else
                  nBudget := nBudget + 1
                  lines := lines.push s!"BUDGET   {nm} arity={tl.length}"
    IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
  lines := lines.push ""
  lines := lines.push s!"NOTDEFEQ={nDiff} DEFEQ={nSame} BUDGET={nBudget} SKIP={nSkip}"
  IO.FS.writeFile outPath (String.intercalate "\n" lines.toList)
  Lean.logInfo m!"notDefEq={nDiff} defEq={nSame} budget={nBudget} skip={nSkip}"

end DPWDiffD
