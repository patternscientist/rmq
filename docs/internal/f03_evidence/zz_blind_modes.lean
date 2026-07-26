import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
Empirical characterisation of `countUnderLength`'s failure modes.

We construct real definitions exhibiting each suspect pattern and run the
coordinator's EXACT algorithm on them, so the verdicts are executed, not
reasoned about.
-/

open Lean
open RMQ.Cartesian

namespace ZZModes

/-! ## Test fixtures: each is a real compiled definition. -/

/-- P1: let-bound bpCode, then length. Semantically SIZE-ONLY. -/
def p1_letLength (s : CartesianShape) : Nat :=
  let bits := s.bpCode
  bits.length

/-- P2 callee: takes a bit list, reads CONTENTS. Contains no bpCode. -/
def p2_callee (bits : List Bool) : Bool :=
  bits.getD 3 false

/-- P2 caller: feeds bpCode into the content-reading callee. -/
def p2_caller (s : CartesianShape) : Bool :=
  p2_callee s.bpCode

/-- P3 record: content routed through a structure field. -/
structure P3Rec where
  bits : List Bool
  tag : Nat

/-- P3 builder: builds the record from bpCode. -/
def p3_build (s : CartesianShape) : P3Rec :=
  { bits := s.bpCode, tag := 0 }

/-- P3 consumer: projects the field and reads CONTENTS. No bpCode present. -/
def p3_consume (r : P3Rec) : Bool :=
  r.bits.getD 3 false

/-- P3 top: the full content read, via the record. -/
def p3_top (s : CartesianShape) : Bool :=
  p3_consume (p3_build s)

/-- P4: length of a TRANSFORMED bpCode. Semantically size-only, head is drop. -/
def p4_lengthOfDrop (s : CartesianShape) (k : Nat) : Nat :=
  (s.bpCode.drop k).length

/-- P5: plain length. Size-only. -/
def p5_plainLength (s : CartesianShape) : Nat :=
  s.bpCode.length

/-- P6: bpCode passed as an unapplied function (eta-reduced). -/
def p6_etaFunction : CartesianShape -> List Bool :=
  CartesianShape.bpCode

/-- P7: length via the tail-recursive length, not `List.length`. Size-only. -/
def p7_lengthTR (s : CartesianShape) : Nat :=
  List.lengthTR s.bpCode

/-- P8: one length use AND one genuine content read. -/
def p8_mixed (s : CartesianShape) : Nat :=
  if s.bpCode.getD 0 false then s.bpCode.length else 0

/-- P9: length of bpCode reached through a let-bound INTERMEDIATE FUNCTION. -/
def p9_indirect (s : CartesianShape) : Bool :=
  let f := fun (bits : List Bool) => bits.getD 3 false
  f s.bpCode

/-! ## The coordinator's exact algorithm, copied verbatim. -/

def bpCodeN : Name := `RMQ.Cartesian.CartesianShape.bpCode
def lengthN : Name := `List.length

partial def countUnderLength (target : Name) : Expr -> Nat × Nat
  | e@(.app _ _) =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const c _ =>
          if c == lengthN then
            let inner := args.findSome? (fun a =>
              if a.getAppFn.isConstOf target then some a else none)
            match inner with
            | some innerArg =>
                let sub := innerArg.getAppArgs.foldl
                  (fun (acc : Nat × Nat) a =>
                    let r := countUnderLength target a
                    (acc.1 + r.1, acc.2 + r.2)) (0, 0)
                let others := args.foldl (fun (acc : Nat × Nat) a =>
                  if a == innerArg then acc
                  else
                    let r := countUnderLength target a
                    (acc.1 + r.1, acc.2 + r.2)) (0, 0)
                (sub.1 + others.1 + 1, sub.2 + others.2 + 1)
            | none =>
                args.foldl (fun (acc : Nat × Nat) a =>
                  let r := countUnderLength target a
                  (acc.1 + r.1, acc.2 + r.2)) (0, 0)
          else
            let here := if c == target then 1 else 0
            args.foldl (fun (acc : Nat × Nat) a =>
              let r := countUnderLength target a
              (acc.1 + r.1, acc.2 + r.2)) (here, 0)
      | _ =>
          let r0 := countUnderLength target fn
          args.foldl (fun (acc : Nat × Nat) a =>
            let r := countUnderLength target a
            (acc.1 + r.1, acc.2 + r.2)) r0
  | .lam _ t b _ =>
      let a := countUnderLength target t
      let b' := countUnderLength target b
      (a.1 + b'.1, a.2 + b'.2)
  | .forallE _ t b _ =>
      let a := countUnderLength target t
      let b' := countUnderLength target b
      (a.1 + b'.1, a.2 + b'.2)
  | .letE _ t v b _ =>
      let a := countUnderLength target t
      let b' := countUnderLength target v
      let c := countUnderLength target b
      (a.1 + b'.1 + c.1, a.2 + b'.2 + c.2)
  | .mdata _ e => countUnderLength target e
  | .proj _ _ e => countUnderLength target e
  | .const c _ => (if c == target then 1 else 0, 0)
  | _ => (0, 0)

/-- Ground truth, stated by hand for each fixture. -/
def truth : List (Name × String) := [
  (`ZZModes.p1_letLength,   "SIZE-ONLY"),
  (`ZZModes.p2_callee,      "CONTENT-READ (no bpCode present)"),
  (`ZZModes.p2_caller,      "CONTENT-READ"),
  (`ZZModes.p3_build,       "BUILDS content into a record"),
  (`ZZModes.p3_consume,     "CONTENT-READ (no bpCode present)"),
  (`ZZModes.p3_top,         "CONTENT-READ"),
  (`ZZModes.p4_lengthOfDrop,"SIZE-ONLY"),
  (`ZZModes.p5_plainLength, "SIZE-ONLY"),
  (`ZZModes.p6_etaFunction, "CONTENT (identity on the channel)"),
  (`ZZModes.p7_lengthTR,    "SIZE-ONLY"),
  (`ZZModes.p8_mixed,       "CONTENT-READ"),
  (`ZZModes.p9_indirect,    "CONTENT-READ")
]

run_cmd do
  let env <- Lean.getEnv
  let mut lines : Array String := #[]
  lines := lines.push "PATTERN | tot | under | INSTRUMENT VERDICT | GROUND TRUTH | AGREE?"
  for (n, gt) in truth do
    match (env.find? n).bind (fun ci => ci.value?) with
    | none => lines := lines.push s!"{n} :: NO VALUE"
    | some v =>
      let (tot, under) := countUnderLength bpCodeN v
      let verdict :=
        if tot == 0 then "INVISIBLE (not listed at all)"
        else if tot == under then "LENGTH-ONLY (benign)"
        else "CONTENT (frontier row)"
      let gtContent := gt.startsWith "CONTENT" || gt.startsWith "BUILDS"
      let instContent := (tot != 0 && tot != under)
      let agree :=
        if gtContent == instContent then "ok"
        else if gtContent && !instContent then "*** FALSE CLEAN ***"
        else "false alarm (safe)"
      lines := lines.push
        s!"{n} | {tot} | {under} | {verdict} | {gt} | {agree}"
  IO.FS.writeFile
    "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/zz_blind_modes_out.txt"
    (String.intercalate "\n" lines.toList)
  for l in lines do Lean.logInfo l

end ZZModes
