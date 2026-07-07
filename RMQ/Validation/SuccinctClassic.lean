import RMQ.Core.SuccinctRMQClassic

/-!
# Executable validation for the classic public succinct RMQ API

This module is an executable differential harness.  It computes
`SuccinctClassic.queryCosted xs left right` directly and compares its erased
answer with the independent linear `scanWindow` kernel on deterministic small
inputs and all nonempty valid windows.
-/

namespace RMQ.Validation.SuccinctClassic

structure Mismatch where
  xs : List Int
  left : Nat
  right : Nat
  got : Option Nat
  expected : Option Nat
deriving Repr

def generatedInput (len seed : Nat) : List Int :=
  (List.range len).map fun i =>
    Int.ofNat ((seed * 5 + len * 3 + i * i + 2 * i) % 7) - 3

def tieInputs : List (List Int) :=
  [[],
    [0],
    [1, 1],
    [2, 2, 1, 1],
    [5, 4, 4],
    [4, 4, 5],
    [3, 1, 4, 1, 5],
    [8, 6, 7, 6, 9],
    [-1, -1, 0, -1],
    [2, -3, -3, 4, -3]]

def generatedInputs : List (List Int) :=
  tieInputs ++
    (List.range 6).flatMap fun len =>
      (List.range (len + 3)).map fun seed =>
        generatedInput len seed

def windowsFor (xs : List Int) : List (Prod Nat Nat) :=
  (List.range xs.length).flatMap fun left =>
    (List.range (xs.length - left)).map fun offset =>
      (left, left + offset + 1)

def checkWindow (xs : List Int) (window : Prod Nat Nat) : Option Mismatch :=
  let left := window.1
  let right := window.2
  let got := (RMQ.SuccinctClassic.queryCosted xs left right).erase
  let expected := some (RMQ.scanWindow xs left (right - left))
  if got == expected then
    none
  else
    some { xs, left, right, got, expected }

def firstWindowMismatch (xs : List Int) : List (Prod Nat Nat) -> Option Mismatch
  | [] => none
  | window :: windows =>
      match checkWindow xs window with
      | some mismatch => some mismatch
      | none => firstWindowMismatch xs windows

def firstMismatch : List (List Int) -> Option Mismatch
  | [] => none
  | xs :: inputs =>
      match firstWindowMismatch xs (windowsFor xs) with
      | some mismatch => some mismatch
      | none => firstMismatch inputs

def totalWindowCount : Nat :=
  generatedInputs.foldl (fun total xs => total + (windowsFor xs).length) 0

def mismatchMessage (mismatch : Mismatch) : String :=
  "mismatch: xs=" ++ reprStr mismatch.xs ++
    " window=[" ++ toString mismatch.left ++ ", " ++
      toString mismatch.right ++ ")" ++
    " got=" ++ reprStr mismatch.got ++
    " expected=" ++ reprStr mismatch.expected

def mainImpl : IO Unit := do
  match firstMismatch generatedInputs with
  | none =>
      IO.println
        ("validated " ++ toString totalWindowCount ++
          " SuccinctClassic query windows across " ++
          toString generatedInputs.length ++ " deterministic inputs")
  | some mismatch =>
      IO.eprintln (mismatchMessage mismatch)
      IO.Process.exit 1

end RMQ.Validation.SuccinctClassic

def main : IO Unit :=
  RMQ.Validation.SuccinctClassic.mainImpl
