import RMQ.Core.WordRAM.Lifecycle.Ownership
import RMQ.Core.WordRAM.Native.Lifecycle.ThinRun

/-! # Fixed-code production lifecycle adapter

The two closed arrays contain the existing lifecycle programs. The first call
executes construction, retirement, and the caller's first query continuously;
later calls execute the existing charged request protocol and service. These
equalities cover every owner, including stopped, faulted, and exhausted runs.
Native sharing and initialization of the closed arrays are separate runtime
properties; their source values are fixed here.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle

@[noinline] def materializeProgram (model : InputModel) : Array Instruction :=
  (Layout.program model).toArray

def wordProgram : Array Instruction := materializeProgram .word

def comparisonProgram : Array Instruction := materializeProgram .comparison

def cachedProgram : InputModel → Array Instruction
  | .word => wordProgram
  | .comparison => comparisonProgram

theorem cachedProgram_eq (model : InputModel) :
    cachedProgram model = (Layout.program model).toArray := by
  cases model <;> rfl

def buildFirst (model : InputModel) (xs : List Int) (left right : Nat) : Owner :=
  runThin (cachedProgram model) (Continuous.lifecycleBudget xs.length)
    (Executable.initialOwner model xs left right)

def query (model : InputModel) (left right : Nat) (owner : Owner) : Owner :=
  runThin (cachedProgram model) Service.budget
    (requestProtocolThin Layout.serviceEntry left right owner)

theorem cached_run (model : InputModel) (fuel : Nat) (owner : Owner) :
    runOwner (cachedProgram model) fuel owner =
      runOwner (Layout.program model).toArray fuel owner := by
  rw [cachedProgram_eq]

theorem buildFirst_eq (model : InputModel) (xs : List Int) (left right : Nat) :
    buildFirst model xs left right = Ownership.owner model xs left right := by
  unfold buildFirst Ownership.owner
  rw [runThin_eq_runOwner, cachedProgram_eq]

theorem query_eq (model : InputModel) (left right : Nat) (owner : Owner) :
    query model left right owner = Executable.queryOwner model left right owner := by
  unfold query Executable.queryOwner
  rw [runThin_eq_runOwner, requestProtocolThin_eq_requestProtocolOwner, cachedProgram_eq]

end RMQ.SuccinctFinal.PackedNative.Lifecycle
