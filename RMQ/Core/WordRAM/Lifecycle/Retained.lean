import RMQ.Core.WordRAM.Lifecycle.QuerySafetyBridge
import RMQ.Core.WordRAM.Lifecycle.BoundarySafety

/-! # Canonical retained data after construction

This is a data invariant on the actual lifecycle state. The projection preserves
every numeric register, the current program counter, and every status; no query
answer or execution certificate is included.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Retained

def projectStatus : PackedConstruction.Status → PackedWordRAM.Status
  | .running => .running
  | .halted value => .halted value
  | .fault => .fault

def projectQueryState (s : State) : PackedWordRAM.State :=
  ⟨s.core.regs, s.core.pc, projectStatus s.core.status⟩

def Data (memory : PackedWordRAM.Memory) (s : State) : Prop :=
  s.core.memory = (fun a => memory[a]?) ∧ s.core.extent = memory.length ∧
    s.core.keys = (fun _ => none) ∧ s.core.keyRegs = (fun _ => 0) ∧
    s.keyExtent = 0 ∧ s.keyRegExtent = 0

def FiniteBank (s : State) : Prop := ∀ r, 8273 ≤ r → s.core.regs r = 0

def Canonical (xs : List Int) (s : State) : Prop :=
  Data (PackedWordRAM.buildMemory xs) s ∧ FiniteBank s ∧
    s.Fits (PackedWordRAM.wordWidth xs.length)

theorem projectStatus_roundtrip (status : PackedConstruction.Status) :
    PackedConstruction.Conservative.status (projectStatus status) = status := by
  cases status <;> rfl

theorem project_embedded (memory : PackedWordRAM.Memory) (s : PackedWordRAM.State) :
    projectQueryState (QuerySafetyBridge.embedded memory s) = s := by
  cases s with
  | mk regs pc status => cases status <;> rfl

theorem Data.roundtrip {memory : PackedWordRAM.Memory} {s : State} (data : Data memory s) :
    s = QuerySafetyBridge.embedded memory (projectQueryState s) := by
  cases s with
  | mk core keys keyRegs =>
    cases core with
    | mk regs backing extent keyValues keyRegisters pc status =>
      rcases data with ⟨hm, he, hk, hkr, hke, hkre⟩
      simp only at hm he hk hkr hke hkre
      subst backing; subst extent; subst keyValues; subst keyRegisters; subst keys; subst keyRegs
      cases status <;> rfl

theorem Data.closed {memory : PackedWordRAM.Memory} {s : State} (data : Data memory s) :
    s.Closed := by
  rw [data.roundtrip]
  exact (QuerySafetyBridge.embedded_closed memory _).1

theorem project_fits {s : State} {W : Nat} (fit : s.Fits W) :
    (projectQueryState s).Fits W := by
  refine ⟨fit.1.2.1, fit.1.1, ?_⟩
  intro value h
  apply fit.1.2.2.2.2 value
  cases hs : s.core.status <;> simp_all [projectQueryState, projectStatus]

theorem Canonical.closed {xs : List Int} {s : State} (canonical : Canonical xs s) :
    s.Closed := canonical.1.closed

theorem Data.boundary (memory : PackedWordRAM.Memory) (s : State) (b : Boundary)
    (data : Data memory s) : Data memory (executeBoundary b s) := by
  cases b <;> exact data

theorem Canonical.boundary {xs : List Int} {s : State} {b : Boundary}
    {len entry : Nat} (canonical : Canonical xs s)
    (safe : b.Safe (PackedWordRAM.wordWidth xs.length) len 8273 entry) :
    Canonical xs (executeBoundary b s) :=
  ⟨canonical.1.boundary _ _ _, boundary_execute_tail safe canonical.2.1,
    boundary_execute_fits canonical.2.2 safe⟩

theorem Data.runBoundary (memory : PackedWordRAM.Memory) (s : State) (bs : List Boundary)
    (data : Data memory s) : Data memory (runBoundary bs s).final := by
  induction bs generalizing s with
  | nil => exact data
  | cons b bs ih =>
    cases hs : boundaryStep b s with
    | none => simpa [PackedLifecycle.runBoundary, hs] using data
    | some t =>
      have eq : t.after = executeBoundary b s := by
        cases hstatus : s.core.status <;> simp [boundaryStep, hstatus] at hs
        exact (congrArg Transition.after hs).symm
      simpa [PackedLifecycle.runBoundary, hs, eq] using ih (executeBoundary b s) (data.boundary _ _ _)

theorem Canonical.requestProtocol {xs : List Int} {s : State}
    (canonical : Canonical xs s) (entry : PackedConstruction.Operand) (left right len : Nat)
    (hl : left < 2 ^ PackedWordRAM.wordWidth xs.length)
    (hr : right < 2 ^ PackedWordRAM.wordWidth xs.length)
    (he : entry.val < len) (hw : entry.val < 2 ^ PackedWordRAM.wordWidth xs.length) :
    Canonical xs (requestProtocol entry left right s).final := by
  have safe := requestProtocol_safe entry left right s hl hr he hw (by decide)
    canonical.2.2 canonical.closed canonical.2.1
  exact ⟨canonical.1.runBoundary _ _ _, safe.2.2.1, safe.1⟩

end RMQ.SuccinctFinal.PackedLifecycle.Retained
