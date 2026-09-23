import RMQ.Core.WordRAM.Native.Finite

/-! # Execution observations without retaining transition states

The tail-recursive runner calls the same finite step as the logged semantics.
Counts are accumulated during execution. Optional read observations contain
only addresses/replies; the default does not allocate a transition trace.
Natural cells are an intermediate container refinement, not a limb encoding.
-/

namespace RMQ.SuccinctFinal.PackedNative

open PackedWordRAM

structure Counts where
  memoryRead : Nat := 0
  registerWrite : Nat := 0
  arithmetic : Nat := 0
  comparison : Nat := 0
  branch : Nat := 0
  control : Nat := 0
deriving Repr, DecidableEq

def Counts.bump (c : Counts) : Category → Counts
  | .memoryRead => { c with memoryRead := c.memoryRead + 1 }
  | .registerWrite => { c with registerWrite := c.registerWrite + 1 }
  | .arithmetic => { c with arithmetic := c.arithmetic + 1 }
  | .comparison => { c with comparison := c.comparison + 1 }
  | .branch => { c with branch := c.branch + 1 }
  | .control => { c with control := c.control + 1 }

structure Stats where
  steps : Nat := 0
  counts : Counts := {}
  readsRev : List Receipt := []
deriving Repr, DecidableEq

def Stats.record (observeReads : Bool) (a : Stats)
    (category : Category) (receipt : Option Receipt) : Stats :=
  { steps := a.steps + 1
    counts := a.counts.bump category
    readsRev := if observeReads then
      match receipt with | none => a.readsRev | some r => r :: a.readsRev
      else a.readsRev }

theorem Stats.record_no_reads (a : Stats) (c : Category) (r : Option Receipt) :
    (a.record false c r).readsRev = a.readsRev := rfl

def recordTransition (observeReads : Bool) (a : Stats) (t : FiniteTransition) : Stats :=
  a.record observeReads t.instruction.category t.receipt

/-- No transition list is constructed by this tail-recursive function. -/
def runThin (observeReads : Bool) (memory : Array Nat) (program : Array Instruction) :
    Nat → FiniteState → Stats → FiniteState × Stats
  | 0, s, a => (s, a)
  | fuel + 1, s, a =>
      match stepFinite memory program s with
      | none => (s, a)
      | some t =>
          runThin observeReads memory program fuel t.after
            (recordTransition observeReads a t)

/-- Exact projection of the operational finite trace; no safety premise is
needed because both sides implement the same total natural-cell semantics. -/
theorem runThin_projection (observeReads : Bool) (memory : Array Nat)
    (program : Array Instruction) (fuel : Nat) (s : FiniteState) (a : Stats) :
    runThin observeReads memory program fuel s a =
      ((runFinite memory program fuel s).final,
        (runFinite memory program fuel s).transitions.foldl
          (recordTransition observeReads) a) := by
  induction fuel generalizing s a with
  | zero => rfl
  | succ fuel ih =>
      simp only [runThin, runFinite]
      cases stepFinite memory program s with
      | none => rfl
      | some t =>
          simpa only [List.foldl_cons] using
            ih t.after (recordTransition observeReads a t)

theorem runThin_no_reads (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState) (a : Stats) :
    (runThin false memory program fuel s a).2.readsRev = a.readsRev := by
  induction fuel generalizing s a with
  | zero => rfl
  | succ fuel ih =>
      simp only [runThin]
      cases stepFinite memory program s with
      | none => rfl
      | some t => exact (ih t.after (recordTransition false a t)).trans rfl

def observeRun (observeReads : Bool) (r : Run) (a : Stats) : State × Stats :=
  (r.final, r.transitions.foldl
    (fun acc t => acc.record observeReads t.instruction.category t.receipt) a)

def decodeThin (r : FiniteState × Stats) : State × Stats := (r.1.decode, r.2)

/-- The trace-free computational implementation refines the original primitive
run, preserving the final state and every accumulated observation. -/
theorem runThin_reference (observeReads : Bool) (memory : Array Nat)
    (program : Array Instruction) (fuel : Nat) (s : FiniteState) (a : Stats)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    decodeThin (runThin observeReads memory program fuel s a) =
      observeRun observeReads (run memory.toList program.toList fuel s.decode) a := by
  rw [runThin_projection, ← runFinite_decode memory program fuel s hwrites]
  simp only [decodeThin, observeRun, FiniteRun.decode, List.foldl_map]
  rfl

end RMQ.SuccinctFinal.PackedNative
