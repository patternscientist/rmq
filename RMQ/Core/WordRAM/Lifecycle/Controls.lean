import RMQ.Core.WordRAM.Lifecycle.ArrayRun
import RMQ.Core.WordRAM.Lifecycle.Descriptor
import RMQ.Core.WordRAM.Lifecycle.Finalizer
import RMQ.Core.WordRAM.Lifecycle.Retained

/-! # Small replayable lifecycle predicate controls

Every observed transition below comes from `runArray`; the fixture programs use
the production scalar evaluator. These controls check named projections, not the
complete public lifecycle theorem. The real service's dirty second query is a
separate required integration control, not certified by this module.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Controls

open PackedConstruction (Memory Operand)

/-- Source interval [1,3) overlaps its destination [0,2). -/
def source : Owner :=
  { regs := #[1, 0, 2, 0, 0, 0, 0, 0]
    memory := #[some 0, some 11, some 22]
    keys := #[]
    keyRegs := #[]
    pc := 0
    status := .running }

def original : Memory := source.toState.core.memory
def finalizerCode : List Instruction := Finalizer.code 0 (by decide)
def forward : ArrayRun := runArray finalizerCode.toArray (Finalizer.cost 1 2) source

theorem source_initialized : Finalizer.Initialized original 1 2 := by
  intro j hj
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl
  · exact ⟨11, rfl⟩
  · exact ⟨22, rfl⟩

theorem source_entry : Finalizer.Entry 0 1 2 source.toState :=
  ⟨rfl, rfl, rfl, rfl, rfl, source_initialized, source.closed.1⟩

theorem forward_accept : Finalizer.FinalOutput original 1 2 forward.final.toState := by
  refine ⟨rfl, ?_, forward.final.closed.1⟩
  intro j hj
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

#guard forward.final.memory == #[some 11, some 22]
#guard forward.categoryCount .numericRelease == 1
#guard forward.reads == [(1, some 11), (2, some 22)]

/-- Both receipt arguments are actual indexed occurrences, not a fabricated trace. -/
def copiedAt (r : ArrayRun) (memory : Memory) (i loadIndex storeIndex : Nat) : Prop :=
  ∃ load store : ArrayTransition,
    r.transitions[loadIndex]? = some load ∧ r.transitions[storeIndex]? = some store ∧
    Finalizer.CopyReceipt memory 1 i load.toTransition store.toTransition

theorem forward_first_copy_accept : copiedAt forward original 0 4 5 := by
  refine ⟨forward.transitions[4]'(by decide), forward.transitions[5]'(by decide),
    rfl, rfl, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem forward_second_copy_accept : copiedAt forward original 1 11 12 := by
  refine ⟨forward.transitions[11]'(by decide), forward.transitions[12]'(by decide),
    rfl, rfl, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- Wrong output source: receipt identity and the actual destination register. -/
def outputSource : Owner := { source with regs := #[0, 0, 0, 11, 22, 0, 0, 0] }
def outputGoodRun := runArray #[.old (.move 0 3)] 1 outputSource
def outputBadRun := runArray #[.old (.move 0 4)] 1 outputSource
def outputGood := (outputGoodRun.transitions[0]'(by decide)).toTransition
def outputBad := (outputBadRun.transitions[0]'(by decide)).toTransition

theorem output_source_accept : Descriptor.OutputReceipt outputGood := by
  refine ⟨rfl, ?_, rfl⟩
  exact executeArray_toState (.old (.move 0 3)) outputSource (by change 0 < 8; decide)

theorem output_source_reject : ¬ Descriptor.OutputReceipt outputBad := by
  intro h
  have wrong := h.1
  change Action.instruction (.old (.move 0 4)) = .instruction (.old (.move 0 3)) at wrong
  cases wrong

theorem output_source_value_dependency :
    outputBad.after.core.regs 0 ≠ outputGood.after.core.regs 0 := by
  have mismatch := Descriptor.output_wrong_source outputSource.toState 4 (by decide)
  rw [← executeArray_toState (.old (.move 0 4)) outputSource (by change 0 < 8; decide),
    ← executeArray_toState (.old (.move 0 3)) outputSource (by change 0 < 8; decide)] at mismatch
  exact mismatch

#guard outputGoodRun.final.regs.getD 0 0 == 11
#guard outputBadRun.final.regs.getD 0 0 == 22

/- Skipping a real producer store leaves a reserved but absent source cell. -/
def beforeInitialization : Owner := { source with memory := #[some 0, some 11] }
def initialization : Array Instruction :=
  #[.old (.reserve 6), .old (.constant 5 22), .old (.store 6 5)]
def skippedInitialization : Array Instruction :=
  #[.old (.reserve 6), .old (.constant 5 22), .old (.constant 7 0)]
def initialized := runOwner initialization 3 beforeInitialization
def skipped := runOwner skippedInitialization 3 beforeInitialization

theorem initialization_accept : Finalizer.Initialized initialized.toState.core.memory 1 2 := by
  intro j hj
  have cases : j = 0 ∨ j = 1 := by omega
  rcases cases with rfl | rfl
  · exact ⟨11, rfl⟩
  · exact ⟨22, rfl⟩

theorem initialization_reject : ¬ Finalizer.Initialized skipped.toState.core.memory 1 2 := by
  intro h
  obtain ⟨v, hv⟩ := h 1 (by decide)
  change none = some v at hv
  cases hv

/-- The continuation really executes the same hosted finalizer after either producer. -/
def initializedProgram : Array Instruction :=
  (initialization.toList ++ Finalizer.code 3 (by decide)).toArray
def absentProgram : Array Instruction :=
  (skippedInitialization.toList ++ Finalizer.code 3 (by decide)).toArray
def initializedCopy := runArray initializedProgram 26 beforeInitialization
def absentCopy := runArray absentProgram 26 beforeInitialization

theorem initialized_copy_reply_accept :
    copiedAt initializedCopy initialized.toState.core.memory 1 14 15 := by
  refine ⟨initializedCopy.transitions[14]'(by decide),
    initializedCopy.transitions[15]'(by decide), rfl, rfl, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem absent_copy_reply_reject :
    ¬ copiedAt absentCopy skipped.toState.core.memory 1 14 15 := by
  rintro ⟨load, store, _, hs, _⟩
  have noStore : absentCopy.transitions[15]? = none := rfl
  rw [noStore] at hs
  cases hs

#guard initializedCopy.final.memory == #[some 11, some 22]
#guard absentCopy.final.status == .fault
#guard absentCopy.reads == [(1, some 11), (2, none)]

/- A stale owned suffix invalidates the full entry and the same final predicate. -/
def staleSource : Owner := { source with memory := #[some 0, some 11, some 22, some 99] }
def stale := runArray finalizerCode.toArray (Finalizer.cost 1 2) staleSource

theorem stale_tail_entry_reject : ¬ Finalizer.Entry 0 1 2 staleSource.toState := by
  intro h
  have bad := h.2.2.1
  change 4 = 3 at bad
  contradiction

theorem stale_tail_reject : ¬ Finalizer.FinalOutput original 1 2 stale.final.toState := by
  intro h
  have bad := h.1
  change 3 = 2 at bad
  contradiction

#guard stale.final.memory == #[some 11, some 22, some 22]

/- Replace only the release instruction. Copying still works; ownership does not. -/
def omitReleaseCode : Array Instruction :=
  finalizerCode.toArray.set! 11 (.old (.constant 7 0))
def omitRelease := runArray omitReleaseCode (Finalizer.cost 1 2) source

theorem omitted_release_reject :
    ¬ Finalizer.FinalOutput original 1 2 omitRelease.final.toState := by
  intro h
  have bad := h.1
  change 3 = 2 at bad
  contradiction

#guard omitRelease.final.memory == #[some 11, some 22, some 22]
#guard omitRelease.categoryCount .numericRelease == 0
#guard omitRelease.reads == forward.reads

/- Reverse the overlapping copy order using scalar loads/stores and one release. -/
def backwardCode : Array Instruction := #[
  .old (.constant 0 2), .old (.constant 1 1),
  .old (.load 5 0), .old (.store 1 5),
  .old (.constant 0 1), .old (.constant 1 0),
  .old (.load 5 0), .old (.store 1 5), .releaseCell]
def backward := runArray backwardCode 9 source

theorem backward_copy_reject :
    ¬ Finalizer.FinalOutput original 1 2 backward.final.toState := by
  intro h
  have bad := h.2.1 0 (by decide)
  change some 22 = some 11 at bad
  contradiction

#guard backward.final.memory == #[some 22, some 22]
#guard backward.reads == [(2, some 22), (1, some 22)]
#guard backward.categoryCount .numericRelease == 1

/- Pointwise default values alone do not retire separately counted key banks. -/
def emptyValuedBanks : Owner := { source with keys := #[none], keyRegs := #[0] }
def retiredBanks := runArray #[.releaseKey, .releaseKeyRegister] 2 emptyValuedBanks
def retainedBanks := runArray #[.old (.constant 7 0), .old (.constant 7 0)] 2 emptyValuedBanks
def Retired (s : State) : Prop := s.keyExtent = 0 ∧ s.keyRegExtent = 0

theorem key_extent_accept : Retired retiredBanks.final.toState := ⟨rfl, rfl⟩
theorem key_extent_reject : ¬ Retired retainedBanks.final.toState := by
  intro h
  have bad := h.1
  change 1 = 0 at bad
  contradiction

theorem retained_key_values_empty :
    (∀ a, retainedBanks.final.toState.core.keys a = none) ∧
    (∀ r, retainedBanks.final.toState.core.keyRegs r = 0) := by
  constructor
  · intro a
    cases a <;> rfl
  · intro r
    cases r <;> rfl

#guard retiredBanks.final.keys.size == 0 && retiredBanks.final.keyRegs.size == 0
#guard retainedBanks.final.keys.size == 1 && retainedBanks.final.keyRegs.size == 1

/- Starting at PC 1 omits the actual base-to-release-counter move. -/
def wrongEntrySource : Owner := { source with pc := 1 }
def wrongEntry := runArray finalizerCode.toArray (Finalizer.cost 1 2) wrongEntrySource

theorem wrong_entry_guard_reject : ¬ Finalizer.Entry 0 1 2 wrongEntrySource.toState := by
  intro h
  have bad := h.2.1
  change 1 = 0 at bad
  contradiction

theorem wrong_entry_result_reject :
    ¬ Finalizer.FinalOutput original 1 2 wrongEntry.final.toState := by
  intro h
  have bad := h.1
  change 3 = 2 at bad
  contradiction

#guard wrongEntry.final.memory == #[some 11, some 22, some 22]

/- All fields, including dormant fields, use the production encoding predicate.
The fixture width is 8; the production language itself bounds operands by 2^32. -/
def fittingDormant : List Instruction := [.old (.halt 0), .old (.constant 0 255)]
def overflowingDormant : List Instruction := [.old (.halt 0), .old (.constant 0 256)]

theorem field_width_accept : ∀ i ∈ fittingDormant, i.Fits 8 := by
  intro i hi
  simp only [fittingDormant, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;>
    simp [Instruction.Fits, Instruction.encoding, PackedConstruction.Prim.constants]

theorem field_width_reject : ¬ (∀ i ∈ overflowingDormant, i.Fits 8) := by
  intro h
  have bad := h (.old (.constant 0 256)) (by simp [overflowingDormant])
  have bound := bad 256 (by simp [Instruction.encoding, PackedConstruction.Prim.constants])
  omega

theorem register_field_width_accept : (Instruction.old (.move 255 0)).Fits 8 := by
  simp [Instruction.Fits, Instruction.encoding, PackedConstruction.Prim.constants]

theorem register_field_width_reject : ¬ (Instruction.old (.move 256 0)).Fits 8 := by
  intro h
  have bad := h 256 (by simp [Instruction.encoding, PackedConstruction.Prim.constants])
  omega

theorem branch_field_width_accept : (Instruction.old (.branchZero 0 255)).Fits 8 := by
  simp [Instruction.Fits, Instruction.encoding, PackedConstruction.Prim.constants]

theorem branch_field_width_reject : ¬ (Instruction.old (.branchZero 0 256)).Fits 8 := by
  intro h
  have bad := h 256 (by simp [Instruction.encoding, PackedConstruction.Prim.constants])
  omega

#guard (runArray fittingDormant.toArray 2 source).final.status == .halted 1
#guard (runArray overflowingDormant.toArray 2 source).final.status == .halted 1
#guard (runArray overflowingDormant.toArray 2 source).steps == 1

/-- The runtime dirty-bank control tests this register projection of the same
query-entry ABI established by the real service setup. Its witness is obtained
from an executed first query; no large closed execution is reduced at import. -/
def entryRegisterClean (owner : Owner) (r : Nat) : Bool := owner.regs.getD r 0 == 0

theorem query_entry_implies_clean (owner : Owner) (n left right r : Nat)
    (high : 3 ≤ r)
    (entry : Retained.projectQueryState owner.toState =
      PackedWordRAM.initialState n left right) : entryRegisterClean owner r = true := by
  have h := congrArg (fun s : PackedWordRAM.State => s.regs r) entry
  have h0 : r ≠ 0 := by omega
  have h1 : r ≠ 1 := by omega
  have h2 : r ≠ 2 := by omega
  simpa [entryRegisterClean, Retained.projectQueryState, Owner.toState,
    PackedConstruction.ExecState.abstract, PackedWordRAM.initialState,
    PackedWordRAM.inputRegisters, PackedWordRAM.Registers.write, h0, h1, h2] using h

theorem dirty_register_rejects_entry (owner : Owner) (n left right r : Nat)
    (high : 3 ≤ r) (dirty : entryRegisterClean owner r = false) :
    Retained.projectQueryState owner.toState ≠ PackedWordRAM.initialState n left right := by
  intro entry
  have clean := query_entry_implies_clean owner n left right r high entry
  rw [dirty] at clean
  contradiction

end RMQ.SuccinctFinal.PackedLifecycle.Controls
