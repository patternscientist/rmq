import RMQ.Core.WordRAM.Packed.Capstone
import RMQ.Core.WordRAM.Native.Route
import RMQ.Core.WordRAM.Native.Observations
import RMQ.Core.WordRAM.Native.Machine

/-! # The exact canonical PQ1 objects at the native source boundary

This instantiation has every natural fuel and endpoint, without a readiness or
valid-query guard. Finite-word safety is consumed separately by the limb join.
-/

namespace RMQ.SuccinctFinal.PackedNative
open PackedWordRAM

private theorem below_max_register_count (bound : Nat) : bound < max 3 (bound + 1) := by
  omega

theorem canonical_destination_bound :
    ∀ i ∈ queryProgram, i.WritesOnly (fun r => r < queryRegisterCount) := by
  intro i hi
  have hw := queryProgram_writesOnly i hi
  have hm : querySource.maxDestination < queryRegisterCount := by
    change querySource.maxDestination < max 3 (querySource.maxDestination + 1)
    exact below_max_register_count querySource.maxDestination
  cases i <;> simp_all [Instruction.WritesOnly] <;> omega

theorem canonical_initial_zero_tail (n left right r : Nat) (hr : queryRegisterCount ≤ r) :
    (initialState n left right).regs r = 0 := by
  simpa only [run] using queryRun_finite_registers [] n left right 0 r hr

theorem canonical_source (xs : List Int) (left right fuel : Nat) (observeReads : Bool) :
    decodeThin
      (routeCore observeReads (buildMemory xs).toArray queryProgram.toArray fuel
        (FiniteState.ofState queryRegisterCount (initialState xs.length left right))) =
      observeRun observeReads
        (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)) {} :=
  routeCore_ofState observeReads (buildMemory xs) queryProgram queryRegisterCount fuel
    (initialState xs.length left right) canonical_destination_bound
    (canonical_initial_zero_tail xs.length left right)

theorem canonical_source_steps (xs : List Int) (left right fuel : Nat) (observeReads : Bool) :
    (routeCore observeReads (buildMemory xs).toArray queryProgram.toArray fuel
      (FiniteState.ofState queryRegisterCount (initialState xs.length left right))).2.steps =
        (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).steps := by
  have h := congrArg (fun x : State × Stats => x.2.steps) (canonical_source xs left right fuel observeReads)
  exact h.trans (observeRun_steps _ _)

theorem canonical_source_reads (xs : List Int) (left right fuel : Nat) :
    (routeCore true (buildMemory xs).toArray queryProgram.toArray fuel
      (FiniteState.ofState queryRegisterCount (initialState xs.length left right))).2.readsRev.reverse =
        (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).reads := by
  have h := congrArg (fun x : State × Stats => x.2.readsRev.reverse) (canonical_source xs left right fuel true)
  exact h.trans (observeRun_reads _)

theorem canonical_source_category (xs : List Int) (left right fuel : Nat)
    (observeReads : Bool) (category : Category) :
    (routeCore observeReads (buildMemory xs).toArray queryProgram.toArray fuel
      (FiniteState.ofState queryRegisterCount (initialState xs.length left right))).2.counts.get category =
        (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).categoryCount category := by
  have h := congrArg (fun x : State × Stats => x.2.counts.get category)
    (canonical_source xs left right fuel observeReads)
  exact h.trans (observeRun_category _ _ _)

/-- The accepted positional safety theorem supplies every actual transition,
including every prefix and every extra fuel value after canonical halting. -/
theorem canonical_run_safe (xs : List Int) (left right fuel : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    LimbMachine.RunSafe (wordWidth xs.length)
      (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)) := by
  have hb : LimbMachine.RunSafe (wordWidth xs.length)
      (run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)) := by
    intro t ht
    obtain ⟨index, hi⟩ := List.getElem?_of_mem ht
    exact (queryRun_execution_safe xs left right hl hr).2.2.1 index t hi
  by_cases hf : fuel ≤ queryBudget
  · exact LimbMachine.RunSafe.prefix _ _ _ _ _ _ hf hb
  · have hle : queryBudget ≤ fuel := by omega
    have he := run_add_of_halted (buildMemory xs) queryProgram queryBudget
      (fuel - queryBudget) (initialState xs.length left right)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value)
      (fullyChargedPackedQueryCapstone_holds.halt xs left right hl hr)
    rw [Nat.add_sub_of_le hle] at he
    rw [he]
    exact hb

/-- Same allocation, program and initial state; all fuel and representable
endpoints. No valid-range, readiness, successful-read or safety premise remains. -/
theorem canonical_limb_run (xs : List Int) (left right fuel : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (LimbMachine.run (wordWidth xs.length)
      (LimbMachine.encodeMemory (wordWidth xs.length) (buildMemory xs))
      (LimbMachine.encodeCode (wordWidth xs.length) queryProgram) fuel
      (LimbMachine.State.encode (wordWidth xs.length) queryRegisterCount
        (initialState xs.length left right))).decode =
      run (buildMemory xs) queryProgram fuel (initialState xs.length left right) :=
  LimbMachine.run_reference (wordWidth xs.length) queryRegisterCount
    (buildMemory xs) queryProgram fuel (initialState xs.length left right)
    (buildMemory_words_fit xs) (queryProgram_fits xs.length) canonical_destination_bound
    (initialState_fits xs.length left right hl hr) (canonical_initial_zero_tail xs.length left right)
    (canonical_run_safe xs left right fuel hl hr)

theorem canonical_limb_thin (xs : List Int) (left right fuel : Nat) (observeReads : Bool)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    let output := LimbMachine.runThin observeReads (wordWidth xs.length)
      (LimbMachine.encodeMemory (wordWidth xs.length) (buildMemory xs))
      (LimbMachine.encodeCode (wordWidth xs.length) queryProgram) fuel
      (LimbMachine.State.encode (wordWidth xs.length) queryRegisterCount
        (initialState xs.length left right)) {}
    (output.1.decode, output.2) =
      observeRun observeReads
        (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)) {} :=
  LimbMachine.runThin_reference observeReads (wordWidth xs.length) queryRegisterCount
    (buildMemory xs) queryProgram fuel (initialState xs.length left right) {}
    (buildMemory_words_fit xs) (queryProgram_fits xs.length) canonical_destination_bound
    (initialState_fits xs.length left right hl hr) (canonical_initial_zero_tail xs.length left right)
    (canonical_run_safe xs left right fuel hl hr)

end RMQ.SuccinctFinal.PackedNative
