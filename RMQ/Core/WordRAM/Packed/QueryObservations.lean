import RMQ.Core.WordRAM.Packed.QueryCorrect

/-! # Whole-query observations on the counted allocation

The read theorem retains each transition occurrence and its actual prefix.
The agreement theorem preserves the entire Run, hence order and multiplicity.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe

theorem wordWidth_log_lower (n : Nat) : Nat.log2 (n + 2) + 1 ≤ wordWidth n := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth n
  have hq := Nat.two_pow_pos (packedReviewerCellWidth n)
  have he : n + 2 < 2 ^ (packedReviewerCellWidth n + 2) := by
    rw [Nat.pow_add]
    change n + 2 < 2 ^ packedReviewerCellWidth n * 4
    omega
  have hl := (Nat.log2_lt (by omega : n + 2 ≠ 0)).mpr he
  unfold wordWidth
  omega

theorem queryRun_reference_reads (xs : List Int) (left right : Nat) :
    (queryRun (buildMemory xs) xs.length left right).reads =
      if ValidRange xs left right then
        (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
          logicalTraceReads (SuccinctClassic.cartesianShape xs) (buildMemory xs)
            (SuccinctClassic.queryTraceResult xs left right).trace
      else [] := by
  by_cases hv : ValidRange xs left right
  · have h := (queryRun_valid (SuccinctClassic.cartesianShape xs) left right hv.1
      (by simpa only [packedReviewerCartesianShape_size] using hv.2)).2.1
    rw [packedReviewerPackedReference_eq_public xs left right hv] at h
    simpa only [if_pos hv, packedReviewerCartesianShape_size] using h
  · simpa only [if_neg hv] using (queryRun_invalid (buildMemory xs) xs.length left right hv).2.1

theorem queryTraceResult_readOnly (xs : List Int) (left right : Nat) :
    ReadOnlyTrace (SuccinctClassic.queryTraceResult xs left right).trace := by
  by_cases hv : ValidRange xs left right
  · have h := (queryRun_valid (SuccinctClassic.cartesianShape xs) left right hv.1
      (by simpa only [packedReviewerCartesianShape_size] using hv.2)).2.2.2
    rw [packedReviewerPackedReference_eq_public xs left right hv] at h
    exact h
  · rw [SuccinctClassic.queryTraceResult_invalid xs left right hv]
    simp [WordRAM.TraceResult.pure, ReadOnlyTrace]

theorem queryRun_read_at (xs : List Int) (left right k : Nat) (t : Transition) (receipt : Receipt)
    (ht : (queryRun (buildMemory xs) xs.length left right).transitions[k]? = some t)
    (hr : t.receipt = some receipt) :
    t.before = (run (buildMemory xs) queryProgram k (initialState xs.length left right)).final ∧
      t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
      execute (buildMemory xs) t.instruction t.before = (t.after, t.receipt) ∧
      ∃ dst addrReg, t.instruction = .load dst addrReg ∧
        receipt.address = t.before.regs addrReg ∧ receipt.reply = (buildMemory xs)[receipt.address]? :=
  run_read_at ht hr

theorem queryRun_agreement (xs : List Int) (memory : Memory) (left right : Nat)
    (h : ∀ receipt ∈ (queryRun (buildMemory xs) xs.length left right).reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) :
    queryRun memory xs.length left right = queryRun (buildMemory xs) xs.length left right :=
  run_eq_of_agree (buildMemory xs) memory queryProgram queryBudget (initialState xs.length left right) h

theorem queryRun_categories_partition (memory : Memory) (n left right : Nat) :
    let actual := queryRun memory n left right
    actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
      actual.categoryCount .arithmetic + actual.categoryCount .comparison +
      actual.categoryCount .branch + actual.categoryCount .control :=
  Run.steps_partition _

theorem queryRun_correct_cost_space (xs : List Int) (left right : Nat) :
    let actual := queryRun (buildMemory xs) xs.length left right
    actual.result = some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
      actual.final.status = .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
      actual.steps ≤ 837572 ∧
      ((buildMemory xs).length + queryProgramWords + queryScratchWords) * wordWidth xs.length ≤
        2 * xs.length + queryCompleteRho xs.length := by
  have hb := queryRun_steps_le (buildMemory xs) xs.length left right
  rw [queryBudget_eq] at hb
  exact ⟨queryRun_result xs left right, queryRun_halts xs left right, hb, query_complete_capacity xs⟩

end RMQ.SuccinctFinal.PackedWordRAM
