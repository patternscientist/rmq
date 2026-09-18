import RMQ.Core.WordRAM.Construction.Proof.Ownership
import RMQ.Core.WordRAM.Construction.Proof.Frames
import RMQ.Core.WordRAM.Construction.HeaderUse

/-! # PRE-1 builder proofs: run facts of both program constants (stage S8)

Outside the builder firewall. `BuilderRunFacts program s0 xs` collects, for the
run of a builder constant at fuel `builderBudget xs.length`: halting, the work
bound `1000000000 * n + 1000000000`, fuel insensitivity, the ten-category
partition, the output region and positional provenance of every output cell,
the temporary workspace bound `3200000 * n + 3200000` below the output base, the
historical peak extent, the extent at every fuel prefix below
`s0.extent + (3200000 * n + 3200000) + (buildMemory xs).length`, the
400-register bank, safety at `wordWidth n` of the
initial state, every transition and the final state, zero input writes, input
retention, write replay, clean tails at every fuel, read-level and
supplied-store agreement, and the array-backed evaluator's reflection.
`builderRunFacts_of` derives them from `builderRun_full`; `comparisonRunFacts`
and `wordRunFacts` instantiate them at `builderProgram` on
`comparisonInputState xs` for every `xs`, and at `builderProgramWord` on
`wordInputState (wordWidth n) xs` under `InputFits (wordWidth n) xs`.
`builderProgram_headerUse` and `builderProgramWord_headerUse` discharge
`HeaderUse` at the constants (V2-1, V3-9). The literals are crude upper bounds.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

open Structured

/-- Run-level facts of one builder constant on one initial state and input list,
at fuel `builderBudget xs.length` (stage S8 capstone component). -/
structure BuilderRunFacts (program : List BInstr) (s0 : State) (xs : List Int) : Prop where
  halts : ∃ outBase, (run program (builderBudget xs.length) s0).final.status = .halted outBase
  work : (run program (builderBudget xs.length) s0).steps ≤ 1000000000 * xs.length + 1000000000
  fuelInsensitive : ∀ extra,
    run program (builderBudget xs.length + extra) s0 = run program (builderBudget xs.length) s0
  categoryPartition :
    (run program (builderBudget xs.length) s0).steps =
      (run program (builderBudget xs.length) s0).categoryCount .read +
      (run program (builderBudget xs.length) s0).categoryCount .register +
      (run program (builderBudget xs.length) s0).categoryCount .arithmetic +
      (run program (builderBudget xs.length) s0).categoryCount .comparison +
      (run program (builderBudget xs.length) s0).categoryCount .branch +
      (run program (builderBudget xs.length) s0).categoryCount .control +
      (run program (builderBudget xs.length) s0).categoryCount .write +
      (run program (builderBudget xs.length) s0).categoryCount .allocation +
      (run program (builderBudget xs.length) s0).categoryCount .keyRead +
      (run program (builderBudget xs.length) s0).categoryCount .oracleComparison
  outputCells : ∀ outBase, (run program (builderBudget xs.length) s0).final.status = .halted outBase →
    s0.extent ≤ outBase ∧
    (run program (builderBudget xs.length) s0).final.extent =
      outBase + (PackedWordRAM.buildMemory xs).length ∧
    ∀ i, i < (PackedWordRAM.buildMemory xs).length →
      (run program (builderBudget xs.length) s0).final.memory (outBase + i) =
        some ((PackedWordRAM.buildMemory xs).getD i 0)
  outputProvenance : ∀ outBase i, (run program (builderBudget xs.length) s0).final.status = .halted outBase →
    i < (PackedWordRAM.buildMemory xs).length →
    ∃ (k : Nat) (t : Transition), (run program (builderBudget xs.length) s0).transitions[k]? = some t ∧
      t.write? = some (outBase + i, (PackedWordRAM.buildMemory xs).getD i 0) ∧
      ∀ (k' : Nat) (t' : Transition), k < k' →
        (run program (builderBudget xs.length) s0).transitions[k']? = some t' →
        ∀ e : Nat × Nat, t'.write? = some e → e.1 ≠ outBase + i
  workspace : ∀ outBase, (run program (builderBudget xs.length) s0).final.status = .halted outBase →
    outBase - s0.extent ≤ 3200000 * xs.length + 3200000
  peakExtent : ∀ fuel,
    (run program fuel s0).final.extent ≤ (run program (builderBudget xs.length) s0).final.extent
  prefixExtent : ∀ fuel outBase, (run program (builderBudget xs.length) s0).final.status = .halted outBase →
    (run program fuel s0).final.extent ≤
      s0.extent + (3200000 * xs.length + 3200000) + (PackedWordRAM.buildMemory xs).length
  registerBank : ∀ fuel reg, 400 ≤ reg → (run program fuel s0).final.regs reg = 0
  initialFits : s0.Fits (PackedWordRAM.wordWidth xs.length)
  runSafe : Run.Safe (PackedWordRAM.wordWidth xs.length) program (run program (builderBudget xs.length) s0)
  finalFits : (run program (builderBudget xs.length) s0).final.Fits (PackedWordRAM.wordWidth xs.length)
  noInputWrites : ∀ e ∈ (run program (builderBudget xs.length) s0).writes, s0.extent ≤ e.1
  inputRetained : (∀ a, a < s0.extent → (run program (builderBudget xs.length) s0).final.memory a = s0.memory a) ∧
    (run program (builderBudget xs.length) s0).final.keys = s0.keys
  replay : Replays s0.memory (run program (builderBudget xs.length) s0).writes
    (run program (builderBudget xs.length) s0).final.memory
  cleanTail : ∀ fuel, CleanTail (run program fuel s0).final
  readAgreement : ∀ s', State.Agree s0 s' →
    (∀ a ∈ (run program (builderBudget xs.length) s0).loads, s'.memory a = s0.memory a) →
    (∀ i ∈ (run program (builderBudget xs.length) s0).keyReads, s'.keys i = s0.keys i) →
    Run.Agree (run program (builderBudget xs.length) s0) (run program (builderBudget xs.length) s')
  suppliedAgreement : ∀ s', State.Agree s0 s' → CleanTail s' →
    (∀ a, a < s0.extent → s'.memory a = s0.memory a) →
    (∀ i ∈ (run program (builderBudget xs.length) s0).keyReads, s'.keys i = s0.keys i) →
    s'.memory = s0.memory ∧
      Run.Agree (run program (builderBudget xs.length) s0) (run program (builderBudget xs.length) s')
  arrayReflects : ∀ (es : ExecState) fuel, es.abstract = s0 → es.regs.size = 400 → es.keyRegs.size = 400 →
    (runArray program.toArray fuel es).steps = (run program fuel s0).steps ∧
    (runArray program.toArray fuel es).categories = (run program fuel s0).categories ∧
    (runArray program.toArray fuel es).writes = (run program fuel s0).writes ∧
    (runArray program.toArray fuel es).reserves = (run program fuel s0).reserves ∧
    (runArray program.toArray fuel es).result = (run program fuel s0).result ∧
    (runArray program.toArray fuel es).final.abstract = (run program fuel s0).final

namespace Proof

open Builder
open RMQ.SuccinctFinal.PackedWordRAM (buildMemory wordWidth)

/-- Peak extent: every fuel prefix of a run that stops within `ts.length` has
extent at most the final one. -/
theorem run_extent_le_final (program : List BInstr) (s sF : State) (ts : List Transition)
    (hR : RunsTo program s sF ts) (hst : sF.status ≠ .running) :
    ∀ fuel, (run program fuel s).final.extent ≤ sF.extent := by
  intro fuel
  rcases Nat.lt_or_ge fuel ts.length with h | h
  · have hsplit := run_add program fuel (ts.length - fuel) s
    rw [Nat.add_sub_cancel' (Nat.le_of_lt h)] at hsplit
    unfold RunsTo at hR
    rw [hR] at hsplit
    have hm := run_extent_mono program (ts.length - fuel) (run program fuel s).final
    have : sF = (run program (ts.length - fuel) (run program fuel s).final).final := by
      have := congrArg Run.final hsplit
      simpa using this
    rw [this]
    exact hm
  · have h2 := hR.fuel_extension hst (fuel - ts.length)
    rw [Nat.add_sub_cancel' h] at h2
    rw [h2]
    exact Nat.le_refl _

/-- **Builder run facts from a halting run with the stage conclusions.** -/
theorem builderRunFacts_of (program : List BInstr) (s0 : State) (xs : List Int)
    (sF : State) (ts : List Transition)
    (hR : RunsTo program s0 sF ts)
    (hlen : ts.length ≤ 4 + (25 * wordWidth xs.length + 40 + 39 * (5 * wordWidth xs.length + 20)) +
      2100 * (400000 * (xs.length + 1)))
    (hst : sF.status = .halted (sF.regs 3)) (h3a : s0.extent ≤ sF.regs 3)
    (h3b : sF.regs 3 ≤ s0.extent + 8 * (400000 * (xs.length + 1)))
    (hext : sF.extent = sF.regs 3 + (buildMemory xs).length)
    (hmem : ∀ i, i < (buildMemory xs).length → sF.memory (sF.regs 3 + i) = some ((buildMemory xs).getD i 0))
    (hbelow : ∀ a, a < s0.extent → sF.memory a = s0.memory a) (hkeys : sF.keys = s0.keys)
    (hsafe : Run.Safe (wordWidth xs.length) program ⟨sF, ts⟩)
    (hwrites : ∀ t ∈ ts, ∀ e, t.write? = some e → s0.extent ≤ e.1)
    (hfit : s0.Fits (wordWidth xs.length)) (hclean : CleanTail s0) (hregs : ∀ r, s0.regs r = 0)
    (hrb : ∀ i ∈ program, i.primitive.RegistersBelow 400) :
    BuilderRunFacts program s0 xs := by
  have hstop : sF.status ≠ .running := by rw [hst]; simp
  have hfuel : ts.length ≤ builderBudget xs.length := Nat.le_trans hlen (budget_ge xs.length)
  have hrun : run program (builderBudget xs.length) s0 = ⟨sF, ts⟩ :=
    run_of_halting program _ s0 sF ts hR hfuel hstop
  have hout : ∀ outBase, (run program (builderBudget xs.length) s0).final.status = .halted outBase →
      outBase = sF.regs 3 := by
    intro outBase h
    rw [hrun] at h
    simp only at h
    rw [hst] at h
    simp only [Status.halted.injEq] at h
    exact h.symm
  have hframe : ∀ i ∈ program, WritesOnly (fun r => r < 400) i :=
    fun i hi d hd => Prim.dest_lt_of_registersBelow (hrb i hi) d hd
  refine
    { halts := ⟨sF.regs 3, by rw [hrun]; exact hst⟩
      work := ?_
      fuelInsensitive := ?_
      categoryPartition := Run.steps_partition _
      outputCells := ?_
      outputProvenance := ?_
      workspace := ?_
      peakExtent := ?_
      prefixExtent := ?_
      registerBank := ?_
      initialFits := hfit
      runSafe := by rw [hrun]; exact hsafe
      finalFits := ?_
      noInputWrites := ?_
      inputRetained := ⟨fun a ha => by rw [hrun]; exact hbelow a ha, by rw [hrun]; exact hkeys⟩
      replay := writes_replay program _ s0
      cleanTail := fun fuel => run_cleanTail program fuel s0 hclean
      readAgreement := fun s' ha hm hk => run_agree_of_reads program _ s0 s' ha hm hk
      suppliedAgreement := fun s' ha hc hb hk => run_agree_of_supplied program _ s0 s' ha hclean hc hb hk
      arrayReflects := ?_ }
  · show (run program (builderBudget xs.length) s0).transitions.length ≤ _
    rw [hrun]
    have := builderBudget_eq_mul_add xs.length
    simp only
    omega
  · intro extra
    have h := hR.fuel_extension hstop (builderBudget xs.length - ts.length + extra)
    rw [← Nat.add_assoc, Nat.add_sub_cancel' hfuel] at h
    rw [h, hrun]
  · intro outBase h
    have e := hout outBase h
    subst e
    rw [hrun]
    exact ⟨h3a, hext, hmem⟩
  · intro outBase i h hi
    have e := hout outBase h
    subst e
    have hnone : s0.memory (sF.regs 3 + i) = none := hclean _ (by omega)
    have hsome : (run program (builderBudget xs.length) s0).final.memory (sF.regs 3 + i) =
        some ((buildMemory xs).getD i 0) := by rw [hrun]; exact hmem i hi
    exact run_last_write program _ s0 _ _ hsome hnone
  · intro outBase h
    have e := hout outBase h
    subst e
    omega
  · intro fuel
    rw [hrun]
    exact run_extent_le_final program s0 sF ts hR hstop fuel
  · intro fuel outBase _
    have h := run_extent_le_final program s0 sF ts hR hstop fuel
    omega
  · intro fuel reg hreg
    rw [run_frame program fuel s0 (fun r => r < 400) hframe reg (by omega), hregs]
  · have hs : Run.Safe (wordWidth xs.length) program (run program (builderBudget xs.length) s0) := by
      rw [hrun]; exact hsafe
    exact hs.final_fits hfit
  · intro e he
    rw [hrun] at he
    obtain ⟨t, ht, hte⟩ := List.mem_filterMap.mp he
    have := hwrites t ht e hte
    omega
  · intro es fuel habs hr hk
    have h := runArray_abstract program 400 hrb fuel es hr hk
    rw [habs] at h
    exact h

end Proof

end RMQ.SuccinctFinal.PackedConstruction

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder
open RMQ.SuccinctFinal.PackedWordRAM (buildMemory wordWidth)

/-! ## HeaderUse at the constants (CONTRACT.md V2-1, V3-9) -/

theorem builderProgram_head : builderProgram[0]? = some headerInstruction := rfl

theorem builderProgramWord_head : builderProgramWord[0]? = some headerInstruction := rfl

theorem builderProgram_tail : builderProgram.tail = (builderBody keyLeaf).compileAt 1 ++ [⟨.halt 3⟩] := by
  simp only [builderProgram, builderSource, Block.compileAt, Block.size, List.nil_append,
    List.cons_append, List.tail_cons, Nat.zero_add]

theorem builderProgramWord_tail :
    builderProgramWord.tail = (builderBody wordLeaf).compileAt 1 ++ [⟨.halt 3⟩] := by
  simp only [builderProgramWord, builderSource, Block.compileAt, Block.size, List.nil_append,
    List.cons_append, List.tail_cons, Nat.zero_add]

theorem tail_writesOnly_of_body (leaf : Block) (hbody : (builderBody leaf).WritesOnly (fun r => r ≠ 1)) :
    ∀ i ∈ (builderBody leaf).compileAt 1 ++ [(⟨.halt 3⟩ : BInstr)], WritesOnly (fun r => r ≠ 1) i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact Block.compile_writesOnly _ _ hbody 1 i hi
  · simp only [List.mem_singleton] at hi
    subst hi
    intro d hd
    simp [Prim.destination?] at hd

theorem builderProgram_tailNeverWritesR1 : ∀ i ∈ builderProgram.tail, WritesOnly (fun r => r ≠ 1) i := by
  rw [builderProgram_tail]
  exact tail_writesOnly_of_body keyLeaf wo_builderBody_key

theorem builderProgramWord_tailNeverWritesR1 :
    ∀ i ∈ builderProgramWord.tail, WritesOnly (fun r => r ≠ 1) i := by
  rw [builderProgramWord_tail]
  exact tail_writesOnly_of_body wordLeaf wo_builderBody_word

theorem builderProgram_headerUse : HeaderUse builderProgram :=
  headerUse_of_program _ builderProgram_head builderProgram_tailNeverWritesR1

theorem builderProgramWord_headerUse : HeaderUse builderProgramWord :=
  headerUse_of_program _ builderProgramWord_head builderProgramWord_tailNeverWritesR1

/-! ## Register operands below 400 -/

theorem registersBelow_of_source (leaf : Block) (hbody : (builderBody leaf).RegsBelow 400) :
    ∀ i ∈ (builderSource leaf).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)], i.primitive.RegistersBelow 400 := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · refine Block.compile_regsBelow 400 (builderSource leaf) ⟨?_, hbody⟩ 0 i hi
    simp [Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  · simp only [List.mem_singleton] at hi
    subst hi
    simp [Prim.RegistersBelow]

theorem builderProgram_registersBelow : ∀ i ∈ builderProgram, i.primitive.RegistersBelow 400 :=
  registersBelow_of_source keyLeaf rb_builderBody_key

theorem builderProgramWord_registersBelow : ∀ i ∈ builderProgramWord, i.primitive.RegistersBelow 400 :=
  registersBelow_of_source wordLeaf rb_builderBody_word

/-! ## Initial states at the word width -/

theorem length_lt_wordWidth (n : Nat) : n < 2 ^ wordWidth n := by
  have := cap_wordWidth n
  omega

theorem comparisonInputState_fits (xs : List Int) :
    (comparisonInputState xs).Fits (wordWidth xs.length) := by
  have hW := wordWidth_ge_32 xs.length
  have h1 := one_lt_two_pow hW
  have hn := length_lt_wordWidth xs.length
  refine ⟨fun _ => by show 0 < _; omega, by show 0 < _; omega, by show 1 < _; exact h1, ?_, ?_⟩
  · intro a v hv
    simp only [comparisonInputState] at hv
    split at hv
    · simp only [Option.some.injEq] at hv; subst hv; exact hn
    · cases hv
  · intro v hv
    simp [comparisonInputState] at hv

theorem wordInputState_fits (xs : List Int) (hfits : InputFits (wordWidth xs.length) xs) :
    (wordInputState (wordWidth xs.length) xs).Fits (wordWidth xs.length) := by
  have hW := wordWidth_ge_32 xs.length
  have hcap := cap_wordWidth xs.length
  refine ⟨fun _ => by show 0 < _; have := one_lt_two_pow hW; omega,
    by show 0 < _; have := one_lt_two_pow hW; omega,
    by show xs.length + 1 < _; omega, ?_, ?_⟩
  · intro a v hv
    change encodeInput (wordWidth xs.length) xs a = some v at hv
    cases a with
    | zero =>
        simp only [encodeInput_header, Option.some.injEq] at hv
        subst hv; omega
    | succ i =>
        simp only [encodeInput_succ, Option.map_eq_some_iff] at hv
        obtain ⟨x, hx, rfl⟩ := hv
        exact encodeInt_lt_capacity (hfits.2.2 x (List.mem_of_getElem? hx))
  · intro v hv
    simp [wordInputState] at hv

theorem program_length_lt (leaf : Block) (hsz : (builderSource leaf).size = 2106) (n : Nat) :
    (builderSource leaf).size + 1 < 2 ^ wordWidth n := by
  rw [hsz]
  have h := Nat.pow_le_pow_right (show 0 < 2 by decide) (wordWidth_ge_32 n)
  have h32 : (2106 + 1 : Nat) < 2 ^ 32 := by decide
  omega

/-! ## Run facts of both constants -/

/-- **Comparison-oracle builder run facts** at every `xs`. -/
theorem comparisonRunFacts (xs : List Int) :
    BuilderRunFacts builderProgram (comparisonInputState xs) xs := by
  have hW := wordWidth_ge_32 xs.length
  have hcap := cap_wordWidth xs.length
  obtain ⟨sF, ts, hR, hlen, hst, h3a, h3b, hext, hmem, hbelow, hk, hsafe, hwrites⟩ :=
    builderRun_full hW xs (OracleInput xs) keyLeaf (keyLeaf_spec hW xs) builderSource_size_keyLeaf _
      flow_builderSource_key (program_length_lt keyLeaf builderSource_size_keyLeaf_eq xs.length)
      (comparisonInputState xs) rfl rfl (fun _ => rfl) (show 0 < 1 by decide)
      (by simp [comparisonInputState]) rfl (oracleInput_below xs _) (bankcap_wordWidth xs.length)
      (by show 1 + _ < _; omega) (Nat.le_refl _) (comparisonInputState_fits xs)
  exact builderRunFacts_of builderProgram _ xs sF ts hR hlen hst h3a h3b hext hmem hbelow hk hsafe hwrites
    (comparisonInputState_fits xs) (comparisonInputState_cleanTail xs) (fun _ => rfl)
    builderProgram_registersBelow

/-- **Word-model builder run facts** at every `xs` whose keys fit the word width. -/
theorem wordRunFacts (xs : List Int) (hfits : InputFits (wordWidth xs.length) xs) :
    BuilderRunFacts builderProgramWord (wordInputState (wordWidth xs.length) xs) xs := by
  have hW := wordWidth_ge_32 xs.length
  have hcap := cap_wordWidth xs.length
  have hinp : WordInput (wordWidth xs.length) xs (wordInputState (wordWidth xs.length) xs) := by
    refine ⟨hfits, Nat.le_refl _, fun k hk => ?_⟩
    simp [wordInputState, encodeInput, List.getD, List.getElem?_eq_getElem hk]
  obtain ⟨sF, ts, hR, hlen, hst, h3a, h3b, hext, hmem, hbelow, hk, hsafe, hwrites⟩ :=
    builderRun_full hW xs (WordInput (wordWidth xs.length) xs) wordLeaf (wordLeaf_spec hW xs)
      builderSource_size_wordLeaf _ flow_builderSource_word
      (program_length_lt wordLeaf builderSource_size_wordLeaf_eq xs.length)
      (wordInputState (wordWidth xs.length) xs) rfl rfl (fun _ => rfl)
      (by simp [wordInputState, inputCellCount]) (by simp [wordInputState, encodeInput]) hinp
      (wordInput_below _ xs _ (Nat.le_refl _)) (bankcap_wordWidth xs.length)
      (by show xs.length + 1 + _ < _; omega) (Nat.le_refl _) (wordInputState_fits xs hfits)
  exact builderRunFacts_of builderProgramWord _ xs sF ts hR hlen hst h3a h3b hext hmem hbelow hk hsafe hwrites
    (wordInputState_fits xs hfits) (wordInputState_cleanTail _ xs) (fun _ => rfl)
    builderProgramWord_registersBelow

end RMQ.SuccinctFinal.PackedConstruction.Proof
