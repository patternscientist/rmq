import RMQ.Core.WordRAM.Construction.Proof.Tail
import RMQ.Core.WordRAM.Construction.Proof.Leaves
import RMQ.Core.WordRAM.Construction.Proof.Constants

/-! # PRE-1 builder proofs: the runs of the program constants and exactness (stage S7)

Outside the builder firewall. `builderSource_spec` composes the header load, the
constants, the geometry prelude and `tailStage_spec`; `builderRun_spec` compiles
the source (`EvalG.compile_realizes'`) and appends the final `halt 3`, so the run
halts with `outBase` and the cells from `outBase` to the extent are
`buildMemory xs`. The capacity premises hold at `W = wordWidth n` for every `n`
(`bankcap_wordWidth`, `cap_wordWidth`), and the fuel `builderBudget n` covers the
proven work bound for every `n` (`budget_ge`), so `run_of_halting` fixes the run
at that fuel and both V3-6 equality theorems follow at their exact left-hand
sides. The literal pins of the constants are in `Proof/Constants.lean`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

/-! ## Capacity at the word width -/

theorem fringeOverhead_ge_two (n : Nat) : 2 ≤ bpFringeTableOverhead n := by
  unfold bpFringeTableOverhead bpFringeChunkRowCount bpFringeChunkEntryWidth
  have hc := bpFringeChunkBits_pos (2 * n)
  generalize bpFringeChunkBits (2 * n) = c at hc ⊢
  have h2 : 2 ≤ 2 ^ c := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hc
    simpa using this
  have h4 : 4 ≤ (c + 1) * (c + 1) := Nat.mul_le_mul (by omega : 2 ≤ c + 1) (by omega : 2 ≤ c + 1)
  have h8 : 8 ≤ 2 ^ c * ((c + 1) * (c + 1)) := Nat.mul_le_mul h2 h4
  have hw : 1 ≤ Nat.log2 (bpFringeChunkEntryBound c) + 1 := by omega
  have := Nat.mul_le_mul h8 hw
  omega

/-- The oldest cell width leaves room for `2 n + 4`. -/
theorem two_n_four_lt_cellPow (n : Nat) : 2 * n + 4 < 2 ^ packedReviewerCellWidth n := by
  have h1 := packedReviewerCellBound_lt_two_pow_width n
  have h2 := fringeOverhead_ge_two n
  unfold packedReviewerCellBound concreteBPNativeSuccinctRMQCanonicalReviewerOverhead at h1
  omega

/-- **Bank capacity at the word width.** -/
theorem bankcap_wordWidth (n : Nat) : 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ wordWidth n := by
  have h := Nat.pow_lt_pow_left (two_n_four_lt_cellPow n) (show (8 : Nat) ≠ 0 by decide)
  have e : 2 ^ wordWidth n = 2 ^ 32 * (2 ^ packedReviewerCellWidth n) ^ 8 := by
    unfold wordWidth
    rw [Nat.pow_add, ← Nat.pow_mul, Nat.mul_comm 8]
  rw [e]
  exact Nat.mul_lt_mul_of_pos_left h (by decide)

/-- **Extent capacity at the word width.** -/
theorem cap_wordWidth (n : Nat) : n + 1 + 64 * (400000 * (n + 1)) < 2 ^ wordWidth n := by
  have h := bankcap_wordWidth n
  have h1 : 2 * n + 4 ≤ (2 * n + 4) ^ 8 := Nat.le_self_pow (by decide) _
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [h32] at h
  omega

/-! ## The header -/

theorem header_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (h0 : s.regs 0 = 0) (hext : 0 < s.extent) {n : Nat} (hmem : s.memory 0 = some n)
    (hn : n < 2 ^ W) :
    ∃ s', SafeEval W (.action (.load 1 0)) s s' 1 ∧ s'.status = .running ∧
      s'.regs = put s.regs 1 n ∧ s'.memory = s.memory ∧ s'.extent = s.extent ∧
      s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs := by
  have ha : s.regs (0 : Operand) < s.extent := by simp only [operand_val_0]; rw [h0]; exact hext
  have hm : s.memory (s.regs (0 : Operand)) = some n := by simp only [operand_val_0]; rw [h0]; exact hmem
  obtain ⟨s', e, hr, hR, hM, hE, hK, hKR⟩ := step_load hW 1 0 s hrun ha hm hn
  exact ⟨s', e, hr, hR, hM, hE, hK, hKR⟩

/-! ## The whole body -/

set_option maxHeartbeats 1600000 in
/-- **Builder body.** From a running state with all registers zero, the input
length in cell 0 and an input predicate the leaf needs, `builderSource leaf`
reaches a running state holding `outBase` in register 3 with `buildMemory xs`
stored from `outBase` to the extent. -/
theorem builderSource_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (s : State) (hrun : s.status = .running)
    (hregs : ∀ r, s.regs r = 0) (hext : 0 < s.extent) (hmem : s.memory 0 = some xs.length)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (hbankcap : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W)
    (hcap : s.extent + 64 * (400000 * (xs.length + 1)) < 2 ^ W)
    (hWW : wordWidth xs.length ≤ W) :
    ∃ s' k, SafeEval W (builderSource leaf) s s' k ∧
      k ≤ 3 + (25 * W + 40 + 39 * (5 * W + 20)) + 2100 * (400000 * (xs.length + 1)) ∧
      s'.status = .running ∧ s.extent ≤ s'.regs 3 ∧
      s'.regs 3 ≤ s.extent + 8 * (400000 * (xs.length + 1)) ∧
      s'.extent = s'.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        s'.memory (s'.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧ s'.keys = s.keys := by
  have hW1 : 1 < 2 ^ W := one_lt_two_pow hW
  have hnW : xs.length < 2 ^ W := by
    have h1 : 2 * xs.length + 4 ≤ (2 * xs.length + 4) ^ 8 := Nat.le_self_pow (by decide) _
    have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
    rw [h32] at hbankcap
    omega
  obtain ⟨h1, eH, hr1, hR1, hM1, hE1, hK1, hKR1⟩ :=
    header_spec hW s hrun (hregs 0) hext hmem hnW
  obtain ⟨h2, eC, hr2, h2_2, h2_9, hM2, hE2, hF2, hKR2, hK2⟩ := constantsBlock_spec hW h1 hr1
  have h2n : h2.regs 1 = xs.length := by rw [hF2 1 (by decide) (by decide), hR1, put_same]
  obtain ⟨p, kP, eP, hkP, hpr, hpb, hpg, hpf, hpM, hpE, hpK, hpKR⟩ :=
    geometryPrelude_spec hW hbankcap h2 hr2 h2_2 h2_9 h2n
  have hp0 : p.regs 0 = 0 := by
    rw [hpf 0 (by omega) (by omega), hF2 0 (by decide) (by decide), hR1, put_ne _ _ (by decide), hregs]
  have hfit0 : ∀ r, s.regs r < 2 ^ W := fun r => by rw [hregs]; omega
  have hfitP := SafeEval.regs_fit hW eP (SafeEval.regs_fit hW eC (SafeEval.regs_fit hW eH hfit0))
  have hpext : p.extent = s.extent := by rw [hpE, hE2, hE1]
  have hpmem : p.memory = s.memory := by rw [hpM, hM2, hM1]
  have hpkeys : p.keys = s.keys := by rw [hpK, hK2, hK1]
  obtain ⟨t, kT, eT, hkT, htr, ht3a, ht3b, htext, htmem, htbelow, htk⟩ :=
    tailStage_spec hW xs Inp leaf hleaf p hpr hfitP hp0 hpb hpg
      (hInp s p hinp (fun b _ => by rw [hpmem]) (Nat.le_of_eq hpext.symm) hpkeys) (by rw [hpext]; exact hInp)
      hbankcap (by rw [hpext]; exact hcap) hWW
  refine ⟨t, 1 + (2 + (kP + kT)), EvalG.seq eH (EvalG.seq eC (EvalG.seq eP eT)), by omega, htr,
    by rw [← hpext]; exact ht3a, by rw [← hpext]; exact ht3b, htext, htmem, ?_, by rw [htk, hpkeys]⟩
  intro a ha
  rw [htbelow a (by rw [hpext]; exact ha), hpmem]

/-! ## The run -/

/-- The halting run of a compiled builder source. -/
theorem builderRun_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (hsize : (builderSource leaf).size < 2 ^ 32)
    (s : State) (hpc : s.pc = 0) (hrun : s.status = .running)
    (hregs : ∀ r, s.regs r = 0) (hext : 0 < s.extent) (hmem : s.memory 0 = some xs.length)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (hbankcap : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W)
    (hcap : s.extent + 64 * (400000 * (xs.length + 1)) < 2 ^ W)
    (hWW : wordWidth xs.length ≤ W) :
    ∃ sF ts, RunsTo ((builderSource leaf).compileAt 0 ++ [⟨.halt 3⟩]) s sF ts ∧
      ts.length ≤ 4 + (25 * W + 40 + 39 * (5 * W + 20)) + 2100 * (400000 * (xs.length + 1)) ∧
      sF.status = .halted (sF.regs 3) ∧ s.extent ≤ sF.regs 3 ∧
      sF.regs 3 ≤ s.extent + 8 * (400000 * (xs.length + 1)) ∧
      sF.extent = sF.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        sF.memory (sF.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < s.extent → sF.memory a = s.memory a) ∧ sF.keys = s.keys := by
  obtain ⟨t, k, e, hk, htr, h3a, h3b, htext, htmem, htbelow, htk⟩ :=
    builderSource_spec hW xs Inp leaf hleaf s hrun hregs hext hmem hinp hInp hbankcap hcap hWW
  let prog := (builderSource leaf).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)]
  have host : HostedAt prog 0 ((builderSource leaf).compileAt 0) :=
    HostedAt.append_left (HostedAt.self prog)
  obtain ⟨s'', ts, hR, hlen, hagree, hpc''⟩ :=
    EvalG.compile_realizes' (P := Action.Safe W) (fun _ q _ hp => Action.Safe.pc_set hp q) prog e 0 host
      (by simpa using hsize)
  have hs0 : ({ s with pc := 0 } : State) = s := by
    cases s; simp only at hpc; subst hpc; rfl
  rw [hs0] at hR
  have hs''r : s''.status = .running := by rw [hagree]; exact htr
  have hs''pc : s''.pc = (builderSource leaf).size := by
    have := hpc'' hs''r; simpa using this
  have hfetch : prog[s''.pc]? = some ⟨.halt 3⟩ := by
    rw [hs''pc]
    show ((builderSource leaf).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)])[(builderSource leaf).size]? = _
    rw [List.getElem?_append_right (by simp)]
    simp
  have hstep := RunsTo.instruction hs''r hfetch
  have hall := hR.trans hstep
  have hfin : execPrim (Prim.halt 3) s'' = { s'' with status := .halted (s''.regs 3) } := rfl
  have hreg : s''.regs = t.regs := by rw [hagree]
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · show (execPrim (Prim.halt 3) s'').status = .halted ((execPrim (Prim.halt 3) s'').regs 3)
    rw [hfin]
  · show s.extent ≤ (execPrim (Prim.halt 3) s'').regs 3
    rw [hfin]; rw [hreg]; exact h3a
  · show (execPrim (Prim.halt 3) s'').regs 3 ≤ _
    rw [hfin]; rw [hreg]; exact h3b
  · show (execPrim (Prim.halt 3) s'').extent = (execPrim (Prim.halt 3) s'').regs 3 + _
    rw [hfin]; rw [hreg, hagree]; exact htext
  · intro i hi
    show (execPrim (Prim.halt 3) s'').memory ((execPrim (Prim.halt 3) s'').regs 3 + i) = _
    rw [hfin]; rw [hreg, hagree]; exact htmem i hi
  · intro a ha
    show (execPrim (Prim.halt 3) s'').memory a = _
    rw [hfin]; simp only; rw [hagree]; exact htbelow a ha
  · show (execPrim (Prim.halt 3) s'').keys = _
    rw [hfin]; simp only; rw [hagree]; exact htk

/-- Reading back a list stored from a base. -/
theorem emitted_eq_of_stored (s : State) (base : Nat) (l : List Nat)
    (h : ∀ i, i < l.length → s.memory (base + i) = some (l.getD i 0)) :
    emitted s base l.length = l := by
  unfold emitted
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [h i (by simpa using h1)]
    simp [List.getD, List.getElem?_eq_getElem h2]

/-- A halting segment determines the run at any larger fuel. -/
theorem run_of_halting (prog : List BInstr) (fuel : Nat) (s sF : State) (ts : List Transition)
    (hR : RunsTo prog s sF ts) (hfuel : ts.length ≤ fuel) (hst : sF.status ≠ .running) :
    run prog fuel s = ⟨sF, ts⟩ := by
  have h := hR.fuel_extension hst (fuel - ts.length)
  rwa [Nat.add_sub_cancel' hfuel] at h

theorem wordWidth_ge_32 (n : Nat) : 32 ≤ wordWidth n := by unfold wordWidth; omega

theorem budget_ge (n : Nat) :
    4 + (25 * wordWidth n + 40 + 39 * (5 * wordWidth n + 20)) + 2100 * (400000 * (n + 1)) ≤
      builderBudget n := by
  have := wordWidth_le_linear n
  unfold builderBudget
  omega

/-- The comparison-oracle run halts with the reference memory from `outBase`. -/
theorem builder_run_comparison (xs : List Int) :
    ∃ sF ts, run builderProgram (builderBudget xs.length) (comparisonInputState xs) = ⟨sF, ts⟩ ∧
      RunsTo builderProgram (comparisonInputState xs) sF ts ∧
      ts.length ≤ 4 + (25 * wordWidth xs.length + 40 + 39 * (5 * wordWidth xs.length + 20)) +
        2100 * (400000 * (xs.length + 1)) ∧
      sF.status = .halted (sF.regs 3) ∧ 1 ≤ sF.regs 3 ∧
      sF.regs 3 ≤ 1 + 8 * (400000 * (xs.length + 1)) ∧
      sF.extent = sF.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        sF.memory (sF.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < 1 → sF.memory a = (comparisonInputState xs).memory a) ∧
      sF.keys = (comparisonInputState xs).keys := by
  have hW := wordWidth_ge_32 xs.length
  have hcap := cap_wordWidth xs.length
  obtain ⟨sF, ts, hR, hlen, hst, h3a, h3b, hext, hmem, hbelow, hk⟩ :=
    builderRun_spec hW xs (OracleInput xs) keyLeaf (keyLeaf_spec hW xs) builderSource_size_keyLeaf
      (comparisonInputState xs) rfl rfl (fun _ => rfl) (show 0 < 1 by decide) (by simp [comparisonInputState])
      rfl (oracleInput_below xs _) (bankcap_wordWidth xs.length)
      (by show 1 + _ < _; omega) (Nat.le_refl _)
  have hrun := run_of_halting builderProgram (builderBudget xs.length) _ sF ts hR
    (Nat.le_trans hlen (budget_ge xs.length)) (by rw [hst]; simp)
  exact ⟨sF, ts, hrun, hR, hlen, hst, h3a, h3b, hext, hmem, hbelow, hk⟩

/-- **Exactness, comparison-oracle model.** -/
theorem efficientBuild_eq_buildMemory : ∀ xs : List Int, efficientBuild xs = buildMemory xs := by
  intro xs
  obtain ⟨sF, ts, hrun, _, _, hst, _, _, hext, hmem, _, _⟩ := builder_run_comparison xs
  unfold efficientBuild
  rw [hrun]
  simp only [hst]
  rw [hext, Nat.add_sub_cancel_left]
  exact emitted_eq_of_stored sF _ _ hmem

/-- **Exactness, word model.** -/
theorem efficientBuildWord_eq_buildMemory : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
    efficientBuildWord (wordWidth xs.length) xs = buildMemory xs := by
  intro xs hfits
  have hW := wordWidth_ge_32 xs.length
  have hcap := cap_wordWidth xs.length
  have hinp : WordInput (wordWidth xs.length) xs (wordInputState (wordWidth xs.length) xs) := by
    refine ⟨hfits, Nat.le_refl _, fun k hk => ?_⟩
    simp [wordInputState, encodeInput, List.getD, List.getElem?_eq_getElem hk]
  obtain ⟨sF, ts, hR, hlen, hst, h3a, h3b, hext, hmem, hbelow, hk⟩ :=
    builderRun_spec hW xs (WordInput (wordWidth xs.length) xs) wordLeaf (wordLeaf_spec hW xs)
      builderSource_size_wordLeaf (wordInputState (wordWidth xs.length) xs) rfl rfl (fun _ => rfl)
      (by simp [wordInputState, inputCellCount]) (by simp [wordInputState, encodeInput]) hinp
      (wordInput_below _ xs _ (Nat.le_refl _)) (bankcap_wordWidth xs.length)
      (by show xs.length + 1 + _ < _; omega) (Nat.le_refl _)
  have hrun := run_of_halting builderProgramWord (builderBudget xs.length) _ sF ts hR
    (Nat.le_trans hlen (budget_ge xs.length)) (by rw [hst]; simp)
  unfold efficientBuildWord
  rw [hrun]
  simp only [hst]
  rw [hext, Nat.add_sub_cancel_left]
  exact emitted_eq_of_stored sF _ _ hmem

end RMQ.SuccinctFinal.PackedConstruction.Proof
