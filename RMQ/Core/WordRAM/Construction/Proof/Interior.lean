import RMQ.Core.WordRAM.Construction.Proof.Emit
import RMQ.Core.WordRAM.Construction.Builder.Interior
import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.SparseLevelTable

/-! # PRE-1 builder proofs: interior close tables (stage S2 subset)

Outside the builder firewall. The charged sparse-level tables: the entry block
computes the reference cell `bpSparseLevelCell dom slot` exactly, and the whole
table block emits the reference table bits `flattenPayloadWords
((bpSparseLevelEntries dom).map (natToBitsLE width))` as 0/1 cells.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder SuccinctSpace SuccinctClose

theorem log2_lt_width {x W : Nat} (hW : 0 < W) (hx : x < 2 ^ W) : Nat.log2 x < W := by
  by_cases h0 : x = 0
  · subst h0; rw [Nat.log2_zero]; exact hW
  · exact (Nat.log2_lt h0).mpr hx

theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  have := SuccinctRank.machineWordBits_mono_le h
  simp only [SuccinctRank.machineWordBits] at this
  omega

/-- Registers the level entry block writes. -/
abbrev LevelEntryWrites (r : Nat) : Prop := r = 16 ∨ (20 ≤ r ∧ r ≤ 24)

/-- **Level cell.** -/
theorem levelEntry_spec {W : Nat} (hW : 32 ≤ W) (dom : Operand)
    (hdomw : ¬ LevelEntryWrites dom)
    (u : State) (hrun : u.status = .running) (hone : u.regs 2 = 1) (htwo : u.regs 9 = 2)
    (hd : 2 ≤ u.regs dom) (hi : u.regs 14 < u.regs dom)
    (hcap : u.regs dom * (Nat.log2 (u.regs dom) + 1) < 2 ^ W) :
    ∃ u' j, SafeEval W (levelEntryBlock dom) u u' j ∧
      j ≤ 5 * Nat.log2 (u.regs dom) + 7 ∧ u'.status = .running ∧
      u'.regs 16 = bpSparseLevelCell (u.regs dom) (u.regs 14) ∧ u'.regs 16 < 2 ^ W ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, ¬ LevelEntryWrites r → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys := by
  generalize hdv : u.regs dom = d at hd hi hcap ⊢
  generalize hiv : u.regs 14 = i at hi ⊢
  have hd20 : (dom : Nat) ≠ 20 := fun h => hdomw (Or.inr ⟨by omega, by omega⟩)
  have hd21 : (dom : Nat) ≠ 21 := fun h => hdomw (Or.inr ⟨by omega, by omega⟩)
  have hd22 : (dom : Nat) ≠ 22 := fun h => hdomw (Or.inr ⟨by omega, by omega⟩)
  have hd23 : (dom : Nat) ≠ 23 := fun h => hdomw (Or.inr ⟨by omega, by omega⟩)
  have hdlog : d ≤ d * (Nat.log2 d + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hdW : d < 2 ^ W := by omega
  have hiW : i < 2 ^ W := by omega
  -- log2 of the slot
  obtain ⟨u1, j1, hlog, hj1, hu1run, hu1ll, hu1mem, hu1ext, hu1fr, hu1kr, hu1k⟩ :=
    log2Block_spec hW rLL (14 : Operand) (by decide) (by decide) (by decide) (by decide)
      u hrun hone htwo (by simpa [hiv] using hiW)
  simp only [operand_val_14, operand_val_22, hiv] at hj1 hu1ll
  have hu1one : u1.regs 2 = 1 := by rw [hu1fr 2 (by decide) (by decide) (by decide), hone]
  have hu1dom : u1.regs dom = d := by
    rw [hu1fr dom (by simpa using hd22) hd20 hd21, hdv]
  have hLi : Nat.log2 i ≤ Nat.log2 d := log2_mono (by omega)
  have hLW : Nat.log2 i < W := log2_lt_width (by omega) hiW
  have hcell : bpSparseLevelCell d i < d * (Nat.log2 d + 1) := bpSparseLevelCell_lt hd hi
  -- the three arithmetic actions
  let v1 := execPrim (Prim.arithmetic .shl rLP rONE rLL) u1
  have g1 := exec_arithmetic u1 .shl rLP rONE rLL
  let v2 := execPrim (Prim.arithmetic .mul rLM dom rLL) v1
  have g2 := exec_arithmetic v1 .mul rLM dom rLL
  let v3 := execPrim (Prim.arithmetic .add rENT rLP rLM) v2
  have g3 := exec_arithmetic v2 .add rENT rLP rLM
  have v1r : v1.regs = put u1.regs 23 (2 ^ Nat.log2 i) := by
    show (execPrim (Prim.arithmetic .shl rLP rONE rLL) u1).regs = _
    rw [g1]
    show put u1.regs 23 (Nat.shiftLeft (u1.regs 2) (u1.regs 22)) = _
    rw [hu1one, hu1ll, show Nat.shiftLeft 1 (Nat.log2 i) = 2 ^ Nat.log2 i from Nat.one_shiftLeft _]
  have v1dom : v1.regs dom = d := by rw [v1r, put_ne _ _ hd23, hu1dom]
  have v1ll : v1.regs 22 = Nat.log2 i := by rw [v1r, put_ne _ _ (by decide), hu1ll]
  have v2r : v2.regs = put v1.regs 24 (d * Nat.log2 i) := by
    show (execPrim (Prim.arithmetic .mul rLM dom rLL) v1).regs = _
    rw [g2]
    show put v1.regs 24 (v1.regs dom * v1.regs 22) = _
    rw [v1dom, v1ll]
  have v2lp : v2.regs 23 = 2 ^ Nat.log2 i := by
    rw [v2r, put_ne _ _ (by decide), v1r, put_same]
  have v3r : v3.regs = put v2.regs 16 (2 ^ Nat.log2 i + d * Nat.log2 i) := by
    show (execPrim (Prim.arithmetic .add rENT rLP rLM) v2).regs = _
    rw [g3]
    show put v2.regs 16 (v2.regs 23 + v2.regs 24) = _
    rw [v2lp, v2r, put_same]
  have v3s : v3.status = .running := by simp [v3, g3, v2, g2, v1, g1, hu1run]
  have hmulle : d * Nat.log2 i ≤ d * Nat.log2 d := Nat.mul_le_mul_left _ hLi
  have hexpand : d * (Nat.log2 d + 1) = d * Nat.log2 d + d := by rw [Nat.mul_add, Nat.mul_one]
  have hpowW : 2 ^ Nat.log2 i < 2 ^ W := Nat.pow_lt_pow_right (by decide) hLW
  have hsafe : ActsOK (Action.Safe W) [.arithmetic .shl rLP rONE rLL,
      .arithmetic .mul rLM dom rLL, .arithmetic .add rENT rLP rLM] u1 := by
    refine ⟨safe_shl hW u1 _ _ _ (by simp only [operand_val_22]; rw [hu1ll]; exact hLW) ?_,
      by simp [Action.prim, exec_arithmetic, hu1run], ?_⟩
    · show Nat.shiftLeft (u1.regs 2) (u1.regs 22) < 2 ^ W
      rw [hu1one, hu1ll, show Nat.shiftLeft 1 (Nat.log2 i) = 2 ^ Nat.log2 i from
        Nat.one_shiftLeft _]
      exact hpowW
    refine ⟨safe_mul hW v1 _ _ _ ?_, by simp [Action.prim, exec_arithmetic, hu1run], ?_⟩
    · show v1.regs dom * v1.regs 22 < 2 ^ W
      rw [v1dom, v1ll]; omega
    refine ⟨safe_add hW v2 _ _ _ ?_, v3s, trivial⟩
    · show v2.regs 23 + v2.regs 24 < 2 ^ W
      rw [v2lp, v2r, put_same]
      have : 2 ^ Nat.log2 i + d * Nat.log2 i = bpSparseLevelCell d i := rfl
      omega
  have heval := EvalG.seq hlog (acts_evalG (P := Action.Safe W) _ u1 hu1run hsafe)
  refine ⟨v3, j1 + 3, heval, by omega, v3s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v3r, put_same]; rfl
  · rw [v3r, put_same]
    have : 2 ^ Nat.log2 i + d * Nat.log2 i = bpSparseLevelCell d i := rfl
    omega
  · simp [v3, g3, v2, g2, v1, g1, hu1mem]
  · simp [v3, g3, v2, g2, v1, g1, hu1ext]
  · intro r hr
    have h16 : r ≠ 16 := fun h => hr (Or.inl h)
    have h20 : r ≠ 20 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
    have h21 : r ≠ 21 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
    have h22 : r ≠ 22 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
    have h23 : r ≠ 23 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
    have h24 : r ≠ 24 := fun h => hr (Or.inr ⟨by omega, by omega⟩)
    rw [v3r, put_ne _ _ h16, v2r, put_ne _ _ h24, v1r, put_ne _ _ h23,
      hu1fr r (by simpa using h22) h20 h21]
  · simp [v3, g3, v2, g2, v1, g1, hu1kr]
  · simp [v3, g3, v2, g2, v1, g1, hu1k]

/-- **Sparse-level table.** From a running state with the constants in place,
`levelTableBlock dom wid` safely appends the reference table bits
`flattenPayloadWords ((bpSparseLevelEntries d).map (natToBitsLE w))` as 0/1
cells, for `d = regs dom ≥ 2` and `w = regs wid`. -/
theorem levelTable_spec {W : Nat} (hW : 32 ≤ W) (dom wid : Operand)
    (hdomS : ¬ TableScratch dom) (hwidS : ¬ TableScratch wid)
    (hdomW : ¬ LevelEntryWrites dom) (hwidW : ¬ LevelEntryWrites wid)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hd : 2 ≤ s.regs dom) (hdW : s.regs dom + 1 < 2 ^ W) (hwW : s.regs wid < 2 ^ W)
    (hext : s.extent + s.regs dom * s.regs wid < 2 ^ W)
    (hcap : s.regs dom * (Nat.log2 (s.regs dom) + 1) < 2 ^ W) :
    ∃ s' k, SafeEval W (levelTableBlock dom wid) s s' k ∧
      k ≤ s.regs dom * (5 * Nat.log2 (s.regs dom) + 7 + 7 * s.regs wid + 7) + 3 ∧
      s'.status = .running ∧
      Emits s s' ((flattenPayloadWords ((bpSparseLevelEntries (s.regs dom)).map
        (natToBitsLE (s.regs wid)))).map bitToNat) ∧
      (∀ r, ¬ LevelEntryWrites r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  obtain ⟨s', k, heval, hk, hrun', hemit, hfr, hkr, hk'⟩ :=
    emitTable_spec hW dom wid (levelEntryBlock dom) (bpSparseLevelCell (s.regs dom))
      (5 * Nat.log2 (s.regs dom) + 7) LevelEntryWrites hdomS hwidS hdomW hwidW
      (by decide) (by decide) (by decide) s hrun hone htwo hdW hwW hext
      (by
        intro u hurun hufr humem _ huk hukr hslot
        have huone : u.regs 2 = 1 := by rw [hufr 2 (by decide) (by decide), hone]
        have hutwo : u.regs 9 = 2 := by rw [hufr 9 (by decide) (by decide), htwo]
        have hudom : u.regs dom = s.regs dom := hufr dom hdomW hdomS
        obtain ⟨u', j, hev, hj, hu'run, hu'ent, hu'W, hu'mem, hu'ext, hu'fr, hu'kr, hu'k⟩ :=
          levelEntry_spec hW dom hdomW u hurun huone hutwo (by rw [hudom]; exact hd)
            (by rw [hudom]; exact hslot) (by rw [hudom]; exact hcap)
        refine ⟨u', j, hev, by rw [hudom] at hj; exact hj, hu'run, by rw [hu'ent, hudom],
          hu'W, hu'mem, hu'ext, fun r hr _ => hu'fr r hr, hu'kr, hu'k⟩)
  exact ⟨s', k, heval, hk, hrun', hemit, hfr, hkr, hk'⟩
end RMQ.SuccinctFinal.PackedConstruction.Proof
