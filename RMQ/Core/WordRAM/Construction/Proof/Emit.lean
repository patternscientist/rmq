import RMQ.Core.WordRAM.Construction.Proof.Base
import RMQ.Core.SuccinctSpace.WordStore

/-! # PRE-1 builder proofs: emission blocks

Outside the builder firewall. Safe-evaluation specifications of the emission
source blocks of `Builder/Emit.lean`: every executed action satisfies
`Prim.Safe W` at its pre-state (`SafeEval W`), the cost is bounded by a literal
function of the emitted width, the result state is running, the emitted cells
are exactly the reference bits as 0/1 values (`Emits`), and the register frame
and key registers are stated.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder SuccinctSpace

theorem two_le_two_pow {W : Nat} (hW : 32 ≤ W) : 2 < 2 ^ W := by
  have : 2 ^ 32 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  have h32 : (2 : Nat) < 2 ^ 32 := by decide
  omega

/-- **Single bit.** -/
theorem emitBit_spec {W : Nat} (hW : 32 ≤ W) (src : Operand) (hsrc : (src : Nat) ≠ 10)
    (s : State) (hrun : s.status = .running) (hv : s.regs src < 2 ^ W)
    (hext : s.extent + 1 < 2 ^ W) :
    ∃ s', SafeEval W (emitBit src) s s' 2 ∧ s'.status = .running ∧
      Emits s s' [s.regs src] ∧ (∀ r, r ≠ 10 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  let s₁ := execPrim (.reserve rCUR) s
  have e₁ := exec_reserve s rCUR
  have hlt : s₁.regs rCUR < s₁.extent := by simp [s₁, e₁]
  have h₁run : s₁.status = .running := by simp [s₁, e₁, hrun]
  have h₁src : s₁.regs src = s.regs src := by simp [s₁, e₁]; exact put_ne _ _ hsrc
  have h₁cur : s₁.regs rCUR = s.extent := by simp [s₁, e₁]
  let s₂ := execPrim (.store rCUR src) s₁
  have e₂ := exec_store s₁ rCUR src hlt
  have hsafe₂ : Action.Safe W s₁ (.store rCUR src) :=
    safe_store hW s₁ rCUR src hlt (by rw [h₁src]; exact hv)
  refine ⟨s₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact EvalG.seq (EvalG.action (.reserve rCUR) s hrun (safe_reserve hW s rCUR hext))
      (EvalG.action (.store rCUR src) s₁ h₁run hsafe₂)
  · simp [s₂, e₂, h₁run]
  · refine ⟨by simp [s₂, e₂, s₁, e₁], fun a => ?_⟩
    simp only [s₂, e₂, h₁src, h₁cur]
    by_cases ha : a = s.extent
    · subst ha; simp
    · rw [put_ne _ _ ha, if_neg (by simp; omega)]
      simp [s₁, e₁]
  · intro r hr
    simp [s₂, e₂, s₁, e₁]
    exact put_ne _ _ hr
  · simp [s₂, e₂, s₁, e₁]
  · simp [s₂, e₂, s₁, e₁]
/-! ## Little-endian bit words -/

theorem natToBitsLE_succ_right : ∀ (j v : Nat),
    natToBitsLE (j + 1) v = natToBitsLE j v ++ [decide ((v / 2 ^ j) % 2 = 1)]
  | 0, v => by simp [natToBitsLE]
  | j + 1, v => by
      have ih := natToBitsLE_succ_right j (v / 2)
      rw [show j + 1 + 1 = (j + 1) + 1 from rfl, natToBitsLE, ih, natToBitsLE]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      rfl

theorem bitToNat_decide_mod_two (x : Nat) : bitToNat (decide (x % 2 = 1)) = x % 2 := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [bitToNat, h]

/-! ## One round of `emitBits` -/

theorem emitBitsBody_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2) (hx : s.regs 13 < 2 ^ W)
    (hk : 0 < s.regs 12) (hkW : s.regs 12 < 2 ^ W) (hext : s.extent + 1 < 2 ^ W) :
    ∃ s', SafeEval W emitBitsBody s s' 5 ∧ s'.status = .running ∧
      Emits s s' [s.regs 13 % 2] ∧ s'.regs 13 = s.regs 13 / 2 ∧ s'.regs 12 = s.regs 12 - 1 ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have htwoPos : 0 < s.regs 9 := by omega
  -- step 1: rBIT := rEVAL % 2
  let s1 := execPrim (Prim.arithmetic .mod rBIT rEVAL rTWO) s
  have e1 := exec_arithmetic s .mod rBIT rEVAL rTWO
  have s1r : s1.regs = put s.regs 11 (s.regs 13 % 2) := by
    simp [s1, e1, Arithmetic.eval, htwo]
  have s1m : s1.memory = s.memory := by simp [s1, e1]
  have s1e : s1.extent = s.extent := by simp [s1, e1]
  have s1s : s1.status = .running := by simp [s1, e1, hrun]
  have s1k : s1.keys = s.keys ∧ s1.keyRegs = s.keyRegs := by simp [s1, e1]
  -- step 2: reserve rCUR
  let s2 := execPrim (Prim.reserve rCUR) s1
  have e2 := exec_reserve s1 rCUR
  have s2r : s2.regs = put s1.regs 10 s1.extent := by simp [s2, e2]
  have s2m : s2.memory = s.memory := by simp [s2, e2, s1m]
  have s2e : s2.extent = s.extent + 1 := by simp [s2, e2, s1e]
  have s2s : s2.status = .running := by simp [s2, e2, s1s]
  have s2k : s2.keys = s.keys ∧ s2.keyRegs = s.keyRegs := by simp [s2, e2, s1k]
  have s2cur : s2.regs 10 = s.extent := by simp [s2r, s1e]
  have s2bit : s2.regs 11 = s.regs 13 % 2 := by simp [s2r, s1r, put]
  -- step 3: store rCUR rBIT
  have hlt3 : s2.regs rCUR < s2.extent := by simp [s2cur, s2e]
  let s3 := execPrim (Prim.store rCUR rBIT) s2
  have e3 := exec_store s2 rCUR rBIT hlt3
  have s3r : s3.regs = s2.regs := by simp [s3, e3]
  have s3m : s3.memory = put s.memory s.extent (some (s.regs 13 % 2)) := by
    simp [s3, e3, s2m, s2cur, s2bit]
  have s3e : s3.extent = s.extent + 1 := by simp [s3, e3, s2e]
  have s3s : s3.status = .running := by simp [s3, e3, s2s]
  have s3k : s3.keys = s.keys ∧ s3.keyRegs = s.keyRegs := by simp [s3, e3, s2k]
  -- step 4: rEVAL := rEVAL / 2
  let s4 := execPrim (Prim.arithmetic .div rEVAL rEVAL rTWO) s3
  have e4 := exec_arithmetic s3 .div rEVAL rEVAL rTWO
  have s3eval : s3.regs 13 = s.regs 13 := by simp [s3r, s2r, s1r, put]
  have s3two : s3.regs 9 = 2 := by simp [s3r, s2r, s1r, put, htwo]
  have s4r : s4.regs = put s3.regs 13 (s.regs 13 / 2) := by
    simp [s4, e4, Arithmetic.eval, s3eval, s3two]
  have s4m : s4.memory = s3.memory := by simp [s4, e4]
  have s4e : s4.extent = s.extent + 1 := by simp [s4, e4, s3e]
  have s4s : s4.status = .running := by simp [s4, e4, s3s]
  have s4k : s4.keys = s.keys ∧ s4.keyRegs = s.keyRegs := by simp [s4, e4, s3k]
  -- step 5: rECNT := rECNT - 1
  let s5 := execPrim (Prim.arithmetic .sub rECNT rECNT rONE) s4
  have e5 := exec_arithmetic s4 .sub rECNT rECNT rONE
  have s4cnt : s4.regs 12 = s.regs 12 := by simp [s4r, s3r, s2r, s1r, put]
  have s4one : s4.regs 2 = 1 := by simp [s4r, s3r, s2r, s1r, put, hone]
  have s5r : s5.regs = put s4.regs 12 (s.regs 12 - 1) := by
    simp [s5, e5, Arithmetic.eval, s4cnt, s4one]
  have s5m : s5.memory = s3.memory := by simp [s5, e5, s4m]
  have s5e : s5.extent = s.extent + 1 := by simp [s5, e5, s4e]
  have s5s : s5.status = .running := by simp [s5, e5, s4s]
  have s5k : s5.keys = s.keys ∧ s5.keyRegs = s.keyRegs := by simp [s5, e5, s4k]
  -- safety and evaluation
  have hsafe : ActsOK (Action.Safe W)
      [.arithmetic .mod rBIT rEVAL rTWO, .reserve rCUR, .store rCUR rBIT,
        .arithmetic .div rEVAL rEVAL rTWO, .arithmetic .sub rECNT rECNT rONE] s := by
    refine ⟨safe_mod hW s _ _ _ (by simpa using hx) (by simpa using htwoPos), s1s, ?_⟩
    refine ⟨safe_reserve hW s1 _ (by rw [s1e]; exact hext), s2s, ?_⟩
    refine ⟨safe_store hW s2 _ _ hlt3 ?_, s3s, ?_⟩
    · have : s2.regs 11 < 2 := by rw [s2bit]; exact Nat.mod_lt _ (by decide)
      have h2 := two_le_two_pow hW
      simp only [operand_val_11]; omega
    refine ⟨safe_div hW s3 _ _ _ (by simpa [s3eval] using hx) (by simp [s3two]), s4s, ?_⟩
    refine ⟨safe_sub hW s4 _ _ _ (by simp [s4cnt, s4one]; omega) (by simpa [s4cnt] using hkW),
      s5s, trivial⟩
  have heval := acts_evalG (P := Action.Safe W) _ s hrun hsafe
  refine ⟨s5, heval, s5s, ?_, ?_, ?_, ?_, s5k.2, s5k.1⟩
  · refine ⟨by simp [s5e], fun a => ?_⟩
    rw [s5m, s3m]
    by_cases ha : a = s.extent
    · subst ha; simp
    · rw [put_ne _ _ ha, if_neg (by simp; omega)]
  · simp [s5r, s4r, put]
  · simp [s5r]
  · intro r h10 h11 h12 h13
    simp [s5r, s4r, s3r, s2r, s1r, put, h10, h11, h12, h13]
/-! ## `emitBits` -/

/-- **Word emission.** From a running state with the constants 1 and 2 in their
registers, `emitBits w v` safely appends the `regs w`-bit little-endian encoding
of `regs v` as 0/1 cells, in at most `7 * regs w + 3` steps, changing only the
emission registers 10-13. -/
theorem emitBits_spec {W : Nat} (hW : 32 ≤ W) (w v : Operand) (hv : (v : Nat) ≠ 12)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hvW : s.regs v < 2 ^ W) (hwW : s.regs w < 2 ^ W) (hext : s.extent + s.regs w < 2 ^ W) :
    ∃ s' k, SafeEval W (emitBits w v) s s' k ∧ k ≤ 7 * s.regs w + 3 ∧ s'.status = .running ∧
      Emits s s' ((natToBitsLE (s.regs w) (s.regs v)).map bitToNat) ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  let width := s.regs w
  let v0 := s.regs v
  -- initialization: rECNT := w; rEVAL := v
  let t1 := execPrim (Prim.move rECNT w) s
  have f1 := exec_move s rECNT w
  let t2 := execPrim (Prim.move rEVAL v) t1
  have f2 := exec_move t1 rEVAL v
  have t2r : t2.regs = put (put s.regs 12 width) 13 v0 := by
    simp [t2, f2, t1, f1, width, v0, put, hv]
  have t2m : t2.memory = s.memory := by simp [t2, f2, t1, f1]
  have t2e : t2.extent = s.extent := by simp [t2, f2, t1, f1]
  have t2s : t2.status = .running := by simp [t2, f2, t1, f1, hrun]
  have t2k : t2.keys = s.keys ∧ t2.keyRegs = s.keyRegs := by simp [t2, f2, t1, f1]
  have hinit : SafeEval W (acts [.move rECNT w, .move rEVAL v]) s t2 2 :=
    acts_evalG (P := Action.Safe W) [.move rECNT w, .move rEVAL v] s hrun
      ⟨safe_move hW s _ _, by simp [Action.prim, exec_move, hrun], safe_move hW t1 _ _, t2s, trivial⟩
  -- loop invariant at `k` remaining bits
  let Q : Nat → State → Prop := fun k u =>
    u.status = .running ∧ u.regs 2 = 1 ∧ u.regs 9 = 2 ∧ u.regs 12 = k ∧ k ≤ width ∧
      u.regs 13 = v0 / 2 ^ (width - k) ∧
      Emits t2 u ((natToBitsLE (width - k) v0).map bitToNat) ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → u.regs r = s.regs r) ∧
      u.keyRegs = s.keyRegs ∧ u.keys = s.keys
  have hQ0 : Q width t2 := by
    refine ⟨t2s, by simp [t2r, put, hone], by simp [t2r, put, htwo], by simp [t2r, put],
      Nat.le_refl _, by simp [t2r, put], ?_, ?_, t2k.2, t2k.1⟩
    · simp only [Nat.sub_self, natToBitsLE, List.map_nil]
      exact Emits.refl t2
    · intro r h10 h11 h12 h13
      simp [t2r, put, h12, h13]
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rECNT emitBitsBody 5
    (fun k u hu => hu.1)
    (fun k u hu => by simp only [operand_val_12]; rw [hu.2.2.2.1]; omega)
    (fun u hu => by simp only [operand_val_12]; exact hu.2.2.2.1)
    (by
      intro k u hu
      obtain ⟨hurun, huone, hutwo, hucnt, hkle, hueval, huemit, hufr, hukr, huk⟩ := hu
      have hx : u.regs 13 < 2 ^ W := by
        rw [hueval]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hvW
      have hext' : u.extent + 1 < 2 ^ W := by
        rw [huemit.1, t2e]; simp only [List.length_map, natToBitsLE_length]; omega
      obtain ⟨u', hbody, hu'run, hu'emit, hu'eval, hu'cnt, hu'fr, hu'kr, hu'k⟩ :=
        emitBitsBody_spec hW u hurun huone hutwo hx (by omega) (by omega) hext'
      refine ⟨u', 5, hbody, Nat.le_refl _, hu'run, ?_, ?_, ?_, by omega, ?_, ?_, ?_,
        by rw [hu'kr, hukr], by rw [hu'k, huk]⟩
      · rw [hu'fr 2 (by decide) (by decide) (by decide) (by decide), huone]
      · rw [hu'fr 9 (by decide) (by decide) (by decide) (by decide), hutwo]
      · rw [hu'cnt, hucnt]; rfl
      · rw [hu'eval, hueval, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        congr 2
        omega
      · have hw' : width - k = (width - (k + 1)) + 1 := by omega
        rw [hw', natToBitsLE_succ_right, List.map_append]
        have := huemit.trans hu'emit
        rw [hueval] at this
        simpa [bitToNat_decide_mod_two] using this
      · intro r h10 h11 h12 h13
        rw [hu'fr r h10 h11 h12 h13, hufr r h10 h11 h12 h13])
    width t2 hQ0
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨hs'run, _, _, _, _, _, hs'emit, hs'fr, hs'kr, hs'k⟩ := hq
  refine ⟨s', 2 + j, EvalG.seq hinit hl, by omega, hs'run, ?_, hs'fr, hs'kr, hs'k⟩
  have hemit0 : Emits s t2 [] := by
    refine ⟨by simp [t2e], fun a => ?_⟩
    rw [t2m, if_neg (by simp only [List.length_nil]; omega)]
  have := hemit0.trans hs'emit
  simpa [width, v0] using this
/-! ## `emitTable` -/

/-- Registers the table machinery itself writes: emission 10-13, slot 14, guard 15, entry 16. -/
abbrev TableScratch (r : Nat) : Prop := 10 ≤ r ∧ r ≤ 16

theorem flatten_bits_length (width : Nat) :
    ∀ es : List Nat, (flattenPayloadWords (es.map (natToBitsLE width))).length = es.length * width
  | [] => by simp [flattenPayloadWords]
  | e :: rest => by
      simp only [List.map_cons, flattenPayloadWords, List.length_append, natToBitsLE_length,
        flatten_bits_length width rest, List.length_cons, Nat.succ_mul]
      omega

theorem flatten_range_succ (f : Nat → Nat) (width k : Nat) :
    flattenPayloadWords (((List.range (k + 1)).map f).map (natToBitsLE width)) =
      flattenPayloadWords (((List.range k).map f).map (natToBitsLE width)) ++
        natToBitsLE width (f k) := by
  rw [List.range_succ, List.map_append, List.map_append, flattenPayloadWords_append]
  simp [flattenPayloadWords]

theorem Emits.of_eq {s s' : State} (he : s'.extent = s.extent) (hm : s'.memory = s.memory) :
    Emits s s' [] := by
  refine ⟨by simp [he], fun a => ?_⟩
  rw [hm, if_neg (by simp only [List.length_nil]; omega)]

/-- **Table emission.** Let `entry` compute `f slot` into `rENT` (register 16)
from any running state that agrees with `s` on every register it does not
write and outside the table scratch, and on memory below `s.extent`, without
touching memory, extent, keys, key registers or registers 2, 9, 14, `count`,
`w`. Then `emitTable count w entry` safely appends the fixed-width encoding
of `(List.range (regs count)).map f` at width `regs w` as 0/1 cells. -/
theorem emitTable_spec {W : Nat} (hW : 32 ≤ W) (count w : Operand) (entry : Block)
    (f : Nat → Nat) (J : Nat) (writes : Nat → Prop)
    (hcount : ¬ TableScratch count) (hwreg : ¬ TableScratch w)
    (hwc : ¬ writes count) (hww : ¬ writes w) (hw2 : ¬ writes 2) (hw9 : ¬ writes 9)
    (hw14 : ¬ writes 14)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hcntW : s.regs count + 1 < 2 ^ W) (hwW : s.regs w < 2 ^ W)
    (hext : s.extent + s.regs count * s.regs w < 2 ^ W)
    (hentry : ∀ u, u.status = .running →
      (∀ r, ¬ writes r → ¬ TableScratch r → u.regs r = s.regs r) →
      (∀ a, a < s.extent → u.memory a = s.memory a) → s.extent ≤ u.extent → u.keys = s.keys →
      u.keyRegs = s.keyRegs → u.regs 14 < s.regs count →
      ∃ u' j, SafeEval W entry u u' j ∧ j ≤ J ∧ u'.status = .running ∧
        u'.regs 16 = f (u.regs 14) ∧ u'.regs 16 < 2 ^ W ∧ u'.memory = u.memory ∧
        u'.extent = u.extent ∧ (∀ r, ¬ writes r → r ≠ 16 → u'.regs r = u.regs r) ∧
        u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys) :
    ∃ s' k, SafeEval W (emitTable count w entry) s s' k ∧
      k ≤ s.regs count * (J + 7 * s.regs w + 7) + 3 ∧ s'.status = .running ∧
      Emits s s' ((flattenPayloadWords (((List.range (s.regs count)).map f).map
        (natToBitsLE (s.regs w)))).map bitToNat) ∧
      (∀ r, ¬ writes r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  let cnt := s.regs count
  let width := s.regs w
  have hc14 : (count : Nat) ≠ 14 := by intro h; exact hcount ⟨by omega, by omega⟩
  have hc15 : (count : Nat) ≠ 15 := by intro h; exact hcount ⟨by omega, by omega⟩
  -- initialization: slot := 0; go := [slot < count]
  let t1 := execPrim (Prim.constant rSLOT 0) s
  have f1 := exec_constant s rSLOT 0
  let t2 := execPrim (Prim.comparison .lt rGO rSLOT count) t1
  have f2 := exec_comparison t1 .lt rGO rSLOT count
  have t1cnt : t1.regs count = cnt := by simp [t1, f1, put, hc14, cnt]
  have t2r : t2.regs = put (put s.regs 14 0) 15 (if 0 < cnt then 1 else 0) := by
    simp [t2, f2, Comparison.eval, t1cnt]; simp [t1, f1]
  have t2m : t2.memory = s.memory := by simp [t2, f2, t1, f1]
  have t2e : t2.extent = s.extent := by simp [t2, f2, t1, f1]
  have t2s : t2.status = .running := by simp [t2, f2, t1, f1, hrun]
  have t2k : t2.keys = s.keys ∧ t2.keyRegs = s.keyRegs := by simp [t2, f2, t1, f1]
  have hinit : SafeEval W (acts [.constant rSLOT 0, .comparison .lt rGO rSLOT count]) s t2 2 :=
    acts_evalG (P := Action.Safe W) _ s hrun
      ⟨safe_constant hW s _ _, by simp [Action.prim, exec_constant, hrun],
        safe_comparison hW t1 _ _ _ _, t2s, trivial⟩
  -- invariant at `k` remaining slots
  let Q : Nat → State → Prop := fun k u =>
    u.status = .running ∧ k ≤ cnt ∧ u.regs 14 = cnt - k ∧
      u.regs 15 = (if cnt - k < cnt then 1 else 0) ∧
      Emits t2 u ((flattenPayloadWords (((List.range (cnt - k)).map f).map
        (natToBitsLE width))).map bitToNat) ∧
      (∀ r, ¬ writes r → ¬ TableScratch r → u.regs r = s.regs r) ∧
      u.keyRegs = s.keyRegs ∧ u.keys = s.keys
  have hQ0 : Q cnt t2 := by
    refine ⟨t2s, Nat.le_refl _, by simp [t2r, put], by simp [t2r, put], ?_, ?_, t2k.2, t2k.1⟩
    · simp only [Nat.sub_self, List.range_zero, List.map_nil, flattenPayloadWords]
      exact Emits.refl t2
    · intro r hr hs
      have h14 : r ≠ 14 := by intro h; exact hs ⟨by omega, by omega⟩
      have h15 : r ≠ 15 := by intro h; exact hs ⟨by omega, by omega⟩
      simp [t2r, put, h14, h15]
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rGO (emitTableBody count w entry)
    (J + 7 * width + 5)
    (fun k u hu => hu.1)
    (fun k u hu => by
      simp only [operand_val_15]; rw [hu.2.2.2.1]; have := hu.2.1; split <;> omega)
    (fun u hu => by simp only [operand_val_15]; rw [hu.2.2.2.1]; simp)
    (by
      intro k u hu
      obtain ⟨hurun, hkle, huslot, _, huemit, hufr, hukr, huk⟩ := hu
      have huone : u.regs 2 = 1 := by
        rw [hufr 2 hw2 (by simp [TableScratch]), hone]
      have hutwo : u.regs 9 = 2 := by
        rw [hufr 9 hw9 (by simp [TableScratch]), htwo]
      have hucnt : u.regs count = cnt := hufr count hwc hcount
      have huw : u.regs w = width := hufr w hww hwreg
      have huext : u.extent = s.extent + (cnt - (k + 1)) * width := by
        rw [huemit.1, t2e, List.length_map, flatten_bits_length, List.length_map,
          List.length_range]
      -- the entry block
      obtain ⟨u1, j1, hentryEval, hj1, hu1run, hu1ent, hu1entW, hu1mem, hu1ext, hu1fr,
          hu1kr, hu1k⟩ :=
        hentry u hurun hufr
          (fun a ha => by
            rw [huemit.memory_below (by rw [t2e]; exact ha), t2m])
          (by rw [huext]; omega) huk hukr (by rw [huslot]; omega)
      have hu1one : u1.regs 2 = 1 := by rw [hu1fr 2 hw2 (by decide), huone]
      have hu1two : u1.regs 9 = 2 := by rw [hu1fr 9 hw9 (by decide), hutwo]
      have hu1w : u1.regs w = width := by
        rw [hu1fr w hww (by intro h; exact hwreg ⟨by omega, by omega⟩), huw]
      have hu1slot : u1.regs 14 = cnt - (k + 1) := by rw [hu1fr 14 hw14 (by decide), huslot]
      have hu1cnt : u1.regs count = cnt := by
        rw [hu1fr count hwc (by intro h; exact hcount ⟨by omega, by omega⟩), hucnt]
      have hbound : (cnt - (k + 1)) * width + width ≤ cnt * width := by
        have : (cnt - (k + 1) + 1) * width ≤ cnt * width := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      -- the word emission
      obtain ⟨u2, j2, hbitsEval, hj2, hu2run, hu2emit, hu2fr, hu2kr, hu2k⟩ :=
        emitBits_spec hW w rENT (by decide) u1 hu1run hu1one hu1two hu1entW
          (by rw [hu1w]; exact hwW)
          (by have hext' : s.extent + cnt * width < 2 ^ W := hext
              rw [hu1w, hu1ext, huext]; omega)
      have hu2slot : u2.regs 14 = cnt - (k + 1) := by
        rw [hu2fr 14 (by decide) (by decide) (by decide) (by decide), hu1slot]
      have hu2one : u2.regs 2 = 1 := by
        rw [hu2fr 2 (by decide) (by decide) (by decide) (by decide), hu1one]
      have hu2cnt : u2.regs count = cnt := by
        rw [hu2fr count (by intro h; exact hcount ⟨by omega, by omega⟩)
          (by intro h; exact hcount ⟨by omega, by omega⟩)
          (by intro h; exact hcount ⟨by omega, by omega⟩)
          (by intro h; exact hcount ⟨by omega, by omega⟩), hu1cnt]
      -- advance and retest
      let u3 := execPrim (Prim.arithmetic .add rSLOT rSLOT rONE) u2
      have g3 := exec_arithmetic u2 .add rSLOT rSLOT rONE
      let u4 := execPrim (Prim.comparison .lt rGO rSLOT count) u3
      have g4 := exec_comparison u3 .lt rGO rSLOT count
      have u3r : u3.regs = put u2.regs 14 (cnt - (k + 1) + 1) := by
        simp [u3, g3, Arithmetic.eval, hu2slot, hu2one]
      have u3cnt : u3.regs count = cnt := by simp [u3r, put, hc14, hu2cnt]
      have u4r : u4.regs = put (put u2.regs 14 (cnt - (k + 1) + 1)) 15
          (if cnt - (k + 1) + 1 < cnt then 1 else 0) := by
        simp [u4, g4, Comparison.eval, u3cnt]; simp [u3r]
      have u4m : u4.memory = u2.memory := by simp [u4, g4, u3, g3]
      have u4e : u4.extent = u2.extent := by simp [u4, g4, u3, g3]
      have u4s : u4.status = .running := by simp [u4, g4, u3, g3, hu2run]
      have u4k : u4.keys = u2.keys ∧ u4.keyRegs = u2.keyRegs := by simp [u4, g4, u3, g3]
      have hadv : SafeEval W (acts [.arithmetic .add rSLOT rSLOT rONE,
          .comparison .lt rGO rSLOT count]) u2 u4 2 :=
        acts_evalG (P := Action.Safe W) _ u2 hu2run
          ⟨safe_add hW u2 _ _ _ (by simp only [operand_val_14, operand_val_2]; omega),
            by simp [Action.prim, exec_arithmetic, hu2run],
            safe_comparison hW u3 _ _ _ _, u4s, trivial⟩
      refine ⟨u4, j1 + (j2 + 2), EvalG.seq hentryEval (EvalG.seq hbitsEval hadv),
        by omega, u4s, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [u4r, put]; omega
      · simp [u4r, put]
        have h1 : cnt - (k + 1) + 1 = cnt - k := by omega
        rw [h1]
      · have hsub : cnt - k = (cnt - (k + 1)) + 1 := by omega
        rw [hsub, flatten_range_succ, List.map_append]
        have e01 : Emits u u1 [] := Emits.of_eq hu1ext hu1mem
        have e34 : Emits u2 u4 [] := Emits.of_eq u4e u4m
        have := ((huemit.trans e01).trans hu2emit).trans e34
        simpa [hu1ent, hu1w, huslot] using this
      · intro r hr hs
        have h14 : r ≠ 14 := by intro h; exact hs ⟨by omega, by omega⟩
        have h15 : r ≠ 15 := by intro h; exact hs ⟨by omega, by omega⟩
        have h10 : r ≠ 10 := by intro h; exact hs ⟨by omega, by omega⟩
        have h11 : r ≠ 11 := by intro h; exact hs ⟨by omega, by omega⟩
        have h12 : r ≠ 12 := by intro h; exact hs ⟨by omega, by omega⟩
        have h13 : r ≠ 13 := by intro h; exact hs ⟨by omega, by omega⟩
        have h16 : r ≠ 16 := by intro h; exact hs ⟨by omega, by omega⟩
        rw [u4r, put_ne _ _ h15, put_ne _ _ h14, hu2fr r h10 h11 h12 h13, hu1fr r hr h16,
          hufr r hr hs]
      · rw [u4k.2, hu2kr, hu1kr, hukr]
      · rw [u4k.1, hu2k, hu1k, huk])
    cnt t2 hQ0
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨hs'run, _, _, _, hs'emit, hs'fr, hs'kr, hs'k⟩ := hq
  refine ⟨s', 2 + j, EvalG.seq hinit hl, ?_, hs'run, ?_, hs'fr, hs'kr, hs'k⟩
  · have h7 : J + 7 * width + 5 + 2 = J + 7 * width + 7 := by omega
    rw [h7] at hj
    show 2 + j ≤ cnt * (J + 7 * width + 7) + 3
    omega
  · have := (Emits.of_eq t2e t2m).trans hs'emit
    simpa [cnt, width] using this
/-! ## `log2Block` -/

theorem div_pow_ge_two_of_log2 {x L k : Nat} (hx : x ≠ 0) (hL : L = Nat.log2 x) (hk : k + 1 ≤ L) :
    2 ≤ x / 2 ^ (L - (k + 1)) := by
  have hself : 2 ^ L ≤ x := by rw [hL]; exact Nat.log2_self_le hx
  have hsplit : 2 ^ L = 2 ^ (L - (k + 1)) * 2 ^ (k + 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (L - (k + 1)) := Nat.pow_pos (by decide)
  have h2 : 2 ≤ 2 ^ (k + 1) := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_succ (Nat.zero_le k))
    simpa using this
  rw [Nat.le_div_iff_mul_le hpos]
  calc 2 * 2 ^ (L - (k + 1)) ≤ 2 ^ (k + 1) * 2 ^ (L - (k + 1)) := Nat.mul_le_mul_right _ h2
    _ = 2 ^ L := by rw [hsplit, Nat.mul_comm]
    _ ≤ x := hself

theorem div_pow_log2_lt_two (x : Nat) : x / 2 ^ Nat.log2 x < 2 := by
  have hlt : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
  rw [Nat.pow_succ] at hlt
  exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr (by rw [Nat.mul_comm]; exact hlt)

/-- **Halving loop.** `log2Block dst src` safely sets `regs dst` to
`Nat.log2 (regs src)` in at most `5 * Nat.log2 (regs src) + 4` steps, writing
only `dst`, 20 and 21, without touching memory, extent or keys. -/
theorem log2Block_spec {W : Nat} (hW : 32 ≤ W) (dst src : Operand)
    (hd2 : (dst : Nat) ≠ 2) (hd9 : (dst : Nat) ≠ 9) (hd20 : (dst : Nat) ≠ 20)
    (hd21 : (dst : Nat) ≠ 21)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hxW : s.regs src < 2 ^ W) :
    ∃ s' k, SafeEval W (log2Block dst src) s s' k ∧ k ≤ 5 * Nat.log2 (s.regs src) + 4 ∧
      s'.status = .running ∧ s'.regs dst = Nat.log2 (s.regs src) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧
      (∀ r : Nat, r ≠ (dst : Nat) → r ≠ 20 → r ≠ 21 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  have n2 : (2 : Nat) ≠ dst := fun h => hd2 h.symm
  have n9 : (9 : Nat) ≠ dst := fun h => hd9 h.symm
  have n20 : (20 : Nat) ≠ dst := fun h => hd20 h.symm
  have n21 : (21 : Nat) ≠ dst := fun h => hd21 h.symm
  generalize hx : s.regs src = x at hxW ⊢
  generalize hL : Nat.log2 x = L
  have hLx : L ≤ x := by rw [← hL]; exact Nat.log2_le_self x
  have hLW : L < 2 ^ W := Nat.lt_of_le_of_lt hLx hxW
  -- initialization
  let t1 := execPrim (Prim.move rLX src) s
  have f1 := exec_move s rLX src
  let t2 := execPrim (Prim.constant dst 0) t1
  have f2 := exec_constant t1 dst 0
  let t3 := execPrim (Prim.comparison .lt rLC rONE rLX) t2
  have f3 := exec_comparison t2 .lt rLC rONE rLX
  have t1r : t1.regs = put s.regs 20 x := by simp [t1, f1, hx]
  have t2r : t2.regs = put t1.regs dst 0 := by simp [t2, f2]
  have t2one : t2.regs 2 = 1 := by
    rw [t2r, put_ne _ _ n2, t1r, put_ne _ _ (by decide), hone]
  have t2two : t2.regs 9 = 2 := by
    rw [t2r, put_ne _ _ n9, t1r, put_ne _ _ (by decide), htwo]
  have t2lx : t2.regs 20 = x := by rw [t2r, put_ne _ _ n20, t1r, put_same]
  have t2dst : t2.regs dst = 0 := by rw [t2r, put_same]
  have t3r : t3.regs = put t2.regs 21 (if 1 < x then 1 else 0) := by
    simp [t3, f3, Comparison.eval, t2one, t2lx]
  have t3m : t3.memory = s.memory := by simp [t3, f3, t2, f2, t1, f1]
  have t3e : t3.extent = s.extent := by simp [t3, f3, t2, f2, t1, f1]
  have t3s : t3.status = .running := by simp [t3, f3, t2, f2, t1, f1, hrun]
  have t3k : t3.keys = s.keys ∧ t3.keyRegs = s.keyRegs := by simp [t3, f3, t2, f2, t1, f1]
  have hinit : SafeEval W (acts [.move rLX src, .constant dst 0,
      .comparison .lt rLC rONE rLX]) s t3 3 :=
    acts_evalG (P := Action.Safe W) _ s hrun
      ⟨safe_move hW s _ _, by simp [Action.prim, exec_move, hrun],
        safe_constant hW t1 _ _, by simp [Action.prim, f1, exec_constant, hrun],
        safe_comparison hW t2 _ _ _ _, t3s, trivial⟩
  let Q : Nat → State → Prop := fun k u =>
    u.status = .running ∧ k ≤ L ∧ u.regs 2 = 1 ∧ u.regs 9 = 2 ∧
      u.regs 20 = x / 2 ^ (L - k) ∧ u.regs dst = L - k ∧
      u.regs 21 = (if 1 < x / 2 ^ (L - k) then 1 else 0) ∧
      u.memory = s.memory ∧ u.extent = s.extent ∧
      (∀ r : Nat, r ≠ (dst : Nat) → r ≠ 20 → r ≠ 21 → u.regs r = s.regs r) ∧
      u.keyRegs = s.keyRegs ∧ u.keys = s.keys
  have hQ0 : Q L t3 := by
    refine ⟨t3s, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_, t3m, t3e, ?_, t3k.2, t3k.1⟩
    · rw [t3r, put_ne _ _ (by decide), t2one]
    · rw [t3r, put_ne _ _ (by decide), t2two]
    · rw [t3r, put_ne _ _ (by decide), t2lx, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    · rw [t3r, put_ne _ _ (fun h => hd21 h), t2dst, Nat.sub_self]
    · rw [t3r, put_same, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    · intro r hd h20 h21
      rw [t3r, put_ne _ _ h21, t2r, put_ne _ _ hd, t1r, put_ne _ _ h20]
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rLC (log2Body dst) 3
    (fun k u hu => hu.1)
    (fun k u hu => by
      obtain ⟨_, hkL, _, _, _, _, hlc, _⟩ := hu
      simp only [operand_val_21]
      rw [hlc]
      have hx0 : x ≠ 0 := by intro h; rw [h, Nat.log2_zero] at hL; omega
      have := div_pow_ge_two_of_log2 hx0 hL.symm hkL
      rw [if_pos (by omega)]; decide)
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, hlc, _⟩ := hu
      simp only [operand_val_21]
      rw [hlc, Nat.sub_zero, if_neg (by have := div_pow_log2_lt_two x; rw [hL] at this; omega)])
    (by
      intro k u hu
      obtain ⟨hurun, hkL, huone, hutwo, hulx, hudst, _, humem, huext, hufr, hukr, huk⟩ := hu
      let u1 := execPrim (Prim.arithmetic .div rLX rLX rTWO) u
      have g1 := exec_arithmetic u .div rLX rLX rTWO
      let u2 := execPrim (Prim.arithmetic .add dst dst rONE) u1
      have g2 := exec_arithmetic u1 .add dst dst rONE
      let u3 := execPrim (Prim.comparison .lt rLC rONE rLX) u2
      have g3 := exec_comparison u2 .lt rLC rONE rLX
      have hdiv : x / 2 ^ (L - (k + 1)) / 2 = x / 2 ^ (L - k) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]; congr 2; omega
      have u1r : u1.regs = put u.regs 20 (x / 2 ^ (L - k)) := by
        simp [u1, g1, Arithmetic.eval, hulx, hutwo, hdiv]
      have u1dst : u1.regs dst = L - (k + 1) := by rw [u1r, put_ne _ _ hd20, hudst]
      have u1one : u1.regs 2 = 1 := by rw [u1r, put_ne _ _ (by decide), huone]
      have u2r : u2.regs = put u1.regs dst (L - k) := by
        show (execPrim (Prim.arithmetic .add dst dst rONE) u1).regs = _
        rw [g2]
        show put u1.regs dst (u1.regs dst + u1.regs 2) = _
        rw [u1dst, u1one, show L - (k + 1) + 1 = L - k by omega]
      have u2one : u2.regs 2 = 1 := by rw [u2r, put_ne _ _ n2, u1one]
      have u2two : u2.regs 9 = 2 := by
        rw [u2r, put_ne _ _ n9, u1r, put_ne _ _ (by decide), hutwo]
      have u2lx : u2.regs 20 = x / 2 ^ (L - k) := by rw [u2r, put_ne _ _ n20, u1r, put_same]
      have u3r : u3.regs = put u2.regs 21 (if 1 < x / 2 ^ (L - k) then 1 else 0) := by
        simp [u3, g3, Comparison.eval, u2one, u2lx]
      have u3s : u3.status = .running := by simp [u3, g3, u2, g2, u1, g1, hurun]
      have hsafe : ActsOK (Action.Safe W) [.arithmetic .div rLX rLX rTWO,
          .arithmetic .add dst dst rONE, .comparison .lt rLC rONE rLX] u := by
        refine ⟨safe_div hW u _ _ _ ?_ (by simp [hutwo]), by simp [Action.prim, exec_arithmetic, hurun], ?_⟩
        · simp only [operand_val_20]; rw [hulx]
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hxW
        refine ⟨safe_add hW u1 _ _ _ ?_, by simp [Action.prim, exec_arithmetic, hurun], ?_⟩
        · show u1.regs dst + u1.regs 2 < 2 ^ W
          rw [u1dst, u1one]; omega
        exact ⟨safe_comparison hW u2 _ _ _ _, u3s, trivial⟩
      refine ⟨u3, 3, acts_evalG (P := Action.Safe W) _ u hurun hsafe, Nat.le_refl _, u3s,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [u3r, put_ne _ _ (by decide), u2one]
      · rw [u3r, put_ne _ _ (by decide), u2two]
      · rw [u3r, put_ne _ _ (by decide), u2lx]
      · rw [u3r, put_ne _ _ (fun h => hd21 h), u2r, put_same]
      · rw [u3r, put_same]
      · simp [u3, g3, u2, g2, u1, g1, humem]
      · simp [u3, g3, u2, g2, u1, g1, huext]
      · intro r hd h20 h21
        rw [u3r, put_ne _ _ h21, u2r, put_ne _ _ hd, u1r, put_ne _ _ h20, hufr r hd h20 h21]
      · simp [u3, g3, u2, g2, u1, g1, hukr]
      · simp [u3, g3, u2, g2, u1, g1, huk])
    L t3 hQ0
  obtain ⟨s', j, hl, hj, hq⟩ := hloop
  obtain ⟨hs'run, _, _, _, _, hs'dst, _, hs'mem, hs'ext, hs'fr, hs'kr, hs'k⟩ := hq
  refine ⟨s', 3 + j, EvalG.seq hinit hl, ?_, hs'run, by rw [hs'dst, Nat.sub_zero],
    hs'mem, hs'ext, hs'fr, hs'kr, hs'k⟩
  have : L * (3 + 2) = 5 * L := by rw [Nat.mul_comm]
  omega
end RMQ.SuccinctFinal.PackedConstruction.Proof
