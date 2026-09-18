import RMQ.Core.WordRAM.Construction.Proof.Loops
import RMQ.Core.WordRAM.Construction.Proof.Stage2

/-! # PRE-1 builder proofs: the size-only geometry bank

Outside the builder firewall. `geometryPrelude` computes, from the input length
in register 1 by charged arithmetic only, every size-only quantity the later
phases use as a loop bound, a width or a budget. Each register is identified
with its reference definition (`PackedCellProbe.packed*`, the layout of
`SuccinctClose.RelativeRmm.canonicalLayout`, the microtable row counts and
widths, the interior raw payload bits, the access overhead budget,
`packedReviewerCellWidth` and `PackedWordRAM.wordWidth`).

All capacity obligations are discharged from the single premise
`2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W`, which holds at `W = wordWidth n`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder SuccinctSpace SuccinctClose PackedCellProbe

theorem log2_succ_lt_pow {W x : Nat} (hW : 32 ≤ W) (hx : x < 2 ^ W) :
    Nat.log2 x + 1 < 2 ^ W := by
  have h1 : Nat.log2 x < W := log2_lt_width (by omega) hx
  have h2 : W < 2 ^ W := Nat.lt_two_pow_self
  omega

/-- **Word bits.** `wordBitsBlock dst src` sets `dst` to `Nat.log2 x + 1`. -/
theorem RegSpec.wordBits {W : Nat} (hW : 32 ≤ W) (dst src : Operand)
    (hd2 : (dst : Nat) ≠ 2) (hd9 : (dst : Nat) ≠ 9) (hd20 : (dst : Nat) ≠ 20)
    (hd21 : (dst : Nat) ≠ 21) :
    RegSpec W (wordBitsBlock dst src) (fun r => r 2 = 1 ∧ r 9 = 2 ∧ r src < 2 ^ W)
      (fun r => put (put (put r 20 (r src / 2 ^ Nat.log2 (r src))) 21 0) dst
        (Nat.log2 (r src) + 1))
      (fun r => 5 * Nat.log2 (r src) + 5) := by
  refine (RegSpec.seq (RegSpec.log2 hW dst src hd2 hd9 hd20 hd21)
    (RegSpec.pure hW [.arithmetic .add dst dst rONE])).weaken ?_ ?_ ?_
  · intro r ⟨h1, h9, hx⟩
    refine ⟨⟨h1, h9, hx⟩, ?_, trivial⟩
    have hl := log2_succ_lt_pow hW hx
    have hne : (2 : Nat) ≠ dst := fun h => hd2 h.symm
    refine ⟨?_, by simp, by simp, by simp⟩
    show put (put (put r 20 _) 21 0) dst (Nat.log2 (r src)) dst +
      put (put (put r 20 _) 21 0) dst (Nat.log2 (r src)) 2 < 2 ^ W
    rw [put_same, put_ne _ _ hne, put_ne _ _ (by decide), put_ne _ _ (by decide), h1]
    exact hl
  · intro r ⟨h1, _, _⟩
    have hne : (2 : Nat) ≠ dst := fun h => hd2 h.symm
    show put (put (put (put r 20 _) 21 0) dst (Nat.log2 (r src))) dst
      (put (put (put r 20 _) 21 0) dst (Nat.log2 (r src)) dst +
        put (put (put r 20 _) 21 0) dst (Nat.log2 (r src)) 2) = _
    rw [put_same, put_ne _ _ hne, put_ne _ _ (by decide), put_ne _ _ (by decide), h1]
    funext x
    simp only [put]
    split <;> rfl
  · intro r _
    show 5 * Nat.log2 (r src) + 4 + 1 ≤ 5 * Nat.log2 (r src) + 5
    omega


/-! ## Frames of straight-line actions -/

/-- The register a register-only action writes. -/
def pureDst : Action → Option Nat
  | .constant d _ => some d
  | .move d _ => some d
  | .arithmetic _ d _ _ => some d
  | .comparison _ d _ _ => some d
  | _ => none

theorem pureReg_frame (a : Action) (r : Registers) (x : Nat) (h : pureDst a ≠ some x) :
    pureReg a r x = r x := by
  cases a <;> simp only [pureReg, pureDst] at h ⊢
  all_goals first
    | rfl
    | exact put_ne _ _ (fun hx => h (by rw [hx]))

theorem pureRegs_frame : ∀ (ops : List Action) (r : Registers) (x : Nat),
    (∀ a ∈ ops, pureDst a ≠ some x) → pureRegs ops r x = r x
  | [], _, _, _ => rfl
  | a :: rest, r, x, h => by
      show pureRegs rest (pureReg a r) x = r x
      rw [pureRegs_frame rest _ x (fun b hb => h b (List.mem_cons_of_mem _ hb)),
        pureReg_frame a r x (h a (List.mem_cons_self))]

/-! ## The bank: reference values, invariant and steps -/

/-- Reference value of bank register `38 + i`. -/
def geoVal (n : Nat) : Nat → Nat
  | 0 => 2 * n
  | 1 => packedRankWordSize n
  | 2 => GenericSelect.superStride (2 * n)
  | 3 => GenericSelect.ell (2 * n)
  | 4 => GenericSelect.localStride (2 * n)
  | 5 => GenericSelect.localSlotsPerSuper (2 * n)
  | 6 => GenericSelect.superLongSpan (2 * n)
  | 7 => packedSuperSlots n
  | 8 => packedLocalSlots n
  | 9 => packedSparseSlots n
  | 10 => packedRankBlockWidth n
  | 11 => packedLocalWidth n
  | 12 => packedLongFlagWordSize n
  | 13 => packedSparseWordSize n
  | 14 => packedRankSuperSlots n
  | 15 => packedRankBlockSlots n
  | 16 => packedLongFlagRankSlots n
  | 17 => packedSparseRankSlots n
  | 18 => 2 * geoBase n
  | 19 => geoBlocks n / geoBase n + 1
  | 20 => SuccinctRank.machineWordBits (geoMacro n)
  | 21 => SuccinctRank.machineWordBits (geoMacros n)
  | 22 => SuccinctRank.machineWordBits (geoBlocks n)
  | 23 => 2 * (Nat.log2 (geoBase n) + 1) + 3
  | 24 => geoMacros n * (SuccinctRank.machineWordBits (geoMacro n) * geoMacro n)
  | 25 => SuccinctRank.machineWordBits (geoMacros n) * geoMacros n
  | 26 => bpFringeChunkBits (2 * n)
  | 27 => bpFringeChunkRowCount (bpFringeChunkBits (2 * n))
  | 28 => bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n))
  | 29 => bpChunkSelectRowCount (bpFringeChunkBits (2 * n))
  | 30 => bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n))
  | 31 => canonicalRelativeRmmInteriorRawPayloadOverhead n
  | 32 => bpFringeTableOverhead n
  | 33 => bpChunkSelectTableOverhead n
  | 34 => 2 * n / packedRankWordSize n *
      (GenericSelect.ell (2 * n) * (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n)))
  | 35 => 2 * n / GenericSelect.ell (2 * n)
  | 36 => genericSparseExceptionBPCloseAccessOverhead n
  | 37 => packedReviewerCellWidth n
  | 38 => PackedWordRAM.wordWidth n
  | _ => 0

/-- Registers the bank reads but never writes: length, constants, interior subset. -/
def GeoBase (n : Nat) (r : Registers) : Prop :=
  r 1 = n ∧ r 2 = 1 ∧ r 9 = 2 ∧ r 30 = geoBase n ∧ r 31 = geoMacro n ∧
    r 32 = geoBlocks n ∧ r 33 = geoMacros n ∧
    r 34 = bpSparseLevelDomain (geoMacro n) ∧ r 35 = bpSparseLevelDomain (geoMacros n) ∧
    r 36 = bpSparseLevelWidth (bpSparseLevelDomain (geoMacro n)) ∧
    r 37 = bpSparseLevelWidth (bpSparseLevelDomain (geoMacros n))

/-- The first `k` bank registers hold their reference values. -/
def GeoUpTo (n k : Nat) (r : Registers) : Prop := ∀ i, i < k → r (38 + i) = geoVal n i

/-- Bank step `i` from a state with the base and the first `i` bank registers. -/
def GeoStepOK (W n i : Nat) (b : Block) : Prop :=
  ∀ s : State, s.status = .running → GeoBase n s.regs → GeoUpTo n i s.regs →
    ∃ s' k, SafeEval W b s s' k ∧ k ≤ 5 * W + 20 ∧ s'.status = .running ∧
      s'.regs (38 + i) = geoVal n i ∧
      (∀ x : Nat, x ≠ 38 + i → ¬ (20 ≤ x ∧ x ≤ 28) → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧
      s'.keyRegs = s.keyRegs

theorem GeoStepOK.of_regSpec {W n i : Nat} {b : Block} {pre : Registers → Prop}
    {F : Registers → Registers} {cost : Registers → Nat} (h : RegSpec W b pre F cost)
    (hpre : ∀ r, GeoBase n r → GeoUpTo n i r → pre r)
    (hcost : ∀ r, GeoBase n r → GeoUpTo n i r → cost r ≤ 5 * W + 20)
    (hval : ∀ r, GeoBase n r → GeoUpTo n i r → F r (38 + i) = geoVal n i)
    (hframe : ∀ r (x : Nat), x ≠ 38 + i → ¬ (20 ≤ x ∧ x ≤ 28) → F r x = r x) :
    GeoStepOK W n i b := by
  intro s hrun hb hg
  obtain ⟨s', k, e, hk, hr, hR, hm, he, hks, hkr⟩ := h s hrun (hpre _ hb hg)
  exact ⟨s', k, e, Nat.le_trans hk (hcost _ hb hg), hr, by rw [hR]; exact hval _ hb hg,
    fun x h1 h2 => by rw [hR]; exact hframe _ x h1 h2, hm, he, hks, hkr⟩

theorem wordBits_cost_le {W x : Nat} (hW : 32 ≤ W) (hx : x < 2 ^ W) :
    5 * Nat.log2 x + 5 ≤ 5 * W + 20 := by
  have := log2_lt_width (by omega) hx
  omega

/-- Frame of `RegSpec.wordBits`. -/
theorem wordBitsF_frame (r : Registers) (dst src : Operand) (x : Nat) (hd : x ≠ dst)
    (h20 : x ≠ 20) (h21 : x ≠ 21) :
    put (put (put r 20 (r src / 2 ^ Nat.log2 (r src))) 21 0) dst (Nat.log2 (r src) + 1) x =
      r x := by
  rw [put_ne _ _ hd, put_ne _ _ h21, put_ne _ _ h20]

/-! ## Capacity -/

theorem cap_of_le {W n v : Nat} (hcap : 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W)
    (hv : v ≤ 65536 * (2 * n + 4) ^ 6) : v < 2 ^ W := by
  have h1 : (2 * n + 4) ^ 6 ≤ (2 * n + 4) ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : 65536 * (2 * n + 4) ^ 6 ≤ 2 ^ 32 * (2 * n + 4) ^ 8 :=
    Nat.mul_le_mul (by decide) h1
  omega

theorem powB_succ (n k : Nat) : 4 * (2 * n + 4) ^ k ≤ (2 * n + 4) ^ (k + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

theorem mulB {n a b i j k : Nat} (ha : a ≤ (2 * n + 4) ^ i) (hb : b ≤ (2 * n + 4) ^ j)
    (hk : i + j = k) : a * b ≤ (2 * n + 4) ^ k := by
  rw [← hk, Nat.pow_add]
  exact Nat.mul_le_mul ha hb

theorem log2_succ_le_succ (x : Nat) : Nat.log2 x + 1 ≤ x + 1 := by
  have := Nat.log2_le_self x
  omega

/-- Powers of `B = 2 n + 4` used by `omega` as atoms. -/
theorem powB_facts (n : Nat) :
    4 ≤ (2 * n + 4) ^ 1 ∧ 4 * (2 * n + 4) ^ 1 ≤ (2 * n + 4) ^ 2 ∧
    4 * (2 * n + 4) ^ 2 ≤ (2 * n + 4) ^ 3 ∧ 4 * (2 * n + 4) ^ 3 ≤ (2 * n + 4) ^ 4 ∧
    4 * (2 * n + 4) ^ 4 ≤ (2 * n + 4) ^ 5 ∧ 4 * (2 * n + 4) ^ 5 ≤ (2 * n + 4) ^ 6 ∧
    (2 * n + 4) ^ 1 = 2 * n + 4 := by
  refine ⟨by simp, powB_succ n 1, powB_succ n 2, powB_succ n 3, powB_succ n 4, powB_succ n 5,
    by simp⟩

/-! ## Step shapes -/

/-- Register function of `wordBitsBlock dst src`. -/
def wordBitsF (r : Registers) (dst src : Operand) : Registers :=
  put (put (put r 20 (r src / 2 ^ Nat.log2 (r src))) 21 0) dst (Nat.log2 (r src) + 1)

/-- Register function of `log2Block dst src`. -/
def log2F (r : Registers) (dst src : Operand) : Registers :=
  put (put (put r 20 (r src / 2 ^ Nat.log2 (r src))) 21 0) dst (Nat.log2 (r src))

theorem wordBits_cost_le5 {W x : Nat} (hW : 32 ≤ W) (hx : x < 2 ^ W) :
    5 * Nat.log2 x + 5 ≤ 5 * W := by
  have := log2_lt_width (by omega) hx
  omega

theorem scratch_of_all {ops : List Action} {P : Nat → Bool}
    (h : (ops.filterMap pureDst).all P = true) {a : Action} (ha : a ∈ ops) {x : Nat}
    (hax : pureDst a = some x) : P x = true :=
  List.all_eq_true.mp h x (List.mem_filterMap.mpr ⟨a, ha, hax⟩)

theorem geoStep_pure {W n i : Nat} (hW : 32 ≤ W) (ops : List Action) (hlen : ops.length ≤ 20)
    (hdst : (ops.filterMap pureDst).all (fun d => d == 38 + i || (20 ≤ d && d ≤ 28)) = true)
    (hpre : ∀ r, GeoBase n r → GeoUpTo n i r → pureOKs W ops r)
    (hval : ∀ r, GeoBase n r → GeoUpTo n i r → pureRegs ops r (38 + i) = geoVal n i) :
    GeoStepOK W n i (acts ops) := by
  refine GeoStepOK.of_regSpec (RegSpec.pure hW ops) hpre (fun _ _ _ => by omega) hval ?_
  intro r x hx1 hx2
  apply pureRegs_frame
  intro a ha hax
  have := scratch_of_all hdst ha hax
  simp at this
  omega

theorem geoStep_wordBits {W n i : Nat} (hW : 32 ≤ W) (dst src : Operand)
    (hdst : (dst : Nat) = 38 + i) (hd2 : (dst : Nat) ≠ 2) (hd9 : (dst : Nat) ≠ 9)
    (hd20 : (dst : Nat) ≠ 20) (hd21 : (dst : Nat) ≠ 21)
    (hsrc : ∀ r, GeoBase n r → GeoUpTo n i r → r src < 2 ^ W)
    (hval : ∀ r, GeoBase n r → GeoUpTo n i r → Nat.log2 (r src) + 1 = geoVal n i) :
    GeoStepOK W n i (wordBitsBlock dst src) := by
  refine GeoStepOK.of_regSpec (RegSpec.wordBits hW dst src hd2 hd9 hd20 hd21)
    (fun r hb hg => ⟨hb.2.1, hb.2.2.1, hsrc r hb hg⟩)
    (fun r hb hg => by have := wordBits_cost_le5 hW (hsrc r hb hg); omega) ?_ ?_
  · intro r hb hg
    show put (put (put r 20 _) 21 0) dst _ (38 + i) = _
    rw [← hdst, put_same]
    exact hval r hb hg
  · intro r x hx1 hx2
    exact wordBitsF_frame r dst src x (by rw [hdst]; exact hx1) (by omega) (by omega)

theorem geoStep_pure_wordBits {W n i : Nat} (hW : 32 ≤ W) (ops : List Action) (dst src : Operand)
    (hlen : ops.length ≤ 15) (hdst : (dst : Nat) = 38 + i) (hd2 : (dst : Nat) ≠ 2)
    (hd9 : (dst : Nat) ≠ 9) (hd20 : (dst : Nat) ≠ 20) (hd21 : (dst : Nat) ≠ 21)
    (hops : (ops.filterMap pureDst).all (fun d => 20 ≤ d && d ≤ 28) = true)
    (hpre : ∀ r, GeoBase n r → GeoUpTo n i r → pureOKs W ops r ∧ pureRegs ops r src < 2 ^ W)
    (hval : ∀ r, GeoBase n r → GeoUpTo n i r →
      Nat.log2 (pureRegs ops r src) + 1 = geoVal n i) :
    GeoStepOK W n i (.seq (acts ops) (wordBitsBlock dst src)) := by
  have hfr : ∀ r (x : Nat), ¬ (20 ≤ x ∧ x ≤ 28) → pureRegs ops r x = r x := by
    intro r x hx
    apply pureRegs_frame
    intro a ha hax
    have := scratch_of_all hops ha hax
    simp at this
    omega
  refine GeoStepOK.of_regSpec (RegSpec.seq (RegSpec.pure hW ops)
    (RegSpec.wordBits hW dst src hd2 hd9 hd20 hd21)) ?_ ?_ ?_ ?_
  · intro r hb hg
    obtain ⟨h1, h2⟩ := hpre r hb hg
    exact ⟨h1, by rw [hfr r 2 (by omega)]; exact hb.2.1,
      by rw [hfr r 9 (by omega)]; exact hb.2.2.1, h2⟩
  · intro r hb hg
    have := wordBits_cost_le5 hW (hpre r hb hg).2
    show ops.length + (5 * Nat.log2 (pureRegs ops r src) + 5) ≤ _
    omega
  · intro r hb hg
    show put (put (put (pureRegs ops r) 20 _) 21 0) dst _ (38 + i) = _
    rw [← hdst, put_same]
    exact hval r hb hg
  · intro r x hx1 hx2
    show put (put (put (pureRegs ops r) 20 _) 21 0) dst _ x = _
    rw [put_ne _ _ (by rw [hdst]; exact hx1), put_ne _ _ (by omega), put_ne _ _ (by omega),
      hfr r x hx2]

theorem geoStep_wordBits_pure {W n i : Nat} (hW : 32 ≤ W) (tmp src : Operand) (ops : List Action)
    (hlen : ops.length ≤ 15) (htmp : 20 ≤ (tmp : Nat) ∧ (tmp : Nat) ≤ 28)
    (htmp' : (tmp : Nat) ≠ 20 ∧ (tmp : Nat) ≠ 21)
    (hops : (ops.filterMap pureDst).all (fun d => d == 38 + i || (20 ≤ d && d ≤ 28)) = true)
    (hsrc : ∀ r, GeoBase n r → GeoUpTo n i r → r src < 2 ^ W)
    (hpre : ∀ r, GeoBase n r → GeoUpTo n i r → pureOKs W ops (wordBitsF r tmp src))
    (hval : ∀ r, GeoBase n r → GeoUpTo n i r →
      pureRegs ops (wordBitsF r tmp src) (38 + i) = geoVal n i) :
    GeoStepOK W n i (.seq (wordBitsBlock tmp src) (acts ops)) := by
  refine GeoStepOK.of_regSpec (RegSpec.seq
    (RegSpec.wordBits hW tmp src (by omega) (by omega) htmp'.1 htmp'.2)
    (RegSpec.pure hW ops)) ?_ ?_ ?_ ?_
  · intro r hb hg
    exact ⟨⟨hb.2.1, hb.2.2.1, hsrc r hb hg⟩, hpre r hb hg⟩
  · intro r hb hg
    have := wordBits_cost_le5 hW (hsrc r hb hg)
    show 5 * Nat.log2 (r src) + 5 + ops.length ≤ _
    omega
  · intro r hb hg
    exact hval r hb hg
  · intro r x hx1 hx2
    show pureRegs ops (wordBitsF r tmp src) x = r x
    rw [pureRegs_frame _ _ x (fun a ha hax => by
      have := scratch_of_all hops ha hax
      simp at this
      omega)]
    exact wordBitsF_frame r tmp src x (by omega) (by omega) (by omega)

theorem geoStep_log2_pure {W n i : Nat} (hW : 32 ≤ W) (tmp src : Operand) (ops : List Action)
    (hlen : ops.length ≤ 15) (htmp : 20 ≤ (tmp : Nat) ∧ (tmp : Nat) ≤ 28)
    (htmp' : (tmp : Nat) ≠ 20 ∧ (tmp : Nat) ≠ 21)
    (hops : (ops.filterMap pureDst).all (fun d => d == 38 + i || (20 ≤ d && d ≤ 28)) = true)
    (hsrc : ∀ r, GeoBase n r → GeoUpTo n i r → r src < 2 ^ W)
    (hpre : ∀ r, GeoBase n r → GeoUpTo n i r → pureOKs W ops (log2F r tmp src))
    (hval : ∀ r, GeoBase n r → GeoUpTo n i r →
      pureRegs ops (log2F r tmp src) (38 + i) = geoVal n i) :
    GeoStepOK W n i (.seq (log2Block tmp src) (acts ops)) := by
  refine GeoStepOK.of_regSpec (RegSpec.seq
    (RegSpec.log2 hW tmp src (by omega) (by omega) htmp'.1 htmp'.2)
    (RegSpec.pure hW ops)) ?_ ?_ ?_ ?_
  · intro r hb hg
    exact ⟨⟨hb.2.1, hb.2.2.1, hsrc r hb hg⟩, hpre r hb hg⟩
  · intro r hb hg
    have := wordBits_cost_le5 hW (hsrc r hb hg)
    show 5 * Nat.log2 (r src) + 4 + ops.length ≤ _
    omega
  · intro r hb hg
    exact hval r hb hg
  · intro r x hx1 hx2
    show pureRegs ops (log2F r tmp src) x = r x
    rw [pureRegs_frame _ _ x (fun a ha hax => by
      have := scratch_of_all hops ha hax
      simp at this
      omega)]
    show put (put (put r 20 _) 21 0) tmp _ x = r x
    rw [put_ne _ _ (by omega), put_ne _ _ (by omega), put_ne _ _ (by omega)]

/-! ## Bounds of the bank values by powers of `B = 2 n + 4` -/

theorem bnd_ws (n : Nat) : packedRankWordSize n ≤ (2 * n + 4) ^ 1 ∧ 1 ≤ packedRankWordSize n := by
  have := log2_succ_le_succ (2 * n)
  simp only [packedRankWordSize, SuccinctRank.machineWordBits, Nat.pow_one]
  omega

theorem bnd_S (n : Nat) :
    GenericSelect.superStride (2 * n) ≤ (2 * n + 4) ^ 2 ∧ 1 ≤ GenericSelect.superStride (2 * n) := by
  obtain ⟨h1, h2⟩ := bnd_ws n
  exact ⟨mulB h1 h1 rfl, Nat.mul_le_mul h2 h2⟩

theorem bnd_e (n : Nat) :
    GenericSelect.ell (2 * n) ≤ (2 * n + 4) ^ 1 ∧ 1 ≤ GenericSelect.ell (2 * n) := by
  have h := log2_succ_le_succ (packedRankWordSize n)
  obtain ⟨h1, _⟩ := bnd_ws n
  simp only [Nat.pow_one] at h1
  show Nat.log2 (packedRankWordSize n) + 1 ≤ (2 * n + 4) ^ 1 ∧ 1 ≤ Nat.log2 (packedRankWordSize n) + 1
  have : 2 * n + 1 ≤ 2 * n + 1 := Nat.le_refl _
  simp only [packedRankWordSize, SuccinctRank.machineWordBits] at h h1 ⊢
  have := log2_succ_le_succ (2 * n)
  simp only [Nat.pow_one]
  omega

theorem bnd_ls (n : Nat) :
    GenericSelect.localStride (2 * n) ≤ (2 * n + 4) ^ 1 ∧ 1 ≤ GenericSelect.localStride (2 * n) := by
  obtain ⟨h1, _⟩ := bnd_ws n
  have hd : packedRankWordSize n / (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n)) ≤
      packedRankWordSize n := Nat.div_le_self _ _
  show max 1 (packedRankWordSize n / (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n))) ≤
      (2 * n + 4) ^ 1 ∧
    1 ≤ max 1 (packedRankWordSize n / (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n)))
  simp only [Nat.pow_one] at h1 ⊢
  omega

theorem bnd_lps (n : Nat) : GenericSelect.localSlotsPerSuper (2 * n) ≤ 2 * (2 * n + 4) ^ 2 := by
  obtain ⟨hS, _⟩ := bnd_S n
  obtain ⟨hl, _⟩ := bnd_ls n
  have hB := powB_facts n
  show (GenericSelect.superStride (2 * n) + GenericSelect.localStride (2 * n) - 1) /
      GenericSelect.localStride (2 * n) ≤ _
  have := Nat.div_le_self (GenericSelect.superStride (2 * n) + GenericSelect.localStride (2 * n) - 1)
    (GenericSelect.localStride (2 * n))
  omega

theorem bnd_LS (n : Nat) : GenericSelect.superLongSpan (2 * n) ≤ (2 * n + 4) ^ 4 := by
  obtain ⟨hS, _⟩ := bnd_S n
  obtain ⟨hw, _⟩ := bnd_ws n
  obtain ⟨he, _⟩ := bnd_e n
  exact mulB (mulB hS hw rfl) he rfl

theorem bnd_sup (n : Nat) : packedSuperSlots n ≤ 2 * (2 * n + 4) ^ 2 := by
  obtain ⟨hS, _⟩ := bnd_S n
  have hB := powB_facts n
  show (n + GenericSelect.superStride (2 * n) - 1) / GenericSelect.superStride (2 * n) ≤ _
  have := Nat.div_le_self (n + GenericSelect.superStride (2 * n) - 1) (GenericSelect.superStride (2 * n))
  omega

theorem bnd_loc (n : Nat) : packedLocalSlots n ≤ 4 * (2 * n + 4) ^ 4 := by
  have h1 := bnd_sup n
  have h2 := bnd_lps n
  have h3 : packedSuperSlots n * GenericSelect.localSlotsPerSuper (2 * n) ≤
      (2 * (2 * n + 4) ^ 2) * (2 * (2 * n + 4) ^ 2) := Nat.mul_le_mul h1 h2
  have h4 : (2 * (2 * n + 4) ^ 2) * (2 * (2 * n + 4) ^ 2) = 4 * (2 * n + 4) ^ 4 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, show (2 * n + 4) ^ 4 = (2 * n + 4) ^ 2 * (2 * n + 4) ^ 2 by
      rw [← Nat.pow_add]]
    simp only [Nat.mul_assoc, Nat.mul_left_comm]
  exact h4 ▸ h3

theorem bnd_sp (n : Nat) : packedSparseSlots n ≤ (2 * n + 4) ^ 1 := by
  show Nat.min (packedLocalSlots n) n ≤ _
  simp only [Nat.pow_one, Nat.min_def]
  split <;> omega

theorem log2_mul_self_le (x : Nat) : Nat.log2 (x * x) ≤ 2 * Nat.log2 x + 1 := by
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · have hx : x < 2 ^ (Nat.log2 x + 1) := Nat.lt_log2_self
    have hxx : x * x < 2 ^ (2 * Nat.log2 x + 2) := by
      have := Nat.mul_lt_mul'' hx hx
      rw [← Nat.pow_add] at this
      have e : Nat.log2 x + 1 + (Nat.log2 x + 1) = 2 * Nat.log2 x + 2 := by omega
      rw [e] at this
      exact this
    have hne : x * x ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have := (Nat.log2_lt hne).mpr hxx
    omega

theorem log2_succ_le_of_pos {x : Nat} (hx : 1 ≤ x) : Nat.log2 x + 1 ≤ x :=
  log2_succ_le_self hx

theorem bnd_base (n : Nat) : geoBase n ≤ (2 * n + 4) ^ 1 ∧ 1 ≤ geoBase n := by
  have := Nat.log2_le_self n
  simp only [geoBase, Nat.pow_one]
  omega

theorem bnd_macro (n : Nat) : geoMacro n ≤ (2 * n + 4) ^ 2 ∧ 1 ≤ geoMacro n := by
  obtain ⟨h1, h2⟩ := bnd_base n
  exact ⟨mulB h1 h1 rfl, Nat.mul_le_mul h2 h2⟩

theorem bnd_blocks (n : Nat) : geoBlocks n ≤ n := Nat.div_le_self _ _

theorem bnd_macros (n : Nat) : geoMacros n ≤ n + 1 ∧ 1 ≤ geoMacros n := by
  have := Nat.div_le_self (geoBlocks n) (geoMacro n)
  have := bnd_blocks n
  simp only [geoMacros]
  generalize geoBlocks n / geoMacro n = q at *
  omega

theorem bnd_ow (n : Nat) : SuccinctRank.machineWordBits (geoMacro n) ≤ 2 * n + 2 := by
  have h1 := log2_mul_self_le (geoBase n)
  obtain ⟨_, hb1⟩ := bnd_base n
  have h2 := log2_succ_le_of_pos hb1
  have h3 := Nat.log2_le_self n
  simp only [SuccinctRank.machineWordBits, geoMacro]
  simp only [geoBase] at h1 h2 ⊢
  omega

theorem bnd_wb_le (x : Nat) : SuccinctRank.machineWordBits x ≤ x + 1 := by
  simp only [SuccinctRank.machineWordBits]
  exact log2_succ_le_succ x

theorem wb_pos (x : Nat) : 1 ≤ SuccinctRank.machineWordBits x := by
  simp [SuccinctRank.machineWordBits]

theorem bnd_levelWidth {d : Nat} (hd : 1 ≤ d) : bpSparseLevelWidth d ≤ 2 * d := by
  have h1 : d * (Nat.log2 d + 1) ≤ d * d := Nat.mul_le_mul_left _ (log2_succ_le_of_pos hd)
  have h2 := log2_mono h1
  have h3 := log2_mul_self_le d
  have h4 := log2_succ_le_of_pos hd
  simp only [bpSparseLevelWidth]
  omega

theorem bnd_c (n : Nat) :
    1 ≤ bpFringeChunkBits (2 * n) ∧ 2 * bpFringeChunkBits (2 * n) + 2 ≤ 2 * n + 4 ∧
      bpFringeChunkBits (2 * n) ≤ Nat.log2 (2 * n) / 8 + 1 := by
  have := Nat.log2_le_self (2 * n)
  simp only [bpFringeChunkBits]
  omega

theorem bnd_pow_c (n : Nat) : 2 ^ bpFringeChunkBits (2 * n) ≤ 2 * (2 * n + 4) := by
  have h1 : 2 ^ bpFringeChunkBits (2 * n) ≤ 2 ^ (Nat.log2 (2 * n) + 1) := by
    apply Nat.pow_le_pow_right (by decide)
    simp only [bpFringeChunkBits]
    omega
  have h2 : 2 ^ Nat.log2 (2 * n) ≤ 2 * n + 1 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have := Nat.log2_self_le (n := 2 * n) (by omega)
      omega
  rw [Nat.pow_succ] at h1
  omega

theorem c_lt_width {W n : Nat} (hW : 32 ≤ W) (hm : 2 * n < 2 ^ W) : bpFringeChunkBits (2 * n) < W := by
  have := log2_lt_width (by omega) hm
  simp only [bpFringeChunkBits]
  omega

theorem shiftLeft_one (c : Nat) : Nat.shiftLeft 1 c = 2 ^ c := by
  have := Nat.shiftLeft_eq 1 c
  simpa using this

theorem mulC {B a b c1 c2 i j k : Nat} (ha : a ≤ c1 * B ^ i) (hb : b ≤ c2 * B ^ j)
    (hk : i + j = k) : a * b ≤ (c1 * c2) * B ^ k := by
  have := Nat.mul_le_mul ha hb
  rw [← hk, Nat.pow_add]
  calc a * b ≤ c1 * B ^ i * (c2 * B ^ j) := this
    _ = c1 * c2 * (B ^ i * B ^ j) := by
      rw [Nat.mul_assoc, Nat.mul_left_comm (B ^ i), ← Nat.mul_assoc]

theorem eight_w_lt {W : Nat} (hW : 32 ≤ W) : 8 * W + 32 < 2 ^ W := by
  have h := Nat.lt_two_pow_self (n := W - 6)
  have e : 2 ^ W = 2 ^ (W - 6) * 2 ^ 6 := by rw [← Nat.pow_add]; congr 1; omega
  rw [e]
  omega

/-- The access overhead budget in closed form. -/
theorem ao_eq (n : Nat) :
    SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n =
      1180 * (2 * n / packedRankWordSize n *
        (GenericSelect.ell (2 * n) * (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n)))) +
      513 * (2 * n / GenericSelect.ell (2 * n)) + 561 := by
  simp only [SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead,
    SuccinctFinal.relativeSplitSparseExceptionBPCloseRankOverhead,
    GenericSelect.canonicalSparseExceptionSelectOverhead,
    GenericSelect.longSuperRelativeTableOverhead,
    GenericSelect.canonicalSparseExceptionDirectoryOverhead,
    GenericSelect.sparseExceptionRelativeTableOverhead,
    SuccinctSpace.logLogCubedSampledDirectoryOverhead, SuccinctSpace.idDivLogLogOverhead,
    packedRankWordSize, GenericSelect.ell, GenericSelect.wordBits, SuccinctRank.machineWordBits]
  omega

theorem bnd_q (n : Nat) :
    2 * n / packedRankWordSize n *
      (GenericSelect.ell (2 * n) * (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n))) ≤
      (2 * n + 4) ^ 4 := by
  obtain ⟨he, _⟩ := bnd_e n
  have hd : 2 * n / packedRankWordSize n ≤ (2 * n + 4) ^ 1 := by
    have := Nat.div_le_self (2 * n) (packedRankWordSize n)
    simp only [Nat.pow_one]; omega
  exact mulB hd (mulB he (mulB he he rfl) rfl) rfl

theorem bnd_AO (n : Nat) :
    SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n ≤ 2254 * (2 * n + 4) ^ 4 := by
  rw [ao_eq]
  have hq := bnd_q n
  have hr : 2 * n / GenericSelect.ell (2 * n) ≤ 2 * n := Nat.div_le_self _ _
  have hB := powB_facts n
  generalize 2 * n / GenericSelect.ell (2 * n) = r at *
  omega

theorem bnd_I (n : Nat) :
    canonicalRelativeRmmInteriorRawPayloadOverhead n ≤ 32 * (2 * n + 4) ^ 5 := by
  have hB := powB_facts n
  obtain ⟨hws, _⟩ := bnd_ws n
  obtain ⟨hb, hb1⟩ := bnd_base n
  obtain ⟨hms, hms1⟩ := bnd_macro n
  obtain ⟨hmc, hmc1⟩ := bnd_macros n
  have hbl := bnd_blocks n
  have hdiv := Nat.div_le_self (geoBlocks n) (geoBase n)
  have how := bnd_ow n
  have hlb := Nat.log2_le_self (geoBase n)
  -- the six products
  have hssc : geoBlocks n / geoBase n + 1 ≤ 1 * (2 * n + 4) ^ 1 := by
    simp only [Nat.pow_one]; generalize geoBlocks n / geoBase n = q at *; omega
  have p1 : (geoBlocks n / geoBase n + 1) * packedRankWordSize n ≤ (1 * 1) * (2 * n + 4) ^ 2 :=
    mulC hssc (show packedRankWordSize n ≤ 1 * (2 * n + 4) ^ 1 by simpa using hws) rfl
  have hrw : 2 * (Nat.log2 (geoBase n) + 1) + 3 ≤ 2 * (2 * n + 4) ^ 1 := by
    have hbn : geoBase n ≤ n + 1 := by
      simp only [geoBase]; have := Nat.log2_le_self n; omega
    simp only [Nat.pow_one]; omega
  have hbl' : geoBlocks n ≤ 1 * (2 * n + 4) ^ 1 := by simp only [Nat.pow_one]; omega
  have p2 : geoBlocks n * (2 * (Nat.log2 (geoBase n) + 1) + 3) ≤ (1 * 2) * (2 * n + 4) ^ 2 :=
    mulC hbl' hrw rfl
  have how' : SuccinctRank.machineWordBits (geoMacro n) ≤ 1 * (2 * n + 4) ^ 1 := by
    simp only [Nat.pow_one]; omega
  have hmc' : geoMacros n ≤ 1 * (2 * n + 4) ^ 1 := by simp only [Nat.pow_one]; omega
  have hms' : geoMacro n ≤ 1 * (2 * n + 4) ^ 2 := by simpa using hms
  have p3 : geoMacros n * (SuccinctRank.machineWordBits (geoMacro n) * geoMacro n) *
      SuccinctRank.machineWordBits (geoMacro n) ≤ (1 * (1 * 1) * 1) * (2 * n + 4) ^ 5 :=
    mulC (mulC hmc' (mulC how' hms' rfl) rfl) how' rfl
  have hglc : SuccinctRank.machineWordBits (geoMacros n) ≤ 1 * (2 * n + 4) ^ 1 := by
    have := bnd_wb_le (geoMacros n); simp only [Nat.pow_one]; omega
  have hbaw : SuccinctRank.machineWordBits (geoBlocks n) ≤ 1 * (2 * n + 4) ^ 1 := by
    have := bnd_wb_le (geoBlocks n); simp only [Nat.pow_one]; omega
  have p4 : SuccinctRank.machineWordBits (geoMacros n) * geoMacros n *
      SuccinctRank.machineWordBits (geoBlocks n) ≤ (1 * 1 * 1) * (2 * n + 4) ^ 3 :=
    mulC (mulC hglc hmc' rfl) hbaw rfl
  have hld : bpSparseLevelDomain (geoMacro n) ≤ 2 * (2 * n + 4) ^ 2 := by
    simp only [bpSparseLevelDomain]; omega
  have hlw : bpSparseLevelWidth (bpSparseLevelDomain (geoMacro n)) ≤ 4 * (2 * n + 4) ^ 2 := by
    have := bnd_levelWidth (d := bpSparseLevelDomain (geoMacro n))
      (by simp only [bpSparseLevelDomain]; omega)
    omega
  have p5 : bpSparseLevelDomain (geoMacro n) * bpSparseLevelWidth (bpSparseLevelDomain (geoMacro n)) ≤
      (2 * 4) * (2 * n + 4) ^ 4 := mulC hld hlw rfl
  have hgd : bpSparseLevelDomain (geoMacros n) ≤ 2 * (2 * n + 4) ^ 1 := by
    simp only [bpSparseLevelDomain, Nat.pow_one]; omega
  have hgw : bpSparseLevelWidth (bpSparseLevelDomain (geoMacros n)) ≤ 4 * (2 * n + 4) ^ 1 := by
    have := bnd_levelWidth (d := bpSparseLevelDomain (geoMacros n))
      (by simp only [bpSparseLevelDomain]; omega)
    omega
  have p6 : bpSparseLevelDomain (geoMacros n) * bpSparseLevelWidth (bpSparseLevelDomain (geoMacros n)) ≤
      (2 * 4) * (2 * n + 4) ^ 2 := mulC hgd hgw rfl
  show (geoBlocks n / geoBase n + 1) * packedRankWordSize n +
      3 * (geoBlocks n * (2 * (Nat.log2 (geoBase n) + 1) + 3)) +
      geoMacros n * (SuccinctRank.machineWordBits (geoMacro n) * geoMacro n) *
        SuccinctRank.machineWordBits (geoMacro n) +
      SuccinctRank.machineWordBits (geoMacros n) * geoMacros n *
        SuccinctRank.machineWordBits (geoBlocks n) +
      bpSparseLevelDomain (geoMacro n) * bpSparseLevelWidth (bpSparseLevelDomain (geoMacro n)) +
      bpSparseLevelDomain (geoMacros n) * bpSparseLevelWidth (bpSparseLevelDomain (geoMacros n)) ≤ _
  omega

theorem bnd_F (n : Nat) : bpFringeTableOverhead n ≤ 4 * (2 * n + 4) ^ 6 := by
  obtain ⟨hc1, hc2, _⟩ := bnd_c n
  have hp := bnd_pow_c n
  have hc1' : bpFringeChunkBits (2 * n) + 1 ≤ 1 * (2 * n + 4) ^ 1 := by
    simp only [Nat.pow_one]; omega
  have hrows : bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) ≤ (2 * (1 * 1)) * (2 * n + 4) ^ 3 :=
    mulC (show 2 ^ bpFringeChunkBits (2 * n) ≤ 2 * (2 * n + 4) ^ 1 by simpa using hp)
      (mulC hc1' hc1' rfl) rfl
  have hbound : bpFringeChunkEntryBound (bpFringeChunkBits (2 * n)) ≤ (1 * (1 * 1)) * (2 * n + 4) ^ 3 :=
    mulC (show 2 * bpFringeChunkBits (2 * n) + 1 ≤ 1 * (2 * n + 4) ^ 1 by
        simp only [Nat.pow_one]; omega)
      (mulC (show 2 * bpFringeChunkBits (2 * n) + 2 ≤ 1 * (2 * n + 4) ^ 1 by
        simp only [Nat.pow_one]; omega) hc1' rfl) rfl
  have hwid : bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) ≤ 2 * (2 * n + 4) ^ 3 := by
    have := log2_succ_le_succ (bpFringeChunkEntryBound (bpFringeChunkBits (2 * n)))
    have hB := powB_facts n
    simp only [bpFringeChunkEntryWidth]
    omega
  exact mulC hrows hwid rfl

theorem bnd_C (n : Nat) : bpChunkSelectTableOverhead n ≤ 2 * (2 * n + 4) ^ 3 := by
  obtain ⟨hc1, hc2, _⟩ := bnd_c n
  have hp := bnd_pow_c n
  have hc1' : bpFringeChunkBits (2 * n) + 1 ≤ 1 * (2 * n + 4) ^ 1 := by
    simp only [Nat.pow_one]; omega
  have hrows : bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) ≤ (2 * 1) * (2 * n + 4) ^ 2 :=
    mulC (show 2 ^ bpFringeChunkBits (2 * n) ≤ 2 * (2 * n + 4) ^ 1 by simpa using hp) hc1' rfl
  have hwid : bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n)) ≤ 1 * (2 * n + 4) ^ 1 := by
    have := log2_succ_le_succ (bpFringeChunkBits (2 * n) + 1)
    simp only [bpChunkSelectEntryWidth, Nat.pow_one]
    omega
  exact mulC hrows hwid rfl

/-- Evaluate straight-line register actions at literal registers. -/
syntax "pre1_geo_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pre1_geo_simp [$hs,*]) => do
    let hs' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar,
      `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," := ⟨hs.elemsAndSeps⟩
    `(tactic| simp only [pureOKs, pureOK, pureRegs, pureReg, wordBitsF, log2F, put,
      Arithmetic.eval, Comparison.eval, reduceCtorEq, false_implies, false_or, or_false,
      and_true, true_and, implies_true, ite_true, ite_false, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd,
      operand_val_0, operand_val_1, operand_val_2, operand_val_3, operand_val_4, operand_val_5, operand_val_6, operand_val_7, operand_val_8, operand_val_9, operand_val_10, operand_val_11, operand_val_12, operand_val_13, operand_val_14, operand_val_15, operand_val_16, operand_val_17, operand_val_18, operand_val_19, operand_val_20, operand_val_21, operand_val_22, operand_val_23, operand_val_24, operand_val_25, operand_val_26, operand_val_27, operand_val_28, operand_val_29, operand_val_30, operand_val_31, operand_val_32, operand_val_33, operand_val_34, operand_val_35, operand_val_36, operand_val_37, operand_val_38, operand_val_39, operand_val_40, operand_val_41, operand_val_42, operand_val_43, operand_val_44, operand_val_45, operand_val_46, operand_val_47, operand_val_48, operand_val_49, operand_val_50, operand_val_51, operand_val_52, operand_val_53, operand_val_54, operand_val_55, operand_val_56, operand_val_57, operand_val_58, operand_val_59, operand_val_60, operand_val_61, operand_val_62, operand_val_63, operand_val_64, operand_val_65, operand_val_66, operand_val_67, operand_val_68, operand_val_69, operand_val_70, operand_val_71, operand_val_72, operand_val_73, operand_val_74, operand_val_75, operand_val_76, operand_val_513, operand_val_561, operand_val_1180, $hs',*])

/-! ## Bank steps 0-9 (select geometry) -/

section Steps

variable {W n : Nat} (hW : 32 ≤ W) (hcap : 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W)
include hW hcap

omit hW in
theorem capB : 65536 * (2 * n + 4) ^ 6 < 2 ^ W := cap_of_le hcap (Nat.le_refl _)

theorem geoStep0 : GeoStepOK W n 0 (geoStepBlock 0) := by
  have hc := capB hcap
  have hB := powB_facts n
  refine GeoStepOK.of_regSpec (RegSpec.pure hW _) ?_ (fun _ _ _ => by simp) ?_ ?_
  · intro r ⟨hn, h1, h9, _⟩ _
    simp only [pureOKs, pureOK, Arithmetic.eval, operand_val_9, operand_val_1, hn, h9,
      reduceCtorEq, false_implies, false_or, and_true]
    omega
  · intro r ⟨hn, h1, h9, _⟩ _
    simp [pureRegs, pureReg, Arithmetic.eval, hn, h9, geoVal]
  · intro r x hx _
    exact pureRegs_frame _ _ _ (by simp [pureDst]; omega)

theorem geoStep1 : GeoStepOK W n 1 (geoStepBlock 1) := by
  have hc := capB hcap
  have hB := powB_facts n
  refine geoStep_wordBits hW rWS rM2 rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    simp only [operand_val_38, g0]
    omega
  · intro r _ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    simp only [operand_val_38, g0]
    rfl

theorem geoStep2 : GeoStepOK W n 2 (geoStepBlock 2) := by
  have hc := capB hcap
  have hB := powB_facts n
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have hS : packedRankWordSize n * packedRankWordSize n ≤ (2 * n + 4) ^ 2 := (bnd_S n).1
    pre1_geo_simp [g1]
    omega
  · intro r _ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    pre1_geo_simp [g1]
    rfl

theorem geoStep3 : GeoStepOK W n 3 (geoStepBlock 3) := by
  have hc := capB hcap
  have hB := powB_facts n
  refine geoStep_wordBits hW rEL rWS rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have := (bnd_ws n).1
    simp only [operand_val_39, g1]
    omega
  · intro r _ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    simp only [operand_val_39, g1]
    rfl

theorem geoStep4 : GeoStepOK W n 4 (geoStepBlock 4) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hw, hw1⟩ := bnd_ws n
  obtain ⟨he, he1⟩ := bnd_e n
  have hee : GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n) ≤ (2 * n + 4) ^ 2 :=
    mulB he he rfl
  have hee1 : 1 ≤ GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n) := Nat.mul_le_mul he1 he1
  have hdiv := Nat.div_le_self (packedRankWordSize n)
    (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n))
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g1, g3, h1]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨_, h1, _⟩ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g1, g3, h1]
    show _ = max 1 (packedRankWordSize n / (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n)))
    generalize packedRankWordSize n / (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n)) = q
    split <;> omega

theorem geoStep5 : GeoStepOK W n 5 (geoStepBlock 5) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hS, hS1⟩ := bnd_S n
  obtain ⟨hl, hl1⟩ := bnd_ls n
  have hdiv := Nat.div_le_self (GenericSelect.superStride (2 * n) +
    GenericSelect.localStride (2 * n) - 1) (GenericSelect.localStride (2 * n))
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    have g4 : r 42 = GenericSelect.localStride (2 * n) := hg 4 (by decide)
    pre1_geo_simp [g2, g4, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    have g4 : r 42 = GenericSelect.localStride (2 * n) := hg 4 (by decide)
    pre1_geo_simp [g2, g4, h1]
    rfl

theorem geoStep6 : GeoStepOK W n 6 (geoStepBlock 6) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hS, _⟩ := bnd_S n
  obtain ⟨hw, _⟩ := bnd_ws n
  obtain ⟨he, _⟩ := bnd_e n
  have h3 : GenericSelect.superStride (2 * n) * packedRankWordSize n ≤ (2 * n + 4) ^ 3 :=
    mulB hS hw rfl
  have h4 : GenericSelect.superStride (2 * n) * packedRankWordSize n * GenericSelect.ell (2 * n) ≤
      (2 * n + 4) ^ 4 := mulB h3 he rfl
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g1, g2, g3]
    repeat' apply And.intro
    all_goals omega
  · intro r _ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g1, g2, g3]
    rfl

theorem geoStep7 : GeoStepOK W n 7 (geoStepBlock 7) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hS, hS1⟩ := bnd_S n
  have hdiv := Nat.div_le_self (n + GenericSelect.superStride (2 * n) - 1)
    (GenericSelect.superStride (2 * n))
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hn, h1, _⟩ hg
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    pre1_geo_simp [g2, hn, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨hn, h1, _⟩ hg
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    pre1_geo_simp [g2, hn, h1]
    rfl

theorem geoStep8 : GeoStepOK W n 8 (geoStepBlock 8) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hloc : packedSuperSlots n * GenericSelect.localSlotsPerSuper (2 * n) ≤
      4 * (2 * n + 4) ^ 4 := bnd_loc n
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g5 : r 43 = GenericSelect.localSlotsPerSuper (2 * n) := hg 5 (by decide)
    have g7 : r 45 = packedSuperSlots n := hg 7 (by decide)
    pre1_geo_simp [g5, g7]
    omega
  · intro r _ hg
    have g5 : r 43 = GenericSelect.localSlotsPerSuper (2 * n) := hg 5 (by decide)
    have g7 : r 45 = packedSuperSlots n := hg 7 (by decide)
    pre1_geo_simp [g5, g7]
    rfl

theorem geoStep9 : GeoStepOK W n 9 (geoStepBlock 9) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hloc := bnd_loc n
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hn, h1, _⟩ hg
    have g8 : r 46 = packedLocalSlots n := hg 8 (by decide)
    pre1_geo_simp [g8, hn, h1, minActs]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hn, h1, _⟩ hg
    have g8 : r 46 = packedLocalSlots n := hg 8 (by decide)
    pre1_geo_simp [g8, hn, h1, minActs]
    show _ = Nat.min (packedLocalSlots n) n
    simp only [Nat.min_def]
    split <;> split <;> omega

theorem geoStep10 : GeoStepOK W n 10 (geoStepBlock 10) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hS := (bnd_S n).1
  refine geoStep_wordBits hW rRBW rSS rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    simp only [operand_val_40, g2]
    omega
  · intro r _ hg
    have g2 : r 40 = GenericSelect.superStride (2 * n) := hg 2 (by decide)
    simp only [operand_val_40, g2]
    rfl

theorem geoStep11 : GeoStepOK W n 11 (geoStepBlock 11) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hLS := bnd_LS n
  refine geoStep_pure_wordBits hW _ rLW rT0 (by decide) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g6 : r 44 = GenericSelect.superLongSpan (2 * n) := hg 6 (by decide)
    pre1_geo_simp [g0, g6, h1, minActs]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g6 : r 44 = GenericSelect.superLongSpan (2 * n) := hg 6 (by decide)
    pre1_geo_simp [g0, g6, h1, minActs]
    show _ = Nat.log2 (Nat.min (2 * n) (GenericSelect.superLongSpan (2 * n))) + 1
    congr 2
    simp only [Nat.min_def]
    split <;> split <;> omega

theorem geoStep12 : GeoStepOK W n 12 (geoStepBlock 12) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hs := bnd_sup n
  refine geoStep_wordBits hW rLFW rSUP rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g7 : r 45 = packedSuperSlots n := hg 7 (by decide)
    simp only [operand_val_45, g7]
    omega
  · intro r _ hg
    have g7 : r 45 = packedSuperSlots n := hg 7 (by decide)
    simp only [operand_val_45, g7]
    rfl

theorem geoStep13 : GeoStepOK W n 13 (geoStepBlock 13) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hs := bnd_sp n
  refine geoStep_wordBits hW rSFW rSP rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g9 : r 47 = packedSparseSlots n := hg 9 (by decide)
    simp only [operand_val_47, g9]
    omega
  · intro r _ hg
    have g9 : r 47 = packedSparseSlots n := hg 9 (by decide)
    simp only [operand_val_47, g9]
    rfl

theorem geoStep14 : GeoStepOK W n 14 (geoStepBlock 14) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨_, hw1⟩ := bnd_ws n
  have hd1 := Nat.div_le_self (2 * n) (packedRankWordSize n)
  have hd2 := Nat.div_le_self (2 * n / packedRankWordSize n) (packedRankWordSize n)
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    pre1_geo_simp [g0, g1, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    pre1_geo_simp [g0, g1, h1]
    rfl

theorem geoStep15 : GeoStepOK W n 15 (geoStepBlock 15) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨_, hw1⟩ := bnd_ws n
  have hd1 := Nat.div_le_self (2 * n) (packedRankWordSize n)
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    pre1_geo_simp [g0, g1, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    pre1_geo_simp [g0, g1, h1]
    rfl

theorem geoStep16 : GeoStepOK W n 16 (geoStepBlock 16) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hs := bnd_sup n
  have hd := Nat.div_le_self (packedSuperSlots n) (packedLongFlagWordSize n)
  have hl1 : 1 ≤ packedLongFlagWordSize n := by
    simp [packedLongFlagWordSize, SuccinctRank.machineWordBits]
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g7 : r 45 = packedSuperSlots n := hg 7 (by decide)
    have g12 : r 50 = packedLongFlagWordSize n := hg 12 (by decide)
    pre1_geo_simp [g7, g12, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g7 : r 45 = packedSuperSlots n := hg 7 (by decide)
    have g12 : r 50 = packedLongFlagWordSize n := hg 12 (by decide)
    pre1_geo_simp [g7, g12, h1]
    rfl

theorem geoStep17 : GeoStepOK W n 17 (geoStepBlock 17) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hs := bnd_sp n
  have hd := Nat.div_le_self (packedSparseSlots n) (packedSparseWordSize n)
  have hl1 : 1 ≤ packedSparseWordSize n := by
    simp [packedSparseWordSize, SuccinctRank.machineWordBits]
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g9 : r 47 = packedSparseSlots n := hg 9 (by decide)
    have g13 : r 51 = packedSparseWordSize n := hg 13 (by decide)
    pre1_geo_simp [g9, g13, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g9 : r 47 = packedSparseSlots n := hg 9 (by decide)
    have g13 : r 51 = packedSparseWordSize n := hg 13 (by decide)
    pre1_geo_simp [g9, g13, h1]
    rfl

theorem geoStep18 : GeoStepOK W n 18 (geoStepBlock 18) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hb := (bnd_base n).1
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, h9, h30, _⟩ _
    pre1_geo_simp [h9, h30]
    omega
  · intro r ⟨_, _, h9, h30, _⟩ _
    pre1_geo_simp [h9, h30]
    rfl

theorem geoStep19 : GeoStepOK W n 19 (geoStepBlock 19) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨_, hb1⟩ := bnd_base n
  have hbl := bnd_blocks n
  have hd := Nat.div_le_self (geoBlocks n) (geoBase n)
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _, h30, _, h32, _⟩ _
    pre1_geo_simp [h1, h30, h32]
    generalize geoBlocks n / geoBase n = q at *
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _, h30, _, h32, _⟩ _
    pre1_geo_simp [h1, h30, h32]
    rfl

theorem geoStep20 : GeoStepOK W n 20 (geoStepBlock 20) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hm := (bnd_macro n).1
  refine geoStep_wordBits hW rOW rMACRO rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, _, _, h31, _⟩ _
    simp only [operand_val_31, h31]
    omega
  · intro r ⟨_, _, _, _, h31, _⟩ _
    simp only [operand_val_31, h31]
    rfl

theorem geoStep21 : GeoStepOK W n 21 (geoStepBlock 21) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hm := (bnd_macros n).1
  refine geoStep_wordBits hW rGLC rMACROS rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, _, _, _, _, h33, _⟩ _
    simp only [operand_val_33, h33]
    omega
  · intro r ⟨_, _, _, _, _, _, h33, _⟩ _
    simp only [operand_val_33, h33]
    rfl

theorem geoStep22 : GeoStepOK W n 22 (geoStepBlock 22) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hm := bnd_blocks n
  refine geoStep_wordBits hW rBAW rBLOCKS rfl (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, _, _, _, h32, _⟩ _
    simp only [operand_val_32, h32]
    omega
  · intro r ⟨_, _, _, _, _, h32, _⟩ _
    simp only [operand_val_32, h32]
    rfl

theorem geoStep23 : GeoStepOK W n 23 (geoStepBlock 23) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hb := (bnd_base n).1
  have hl := Nat.log2_le_self (geoBase n)
  refine geoStep_wordBits_pure hW rT1 rBASE _ (by decide) (by decide) (by decide) (by decide)
    ?_ ?_ ?_
  · intro r ⟨_, _, _, h30, _⟩ _
    simp only [operand_val_30, h30]
    omega
  · intro r ⟨_, _, h9, h30, _⟩ _
    pre1_geo_simp [h9, h30]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, _, h9, h30, _⟩ _
    pre1_geo_simp [h9, h30]
    rfl

theorem geoStep24 : GeoStepOK W n 24 (geoStepBlock 24) := by
  have hc := capB hcap
  have hB := powB_facts n
  have how : SuccinctRank.machineWordBits (geoMacro n) ≤ (2 * n + 4) ^ 1 := by
    have := bnd_ow n; simp only [Nat.pow_one]; omega
  have hms : geoMacros n ≤ (2 * n + 4) ^ 1 := by
    have := (bnd_macros n).1; simp only [Nat.pow_one]; omega
  have hp1 : SuccinctRank.machineWordBits (geoMacro n) * geoMacro n ≤ (2 * n + 4) ^ 3 :=
    mulB how (bnd_macro n).1 rfl
  have hp2 : geoMacros n * (SuccinctRank.machineWordBits (geoMacro n) * geoMacro n) ≤
      (2 * n + 4) ^ 4 := mulB hms hp1 rfl
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, _, _, h31, _, h33, _⟩ hg
    have g20 : r 58 = SuccinctRank.machineWordBits (geoMacro n) := hg 20 (by decide)
    pre1_geo_simp [h31, h33, g20]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, _, _, _, h31, _, h33, _⟩ hg
    have g20 : r 58 = SuccinctRank.machineWordBits (geoMacro n) := hg 20 (by decide)
    pre1_geo_simp [h31, h33, g20]
    rfl

theorem geoStep25 : GeoStepOK W n 25 (geoStepBlock 25) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hg1 : SuccinctRank.machineWordBits (geoMacros n) ≤ (2 * n + 4) ^ 1 := by
    have := bnd_wb_le (geoMacros n); have := (bnd_macros n).1; simp only [Nat.pow_one]; omega
  have hms : geoMacros n ≤ (2 * n + 4) ^ 1 := by
    have := (bnd_macros n).1; simp only [Nat.pow_one]; omega
  have hp : SuccinctRank.machineWordBits (geoMacros n) * geoMacros n ≤ (2 * n + 4) ^ 2 :=
    mulB hg1 hms rfl
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, _, _, _, _, h33, _⟩ hg
    have g21 : r 59 = SuccinctRank.machineWordBits (geoMacros n) := hg 21 (by decide)
    pre1_geo_simp [h33, g21]
    omega
  · intro r ⟨_, _, _, _, _, _, h33, _⟩ hg
    have g21 : r 59 = SuccinctRank.machineWordBits (geoMacros n) := hg 21 (by decide)
    pre1_geo_simp [h33, g21]
    rfl

theorem geoStep26 : GeoStepOK W n 26 (geoStepBlock 26) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hl := Nat.log2_le_self (2 * n)
  refine geoStep_log2_pure hW rT1 rM2 _ (by decide) (by decide) (by decide) (by decide) ?_ ?_ ?_
  · intro r _ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    simp only [operand_val_38, g0]
    omega
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    pre1_geo_simp [g0, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    pre1_geo_simp [g0, h1]
    rfl

theorem geoStep27 : GeoStepOK W n 27 (geoStepBlock 27) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hc1, hc2, _⟩ := bnd_c n
  have hp := bnd_pow_c n
  have hcw : bpFringeChunkBits (2 * n) < W := c_lt_width hW (by omega)
  have hc1' : bpFringeChunkBits (2 * n) + 1 ≤ 1 * (2 * n + 4) ^ 1 := by
    simp only [Nat.pow_one]; omega
  have hsq : (bpFringeChunkBits (2 * n) + 1) * (bpFringeChunkBits (2 * n) + 1) ≤
      (1 * 1) * (2 * n + 4) ^ 2 := mulC hc1' hc1' rfl
  have hrows : 2 ^ bpFringeChunkBits (2 * n) *
      ((bpFringeChunkBits (2 * n) + 1) * (bpFringeChunkBits (2 * n) + 1)) ≤
      (2 * (1 * 1)) * (2 * n + 4) ^ 3 :=
    mulC (show 2 ^ bpFringeChunkBits (2 * n) ≤ 2 * (2 * n + 4) ^ 1 by simpa using hp) hsq rfl
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1, shiftLeft_one]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1, shiftLeft_one]
    rfl

theorem geoStep28 : GeoStepOK W n 28 (geoStepBlock 28) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hc1, hc2, _⟩ := bnd_c n
  have hc1' : bpFringeChunkBits (2 * n) + 1 ≤ 1 * (2 * n + 4) ^ 1 := by
    simp only [Nat.pow_one]; omega
  have hp1 : (2 * bpFringeChunkBits (2 * n) + 2) * (bpFringeChunkBits (2 * n) + 1) ≤
      (1 * 1) * (2 * n + 4) ^ 2 :=
    mulC (show 2 * bpFringeChunkBits (2 * n) + 2 ≤ 1 * (2 * n + 4) ^ 1 by
      simp only [Nat.pow_one]; omega) hc1' rfl
  have hp2 : (2 * bpFringeChunkBits (2 * n) + 1) *
      ((2 * bpFringeChunkBits (2 * n) + 2) * (bpFringeChunkBits (2 * n) + 1)) ≤
      (1 * (1 * 1)) * (2 * n + 4) ^ 3 :=
    mulC (show 2 * bpFringeChunkBits (2 * n) + 1 ≤ 1 * (2 * n + 4) ^ 1 by
      simp only [Nat.pow_one]; omega) hp1 rfl
  refine geoStep_pure_wordBits hW _ rFWID rT1 (by decide) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, h9, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1, h9]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, h9, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1, h9]
    rfl

theorem geoStep29 : GeoStepOK W n 29 (geoStepBlock 29) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hc1, hc2, _⟩ := bnd_c n
  have hp := bnd_pow_c n
  have hcw : bpFringeChunkBits (2 * n) < W := c_lt_width hW (by omega)
  have hc1' : bpFringeChunkBits (2 * n) + 1 ≤ 1 * (2 * n + 4) ^ 1 := by
    simp only [Nat.pow_one]; omega
  have hrows : 2 ^ bpFringeChunkBits (2 * n) * (bpFringeChunkBits (2 * n) + 1) ≤
      (2 * 1) * (2 * n + 4) ^ 2 :=
    mulC (show 2 ^ bpFringeChunkBits (2 * n) ≤ 2 * (2 * n + 4) ^ 1 by simpa using hp) hc1' rfl
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1, shiftLeft_one]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1, shiftLeft_one]
    rfl

theorem geoStep30 : GeoStepOK W n 30 (geoStepBlock 30) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨hc1, hc2, _⟩ := bnd_c n
  refine geoStep_pure_wordBits hW _ rSWID rT1 (by decide) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ ?_
  · intro r ⟨_, h1, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, h1, _⟩ hg
    have g26 : r 64 = bpFringeChunkBits (2 * n) := hg 26 (by decide)
    pre1_geo_simp [g26, h1]
    rfl

theorem geoStep31 : GeoStepOK W n 31 (geoStepBlock 31) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hI := bnd_I n
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, _, _, _, h32, _, h34, h35, h36, h37⟩ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g19 : r 57 = geoBlocks n / geoBase n + 1 := hg 19 (by decide)
    have g20 : r 58 = SuccinctRank.machineWordBits (geoMacro n) := hg 20 (by decide)
    have g22 : r 60 = SuccinctRank.machineWordBits (geoBlocks n) := hg 22 (by decide)
    have g23 : r 61 = 2 * (Nat.log2 (geoBase n) + 1) + 3 := hg 23 (by decide)
    have g24 : r 62 = geoMacros n * (SuccinctRank.machineWordBits (geoMacro n) * geoMacro n) :=
      hg 24 (by decide)
    have g25 : r 63 = SuccinctRank.machineWordBits (geoMacros n) * geoMacros n := hg 25 (by decide)
    have hIeq : canonicalRelativeRmmInteriorRawPayloadOverhead n =
        (geoBlocks n / geoBase n + 1) * packedRankWordSize n +
          3 * (geoBlocks n * (2 * (Nat.log2 (geoBase n) + 1) + 3)) +
          geoMacros n * (SuccinctRank.machineWordBits (geoMacro n) * geoMacro n) *
            SuccinctRank.machineWordBits (geoMacro n) +
          SuccinctRank.machineWordBits (geoMacros n) * geoMacros n *
            SuccinctRank.machineWordBits (geoBlocks n) +
          bpSparseLevelDomain (geoMacro n) * bpSparseLevelWidth (bpSparseLevelDomain (geoMacro n)) +
          bpSparseLevelDomain (geoMacros n) *
            bpSparseLevelWidth (bpSparseLevelDomain (geoMacros n)) := rfl
    pre1_geo_simp [g1, g19, g20, g22, g23, g24, g25, h32, h34, h35, h36, h37]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, _, _, _, _, h32, _, h34, h35, h36, h37⟩ hg
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g19 : r 57 = geoBlocks n / geoBase n + 1 := hg 19 (by decide)
    have g20 : r 58 = SuccinctRank.machineWordBits (geoMacro n) := hg 20 (by decide)
    have g22 : r 60 = SuccinctRank.machineWordBits (geoBlocks n) := hg 22 (by decide)
    have g23 : r 61 = 2 * (Nat.log2 (geoBase n) + 1) + 3 := hg 23 (by decide)
    have g24 : r 62 = geoMacros n * (SuccinctRank.machineWordBits (geoMacro n) * geoMacro n) :=
      hg 24 (by decide)
    have g25 : r 63 = SuccinctRank.machineWordBits (geoMacros n) * geoMacros n := hg 25 (by decide)
    pre1_geo_simp [g1, g19, g20, g22, g23, g24, g25, h32, h34, h35, h36, h37]
    rfl

theorem geoStep32 : GeoStepOK W n 32 (geoStepBlock 32) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hF : bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) *
      bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) ≤ 4 * (2 * n + 4) ^ 6 := bnd_F n
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g27 : r 65 = bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) := hg 27 (by decide)
    have g28 : r 66 = bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) := hg 28 (by decide)
    pre1_geo_simp [g27, g28]
    omega
  · intro r _ hg
    have g27 : r 65 = bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) := hg 27 (by decide)
    have g28 : r 66 = bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) := hg 28 (by decide)
    pre1_geo_simp [g27, g28]
    rfl

theorem geoStep33 : GeoStepOK W n 33 (geoStepBlock 33) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hC : bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) *
      bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n)) ≤ 2 * (2 * n + 4) ^ 3 := bnd_C n
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g29 : r 67 = bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) := hg 29 (by decide)
    have g30 : r 68 = bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n)) := hg 30 (by decide)
    pre1_geo_simp [g29, g30]
    omega
  · intro r _ hg
    have g29 : r 67 = bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) := hg 29 (by decide)
    have g30 : r 68 = bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n)) := hg 30 (by decide)
    pre1_geo_simp [g29, g30]
    rfl

theorem geoStep34 : GeoStepOK W n 34 (geoStepBlock 34) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨_, hw1⟩ := bnd_ws n
  obtain ⟨he, he1⟩ := bnd_e n
  have hee : GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n) ≤ (2 * n + 4) ^ 2 :=
    mulB he he rfl
  have heee : GenericSelect.ell (2 * n) * (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n)) ≤
      (2 * n + 4) ^ 3 := mulB he hee rfl
  have hq := bnd_q n
  have hd := Nat.div_le_self (2 * n) (packedRankWordSize n)
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g0, g1, g3]
    repeat' apply And.intro
    all_goals omega
  · intro r _ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g1 : r 39 = packedRankWordSize n := hg 1 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g0, g1, g3]
    rfl

theorem geoStep35 : GeoStepOK W n 35 (geoStepBlock 35) := by
  have hc := capB hcap
  have hB := powB_facts n
  obtain ⟨_, he1⟩ := bnd_e n
  have hd := Nat.div_le_self (2 * n) (GenericSelect.ell (2 * n))
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g0, g3]
    repeat' apply And.intro
    all_goals omega
  · intro r _ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g3 : r 41 = GenericSelect.ell (2 * n) := hg 3 (by decide)
    pre1_geo_simp [g0, g3]
    rfl

theorem geoStep36 : GeoStepOK W n 36 (geoStepBlock 36) := by
  have hc := capB hcap
  have hB := powB_facts n
  have hq := bnd_q n
  have hr := Nat.div_le_self (2 * n) (GenericSelect.ell (2 * n))
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g34 : r 72 = 2 * n / packedRankWordSize n *
        (GenericSelect.ell (2 * n) * (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n))) :=
      hg 34 (by decide)
    have g35 : r 73 = 2 * n / GenericSelect.ell (2 * n) := hg 35 (by decide)
    pre1_geo_simp [g34, g35]
    generalize 2 * n / GenericSelect.ell (2 * n) = rr at *
    repeat' apply And.intro
    all_goals omega
  · intro r _ hg
    have g34 : r 72 = 2 * n / packedRankWordSize n *
        (GenericSelect.ell (2 * n) * (GenericSelect.ell (2 * n) * GenericSelect.ell (2 * n))) :=
      hg 34 (by decide)
    have g35 : r 73 = 2 * n / GenericSelect.ell (2 * n) := hg 35 (by decide)
    pre1_geo_simp [g34, g35]
    show _ = SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n
    rw [ao_eq]

omit hW in
theorem cellArg_lt : 2 * n + SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n +
    canonicalRelativeRmmInteriorRawPayloadOverhead n + bpFringeTableOverhead n +
    bpChunkSelectTableOverhead n + 2 < 2 ^ W := by
  have hc := capB hcap
  have hB := powB_facts n
  have := bnd_AO n
  have := bnd_I n
  have := bnd_F n
  have := bnd_C n
  omega

theorem geoStep37 : GeoStepOK W n 37 (geoStepBlock 37) := by
  have harg := cellArg_lt hcap
  refine geoStep_pure_wordBits hW _ rOLDW rT1 (by decide) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ ?_
  · intro r ⟨_, _, h9, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g31 : r 69 = canonicalRelativeRmmInteriorRawPayloadOverhead n := hg 31 (by decide)
    have g32 : r 70 = bpFringeTableOverhead n := hg 32 (by decide)
    have g33 : r 71 = bpChunkSelectTableOverhead n := hg 33 (by decide)
    have g36 : r 74 = SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n := hg 36 (by decide)
    pre1_geo_simp [g0, g31, g32, g33, g36, h9]
    repeat' apply And.intro
    all_goals omega
  · intro r ⟨_, _, h9, _⟩ hg
    have g0 : r 38 = 2 * n := hg 0 (by decide)
    have g31 : r 69 = canonicalRelativeRmmInteriorRawPayloadOverhead n := hg 31 (by decide)
    have g32 : r 70 = bpFringeTableOverhead n := hg 32 (by decide)
    have g33 : r 71 = bpChunkSelectTableOverhead n := hg 33 (by decide)
    have g36 : r 74 = SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n := hg 36 (by decide)
    pre1_geo_simp [g0, g31, g32, g33, g36, h9]
    show _ = Nat.log2 (2 * n + (SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n +
      canonicalRelativeRmmInteriorRawPayloadOverhead n + bpFringeTableOverhead n +
      bpChunkSelectTableOverhead n) + 2) + 1
    congr 2
    omega

theorem geoStep38 : GeoStepOK W n 38 (geoStepBlock 38) := by
  have harg := cellArg_lt hcap
  have hw8 := eight_w_lt hW
  have hold : packedReviewerCellWidth n ≤ W := by
    have := log2_lt_width (W := W) (by omega) harg
    show Nat.log2 (2 * n + (SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n +
      canonicalRelativeRmmInteriorRawPayloadOverhead n + bpFringeTableOverhead n +
      bpChunkSelectTableOverhead n) + 2) + 1 ≤ W
    have e : 2 * n + (SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n +
      canonicalRelativeRmmInteriorRawPayloadOverhead n + bpFringeTableOverhead n +
      bpChunkSelectTableOverhead n) + 2 = 2 * n + SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n +
      canonicalRelativeRmmInteriorRawPayloadOverhead n + bpFringeTableOverhead n +
      bpChunkSelectTableOverhead n + 2 := by omega
    rw [e]
    omega
  refine geoStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r _ hg
    have g37 : r 75 = packedReviewerCellWidth n := hg 37 (by decide)
    pre1_geo_simp [g37]
    repeat' apply And.intro
    all_goals omega
  · intro r _ hg
    have g37 : r 75 = packedReviewerCellWidth n := hg 37 (by decide)
    pre1_geo_simp [g37]
    show _ = 32 + 8 * packedReviewerCellWidth n
    rfl

/-- Every bank step meets its step contract. -/
theorem geoStep_all : ∀ i, i < 39 → GeoStepOK W n i (geoStepBlock i)
  | 0, _ => geoStep0 hW hcap
  | 1, _ => geoStep1 hW hcap
  | 2, _ => geoStep2 hW hcap
  | 3, _ => geoStep3 hW hcap
  | 4, _ => geoStep4 hW hcap
  | 5, _ => geoStep5 hW hcap
  | 6, _ => geoStep6 hW hcap
  | 7, _ => geoStep7 hW hcap
  | 8, _ => geoStep8 hW hcap
  | 9, _ => geoStep9 hW hcap
  | 10, _ => geoStep10 hW hcap
  | 11, _ => geoStep11 hW hcap
  | 12, _ => geoStep12 hW hcap
  | 13, _ => geoStep13 hW hcap
  | 14, _ => geoStep14 hW hcap
  | 15, _ => geoStep15 hW hcap
  | 16, _ => geoStep16 hW hcap
  | 17, _ => geoStep17 hW hcap
  | 18, _ => geoStep18 hW hcap
  | 19, _ => geoStep19 hW hcap
  | 20, _ => geoStep20 hW hcap
  | 21, _ => geoStep21 hW hcap
  | 22, _ => geoStep22 hW hcap
  | 23, _ => geoStep23 hW hcap
  | 24, _ => geoStep24 hW hcap
  | 25, _ => geoStep25 hW hcap
  | 26, _ => geoStep26 hW hcap
  | 27, _ => geoStep27 hW hcap
  | 28, _ => geoStep28 hW hcap
  | 29, _ => geoStep29 hW hcap
  | 30, _ => geoStep30 hW hcap
  | 31, _ => geoStep31 hW hcap
  | 32, _ => geoStep32 hW hcap
  | 33, _ => geoStep33 hW hcap
  | 34, _ => geoStep34 hW hcap
  | 35, _ => geoStep35 hW hcap
  | 36, _ => geoStep36 hW hcap
  | 37, _ => geoStep37 hW hcap
  | 38, _ => geoStep38 hW hcap
  | _ + 39, h => absurd h (by omega)

/-- **The bank chain.** The first `k ≤ 39` steps establish the first `k` bank
registers, keep the base registers, and change no register outside the scratch
band 20-28 and the bank band `[38, 38 + k)`. -/
theorem geoChain_spec : ∀ k, k ≤ 39 → ∀ s : State, s.status = .running → GeoBase n s.regs →
    ∃ s' j, SafeEval W (geoChain k) s s' j ∧ j ≤ k * (5 * W + 20) ∧ s'.status = .running ∧
      GeoBase n s'.regs ∧ GeoUpTo n k s'.regs ∧
      (∀ x : Nat, ¬ (20 ≤ x ∧ x ≤ 28) → ¬ (38 ≤ x ∧ x < 38 + k) → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs
  | 0, _, s, hrun, hb =>
      ⟨s, 0, EvalG.skip s hrun, by simp, hrun, hb, fun _ hi => absurd hi (by omega),
        fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | k + 1, hk, s, hrun, hb => by
      obtain ⟨s₁, j₁, e₁, hj₁, hr₁, hb₁, hg₁, hf₁, hm₁, he₁, hks₁, hkr₁⟩ :=
        geoChain_spec k (by omega) s hrun hb
      obtain ⟨s₂, j₂, e₂, hj₂, hr₂, hv₂, hf₂, hm₂, he₂, hks₂, hkr₂⟩ :=
        geoStep_all hW hcap k (by omega) s₁ hr₁ hb₁ hg₁
      refine ⟨s₂, j₁ + j₂, EvalG.seq e₁ e₂, ?_, hr₂, ?_, ?_, ?_, by rw [hm₂, hm₁],
        by rw [he₂, he₁], by rw [hks₂, hks₁], by rw [hkr₂, hkr₁]⟩
      · rw [Nat.succ_mul]; omega
      · obtain ⟨a1, a2, a9, a30, a31, a32, a33, a34, a35, a36, a37⟩ := hb₁
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hf₂ 1 (by omega) (by omega)]; exact a1
        · rw [hf₂ 2 (by omega) (by omega)]; exact a2
        · rw [hf₂ 9 (by omega) (by omega)]; exact a9
        · rw [hf₂ 30 (by omega) (by omega)]; exact a30
        · rw [hf₂ 31 (by omega) (by omega)]; exact a31
        · rw [hf₂ 32 (by omega) (by omega)]; exact a32
        · rw [hf₂ 33 (by omega) (by omega)]; exact a33
        · rw [hf₂ 34 (by omega) (by omega)]; exact a34
        · rw [hf₂ 35 (by omega) (by omega)]; exact a35
        · rw [hf₂ 36 (by omega) (by omega)]; exact a36
        · rw [hf₂ 37 (by omega) (by omega)]; exact a37
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · rw [hf₂ (38 + i) (by omega) (by omega)]; exact hg₁ i h
        · subst h; exact hv₂
      · intro x h1 h2
        rw [hf₂ x (by omega) h1, hf₁ x h1 (by omega)]

end Steps

theorem interior_cap_of_bank {W n : Nat} (hcap : 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W) :
    (n + 2) * (n + 2) * ((n + 2) * (n + 2)) < 2 ^ W := by
  have h1 : n + 2 ≤ 2 * n + 4 := by omega
  have h2 : (n + 2) * (n + 2) * ((n + 2) * (n + 2)) ≤ (2 * n + 4) ^ 4 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h1) (Nat.mul_le_mul h1 h1)
    have e : (2 * n + 4) ^ 4 = (2 * n + 4) * (2 * n + 4) * ((2 * n + 4) * (2 * n + 4)) := by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]
    rw [e]; exact this
  have hB := powB_facts n
  have hc := capB hcap
  omega

/-- **S2 geometry prelude.** From a running state with the input length in
register 1 and the constants in registers 2 and 9, `geometryPrelude` safely
stores the interior subset (registers 30-37) and all 39 bank registers (38-76)
at their reference values, changing no register outside the scratch band 20-28
and the geometry band 30-76, and leaving memory, extent, keys and key registers
unchanged, in at most `25 * W + 40 + 39 * (5 * W + 20)` transitions. -/
theorem geometryPrelude_spec {W n : Nat} (hW : 32 ≤ W) (hcap : 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hn : s.regs 1 = n) :
    ∃ s' k, SafeEval W geometryPrelude s s' k ∧ k ≤ 25 * W + 40 + 39 * (5 * W + 20) ∧
      s'.status = .running ∧ GeoBase n s'.regs ∧ GeoUpTo n 39 s'.regs ∧
      (∀ x : Nat, ¬ (20 ≤ x ∧ x ≤ 28) → ¬ (30 ≤ x ∧ x ≤ 76) → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧
      s'.keyRegs = s.keyRegs := by
  obtain ⟨g, k1, hg, hk1, hgrun, g30, g31, g32, g33, g34, g35, g36, g37, hgm, hge, hgfr, hgkr, hgk⟩ :=
    interiorGeometry_spec hW s n hrun hone htwo hn (interior_cap_of_bank hcap)
  have hbase : GeoBase n g.regs := by
    refine ⟨?_, ?_, ?_, g30, g31, g32, g33, g34, g35, g36, g37⟩
    · rw [hgfr 1 (by omega) (by omega)]; exact hn
    · rw [hgfr 2 (by omega) (by omega)]; exact hone
    · rw [hgfr 9 (by omega) (by omega)]; exact htwo
  obtain ⟨s', k2, hc, hk2, hr, hb, hgu, hfr, hm, he, hks, hkr⟩ :=
    geoChain_spec hW hcap 39 (Nat.le_refl _) g hgrun hbase
  refine ⟨s', k1 + k2, EvalG.seq hg hc, by omega, hr, hb, hgu, ?_, by rw [hm, hgm], by rw [he, hge],
    by rw [hks, hgk], by rw [hkr, hgkr]⟩
  intro x h1 h2
  rw [hfr x h1 (by omega), hgfr x (by omega) (by omega)]

end RMQ.SuccinctFinal.PackedConstruction.Proof
