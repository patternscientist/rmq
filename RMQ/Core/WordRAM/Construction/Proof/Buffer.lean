import RMQ.Core.WordRAM.Construction.Proof.Finish
import RMQ.Core.WordRAM.Construction.Proof.InteriorClose
import RMQ.Core.WordRAM.Construction.Proof.BPEmit

/-! # PRE-1 builder proofs: the bit buffer (stage S6 exit)

Outside the builder firewall. `bufferStage_spec` runs the stack arrays, the
Cartesian stack pass and `bufferBlock` from a state holding the geometry bank
and the access and interior array bases below the extent. The buffer starts
right after the stack arrays; its first `denseCount * W` cells are exactly
`(densePad W (packedReviewerPaddedBits shape)).map bitToNat` at
`W = wordWidth n`, and the extent ends at most one probe cell later.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec Spec.StackCartesianTreeSpec RMQ.Cartesian SuccinctClose RMQ.GenericSelect
  SuccinctSpace

/-! ## Register transport -/

theorem GeoBase.congr {n : Nat} {r r' : Registers} (h : GeoBase n r)
    (hr : ∀ x : Nat, (x = 1 ∨ x = 2 ∨ x = 9 ∨ (30 ≤ x ∧ x ≤ 37)) → r' x = r x) :
    GeoBase n r' := by
  obtain ⟨h1, h2, h9, h30, h31, h32, h33, h34, h35, h36, h37⟩ := h
  exact ⟨by rw [hr 1 (by omega)]; exact h1, by rw [hr 2 (by omega)]; exact h2,
    by rw [hr 9 (by omega)]; exact h9, by rw [hr 30 (by omega)]; exact h30,
    by rw [hr 31 (by omega)]; exact h31, by rw [hr 32 (by omega)]; exact h32,
    by rw [hr 33 (by omega)]; exact h33, by rw [hr 34 (by omega)]; exact h34,
    by rw [hr 35 (by omega)]; exact h35, by rw [hr 36 (by omega)]; exact h36,
    by rw [hr 37 (by omega)]; exact h37⟩

theorem GeoUpTo.congr {n k : Nat} {r r' : Registers} (h : GeoUpTo n k r)
    (hr : ∀ x : Nat, 38 ≤ x → x < 38 + k → r' x = r x) : GeoUpTo n k r' :=
  fun i hi => by rw [hr (38 + i) (by omega) (by omega)]; exact h i hi

/-- Registers every phase of the buffer stage leaves unchanged. -/
abbrev BufferKept (r : Nat) : Prop :=
  r ≤ 3 ∨ r = 9 ∨ (29 ≤ r ∧ r ≤ 99) ∨ (115 ≤ r ∧ r ≤ 118) ∨ r = 135 ∨ r = 136 ∨
    (159 ≤ r ∧ r ≤ 164) ∨ 229 ≤ r

/-- Registers the buffer stage leaves unchanged, as reported. -/
abbrev BufferFrame (r : Nat) : Prop := ¬ (4 ≤ r ∧ r ≤ 28) ∧ ¬ (100 ≤ r ∧ r ≤ 228)

/-! ## Emission above a base address -/

/-- `Emits` restricted to the addresses at or above `base`. -/
def EmitsFrom (base : Nat) (s₀ s : State) (vals : List Nat) : Prop :=
  s.extent = s₀.extent + vals.length ∧
    ∀ a, base ≤ a → s.memory a =
      if s₀.extent ≤ a ∧ a < s₀.extent + vals.length then vals[a - s₀.extent]? else s₀.memory a

theorem Emits.emitsFrom {base : Nat} {s₀ s : State} {vals : List Nat} (h : Emits s₀ s vals) :
    EmitsFrom base s₀ s vals := ⟨h.1, fun a _ => h.2 a⟩

theorem Emits.shiftFrom {base : Nat} {u t s : State} {vals : List Nat} (h : Emits t s vals)
    (he : t.extent = u.extent) (hm : ∀ a, base ≤ a → t.memory a = u.memory a) :
    EmitsFrom base u s vals :=
  ⟨by rw [h.1, he], fun a ha => by rw [h.2 a, he, hm a ha]⟩

theorem EmitsFrom.trans {base : Nat} {s₀ s₁ s₂ : State} {v w : List Nat}
    (h₁ : EmitsFrom base s₀ s₁ v) (h₂ : EmitsFrom base s₁ s₂ w) : EmitsFrom base s₀ s₂ (v ++ w) := by
  obtain ⟨he₁, hm₁⟩ := h₁
  obtain ⟨he₂, hm₂⟩ := h₂
  refine ⟨by simp [he₂, he₁, Nat.add_assoc], fun a ha => ?_⟩
  rw [hm₂ a ha, hm₁ a ha, he₁]
  simp only [List.length_append]
  by_cases hlo : s₀.extent ≤ a
  · by_cases hv : a < s₀.extent + v.length
    · have hin : s₀.extent ≤ a ∧ a < s₀.extent + (v.length + w.length) := ⟨hlo, by omega⟩
      have hout : ¬ (s₀.extent + v.length ≤ a ∧ a < s₀.extent + v.length + w.length) := by omega
      rw [if_neg hout, if_pos ⟨hlo, hv⟩, if_pos hin, List.getElem?_append_left (by omega)]
    · by_cases hw : a < s₀.extent + v.length + w.length
      · have hin : s₀.extent ≤ a ∧ a < s₀.extent + (v.length + w.length) := ⟨hlo, by omega⟩
        rw [if_pos ⟨by omega, hw⟩, if_pos hin, List.getElem?_append_right (by omega)]
        congr 1
        omega
      · have hout : ¬ (s₀.extent + v.length ≤ a ∧ a < s₀.extent + v.length + w.length) := by omega
        have hout' : ¬ (s₀.extent ≤ a ∧ a < s₀.extent + (v.length + w.length)) := by omega
        rw [if_neg hout, if_neg (by omega), if_neg hout']
  · have hout : ¬ (s₀.extent + v.length ≤ a ∧ a < s₀.extent + v.length + w.length) := by omega
    rw [if_neg hout, if_neg (by omega), if_neg (by omega)]

theorem EmitsFrom.memory_at {base : Nat} {s₀ s : State} {vals : List Nat}
    (h : EmitsFrom base s₀ s vals) (hb : base ≤ s₀.extent) {i : Nat} (hi : i < vals.length) :
    s.memory (s₀.extent + i) = some vals[i] := by
  rw [h.2 _ (by omega), if_pos ⟨by omega, by omega⟩]
  simp [List.getElem?_eq_getElem hi]

/-! ## The dense buffer of the reference, cell by cell -/

theorem getD_map_append_replicate_false (P : List Bool) (m j : Nat) :
    ((P ++ List.replicate m false).map bitToNat).getD j 0 = (P.map bitToNat).getD j 0 := by
  simp only [List.map_append, List.map_replicate, List.getD_eq_getElem?_getD]
  by_cases hj : j < P.length
  · rw [List.getElem?_append_left (by simpa using hj)]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate,
      List.getElem?_eq_none (l := P.map bitToNat) (by simp; omega)]
    split <;> simp [bitToNat]

/-- **Buffer cells.** Cell `i` of the dense buffer is bit `i` of the long count
inside the header, and otherwise the payload cell `i - oldW` (zero past the
payload). -/
theorem bufferCells_getD (shape : CartesianShape) (i : Nat) :
    ((PackedWordRAM.densePad (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerPaddedBits shape)).map bitToNat).getD i 0 =
      if i < PackedCellProbe.packedReviewerCellWidth shape.size then
        PackedCellProbe.longCount shape / 2 ^ i % 2
      else ((PackedCellProbe.packedReviewerPayloadBits shape).map bitToNat).getD
        (i - PackedCellProbe.packedReviewerCellWidth shape.size) 0 := by
  simp only [PackedWordRAM.densePad]
  rw [getD_map_append_replicate_false]
  simp only [PackedCellProbe.packedReviewerPaddedBits]
  rw [getD_map_append_replicate_false]
  simp only [PackedCellProbe.packedReviewerSerializedBits, PackedCellProbe.packedReviewerHeaderBits,
    List.map_append, List.getD_eq_getElem?_getD]
  have hlen := natToBitsLE_length (PackedCellProbe.packedReviewerCellWidth shape.size)
    (PackedCellProbe.longCount shape)
  split
  · rename_i hi
    rw [List.getElem?_append_left (by simp [hlen]; exact hi), List.getElem?_map,
      Spec.natToBitsLE_getElem? _ _ _ hi]
    simp only [Option.map_some, Option.getD_some]
    exact bitToNat_decide_mod_two _
  · rename_i hi
    rw [List.getElem?_append_right (by simp [hlen]; omega)]
    simp [hlen]

/-! ## Dense bit count -/

/-- The dense bit count of the reference, in the pad block's form. -/
theorem bufferCells_length (shape : CartesianShape) :
    ((PackedWordRAM.densePad (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerPaddedBits shape)).map bitToNat).length =
      denseBitsOf (PackedCellProbe.packedReviewerCellWidth shape.size)
        (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerCellWidth shape.size +
          PackedCellProbe.packedReviewerPayloadLength shape.size (PackedCellProbe.longCount shape)
            (PackedCellProbe.packedReviewerSparseCount shape)) := by
  have hpos := PackedCellProbe.packedReviewerCellWidth_pos shape.size
  rw [List.length_map, PackedWordRAM.densePad_length _ _ (PackedWordRAM.wordWidth_pos _)]
  unfold PackedWordRAM.denseCount denseBitsOf
  rw [PackedCellProbe.packedReviewerPaddedBits_length]
  unfold PackedCellProbe.packedReviewerAllocatedBits PackedCellProbe.packedReviewerCellCount
    GenericSelect.selectCeilDiv
  rw [Nat.add_comm 1, Nat.add_comm (PackedCellProbe.packedReviewerCellWidth shape.size)]

/-! ## Microtables, header patch and paddings -/

/-- **Buffer tail.** From a state whose cells above `buf` are `oldW` zero header
cells followed by `Q`, the microtables, the header patch and the paddings leave
the dense bit count `D` of `L = oldW + (Q ++ microtables).length` cells at `buf`:
the long-count bits in the header, then `Q ++ microtables`, then zeros. -/
theorem bufferTail_spec {W : Nat} (hW : 32 ≤ W) (n c oldW WW buf lc : Nat)
    (hc : bpFringeChunkBits (2 * n) = c) (hOW : PackedCellProbe.packedReviewerCellWidth n = oldW)
    (hWW : PackedWordRAM.wordWidth n = WW)
    (sC u0 : State) (hrun : sC.status = .running) (hbank : GeoUpTo n 39 sC.regs)
    (hzero : sC.regs 0 = 0) (hone : sC.regs 2 = 1) (htwo : sC.regs 9 = 2)
    (h220 : sC.regs 220 = buf) (h177 : sC.regs 177 = lc) (hlc : lc ≤ n)
    (Q : List Nat) (hu0 : u0.extent = buf)
    (Epre : EmitsFrom buf u0 sC (List.replicate oldW 0 ++ Q))
    (hQ : Q.length + (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).length +
      (tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).length + 2 ≤
        400000 * (n + 1))
    (hcap : buf + 8 * (400000 * (n + 1)) < 2 ^ W) :
    ∃ s' k, SafeEval W (.seq microtablesBlock (.seq headerPatchBlock padBlock)) sC s' k ∧
      k ≤ 100 * (400000 * (n + 1)) ∧ s'.status = .running ∧
      buf + denseBitsOf oldW WW (oldW + (Q ++ (tableBits (bpFringeChunkEntries c)
          (bpFringeChunkEntryWidth c) ++ tableBits (bpChunkSelectEntries c false)
          (bpChunkSelectEntryWidth c)).map bitToNat).length) ≤ s'.extent ∧
      s'.extent ≤ buf + denseBitsOf oldW WW (oldW + (Q ++ (tableBits (bpFringeChunkEntries c)
          (bpFringeChunkEntryWidth c) ++ tableBits (bpChunkSelectEntries c false)
          (bpChunkSelectEntryWidth c)).map bitToNat).length) + 1 ∧
      (∀ i, i < denseBitsOf oldW WW (oldW + (Q ++ (tableBits (bpFringeChunkEntries c)
          (bpFringeChunkEntryWidth c) ++ tableBits (bpChunkSelectEntries c false)
          (bpChunkSelectEntryWidth c)).map bitToNat).length) →
        s'.memory (buf + i) = some (if i < oldW then lc / 2 ^ i % 2 else
          (Q ++ (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c) ++
            tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map bitToNat).getD
            (i - oldW) 0)) ∧
      (∀ a, a < buf → s'.memory a = sC.memory a) ∧
      (∀ r, BufferKept r → s'.regs r = sC.regs r) ∧
      s'.regs 220 = buf ∧ s'.regs 177 = lc ∧ s'.regs 178 = sC.regs 178 ∧ s'.keys = sC.keys := by
  generalize hMd : (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c) ++
    tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map bitToNat = Mc
  have hMcl : Mc.length = (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).length +
      (tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).length := by
    rw [← hMd, List.length_map, List.length_append]
  have hWl := wordWidth_le_linear n
  have hOWlt := PackedWordRAM.oldWidth_lt_wordWidth n
  have hOWpos := PackedCellProbe.packedReviewerCellWidth_pos n
  have hWWpos := PackedWordRAM.wordWidth_pos n
  have hfr := fringeRows_mul_scan_le n
  have hsr := selectRows_mul_scan_le n
  rw [hOW] at hOWlt hOWpos
  rw [hWW] at hOWlt hWWpos hWl
  rw [hc] at hfr hsr
  generalize hB : 400000 * (n + 1) = B at *
  have hbufe : buf + oldW ≤ sC.extent := by
    rw [Epre.1, hu0, List.length_append, List.length_replicate]; omega
  have hCext : sC.extent = buf + oldW + Q.length := by
    rw [Epre.1, hu0, List.length_append, List.length_replicate, Nat.add_assoc]
  -- microtables
  have hrowsF : (c + 1) * (c + 1) ≤ bpFringeChunkRowCount c :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos c)
  have hcube : (c + 1) * (c + 1) * (c + 1) ≤ bpFringeChunkRowCount c * (c + 1) :=
    Nat.mul_le_mul_right _ hrowsF
  have hrF1 : bpFringeChunkRowCount c ≤ bpFringeChunkRowCount c * (c + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hrS1 : bpChunkSelectRowCount c ≤ bpChunkSelectRowCount c * (c + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hlenF : (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).length =
      bpFringeChunkRowCount c * bpFringeChunkEntryWidth c := by
    rw [tableBits_length, bpFringeChunkEntries_length]
  have hlenS : (tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).length =
      bpChunkSelectRowCount c * bpChunkSelectEntryWidth c := by
    rw [tableBits_length, bpChunkSelectEntries_length]
  obtain ⟨sM, kM, eM, hkM, hMr, EM, hMfr, _, hMk⟩ :=
    microtables_spec hW sC hrun hone htwo c
      (by rw [← hc]; exact hbank 26 (by decide))
      (by rw [← hc]; exact hbank 27 (by decide))
      (by rw [← hc]; exact hbank 28 (by decide))
      (by rw [← hc]; exact hbank 29 (by decide))
      (by rw [← hc]; exact hbank 30 (by decide))
      (by omega) (by rw [hCext]; omega)
  rw [hMd] at EM
  have hMext : sM.extent = buf + oldW + (Q.length + Mc.length) := by
    rw [EM.1, hCext, Nat.add_assoc]
  have fM : ∀ r, BufferKept r → sM.regs r = sC.regs r := by
    intro r hr
    unfold BufferKept at hr
    exact hMfr r (by omega) (show ¬ (10 ≤ r ∧ r ≤ 16) by omega)
  have hM220 : sM.regs 220 = buf := by rw [hMfr 220 (by decide) (by decide), h220]
  have hM177 : sM.regs 177 = lc := by rw [hMfr 177 (by decide) (by decide), h177]
  have Eall : EmitsFrom buf u0 sM (List.replicate oldW 0 ++ (Q ++ Mc)) := by
    have h := Epre.trans EM.emitsFrom
    rw [List.append_assoc] at h
    exact h
  -- header patch
  obtain ⟨sQ, kQ, eQ, hkQ, hQr, hQext, hQmem, hQfr, _, hQk⟩ :=
    headerPatch_spec hW sM hMr (by rw [fM 2 (by decide), hone]) (by rw [fM 9 (by decide), htwo])
      buf oldW lc hM220
      (by rw [fM 75 (by decide), ← hOW]; exact hbank 37 (by decide)) hM177 (by omega)
      (by rw [hMext]; omega) (by rw [hMext]; omega)
  -- paddings
  obtain ⟨s', kZ, eZ, hkZ, hs'r, hLD, hDle, EZ, hZfr, _, hZk⟩ :=
    pad_spec hW sQ hQr (by rw [hQfr 0 (by decide) (by decide) (by decide), fM 0 (by decide), hzero])
      (by rw [hQfr 2 (by decide) (by decide) (by decide), fM 2 (by decide), hone]) buf
      (oldW + (Q ++ Mc).length) oldW WW
      (by rw [hQfr 220 (by decide) (by decide) (by decide), hM220])
      (by rw [hQext, hMext, List.length_append]; omega)
      (by rw [hQfr 75 (by decide) (by decide) (by decide), fM 75 (by decide), ← hOW]
          exact hbank 37 (by decide))
      (by rw [hQfr 76 (by decide) (by decide) (by decide), fM 76 (by decide), ← hWW]
          exact hbank 38 (by decide))
      hOWpos hWWpos (by omega) (by rw [List.length_append]; omega)
  rw [List.length_append] at hLD hDle hkZ EZ ⊢
  generalize hDg : denseBitsOf oldW WW (oldW + (Q.length + Mc.length)) = D at hLD hDle hkZ EZ ⊢
  generalize hZd : (D - (oldW + (Q.length + Mc.length)) -
    (if oldW + (Q.length + Mc.length) < D then 1 else 0)) = Z at EZ
  have hZ1 : D - (oldW + (Q.length + Mc.length)) ≤ Z + 1 ∧ Z + 1 ≤ D - (oldW + (Q.length + Mc.length)) + 1 := by
    rw [← hZd]; split <;> omega
  have hsext : s'.extent = buf + (oldW + (Q.length + Mc.length)) + (Z + 1) := by
    rw [EZ.1, List.length_replicate, hQext, hMext]; omega
  refine ⟨s', kM + (kQ + kZ), EvalG.seq eM (EvalG.seq eQ eZ), ?_, hs'r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [hZk, hQk, hMk]⟩
  · have hmF : bpFringeChunkRowCount c * (25 * c + 42 + 7 * bpFringeChunkEntryWidth c + 7) =
        25 * (bpFringeChunkRowCount c * c) + 49 * bpFringeChunkRowCount c +
          7 * (bpFringeChunkRowCount c * bpFringeChunkEntryWidth c) := by
      simp only [Nat.mul_add]
      rw [Nat.mul_left_comm (bpFringeChunkRowCount c) 25 c,
        Nat.mul_left_comm (bpFringeChunkRowCount c) 7 (bpFringeChunkEntryWidth c)]
      omega
    have hmS : bpChunkSelectRowCount c * (14 * c + 9 + 7 * bpChunkSelectEntryWidth c + 7) =
        14 * (bpChunkSelectRowCount c * c) + 16 * bpChunkSelectRowCount c +
          7 * (bpChunkSelectRowCount c * bpChunkSelectEntryWidth c) := by
      simp only [Nat.mul_add]
      rw [Nat.mul_left_comm (bpChunkSelectRowCount c) 14 c,
        Nat.mul_left_comm (bpChunkSelectRowCount c) 7 (bpChunkSelectEntryWidth c)]
      omega
    have hcF : bpFringeChunkRowCount c * c ≤ bpFringeChunkRowCount c * (c + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hcS : bpChunkSelectRowCount c * c ≤ bpChunkSelectRowCount c * (c + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [hsext]; omega
  · rw [hsext]; omega
  · intro i hi
    by_cases hiL : i < oldW + (Q.length + Mc.length)
    · rw [EZ.memory_below (by rw [hQext, hMext]; omega), hQmem]
      by_cases hio : i < oldW
      · rw [if_pos ⟨by omega, by omega⟩, if_pos hio, show buf + i - buf = i by omega]
      · rw [if_neg (by omega), if_neg hio]
        have hm := Eall.memory_at (i := i) (by rw [hu0]; exact Nat.le_refl _)
          (by rw [List.length_append, List.length_replicate, List.length_append]; omega)
        rw [hu0] at hm
        rw [hm, List.getElem_append_right (by simp; omega)]
        simp only [List.length_replicate]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
    · rw [show buf + i = sQ.extent + (i - (oldW + (Q.length + Mc.length))) by rw [hQext, hMext]; omega,
        EZ.memory_at (by simp only [List.length_replicate]; omega)]
      simp only [List.getElem_replicate]
      rw [if_neg (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_append]; omega)]
      rfl
  · intro a ha
    rw [EZ.memory_below (by rw [hQext, hMext]; omega), hQmem, if_neg (by omega),
      EM.memory_below (by rw [hCext]; omega)]
  · intro r hr
    have hr' := hr
    unfold BufferKept at hr'
    rw [hZfr r (by omega) (by omega) (by omega), hQfr r (by omega) (by omega) (by omega), fM r hr]
  · rw [hZfr 220 (by decide) (by decide) (by decide), hQfr 220 (by decide) (by decide) (by decide), hM220]
  · rw [hZfr 177 (by decide) (by decide) (by decide), hQfr 177 (by decide) (by decide) (by decide), hM177]
  · rw [hZfr 178 (by decide) (by decide) (by decide), hQfr 178 (by decide) (by decide) (by decide),
      hMfr 178 (by decide) (by decide)]

/-! ## Access half and interior close -/

/-- **Access and close.** From the bank, the BP cells at `B`, the array bases
laid out below `buf ≤ B`, the access half and the interior close append the
live access payload and the interior directory payload. -/
theorem bufferAccessClose_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (n : Nat)
    (hsize : shape.size = n) (sB : State) (hrun : sB.status = .running)
    (hgeo : GeoBase n sB.regs) (hbank : GeoUpTo n 39 sB.regs)
    (hbankcap : 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W)
    (P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb buf B : Nat)
    (h119 : sB.regs 119 = B)
    (h159 : sB.regs 159 = P0) (h160 : sB.regs 160 = R0) (h161 : sB.regs 161 = L0)
    (h162 : sB.regs 162 = C0) (h163 : sB.regs 163 = F0) (h164 : sB.regs 164 = G0)
    (h115 : sB.regs 115 = A0) (h116 : sB.regs 116 = A1) (h117 : sB.regs 117 = A2)
    (h118 : sB.regs 118 = A3) (h135 : sB.regs 135 = Bm) (h136 : sB.regs 136 = Gb)
    (hR : Region sB B shape.bpCode.length (bpCell shape))
    (hBext : sB.extent = B + shape.bpCode.length)
    (hPR : P0 + n + 1 ≤ R0)
    (hRL : R0 + shape.bpCode.length / wordBits shape.bpCode.length + 1 ≤ L0)
    (hLC : L0 + superSlotCount shape.bpCode false ≤ C0)
    (hCF : C0 + superSlotCount shape.bpCode false + 1 ≤ F0)
    (hFG : F0 + localSlotCount shape.bpCode false ≤ G0)
    (hGe : G0 + localSlotCount shape.bpCode false + 1 ≤ buf)
    (hA01 : A0 + geoBlocks n + 1 ≤ A1) (hA12 : A1 + geoBlocks n ≤ A2)
    (hA23 : A2 + geoBlocks n ≤ A3) (hA3m : A3 + geoBlocks n ≤ Bm)
    (hmG : Bm + SuccinctRank.machineWordBits (geoMacro n) * geoBlocks n ≤ Gb)
    (hGbe : Gb + SuccinctRank.machineWordBits (geoMacros n) * geoMacros n ≤ buf)
    (hbufB : buf ≤ B)
    (hcap : sB.extent + 17 * (400000 * (n + 1)) < 2 ^ W) :
    ∃ sX sC kA kC, SafeEval W accessHalfBlock sB sX kA ∧ SafeEval W interiorCloseBlock sX sC kC ∧
      kA + kC ≤ 1800 * (400000 * (n + 1)) ∧ sC.status = .running ∧
      EmitsFrom buf sB sC
        ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).map bitToNat ++
          (canonicalRelativeRmmInteriorDirectory shape).payload.map bitToNat) ∧
      (∀ a, a < buf → (a < P0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) →
        (a < A0 ∨ Gb + SuccinctRank.machineWordBits (geoMacros n) * geoMacros n ≤ a) →
        sC.memory a = sB.memory a) ∧
      sC.regs 177 = PackedCellProbe.longCount shape ∧
      sC.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r, BufferKept r → sC.regs r = sB.regs r) ∧ sC.regs 220 = sB.regs 220 ∧
      sC.keys = sB.keys := by
  subst hsize
  have hlen : shape.bpCode.length = 2 * shape.size := CartesianShape.bpCode_length shape
  have hsegs := planPayload_length_add_two_le shape
  rw [← liveAccessPayload_eq_segments] at hsegs
  simp only [List.length_append] at hsegs
  generalize hB : 400000 * (shape.size + 1) = BB at *
  obtain ⟨tA, sX, kA, eA, hkA, hXr, htAext, htAmem, EX, hX177, hX178, hXfr, hXk⟩ :=
    accessHalf_spec hW shape sB hrun hgeo hbank hbankcap P0 R0 L0 C0 F0 G0 B h119 h159 h160 h161
      h162 h163 h164 hR (by omega) hPR hRL hLC hCF hFG (by omega) (by omega)
  have hXext : sX.extent = sB.extent +
      (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).length := by
    rw [EX.1, List.length_map, htAext]
  have kX : ∀ r, BufferKept r → sX.regs r = sB.regs r := by
    intro r hr
    unfold BufferKept at hr
    exact hXfr r ⟨show ¬ (10 ≤ r ∧ r ≤ 16) by omega, by omega, by omega, by omega, by omega⟩
  have hXR : Region sX B shape.bpCode.length (bpCell shape) := by
    intro k hk
    rw [EX.memory_below (by rw [htAext, hBext]; omega), htAmem _ (Or.inr (by omega))]
    exact hR k hk
  have geoX : GeoBase shape.size sX.regs :=
    GeoBase.congr hgeo (fun x hx => kX x (by unfold BufferKept; omega))
  have bankX : GeoUpTo shape.size 39 sX.regs :=
    GeoUpTo.congr hbank (fun x h1 h2 => kX x (by unfold BufferKept; omega))
  obtain ⟨tC, sC, kC, eC, hkC, hCr, htCext, htCmem, EC, hCfr, hCk⟩ :=
    closeSegment_spec hW shape sX hXr geoX bankX A0 A1 A2 A3 B Bm Gb
      (by rw [kX 115 (by decide), h115]) (by rw [kX 116 (by decide), h116])
      (by rw [kX 117 (by decide), h117]) (by rw [kX 118 (by decide), h118])
      (by rw [hXfr 119 (by decide), h119])
      (by rw [kX 135 (by decide), h135]) (by rw [kX 136 (by decide), h136]) hXR
      (by rw [hXext]; omega) hA01 hA12 hA23 hA3m hmG (by omega) (by rw [hXext]; omega)
  refine ⟨sX, sC, kA, kC, eA, eC, by omega, hCr, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hCk, hXk]⟩
  · exact (EX.shiftFrom htAext (fun a ha => htAmem a (Or.inr (by omega)))).trans
      (EC.shiftFrom htCext (fun a ha => htCmem a (Or.inr (by omega))))
  · intro a ha hP hA
    rw [EC.memory_below (by rw [htCext, hXext]; omega), htCmem a hA,
      EX.memory_below (by rw [htAext]; omega), htAmem a hP]
  · rw [hCfr 177 ⟨by omega, by omega, by omega, by omega, by omega⟩, hX177]; rfl
  · rw [hCfr 178 ⟨by omega, by omega, by omega, by omega, by omega⟩, hX178]
  · intro r hr
    have hr' := hr
    unfold BufferKept at hr'
    rw [hCfr r ⟨by omega, by omega, by omega, by omega, by omega⟩, kX r hr]
  · rw [hCfr 220 ⟨by omega, by omega, by omega, by omega, by omega⟩, hXfr 220 (by decide)]

/-! ## Stack arrays, stack pass, header cells and BP code -/

/-- **Buffer head.** The stack arrays and the stack pass, then the `oldW` header
cells at `buf = s.extent + 3 * (n + 1)` and the BP code of `shape xs` right
after them. -/
theorem bufferHead_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (s : State) (hrun : s.status = .running)
    (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1) (hn : s.regs 1 = xs.length)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent) (oldW : Nat) (h75 : s.regs 75 = oldW)
    (hold : 1 ≤ oldW) (hcap : s.extent + 3 * (xs.length + 1) + oldW + 2 * xs.length + 2 < 2 ^ W) :
    ∃ sA sP sH sB k1 k2 kH kE, SafeEval W stackArraysBlock s sA k1 ∧
      SafeEval W (stackPassBlock leaf) sA sP k2 ∧ SafeEval W headerReserveBlock sP sH kH ∧
      SafeEval W bpEmitBlock sH sB kE ∧ k1 + k2 + kH + kE ≤ 79 * xs.length + 21 + 5 * oldW ∧
      sB.status = .running ∧ sP.extent = s.extent + 3 * (xs.length + 1) ∧
      EmitsFrom (s.extent + 3 * (xs.length + 1)) sP sB
        (List.replicate oldW 0 ++ (shape xs).bpCode.map bitToNat) ∧
      sB.extent = s.extent + 3 * (xs.length + 1) + oldW + (shape xs).bpCode.length ∧
      Region sB (s.extent + 3 * (xs.length + 1) + oldW) (shape xs).bpCode.length (bpCell (shape xs)) ∧
      (∀ a, a < s.extent → sB.memory a = s.memory a) ∧
      sB.regs 119 = s.extent + 3 * (xs.length + 1) + oldW ∧
      sB.regs 220 = s.extent + 3 * (xs.length + 1) ∧
      (∀ r, BufferKept r → sB.regs r = s.regs r) ∧ sB.keys = s.keys := by
  have hlen0 := CartesianShape.bpCode_length (shape xs)
  rw [Cartesian.shape_size] at hlen0
  generalize hnv : xs.length = n at *
  -- arrays
  obtain ⟨sA, k1, e1, hk1, hAr, hAem, hA100, hA101, hA102, hAfr, _, hAk⟩ :=
    stackArrays_spec hW n s hrun hzero hone hn (by omega)
  have hAext : sA.extent = s.extent + 3 * (n + 1) := by rw [hAem.1]; simp
  have hA : PassStart xs s.extent sA := by
    refine ⟨hA100, by rw [hnv]; exact hA101, by rw [hnv]; exact hA102, ?_, ?_, ?_⟩
    · rw [hAfr 2 (by decide) (by decide) (by decide) (by decide) (by decide), hone]
    · rw [hAfr 1 (by decide) (by decide) (by decide) (by decide) (by decide), hn, hnv]
    · rw [hAext, hnv]; exact Nat.le_refl _
  have hinpA : Inp sA := hInp s sA hinp (fun b hb => hAem.memory_below hb)
    (by rw [hAext]; exact Nat.le_add_right _ _) (by rw [hAk])
  have hzeroA : Region sA s.extent (3 * (xs.length + 1)) (fun _ => 0) := by
    rw [hnv]; exact hAem.region_zero
  -- stack pass
  obtain ⟨sP, k2, e2, hk2, hPr, hinv, hP1, hP2⟩ :=
    stackPass_spec hW xs Inp leaf hleaf s.extent hInp sA hA hinpA hAr hzeroA
      (by rw [hnv]; omega)
  obtain ⟨_, hPext, hPkeys, hPout, hPfr, M, hPR', _, _, hPcnt⟩ := hinv
  rw [hnv] at hk2 hP1 hPR' hPcnt hPout
  have hCeq : countsAt xs n = openCounts (StackCartesianTree.buildTree xs).shape := by
    show openCounts (StackCartesianTree.buildTree (xs.take n)).shape = _
    rw [← hnv, List.take_length]
  have hsize' : (StackCartesianTree.buildTree xs).shape.size = n := by
    rw [← values_length, StackCartesianTree.buildTree_values, hnv]
  have fP : ∀ r, BufferKept r → sP.regs r = s.regs r := by
    intro r hr
    unfold BufferKept at hr
    rw [hPfr r (by omega) (by omega), hAfr r (by omega) (by omega) (by omega) (by omega) (by omega)]
  have hPe : sP.extent = s.extent + 3 * (n + 1) := by rw [hPext, hAext]
  -- header cells
  obtain ⟨sH, kH, eH, hkH, hHr, EH, hH220, hH119, hHfr, _, hHk⟩ :=
    headerReserve_spec hW sP hPr (by rw [fP 0 (by decide), hzero]) hP2 oldW
      (by rw [fP 75 (by decide), h75]) hold (by rw [hPe]; omega)
  rw [hPe] at hH220 hH119
  have fH : ∀ r, BufferKept r → sH.regs r = s.regs r := by
    intro r hr
    have hr' := hr
    unfold BufferKept at hr'
    rw [hHfr r (by omega) (by omega) (by omega) (by omega) (by omega), fP r hr]
  have hHext : sH.extent = s.extent + 3 * (n + 1) + oldW := by rw [EH.1, List.length_replicate, hPe]
  -- BP code
  have hRH : Region sH s.extent (3 * (n + 1)) M := by
    intro a ha
    rw [EH.memory_below (by rw [hPe]; omega)]
    exact hPR' a ha
  obtain ⟨sB, kE, eE, hkE, hBr, EB, hBfr, hBk⟩ :=
    bpEmit_spec hW s.extent n (openCounts (StackCartesianTree.buildTree xs).shape)
      (by rw [openCounts_length, hsize']) (by rw [openCounts_sum, hsize']) M sH hHr
      (by rw [fH 0 (by decide), hzero]) (by rw [fH 2 (by decide), hone])
      (by rw [fH 1 (by decide), hn])
      (by rw [hHfr 102 (by decide) (by decide) (by decide) (by decide) (by decide),
        hPfr 102 (by decide) (by decide), hA102])
      hRH (by rw [hHext]; omega)
      (fun j hj => by rw [hPcnt j (by omega), hCeq])
      (by rw [hHext]; omega)
  rw [← bpCells_eq] at EB
  have hbpl : ((shape xs).bpCode.map bitToNat).length = (shape xs).bpCode.length := List.length_map _
  refine ⟨sA, sP, sH, sB, k1, k2, kH, kE, e1, e2, eH, eE, by omega, hBr, hPe, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, by rw [hBk, hHk, hPkeys, hAk]⟩
  · have h := EH.emitsFrom (base := s.extent + 3 * (n + 1)) |>.trans EB.emitsFrom
    exact h
  · rw [EB.1, hbpl, hHext]
  · intro k hk
    have hk' : k < ((shape xs).bpCode.map bitToNat).length := by rw [hbpl]; exact hk
    have hm := EB.memory_at hk'
    rw [hHext] at hm
    rw [hm]
    simp [bpCell, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  · intro a ha
    rw [EB.memory_below (by rw [hHext]; omega), EH.memory_below (by rw [hPe]; omega),
      hPout a (Or.inl ha), hAem.memory_below ha]
  · rw [hBfr 119 (by decide) (by decide) (by decide) (by decide) (by decide), hH119]
  · rw [hBfr 220 (by decide) (by decide) (by decide) (by decide) (by decide), hH220]
  · intro r hr
    have hr' := hr
    unfold BufferKept at hr'
    rw [hBfr r (by omega) (by omega) (by omega) (by omega) (by omega), fH r hr]

/-! ## The buffer stage -/

/-- **S6 exit: the bit buffer.** From a running state with the constants, the
input length and the geometry bank in their registers, an input predicate that
only reads memory below the extent, the access and interior array bases laid
out below the extent, and a capacity margin, the stack arrays, the stack pass
and `bufferBlock` leave, at the buffer base `s.extent + 3 * (n + 1)` held in
register 220, exactly the dense buffer of the reference; the extent ends at
most one cell after it. Memory below `s.extent` changes only inside the two
array layouts, the long count is in register 177 and the sparse-exception flag
count in register 178. Every register the buffer phase does not use
(`BufferKept`) is unchanged. -/
theorem bufferStage_kept {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (s : State) (hrun : s.status = .running)
    (hzero : s.regs 0 = 0) (hgeo : GeoBase xs.length s.regs)
    (hbank : GeoUpTo xs.length 39 s.regs)
    (hbankcap : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb : Nat)
    (h159 : s.regs 159 = P0) (h160 : s.regs 160 = R0) (h161 : s.regs 161 = L0)
    (h162 : s.regs 162 = C0) (h163 : s.regs 163 = F0) (h164 : s.regs 164 = G0)
    (h115 : s.regs 115 = A0) (h116 : s.regs 116 = A1) (h117 : s.regs 117 = A2)
    (h118 : s.regs 118 = A3) (h135 : s.regs 135 = Bm) (h136 : s.regs 136 = Gb)
    (hPR : P0 + xs.length + 1 ≤ R0)
    (hRL : R0 + (shape xs).bpCode.length / wordBits (shape xs).bpCode.length + 1 ≤ L0)
    (hLC : L0 + superSlotCount (shape xs).bpCode false ≤ C0)
    (hCF : C0 + superSlotCount (shape xs).bpCode false + 1 ≤ F0)
    (hFG : F0 + localSlotCount (shape xs).bpCode false ≤ G0)
    (hGe : G0 + localSlotCount (shape xs).bpCode false + 1 ≤ s.extent)
    (hA01 : A0 + geoBlocks xs.length + 1 ≤ A1) (hA12 : A1 + geoBlocks xs.length ≤ A2)
    (hA23 : A2 + geoBlocks xs.length ≤ A3) (hA3m : A3 + geoBlocks xs.length ≤ Bm)
    (hmG : Bm + SuccinctRank.machineWordBits (geoMacro xs.length) * geoBlocks xs.length ≤ Gb)
    (hGbe : Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ s.extent)
    (hcap : s.extent + 32 * (400000 * (xs.length + 1)) < 2 ^ W) :
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock leaf) bufferBlock)) s s' k ∧
      k ≤ 2000 * (400000 * (xs.length + 1)) ∧ s'.status = .running ∧
      s'.regs 220 = s.extent + 3 * (xs.length + 1) ∧
      ArrayAt s' (s.extent + 3 * (xs.length + 1))
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length
        (fun i => ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).getD i 0) ∧
      s'.extent ≤ s.extent + 3 * (xs.length + 1) +
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length + 1 ∧
      (∀ a, a < s.extent → (a < P0 ∨ G0 + localSlotCount (shape xs).bpCode false + 1 ≤ a) →
        (a < A0 ∨ Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ a) →
        s'.memory a = s.memory a) ∧
      s'.regs 177 = PackedCellProbe.longCount (shape xs) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits (shape xs).bpCode false)
        (localSlotCount (shape xs).bpCode false) ∧
      (∀ r, BufferKept r → s'.regs r = s.regs r) ∧ s'.keys = s.keys := by
  have hsize : (shape xs).size = xs.length := Cartesian.shape_size xs
  have hlen : (shape xs).bpCode.length = 2 * xs.length := by rw [CartesianShape.bpCode_length, hsize]
  have hWl := wordWidth_le_linear xs.length
  have hOW := PackedWordRAM.oldWidth_lt_wordWidth xs.length
  -- head
  obtain ⟨sA, sP, sH, sB, k1, k2, kH, kE, e1, e2, eH, eE, hkh, hBr, hPe, EPB, hBext, hBR, hBmem,
      hB119, hB220, fB, hBk⟩ :=
    bufferHead_spec hW xs Inp leaf hleaf s hrun hzero hgeo.2.1 hgeo.1 hinp hInp
      (PackedCellProbe.packedReviewerCellWidth xs.length) (hbank 37 (by decide))
      (PackedCellProbe.packedReviewerCellWidth_pos _) (by omega)
  generalize hbuf : s.extent + 3 * (xs.length + 1) = buf at hPe EPB hBext hBR hB119 hB220 ⊢
  -- access half and interior close
  obtain ⟨sX, sC, kA, kC, eA, eC, hkAC, hCr, EBC, hCmem, hC177, hC178, fCB, hC220, hCk⟩ :=
    bufferAccessClose_spec hW (shape xs) xs.length hsize sB hBr
      (GeoBase.congr hgeo (fun x hx => fB x (by unfold BufferKept; omega)))
      (GeoUpTo.congr hbank (fun x h1 h2 => fB x (by unfold BufferKept; omega))) hbankcap
      P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb buf
      (buf + PackedCellProbe.packedReviewerCellWidth xs.length) hB119
      (by rw [fB 159 (by decide), h159]) (by rw [fB 160 (by decide), h160])
      (by rw [fB 161 (by decide), h161]) (by rw [fB 162 (by decide), h162])
      (by rw [fB 163 (by decide), h163]) (by rw [fB 164 (by decide), h164])
      (by rw [fB 115 (by decide), h115]) (by rw [fB 116 (by decide), h116])
      (by rw [fB 117 (by decide), h117]) (by rw [fB 118 (by decide), h118])
      (by rw [fB 135 (by decide), h135]) (by rw [fB 136 (by decide), h136])
      hBR hBext hPR hRL hLC hCF hFG (by omega) hA01 hA12 hA23 hA3m hmG (by omega) (by omega)
      (by rw [hBext, hlen]; omega)
  have fC : ∀ r, BufferKept r → sC.regs r = s.regs r := fun r hr => by rw [fCB r hr, fB r hr]
  have Epre : EmitsFrom buf sP sC (List.replicate (PackedCellProbe.packedReviewerCellWidth xs.length) 0 ++
      ((shape xs).bpCode.map bitToNat ++
        ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload (shape xs)).map bitToNat ++
          (canonicalRelativeRmmInteriorDirectory (shape xs)).payload.map bitToNat))) := by
    have h := EPB.trans EBC
    rw [List.append_assoc] at h
    exact h
  -- the payload as one list
  have hPmap : (PackedCellProbe.packedReviewerPayloadBits (shape xs)).map bitToNat =
      ((shape xs).bpCode.map bitToNat ++
        ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload (shape xs)).map bitToNat ++
          (canonicalRelativeRmmInteriorDirectory (shape xs)).payload.map bitToNat)) ++
        (tableBits (bpFringeChunkEntries (bpFringeChunkBits (2 * xs.length)))
            (bpFringeChunkEntryWidth (bpFringeChunkBits (2 * xs.length))) ++
          tableBits (bpChunkSelectEntries (bpFringeChunkBits (2 * xs.length)) false)
            (bpChunkSelectEntryWidth (bpFringeChunkBits (2 * xs.length)))).map bitToNat := by
    rw [canonicalReviewerPayload_eq_plan, ← liveAccessPayload_eq_segments, ← interiorPayload_eq_segments]
    simp only [fringeSegment, selectChunkSegment, List.map_append, List.append_assoc, hlen]
  have hsegs : ((PackedCellProbe.packedReviewerPayloadBits (shape xs)).map bitToNat).length + 2 ≤
      400000 * (xs.length + 1) := by
    have h := planPayload_length_add_two_le (shape xs)
    rw [← canonicalReviewerPayload_eq_plan, hsize] at h
    rw [List.length_map]; exact h
  rw [hPmap] at hsegs
  simp only [List.length_append, List.length_map] at hsegs
  -- microtables, header patch, paddings
  obtain ⟨s', kT, eT, hkT, hs'r, hext1, hext2, hcells, hbelow, fT, h220', h177', h178', hks⟩ :=
    bufferTail_spec hW xs.length (bpFringeChunkBits (2 * xs.length))
      (PackedCellProbe.packedReviewerCellWidth xs.length) (PackedWordRAM.wordWidth xs.length) buf
      (PackedCellProbe.longCount (shape xs)) rfl rfl rfl sC sP hCr
      (GeoUpTo.congr hbank (fun x h1 h2 => fC x (by unfold BufferKept; omega)))
      (by rw [fC 0 (by decide), hzero]) (by rw [fC 2 (by decide), hgeo.2.1])
      (by rw [fC 9 (by decide), hgeo.2.2.1]) (by rw [hC220, hB220]) hC177
      (by
        have h1 := PackedCellProbe.longCount_le_superSlots (shape xs)
        have h2 := PackedCellProbe.packedSuperSlots_le (shape xs).size
        rw [hsize] at h1 h2
        omega)
      _ hPe Epre (by simp only [List.length_append, List.length_map]; omega) (by omega)
  rw [← hPmap] at hext1 hext2 hcells
  have hTlen := bufferCells_length (shape xs)
  have hPL : ((PackedCellProbe.packedReviewerPayloadBits (shape xs)).map bitToNat).length =
      PackedCellProbe.packedReviewerPayloadLength xs.length (PackedCellProbe.longCount (shape xs))
        (PackedCellProbe.packedReviewerSparseCount (shape xs)) := by
    rw [List.length_map, PackedCellProbe.packedReviewerPayloadBits_length_eq, hsize]
  rw [hsize] at hTlen
  rw [hPL, ← hTlen] at hext1 hext2 hcells
  have hcell0 := bufferCells_getD (shape xs)
  rw [hsize] at hcell0
  refine ⟨s', k1 + (k2 + (kH + (kE + (kA + (kC + kT))))),
    EvalG.seq e1 (EvalG.seq e2 (EvalG.seq eH (EvalG.seq eE (EvalG.seq eA (EvalG.seq eC eT))))),
    by omega, hs'r, h220', ⟨hext1, ?_⟩, hext2, ?_, h177', by rw [h178', hC178], ?_, ?_⟩
  · intro i hi
    dsimp only
    rw [hcells i hi, hcell0 i]
  · intro a ha hP hA
    rw [hbelow a (by omega), hCmem a (by omega) hP hA, hBmem a ha]
  · intro r hr
    exact (fT r hr).trans (fC r hr)
  · rw [hks, hCk, hBk]


/-- **S6 buffer stage**, frame form: registers outside 4-28 and 100-228 are
unchanged (a weakening of `bufferStage_kept`). -/
theorem bufferStage_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (s : State) (hrun : s.status = .running)
    (hzero : s.regs 0 = 0) (hgeo : GeoBase xs.length s.regs)
    (hbank : GeoUpTo xs.length 39 s.regs)
    (hbankcap : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb : Nat)
    (h159 : s.regs 159 = P0) (h160 : s.regs 160 = R0) (h161 : s.regs 161 = L0)
    (h162 : s.regs 162 = C0) (h163 : s.regs 163 = F0) (h164 : s.regs 164 = G0)
    (h115 : s.regs 115 = A0) (h116 : s.regs 116 = A1) (h117 : s.regs 117 = A2)
    (h118 : s.regs 118 = A3) (h135 : s.regs 135 = Bm) (h136 : s.regs 136 = Gb)
    (hPR : P0 + xs.length + 1 ≤ R0)
    (hRL : R0 + (shape xs).bpCode.length / wordBits (shape xs).bpCode.length + 1 ≤ L0)
    (hLC : L0 + superSlotCount (shape xs).bpCode false ≤ C0)
    (hCF : C0 + superSlotCount (shape xs).bpCode false + 1 ≤ F0)
    (hFG : F0 + localSlotCount (shape xs).bpCode false ≤ G0)
    (hGe : G0 + localSlotCount (shape xs).bpCode false + 1 ≤ s.extent)
    (hA01 : A0 + geoBlocks xs.length + 1 ≤ A1) (hA12 : A1 + geoBlocks xs.length ≤ A2)
    (hA23 : A2 + geoBlocks xs.length ≤ A3) (hA3m : A3 + geoBlocks xs.length ≤ Bm)
    (hmG : Bm + SuccinctRank.machineWordBits (geoMacro xs.length) * geoBlocks xs.length ≤ Gb)
    (hGbe : Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ s.extent)
    (hcap : s.extent + 32 * (400000 * (xs.length + 1)) < 2 ^ W) :
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock leaf) bufferBlock)) s s' k ∧
      k ≤ 2000 * (400000 * (xs.length + 1)) ∧ s'.status = .running ∧
      s'.regs 220 = s.extent + 3 * (xs.length + 1) ∧
      ArrayAt s' (s.extent + 3 * (xs.length + 1))
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length
        (fun i => ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).getD i 0) ∧
      s'.extent ≤ s.extent + 3 * (xs.length + 1) +
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length + 1 ∧
      (∀ a, a < s.extent → (a < P0 ∨ G0 + localSlotCount (shape xs).bpCode false + 1 ≤ a) →
        (a < A0 ∨ Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ a) →
        s'.memory a = s.memory a) ∧
      s'.regs 177 = PackedCellProbe.longCount (shape xs) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits (shape xs).bpCode false)
        (localSlotCount (shape xs).bpCode false) ∧
      (∀ r, BufferFrame r → s'.regs r = s.regs r) ∧ s'.keys = s.keys := by
  obtain ⟨s', k, e, hk, hr, h220, harr, hext, hmem, h177, h178, hfr, hks⟩ :=
    bufferStage_kept hW xs Inp leaf hleaf s hrun hzero hgeo hbank hbankcap hinp hInp
      P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb h159 h160 h161 h162 h163 h164 h115 h116 h117 h118
      h135 h136 hPR hRL hLC hCF hFG hGe hA01 hA12 hA23 hA3m hmG hGbe hcap
  exact ⟨s', k, e, hk, hr, h220, harr, hext, hmem, h177, h178,
    fun r hr' => hfr r (by unfold BufferKept; omega), hks⟩
end RMQ.SuccinctFinal.PackedConstruction.Proof
