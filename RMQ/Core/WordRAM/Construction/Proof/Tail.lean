import RMQ.Core.WordRAM.Construction.Proof.Output

/-! # PRE-1 builder proofs: from the geometry bank to the output (stage S7)

Outside the builder firewall. `tailStage_spec` composes the arrays, the
Cartesian stack pass, the bit buffer and the output phase for an arbitrary leaf
meeting `KeySpec`: from a running state holding the geometry bank it reaches a
running state whose register 3 holds `outBase`, whose extent is
`outBase + (buildMemory xs).length`, and whose cells from `outBase` are exactly
`buildMemory xs`. The metadata envelope premise of the output phase is
discharged from `planPayload_length_add_two_le`; the capacity premises are
`2 ^ 32 * (2 n + 4) ^ 8 < 2 ^ W`, `extent + 64 * (400000 * (n + 1)) < 2 ^ W` and
`wordWidth n ≤ W`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

/-- The payload of the actual shape is within the payload envelope, in the
metadata bank's form. -/
theorem pay_le_of_shape (xs : List Int) :
    mv_pay xs.length (longCount (shape xs))
        (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
          (GenericSelect.localSlotCount (shape xs).bpCode false)) + 2 ≤
      400000 * (xs.length + 1) := by
  have hsize : (shape xs).size = xs.length := Cartesian.shape_size xs
  have h := planPayload_length_add_two_le (shape xs)
  rw [planPayload_length, hsize] at h
  have hsc := sc_eq_sparseCount (shape xs)
  rw [CartesianShape.bpCode_length, hsize] at hsc
  rw [← pay_eq, hsc]
  exact h

/-- The array sizes are within the payload envelope. -/
theorem arrays_le_of_pay (n lc c : Nat) (hpay : mv_pay n lc c + 2 ≤ 400000 * (n + 1)) :
    packedLocalSlots n ≤ mv_pay n lc c ∧
      (packedInteriorLayout n).offsetWidth * (packedInteriorLayout n).blockCount ≤ mv_pay n lc c ∧
      (packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount ≤
        mv_pay n lc c ∧
      packedRankBlockSlots n ≤ 2 * n + 1 ∧ packedSuperSlots n ≤ n := by
  obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how,
    hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
  have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + canonicalRelativeRmmInteriorRawPayloadOverhead n +
      bpFringeTableOverhead n + bpChunkSelectTableOverhead n := rfl
  have hloc : packedLocalSlots n ≤ mv_len7 n lc c :=
    Nat.le_mul_of_pos_right _ (SuccinctRank.machineWordBits_pos _)
  have howrw : (packedInteriorLayout n).offsetWidth ≤ (packedInteriorLayout n).relativeWidth := by
    show Nat.log2 ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1 ≤ 2 * (Nat.log2 (Nat.log2 n + 1) + 1) + 3
    have := log2_mul_self_le (Nat.log2 n + 1)
    omega
  have hq2 : (packedInteriorLayout n).offsetWidth * (packedInteriorLayout n).blockCount ≤
      mv_q2bits n lc c := by
    show _ ≤ (packedInteriorLayout n).blockCount * (packedInteriorLayout n).relativeWidth
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ howrw
  have hq6 : (packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount ≤
      mv_q6bits n lc c := Nat.le_mul_of_pos_right _ (SuccinctRank.machineWordBits_pos _)
  have hrbs : packedRankBlockSlots n ≤ 2 * n + 1 := by
    show 2 * n / packedRankWordSize n + 1 ≤ _
    have := Nat.div_le_self (2 * n) (packedRankWordSize n)
    omega
  exact ⟨by omega, by omega, by omega, hrbs, packedSuperSlots_le n⟩

set_option maxHeartbeats 1600000 in
/-- **Tail stage.** -/
theorem tailStage_spec {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop) (leaf : Block)
    (hleaf : KeySpec W xs Inp leaf) (s : State) (hrun : s.status = .running)
    (hfit : ∀ r, s.regs r < 2 ^ W) (hzero : s.regs 0 = 0) (hgeo : GeoBase xs.length s.regs)
    (hbank : GeoUpTo xs.length 39 s.regs) (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (hbankcap : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W)
    (hcap : s.extent + 64 * (400000 * (xs.length + 1)) < 2 ^ W)
    (hWW : wordWidth xs.length ≤ W) :
    ∃ s' k, SafeEval W (.seq arraysBlock (.seq (.seq stackArraysBlock (.seq (stackPassBlock leaf)
        bufferBlock)) outputBlock)) s s' k ∧
      k ≤ 2100 * (400000 * (xs.length + 1)) ∧ s'.status = .running ∧
      s.extent ≤ s'.regs 3 ∧ s'.regs 3 ≤ s.extent + 8 * (400000 * (xs.length + 1)) ∧
      s'.extent = s'.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        s'.memory (s'.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧ s'.keys = s.keys := by
  have hsize : (shape xs).size = xs.length := Cartesian.shape_size xs
  have hlen : (shape xs).bpCode.length = 2 * xs.length := by
    rw [CartesianShape.bpCode_length, hsize]
  have hcellsLen : ((densePad (wordWidth xs.length) (packedReviewerPaddedBits (shape xs))).map
      SuccinctSpace.bitToNat).length =
      mv_dcount xs.length (longCount (shape xs))
        (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
          (GenericSelect.localSlotCount (shape xs).bpCode false)) * wordWidth xs.length := by
    have hdc := dcount_eq_denseCount (shape xs)
    rw [hsize] at hdc
    rw [List.length_map, densePad_length _ _ (wordWidth_pos _), hdc]
  have hlenle : ((densePad (wordWidth xs.length) (packedReviewerPaddedBits (shape xs))).map
      SuccinctSpace.bitToNat).length ≤ 400576 * xs.length + 401726 := by
    have h := (planBuffer_le xs).2
    rw [List.length_map, densePad_length _ _ (wordWidth_pos _)]
    unfold denseCount
    rw [packedReviewerPaddedBits_length, hsize]
    exact h
  have hwords := outputWords_eq_buildMemory xs
  generalize hn : xs.length = n at *
  generalize hlc : longCount (shape xs) = lc at hcellsLen hlenle hwords
  generalize hc : RMQ.Succinct.rankPrefix true
    (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
    (GenericSelect.localSlotCount (shape xs).bpCode false) = c at hcellsLen hlenle hwords
  have hpay : mv_pay n lc c + 2 ≤ 400000 * (n + 1) := by
    have h := pay_le_of_shape xs
    rw [hn, hlc, hc] at h
    exact h
  obtain ⟨hloc, hPQ, hGM, hrbs, hsup⟩ := arrays_le_of_pay n lc c hpay
  have hBn : geoBlocks n ≤ n := Nat.div_le_self _ _
  -- arrays
  obtain ⟨q, kA, eA, hkA, hqr, EA, q159, q160, q161, q162, q163, q164, q115, q116, q117, q118,
      q135, q136, qext, qfr, qkr, qks⟩ :=
    arraysBlock_spec hW s hrun hzero hgeo.2.1 n (packedRankBlockSlots n) (packedSuperSlots n)
      (packedLocalSlots n) (geoBlocks n) (SuccinctRank.machineWordBits (geoMacro n))
      (SuccinctRank.machineWordBits (geoMacros n)) (geoMacros n) hgeo.1 (hbank 15 (by decide))
      (hbank 7 (by decide)) (hbank 8 (by decide)) hgeo.2.2.2.2.2.1 (hbank 20 (by decide))
      (hbank 21 (by decide)) hgeo.2.2.2.2.2.2.1 (by
        have e1 : SuccinctRank.machineWordBits (geoMacro n) * geoBlocks n =
          (packedInteriorLayout n).offsetWidth * (packedInteriorLayout n).blockCount := rfl
        have e2 : SuccinctRank.machineWordBits (geoMacros n) * geoMacros n =
          (packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount := rfl
        rw [e1, e2]
        omega)
  have qW : ∀ r : Nat, ¬ ArraysWritten r → q.regs r = s.regs r := qfr
  have nw : ∀ r : Nat, (r ≤ 9 ∨ (29 ≤ r ∧ r ≤ 99)) → ¬ ArraysWritten r := by
    intro r hr; unfold ArraysWritten; omega
  have hqext : q.extent = s.extent + ((n + 1) + (packedRankBlockSlots n + 1) +
      2 * (packedSuperSlots n + 1) + 2 * (packedLocalSlots n + 1) + 4 * (geoBlocks n + 1) +
      (SuccinctRank.machineWordBits (geoMacro n) * geoBlocks n + 1) +
      (SuccinctRank.machineWordBits (geoMacros n) * geoMacros n + 1)) := by
    rw [EA.1, List.length_replicate]
  have e1 : SuccinctRank.machineWordBits (geoMacro n) * geoBlocks n =
    (packedInteriorLayout n).offsetWidth * (packedInteriorLayout n).blockCount := rfl
  have e2 : SuccinctRank.machineWordBits (geoMacros n) * geoMacros n =
    (packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount := rfl
  have eB : geoBlocks n = (packedInteriorLayout n).blockCount := rfl
  rw [e1, e2, eB] at hqext
  have hfitq := SafeEval.regs_fit hW eA hfit
  -- buffer
  have hsup' : GenericSelect.superSlotCount (shape xs).bpCode false = packedSuperSlots n := by
    rw [superSlotCount_eq_packed, hsize]
  have hloc' : GenericSelect.localSlotCount (shape xs).bpCode false = packedLocalSlots n := by
    rw [localSlotCount_eq_packed, hsize]
  have hwb : (shape xs).bpCode.length / GenericSelect.wordBits (shape xs).bpCode.length ≤
      packedRankBlockSlots n := by
    rw [hlen]
    show 2 * n / SuccinctRank.machineWordBits (2 * n) ≤ 2 * n / SuccinctRank.machineWordBits (2 * n) + 1
    omega
  obtain ⟨b, kB, eB', hkB, hbr, hb220, hbarr, hbext, hbmem, hb177, hb178, hbfr, hbks⟩ :=
    bufferStage_kept hW xs Inp leaf hleaf q hqr (by rw [qW 0 (nw 0 (by omega)), hzero])
      (by rw [hn]; exact GeoBase.congr hgeo (fun x hx => qW x (nw x (by omega))))
      (by rw [hn]; exact GeoUpTo.congr hbank (fun x h1 h2 => qW x (nw x (by omega))))
      (by rw [hn]; exact hbankcap)
      (hInp s q hinp (fun a ha => EA.memory_below ha) (by rw [EA.1]; omega) qks)
      (fun u v hu hm he hk => hInp u v hu (fun a ha => hm a (by rw [EA.1] at *; omega)) he hk)
      _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (by (try rw [hn]); omega) (by (try rw [hn]); omega)
      (by rw [hsup']; omega) (by rw [hsup']; omega) (by rw [hloc']; omega) (by rw [hloc']; omega)
      (by (try rw [hn]); omega) (by (try rw [hn]); omega) (by (try rw [hn]); omega)
      (by (try rw [hn]); omega) (by (try rw [hn]); omega) (by (try rw [hn]); omega)
      (by (try rw [hn]); omega)
  rw [hn] at hb220 hbarr hbext
  rw [hlc] at hb177
  rw [hc] at hb178
  generalize hcells : (densePad (wordWidth n) (packedReviewerPaddedBits (shape xs))).map
    SuccinctSpace.bitToNat = cells at hbarr hbext hcellsLen hlenle hwords
  have hfitb := SafeEval.regs_fit hW eB' hfitq
  have bK : ∀ r : Nat, (r ≤ 3 ∨ r = 9 ∨ (29 ≤ r ∧ r ≤ 99)) → b.regs r = s.regs r := by
    intro r hr
    rw [hbfr r (by unfold BufferKept; omega), qW r (nw r (by omega))]
  have hbits : ∀ j, cells.getD j 0 ≤ 1 := by
    intro j
    rw [← hcells, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (densePad (wordWidth n) (packedReviewerPaddedBits (shape xs)))[j]? with
    | none => simp
    | some bit => cases bit <;> simp [SuccinctSpace.bitToNat]
  have hB3 : q.extent + 3 * (n + 1) + cells.length ≤ b.extent := by
    have := hbarr.1; omega
  obtain ⟨o, kO, eO, hkO, hor, ho3, EO, hoks⟩ :=
    outputStage_spec (n := n) (lc := lc) (c := c) hW b hbr hfitb
      (GeoBase.congr hgeo (fun x hx => bK x (by omega)))
      (GeoUpTo.congr hbank (fun x h1 h2 => bK x (by omega))) hb177 hb178
      (by rw [bK 0 (by omega), hzero]) (fun j => cells.getD j 0) _ hb220
      (fun j hj => by
        have := hbarr.2 j (by rw [hcellsLen]; exact hj)
        exact this)
      (fun j _ => hbits j) (by rw [← hcellsLen]; exact hbarr.1) hpay
      (by rw [hqext] at hbext; omega) hWW
  have hNW : mv_dcount n lc c * (7 * wordWidth n + 12) =
      7 * (mv_dcount n lc c * wordWidth n) + 12 * mv_dcount n lc c := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm (mv_dcount n lc c) 12]
  have hN3 : mv_dcount n lc c ≤ 3 * (400000 * (n + 1)) := by
    simpa only [metaVal_48] using metaVal_le n lc c hpay 48 (by decide)
  rw [hwords] at EO
  refine ⟨o, kA + (kB + kO), EvalG.seq eA (EvalG.seq eB' eO), ?_, hor, ?_, ?_, ?_, ?_, ?_,
    by rw [hoks, hbks, qks]⟩
  · rw [hn] at hkB
    rw [e1, e2, eB] at hkA
    omega
  · rw [ho3]; omega
  · rw [ho3, hqext] at *; omega
  · rw [EO.1, ho3]
  · intro i hi
    rw [ho3, EO.memory_at hi]
    simp [List.getD, List.getElem?_eq_getElem hi]
  · intro a ha
    rw [EO.memory_below (by omega), hbmem a (by rw [EA.1]; omega) (by left; rw [q159]; exact ha)
      (by left; omega), EA.memory_below ha]

end RMQ.SuccinctFinal.PackedConstruction.Proof
