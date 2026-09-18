import RMQ.Core.WordRAM.Construction.Proof.AccessTables
import RMQ.Core.WordRAM.Construction.Proof.GeometryBank
import RMQ.Core.WordRAM.Construction.Spec.Envelope

/-! # PRE-1 builder proofs: the access half (stage S5)

Outside the builder firewall. The bank registers read in reference names, the
two numeric envelopes from the bank capacity, the three in-place passes reaching
an access state, and the composition `accessHalf_spec`: from the geometry bank
and a BP region with the six arrays laid out below it, `accessHalfBlock` appends
exactly `concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape`
as 0/1 cells, in at most `200 * (400000 * (n + 1))` transitions, and leaves the
long-flag and sparse-exception counts for the header (`lc_eq_longCount`,
`sc_eq_sparseCount`).
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect SuccinctSpace

/-! ## The bank registers in reference terms -/

open RMQ.SuccinctFinal.PackedCellProbe in
/-- The access half of the geometry bank, read in the reference names. -/
theorem accessRegs_of_bank (shape : CartesianShape) {r : Registers} (hbank : GeoUpTo shape.size 39 r) :
    r 38 = shape.bpCode.length ∧ r 39 = wordBits shape.bpCode.length ∧
    r 40 = superStride shape.bpCode.length ∧ r 42 = localStride shape.bpCode.length ∧
    r 43 = localSlotsPerSuper shape.bpCode.length ∧ r 44 = superLongSpan shape.bpCode.length ∧
    r 45 = superSlotCount shape.bpCode false ∧ r 46 = localSlotCount shape.bpCode false ∧
    r 47 = (sparseExceptionEffectiveFlagBits shape.bpCode false).length ∧
    r 48 = SuccinctRank.machineWordBits
      (SuccinctRank.machineWordBits shape.bpCode.length * SuccinctRank.machineWordBits shape.bpCode.length) ∧
    r 49 = sparseExceptionRelativeWidth shape.bpCode ∧
    r 50 = SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length ∧
    r 51 = SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length ∧
    r 52 = shape.bpCode.length / SuccinctRank.machineWordBits shape.bpCode.length /
      SuccinctRank.machineWordBits shape.bpCode.length + 1 ∧
    r 53 = shape.bpCode.length / SuccinctRank.machineWordBits shape.bpCode.length + 1 ∧
    r 54 = (longSuperFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length + 1 ∧
    r 55 = (sparseExceptionEffectiveFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length + 1 := by
  have hlen : shape.bpCode.length = 2 * shape.size := CartesianShape.bpCode_length shape
  have hsup := superSlotCount_eq_packed shape
  have hloc := localSlotCount_eq_packed shape
  have hlb := longFlagBits_length_eq_packed shape
  have hsb := sparseFlagBits_length_eq_packed shape
  have hlw := localFieldWidth_eq_packed shape
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen]; exact hbank 0 (by decide)
  · rw [hlen]; exact hbank 1 (by decide)
  · rw [hlen]; exact hbank 2 (by decide)
  · rw [hlen]; exact hbank 4 (by decide)
  · rw [hlen]; exact hbank 5 (by decide)
  · rw [hlen]; exact hbank 6 (by decide)
  · rw [hsup]; exact hbank 7 (by decide)
  · rw [hloc]; exact hbank 8 (by decide)
  · rw [hsb]; exact hbank 9 (by decide)
  · rw [hlen]; exact hbank 10 (by decide)
  · show r 49 = localFieldWidth shape.bpCode
    rw [hlw]; exact hbank 11 (by decide)
  · rw [hlb]; exact hbank 12 (by decide)
  · rw [hsb]; exact hbank 13 (by decide)
  · rw [hlen]; exact hbank 14 (by decide)
  · rw [hlen]; exact hbank 15 (by decide)
  · rw [hlb]; exact hbank 16 (by decide)
  · rw [hsb]; exact hbank 17 (by decide)

/-! ## Numeric envelopes from the bank capacity -/

theorem access_caps {W : Nat} (shape : CartesianShape)
    (hbankcap : 2 ^ 32 * (2 * shape.size + 4) ^ 8 < 2 ^ W) :
    (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W ∧ shape.bpCode.length + 1 < 2 ^ W := by
  have hlen : shape.bpCode.length = 2 * shape.size := CartesianShape.bpCode_length shape
  have hc := capB hbankcap
  have hB := powB_facts shape.size
  have hws : wordBits shape.bpCode.length ≤ (2 * shape.size + 4) ^ 1 := by
    have := machineWordBits_le_succ shape.bpCode.length
    show SuccinctRank.machineWordBits shape.bpCode.length ≤ _
    omega
  have hS : superStride shape.bpCode.length ≤ (2 * shape.size + 4) ^ 2 := mulB hws hws rfl
  have hsupn : superSlotCount shape.bpCode false ≤ shape.size := by
    rw [RMQ.SuccinctFinal.PackedCellProbe.superSlotCount_eq_packed]
    exact RMQ.SuccinctFinal.PackedCellProbe.packedSuperSlots_le _
  have hsup2 : superSlotCount shape.bpCode false + 2 ≤ (2 * shape.size + 4) ^ 1 := by omega
  have h3 : (superSlotCount shape.bpCode false + 2) * superStride shape.bpCode.length ≤
      (2 * shape.size + 4) ^ 3 := mulB hsup2 hS rfl
  have hls := localStride_le_superStride shape.bpCode.length
  have hsplit : (superSlotCount shape.bpCode false + 2) * superStride shape.bpCode.length =
      (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
        superStride shape.bpCode.length := Nat.succ_mul _ _
  constructor <;> omega

/-! ## The three passes -/

/-- Registers the access half never writes. -/
abbrev AccessHalfFrame (r : Nat) : Prop :=
  ¬ TableScratch r ∧ ¬ (26 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ r ≠ 130 ∧ ¬ (165 ≤ r ∧ r ≤ 189)

/-- **Occurrence and flag passes.** From the bank, the array bases and the BP
region, the three passes reach an access state without emitting, changing
memory only inside the arrays. -/
theorem accessPasses_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hgeo : GeoBase shape.size s.regs)
    (hbank : GeoUpTo shape.size 39 s.regs)
    (hbankcap : 2 ^ 32 * (2 * shape.size + 4) ^ 8 < 2 ^ W)
    (P0 R0 L0 C0 F0 G0 B : Nat) (h119 : s.regs 119 = B) (h159 : s.regs 159 = P0)
    (h160 : s.regs 160 = R0) (h161 : s.regs 161 = L0) (h162 : s.regs 162 = C0)
    (h163 : s.regs 163 = F0) (h164 : s.regs 164 = G0)
    (hR : Region s B shape.bpCode.length (bpCell shape)) (hBext : B + shape.bpCode.length ≤ s.extent)
    (hPR : P0 + shape.size + 1 ≤ R0)
    (hRL : R0 + shape.bpCode.length / wordBits shape.bpCode.length + 1 ≤ L0)
    (hLC : L0 + superSlotCount shape.bpCode false ≤ C0)
    (hCF : C0 + superSlotCount shape.bpCode false + 1 ≤ F0)
    (hFG : F0 + localSlotCount shape.bpCode false ≤ G0)
    (hGB : G0 + localSlotCount shape.bpCode false + 1 ≤ B)
    (hextW : s.extent < 2 ^ W) :
    ∃ t k, (∀ (rest : Block) (t' : State) (k' : Nat), SafeEval W rest t t' k' →
        SafeEval W (.seq posPassBlock (.seq longFlagsBlock (.seq sparseFlagsBlock rest))) s t' (k + k')) ∧
      k ≤ (shape.bpCode.length + 1) * 20 + 7 + (superSlotCount shape.bpCode false * 39 + 6) +
        (localSlotCount shape.bpCode false * 64 + 6) ∧
      AccessReady W shape P0 R0 L0 C0 F0 G0 t ∧ t.extent = s.extent ∧
      (∀ a, (a < P0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) → t.memory a = s.memory a) ∧
      t.regs 177 = RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false)
        (superSlotCount shape.bpCode false) ∧
      t.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r, AccessHalfFrame r → t.regs r = s.regs r) ∧ t.keys = s.keys := by
  obtain ⟨g1, g2, g9, _⟩ := hgeo
  obtain ⟨b38, b39, b40, b42, b43, b44, b45, b46, b47, b48, b49, b50, b51, b52, b53, b54, b55⟩ :=
    accessRegs_of_bank shape hbank
  obtain ⟨hcapS, hlenW1⟩ := access_caps shape hbankcap
  have hws := wordBits_pos shape.bpCode.length
  obtain ⟨Lq, hLq⟩ : ∃ x, shape.bpCode.length / wordBits shape.bpCode.length = x := ⟨_, rfl⟩
  have hRL' : R0 + Lq + 1 ≤ L0 := hLq ▸ hRL
  have hsupS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length =
      superSlotCount shape.bpCode false * superStride shape.bpCode.length + superStride shape.bpCode.length :=
    Nat.succ_mul _ _
  -- occurrence pass
  obtain ⟨s1, j1, e1, hj1, hr1, POS1, RW1, M1, F1, X1, K1⟩ :=
    posPass_spec hW shape s hrun g2 B P0 R0 _ h119 h159 h160 b39 b38 hws hR hPR (by omega) hBext hextW
  rw [hLq] at RW1 M1
  have s1get : ∀ r, r ≠ 108 → r ≠ 130 → ¬ (165 ≤ r ∧ r ≤ 170) → s1.regs r = s.regs r := F1
  -- long flags
  obtain ⟨s2, j2, e2, hj2, hr2, LF2, LFC2, M2, R177, F2, X2, K2⟩ :=
    longFlags_spec hW shape s1 hr1 (by rw [s1get 2 (by decide) (by decide) (by decide), g2]) P0 L0 C0
      (by rw [s1get 1 (by decide) (by decide) (by decide), g1])
      (by rw [s1get 159 (by decide) (by decide) (by decide), h159])
      (by rw [s1get 161 (by decide) (by decide) (by decide), h161])
      (by rw [s1get 162 (by decide) (by decide) (by decide), h162])
      (by rw [s1get 40 (by decide) (by decide) (by decide), b40])
      (by rw [s1get 44 (by decide) (by decide) (by decide), b44])
      (by rw [s1get 45 (by decide) (by decide) (by decide), b45])
      POS1 (by omega) hLC (by rw [X1]; omega) (by rw [X1]; exact hextW) hlenW1 (by omega)
  have s2get : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → ¬ (173 ≤ r ∧ r ≤ 184) → r ≠ 188 →
      r ≠ 189 → s2.regs r = s1.regs r := F2
  have s2s : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 130 → ¬ (165 ≤ r ∧ r ≤ 189) →
      s2.regs r = s.regs r := fun r a b c d => by
    rw [s2get r a b (by omega) (by omega) (by omega) (by omega), s1get r b c (by omega)]
  have hPOS2 : ∀ q, q ≤ shape.size → s2.memory (P0 + q) = some (position shape.bpCode false q) :=
    fun q hq => by rw [M2 _ (Or.inl (by omega))]; exact POS1 q hq
  -- sparse flags
  obtain ⟨t, j3, e3, hj3, hrt, SF3, SFC3, M3, R178, F3, X3, K3⟩ :=
    sparseFlags_spec hW shape s2 hr2 (by rw [s2s 2 (by decide) (by decide) (by decide) (by decide), g2])
      P0 L0 F0 G0
      (by rw [s2s 1 (by decide) (by decide) (by decide) (by decide), g1])
      (by rw [s2s 159 (by decide) (by decide) (by decide) (by decide), h159])
      (by rw [s2s 161 (by decide) (by decide) (by decide) (by decide), h161])
      (by rw [s2s 163 (by decide) (by decide) (by decide) (by decide), h163])
      (by rw [s2s 164 (by decide) (by decide) (by decide) (by decide), h164])
      (by rw [s2s 39 (by decide) (by decide) (by decide) (by decide), b39])
      (by rw [s2s 40 (by decide) (by decide) (by decide) (by decide), b40])
      (by rw [s2s 42 (by decide) (by decide) (by decide) (by decide), b42])
      (by rw [s2s 43 (by decide) (by decide) (by decide) (by decide), b43])
      (by rw [s2s 46 (by decide) (by decide) (by decide) (by decide), b46])
      hPOS2 LF2 (by omega) (by omega) hFG (by rw [X2, X1]; omega) (by rw [X2, X1]; exact hextW) hlenW1 hcapS
  have tget : ∀ r, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → r ≠ 175 → r ≠ 176 →
      ¬ (178 ≤ r ∧ r ≤ 189) → t.regs r = s2.regs r := F3
  have ts : ∀ r, AccessHalfFrame r → t.regs r = s.regs r := fun r ⟨_, a, b, c, d⟩ => by
    rw [tget r a b (by omega) (by omega) (by omega) (by omega), s2s r a b c d]
  have tb : ∀ r, 1 ≤ r → r ≤ 164 → r ≠ 108 → r ≠ 130 → ¬ (10 ≤ r ∧ r ≤ 16) → ¬ (26 ≤ r ∧ r ≤ 28) →
      t.regs r = s.regs r := fun r a b c d e f => ts r ⟨e, f, c, d, by omega⟩
  have text : t.extent = s.extent := by rw [X3, X2, X1]
  refine ⟨t, j1 + (j2 + j3), fun rest t' k' er => ?_, by omega, ?_, text, ?_, ?_, ?_, ts,
    by rw [K3, K2, K1]⟩
  · have := EvalG.seq e1 (EvalG.seq e2 (EvalG.seq e3 er))
    rwa [show j1 + (j2 + (j3 + k')) = j1 + (j2 + j3) + k' by omega] at this
  · exact {
      run := hrt
      r1 := by rw [tb 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g1]
      r2 := by rw [tb 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g2]
      r9 := by rw [tb 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g9]
      r39 := by rw [tb 39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b39]
      r40 := by rw [tb 40 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b40]
      r42 := by rw [tb 42 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b42]
      r43 := by rw [tb 43 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b43]
      r45 := by rw [tb 45 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b45]
      r46 := by rw [tb 46 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b46]
      r47 := by rw [tb 47 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b47]
      r48 := by rw [tb 48 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b48]
      r49 := by rw [tb 49 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b49]
      r50 := by rw [tb 50 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b50]
      r51 := by rw [tb 51 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b51]
      r52 := by rw [tb 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b52]
      r53 := by rw [tb 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b53]
      r54 := by rw [tb 54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b54]
      r55 := by rw [tb 55 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), b55]
      r159 := by rw [tb 159 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h159]
      r160 := by rw [tb 160 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h160]
      r161 := by rw [tb 161 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h161]
      r162 := by rw [tb 162 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h162]
      r163 := by rw [tb 163 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h163]
      r164 := by rw [tb 164 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h164]
      pos := fun q hq => by rw [M3 _ (Or.inl (by omega))]; exact hPOS2 q hq
      rw := fun j hj => by
        rw [hLq] at hj
        rw [M3 _ (Or.inl (by omega)), M2 _ (Or.inl (by omega))]; exact RW1 j hj
      lf := fun k hk => by rw [M3 _ (Or.inl (by omega))]; exact LF2 k hk
      lfc := fun k hk => by rw [M3 _ (Or.inl (by omega))]; exact LFC2 k hk
      sf := SF3
      sfc := SFC3
      lay1 := hPR
      lay2 := hRL
      lay3 := hLC
      lay4 := hCF
      lay5 := hFG
      lay6 := by rw [text]; omega
      capS := hcapS
      lenW := hlenW1 }
  · intro a ha
    rw [M3 _ (by omega), M2 _ (by omega), M1 _ (by omega)]
  · rw [tget 177 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact R177
  · exact R178

/-! ## Sources 14 and 18 from an access state -/

theorem accessTable14_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (longSuperRelativeEntries shape.bpCode false)
      (longSuperRelativeWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (forSlots rK rKGO rSUP longRelativeBodyBlock) u v k ∧
      k ≤ superSlotCount shape.bpCode false * 25 + 3 +
        34 * (tableBits (longSuperRelativeEntries shape.bpCode false) (longSuperRelativeWidth shape.bpCode)).length ∧
      v.status = .running ∧
      Emits u v ((tableBits (longSuperRelativeEntries shape.bpCode false)
        (longSuperRelativeWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have l1 := hA.lay1
  have l3 := hA.lay3
  have l4 := hA.lay4
  have l5 := hA.lay5
  have l6 := hA.lay6
  have lc := hA.capS
  obtain ⟨Lq, hLq⟩ : ∃ y, shape.bpCode.length / wordBits shape.bpCode.length = y := ⟨_, rfl⟩
  have l2 := hA.lay2
  rw [hLq] at l2
  obtain ⟨v, k, ev, hk, hr, hE, hfr, hkr, hks⟩ :=
    longRelative_spec hW shape u hA.run hA.r2 hA.r9 P0 L0 hA.r1 hA.r159 hA.r161 hA.r39 hA.r40 hA.r45
      hA.lf hA.pos (by omega) (by omega) hext (by omega) hA.lenW'
  exact ⟨v, k, ev, hk, hr, hE, fun r h => by
    obtain ⟨a, b, c, _, _⟩ := accessFrame_of_body h
    exact hfr r a b c, hkr, hks⟩

theorem accessTable18_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (sparseExceptionRelativeEntries shape.bpCode false)
      (sparseExceptionRelativeWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (forSlots rG rGGO rLOC sparseRelativeBodyBlock) u v k ∧
      k ≤ localSlotCount shape.bpCode false * 29 + 3 +
        34 * (tableBits (sparseExceptionRelativeEntries shape.bpCode false)
          (sparseExceptionRelativeWidth shape.bpCode)).length ∧
      v.status = .running ∧
      Emits u v ((tableBits (sparseExceptionRelativeEntries shape.bpCode false)
        (sparseExceptionRelativeWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have l1 := hA.lay1
  have l3 := hA.lay3
  have l4 := hA.lay4
  have l5 := hA.lay5
  have l6 := hA.lay6
  obtain ⟨Lq, hLq⟩ : ∃ y, shape.bpCode.length / wordBits shape.bpCode.length = y := ⟨_, rfl⟩
  have l2 := hA.lay2
  rw [hLq] at l2
  obtain ⟨v, k, ev, hk, hr, hE, hfr, hkr, hks⟩ :=
    sparseRelative_spec hW shape u hA.run hA.r2 hA.r9 P0 F0 hA.r1 hA.r159 hA.r163 hA.r40 hA.r42 hA.r43
      hA.r46 hA.r49 hA.sf hA.pos (by omega) (by omega) hext hA.capS hA.lenW'
  exact ⟨v, k, ev, hk, hr, hE, fun r h => by
    obtain ⟨a, _, _, b, c⟩ := accessFrame_of_body h
    exact hfr r a b c, hkr, hks⟩

/-! ## The access half -/

/-- The eighteen access sources, spelled out. -/
theorem accessSegments_eq (shape : CartesianShape) :
    accessSegments shape =
      [ tableBits (SuccinctRank.canonicalSuperRankEntries false shape.bpCode
          (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
          (SuccinctRank.machineWordBits shape.bpCode.length),
        tableBits (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
          (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
          (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
            SuccinctRank.machineWordBits shape.bpCode.length)),
        tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SuccinctRank.canonicalSuperRankEntries true (longSuperFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length),
        tableBits (SuccinctRank.canonicalBlockRankEntries true (longSuperFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length),
        longSuperFlagBits shape.bpCode false,
        tableBits (longSuperRelativeEntries shape.bpCode false) (longSuperRelativeWidth shape.bpCode),
        tableBits (SuccinctRank.canonicalSuperRankEntries true (sparseExceptionEffectiveFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length),
        tableBits (SuccinctRank.canonicalBlockRankEntries true (sparseExceptionEffectiveFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length),
        sparseExceptionEffectiveFlagBits shape.bpCode false,
        tableBits (sparseExceptionRelativeEntries shape.bpCode false) (sparseExceptionRelativeWidth shape.bpCode) ] :=
  rfl

/-- **S5 exit: the access half.** From the geometry bank, array bases laid out
below the BP region and a capacity margin, `accessHalfBlock` fills the
occurrence and flag arrays in place and then appends exactly the live access
payload of the reference, in linear cost. It also leaves the long-flag count
and the sparse-exception flag count in registers 177 and 178. -/
theorem accessHalf_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hgeo : GeoBase shape.size s.regs)
    (hbank : GeoUpTo shape.size 39 s.regs)
    (hbankcap : 2 ^ 32 * (2 * shape.size + 4) ^ 8 < 2 ^ W)
    (P0 R0 L0 C0 F0 G0 B : Nat) (h119 : s.regs 119 = B) (h159 : s.regs 159 = P0)
    (h160 : s.regs 160 = R0) (h161 : s.regs 161 = L0) (h162 : s.regs 162 = C0)
    (h163 : s.regs 163 = F0) (h164 : s.regs 164 = G0)
    (hR : Region s B shape.bpCode.length (bpCell shape)) (hBext : B + shape.bpCode.length ≤ s.extent)
    (hPR : P0 + shape.size + 1 ≤ R0)
    (hRL : R0 + shape.bpCode.length / wordBits shape.bpCode.length + 1 ≤ L0)
    (hLC : L0 + superSlotCount shape.bpCode false ≤ C0)
    (hCF : C0 + superSlotCount shape.bpCode false + 1 ≤ F0)
    (hFG : F0 + localSlotCount shape.bpCode false ≤ G0)
    (hGB : G0 + localSlotCount shape.bpCode false + 1 ≤ B)
    (hcap : s.extent + 16 * (400000 * (shape.size + 1)) < 2 ^ W) :
    ∃ t s' k, SafeEval W accessHalfBlock s s' k ∧ k ≤ 200 * (400000 * (shape.size + 1)) ∧
      s'.status = .running ∧ t.extent = s.extent ∧
      (∀ a, (a < P0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) → t.memory a = s.memory a) ∧
      Emits t s' ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).map
        SuccinctSpace.bitToNat) ∧
      s'.regs 177 = RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false)
        (superSlotCount shape.bpCode false) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r, AccessHalfFrame r → s'.regs r = s.regs r) ∧ s'.keys = s.keys := by
  have hlen : shape.bpCode.length = 2 * shape.size := CartesianShape.bpCode_length shape
  obtain ⟨t, k0, e0, hk0, A0, text, tmem, t177, t178, tfr, tkeys⟩ :=
    accessPasses_spec hW shape s hrun hgeo hbank hbankcap P0 R0 L0 C0 F0 G0 B h119 h159 h160 h161 h162
      h163 h164 hR hBext hPR hRL hLC hCF hFG hGB (by omega)
  have hsupn : superSlotCount shape.bpCode false ≤ shape.size := by
    rw [RMQ.SuccinctFinal.PackedCellProbe.superSlotCount_eq_packed]
    exact RMQ.SuccinctFinal.PackedCellProbe.packedSuperSlots_le _
  have hlocB := (selectSlotCounts_le shape).2
  have hlens := planPayload_length_add_two_le shape
  rw [accessSegments_eq] at hlens
  simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.append_nil] at hlens
  obtain ⟨u1, k1, e1, hk1, hr1, E1, fr1, kr1, ks1⟩ := accessTable1_spec hW t A0 (by omega)
  have x1 := E1.1
  rw [List.length_map] at x1
  have A1 := A0.step E1 hr1 fr1
  obtain ⟨u2, k2, e2, hk2, hr2, E2, fr2, kr2, ks2⟩ := accessTable2_spec hW u1 A1 (by omega)
  have x2 := E2.1
  rw [List.length_map] at x2
  have A2 := A1.step E2 hr2 fr2
  obtain ⟨u3, k3, e3, hk3, hr3, E3, fr3, kr3, ks3⟩ := accessTable3_spec hW u2 A2 (by omega)
  have x3 := E3.1
  rw [List.length_map] at x3
  have A3 := A2.step E3 hr3 fr3
  obtain ⟨u4, k4, e4, hk4, hr4, E4, fr4, kr4, ks4⟩ := accessTable4_spec hW u3 A3 (by omega)
  have x4 := E4.1
  rw [List.length_map] at x4
  have A4 := A3.step E4 hr4 fr4
  obtain ⟨u5, k5, e5, hk5, hr5, E5, fr5, kr5, ks5⟩ := accessTable5_spec hW u4 A4 (by omega)
  have x5 := E5.1
  rw [List.length_map] at x5
  have A5 := A4.step E5 hr5 fr5
  obtain ⟨u6, k6, e6, hk6, hr6, E6, fr6, kr6, ks6⟩ := accessTable6_spec hW u5 A5 (by omega)
  have x6 := E6.1
  rw [List.length_map] at x6
  have A6 := A5.step E6 hr6 fr6
  obtain ⟨u7, k7, e7, hk7, hr7, E7, fr7, kr7, ks7⟩ := accessTable7_spec hW u6 A6 (by omega)
  have x7 := E7.1
  rw [List.length_map] at x7
  have A7 := A6.step E7 hr7 fr7
  obtain ⟨u8, k8, e8, hk8, hr8, E8, fr8, kr8, ks8⟩ := accessTable8_spec hW u7 A7 (by omega)
  have x8 := E8.1
  rw [List.length_map] at x8
  have A8 := A7.step E8 hr8 fr8
  obtain ⟨u9, k9, e9, hk9, hr9, E9, fr9, kr9, ks9⟩ := accessTable9_spec hW u8 A8 (by omega)
  have x9 := E9.1
  rw [List.length_map] at x9
  have A9 := A8.step E9 hr9 fr9
  obtain ⟨u10, k10, e10, hk10, hr10, E10, fr10, kr10, ks10⟩ := accessTable10_spec hW u9 A9 (by omega)
  have x10 := E10.1
  rw [List.length_map] at x10
  have A10 := A9.step E10 hr10 fr10
  obtain ⟨u11, k11, e11, hk11, hr11, E11, fr11, kr11, ks11⟩ := accessTable11_spec hW u10 A10 (by omega)
  have x11 := E11.1
  rw [List.length_map] at x11
  have A11 := A10.step E11 hr11 fr11
  obtain ⟨u12, k12, e12, hk12, hr12, E12, fr12, kr12, ks12⟩ := accessTable12_spec hW u11 A11 (by omega)
  have x12 := E12.1
  rw [List.length_map] at x12
  have A12 := A11.step E12 hr12 fr12
  obtain ⟨u13, k13, e13, hk13, hr13, E13, fr13, kr13, ks13⟩ := accessTable13_spec hW u12 A12 (by omega)
  have x13 := E13.1
  rw [List.length_map] at x13
  have A13 := A12.step E13 hr13 fr13
  obtain ⟨u14, k14, e14, hk14, hr14, E14, fr14, kr14, ks14⟩ := accessTable14_spec hW u13 A13 (by omega)
  have x14 := E14.1
  rw [List.length_map] at x14
  have A14 := A13.step E14 hr14 fr14
  obtain ⟨u15, k15, e15, hk15, hr15, E15, fr15, kr15, ks15⟩ := accessTable15_spec hW u14 A14 (by omega)
  have x15 := E15.1
  rw [List.length_map] at x15
  have A15 := A14.step E15 hr15 fr15
  obtain ⟨u16, k16, e16, hk16, hr16, E16, fr16, kr16, ks16⟩ := accessTable16_spec hW u15 A15 (by omega)
  have x16 := E16.1
  rw [List.length_map] at x16
  have A16 := A15.step E16 hr16 fr16
  obtain ⟨u17, k17, e17, hk17, hr17, E17, fr17, kr17, ks17⟩ := accessTable17_spec hW u16 A16 (by omega)
  have x17 := E17.1
  rw [List.length_map] at x17
  have A17 := A16.step E17 hr17 fr17
  obtain ⟨u18, k18, e18, hk18, hr18, E18, fr18, kr18, ks18⟩ := accessTable18_spec hW u17 A17 (by omega)
  have ev := e0 _ _ _ (EvalG.seq e1 (EvalG.seq e2 (EvalG.seq e3 (EvalG.seq e4 (EvalG.seq e5 (EvalG.seq e6
    (EvalG.seq e7 (EvalG.seq e8 (EvalG.seq e9 (EvalG.seq e10 (EvalG.seq e11 (EvalG.seq e12 (EvalG.seq e13
    (EvalG.seq e14 (EvalG.seq e15 (EvalG.seq e16 (EvalG.seq e17 e18)))))))))))))))))
  have hE := E1.trans (E2.trans (E3.trans (E4.trans (E5.trans (E6.trans (E7.trans (E8.trans (E9.trans
    (E10.trans (E11.trans (E12.trans (E13.trans (E14.trans (E15.trans (E16.trans (E17.trans E18))))))))))))))))
  have hHF : ∀ r, AccessHalfFrame r → AccessFrame r := fun r ⟨a, b, c, _, d⟩ =>
    ⟨a, b, c, by omega, by omega⟩
  refine ⟨t, u18, _, ev, ?_, hr18, text, tmem, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · rw [liveAccessPayload_eq_segments, accessSegments_eq]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append]
    exact hE
  · have h177 : AccessFrame 177 := by decide
    rw [fr18 177 h177, fr17 177 h177, fr16 177 h177, fr15 177 h177, fr14 177 h177, fr13 177 h177,
      fr12 177 h177, fr11 177 h177, fr10 177 h177, fr9 177 h177, fr8 177 h177, fr7 177 h177, fr6 177 h177,
      fr5 177 h177, fr4 177 h177, fr3 177 h177, fr2 177 h177, fr1 177 h177]
    exact t177
  · have h178 : AccessFrame 178 := by decide
    rw [fr18 178 h178, fr17 178 h178, fr16 178 h178, fr15 178 h178, fr14 178 h178, fr13 178 h178,
      fr12 178 h178, fr11 178 h178, fr10 178 h178, fr9 178 h178, fr8 178 h178, fr7 178 h178, fr6 178 h178,
      fr5 178 h178, fr4 178 h178, fr3 178 h178, fr2 178 h178, fr1 178 h178]
    exact t178
  · intro r hr
    have h := hHF r hr
    rw [fr18 r h, fr17 r h, fr16 r h, fr15 r h, fr14 r h, fr13 r h, fr12 r h, fr11 r h, fr10 r h, fr9 r h,
      fr8 r h, fr7 r h, fr6 r h, fr5 r h, fr4 r h, fr3 r h, fr2 r h, fr1 r h]
    exact tfr r hr
  · rw [ks18, ks17, ks16, ks15, ks14, ks13, ks12, ks11, ks10, ks9, ks8, ks7, ks6, ks5, ks4, ks3, ks2, ks1,
      tkeys]

/-! ## The two counts -/

/-- The long-flag count left in register 177 is the header's long count. -/
theorem lc_eq_longCount (shape : CartesianShape) :
    RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) (superSlotCount shape.bpCode false) =
      RMQ.SuccinctFinal.PackedCellProbe.longCount shape := rfl

/-- The local stride times the sparse-exception count left in register 178 is the
sparse-relative word count. -/
theorem sc_eq_sparseCount (shape : CartesianShape) :
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) (localSlotCount shape.bpCode false) *
      localStride shape.bpCode.length = RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparseCount shape :=
  (sparseExceptionRelativeEntries_length _ _).symm

end RMQ.SuccinctFinal.PackedConstruction.Proof
