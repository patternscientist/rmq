import RMQ.Core.WordRAM.Construction.Proof.Geometry
import RMQ.Core.WordRAM.Construction.Spec.Plan

/-! # PRE-1 builder proofs: stage S2 end-to-end table example

Outside the builder firewall. The first end-to-end table equality of the
builder: from a running state holding the input length in register 1 and the
two constants, the charged source fragment "interior geometry prelude, then a
sparse-level table" safely appends exactly the payload of the canonical
reference table `SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable
shape` (respectively the global one) as 0/1 cells, for every shape. The
geometry registers are identified with the fields of
`SuccinctClose.RelativeRmm.canonicalLayout shape` by `rfl`.

Premises of the form `_ < 2 ^ W` are word-capacity premises about the declared
width; stage S8 discharges them at `wordWidth n`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder SuccinctSpace SuccinctClose Cartesian

theorem geoMacro_layout (shape : CartesianShape) :
    geoMacro shape.size = (RelativeRmm.canonicalLayout shape).macroSize := rfl

theorem geoMacros_layout (shape : CartesianShape) :
    geoMacros shape.size = (RelativeRmm.canonicalLayout shape).macroSampleCount := rfl

theorem geoBase_layout (shape : CartesianShape) :
    geoBase shape.size = (RelativeRmm.canonicalLayout shape).blocksPerSuper := rfl

theorem geoBlocks_layout (shape : CartesianShape) :
    geoBlocks shape.size = (RelativeRmm.canonicalLayout shape).blockCount := rfl

theorem level_domain_facts {n W D : Nat} (hD2 : 2 ≤ D) (hDB : D ≤ (n + 2) * (n + 2))
    (hcap : (n + 2) * (n + 2) * ((n + 2) * (n + 2)) < 2 ^ W) :
    D + 1 < 2 ^ W ∧ bpSparseLevelWidth D < 2 ^ W ∧ D * (Nat.log2 D + 1) < 2 ^ W := by
  have hcapD : D * (Nat.log2 D + 1) < 2 ^ W := level_cap_of_le (by omega) hDB hcap
  have hl1 : 1 ≤ Nat.log2 D := (Nat.le_log2 (by omega)).mpr (by simpa using hD2)
  have h2D : D * 2 ≤ D * (Nat.log2 D + 1) := Nat.mul_le_mul_left _ (by omega)
  have hWpos : 0 < W := by
    rcases Nat.eq_zero_or_pos W with h | h
    · subst h
      have : 2 ≤ D * (Nat.log2 D + 1) := Nat.le_trans hD2 (Nat.le_mul_of_pos_right _ (by omega))
      have h1 : (2 : Nat) ^ 0 = 1 := rfl
      omega
    · exact h
  have hwlt : Nat.log2 (D * (Nat.log2 D + 1)) < W := log2_lt_width hWpos hcapD
  have hW2 : W < 2 ^ W := Nat.lt_two_pow_self
  refine ⟨by omega, ?_, hcapD⟩
  show Nat.log2 (D * (Nat.log2 D + 1)) + 1 < 2 ^ W
  omega

/-- **S2 end-to-end: local sparse-level table.** For every shape, from a running
state with `regs 1 = shape.size` and the constants in place, the charged
fragment `interiorGeometryBlock` then `levelTableBlock rLDOM rLWID` safely
appends exactly `(canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload`
as 0/1 cells. -/
theorem localLevelTable_emits_payload {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hn : s.regs 1 = shape.size)
    (hcap : (shape.size + 2) * (shape.size + 2) * ((shape.size + 2) * (shape.size + 2)) < 2 ^ W)
    (hext : s.extent + bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize *
      bpSparseLevelWidth (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <
        2 ^ W) :
    ∃ s' k, SafeEval W (.seq interiorGeometryBlock (levelTableBlock rLDOM rLWID)) s s' k ∧
      s'.status = .running ∧
      Emits s s' ((canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload.map
        bitToNat) := by
  obtain ⟨g, k1, hg, _, hgrun, _, _, _, _, hg34, _, hg36, _, hgmem, hgext, hgfr, _, _⟩ :=
    interiorGeometry_spec hW s shape.size hrun hone htwo hn hcap
  have hg2 : g.regs 2 = 1 := by rw [hgfr 2 (by omega) (by omega), hone]
  have hg9 : g.regs 9 = 2 := by rw [hgfr 9 (by omega) (by omega), htwo]
  have hmacro_le : geoMacro shape.size + 2 ≤ (shape.size + 2) * (shape.size + 2) := by
    have hb : geoBase shape.size ≤ shape.size + 1 := by
      simp [geoBase]; exact Nat.log2_le_self _
    have : geoMacro shape.size ≤ (shape.size + 1) * (shape.size + 1) := Nat.mul_le_mul hb hb
    have e : (shape.size + 2) * (shape.size + 2) =
        (shape.size + 1) * (shape.size + 1) + 2 * shape.size + 3 := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    omega
  obtain ⟨hD1, hwW, hcapD⟩ := level_domain_facts (n := shape.size) (W := W)
    (D := bpSparseLevelDomain (geoMacro shape.size)) (by simp [bpSparseLevelDomain])
    (by simp only [bpSparseLevelDomain]; exact hmacro_le) hcap
  obtain ⟨s', k2, ht, _, htrun, htemit, _, _, _⟩ :=
    levelTable_spec hW rLDOM rLWID (by decide) (by decide) (by decide) (by decide)
      g hgrun hg2 hg9
      (by simp only [operand_val_34]; rw [hg34]; simp [bpSparseLevelDomain])
      (by simp only [operand_val_34]; rw [hg34]; exact hD1)
      (by simp only [operand_val_36]; rw [hg36]; exact hwW)
      (by simp only [operand_val_34, operand_val_36]; rw [hg34, hg36, hgext]; exact hext)
      (by simp only [operand_val_34]; rw [hg34]; exact hcapD)
  refine ⟨s', k1 + k2, EvalG.seq hg ht, htrun, ?_⟩
  have hpay := Spec.FixedWidthNatTable.payload_eq_tableBits
    (canonicalRelativeRmmInteriorLocalLevelTable shape).table
  have := (Emits.of_eq hgext hgmem).trans htemit
  simp only [operand_val_34, operand_val_36, hg34, hg36, List.nil_append] at this
  rw [hpay]
  exact this

/-- **S2 end-to-end: global sparse-level table.** -/
theorem globalLevelTable_emits_payload {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape)
    (s : State) (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (hn : s.regs 1 = shape.size)
    (hcap : (shape.size + 2) * (shape.size + 2) * ((shape.size + 2) * (shape.size + 2)) < 2 ^ W)
    (hext : s.extent + bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount *
      bpSparseLevelWidth (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount) <
        2 ^ W) :
    ∃ s' k, SafeEval W (.seq interiorGeometryBlock (levelTableBlock rGDOM rGWID)) s s' k ∧
      s'.status = .running ∧
      Emits s s' ((canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload.map
        bitToNat) := by
  obtain ⟨g, k1, hg, _, hgrun, _, _, _, _, _, hg35, _, hg37, hgmem, hgext, hgfr, _, _⟩ :=
    interiorGeometry_spec hW s shape.size hrun hone htwo hn hcap
  have hg2 : g.regs 2 = 1 := by rw [hgfr 2 (by omega) (by omega), hone]
  have hg9 : g.regs 9 = 2 := by rw [hgfr 9 (by omega) (by omega), htwo]
  have hmacros_le : geoMacros shape.size + 2 ≤ (shape.size + 2) * (shape.size + 2) := by
    have h1 : geoMacros shape.size ≤ shape.size + 1 := by
      have := Nat.div_le_self (geoBlocks shape.size) (geoMacro shape.size)
      have := Nat.div_le_self shape.size (geoBase shape.size)
      simp only [geoMacros, geoBlocks] at *; omega
    have : shape.size + 3 ≤ (shape.size + 2) * (shape.size + 2) := by
      simp only [Nat.add_mul, Nat.mul_add]; omega
    omega
  obtain ⟨hD1, hwW, hcapD⟩ := level_domain_facts (n := shape.size) (W := W)
    (D := bpSparseLevelDomain (geoMacros shape.size)) (by simp [bpSparseLevelDomain])
    (by simp only [bpSparseLevelDomain]; exact hmacros_le) hcap
  obtain ⟨s', k2, ht, _, htrun, htemit, _, _, _⟩ :=
    levelTable_spec hW rGDOM rGWID (by decide) (by decide) (by decide) (by decide)
      g hgrun hg2 hg9
      (by simp only [operand_val_35]; rw [hg35]; simp [bpSparseLevelDomain])
      (by simp only [operand_val_35]; rw [hg35]; exact hD1)
      (by simp only [operand_val_37]; rw [hg37]; exact hwW)
      (by simp only [operand_val_35, operand_val_37]; rw [hg35, hg37, hgext]; exact hext)
      (by simp only [operand_val_35]; rw [hg35]; exact hcapD)
  refine ⟨s', k1 + k2, EvalG.seq hg ht, htrun, ?_⟩
  have hpay := Spec.FixedWidthNatTable.payload_eq_tableBits
    (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
  have := (Emits.of_eq hgext hgmem).trans htemit
  simp only [operand_val_35, operand_val_37, hg35, hg37, List.nil_append] at this
  rw [hpay]
  exact this

end RMQ.SuccinctFinal.PackedConstruction.Proof
