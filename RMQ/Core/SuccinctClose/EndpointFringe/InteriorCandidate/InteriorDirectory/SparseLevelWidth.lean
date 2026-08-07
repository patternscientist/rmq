import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory.Base

/-!
# Interior directory: charged sparse-level stored width

Part of `RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory`, which remains the module downstream code imports.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

/-! ### Charged sparse-level table: stored width against the machine word

The charged level/span table is read ONCE per two-span call, and that read is
one machine word only if the stored width fits one.  The four theorems below
settle the fit for EVERY shape, not for a sampled table of sizes.

The two `_of_macro_crossing` theorems carry the reachability hypothesis
`macroSize < blockCount`, which is exactly what the interior dispatcher
already derives before it can reach a cross-macro two-span call (see
`canonicalRelativeRmmInteriorRangeMinCosted_cost_le_...`, where `hcross` and
`hbound` produce `hmacro`).  The hypothesis is NOT a size threshold introduced
for convenience: at small shapes the fit genuinely fails (at `size = 4` the
stored width is 6 against a 4-bit machine word), and macro crossing is
precisely what is unreachable there.  The two unconditional theorems cover the
remaining branches, where the read is charged at the `cost_le_eight` rate and
the interior cap has ample headroom.
-/

/--
CORE WIDTH HELPER.  Any exponent dominating the packed product bounds the
stored width.  Every fit below feeds this one lemma.
-/
private theorem bpSparseLevelWidth_le_of_prod_lt_two_pow
    {domain m : Nat} (hpos : 0 < domain)
    (hprod : domain * (Nat.log2 domain + 1) < 2 ^ m) :
    bpSparseLevelWidth domain <= m := by
  have hprodPos : 0 < domain * (Nat.log2 domain + 1) :=
    Nat.mul_pos hpos (Nat.succ_pos _)
  simpa [bpSparseLevelWidth] using
    natLog2_succ_le_of_pos_lt_pow hprodPos hprod

/-- A domain below `2 ^ m` has stored width at most `m + m`. -/
private theorem bpSparseLevelWidth_le_two_mul_of_lt_two_pow
    {domain m : Nat} (hpos : 0 < domain) (hlt : domain < 2 ^ m) :
    bpSparseLevelWidth domain <= m + m := by
  have hpowPos : 0 < 2 ^ m := Nat.pow_pos (by omega : 0 < 2)
  have hlogLe : Nat.log2 domain + 1 <= m :=
    natLog2_succ_le_of_pos_lt_pow hpos hlt
  have hmLe : m <= 2 ^ m := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hprod : domain * (Nat.log2 domain + 1) < 2 ^ m * 2 ^ m :=
    Nat.mul_lt_mul_of_lt_of_le hlt (Nat.le_trans hlogLe hmLe) hpowPos
  exact bpSparseLevelWidth_le_of_prod_lt_two_pow hpos
    (by simpa [Nat.pow_add] using hprod)

/-- The canonical base never exceeds the physical machine word. -/
private theorem canonicalRelativeRmmBase_le_machine
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBase shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hmono :
      SuccinctRank.machineWordBits shape.size <=
        SuccinctRank.machineWordBits shape.bpCode.length :=
    SuccinctRank.machineWordBits_mono_le
      (by rw [Cartesian.CartesianShape.bpCode_length]; omega)
  simpa [canonicalBPRelativeSummaryBase, SuccinctRank.machineWordBits] using
    hmono

/-- Local domain `base*base + 2` sits below `2 ^ (base+base+1)`. -/
private theorem bpSparseLevelWidth_square_domain_le
    (base : Nat) (hbase : 0 < base) :
    bpSparseLevelWidth (bpSparseLevelDomain (base * base)) <=
      (base + base + 1) + (base + base + 1) := by
  have hD : bpSparseLevelDomain (base * base) = base * base + 2 := rfl
  have hb2 : base < 2 ^ base := Nat.lt_two_pow_self
  have hpowPos : 0 < 2 ^ base := Nat.pow_pos (by omega)
  have hsq : base * base < 2 ^ base * 2 ^ base :=
    Nat.mul_lt_mul_of_lt_of_le hb2 (Nat.le_of_lt hb2) hpowPos
  have hsq' : base * base < 2 ^ (base + base) := by
    simpa [Nat.pow_add] using hsq
  have htwo2 : 2 <= 2 ^ (base + base) := by
    have h : 2 ^ 1 <= 2 ^ (base + base) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa using h
  have hsucc : 2 ^ (base + base + 1) = 2 ^ (base + base) * 2 := by
    rw [Nat.pow_succ]
  have hlt : bpSparseLevelDomain (base * base) < 2 ^ (base + base + 1) := by
    rw [hD, hsucc]; omega
  have hpos : 0 < bpSparseLevelDomain (base * base) := by rw [hD]; omega
  exact bpSparseLevelWidth_le_two_mul_of_lt_two_pow hpos hlt

/-- UNCONDITIONAL FIT, local instance. -/
theorem bpSparseLevelLocalWidth_le_seven_machine
    (shape : Cartesian.CartesianShape) :
    bpSparseLevelWidth
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hmacroSize : (RelativeRmm.canonicalLayout shape).macroSize
      = canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape := rfl
  have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  have hw := canonicalRelativeRmmBase_le_machine shape
  have hwpos := SuccinctRank.machineWordBits_pos shape.bpCode.length
  rw [hmacroSize]
  have hmain := bpSparseLevelWidth_square_domain_le _ hbasePos
  omega

/-- UNCONDITIONAL FIT, global instance. -/
theorem bpSparseLevelGlobalWidth_le_seven_machine
    (shape : Cartesian.CartesianShape) :
    bpSparseLevelWidth
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length := by
  have hwpos := SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hself := SuccinctRank.self_lt_two_pow_machineWordBits shape.bpCode.length
  have hcode : shape.bpCode.length = 2 * shape.size :=
    Cartesian.CartesianShape.bpCode_length shape
  have hsizeLt :
      shape.size < 2 ^ SuccinctRank.machineWordBits shape.bpCode.length := by
    omega
  have hsample :
      (RelativeRmm.canonicalLayout shape).macroSampleCount <=
        shape.size + 1 := by
    have hblock : (RelativeRmm.canonicalLayout shape).blockCount <= shape.size :=
      Nat.div_le_self _ _
    have hdiv :
        (RelativeRmm.canonicalLayout shape).blockCount /
            (RelativeRmm.canonicalLayout shape).macroSize <=
          (RelativeRmm.canonicalLayout shape).blockCount :=
      Nat.div_le_self _ _
    have heq : (RelativeRmm.canonicalLayout shape).macroSampleCount =
        (RelativeRmm.canonicalLayout shape).blockCount /
          (RelativeRmm.canonicalLayout shape).macroSize + 1 := rfl
    omega
  have hstep :
      2 ^ (SuccinctRank.machineWordBits shape.bpCode.length + 2) =
        2 ^ SuccinctRank.machineWordBits shape.bpCode.length * 2 * 2 := by
    rw [Nat.pow_succ, Nat.pow_succ]
  have hD : bpSparseLevelDomain
      (RelativeRmm.canonicalLayout shape).macroSampleCount =
    (RelativeRmm.canonicalLayout shape).macroSampleCount + 2 := rfl
  have hlt :
      bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount <
        2 ^ (SuccinctRank.machineWordBits shape.bpCode.length + 2) := by
    rw [hD, hstep]; omega
  have hpos :
      0 < bpSparseLevelDomain
        (RelativeRmm.canonicalLayout shape).macroSampleCount := by
    rw [hD]; omega
  have hmain := bpSparseLevelWidth_le_two_mul_of_lt_two_pow hpos hlt
  omega


/-- Macro crossing forces a genuine cube of real block capacity. -/
private theorem canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape) < shape.size := by
  have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  have hmacroRaw : canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape <
        shape.size / canonicalBPRelativeSummaryBase shape := hmacro
  have hsucc : canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape + 1 <=
        shape.size / canonicalBPRelativeSummaryBase shape := by omega
  have hscaled : (canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape + 1) *
        canonicalBPRelativeSummaryBase shape <= shape.size :=
    (Nat.le_div_iff_mul_le hbasePos).mp hsucc
  have hstrict : (canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape) *
        canonicalBPRelativeSummaryBase shape <
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape + 1) *
        canonicalBPRelativeSummaryBase shape :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hbasePos
  exact Nat.lt_of_lt_of_le (by simpa [Nat.mul_assoc] using hstrict) hscaled

private theorem canonicalRelativeRmmSize_lt_two_pow_base
    (shape : Cartesian.CartesianShape) :
    shape.size < 2 ^ canonicalBPRelativeSummaryBase shape := by
  simpa [canonicalBPRelativeSummaryBase] using
    (Nat.lt_log2_self (n := shape.size))

private theorem canonicalRelativeRmmBase_ten_le_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    10 <= canonicalBPRelativeSummaryBase shape := by
  have hcube := canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing hmacro
  have hsize := canonicalRelativeRmmSize_lt_two_pow_base shape
  have hcubePow : canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape) <
      2 ^ canonicalBPRelativeSummaryBase shape := by omega
  by_cases hten : 10 <= canonicalBPRelativeSummaryBase shape
  · exact hten
  · exfalso
    have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by
      simp [canonicalBPRelativeSummaryBase]
    have hcases : canonicalBPRelativeSummaryBase shape = 1 ∨
        canonicalBPRelativeSummaryBase shape = 2 ∨
        canonicalBPRelativeSummaryBase shape = 3 ∨
        canonicalBPRelativeSummaryBase shape = 4 ∨
        canonicalBPRelativeSummaryBase shape = 5 ∨
        canonicalBPRelativeSummaryBase shape = 6 ∨
        canonicalBPRelativeSummaryBase shape = 7 ∨
        canonicalBPRelativeSummaryBase shape = 8 ∨
        canonicalBPRelativeSummaryBase shape = 9 := by omega
    rcases hcases with h | h | h | h | h | h | h | h | h <;>
      rw [h] at hcubePow <;> simp_all <;> omega

/-- TIGHT FIT ARITHMETIC, local: domain `base*base + 2` in one word. -/
private theorem bpSparseLevelWidth_square_domain_le_succ
    {base : Nat} (hbase : 10 <= base)
    (hcube : base * (base * base) < 2 ^ base) :
    bpSparseLevelWidth (bpSparseLevelDomain (base * base)) <= base + 1 := by
  have hD : bpSparseLevelDomain (base * base) = base * base + 2 := rfl
  have hbb : 100 <= base * base := by
    have h := Nat.mul_le_mul hbase hbase
    omega
  have hten : 10 * (base * base) <= base * (base * base) :=
    Nat.mul_le_mul_right (base * base) hbase
  have hpos : 0 < bpSparseLevelDomain (base * base) := by rw [hD]; omega
  have hDlt : bpSparseLevelDomain (base * base) < 2 ^ base := by rw [hD]; omega
  have hlog : Nat.log2 (bpSparseLevelDomain (base * base)) + 1 <= base :=
    natLog2_succ_le_of_pos_lt_pow hpos hDlt
  have hmul : bpSparseLevelDomain (base * base) *
      (Nat.log2 (bpSparseLevelDomain (base * base)) + 1) <=
      bpSparseLevelDomain (base * base) * base :=
    Nat.mul_le_mul_left _ hlog
  have hexp : bpSparseLevelDomain (base * base) * base =
      base * (base * base) + 2 * base := by
    rw [hD, Nat.add_mul, Nat.mul_assoc]
  have h2b : 2 * base <= base * (base * base) := by
    have h1 : 2 * base <= base * base :=
      Nat.mul_le_mul_right base (by omega : 2 <= base)
    have h2 : 1 * (base * base) <= base * (base * base) :=
      Nat.mul_le_mul_right (base * base) (by omega : 1 <= base)
    omega
  have hsucc : 2 ^ (base + 1) = 2 ^ base * 2 := by rw [Nat.pow_succ]
  have hprod : bpSparseLevelDomain (base * base) *
      (Nat.log2 (bpSparseLevelDomain (base * base)) + 1) < 2 ^ (base + 1) := by
    rw [hsucc]; omega
  exact bpSparseLevelWidth_le_of_prod_lt_two_pow hpos hprod

/-- TIGHT FIT ARITHMETIC, global: sample domain in one word. -/
private theorem bpSparseLevelWidth_sample_domain_le_succ
    {base x size : Nat} (hbase : 10 <= base)
    (hcube : base * (base * base) < 2 ^ base)
    (hsize : size < 2 ^ base)
    (hbx : base * x <= size) :
    bpSparseLevelWidth (bpSparseLevelDomain (x + 1)) <= base + 1 := by
  have hD : bpSparseLevelDomain (x + 1) = x + 3 := rfl
  have hbb : 100 <= base * base := by
    have h := Nat.mul_le_mul hbase hbase
    omega
  have hten : 10 * (base * base) <= base * (base * base) :=
    Nat.mul_le_mul_right (base * base) hbase
  have h10x : 10 * x <= base * x := Nat.mul_le_mul_right x hbase
  have hpos : 0 < bpSparseLevelDomain (x + 1) := by rw [hD]; omega
  have hDlt : bpSparseLevelDomain (x + 1) < 2 ^ base := by rw [hD]; omega
  have hlog : Nat.log2 (bpSparseLevelDomain (x + 1)) + 1 <= base :=
    natLog2_succ_le_of_pos_lt_pow hpos hDlt
  have hmul : bpSparseLevelDomain (x + 1) *
      (Nat.log2 (bpSparseLevelDomain (x + 1)) + 1) <=
      bpSparseLevelDomain (x + 1) * base :=
    Nat.mul_le_mul_left _ hlog
  have hexp : bpSparseLevelDomain (x + 1) * base = x * base + 3 * base := by
    rw [hD, Nat.add_mul]
  have hcomm : x * base = base * x := Nat.mul_comm x base
  have h3b : 3 * base <= base * (base * base) := by
    have h1 : 3 * base <= (base * base) * base :=
      Nat.mul_le_mul_right base (by omega : 3 <= base * base)
    have h2 : (base * base) * base = base * (base * base) := by
      rw [Nat.mul_assoc]
    omega
  have hsucc : 2 ^ (base + 1) = 2 ^ base * 2 := by rw [Nat.pow_succ]
  have hprod : bpSparseLevelDomain (x + 1) *
      (Nat.log2 (bpSparseLevelDomain (x + 1)) + 1) < 2 ^ (base + 1) := by
    rw [hsucc]; omega
  exact bpSparseLevelWidth_le_of_prod_lt_two_pow hpos hprod


/-- ALL-SIZE FIT, local instance, under the route's own macro-crossing guard. -/
theorem bpSparseLevelLocalWidth_le_machine_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    bpSparseLevelWidth
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hmacroSize : (RelativeRmm.canonicalLayout shape).macroSize
      = canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape := rfl
  have hten := canonicalRelativeRmmBase_ten_le_of_macro_crossing hmacro
  have hcube := canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing hmacro
  have hsizePow := canonicalRelativeRmmSize_lt_two_pow_base shape
  have hcubePow : canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape) <
      2 ^ canonicalBPRelativeSummaryBase shape := by omega
  have hsizePos : 0 < shape.size := by omega
  have hmachine := canonicalRelativeRmmBase_succ_le_machine_of_size_pos (shape := shape) hsizePos
  rw [hmacroSize]
  exact Nat.le_trans
    (bpSparseLevelWidth_square_domain_le_succ hten hcubePow) hmachine

/-- ALL-SIZE FIT, global instance, under the route's own macro-crossing guard. -/
theorem bpSparseLevelGlobalWidth_le_machine_of_macro_crossing
    {shape : Cartesian.CartesianShape}
    (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount) :
    bpSparseLevelWidth
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hten := canonicalRelativeRmmBase_ten_le_of_macro_crossing hmacro
  have hcube := canonicalRelativeRmmBase_cube_lt_size_of_macro_crossing hmacro
  have hsizePow := canonicalRelativeRmmSize_lt_two_pow_base shape
  have hcubePow : canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape) <
      2 ^ canonicalBPRelativeSummaryBase shape := by omega
  have hsizePos : 0 < shape.size := by omega
  have hmachine := canonicalRelativeRmmBase_succ_le_machine_of_size_pos (shape := shape) hsizePos
  have hsample : (RelativeRmm.canonicalLayout shape).macroSampleCount =
      shape.size / (canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape)) + 1 := by
    show shape.size / canonicalBPRelativeSummaryBase shape /
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape) + 1 = _
    rw [Nat.div_div_eq_div_mul]
  have hbasePos : 0 < canonicalBPRelativeSummaryBase shape := by omega
  have hsqPos : 0 < canonicalBPRelativeSummaryBase shape *
      canonicalBPRelativeSummaryBase shape := Nat.mul_pos hbasePos hbasePos
  have hNle : canonicalBPRelativeSummaryBase shape <=
      canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape) :=
    Nat.le_mul_of_pos_right _ hsqPos
  have hNdiv := Nat.mul_div_le shape.size
    (canonicalBPRelativeSummaryBase shape *
      (canonicalBPRelativeSummaryBase shape *
        canonicalBPRelativeSummaryBase shape))
  have hbx : canonicalBPRelativeSummaryBase shape *
      (shape.size / (canonicalBPRelativeSummaryBase shape *
        (canonicalBPRelativeSummaryBase shape *
          canonicalBPRelativeSummaryBase shape))) <= shape.size :=
    Nat.le_trans (Nat.mul_le_mul_right _ hNle) hNdiv
  rw [hsample]
  exact Nat.le_trans
    (bpSparseLevelWidth_sample_domain_le_succ hten hcubePow hsizePow hbx)
    hmachine

theorem canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
    {entries : List Nat} {width : Nat}
    {shape : Cartesian.CartesianShape}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <=
      7 * SuccinctRank.machineWordBits shape.bpCode.length)
    (i : Nat) :
    (canonicalRelativeRmmMachineReadNatCosted shape table i).cost <= 8 := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  have hwordSize : 0 < wordSize :=
    SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hdiv : width / wordSize <= 7 := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm, wordSize] using hwidth
  unfold canonicalRelativeRmmMachineReadNatCosted
  unfold SuccinctSpace.FixedWidthNatTable.machineReadCosted
  rw [SuccinctSpace.FixedWidthNatTable.machineReadCostedWithStore_cost]
  by_cases hvalid : i < entries.length
  · rw [if_pos hvalid]
    change
      (SuccinctSpace.fixedWidthNatTableMachineFootprint width wordSize i).length <= 8
    simp [SuccinctSpace.fixedWidthNatTableMachineFootprint,
      SuccinctSpace.fixedWidthNatTableMachineChunkCount]
    split <;> omega
  · rw [if_neg hvalid]
    omega

theorem costed_bind_cost_le
    {α β : Type} (x : Costed α) (f : α -> Costed β)
    {a b : Nat} (hx : x.cost <= a)
    (hf : forall value, (f value).cost <= b) :
    (Costed.bind x f).cost <= a + b := by
  exact Nat.add_le_add hx (hf x.value)

theorem canonicalRelativeRmmMachineSummaryCosted_cost_le_thirty_two
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost <= 32 := by
  let baselineRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).baselineTable
      (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  let minRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).minRelTable block
  let maxRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).maxRelTable block
  let argRead :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmSummaryTable shape).argOffsetTable block
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        7 * SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
    have hpos := SuccinctRank.machineWordBits_pos shape.bpCode.length
    omega
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_seven_machine shape
  have hb : baselineRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).baselineTable hsuper
      (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin : minRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).minRelTable hrelative block
  have hmax : maxRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelative block
  have harg : argRead.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelative block
  have h3 (baseline? minRel? maxRel? : Option Nat) :
      (Costed.map
        (fun argOffset? =>
          match baseline?, minRel?, maxRel?, argOffset? with
          | some baseline, some minRel, some maxRel, some argOffset =>
              some (baseline, minRel, maxRel, argOffset)
          | _, _, _, _ => none) argRead).cost <= 8 := by
    simpa [Costed.map] using harg
  have h2 (baseline? minRel? : Option Nat) :
      (Costed.bind maxRead fun maxRel? =>
        Costed.map
          (fun argOffset? =>
            match baseline?, minRel?, maxRel?, argOffset? with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) argRead).cost <= 16 := by
    exact costed_bind_cost_le _ _ hmax (fun maxRel? => h3 _ _ maxRel?)
  have h1 (baseline? : Option Nat) :
      (Costed.bind minRead fun minRel? =>
        Costed.bind maxRead fun maxRel? =>
          Costed.map
            (fun argOffset? =>
              match baseline?, minRel?, maxRel?, argOffset? with
              | some baseline, some minRel, some maxRel, some argOffset =>
                  some (baseline, minRel, maxRel, argOffset)
              | _, _, _, _ => none) argRead).cost <= 24 := by
    exact costed_bind_cost_le _ _ hmin (fun minRel? => h2 _ minRel?)
  have hall :=
    costed_bind_cost_le baselineRead
      (fun baseline? =>
        Costed.bind minRead fun minRel? =>
          Costed.bind maxRead fun maxRel? =>
            Costed.map
              (fun argOffset? =>
                match baseline?, minRel?, maxRel?, argOffset? with
                | some baseline, some minRel, some maxRel, some argOffset =>
                    some (baseline, minRel, maxRel, argOffset)
                | _, _, _, _ => none) argRead)
      hb h1
  simpa [canonicalRelativeRmmMachineSummaryCosted, baselineRead,
    minRead, maxRead, argRead] using hall

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_le_thirty_two
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost <= 32 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_le_thirty_two shape block

theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_forty
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost <= 40 := by
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalTable shape).table
      (bpLocalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount
        macroIdx localStart level)
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorLocalTable shape).table
      (canonicalRelativeRmmOffsetWidth_le_seven_machine shape)
      (bpLocalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount
        macroIdx localStart level)
  have htail : forall offset?,
      (match offset? with
      | some offset =>
          canonicalRelativeRmmMachineMinCandidateCosted shape
            (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none).cost <= 32 := by
    intro offset?
    cases offset? with
    | none => simp [Costed.pure]
    | some offset =>
        exact
          canonicalRelativeRmmMachineMinCandidateCosted_cost_le_thirty_two
            shape
            (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
  have hall := costed_bind_cost_le read
    (fun offset? =>
      match offset? with
      | some offset =>
          canonicalRelativeRmmMachineMinCandidateCosted shape
            (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalSpanCandidateCosted, read] using hall

theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_forty
    (shape : Cartesian.CartesianShape)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost <= 40 := by
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        macroStart level)
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (canonicalRelativeRmmBlockWidth_le_seven_machine shape)
      (bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        macroStart level)
  have htail : forall block?,
      (match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none).cost <= 32 := by
    intro block?
    cases block? with
    | none => simp [Costed.pure]
    | some block =>
        exact
          canonicalRelativeRmmMachineMinCandidateCosted_cost_le_thirty_two
            shape block
  have hall := costed_bind_cost_le read
    (fun block? =>
      match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineGlobalSpanCandidateCosted, read] using hall

/--
Generic all-size cap.  The charged level read is bounded unconditionally at the
`cost_le_eight` rate, via `bpSparseLevelLocalWidth_le_seven_machine`: no branch
guard is available here, so no `hmacro` fit may be assumed.
-/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
    (shape : Cartesian.CartesianShape)
    (macroIdx localStart count : Nat) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart count).cost <= 88 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table count
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      (bpSparseLevelLocalWidth_le_seven_machine shape) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 80 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_forty
            shape macroIdx localStart (cell / domain))
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_forty
                shape macroIdx (localStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted, read, domain]
    using hall

/-- Global twin of the generic all-size two-span cap. -/
theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eighty_eight
    (shape : Cartesian.CartesianShape)
    (macroStart count : Nat) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      macroStart count).cost <= 88 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table count
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      (bpSparseLevelGlobalWidth_le_seven_machine shape) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 80 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_forty
            shape macroStart (cell / domain))
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_forty
                shape (macroStart + count - cell % domain) (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted, read, domain]
    using hall

theorem canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted shape
      macroStart localStart rightCount).cost <= 176 := by
  let left :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let right :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      (macroStart + 1) 0 rightCount
  have hleft : left.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  have hright : right.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1) 0 rightCount
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun right? => bpCandidateMerge? left? right?)
      right)
    hleft (fun _ => by simpa [Costed.map] using hright)
  simpa [canonicalRelativeRmmMachineAdjacentMacroCandidateCosted,
    left, right] using hall

theorem canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted shape
      macroStart localStart middleMacroCount).cost <= 176 := by
  let left :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      (macroStart + 1) middleMacroCount
  have hleft : left.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  have hmiddle : middle.cost <= 88 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1) middleMacroCount
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun middle? => bpCandidateMerge? left? middle?)
      middle)
    hleft (fun _ => by simpa [Costed.map] using hmiddle)
  simpa [canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted,
    left, middle] using hall

theorem canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (canonicalRelativeRmmMachineCrossMacroCandidateCosted shape
      macroStart localStart middleMacroCount rightCount).cost <= 264 := by
  let left :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      (macroStart + 1) middleMacroCount
  let right :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      (macroStart + 1 + middleMacroCount) 0 rightCount
  have hleft : left.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape macroStart localStart
      ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  have hmiddle : middle.cost <= 88 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1) middleMacroCount
  have hright : right.cost <= 88 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
      shape (macroStart + 1 + middleMacroCount) 0 rightCount
  have htail : forall left?,
      (Costed.bind middle fun middle? =>
        Costed.map (fun right? => bpCandidateMerge3? left? middle? right?)
          right).cost <= 176 := by
    intro left?
    exact costed_bind_cost_le _ _ hmiddle
      (fun _ => by simpa [Costed.map] using hright)
  have hall := costed_bind_cost_le left
    (fun left? =>
      Costed.bind middle fun middle? =>
        Costed.map (fun right? => bpCandidateMerge3? left? middle? right?)
          right)
    hleft htail
  simpa [canonicalRelativeRmmMachineCrossMacroCandidateCosted,
    left, middle, right] using hall

theorem canonicalRelativeRmmInteriorRangeMinCosted_cost_le
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).cost <=
      canonicalRelativeRmmInteriorQueryCost := by
  unfold canonicalRelativeRmmInteriorRangeMinCosted
  by_cases hcount : count = 0
  · simp [hcount, canonicalRelativeRmmInteriorQueryCost, Costed.pure]
  · simp only [hcount, if_false]
    by_cases hwithin :
        count <=
          (RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    · simp only [hwithin, if_true]
      exact Nat.le_trans
        (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eighty_eight
          shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
          (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
          count) (by simp [canonicalRelativeRmmInteriorQueryCost])
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize = 0
      · simp only [hmiddle, if_true]
        exact Nat.le_trans
          (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le
            shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize))
          (by simp [canonicalRelativeRmmInteriorQueryCost])
      · simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize = 0
        · simp only [hright, if_true]
          exact Nat.le_trans
            (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le
              shape
              (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize))
            (by simp [canonicalRelativeRmmInteriorQueryCost])
        · simp only [hright, if_false]
          exact
            canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le
              shape
              (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize)
              ((count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize)

/-- Exact charged-read decomposition of one summary-cell execution. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_eq
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost =
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).baselineTable
        (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)).cost +
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).minRelTable block).cost +
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).maxRelTable block).cost +
      (canonicalRelativeRmmMachineReadNatCosted shape
        (canonicalRelativeRmmSummaryTable shape).argOffsetTable block).cost := by
  simp [canonicalRelativeRmmMachineSummaryCosted, Costed.bind, Costed.map,
    Nat.add_assoc]

/-- A canonical summary costs one baseline word plus three two-word fields. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_le_seven_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost <= 7 := by
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_lt_two_machine_of_size_ge_four
      (shape := shape) hsize
  have hb := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).baselineTable hsuper
    (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin := canonicalRelativeRmmMachineReadNatCosted_cost_le_two
    (canonicalRelativeRmmSummaryTable shape).minRelTable hrelative block
  have hmax := canonicalRelativeRmmMachineReadNatCosted_cost_le_two
    (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelative block
  have harg := canonicalRelativeRmmMachineReadNatCosted_cost_le_two
    (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelative block
  rw [canonicalRelativeRmmMachineSummaryCosted_cost_eq]
  omega

/-- In a genuine macro-crossing layout all four summary fields are one word. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_le_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost <= 4 := by
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacro
  have hb := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).baselineTable hsuper
    (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).minRelTable hrelative block
  have hmax := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelative block
  have harg := canonicalRelativeRmmMachineReadNatCosted_cost_le_one
    (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelative block
  rw [canonicalRelativeRmmMachineSummaryCosted_cost_eq]
  omega

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_le_seven_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost <= 7 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_le_seven_of_size_ge_four
      shape hsize block

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_le_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost <= 4 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_le_four_of_macro_crossing
      shape hmacro block

theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_nine_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost <= 9 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalTable shape).table
    (bpLocalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSize
      (RelativeRmm.canonicalLayout shape).levelCount
      macroIdx localStart level)
  have hoffset :
      (RelativeRmm.canonicalLayout shape).offsetWidth <
        2 * SuccinctRank.machineWordBits shape.bpCode.length :=
    Nat.lt_of_le_of_lt (canonicalRelativeRmmOffsetWidth_le_relativeWidth shape)
      (canonicalRelativeRmmRelativeWidth_lt_two_machine_of_size_ge_four
        (shape := shape) hsize)
  have hread : read.cost <= 2 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_two
      (canonicalRelativeRmmInteriorLocalTable shape).table hoffset _
  have htail : forall offset?,
      (match offset? with
      | some offset => canonicalRelativeRmmMachineMinCandidateCosted shape
          (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none).cost <= 7 := by
    intro offset?
    cases offset? with
    | none => simp [Costed.pure]
    | some offset =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_seven_of_size_ge_four
          shape hsize _
  simpa [canonicalRelativeRmmMachineLocalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_eight_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost <= 8 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalTable shape).table
    (bpGlobalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSampleCount macroStart level)
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (canonicalRelativeRmmBlockWidth_le_machine shape) _
  have htail : forall block?,
      (match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none).cost <= 7 := by
    intro block?
    cases block? with
    | none => simp [Costed.pure]
    | some block =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_seven_of_size_ge_four
          shape hsize block
  simpa [canonicalRelativeRmmMachineGlobalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_five_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart level : Nat) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost <= 5 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalTable shape).table
    (bpLocalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSize
      (RelativeRmm.canonicalLayout shape).levelCount
      macroIdx localStart level)
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacro
  have hoffset := Nat.le_trans
    (canonicalRelativeRmmOffsetWidth_le_relativeWidth shape) hrelative
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorLocalTable shape).table hoffset _
  have htail : forall offset?,
      (match offset? with
      | some offset => canonicalRelativeRmmMachineMinCandidateCosted shape
          (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize + offset)
      | none => Costed.pure none).cost <= 4 := by
    intro offset?
    cases offset? with
    | none => simp [Costed.pure]
    | some offset =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_four_of_macro_crossing
          shape hmacro _
  simpa [canonicalRelativeRmmMachineLocalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_five_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart level : Nat) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost <= 5 := by
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalTable shape).table
    (bpGlobalSparseCellSlot
      (RelativeRmm.canonicalLayout shape).macroSampleCount macroStart level)
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      (canonicalRelativeRmmBlockWidth_le_machine shape) _
  have htail : forall block?,
      (match block? with
      | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
      | none => Costed.pure none).cost <= 4 := by
    intro block?
    cases block? with
    | none => simp [Costed.pure]
    | some block =>
        exact canonicalRelativeRmmMachineMinCandidateCosted_cost_le_four_of_macro_crossing
          shape hmacro block
  simpa [canonicalRelativeRmmMachineGlobalSpanCandidateCosted, read] using
    costed_bind_cost_le read _ hread htail

/-- Every summary field is a positive one-word field under macro crossing. -/
theorem canonicalRelativeRmmMachineSummaryCosted_cost_eq_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineSummaryCosted shape block).cost = 4 := by
  have hsuperPos :
      0 < (RelativeRmm.canonicalLayout shape).superWidth shape := by
    exact SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hrelativePos :
      0 < (RelativeRmm.canonicalLayout shape).relativeWidth :=
    (RelativeRmm.canonicalLayout_valid shape).relativeWidth_pos
  have hsuper :
      (RelativeRmm.canonicalLayout shape).superWidth shape <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
    simp [RelativeRmm.Layout.superWidth]
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacro
  have hb := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).baselineTable hsuperPos hsuper
    (block / (RelativeRmm.canonicalLayout shape).blocksPerSuper)
  have hmin := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).minRelTable hrelativePos hrelative
    block
  have hmax := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).maxRelTable hrelativePos hrelative
    block
  have harg := canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
    (canonicalRelativeRmmSummaryTable shape).argOffsetTable hrelativePos
    hrelative block
  rw [canonicalRelativeRmmMachineSummaryCosted_cost_eq, hb, hmin, hmax, harg]

theorem canonicalRelativeRmmMachineMinCandidateCosted_cost_eq_four_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (block : Nat) :
    (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost = 4 := by
  simpa [canonicalRelativeRmmMachineMinCandidateCosted, Costed.map] using
    canonicalRelativeRmmMachineSummaryCosted_cost_eq_four_of_macro_crossing
      shape hmacro block

/-- A live local sparse cell followed by its summary costs exactly five reads. -/
theorem canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_eq_five
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart level : Nat)
    (hmacro : macroIdx <
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    (hlevel : level < (RelativeRmm.canonicalLayout shape).levelCount)
    (hlocal : localStart < (RelativeRmm.canonicalLayout shape).macroSize) :
    (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
      macroIdx localStart level).cost = 5 := by
  let layout := RelativeRmm.canonicalLayout shape
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalTable shape).table
    (bpLocalSparseCellSlot layout.macroSize layout.levelCount
      macroIdx localStart level)
  let offset :=
    bpLocalSparseCellOffset shape layout.blockSize layout.blockCount
      layout.macroSize macroIdx localStart level
  have hreadValue : read.value = some offset := by
    change read.erase = some offset
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase]
    simpa [PayloadLiveBPLocalSparseOffsetTable.readOffsetCosted,
      layout, offset] using
      (canonicalRelativeRmmInteriorLocalTable shape).readOffsetCosted_erase_of_valid
        hmacro hlevel hlocal
  have hoffsetPos : 0 < layout.offsetWidth := by
    exact SuccinctRank.machineWordBits_pos layout.macroSize
  have hrelative :=
    canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount
      (shape := shape) hmacroCrossing
  have hoffset := Nat.le_trans
    (canonicalRelativeRmmOffsetWidth_le_relativeWidth shape) hrelative
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorLocalTable shape).table
      hoffsetPos hoffset _
  have hsummary :
      (canonicalRelativeRmmMachineMinCandidateCosted shape
        (macroIdx * layout.macroSize + offset)).cost = 4 :=
    canonicalRelativeRmmMachineMinCandidateCosted_cost_eq_four_of_macro_crossing
      shape hmacroCrossing _
  change (Costed.bind read fun offset? =>
    match offset? with
    | some offset => canonicalRelativeRmmMachineMinCandidateCosted shape
        (macroIdx * layout.macroSize + offset)
    | none => Costed.pure none).cost = 5
  rw [Costed.cost_bind, hreadValue, hreadCost, hsummary]

/-- A live global sparse cell followed by its summary costs exactly five reads. -/
theorem canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_eq_five
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart level : Nat)
    (hlevel : level <
      (RelativeRmm.canonicalLayout shape).globalLevelCount)
    (hmacro : macroStart <
      (RelativeRmm.canonicalLayout shape).macroSampleCount) :
    (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
      macroStart level).cost = 5 := by
  let layout := RelativeRmm.canonicalLayout shape
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalTable shape).table
    (bpGlobalSparseCellSlot layout.macroSampleCount macroStart level)
  let block :=
    bpGlobalSparseCellBlock shape layout.blockSize layout.blockCount
      layout.macroSize layout.macroSampleCount macroStart level
  have hreadValue : read.value = some block := by
    change read.erase = some block
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase]
    simpa [PayloadLiveBPGlobalSparseBlockTable.readBlockCosted,
      layout, block] using
      (canonicalRelativeRmmInteriorGlobalTable shape).readBlockCosted_erase_of_valid
        hlevel hmacro
  have hblockPos : 0 < layout.blockAddressWidth := by
    exact SuccinctRank.machineWordBits_pos layout.blockCount
  have hblockWidth := canonicalRelativeRmmBlockWidth_le_machine shape
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorGlobalTable shape).table
      hblockPos hblockWidth _
  have hsummary :
      (canonicalRelativeRmmMachineMinCandidateCosted shape block).cost = 4 :=
    canonicalRelativeRmmMachineMinCandidateCosted_cost_eq_four_of_macro_crossing
      shape hmacroCrossing block
  change (Costed.bind read fun block? =>
    match block? with
    | some block => canonicalRelativeRmmMachineMinCandidateCosted shape block
    | none => Costed.pure none).cost = 5
  rw [Costed.cost_bind, hreadValue, hreadCost, hsummary]

/--
Within-macro branch.  Only `4 <= shape.size` is available here - no macro
crossing - so the charged level read is bounded at the unconditional
`cost_le_eight` rate.  The branch has ample headroom under the interior cap:
`26 <= 33`.
-/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_twenty_six_of_size_ge_four
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (macroIdx localStart count : Nat) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart count).cost <= 26 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table count
  have hread : read.cost <= 8 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_eight
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      (bpSparseLevelLocalWidth_le_seven_machine shape) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 18 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_nine_of_size_ge_four
            shape hsize _ _ _)
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_nine_of_size_ge_four
                shape hsize macroIdx (localStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted, read, domain]
    using hall

/--
THE MAXIMIZING-BRANCH LEAF.  Under macro crossing the charged level read fits
in ONE machine word (`bpSparseLevelLocalWidth_le_machine_of_macro_crossing`),
so it costs exactly one charged event: `1 + 5 + 5 = 11`.  This is the read
that enters the accounting and moves the route literal.
-/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart count : Nat) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart count).cost <= 11 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table count
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      (bpSparseLevelLocalWidth_le_machine_of_macro_crossing hmacro) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 10 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_five_of_macro_crossing
            shape hmacro _ _ _)
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_le_five_of_macro_crossing
                shape hmacro macroIdx (localStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx localStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
                macroIdx (localStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted, read, domain]
    using hall

/-- Global twin of the maximizing-branch leaf: `1 + 5 + 5 = 11`. -/
theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart count : Nat) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      macroStart count).cost <= 11 := by
  let domain :=
    bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount
  let read :=
    canonicalRelativeRmmMachineReadNatCosted shape
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table count
  have hread : read.cost <= 1 :=
    canonicalRelativeRmmMachineReadNatCosted_cost_le_one
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      (bpSparseLevelGlobalWidth_le_machine_of_macro_crossing hmacro) count
  have htail : forall cell?,
      (match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none).cost <= 10 := by
    intro cell?
    cases cell? with
    | none => simp [Costed.pure]
    | some cell =>
        exact costed_bind_cost_le _ _
          (canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_five_of_macro_crossing
            shape hmacro _ _)
          (fun _ => by
            simpa [Costed.map] using
              canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_le_five_of_macro_crossing
                shape hmacro (macroStart + count - cell % domain)
                (cell / domain))
  have hall := costed_bind_cost_le read
    (fun cell? =>
      match cell? with
      | some cell =>
          Costed.bind
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              macroStart (cell / domain)) fun left? =>
            Costed.map (fun right? => bpCandidateMerge? left? right?)
              (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
                (macroStart + count - cell % domain) (cell / domain))
      | none => Costed.pure none)
    hread htail
  simpa [canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted, read, domain]
    using hall

/-- A live count-one local two-span call performs `1 + 5 + 5` reads. -/
theorem canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_eq_eleven_of_one
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroIdx localStart : Nat)
    (hmacro : macroIdx <
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    (hlocal : localStart <
      (RelativeRmm.canonicalLayout shape).macroSize) :
    (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
      macroIdx localStart 1).cost = 11 := by
  let layout := RelativeRmm.canonicalLayout shape
  let domain := bpSparseLevelDomain layout.macroSize
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorLocalLevelTable shape).table 1
  have honeLt : 1 < domain := by
    have := two_le_bpSparseLevelDomain layout.macroSize
    simpa [domain] using this
  have hreadValue : read.value = some 1 := by
    change read.erase = some 1
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    change (bpSparseLevelEntries domain)[1]? = some 1
    rw [bpSparseLevelEntries_getElem? honeLt]
    have hlog : Nat.log2 1 = 0 := by
      have hpow : (1 : Nat) < 2 ^ (1 : Nat) := by simp
      have hlt : Nat.log2 1 < 1 :=
        (Nat.log2_lt (by omega : Not ((1 : Nat) = 0))).2 hpow
      omega
    simp [bpSparseLevelCell, bpSparseLogSpan, hlog]
  have hwidthPos : 0 < bpSparseLevelWidth domain := by
    simp [bpSparseLevelWidth]
  have hwidth : bpSparseLevelWidth domain <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [domain, layout] using
      bpSparseLevelLocalWidth_le_machine_of_macro_crossing hmacroCrossing
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table
      hwidthPos hwidth 1
  have hlevelPos : 0 < layout.levelCount := by
    exact SuccinctRank.machineWordBits_pos layout.macroSize
  have hleft :=
    canonicalRelativeRmmMachineLocalSpanCandidateCosted_cost_eq_five
      shape hmacroCrossing macroIdx localStart 0 hmacro hlevelPos hlocal
  have hright := hleft
  have hdiv : 1 / domain = 0 := Nat.div_eq_of_lt honeLt
  have hmod : 1 % domain = 1 := Nat.mod_eq_of_lt honeLt
  have hrightStart : localStart + 1 - 1 = localStart := by omega
  change (Costed.bind read fun cell? =>
    match cell? with
    | some cell =>
        Costed.bind
          (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
            macroIdx localStart (cell / domain)) fun left? =>
          Costed.map (fun right? => bpCandidateMerge? left? right?)
            (canonicalRelativeRmmMachineLocalSpanCandidateCosted shape
              macroIdx (localStart + 1 - cell % domain) (cell / domain))
    | none => Costed.pure none).cost = 11
  rw [Costed.cost_bind, hreadValue]
  simp only [hdiv, hmod]
  rw [hrightStart, Costed.cost_bind, Costed.map_cost, hreadCost, hleft]

/-- A live count-one global two-span call performs `1 + 5 + 5` reads. -/
theorem canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_eq_eleven_of_one
    (shape : Cartesian.CartesianShape)
    (hmacroCrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart : Nat)
    (hmacro : macroStart <
      (RelativeRmm.canonicalLayout shape).macroSampleCount) :
    (canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
      macroStart 1).cost = 11 := by
  let layout := RelativeRmm.canonicalLayout shape
  let domain := bpSparseLevelDomain layout.macroSampleCount
  let read := canonicalRelativeRmmMachineReadNatCosted shape
    (canonicalRelativeRmmInteriorGlobalLevelTable shape).table 1
  have honeLt : 1 < domain := by
    have := two_le_bpSparseLevelDomain layout.macroSampleCount
    simpa [domain] using this
  have hreadValue : read.value = some 1 := by
    change read.erase = some 1
    unfold read
    rw [canonicalRelativeRmmMachineReadNatCosted_erase,
      SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    change (bpSparseLevelEntries domain)[1]? = some 1
    rw [bpSparseLevelEntries_getElem? honeLt]
    have hlog : Nat.log2 1 = 0 := by
      have hpow : (1 : Nat) < 2 ^ (1 : Nat) := by simp
      have hlt : Nat.log2 1 < 1 :=
        (Nat.log2_lt (by omega : Not ((1 : Nat) = 0))).2 hpow
      omega
    simp [bpSparseLevelCell, bpSparseLogSpan, hlog]
  have hwidthPos : 0 < bpSparseLevelWidth domain := by
    simp [bpSparseLevelWidth]
  have hwidth : bpSparseLevelWidth domain <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
    simpa [domain, layout] using
      bpSparseLevelGlobalWidth_le_machine_of_macro_crossing hmacroCrossing
  have hreadCost : read.cost = 1 := by
    exact canonicalRelativeRmmMachineReadNatCosted_cost_eq_one
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
      hwidthPos hwidth 1
  have hlevelPos : 0 < layout.globalLevelCount := by
    exact SuccinctRank.machineWordBits_pos layout.macroSampleCount
  have hleft :=
    canonicalRelativeRmmMachineGlobalSpanCandidateCosted_cost_eq_five
      shape hmacroCrossing macroStart 0 hlevelPos hmacro
  have hright := hleft
  have hdiv : 1 / domain = 0 := Nat.div_eq_of_lt honeLt
  have hmod : 1 % domain = 1 := Nat.mod_eq_of_lt honeLt
  have hrightStart : macroStart + 1 - 1 = macroStart := by omega
  change (Costed.bind read fun cell? =>
    match cell? with
    | some cell =>
        Costed.bind
          (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
            macroStart (cell / domain)) fun left? =>
          Costed.map (fun right? => bpCandidateMerge? left? right?)
            (canonicalRelativeRmmMachineGlobalSpanCandidateCosted shape
              (macroStart + 1 - cell % domain) (cell / domain))
    | none => Costed.pure none).cost = 11
  rw [Costed.cost_bind, hreadValue]
  simp only [hdiv, hmod]
  rw [hrightStart, Costed.cost_bind, Costed.map_cost, hreadCost, hleft]

theorem canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart localStart rightCount : Nat) :
    (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted shape
      macroStart localStart rightCount).cost <= 22 := by
  let left := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    macroStart localStart
    ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let right := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    (macroStart + 1) 0 rightCount
  have hleft : left.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hright : right.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun right? => bpCandidateMerge? left? right?) right)
    hleft (fun _ => by simpa [Costed.map] using hright)
  simpa [canonicalRelativeRmmMachineAdjacentMacroCandidateCosted,
    left, right] using hall

theorem canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart localStart middleMacroCount : Nat) :
    (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted shape
      macroStart localStart middleMacroCount).cost <= 22 := by
  let left := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    macroStart localStart
    ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle := canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
    (macroStart + 1) middleMacroCount
  have hleft : left.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hmiddle : middle.cost <= 11 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _
  have hall := costed_bind_cost_le left
    (fun left? => Costed.map (fun middle? => bpCandidateMerge? left? middle?) middle)
    hleft (fun _ => by simpa [Costed.map] using hmiddle)
  simpa [canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted,
    left, middle] using hall

theorem canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le_thirty_three_of_macro_crossing
    (shape : Cartesian.CartesianShape)
    (hmacro :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (canonicalRelativeRmmMachineCrossMacroCandidateCosted shape
      macroStart localStart middleMacroCount rightCount).cost <= 33 := by
  let left := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    macroStart localStart
    ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
  let middle := canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted shape
    (macroStart + 1) middleMacroCount
  let right := canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted shape
    (macroStart + 1 + middleMacroCount) 0 rightCount
  have hleft : left.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have hmiddle : middle.cost <= 11 :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _
  have hright : right.cost <= 11 :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_eleven_of_macro_crossing
      shape hmacro _ _ _
  have htail : forall left?,
      (Costed.bind middle fun middle? =>
        Costed.map (fun right? => bpCandidateMerge3? left? middle? right?) right).cost <= 22 := by
    intro left?
    exact costed_bind_cost_le _ _ hmiddle
      (fun _ => by simpa [Costed.map] using hright)
  have hall := costed_bind_cost_le left
    (fun left? => Costed.bind middle fun middle? =>
      Costed.map (fun right? => bpCandidateMerge3? left? middle? right?) right)
    hleft htail
  simpa [canonicalRelativeRmmMachineCrossMacroCandidateCosted,
    left, middle, right] using hall

/-!
### Canonical exact-cost witness for the charged sparse-level route

The right-spine witness below is deliberately a real Cartesian shape, with an
ordinary `List Int` representative.  Its list-facing window `[1704, 3469)`
selects closes `3409` and `6937`; the accepted cross-block consumer therefore
passes the interior range `(startBlock, count) = (143, 146)`.  That range takes
the cross-macro branch with parameters `(0, 143, 1, 1)` and performs three
successful eleven-read two-span calls.
-/

def canonicalRelativeRmmInteriorCost33RightSpine :
    Nat -> Cartesian.CartesianShape
  | 0 => .empty
  | n + 1 => .node .empty (canonicalRelativeRmmInteriorCost33RightSpine n)

theorem canonicalRelativeRmmInteriorCost33RightSpine_size (n : Nat) :
    (canonicalRelativeRmmInteriorCost33RightSpine n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [canonicalRelativeRmmInteriorCost33RightSpine,
        Cartesian.CartesianShape.size, ih]
      omega

def canonicalRelativeRmmInteriorCost33WitnessShape :
    Cartesian.CartesianShape :=
  canonicalRelativeRmmInteriorCost33RightSpine 3469

def canonicalRelativeRmmInteriorCost33WitnessInput : List Int :=
  canonicalRelativeRmmInteriorCost33WitnessShape.representative

theorem canonicalRelativeRmmInteriorCost33WitnessShape_size :
    canonicalRelativeRmmInteriorCost33WitnessShape.size = 3469 := by
  exact canonicalRelativeRmmInteriorCost33RightSpine_size 3469

theorem canonicalRelativeRmmInteriorCost33WitnessInput_length :
    canonicalRelativeRmmInteriorCost33WitnessInput.length = 3469 := by
  simp [canonicalRelativeRmmInteriorCost33WitnessInput,
    Cartesian.CartesianShape.representative_length,
    canonicalRelativeRmmInteriorCost33WitnessShape_size]

theorem canonicalRelativeRmmInteriorCost33WitnessInput_shape :
    Cartesian.shape canonicalRelativeRmmInteriorCost33WitnessInput =
      canonicalRelativeRmmInteriorCost33WitnessShape := by
  simp [canonicalRelativeRmmInteriorCost33WitnessInput,
    Cartesian.CartesianShape.shape_representative]

theorem canonicalRelativeRmmInteriorCost33RightSpine_close
    (n i : Nat) (hi : i < n) :
    SuccinctSpace.bpCloseOfInorder?
        (canonicalRelativeRmmInteriorCost33RightSpine n) i =
      some (2 * i + 1) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      by_cases hzero : i = 0
      · subst i
        simp [canonicalRelativeRmmInteriorCost33RightSpine,
          SuccinctSpace.bpCloseOfInorder?, Cartesian.CartesianShape.size,
          Cartesian.CartesianShape.bpCode]
      · have hpos : 0 < i := Nat.pos_of_ne_zero hzero
        have htail : i - 1 < n := by omega
        have ih' := ih (i - 1) htail
        simp [canonicalRelativeRmmInteriorCost33RightSpine,
          SuccinctSpace.bpCloseOfInorder?, Cartesian.CartesianShape.size,
          Cartesian.CartesianShape.bpCode, hzero, ih']
        omega

theorem canonicalRelativeRmmInteriorCost33Witness_closes :
    SuccinctSpace.bpCloseOfInorder?
        canonicalRelativeRmmInteriorCost33WitnessShape 1704 = some 3409 /\
      SuccinctSpace.bpCloseOfInorder?
        canonicalRelativeRmmInteriorCost33WitnessShape 3468 = some 6937 := by
  constructor
  · simpa [canonicalRelativeRmmInteriorCost33WitnessShape] using
      canonicalRelativeRmmInteriorCost33RightSpine_close 3469 1704 (by omega)
  · simpa [canonicalRelativeRmmInteriorCost33WitnessShape] using
      canonicalRelativeRmmInteriorCost33RightSpine_close 3469 3468 (by omega)

/-- The numeral geometry used by the reachable tightness family. -/
theorem canonicalRelativeRmmInteriorCost33Layout_of_size_eq
    (shape : Cartesian.CartesianShape) (hsize : shape.size = 3469) :
    (RelativeRmm.canonicalLayout shape).blockSize = 24 /\
      (RelativeRmm.canonicalLayout shape).blocksPerSuper = 12 /\
      (RelativeRmm.canonicalLayout shape).blockCount = 289 /\
      (RelativeRmm.canonicalLayout shape).macroSize = 144 /\
      (RelativeRmm.canonicalLayout shape).macroSampleCount = 3 := by
  simp only [RelativeRmm.canonicalLayout,
    RelativeRmm.Layout.macroSize, RelativeRmm.Layout.macroSampleCount,
    canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryBlockCountRaw,
    canonicalBPRelativeSummaryBase]
  rw [hsize]
  have hlower : 11 <= Nat.log2 3469 :=
    (Nat.le_log2 (by decide : Not ((3469 : Nat) = 0))).2 (by decide)
  have hupper : Nat.log2 3469 < 12 :=
    (Nat.log2_lt (by decide : Not ((3469 : Nat) = 0))).2 (by decide)
  have hlog : Nat.log2 3469 = 11 := by omega
  rw [hlog]
  decide

/-- The accepted interior dispatcher takes the three-leaf cross-macro route. -/
theorem canonicalRelativeRmmInteriorCost33_dispatch_of_size_eq
    (shape : Cartesian.CartesianShape) (hsize : shape.size = 3469) :
    canonicalRelativeRmmInteriorRangeMinCosted shape 143 146 =
      canonicalRelativeRmmMachineCrossMacroCandidateCosted shape 0 143 1 1 := by
  have hgeometry := canonicalRelativeRmmInteriorCost33Layout_of_size_eq shape hsize
  rcases hgeometry with ⟨_, _, _, hmacroSize, _⟩
  simp [canonicalRelativeRmmInteriorRangeMinCosted, hmacroSize]

/--
Every canonical shape of the witness size has the same exact operational
count.  The proof composes three successful count-one two-span calls; it does
not reduce the shape's payload or infer equality from the public upper bound.
-/
theorem canonicalRelativeRmmInteriorCost33_cost_eq_of_size_eq
    (shape : Cartesian.CartesianShape) (hsize : shape.size = 3469) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape 143 146).cost = 33 := by
  have hgeometry := canonicalRelativeRmmInteriorCost33Layout_of_size_eq shape hsize
  rcases hgeometry with ⟨_, _, hblockCount, hmacroSize, hmacroCount⟩
  have hcrossing :
      (RelativeRmm.canonicalLayout shape).macroSize <
        (RelativeRmm.canonicalLayout shape).blockCount := by omega
  have hleft :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_eq_eleven_of_one
      shape hcrossing 0 143 (by omega) (by omega)
  have hmiddle :=
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateCosted_cost_eq_eleven_of_one
      shape hcrossing 1 (by omega)
  have hright :=
    canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_eq_eleven_of_one
      shape hcrossing 2 0 (by omega) (by omega)
  rw [canonicalRelativeRmmInteriorCost33_dispatch_of_size_eq shape hsize]
  unfold canonicalRelativeRmmMachineCrossMacroCandidateCosted
  simp only [Costed.cost_bind, Costed.map_cost]
  simp [hmacroSize, hleft, hmiddle, hright]

/--
The canonical accepted interior object itself reaches the advertised cap.
This is equality on the live evaluator, not an upper-bound proof.
-/
theorem canonicalRelativeRmmInteriorCost33Witness_exact :
    (canonicalRelativeRmmInteriorRangeMinCosted
      canonicalRelativeRmmInteriorCost33WitnessShape 143 146).cost = 33 := by
  exact canonicalRelativeRmmInteriorCost33_cost_eq_of_size_eq
    canonicalRelativeRmmInteriorCost33WitnessShape
    canonicalRelativeRmmInteriorCost33WitnessShape_size

/-- The retired `cost <= 30` claim fails on that identical canonical object. -/
theorem canonicalRelativeRmmInteriorCost33Witness_not_cost_le_thirty :
    Not ((canonicalRelativeRmmInteriorRangeMinCosted
      canonicalRelativeRmmInteriorCost33WitnessShape 143 146).cost <= 30) := by
  rw [canonicalRelativeRmmInteriorCost33Witness_exact]
  omega

/-- The same exact count holds on the canonical concatenated component store. -/
theorem canonicalRelativeRmmInteriorCost33Witness_store_exact :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore
      canonicalRelativeRmmInteriorCost33WitnessShape
      (canonicalRelativeRmmInteriorComponentStore
        canonicalRelativeRmmInteriorCost33WitnessShape).store.words
      143 146).cost = 33 := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact canonicalRelativeRmmInteriorCost33Witness_exact

/-- Its recorded physical footprint contains exactly the same 33 reads. -/
theorem canonicalRelativeRmmInteriorCost33Witness_footprint_length :
    (canonicalRelativeRmmInteriorRangeFootprintWithStore
      canonicalRelativeRmmInteriorCost33WitnessShape
      (canonicalRelativeRmmInteriorComponentStore
        canonicalRelativeRmmInteriorCost33WitnessShape).store.words
      143 146).length = 33 := by
  rw [<- canonicalRelativeRmmInteriorRange_cost_eq_footprint_length]
  exact canonicalRelativeRmmInteriorCost33Witness_store_exact

/--
The accepted U2 interior execution costs at most thirty-three charged
primitive events on every positive bounded range.  The only use of
`4 <= shape.size` is the all-size width fact in the within-macro branch;
public dispatch remains uniform and contains no activation threshold.

THE VALUE IS ATTAINED, not slack.  The maximizing cross-macro branch performs
three two-span calls, each of which now reads the charged sparse-level table
once (`11 = 1 + 5 + 5`), so `3 * 11 = 33` and the final step is a bare `exact`
against the branch bound with no `Nat.le_trans` widening.  The three units
over the pre-swap `30` are exactly the three charged level reads.
-/
theorem canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (startBlock count : Nat)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).cost <=
      33 := by
  let layout := RelativeRmm.canonicalLayout shape
  unfold canonicalRelativeRmmInteriorRangeMinCosted
  by_cases hcount : count = 0
  · simp [hcount, Costed.pure]
  · simp only [hcount, if_false]
    by_cases hwithin : count <=
        (RelativeRmm.canonicalLayout shape).macroSize -
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    · simp only [hwithin, if_true]
      exact Nat.le_trans
        (canonicalRelativeRmmMachineLocalTwoSpanCandidateCosted_cost_le_twenty_six_of_size_ge_four
          shape hsize _ _ count)
        (by simp)
    · have hvalid := RelativeRmm.canonicalLayout_valid shape
      have hwithin' :
          ¬ count <= layout.macroSize - startBlock % layout.macroSize := by
        simpa [layout] using hwithin
      have hmodLt : startBlock % layout.macroSize < layout.macroSize :=
        Nat.mod_lt startBlock hvalid.macroSize_pos
      have hmodLe : startBlock % layout.macroSize <= startBlock :=
        Nat.mod_le startBlock layout.macroSize
      have hcross : layout.macroSize < startBlock + count := by
        omega
      have hmacro : layout.macroSize < layout.blockCount :=
        Nat.lt_of_lt_of_le hcross (by simpa [layout] using hbound)
      simp only [hwithin, if_false]
      by_cases hmiddle :
          (count -
              ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize = 0
      · simp only [hmiddle, if_true]
        exact Nat.le_trans
          (canonicalRelativeRmmMachineAdjacentMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
            shape (by simpa [layout] using hmacro) _ _ _)
          (by simp)
      · simp only [hmiddle, if_false]
        by_cases hright :
            (count -
                ((RelativeRmm.canonicalLayout shape).macroSize -
                  startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize = 0
        · simp only [hright, if_true]
          exact Nat.le_trans
            (canonicalRelativeRmmMachineLeftMiddleMacroCandidateCosted_cost_le_twenty_two_of_macro_crossing
              shape (by simpa [layout] using hmacro) _ _ _)
            (by simp)
        · simp only [hright, if_false]
          exact canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le_thirty_three_of_macro_crossing
            shape (by simpa [layout] using hmacro) _ _ _ _

/--
The accepted U2 interior execution respects the declared all-size interior
cap.  Stated against the cap FIELD rather than against a literal, so every
consumer of the cap keeps working across a recharge; the tight literal
content lives in the `_literal` theorem above.

At this commit the step is `33 <= 33` and therefore TIGHT.  The announced-slack
theorem that recorded the staging compromise has been deleted: its `30 < cap`
conjunct is unprovable now that the charged sparse-level reads are reachable.
-/
theorem canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (startBlock count : Nat)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).cost <=
      canonicalRelativeRmmPrincipledInteriorChargedTraceCost :=
  Nat.le_trans
    (canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded
      shape hsize startBlock count hbound)
    (by simp [canonicalRelativeRmmPrincipledInteriorChargedTraceCost])

/-
RETIRED AT THE CHARGED SPARSE-LEVEL SWAP.

`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`
stood here.  It announced that the declared cap STRICTLY exceeded what the
route needed (`route <= 30` and `30 < cap = 33`), which was the checked
statement of commit A's staging compromise.

It is DELETED rather than weakened, exactly as its own docstring required.
The swap made its first conjunct false: the maximizing cross-macro branch now
performs three charged sparse-level reads and attains `33`, so `route <= 30`
is no longer provable.  The cap is tight again, and
`canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_three_literal_of_size_ge_four_of_bounded`
carries the tight content.
-/

theorem canonicalRelativeRmmInteriorRangeMinCosted_erase_exact
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    (hcount : 0 < count)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCosted shape startBlock count).erase =
      some
        (bpRangeMinExcess shape
          (RelativeRmm.canonicalLayout shape).blockSize startBlock count,
          bpRangeArgMinPrefixPos shape
            (RelativeRmm.canonicalLayout shape).blockSize startBlock count) := by
  let layout := RelativeRmm.canonicalLayout shape
  have hvalid := RelativeRmm.canonicalLayout_valid shape
  have hmacroCover :
      layout.blockCount <= layout.macroSampleCount * layout.macroSize := by
    have hlt := Nat.lt_div_mul_add hvalid.macroSize_pos
      (a := layout.blockCount)
    have hlt' : layout.blockCount <
        (layout.blockCount / layout.macroSize + 1) * layout.macroSize := by
      simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hlt
    exact Nat.le_of_lt
      (by simpa [RelativeRmm.Layout.macroSampleCount] using hlt')
  have hsuperIndex : forall {block : Nat}, block < layout.blockCount ->
      block / layout.blocksPerSuper < layout.superSampleCount := by
    intro block hblock
    exact PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
      (blockCount := layout.blockCount) hblock
  have hexact := bpTwoLevelInteriorCandidateCosted_erase_exact
    (canonicalRelativeRmmInteriorLocalTable shape)
    (canonicalRelativeRmmInteriorGlobalTable shape)
    (canonicalRelativeRmmSummaryTable shape)
    hvalid.macroSize_pos hcount (by simpa [layout] using hbound)
    (by
      intro block hblock
      exact PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
        (blockCount := layout.blockCount) hblock)
    hmacroCover
    (by
      intro localCount hlocalPos hlocalLe
      have hcap : localCount < 2 ^ layout.levelCount :=
        Nat.lt_of_le_of_lt hlocalLe
          (SuccinctRank.self_lt_two_pow_machineWordBits layout.macroSize)
      have hsucc := natLog2_succ_le_of_pos_lt_pow hlocalPos hcap
      simpa [RelativeRmm.Layout.levelCount,
        RelativeRmm.Layout.offsetWidth] using hsucc)
    (by
      intro macroSpanCount hspanPos hspanLe
      have hcap : macroSpanCount < 2 ^ layout.globalLevelCount :=
        Nat.lt_of_le_of_lt hspanLe
          (SuccinctRank.self_lt_two_pow_machineWordBits
            layout.macroSampleCount)
      have hsucc := natLog2_succ_le_of_pos_lt_pow hspanPos hcap
      simpa [RelativeRmm.Layout.globalLevelCount] using hsucc)
    hvalid.blocksPerSuper_pos hvalid.fullBlocks_fit hsuperIndex
  rw [canonicalRelativeRmmInteriorRangeMinCosted_refines_logical shape startBlock count hbound]
  simpa [layout] using hexact

theorem canonicalRelativeRmmInteriorWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    {word : List Bool}
    (hmem : List.Mem word
      (canonicalRelativeRmmInteriorWordsRead shape startBlock count)) :
    word.length <= SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold canonicalRelativeRmmInteriorWordsRead at hmem
  cases List.mem_flatMap.mp hmem with
  | intro logicalWord hrest =>
      exact SuccinctSpace.chunkPayloadWords_word_length_le
        (SuccinctRank.machineWordBits shape.bpCode.length) hrest.2


theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le
    (shape : Cartesian.CartesianShape) (startBlock count : Nat) :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count).cost <= canonicalRelativeRmmInteriorQueryCost := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact canonicalRelativeRmmInteriorRangeMinCosted_cost_le
    shape startBlock count

theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_cost_le_thirty_of_size_ge_four_of_bounded
    (shape : Cartesian.CartesianShape) (hsize : 4 <= shape.size)
    (startBlock count : Nat)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count).cost <=
        canonicalRelativeRmmPrincipledInteriorChargedTraceCost := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact
    canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded
      shape hsize startBlock count hbound

theorem canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact
    {shape : Cartesian.CartesianShape} {startBlock count : Nat}
    (hcount : 0 < count)
    (hbound : startBlock + count <=
      (RelativeRmm.canonicalLayout shape).blockCount) :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore shape
      (canonicalRelativeRmmInteriorComponentStore shape).store.words
      startBlock count).erase =
      some
        (bpRangeMinExcess shape
          (RelativeRmm.canonicalLayout shape).blockSize startBlock count,
          bpRangeArgMinPrefixPos shape
            (RelativeRmm.canonicalLayout shape).blockSize startBlock count) := by
  rw [canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_current]
  exact canonicalRelativeRmmInteriorRangeMinCosted_erase_exact hcount hbound

/-- The exact-cost store-backed witness returns the accepted leftmost candidate. -/
theorem canonicalRelativeRmmInteriorCost33Witness_store_erase_exact :
    (canonicalRelativeRmmInteriorRangeMinCostedWithStore
      canonicalRelativeRmmInteriorCost33WitnessShape
      (canonicalRelativeRmmInteriorComponentStore
        canonicalRelativeRmmInteriorCost33WitnessShape).store.words
      143 146).erase =
      some
        (bpRangeMinExcess canonicalRelativeRmmInteriorCost33WitnessShape
          (RelativeRmm.canonicalLayout
            canonicalRelativeRmmInteriorCost33WitnessShape).blockSize 143 146,
          bpRangeArgMinPrefixPos canonicalRelativeRmmInteriorCost33WitnessShape
            (RelativeRmm.canonicalLayout
              canonicalRelativeRmmInteriorCost33WitnessShape).blockSize
            143 146) := by
  apply canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact
  · omega
  · have hgeometry := canonicalRelativeRmmInteriorCost33Layout_of_size_eq
      canonicalRelativeRmmInteriorCost33WitnessShape
      canonicalRelativeRmmInteriorCost33WitnessShape_size
    omega


end SuccinctClose
end RMQ
