import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerProof

/-!
# Canonical scalar bounds for the atomic reviewer protocols

This module isolates the scalar-register part of canonical reachability for
Rank, WordSelect, Fringe, and BPWindow.  The predicates below are proof-side
invariants only: no executable state receives a shape, a store, or a proof.

## Frozen acceptance rows

* `ATOM-RANK` -- canonical Rank start, exact-store consume, and result
  projection preserve every member of `packedReviewerRankStateNatFields`.
* `ATOM-WSEL` -- the canonical false-target WordSelect route preserves every
  scalar field and bounds every successful local-position result.
* `ATOM-FRINGE` -- a fringe fold carrying the explicit honest
  `seed + count * chunkWidth` budget preserves every scalar field and result.
* `ATOM-BPWINDOW` -- the four-read BP window preserves all scalar fields; its
  result constructor has no scalar fields.
* `ATOM-CONSUMER` -- the downstream controller-state proof imports these exact
  public predicates and projections.  That composition remains consumer-owned.
* `INV-STORE-IDENTITY` -- every `.consume` theorem below uses literally
  `concreteBPNativeSuccinctRMQGlobalReadStore shape` at the request emitted by
  the corresponding `NextRequest` function.
* `INV-WORD-WIDTH`, `INV-ALL-SIZE`, and `INV-PROOF-SEPARATION` -- word width,
  scalar width, and executable behavior remain separate, and every theorem is
  quantified over all Cartesian shapes.

The extra Rank and Fringe clauses are deliberately stronger than a bare field
inventory.  They retain the decreasing arithmetic envelope needed to justify
new accumulators rather than assuming arbitrary decoded scalars may be added.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

private def PackedReviewerInvocationScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation) : Prop :=
  forall operand,
    operand ∈ packedReviewerInvocationOperands invocation ->
      PackedReviewerNatFits shape.size operand

private theorem PackedReviewerInvocationScalarFits.nat_fields
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    (hinvocation : PackedReviewerInvocationScalarFits shape invocation) :
    forall value,
      value ∈ packedReviewerInvocationNatFields invocation ->
        PackedReviewerNatFits shape.size value := by
  simpa [PackedReviewerInvocationScalarFits,
    packedReviewerInvocationNatFields, packedReviewerInvocationOperands] using
    hinvocation

private theorem packedReviewerCellWidth_scalar_fits (n : Nat) :
    PackedReviewerNatFits n (packedReviewerCellWidth n) := by
  have hpositive : 0 < packedReviewerCellBound n + 2 := by omega
  have hwidthBound :
      packedReviewerCellWidth n <= packedReviewerCellBound n + 2 :=
    GenericSelect.machineWordBits_le_self_of_pos hpositive
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

private theorem PackedReviewerWordFits.length_scalar_fits
    {n : Nat} {word : List Bool} (hword : PackedReviewerWordFits n word) :
    PackedReviewerNatFits n word.length :=
  Nat.lt_of_le_of_lt hword (packedReviewerCellWidth_scalar_fits n)

private theorem packedReviewerCanonicalDecodeNat_fits
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest) :
    forall value,
      packedReviewerDecodeNat
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index) = some value ->
        PackedReviewerNatFits shape.size value := by
  intro value hvalue
  cases hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index with
  | none => simp [packedReviewerDecodeNat, hread] at hvalue
  | some word =>
      have hword :=
        packedReviewerGlobalReadStore_word_fits shape request word hread
      have heq : SuccinctSpace.bitsToNatLE word = value := by
        simpa [packedReviewerDecodeNat, hread] using hvalue
      subst value
      exact hword.value_lt_two_pow

private theorem twoLevelRankData_decoded_samples_add_le
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos super delta : Nat) (hpos : pos <= bits.length)
    (hsuper :
      packedReviewerDecodeNat
          ((data.superSampleWords target)[
            pos / data.wordSize / data.blocksPerSuper]?) = some super)
    (hblock :
      packedReviewerDecodeNat
          ((data.blockSampleWords target)[pos / data.wordSize]?) = some delta) :
    super + delta <= (pos / data.wordSize) * data.wordSize := by
  have hsuperEntry :
      (data.superTables.entries target)[
        pos / data.wordSize / data.blocksPerSuper]? = some super := by
    cases target with
    | false =>
        calc
          (data.superTables.entries false)[
              pos / data.wordSize / data.blocksPerSuper]? =
              (data.superTables.falseTable.store.words[
                pos / data.wordSize / data.blocksPerSuper]?).map
                  SuccinctSpace.bitsToNatLE := by
            simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
              (data.superTables.falseTable.read_exact
                (pos / data.wordSize / data.blocksPerSuper)).symm
          _ = some super := by
            simpa [packedReviewerDecodeNat,
              SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords]
              using hsuper
    | true =>
        calc
          (data.superTables.entries true)[
              pos / data.wordSize / data.blocksPerSuper]? =
              (data.superTables.trueTable.store.words[
                pos / data.wordSize / data.blocksPerSuper]?).map
                  SuccinctSpace.bitsToNatLE := by
            simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
              (data.superTables.trueTable.read_exact
                (pos / data.wordSize / data.blocksPerSuper)).symm
          _ = some super := by
            simpa [packedReviewerDecodeNat,
              SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superSampleWords]
              using hsuper
  have hblockEntry :
      (data.blockTables.entries target)[pos / data.wordSize]? = some delta := by
    cases target with
    | false =>
        calc
          (data.blockTables.entries false)[pos / data.wordSize]? =
              (data.blockTables.falseTable.store.words[
                pos / data.wordSize]?).map SuccinctSpace.bitsToNatLE := by
            simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
              (data.blockTables.falseTable.read_exact
                (pos / data.wordSize)).symm
          _ = some delta := by
            simpa [packedReviewerDecodeNat,
              SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords]
              using hblock
    | true =>
        calc
          (data.blockTables.entries true)[pos / data.wordSize]? =
              (data.blockTables.trueTable.store.words[
                pos / data.wordSize]?).map SuccinctSpace.bitsToNatLE := by
            simpa [SuccinctSpace.FixedWidthRankSampleTables.entries] using
              (data.blockTables.trueTable.read_exact
                (pos / data.wordSize)).symm
          _ = some delta := by
            simpa [packedReviewerDecodeNat,
              SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockSampleWords]
              using hblock
  let wordStart := (pos / data.wordSize) * data.wordSize
  have hwordStart : wordStart <= pos := by
    exact Nat.div_mul_le_self _ _
  have hwordStartBits : wordStart <= bits.length :=
    Nat.le_trans hwordStart hpos
  have hsuperStart :
      (data.superTables.entries target)[
        wordStart / data.wordSize / data.blocksPerSuper]? = some super := by
    simpa [wordStart, data.wordSize_pos] using hsuperEntry
  have hblockStart :
      (data.blockTables.entries target)[wordStart / data.wordSize]? =
        some delta := by
    simpa [wordStart, data.wordSize_pos] using hblockEntry
  rcases data.word_present wordStart hwordStartBits with ⟨word, hword⟩
  have hparts :=
    data.rank_parts_exact target wordStart super delta word hwordStartBits
      hsuperStart hblockStart hword
  have hrank := Succinct.rankPrefix_le_limit target bits wordStart
  simpa [wordStart, data.wordSize_pos] using (show
    super + delta <= wordStart by omega)

/-- Eight charged chunks plus any BP-sized prefix still fit one reviewer cell. -/
private theorem packedReviewerTwoMul_add_eight_chunks_le_cellBound (n : Nat) :
    2 * n + 8 * packedFringeChunkBits n <= packedReviewerCellBound n := by
  let w := packedRankWordSize n
  have hw : w = Nat.log2 (2 * n) + 1 := rfl
  have hdiv : (Nat.log2 (2 * n) / 8) * 8 <= Nat.log2 (2 * n) :=
    Nat.div_mul_le_self _ _
  have hchunk : 8 * packedFringeChunkBits n <= w + 7 := by
    dsimp [w, packedRankWordSize, packedFringeChunkBits,
      SuccinctClose.bpFringeChunkBits, SuccinctRank.machineWordBits]
    omega
  by_cases hlarge : 7 <= w
  · have haux := packedRankAux_le_reviewerBound n
    have htwo := packedRankWordSize_two_le_aux n
    omega
  · have hinput := SuccinctRank.self_lt_two_pow_machineWordBits (2 * n)
    have hpow : 2 ^ w <= 2 ^ 7 :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (by omega : w < 7))
    have hbound := packedReviewerCellBound_ge_five_twelve n
    dsimp [w, packedRankWordSize] at hinput hpow
    omega

private theorem packedReviewerRankEnvelope_fits
    (n base remaining : Nat) (hbase : base <= 2 * n)
    (hremaining : remaining <= 8) :
    PackedReviewerNatFits n
      (base + remaining * packedFringeChunkBits n) := by
  have hbound := packedReviewerTwoMul_add_eight_chunks_le_cellBound n
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  have hmul := Nat.mul_le_mul_right (packedFringeChunkBits n) hremaining
  omega

private theorem packedReviewerRankProgress_step
    (c effectiveLimit j acc rank : Nat)
    (hacc : acc <= Nat.min (j * c) effectiveLimit)
    (hrank : rank <=
      Nat.min c (effectiveLimit - j * c)) :
    acc + rank <= Nat.min ((j + 1) * c) effectiveLimit := by
  apply Nat.le_min.mpr
  constructor
  · have haccJ := Nat.le_trans hacc (Nat.min_le_left _ _)
    have hrankC := Nat.le_trans hrank (Nat.min_le_left _ _)
    rw [Nat.add_mul]
    omega
  · have haccEffective := Nat.le_trans hacc (Nat.min_le_right _ _)
    have haccJ := Nat.le_trans hacc (Nat.min_le_left _ _)
    have hrankTail := Nat.le_trans hrank (Nat.min_le_right _ _)
    by_cases hj : j * c <= effectiveLimit
    · omega
    · have : effectiveLimit - j * c = 0 := Nat.sub_eq_zero_of_le (by omega)
      omega

/-! ## Rank -/

/--
Canonical scalar invariant for the three-sample Rank protocol.  In a fold,
`base + acc + remaining * c` is a decreasing envelope: an honest chunk adds
at most `c` to `acc` while consuming one unit of `remaining`.
-/
def PackedReviewerRankCanonicalScalarFits
    (shape : CartesianShape) (resultBound : Nat) :
    PackedReviewerRankState -> Prop
  | .superSample invocation kind n pos =>
      n = shape.size ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerNatFits shape.size pos ∧
            resultBound = packedReviewerRankQueryPos kind n pos
  | .blockSample invocation kind n pos superSample =>
      n = shape.size ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerNatFits shape.size pos ∧
            resultBound = packedReviewerRankQueryPos kind n pos ∧
            superSample =
              packedReviewerDecodeNat
                ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  kind.superSegment
                  (packedReviewerRankQueryPos kind n pos /
                    kind.wordSize n / kind.blocksPerSuper n))
  | .word invocation kind n pos superSample blockSample =>
      n = shape.size ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerNatFits shape.size pos ∧
            resultBound = packedReviewerRankQueryPos kind n pos ∧
            superSample =
              packedReviewerDecodeNat
                ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  kind.superSegment
                  (packedReviewerRankQueryPos kind n pos /
                    kind.wordSize n / kind.blocksPerSuper n)) ∧
            blockSample =
              packedReviewerDecodeNat
                ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                  kind.blockSegment
                  (packedReviewerRankQueryPos kind n pos / kind.wordSize n))
  | .fold invocation _ n word effectiveLimit j remaining acc base =>
      n = shape.size ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerWordFits shape.size word ∧
            effectiveLimit <= word.length ∧
              j + remaining <= 8 ∧
                PackedReviewerNatFits shape.size
                  (base + acc + remaining * packedFringeChunkBits shape.size) ∧
                  acc <= Nat.min
                    (j * packedFringeChunkBits shape.size) effectiveLimit ∧
                  base + effectiveLimit <= resultBound
  | .done value =>
      PackedReviewerNatFits shape.size value ∧ value <= resultBound

/-- Every public Rank scalar inventory field follows from the canonical invariant. -/
theorem PackedReviewerRankCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerRankState}
    (hstate : PackedReviewerRankCanonicalScalarFits shape resultBound state) :
    forall value,
      value ∈ packedReviewerRankStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  cases state with
  | superSample invocation kind n pos =>
      rcases hstate with ⟨rfl, hinvocation, hpos, hbound⟩
      intro value hmem
      simp [packedReviewerRankStateNatFields] at hmem
      rcases hmem with hinvocationField | rfl | rfl
      · exact hinvocation.nat_fields value hinvocationField
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hpos
  | blockSample invocation kind n pos superSample =>
      rcases hstate with ⟨rfl, hinvocation, hpos, hbound, hsuper⟩
      intro value hmem
      cases superSample with
      | none =>
          simp [packedReviewerRankStateNatFields,
            packedReviewerOptionNatFields] at hmem
          rcases hmem with hinvocationField | rfl | rfl
          · exact hinvocation.nat_fields value hinvocationField
          · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
          · exact hpos
      | some sample =>
          simp [packedReviewerRankStateNatFields,
            packedReviewerOptionNatFields] at hmem
          rcases hmem with hinvocationField | rfl | rfl | rfl
          · exact hinvocation.nat_fields value hinvocationField
          · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
          · exact hpos
          ·
            apply packedReviewerCanonicalDecodeNat_fits shape
              { invocation := invocation, site := .rankSuper,
                segment := kind.superSegment,
                index :=
                  packedReviewerRankQueryPos kind shape.size pos /
                    kind.wordSize shape.size / kind.blocksPerSuper shape.size }
            simpa using hsuper.symm
  | word invocation kind n pos superSample blockSample =>
      rcases hstate with
        ⟨rfl, hinvocation, hpos, hbound, hsuper, hblock⟩
      intro value hmem
      cases superSample with
      | none =>
          cases blockSample with
          | none =>
              simp [packedReviewerRankStateNatFields,
                packedReviewerOptionNatFields] at hmem
              rcases hmem with hinvocationField | rfl | rfl
              · exact hinvocation.nat_fields value hinvocationField
              · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
              · exact hpos
          | some block =>
              simp [packedReviewerRankStateNatFields,
                packedReviewerOptionNatFields] at hmem
              rcases hmem with hinvocationField | rfl | rfl | rfl
              · exact hinvocation.nat_fields value hinvocationField
              · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
              · exact hpos
              ·
                apply packedReviewerCanonicalDecodeNat_fits shape
                  { invocation := invocation, site := .rankBlock,
                    segment := kind.blockSegment,
                    index :=
                      packedReviewerRankQueryPos kind shape.size pos /
                        kind.wordSize shape.size }
                simpa using hblock.symm
      | some sample =>
          cases blockSample with
          | none =>
              simp [packedReviewerRankStateNatFields,
                packedReviewerOptionNatFields] at hmem
              rcases hmem with hinvocationField | rfl | rfl | rfl
              · exact hinvocation.nat_fields value hinvocationField
              · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
              · exact hpos
              ·
                apply packedReviewerCanonicalDecodeNat_fits shape
                  { invocation := invocation, site := .rankSuper,
                    segment := kind.superSegment,
                    index :=
                      packedReviewerRankQueryPos kind shape.size pos /
                        kind.wordSize shape.size /
                          kind.blocksPerSuper shape.size }
                simpa using hsuper.symm
          | some block =>
              simp [packedReviewerRankStateNatFields,
                packedReviewerOptionNatFields] at hmem
              rcases hmem with hinvocationField | rfl | rfl | rfl | rfl
              · exact hinvocation.nat_fields value hinvocationField
              · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
              · exact hpos
              ·
                apply packedReviewerCanonicalDecodeNat_fits shape
                  { invocation := invocation, site := .rankSuper,
                    segment := kind.superSegment,
                    index :=
                      packedReviewerRankQueryPos kind shape.size pos /
                        kind.wordSize shape.size /
                          kind.blocksPerSuper shape.size }
                simpa using hsuper.symm
              ·
                apply packedReviewerCanonicalDecodeNat_fits shape
                  { invocation := invocation, site := .rankBlock,
                    segment := kind.blockSegment,
                    index :=
                      packedReviewerRankQueryPos kind shape.size pos /
                        kind.wordSize shape.size }
                simpa using hblock.symm
  | fold invocation kind n word effectiveLimit j remaining acc base =>
      rcases hstate with
        ⟨rfl, hinvocation, hword, heffective, hcounters, henvelope,
          hprogress, hresultBound⟩
      intro value hmem
      simp [packedReviewerRankStateNatFields] at hmem
      rcases hmem with hinvocationField | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hinvocation.nat_fields value hinvocationField
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact Nat.lt_of_le_of_lt heffective hword.length_scalar_fits
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · exact Nat.lt_of_le_of_lt (by omega) henvelope
      · exact Nat.lt_of_le_of_lt (by omega) henvelope
  | done value =>
      intro stored hmem
      simp [packedReviewerRankStateNatFields] at hmem
      subst stored
      exact hstate.1

/-- The public Rank start stores only the shape size, invocation, and position. -/
theorem packedReviewerRankStart_canonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (pos : Nat)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hpos : PackedReviewerNatFits shape.size pos) :
    PackedReviewerRankCanonicalScalarFits shape
      (packedReviewerRankQueryPos kind shape.size pos)
      (.superSample invocation kind shape.size pos) :=
  ⟨rfl, hinvocation, hpos, rfl⟩

private theorem packedReviewerRankCanonicalSamples_add_le
    (shape : CartesianShape) (kind : PackedReviewerRankKind)
    (pos super delta : Nat)
    (hsuper :
      packedReviewerDecodeNat
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            kind.superSegment
            (packedReviewerRankQueryPos kind shape.size pos /
              kind.wordSize shape.size /
                kind.blocksPerSuper shape.size)) = some super)
    (hblock :
      packedReviewerDecodeNat
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            kind.blockSegment
            (packedReviewerRankQueryPos kind shape.size pos /
              kind.wordSize shape.size)) = some delta) :
    super + delta <=
      (packedReviewerRankQueryPos kind shape.size pos /
        kind.wordSize shape.size) * kind.wordSize shape.size := by
  let q := packedReviewerRankQueryPos kind shape.size pos
  cases kind with
  | selectLong =>
      let data :=
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagRankData
      have hq : q <=
          (GenericSelect.sparseExceptionSelectData
            shape.bpCode false).longFlagBits.length := by
        have hmin := Nat.min_le_right pos (packedSuperSlots shape.size)
        simpa [q, packedReviewerRankQueryPos,
          PackedReviewerRankKind.bitLength,
          packedSelectLongFlagBitsLength_eq shape] using hmin
      have hs := hsuper
      rw [show PackedReviewerRankKind.selectLong.superSegment =
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase by rfl,
        concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagSuper] at hs
      have hb := hblock
      rw [show PackedReviewerRankKind.selectLong.blockSegment =
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase + 1
            by rfl,
        concreteBPNativeSuccinctRMQGlobalReadStore_selectLongFlagBlock] at hb
      have hsum :=
        twoLevelRankData_decoded_samples_add_le data true q super delta hq
          (by
            simpa [data, q, packedReviewerRankQueryPos,
              PackedReviewerRankKind.wordSize,
              PackedReviewerRankKind.blocksPerSuper,
              packedSelectLongFlagRankWordSize_eq shape,
              packedSelectLongFlagRankBlocksPerSuper_eq shape] using hs)
          (by
            simpa [data, q, packedReviewerRankQueryPos,
              PackedReviewerRankKind.wordSize,
              packedSelectLongFlagRankWordSize_eq shape] using hb)
      simpa [q, data, PackedReviewerRankKind.wordSize,
        packedSelectLongFlagRankWordSize_eq shape] using hsum
  | selectSparse =>
      let data :=
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.rankData
      have hq : q <=
          (GenericSelect.sparseExceptionSelectData
            shape.bpCode false).sparseDirectory.flagBits.length := by
        have hmin := Nat.min_le_right pos (packedSparseSlots shape.size)
        simpa [q, packedReviewerRankQueryPos,
          PackedReviewerRankKind.bitLength,
          packedSelectSparseFlagBitsLength_eq shape] using hmin
      have hs := hsuper
      rw [show PackedReviewerRankKind.selectSparse.superSegment =
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            by rfl,
        concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankSuper] at hs
      have hb := hblock
      rw [show PackedReviewerRankKind.selectSparse.blockSegment =
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase +
            1 by rfl,
        concreteBPNativeSuccinctRMQGlobalReadStore_selectSparseRankBlock] at hb
      have hsum :=
        twoLevelRankData_decoded_samples_add_le data true q super delta hq
          (by
            simpa [data, q, packedReviewerRankQueryPos,
              PackedReviewerRankKind.wordSize,
              PackedReviewerRankKind.blocksPerSuper,
              packedSelectSparseRankWordSize_eq shape,
              packedSelectSparseRankBlocksPerSuper_eq shape] using hs)
          (by
            simpa [data, q, packedReviewerRankQueryPos,
              PackedReviewerRankKind.wordSize,
              packedSelectSparseRankWordSize_eq shape] using hb)
      simpa [q, data, PackedReviewerRankKind.wordSize,
        packedSelectSparseRankWordSize_eq shape] using hsum
  | close =>
      let data := builtRelativeSplitBPCloseRankData shape
      have hq : q <= shape.bpCode.length := by
        have hmin := Nat.min_le_right pos (2 * shape.size)
        simpa [q, packedReviewerRankQueryPos,
          PackedReviewerRankKind.bitLength, CartesianShape.bpCode_length shape]
          using hmin
      have hs := hsuper
      rw [show PackedReviewerRankKind.close.superSegment =
          concreteBPNativeRankCloseTraceSegmentBase by rfl,
        concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper] at hs
      have hb := hblock
      rw [show PackedReviewerRankKind.close.blockSegment =
          concreteBPNativeRankCloseTraceSegmentBase + 1 by rfl,
        concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseBlock] at hb
      have hsum :=
        twoLevelRankData_decoded_samples_add_le data false q super delta hq
          (by
            simpa [data, q, packedReviewerRankQueryPos,
              PackedReviewerRankKind.wordSize,
              PackedReviewerRankKind.blocksPerSuper,
              packedCloseRankWordSize_eq shape,
              packedCloseRankBlocksPerSuper_eq shape] using hs)
          (by
            simpa [data, q, packedReviewerRankQueryPos,
              PackedReviewerRankKind.wordSize,
              packedCloseRankWordSize_eq shape] using hb)
      simpa [q, data, PackedReviewerRankKind.wordSize,
        packedCloseRankWordSize_eq shape] using hsum

private theorem packedReviewerCanonicalRankChunkReply_exact
    (shape : CartesianShape) (word : List Bool)
    (effectiveLimit j : Nat) :
    let c := packedFringeChunkBits shape.size
    let value := SuccinctClose.bpFringeWindowChunkValue c word j
    let sliceLen := SuccinctClose.bpWordChunkSliceLen c effectiveLimit j
    let slot := SuccinctClose.bpFringeChunkSlot c value sliceLen sliceLen
    packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 slot) =
      some (SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen) := by
  dsimp only
  unfold packedReviewerDecodeNat
  rw [show (21 : Nat) = concreteBPNativeFringeChunkTraceSegment by rfl]
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable]
  rw [packedFringeChunkBits_eq]
  rw [(SuccinctClose.bpFringeChunkTable
    (packedFringeChunkBits shape.size)).read_exact]
  exact SuccinctClose.bpFringeChunkEntries_getElem
    (SuccinctClose.bpFringeWindowChunkValue_lt
      (packedFringeChunkBits shape.size) word j)
    (SuccinctClose.bpWordChunkSliceLen_le
      (packedFringeChunkBits shape.size) effectiveLimit j)
    (SuccinctClose.bpWordChunkSliceLen_le
      (packedFringeChunkBits shape.size) effectiveLimit j)

/-- Start a Rank fold from any explicitly fitting decreasing envelope. -/
theorem packedReviewerRankStartFold_canonicalScalarFits
    (shape : CartesianShape) (resultBound : Nat)
    (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (word : List Bool)
    (limit base : Nat)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hword : PackedReviewerWordFits shape.size word)
    (hresultBound :
      base + SuccinctClose.bpWordRankEffLimit word limit <= resultBound)
    (hbudget :
      PackedReviewerNatFits shape.size
        (base +
          SuccinctClose.bpWordChunkCount (packedFringeChunkBits shape.size)
              (SuccinctClose.bpWordRankEffLimit word limit) *
            packedFringeChunkBits shape.size)) :
    PackedReviewerRankCanonicalScalarFits shape resultBound
      (packedReviewerRankStartFold invocation kind shape.size word limit base) := by
  let effectiveLimit := SuccinctClose.bpWordRankEffLimit word limit
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits shape.size)
      effectiveLimit
  have heffective : effectiveLimit <= word.length := by
    exact Nat.min_le_right _ _
  have hcount : count <= 8 :=
    SuccinctClose.bpWordChunkCount_le_eight _ _
  change PackedReviewerRankCanonicalScalarFits shape resultBound
    (if count = 0 then .done base else
      .fold invocation kind shape.size word effectiveLimit 0 count 0 base)
  split
  · have hzero : count = 0 := by assumption
    have hbase : PackedReviewerNatFits shape.size base := by
      exact Nat.lt_of_le_of_lt (by omega) hbudget
    refine ⟨hbase, ?_⟩
    have := hresultBound
    omega
  · refine ⟨rfl, hinvocation, hword, heffective, ?_, ?_, ?_, ?_⟩
    · simpa [count] using hcount
    · simpa [count, effectiveLimit] using hbudget
    · simp
    · simpa [effectiveLimit] using hresultBound

private theorem PackedReviewerRankKind.bitLength_le_two_mul
    (kind : PackedReviewerRankKind) (n : Nat) :
    kind.bitLength n <= 2 * n := by
  cases kind with
  | selectLong =>
      have hslots := packedSuperSlots_le_input n
      simpa [PackedReviewerRankKind.bitLength] using
        Nat.le_trans hslots (by omega : n <= 2 * n)
  | selectSparse =>
      have hslots := packedSparseSlots_le_input n
      simpa [PackedReviewerRankKind.bitLength] using
        Nat.le_trans hslots (by omega : n <= 2 * n)
  | close => simp [PackedReviewerRankKind.bitLength]

/-- One exact canonical-store Rank reply preserves the scalar invariant. -/
theorem PackedReviewerRankCanonicalScalarFits.consume
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerRankState}
    {request : PackedReviewerLogicalRequest}
    (hstate : PackedReviewerRankCanonicalScalarFits shape resultBound state)
    (hrequest : packedReviewerRankNextRequest state = some request) :
    PackedReviewerRankCanonicalScalarFits shape resultBound
      (packedReviewerRankConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases state with
  | superSample invocation kind n pos =>
      rcases hstate with ⟨rfl, hinvocation, hpos, hbound⟩
      simp only [packedReviewerRankNextRequest, Option.some.injEq] at hrequest
      subst request
      exact ⟨rfl, hinvocation, hpos, hbound, rfl⟩
  | blockSample invocation kind n pos superSample =>
      rcases hstate with ⟨rfl, hinvocation, hpos, hbound, hsuper⟩
      simp only [packedReviewerRankNextRequest, Option.some.injEq] at hrequest
      subst request
      exact ⟨rfl, hinvocation, hpos, hbound, hsuper, rfl⟩
  | word invocation kind n pos superSample blockSample =>
      rcases hstate with
        ⟨rfl, hinvocation, hpos, hbound, hsuper, hblock⟩
      simp only [packedReviewerRankNextRequest, Option.some.injEq] at hrequest
      subst request
      cases superSample with
      | none =>
          refine ⟨?_, by omega⟩
          simpa [packedReviewerRankConsumeReply] using
            packedReviewerFixedScalar_fits shape.size 0 (by omega)
      | some super =>
          cases blockSample with
          | none =>
              refine ⟨?_, by omega⟩
              simpa [packedReviewerRankConsumeReply] using
                packedReviewerFixedScalar_fits shape.size 0 (by omega)
          | some delta =>
              cases hread :
                  (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                    kind.wordSegment
                    (packedReviewerRankQueryPos kind shape.size pos /
                      kind.wordSize shape.size) with
              | none =>
                  refine ⟨?_, by omega⟩
                  simpa [packedReviewerRankConsumeReply, hread] using
                    packedReviewerFixedScalar_fits shape.size 0 (by omega)
              | some word =>
                  let request : PackedReviewerLogicalRequest :=
                    { invocation := invocation, site := .rankWord,
                      segment := kind.wordSegment,
                      index :=
                        packedReviewerRankQueryPos kind shape.size pos /
                          kind.wordSize shape.size }
                  have hword : PackedReviewerWordFits shape.size word :=
                    packedReviewerGlobalReadStore_word_fits shape request word
                      (by simpa [request] using hread)
                  have hsamples : super + delta <=
                      (packedReviewerRankQueryPos kind shape.size pos /
                        kind.wordSize shape.size) * kind.wordSize shape.size :=
                    packedReviewerRankCanonicalSamples_add_le shape kind pos
                      super delta (by simpa using hsuper.symm)
                      (by simpa using hblock.symm)
                  let effectiveLimit :=
                    SuccinctClose.bpWordRankEffLimit word
                      (packedReviewerRankQueryPos kind shape.size pos -
                        packedReviewerRankQueryPos kind shape.size pos /
                            kind.wordSize shape.size * kind.wordSize shape.size)
                  let count :=
                    SuccinctClose.bpWordChunkCount
                      (packedFringeChunkBits shape.size) effectiveLimit
                  have hcount : count <= 8 :=
                    SuccinctClose.bpWordChunkCount_le_eight _ _
                  have hwordStart :
                      (packedReviewerRankQueryPos kind shape.size pos /
                          kind.wordSize shape.size) * kind.wordSize shape.size <=
                        packedReviewerRankQueryPos kind shape.size pos :=
                    Nat.div_mul_le_self _ _
                  have hqBitLength :
                      packedReviewerRankQueryPos kind shape.size pos <=
                        kind.bitLength shape.size :=
                    Nat.min_le_right _ _
                  have hbase : super + delta <= 2 * shape.size :=
                    Nat.le_trans hsamples (Nat.le_trans hwordStart
                      (Nat.le_trans hqBitLength
                        (PackedReviewerRankKind.bitLength_le_two_mul kind
                          shape.size)))
                  have heffective : effectiveLimit <=
                      packedReviewerRankQueryPos kind shape.size pos -
                        (packedReviewerRankQueryPos kind shape.size pos /
                          kind.wordSize shape.size) * kind.wordSize shape.size :=
                    Nat.min_le_left _ _
                  have hresultBound :
                      super + delta + effectiveLimit <= resultBound := by
                    rw [hbound]
                    omega
                  have hbudget :
                      PackedReviewerNatFits shape.size
                        (super + delta +
                          count * packedFringeChunkBits shape.size) :=
                    packedReviewerRankEnvelope_fits shape.size
                      (super + delta) count hbase hcount
                  simpa [packedReviewerRankConsumeReply, hread, effectiveLimit,
                    count] using
                    packedReviewerRankStartFold_canonicalScalarFits shape
                      resultBound invocation kind word
                      (packedReviewerRankQueryPos kind shape.size pos -
                        packedReviewerRankQueryPos kind shape.size pos /
                            kind.wordSize shape.size * kind.wordSize shape.size)
                      (super + delta) hinvocation hword hresultBound hbudget
  | fold invocation kind n word effectiveLimit j remaining acc base =>
      rcases hstate with
        ⟨rfl, hinvocation, hword, heffective, hcounters, henvelope,
          hprogress, hresultBound⟩
      cases remaining with
      | zero => simp [packedReviewerRankNextRequest] at hrequest
      | succ remaining =>
          let c := packedFringeChunkBits shape.size
          let value := SuccinctClose.bpFringeWindowChunkValue c word j
          let sliceLen := SuccinctClose.bpWordChunkSliceLen c effectiveLimit j
          let slot := SuccinctClose.bpFringeChunkSlot c value sliceLen sliceLen
          simp only [packedReviewerRankNextRequest, Option.some.injEq] at hrequest
          subst request
          have hexact :=
            packedReviewerCanonicalRankChunkReply_exact shape word
              effectiveLimit j
          have hrankEq :
              SuccinctClose.bpChunkRankOfEntry c kind.target sliceLen
                  (SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen) =
                Succinct.rankPrefix kind.target
                  (SuccinctClose.bpFringeChunkPattern c value) sliceLen := by
            exact SuccinctClose.bpChunkRankOfEntry_packed c kind.target
              (SuccinctClose.bpFringeWindowChunkValue_lt c word j)
              (SuccinctClose.bpWordChunkSliceLen_le c effectiveLimit j)
          have hrankLe :
              SuccinctClose.bpChunkRankOfEntry c kind.target sliceLen
                  (SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen) <=
                c := by
            rw [hrankEq]
            exact Nat.le_trans
              (Succinct.rankPrefix_le_limit kind.target
                (SuccinctClose.bpFringeChunkPattern c value) sliceLen)
              (SuccinctClose.bpWordChunkSliceLen_le c effectiveLimit j)
          have hrankSlice :
              SuccinctClose.bpChunkRankOfEntry c kind.target sliceLen
                  (SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen) <=
                Nat.min c (effectiveLimit - j * c) := by
            rw [hrankEq]
            simpa [sliceLen, SuccinctClose.bpWordChunkSliceLen] using
              (Succinct.rankPrefix_le_limit kind.target
                (SuccinctClose.bpFringeChunkPattern c value) sliceLen)
          let acc' :=
            SuccinctClose.bpWordRankStepDecoded c kind.target sliceLen acc
              (some
                (SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen))
          have hnextEnvelope :
              PackedReviewerNatFits shape.size
                (base + acc' + remaining * c) := by
            have hstep :
                base + acc' + remaining * c <=
                  base + acc + (remaining + 1) * c := by
              simp [acc', SuccinctClose.bpWordRankStepDecoded, Nat.add_mul]
              omega
            exact Nat.lt_of_le_of_lt hstep (by simpa [c] using henvelope)
          have hnextProgress :
              acc' <= Nat.min ((j + 1) * c) effectiveLimit := by
            apply packedReviewerRankProgress_step c effectiveLimit j acc
            · simpa [c] using hprogress
            · simpa [acc', SuccinctClose.bpWordRankStepDecoded] using
                hrankSlice
          by_cases hlast : remaining = 0
          · subst remaining
            have hdone :
                PackedReviewerRankCanonicalScalarFits shape resultBound
                  (.done (base + acc')) := by
              refine ⟨by simpa [c] using hnextEnvelope, ?_⟩
              have haccEffective :=
                Nat.le_trans hnextProgress (Nat.min_le_right _ _)
              omega
            simpa [packedReviewerRankConsumeReply, c, value, sliceLen, slot,
              hexact, acc'] using hdone
          · have hout :
                PackedReviewerRankCanonicalScalarFits shape resultBound
                  (.fold invocation kind shape.size word effectiveLimit
                    (j + 1) remaining acc' base) :=
              ⟨rfl, hinvocation, hword, heffective, by omega,
                by simpa [c] using hnextEnvelope,
                by simpa [c] using hnextProgress, hresultBound⟩
            simpa [packedReviewerRankConsumeReply, c, value, sliceLen,
              slot, hexact, acc', hlast] using hout
  | done value => simp [packedReviewerRankNextRequest] at hrequest

/-- A completed canonical Rank state exposes a fitting result scalar. -/
theorem PackedReviewerRankCanonicalScalarFits.result_fits
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerRankState} {value : Nat}
    (hstate : PackedReviewerRankCanonicalScalarFits shape resultBound state)
    (hresult : packedReviewerRankResult state = some value) :
    PackedReviewerNatFits shape.size value ∧ value <= resultBound := by
  cases state with
  | superSample invocation kind n pos =>
      simp [packedReviewerRankResult] at hresult
  | blockSample invocation kind n pos sample =>
      simp [packedReviewerRankResult] at hresult
  | word invocation kind n pos superSample blockSample =>
      simp [packedReviewerRankResult] at hresult
  | fold invocation kind n word effectiveLimit j remaining acc base =>
      simp [packedReviewerRankResult] at hresult
  | done stored =>
      have heq : stored = value := by
        simpa [packedReviewerRankResult] using Option.some.inj hresult
      subst value
      exact hstate

/-! ## WordSelect -/

private theorem packedReviewerCanonicalWordSelectValueReply_exact
    (shape : CartesianShape) (word : List Bool) (j occurrence : Nat)
    (hoccurrence : occurrence <= packedFringeChunkBits shape.size) :
    let c := packedFringeChunkBits shape.size
    let value := SuccinctClose.bpFringeWindowChunkValue c word j
    let slot := SuccinctClose.bpChunkSelectSlot c value occurrence
    packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 22 slot) =
      some (SuccinctClose.bpChunkSelectPos c false value occurrence) := by
  dsimp only
  unfold packedReviewerDecodeNat
  rw [show (22 : Nat) = concreteBPNativeSelectChunkTraceSegment by rfl]
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_selectChunkTable]
  rw [packedFringeChunkBits_eq]
  rw [(SuccinctClose.bpChunkSelectTable
    (packedFringeChunkBits shape.size) false).read_exact]
  exact SuccinctClose.bpChunkSelectEntries_getElem false
    (SuccinctClose.bpFringeWindowChunkValue_lt
      (packedFringeChunkBits shape.size) word j)
    hoccurrence

private theorem packedReviewerChunkSelectPos_lt_slice
    (c : Nat) (word : List Bool) (j occurrence : Nat)
    (hfound :
      occurrence <
        Succinct.rankPrefix false
          (SuccinctClose.bpFringeChunkPattern c
            (SuccinctClose.bpFringeWindowChunkValue c word j))
          (SuccinctClose.bpWordChunkSliceLen c word.length j)) :
    SuccinctClose.bpChunkSelectPos c false
        (SuccinctClose.bpFringeWindowChunkValue c word j) occurrence <
      SuccinctClose.bpWordChunkSliceLen c word.length j := by
  rcases GenericSelect.select_exists_of_lt_rankPrefix hfound with
    ⟨pos, hselect⟩
  have hpos : pos < SuccinctClose.bpWordChunkSliceLen c word.length j := by
    by_cases hlt : pos < SuccinctClose.bpWordChunkSliceLen c word.length j
    · exact hlt
    · exfalso
      have hrankLe :=
        Succinct.rankPrefix_le_occurrence_of_le_select hselect
          (Nat.le_of_not_gt hlt)
      omega
  simpa [SuccinctClose.bpChunkSelectPos, hselect] using hpos

/--
Canonical scalar invariant for the only globally stored select-chunk table,
whose target is `false`.  A `selectChunk` state retains the strict found test;
this excludes the table's sentinel and yields a result inside the source word.
-/
def PackedReviewerWordSelectCanonicalScalarFits
    (shape : CartesianShape) (resultBound : Nat) :
    PackedReviewerWordSelectState -> Prop
  | .rankChunk invocation n target word j remaining occurrence =>
      n = shape.size ∧ target = false ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerWordFits shape.size word ∧
            resultBound = word.length ∧ j + remaining <= 8 ∧
              PackedReviewerNatFits shape.size occurrence
  | .selectChunk invocation n target word j remaining occurrence =>
      n = shape.size ∧ target = false ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerWordFits shape.size word ∧
            resultBound = word.length ∧ j + remaining <= 8 ∧
              PackedReviewerNatFits shape.size occurrence ∧
                occurrence <
                  Succinct.rankPrefix false
                    (SuccinctClose.bpFringeChunkPattern
                      (packedFringeChunkBits shape.size)
                      (SuccinctClose.bpFringeWindowChunkValue
                        (packedFringeChunkBits shape.size) word j))
                    (SuccinctClose.bpWordChunkSliceLen
                      (packedFringeChunkBits shape.size) word.length j)
  | .done none => True
  | .done (some value) =>
      PackedReviewerNatFits shape.size value ∧ value < resultBound

theorem PackedReviewerWordSelectCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerWordSelectState}
    (hstate :
      PackedReviewerWordSelectCanonicalScalarFits shape resultBound state) :
    forall value,
      value ∈ packedReviewerWordSelectStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  cases state with
  | rankChunk invocation n target word j remaining occurrence =>
      rcases hstate with
        ⟨rfl, rfl, hinvocation, hword, hbound, hcounters, hoccurrence⟩
      intro value hmem
      simp [packedReviewerWordSelectStateNatFields] at hmem
      rcases hmem with hinvocationField | rfl | rfl | rfl | rfl
      · exact hinvocation.nat_fields value hinvocationField
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · exact hoccurrence
  | selectChunk invocation n target word j remaining occurrence =>
      rcases hstate with
        ⟨rfl, rfl, hinvocation, hword, hbound, hcounters, hoccurrence,
          hfound⟩
      intro value hmem
      simp [packedReviewerWordSelectStateNatFields] at hmem
      rcases hmem with hinvocationField | rfl | rfl | rfl | rfl
      · exact hinvocation.nat_fields value hinvocationField
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · exact hoccurrence
  | done result =>
      cases result with
      | none =>
          intro value hmem
          simp [packedReviewerWordSelectStateNatFields,
            packedReviewerOptionNatFields] at hmem
      | some stored =>
          intro value hmem
          simp [packedReviewerWordSelectStateNatFields,
            packedReviewerOptionNatFields] at hmem
          subst value
          exact hstate.1

theorem packedReviewerWordSelectStart_canonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (target : Bool) (word : List Bool) (occurrence : Nat)
    (htarget : target = false)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hword : PackedReviewerWordFits shape.size word)
    (hoccurrence : PackedReviewerNatFits shape.size occurrence) :
    PackedReviewerWordSelectCanonicalScalarFits shape word.length
      (packedReviewerWordSelectStart invocation shape.size target word
        occurrence) := by
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits shape.size)
      word.length
  have hcount : count <= 8 :=
    SuccinctClose.bpWordChunkCount_le_eight _ _
  change PackedReviewerWordSelectCanonicalScalarFits shape word.length
    (if count = 0 then .done none else
      .rankChunk invocation shape.size target word 0 count occurrence)
  split
  · trivial
  · exact ⟨rfl, htarget, hinvocation, hword, rfl,
      by simpa [count] using hcount, hoccurrence⟩

theorem PackedReviewerWordSelectCanonicalScalarFits.consume
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerWordSelectState}
    {request : PackedReviewerLogicalRequest}
    (hstate :
      PackedReviewerWordSelectCanonicalScalarFits shape resultBound state)
    (hrequest : packedReviewerWordSelectNextRequest state = some request) :
    PackedReviewerWordSelectCanonicalScalarFits shape resultBound
      (packedReviewerWordSelectConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases state with
  | rankChunk invocation n target word j remaining occurrence =>
      rcases hstate with
        ⟨rfl, rfl, hinvocation, hword, hbound, hcounters, hoccurrence⟩
      cases remaining with
      | zero => simp [packedReviewerWordSelectNextRequest] at hrequest
      | succ remaining =>
          let c := packedFringeChunkBits shape.size
          let value := SuccinctClose.bpFringeWindowChunkValue c word j
          let sliceLen := SuccinctClose.bpWordChunkSliceLen c word.length j
          let slot := SuccinctClose.bpFringeChunkSlot c value sliceLen sliceLen
          simp only [packedReviewerWordSelectNextRequest,
            Option.some.injEq] at hrequest
          subst request
          have hexact :=
            packedReviewerCanonicalRankChunkReply_exact shape word word.length j
          have hrankEq :
              SuccinctClose.bpChunkRankOfEntry c false sliceLen
                  (SuccinctClose.bpFringeChunkPacked c value sliceLen sliceLen) =
                Succinct.rankPrefix false
                  (SuccinctClose.bpFringeChunkPattern c value) sliceLen :=
            SuccinctClose.bpChunkRankOfEntry_packed c false
              (SuccinctClose.bpFringeWindowChunkValue_lt c word j)
              (SuccinctClose.bpWordChunkSliceLen_le c word.length j)
          let rank := Succinct.rankPrefix false
            (SuccinctClose.bpFringeChunkPattern c value) sliceLen
          by_cases hfound : occurrence < rank
          · have hout :
                PackedReviewerWordSelectCanonicalScalarFits shape resultBound
                  (.selectChunk invocation shape.size false word j
                    (remaining + 1) occurrence) :=
              ⟨rfl, rfl, hinvocation, hword, hbound, hcounters,
                hoccurrence, by simpa [rank] using hfound⟩
            simpa [packedReviewerWordSelectConsumeReply, c, value, sliceLen,
              slot, hexact, hrankEq, rank, hfound] using hout
          · by_cases hlast : remaining = 0
            · subst remaining
              have hout :
                  PackedReviewerWordSelectCanonicalScalarFits shape resultBound
                    (.done none) := trivial
              simpa [packedReviewerWordSelectConsumeReply, c, value, sliceLen,
                slot, hexact, hrankEq, rank, hfound] using hout
            · have hoccurrence' :
                  PackedReviewerNatFits shape.size (occurrence - rank) :=
                Nat.lt_of_le_of_lt (Nat.sub_le _ _) hoccurrence
              have hout :
                  PackedReviewerWordSelectCanonicalScalarFits shape resultBound
                    (.rankChunk invocation shape.size false word (j + 1)
                      remaining (occurrence - rank)) :=
                ⟨rfl, rfl, hinvocation, hword, hbound, by omega,
                  hoccurrence'⟩
              simpa [packedReviewerWordSelectConsumeReply, c, value, sliceLen,
                slot, hexact, hrankEq, rank, hfound, hlast] using hout
  | selectChunk invocation n target word j remaining occurrence =>
      rcases hstate with
        ⟨rfl, rfl, hinvocation, hword, hbound, hcounters, hoccurrence,
          hfound⟩
      let c := packedFringeChunkBits shape.size
      let value := SuccinctClose.bpFringeWindowChunkValue c word j
      let sliceLen := SuccinctClose.bpWordChunkSliceLen c word.length j
      let slot := SuccinctClose.bpChunkSelectSlot c value occurrence
      simp only [packedReviewerWordSelectNextRequest,
        Option.some.injEq] at hrequest
      subst request
      have hfound' :
          occurrence < Succinct.rankPrefix false
            (SuccinctClose.bpFringeChunkPattern c value) sliceLen := by
        simpa [c, value, sliceLen] using hfound
      have hrankLe := Succinct.rankPrefix_le_limit false
        (SuccinctClose.bpFringeChunkPattern c value) sliceLen
      have hsliceLe := SuccinctClose.bpWordChunkSliceLen_le c word.length j
      have hoccurrenceC : occurrence <= c := by omega
      have hexact :=
        packedReviewerCanonicalWordSelectValueReply_exact shape word j
          occurrence (by simpa [c] using hoccurrenceC)
      have hpos :=
        packedReviewerChunkSelectPos_lt_slice c word j occurrence
          (by simpa [value, sliceLen] using hfound')
      have hpos' :
          SuccinctClose.bpChunkSelectPos c false value occurrence <
            sliceLen := by
        simpa [value, sliceLen] using hpos
      have hsliceTail : sliceLen <= word.length - j * c :=
        Nat.min_le_right _ _
      have hresultWord :
          j * c + SuccinctClose.bpChunkSelectPos c false value occurrence <
            word.length := by
        omega
      have hresult :
          j * c + SuccinctClose.bpChunkSelectPos c false value occurrence <
            resultBound := by
        rw [hbound]
        exact hresultWord
      have hfit :
          PackedReviewerNatFits shape.size
            (j * c + SuccinctClose.bpChunkSelectPos c false value occurrence) :=
        Nat.lt_trans hresultWord
          hword.length_scalar_fits
      have hout :
          PackedReviewerWordSelectCanonicalScalarFits shape resultBound
            (.done (some
              (j * c +
                SuccinctClose.bpChunkSelectPos c false value occurrence))) :=
        ⟨hfit, hresult⟩
      simpa [packedReviewerWordSelectConsumeReply, c, value, sliceLen, slot,
        hexact] using hout
  | done result => simp [packedReviewerWordSelectNextRequest] at hrequest

theorem PackedReviewerWordSelectCanonicalScalarFits.result_fits
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerWordSelectState} {value : Nat}
    (hstate :
      PackedReviewerWordSelectCanonicalScalarFits shape resultBound state)
    (hresult : packedReviewerWordSelectResult state = some (some value)) :
    PackedReviewerNatFits shape.size value ∧ value < resultBound := by
  cases state with
  | rankChunk invocation n target word j remaining occurrence =>
      simp [packedReviewerWordSelectResult] at hresult
  | selectChunk invocation n target word j remaining occurrence =>
      simp [packedReviewerWordSelectResult] at hresult
  | done result =>
      cases result with
      | none => simp [packedReviewerWordSelectResult] at hresult
      | some stored =>
          have heq : stored = value := by
            simpa [packedReviewerWordSelectResult] using Option.some.inj hresult
          subst value
          exact hstate

/-! ## Fringe -/

def PackedReviewerCandidateWithin
    (bound : Nat) : Option (Nat × Nat) -> Prop
  | none => True
  | some candidate => candidate.1 <= bound ∧ candidate.2 <= bound

private theorem PackedReviewerCandidateWithin.merge
    {bound : Nat} {left right : Option (Nat × Nat)}
    (hleft : PackedReviewerCandidateWithin bound left)
    (hright : PackedReviewerCandidateWithin bound right) :
    PackedReviewerCandidateWithin bound
      (SuccinctClose.bpFringeMergeCand left right) := by
  cases left with
  | none => simpa [SuccinctClose.bpFringeMergeCand] using hright
  | some best =>
      cases right with
      | none => simpa [SuccinctClose.bpFringeMergeCand] using hleft
      | some candidate =>
          by_cases hbetter : candidate.1 < best.1
          · simpa [SuccinctClose.bpFringeMergeCand, hbetter] using hright
          · simpa [SuccinctClose.bpFringeMergeCand, hbetter] using hleft

private theorem PackedReviewerCandidateWithin.scalar_fields
    {shape : CartesianShape} {bound : Nat} {candidate : Option (Nat × Nat)}
    (hbound : PackedReviewerNatFits shape.size bound)
    (hcandidate : PackedReviewerCandidateWithin bound candidate) :
    forall value,
      value ∈ packedReviewerCandidateNatFields candidate ->
        PackedReviewerNatFits shape.size value := by
  cases candidate with
  | none => simp [packedReviewerCandidateNatFields]
  | some candidate =>
      intro value hmem
      simp [packedReviewerCandidateNatFields] at hmem
      rcases hmem with rfl | rfl
      · exact Nat.lt_of_le_of_lt hcandidate.1 hbound
      · exact Nat.lt_of_le_of_lt hcandidate.2 hbound

private theorem packedReviewerCanonicalFringeReply_exact
    (shape : CartesianShape) (window : List Bool)
    (relLo relHi j : Nat) :
    let c := packedFringeChunkBits shape.size
    let value := SuccinctClose.bpFringeWindowChunkValue c window j
    let startOff := SuccinctClose.bpFringeChunkStartOff c relLo j
    let endOff := SuccinctClose.bpFringeChunkEndOff c relHi j
    let slot := SuccinctClose.bpFringeChunkSlot c value startOff endOff
    packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 slot) =
      some
        (SuccinctClose.bpFringeChunkPacked c value startOff endOff) := by
  dsimp only
  unfold packedReviewerDecodeNat
  rw [show (21 : Nat) = concreteBPNativeFringeChunkTraceSegment by rfl]
  rw [concreteBPNativeSuccinctRMQGlobalReadStore_fringeChunkTable]
  rw [packedFringeChunkBits_eq]
  rw [(SuccinctClose.bpFringeChunkTable
    (packedFringeChunkBits shape.size)).read_exact]
  exact SuccinctClose.bpFringeChunkEntries_getElem
    (SuccinctClose.bpFringeWindowChunkValue_lt
      (packedFringeChunkBits shape.size) window j)
    (SuccinctClose.bpFringeChunkStartOff_le
      (packedFringeChunkBits shape.size) relLo j)
    (SuccinctClose.bpFringeChunkEndOff_le
      (packedFringeChunkBits shape.size) relHi j)

private theorem packedReviewerFringeStep_bounds
    (c relLo relHi j acc bound : Nat) (window : List Bool)
    (candidate : Option (Nat × Nat))
    (hacc : acc + c <= bound) (hindex : (j + 1) * c <= bound)
    (hcandidate : PackedReviewerCandidateWithin bound candidate) :
    let value := SuccinctClose.bpFringeWindowChunkValue c window j
    let startOff := SuccinctClose.bpFringeChunkStartOff c relLo j
    let endOff := SuccinctClose.bpFringeChunkEndOff c relHi j
    let next :=
      SuccinctClose.bpFringeChunkStepDecoded c relLo relHi j
        (acc, candidate)
        (some
          (SuccinctClose.bpFringeChunkPacked c value startOff endOff))
    next.1 <= acc + c ∧ PackedReviewerCandidateWithin bound next.2 := by
  dsimp only
  let value := SuccinctClose.bpFringeWindowChunkValue c window j
  let startOff := SuccinctClose.bpFringeChunkStartOff c relLo j
  let endOff := SuccinctClose.bpFringeChunkEndOff c relHi j
  have hstart : startOff <= c :=
    SuccinctClose.bpFringeChunkStartOff_le c relLo j
  have hend : endOff <= c :=
    SuccinctClose.bpFringeChunkEndOff_le c relHi j
  have hdelta := SuccinctClose.bpFringeChunkPacked_delta c value hstart hend
  have hmin := SuccinctClose.bpFringeChunkPacked_min c value hstart hend
  have harg := SuccinctClose.bpFringeChunkPacked_arg c value hstart hend
  have hdeltaLe := SuccinctClose.bpFringeChunkDeltaOffset_le c value
  have hminLe := SuccinctClose.bpFringeChunkMinOffset_le c value startOff endOff
  have hargLe := SuccinctClose.bpFringeChunkArgMin_le c value hstart hend
  have haccNext :
      acc + SuccinctClose.bpFringeChunkDeltaOffset c value - c <= acc + c := by
    omega
  have hnewCandidate :
      PackedReviewerCandidateWithin bound
        (if startOff < endOff then
          some
            (acc + SuccinctClose.bpFringeChunkMinOffset c value startOff endOff - c,
              j * c +
                SuccinctClose.bpFringeChunkArgMin c value startOff endOff)
        else none) := by
    split
    · constructor
      · omega
      · rw [Nat.add_mul] at hindex
        omega
    · trivial
  constructor
  · simpa [SuccinctClose.bpFringeChunkStepDecoded, value, startOff, endOff,
      hdelta] using haccNext
  · simpa [SuccinctClose.bpFringeChunkStepDecoded, value, startOff, endOff,
      hdelta, hmin, harg] using
      hcandidate.merge hnewCandidate

/-- Scalar result envelope exposed by a completed fringe fold. -/
def PackedReviewerFringeResultScalarFits
    (shape : CartesianShape) (resultBound : Nat)
    (result : Nat × Option (Nat × Nat)) : Prop :=
  PackedReviewerNatFits shape.size resultBound ∧
    result.1 <= resultBound ∧
      PackedReviewerCandidateWithin resultBound result.2

def PackedReviewerFringeCanonicalScalarFits
    (shape : CartesianShape) (resultBound : Nat) :
    PackedReviewerFringeState -> Prop
  | .chunk invocation n _window relLo relHi j remaining (acc, candidate) =>
      n = shape.size ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerNatFits shape.size relLo ∧
            PackedReviewerNatFits shape.size relHi ∧
              j + remaining <= 33 ∧
                PackedReviewerNatFits shape.size resultBound ∧
                  acc + remaining * packedFringeChunkBits shape.size <=
                    resultBound ∧
                  (j + remaining) * packedFringeChunkBits shape.size <=
                    resultBound ∧
                  PackedReviewerCandidateWithin resultBound candidate
  | .done result =>
      PackedReviewerFringeResultScalarFits shape resultBound result

theorem PackedReviewerFringeCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerFringeState}
    (hstate : PackedReviewerFringeCanonicalScalarFits shape resultBound state) :
    forall value,
      value ∈ packedReviewerFringeStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  cases state with
  | chunk invocation n window relLo relHi j remaining foldState =>
      rcases foldState with ⟨acc, candidate⟩
      rcases hstate with
        ⟨rfl, hinvocation, hrelLo, hrelHi, hcounters, hbound,
          hacc, hgeometry, hcandidate⟩
      intro value hmem
      simp [packedReviewerFringeStateNatFields] at hmem
      rcases hmem with hinvocationField | rfl | rfl | rfl | rfl | rfl |
        rfl | hcandidateField
      · exact hinvocation.nat_fields value hinvocationField
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hrelLo
      · exact hrelHi
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
      · have haccLe : value <= resultBound :=
          Nat.le_trans (Nat.le_add_right value
            (remaining * packedFringeChunkBits shape.size)) hacc
        exact Nat.lt_of_le_of_lt haccLe hbound
      · exact hcandidate.scalar_fields hbound value hcandidateField
  | done result =>
      rcases result with ⟨acc, candidate⟩
      rcases hstate with ⟨hbound, hacc, hcandidate⟩
      intro value hmem
      simp [packedReviewerFringeStateNatFields] at hmem
      rcases hmem with rfl | hcandidateField
      · exact Nat.lt_of_le_of_lt hacc hbound
      · exact hcandidate.scalar_fields hbound value hcandidateField

theorem packedReviewerFringeStart_canonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (window : List Bool) (seed relLo relHi count : Nat)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hrelLo : PackedReviewerNatFits shape.size relLo)
    (hrelHi : PackedReviewerNatFits shape.size relHi)
    (hcount : count <= 33)
    (hbudget :
      PackedReviewerNatFits shape.size
        (seed + count * packedFringeChunkBits shape.size)) :
    PackedReviewerFringeCanonicalScalarFits shape
      (seed + count * packedFringeChunkBits shape.size)
      (packedReviewerFringeStart invocation shape.size window seed relLo relHi
        count) := by
  let bound := seed + count * packedFringeChunkBits shape.size
  change PackedReviewerFringeCanonicalScalarFits shape bound
    (if count = 0 then .done (seed, none) else
      .chunk invocation shape.size window relLo relHi 0 count (seed, none))
  split
  · refine ⟨by simpa [bound] using hbudget, ?_, trivial⟩
    simp [bound]
  · exact ⟨rfl, hinvocation, hrelLo, hrelHi, by simpa using hcount,
      by simpa [bound] using hbudget, by simp [bound], by simp [bound],
      trivial⟩

theorem PackedReviewerFringeCanonicalScalarFits.consume
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerFringeState}
    {request : PackedReviewerLogicalRequest}
    (hstate : PackedReviewerFringeCanonicalScalarFits shape resultBound state)
    (hrequest : packedReviewerFringeNextRequest state = some request) :
    PackedReviewerFringeCanonicalScalarFits shape resultBound
      (packedReviewerFringeConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases state with
  | chunk invocation n window relLo relHi j remaining foldState =>
      rcases foldState with ⟨acc, candidate⟩
      rcases hstate with
        ⟨rfl, hinvocation, hrelLo, hrelHi, hcounters, hbound,
          hacc, hgeometry, hcandidate⟩
      cases remaining with
      | zero => simp [packedReviewerFringeNextRequest] at hrequest
      | succ remaining =>
          let c := packedFringeChunkBits shape.size
          let value := SuccinctClose.bpFringeWindowChunkValue c window j
          let startOff := SuccinctClose.bpFringeChunkStartOff c relLo j
          let endOff := SuccinctClose.bpFringeChunkEndOff c relHi j
          let slot := SuccinctClose.bpFringeChunkSlot c value startOff endOff
          simp only [packedReviewerFringeNextRequest,
            Option.some.injEq] at hrequest
          subst request
          have hexact := packedReviewerCanonicalFringeReply_exact shape window
            relLo relHi j
          have hacc' : acc + (remaining + 1) * c <= resultBound := by
            simpa [c] using hacc
          have hgeometry' : (j + (remaining + 1)) * c <= resultBound := by
            simpa [c] using hgeometry
          have haccStep : acc + c <= resultBound := by
            rw [Nat.succ_mul] at hacc'
            omega
          have hindexStep : (j + 1) * c <= resultBound := by
            have hj : j + 1 <= j + (remaining + 1) := by omega
            exact Nat.le_trans (Nat.mul_le_mul_right c hj) hgeometry'
          have hstep := packedReviewerFringeStep_bounds c relLo relHi j acc
            resultBound window candidate haccStep hindexStep hcandidate
          let next :=
            SuccinctClose.bpFringeChunkStepDecoded c relLo relHi j
              (acc, candidate)
              (some
                (SuccinctClose.bpFringeChunkPacked c value startOff endOff))
          have hnextStep : next.1 <= acc + c := by
            simpa [next, value, startOff, endOff] using hstep.1
          have hnextAcc : next.1 <= resultBound :=
            Nat.le_trans hnextStep haccStep
          have hnextCandidate :
              PackedReviewerCandidateWithin resultBound next.2 := by
            simpa [next, value, startOff, endOff] using hstep.2
          by_cases hlast : remaining = 0
          · subst remaining
            have hout :
                PackedReviewerFringeCanonicalScalarFits shape resultBound
                  (.done next) := ⟨hbound, hnextAcc, hnextCandidate⟩
            simpa [packedReviewerFringeConsumeReply, c, value, startOff,
              endOff, slot, hexact, next] using hout
          · have hout :
                PackedReviewerFringeCanonicalScalarFits shape resultBound
                  (.chunk invocation shape.size window relLo relHi (j + 1)
                    remaining next) := by
              refine ⟨rfl, hinvocation, hrelLo, hrelHi, by omega, hbound,
                ?_, ?_, hnextCandidate⟩
              · have hnextEnvelope :
                    next.1 + remaining * c <= resultBound := by
                  rw [Nat.succ_mul] at hacc'
                  omega
                simpa [c] using hnextEnvelope
              · have hnextGeometry :
                    (j + 1 + remaining) * c <= resultBound := by
                  rw [show j + 1 + remaining = j + (remaining + 1) by omega]
                  exact hgeometry'
                simpa [c] using hnextGeometry
            simpa [packedReviewerFringeConsumeReply, c, value, startOff,
              endOff, slot, hexact, next, hlast] using hout
  | done result => simp [packedReviewerFringeNextRequest] at hrequest

theorem PackedReviewerFringeCanonicalScalarFits.result_fits
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerFringeState}
    {result : Nat × Option (Nat × Nat)}
    (hstate : PackedReviewerFringeCanonicalScalarFits shape resultBound state)
    (hresult : packedReviewerFringeResult state = some result) :
    PackedReviewerFringeResultScalarFits shape resultBound result := by
  cases state with
  | chunk invocation n window relLo relHi j remaining foldState =>
      simp [packedReviewerFringeResult] at hresult
  | done stored =>
      have heq : stored = result := by
        simpa [packedReviewerFringeResult] using Option.some.inj hresult
      subst result
      exact hstate

/-! ## BPWindow -/

private theorem packedReviewerAtomicFlattenPayloadWords_length_le
    (n : Nat) (words : List (List Bool))
    (hwords : forall word, word ∈ words -> PackedReviewerWordFits n word) :
    (SuccinctSpace.flattenPayloadWords words).length <=
      words.length * packedReviewerCellWidth n := by
  induction words with
  | nil => simp [SuccinctSpace.flattenPayloadWords]
  | cons word words ih =>
      have hword := hwords word List.mem_cons_self
      have htail :
          forall tail, tail ∈ words -> PackedReviewerWordFits n tail := by
        intro tail hmem
        exact hwords tail (List.mem_cons_of_mem word hmem)
      have hrec := ih htail
      have hwordLength : word.length <= packedReviewerCellWidth n := by
        simpa [PackedReviewerWordFits] using hword
      simp only [SuccinctSpace.flattenPayloadWords, List.length_append,
        List.length_cons]
      rw [Nat.add_mul]
      simp only [Nat.one_mul]
      omega

/--
Canonical scalar invariant for the four-read BP-window protocol.  The final
two clauses also retain the separately represented word-buffer bound and the
four-word bound on the assembled wide result; neither is treated as a scalar.
-/
def PackedReviewerBPWindowCanonicalScalarFits
    (shape : CartesianShape) : PackedReviewerBPWindowState -> Prop
  | .read invocation n blockSize close next wordsRev =>
      n = shape.size ∧
        PackedReviewerInvocationScalarFits shape invocation ∧
          PackedReviewerNatFits shape.size blockSize ∧
            PackedReviewerNatFits shape.size close ∧
              next <= 4 ∧
                wordsRev.length = next ∧
                  forall word, word ∈ wordsRev ->
                    PackedReviewerWordFits shape.size word
  | .done bits =>
      bits.length <= 4 * packedReviewerCellWidth shape.size

theorem PackedReviewerBPWindowCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {state : PackedReviewerBPWindowState}
    (hstate : PackedReviewerBPWindowCanonicalScalarFits shape state) :
    forall value,
      value ∈ packedReviewerBPWindowStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      rcases hstate with
        ⟨rfl, hinvocation, hblockSize, hclose, hnext, hlength, hwords⟩
      intro value hmem
      simp [packedReviewerBPWindowStateNatFields] at hmem
      rcases hmem with hinvocationField | rfl | rfl | rfl | rfl
      · exact hinvocation.nat_fields value hinvocationField
      · exact packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      · exact hblockSize
      · exact hclose
      · exact packedReviewerFixedScalar_fits shape.size value (by omega)
  | done bits =>
      simp [packedReviewerBPWindowStateNatFields]

theorem PackedReviewerBPWindowCanonicalScalarFits.word_fields
    {shape : CartesianShape} {state : PackedReviewerBPWindowState}
    (hstate : PackedReviewerBPWindowCanonicalScalarFits shape state) :
    forall word,
      word ∈ packedReviewerBPWindowStateWordFields state ->
        PackedReviewerWordFits shape.size word := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      intro word hmem
      exact hstate.2.2.2.2.2.2 word
        (by simpa [packedReviewerBPWindowStateWordFields] using hmem)
  | done bits =>
      simp [packedReviewerBPWindowStateWordFields]

theorem PackedReviewerBPWindowCanonicalScalarFits.wide_fields
    {shape : CartesianShape} {state : PackedReviewerBPWindowState}
    (hstate : PackedReviewerBPWindowCanonicalScalarFits shape state) :
    forall bits,
      bits ∈ packedReviewerBPWindowStateWideFields state ->
        bits.length <= 4 * packedReviewerCellWidth shape.size := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      simp [packedReviewerBPWindowStateWideFields]
  | done bits =>
      intro stored hmem
      simp [packedReviewerBPWindowStateWideFields] at hmem
      subst stored
      exact hstate

theorem packedReviewerBPWindowStart_canonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (blockSize close : Nat)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hblockSize : PackedReviewerNatFits shape.size blockSize)
    (hclose : PackedReviewerNatFits shape.size close) :
    PackedReviewerBPWindowCanonicalScalarFits shape
      (packedReviewerBPWindowStart invocation shape.size blockSize close) := by
  exact ⟨rfl, hinvocation, hblockSize, hclose, by omega, rfl, by simp⟩

theorem PackedReviewerBPWindowCanonicalScalarFits.consume
    {shape : CartesianShape} {state : PackedReviewerBPWindowState}
    {request : PackedReviewerLogicalRequest}
    (hstate : PackedReviewerBPWindowCanonicalScalarFits shape state)
    (hrequest : packedReviewerBPWindowNextRequest state = some request) :
    PackedReviewerBPWindowCanonicalScalarFits shape
      (packedReviewerBPWindowConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      rcases hstate with
        ⟨rfl, hinvocation, hblockSize, hclose, hnextBound, hlength, hwords⟩
      have hnext : next < 4 := by
        by_cases hlt : next < 4
        · exact hlt
        · simp [packedReviewerBPWindowNextRequest, hlt] at hrequest
      let reply :=
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index
      have hreply :
          forall word, reply = some word ->
            PackedReviewerWordFits shape.size word := by
        intro word hread
        apply packedReviewerGlobalReadStore_word_fits shape request word
        simpa [reply] using hread
      let supplied := reply.getD []
      have hsupplied : PackedReviewerWordFits shape.size supplied := by
        cases hreplyValue : reply with
        | none => simp [supplied, hreplyValue, PackedReviewerWordFits]
        | some word =>
            simpa [supplied, hreplyValue] using hreply word hreplyValue
      have hnewWords :
          forall word, word ∈ supplied :: wordsRev ->
            PackedReviewerWordFits shape.size word := by
        intro word hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · exact hsupplied
        · exact hwords word htail
      by_cases hlast : next + 1 = 4
      · have hreverse :
            forall word, word ∈ (supplied :: wordsRev).reverse ->
              PackedReviewerWordFits shape.size word := by
          intro word hmem
          simp at hmem
          rcases hmem with htail | rfl
          · exact hwords word htail
          · exact hsupplied
        have hflatten :=
          packedReviewerAtomicFlattenPayloadWords_length_le shape.size
            (supplied :: wordsRev).reverse hreverse
        have hfour : (supplied :: wordsRev).reverse.length = 4 := by
          simp [hlength, hlast]
        rw [hfour] at hflatten
        have hout :
            PackedReviewerBPWindowCanonicalScalarFits shape
              (.done
                (SuccinctSpace.flattenPayloadWords
                  (supplied :: wordsRev).reverse)) := by
          exact hflatten
        simpa [packedReviewerBPWindowConsumeReply, reply, supplied, hlast]
          using hout
      · have hout :
            PackedReviewerBPWindowCanonicalScalarFits shape
              (.read invocation shape.size blockSize close (next + 1)
                (supplied :: wordsRev)) := by
          refine ⟨rfl, hinvocation, hblockSize, hclose, by omega, ?_,
            hnewWords⟩
          simp [hlength]
        simpa [packedReviewerBPWindowConsumeReply, reply, supplied, hlast]
          using hout
  | done bits =>
      simp [packedReviewerBPWindowNextRequest] at hrequest

theorem PackedReviewerBPWindowCanonicalScalarFits.result_scalar_fields
    {shape : CartesianShape} {state : PackedReviewerBPWindowState}
    {result : List Bool}
    (hstate : PackedReviewerBPWindowCanonicalScalarFits shape state)
    (hresult : packedReviewerBPWindowResult state = some result) :
    forall value,
      value ∈ packedReviewerBPWindowStateNatFields (.done result) ->
        PackedReviewerNatFits shape.size value := by
  simp [packedReviewerBPWindowStateNatFields]

theorem PackedReviewerBPWindowCanonicalScalarFits.result_fits
    {shape : CartesianShape} {state : PackedReviewerBPWindowState}
    {result : List Bool}
    (hstate : PackedReviewerBPWindowCanonicalScalarFits shape state)
    (hresult : packedReviewerBPWindowResult state = some result) :
    result.length <= 4 * packedReviewerCellWidth shape.size := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      simp [packedReviewerBPWindowResult] at hresult
  | done bits =>
      have heq : bits = result := by
        simpa [packedReviewerBPWindowResult] using Option.some.inj hresult
      subst result
      exact hstate

end PackedCellProbe
end SuccinctFinal
end RMQ
