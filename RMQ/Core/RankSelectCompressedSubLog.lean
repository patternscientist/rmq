import RMQ.Core.RankSelectCompressedSplit
import RMQ.Core.GenericSelect.Source

/-!
# Sub-log chunk accounting for compressed/FID rank/select

The full-log fixed-weight chunks are useful for the primary payload bridge, but
their dense shared decoder is formally too large.  This module records the
positive replacement scale: sub-log chunks make the same dense shared decoder
slot space `o(n)` bits.
-/

namespace RMQ

namespace RankSelectSpec

/--
Sub-log in-block chunk size for the compressed/FID decoder path.

The divisor `8` leaves enough arithmetic slack to prove that the dense shared
decoder slot space is `o(n)` using only the existing Mathlib-free elementary
exponential bounds.
-/
def fixedWeightSubLogChunkBlockSize (n : Nat) : Nat :=
  Nat.log2 n / 8 + 1

theorem fixedWeightSubLogChunkBlockSize_pos (n : Nat) :
    0 < fixedWeightSubLogChunkBlockSize n := by
  unfold fixedWeightSubLogChunkBlockSize
  omega

/-- Sub-log fixed-weight chunks. -/
def fixedWeightSubLogChunkBlocks (bits : List Bool) : List (List Bool) :=
  fixedWeightChunkBlocks (fixedWeightSubLogChunkBlockSize bits.length) bits

/-- Sub-log fixed-weight chunks with an empty sentinel block for total routes. -/
def fixedWeightSubLogChunkBlocksWithSentinel
    (bits : List Bool) : List (List Bool) :=
  fixedWeightChunkBlocksWithSentinel
    (fixedWeightSubLogChunkBlockSize bits.length) bits

def fixedWeightSubLogChunkBlockCountBound : Nat -> Nat :=
  fun n => n / fixedWeightSubLogChunkBlockSize n + 1

def fixedWeightSubLogChunkBlockCountBoundWithSentinel : Nat -> Nat :=
  fun n => n / fixedWeightSubLogChunkBlockSize n + 2

def fixedWeightSubLogChunkClassLengthFieldWidthBound : Nat -> Nat :=
  fixedWeightLogChunkClassLengthFieldWidthBound

def fixedWeightSubLogChunkClassLengthOverhead : Nat -> Nat :=
  fun n =>
    fixedWeightBlockClassLengthTableOverheadBudget
      fixedWeightSubLogChunkBlockCountBoundWithSentinel
      fixedWeightSubLogChunkClassLengthFieldWidthBound n +
        4 * fixedWeightSubLogChunkClassLengthFieldWidthBound n

theorem fixedWeightSubLogChunkBlocksWithSentinel_flatten
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightSubLogChunkBlocksWithSentinel bits) = bits := by
  simpa [fixedWeightSubLogChunkBlocksWithSentinel] using
    fixedWeightChunkBlocksWithSentinel_flatten
      (fixedWeightSubLogChunkBlockSize_pos bits.length) bits

theorem fixedWeightSubLogChunkBlocksWithSentinel_block_length_le
    {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightSubLogChunkBlocksWithSentinel bits)) :
    block.length <= fixedWeightSubLogChunkBlockSize bits.length := by
  simpa [fixedWeightSubLogChunkBlocksWithSentinel] using
    fixedWeightChunkBlocksWithSentinel_block_length_le hmem

theorem fixedWeightSubLogChunkBlocks_length_le
    (bits : List Bool) :
    (fixedWeightSubLogChunkBlocks bits).length <=
      fixedWeightSubLogChunkBlockCountBound bits.length := by
  simpa [fixedWeightSubLogChunkBlocks,
    fixedWeightSubLogChunkBlockCountBound] using
    fixedWeightChunkBlocks_length_le
      (fixedWeightSubLogChunkBlockSize_pos bits.length) bits

theorem fixedWeightSubLogChunkBlocksWithSentinel_length_le
    (bits : List Bool) :
    (fixedWeightSubLogChunkBlocksWithSentinel bits).length <=
      fixedWeightSubLogChunkBlockCountBoundWithSentinel bits.length := by
  simpa [fixedWeightSubLogChunkBlocksWithSentinel,
    fixedWeightSubLogChunkBlockCountBoundWithSentinel] using
    fixedWeightChunkBlocksWithSentinel_length_le
      (fixedWeightSubLogChunkBlockSize_pos bits.length) bits

theorem fixedWeightSubLogChunkBlockCountBoundWithSentinel_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkBlockCountBoundWithSentinel := by
  intro scale hscale
  refine ⟨2 ^ (16 * scale + 8), ?_⟩
  intro n hn
  unfold fixedWeightSubLogChunkBlockCountBoundWithSentinel
  let blockSize := fixedWeightSubLogChunkBlockSize n
  let q := n / blockSize
  have hpow_pos : 0 < 2 ^ (16 * scale + 8) := Nat.pow_pos (by omega)
  have hn1 : 1 <= n := Nat.le_trans hpow_pos hn
  have hlogbig : 16 * scale + 8 <= Nat.log2 n := by
    rcases Nat.lt_or_ge (Nat.log2 n) (16 * scale + 8) with hlt | hge
    · exfalso
      have h2 : 2 ^ (Nat.log2 n + 1) <= 2 ^ (16 * scale + 8) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le h3 (Nat.le_trans h2 hn))
    · exact hge
  have hblock_ge : 2 * scale <= blockSize := by
    unfold blockSize fixedWeightSubLogChunkBlockSize
    omega
  have hblock_pos : 0 < blockSize := by
    unfold blockSize
    exact fixedWeightSubLogChunkBlockSize_pos n
  have hdiv_le : blockSize * q <= n := by
    simpa [q, Nat.mul_comm] using Nat.div_mul_le_self n blockSize
  have hmain :
      2 * (scale * q) <= n := by
    have hmul :
        (2 * scale) * q <= blockSize * q :=
      Nat.mul_le_mul_right q hblock_ge
    exact Nat.le_trans (by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
      hdiv_le
  have htail : 4 * scale <= n := by
    have hscale_pow : 4 * scale <= 2 ^ (4 * scale) :=
      SuccinctSpace.nat_le_two_pow (4 * scale)
    have hpow_mono : 2 ^ (4 * scale) <= 2 ^ (16 * scale + 8) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.le_trans (Nat.le_trans hscale_pow hpow_mono) hn
  have hsum : 2 * (scale * (q + 2)) <= 2 * n := by
    have hleft :
        2 * (scale * (q + 2)) =
          2 * (scale * q) + 4 * scale := by
      rw [Nat.mul_add]
      omega
    rw [hleft]
    omega
  exact Nat.le_of_mul_le_mul_left hsum (by omega)

theorem fixedWeightSubLogChunkBlockCountBound_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkBlockCountBound := by
  apply SuccinctSpace.LittleOLinear.of_le
    fixedWeightSubLogChunkBlockCountBoundWithSentinel_littleO
  intro n
  unfold fixedWeightSubLogChunkBlockCountBound
    fixedWeightSubLogChunkBlockCountBoundWithSentinel
  omega

theorem fixedWeightSubLogChunkBlockPayloadBudget_le_payloadBudget_add_blockCount
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightSubLogChunkBlocksWithSentinel bits) <=
      fixedWeightPayloadBudget bits +
        (fixedWeightSubLogChunkBlocksWithSentinel bits).length := by
  have hprimary :=
    fixedWeightBlockPayloadBudget_le_payloadBudget_flatten_add_blocks
      (fixedWeightSubLogChunkBlocksWithSentinel bits)
  simpa [fixedWeightSubLogChunkBlocksWithSentinel_flatten bits] using hprimary

theorem fixedWeightSubLogChunkBlockPayloadBudget_le_payloadBudget_add_bound
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightSubLogChunkBlocksWithSentinel bits) <=
      fixedWeightPayloadBudget bits +
        fixedWeightSubLogChunkBlockCountBoundWithSentinel bits.length := by
  have hprimary :=
    fixedWeightSubLogChunkBlockPayloadBudget_le_payloadBudget_add_blockCount
      bits
  have hblocks := fixedWeightSubLogChunkBlocksWithSentinel_length_le bits
  omega

theorem fixedWeightSubLogChunkBlockSize_lt_classLengthFieldWidthPow
    (n : Nat) :
    fixedWeightSubLogChunkBlockSize n <
      2 ^ fixedWeightSubLogChunkClassLengthFieldWidthBound n := by
  have hle :
      fixedWeightSubLogChunkBlockSize n <= fixedWeightLogChunkBlockSize n := by
    unfold fixedWeightSubLogChunkBlockSize fixedWeightLogChunkBlockSize
    omega
  exact Nat.lt_of_le_of_lt hle
    (by
      simpa [fixedWeightSubLogChunkClassLengthFieldWidthBound] using
        fixedWeightLogChunkBlockSize_lt_classLengthFieldWidthPow n)

theorem fixedWeightSubLogChunkClassLengthFieldWidthBound_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkClassLengthFieldWidthBound := by
  simpa [fixedWeightSubLogChunkClassLengthFieldWidthBound] using
    fixedWeightLogChunkClassLengthFieldWidthBound_littleO

theorem fixedWeightSubLogChunkClassLengthOverhead_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkClassLengthOverhead := by
  intro scale hscale
  rcases
      SuccinctSpace.eventually_scale_logLog_succ_le_log_succ
        (64 * scale) with
    ⟨threshold, hthreshold⟩
  refine ⟨Nat.max threshold (2 ^ (16 * scale + 8)), ?_⟩
  intro n hn
  have hn_threshold : threshold <= n :=
    Nat.le_trans (Nat.le_max_left threshold (2 ^ (16 * scale + 8))) hn
  have hn_pow : 2 ^ (16 * scale + 8) <= n :=
    Nat.le_trans (Nat.le_max_right threshold (2 ^ (16 * scale + 8))) hn
  unfold fixedWeightSubLogChunkClassLengthOverhead
    fixedWeightBlockClassLengthTableOverheadBudget
    fixedWeightSubLogChunkBlockCountBoundWithSentinel
    fixedWeightSubLogChunkClassLengthFieldWidthBound
    fixedWeightLogChunkClassLengthFieldWidthBound
    fixedWeightLogChunkBlockSize
  let blockSize := fixedWeightSubLogChunkBlockSize n
  let q := n / blockSize
  let w := Nat.log2 (Nat.log2 n + 1) + 1
  change
    scale * (((q + 2 + (q + 2)) * w + 4 * w)) <= n
  have hlogw :
      (64 * scale) * w <= Nat.log2 n + 1 := by
    simpa [w] using hthreshold n hn_threshold
  have hlogw_pos : 0 < 32 * scale * w := by
    have hw : 0 < w := by
      unfold w
      omega
    exact Nat.mul_pos (Nat.mul_pos (by omega) hscale) hw
  have hlogw_half : 32 * scale * w <= Nat.log2 n := by
    have hle : 2 * (32 * scale * w) <= Nat.log2 n + 1 := by
      exact Nat.le_trans (by
        simp [Nat.mul_left_comm, Nat.mul_comm])
        hlogw
    omega
  have hblock_large : 4 * scale * w <= blockSize := by
    have h8 :
        8 * (4 * scale * w) <= Nat.log2 n := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        hlogw_half
    have hdiv : 4 * scale * w <= Nat.log2 n / 8 := by
      omega
    unfold blockSize fixedWeightSubLogChunkBlockSize
    omega
  have hblock_pos : 0 < blockSize := by
    unfold blockSize
    exact fixedWeightSubLogChunkBlockSize_pos n
  have hdiv_le : blockSize * q <= n := by
    simpa [q, Nat.mul_comm] using Nat.div_mul_le_self n blockSize
  have hmain_twice :
      2 * (scale * (2 * (q * w))) <= n := by
    have hmul :
        (4 * scale * w) * q <= blockSize * q :=
      Nat.mul_le_mul_right q hblock_large
    have hraw : (4 * scale * w) * q <= n :=
      Nat.le_trans hmul hdiv_le
    have heq :
        2 * (scale * (2 * (q * w))) =
          (4 * scale * w) * q := by
      have hq : 2 * (2 * q) = 4 * q := by omega
      simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, hq]
    simpa [heq] using hraw
  have htail_twice :
      2 * (scale * (8 * w)) <= n := by
    have htail_log : 16 * scale * w <= Nat.log2 n + 1 := by
      exact Nat.le_trans (by
        have hle : 16 * scale <= 64 * scale := by omega
        exact Nat.mul_le_mul_right w hle)
        hlogw
    have hlog_le_n : Nat.log2 n + 1 <= n := by
      have hpos : 0 < 2 ^ (16 * scale + 8) := Nat.pow_pos (by omega)
      have hn1 : n ≠ 0 := by omega
      have hpow : Nat.log2 n + 1 <= 2 ^ Nat.log2 n :=
        SuccinctSpace.nat_succ_le_two_pow (Nat.log2 n)
      exact Nat.le_trans hpow (Nat.log2_self_le hn1)
    exact Nat.le_trans (by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using htail_log)
      hlog_le_n
  have hrewrite :
      scale * (((q + 2 + (q + 2)) * w + 4 * w)) =
        scale * (2 * (q * w)) + scale * (8 * w) := by
    have hsum : q + 2 + (q + 2) = 2 * q + 4 := by omega
    rw [hsum]
    have hinner :
        (2 * q + 4) * w + 4 * w = 2 * (q * w) + 8 * w := by
      rw [Nat.add_mul]
      rw [Nat.mul_assoc]
      omega
    rw [hinner]
    rw [Nat.mul_add]
  rw [hrewrite]
  have htwice :
      2 * (scale * (2 * (q * w)) + scale * (8 * w)) <=
        2 * n := by
    have hsum :=
      Nat.add_le_add hmain_twice htail_twice
    have hright : n + n = 2 * n := by omega
    simpa [Nat.mul_add, hright] using hsum
  exact Nat.le_of_mul_le_mul_left htwice (by omega)

theorem fixedWeightSubLogChunkBlockClassLengthTableOverhead_le
    (bits : List Bool) :
    fixedWeightBlockClassLengthTableOverhead
        (fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length)
        (fixedWeightSubLogChunkBlocksWithSentinel bits) <=
      fixedWeightSubLogChunkClassLengthOverhead bits.length := by
  have hbudget :
      fixedWeightBlockClassLengthTableOverhead
          (fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length)
          (fixedWeightSubLogChunkBlocksWithSentinel bits) <=
        fixedWeightBlockClassLengthTableOverheadBudget
          fixedWeightSubLogChunkBlockCountBoundWithSentinel
          fixedWeightSubLogChunkClassLengthFieldWidthBound
          bits.length := by
    simpa [fixedWeightSubLogChunkBlocksWithSentinel,
      fixedWeightSubLogChunkBlockCountBoundWithSentinel,
      fixedWeightChunkBlockCountBoundWithSentinel] using
      fixedWeightBlockClassLengthTableOverhead_le_chunk_sentinel_budget
        (fieldWidthBound := fixedWeightSubLogChunkClassLengthFieldWidthBound)
        (bits := bits)
        (blocks := fixedWeightSubLogChunkBlocksWithSentinel bits)
        (fixedWeightSubLogChunkBlockSize_pos bits.length)
        (by rfl)
        (Nat.le_refl _)
  unfold fixedWeightSubLogChunkClassLengthOverhead
  exact Nat.le_trans hbudget (Nat.le_add_right _ _)

/--
Any fixed-width route-field layout access route has a charged metadata schedule.

This rules out treating an empty-metadata semantic route as already being the
payload-backed route-field layout.
-/
theorem fixedWeightRouteFieldTableLayout_accessMetadataReads_ne_nil
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :
    (data.routeData.accessRoute i).metadataReads ≠ [] := by
  intro hnil
  have hmeta := data.access_metadata_reads_eq i
  rw [hnil] at hmeta
  cases hmeta

/--
Any fixed-width route-field layout rank route has a charged metadata schedule.
-/
theorem fixedWeightRouteFieldTableLayout_rankMetadataReads_ne_nil
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    (data.routeData.rankRoute target pos).metadataReads ≠ [] := by
  intro hnil
  have hmeta := data.rank_metadata_reads_eq target pos
  rw [hnil] at hmeta
  cases hmeta

/--
Any fixed-width route-field layout select route has a charged metadata schedule.
The positive sub-log constructor must therefore build payload-routed select
records, not reuse an empty-read semantic select-route scaffold.
-/
theorem fixedWeightRouteFieldTableLayout_selectMetadataReads_ne_nil
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.routeData.selectRoute target occurrence).metadataReads ≠ [] := by
  intro hnil
  have hmeta := data.select_metadata_reads_eq target occurrence
  rw [hnil] at hmeta
  cases hmeta

/--
The route payload of a concrete route-field layout is exactly the flattened
eight-table fixed-width layout.
-/
theorem fixedWeightRouteFieldTableLayout_routePayload_length_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.routeData.routePayload.length =
      (fixedWeightRouteFieldTableLayoutPayload data.fieldWidth
        data.accessBlockEntries data.accessOffsetEntries
        data.rankBlockEntries data.rankLocalLimitEntries
        data.rankBaseRankEntries data.selectBlockEntries
        data.selectLocalOccurrenceEntries
        data.selectBlockStartEntries).length := by
  have herases := congrArg List.length data.routeData.routeStore.erases
  rw [data.routeStore_words_eq_layoutWords] at herases
  rw [<- herases]
  simp [FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.layoutWords,
    fixedWeightRouteFieldTableLayoutPayload]

theorem fixedWeightRouteFieldTableLayout_selectBlockEntries_length_le_routePayload
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (hfield : 0 < data.fieldWidth) :
    data.selectBlockEntries.length <= data.routeData.routePayload.length := by
  rw [fixedWeightRouteFieldTableLayout_routePayload_length_eq data]
  rw [fixedWeightRouteFieldTableLayoutPayload_length]
  let total :=
    data.accessBlockEntries.length + data.accessOffsetEntries.length +
      data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
      data.rankBaseRankEntries.length + data.selectBlockEntries.length +
      data.selectLocalOccurrenceEntries.length +
      data.selectBlockStartEntries.length
  change data.selectBlockEntries.length <= total * data.fieldWidth
  have hselect_le_total : data.selectBlockEntries.length <= total := by
    unfold total
    omega
  have htotal_le_mul : total <= total * data.fieldWidth := by
    have hmul := Nat.mul_le_mul_left total hfield
    simpa using hmul
  exact Nat.le_trans hselect_le_total htotal_le_mul

/--
If select occurrence `k` is routed by reading table slot `k`, then the select
block table must contain at least all queried occurrence slots.

This is the local counting fact behind the Clark-style fork: a direct
occurrence-indexed select route is a full occurrence table, not a compact
predecessor/select directory.
-/
theorem fixedWeightRouteFieldTableLayout_directSelectOccurrenceSlots_entries_length_ge
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {bound : Nat}
    (hdirect :
      forall occurrence,
        occurrence < bound ->
          data.selectBlockLocalSlot target occurrence = occurrence) :
    bound <= data.selectBlockEntries.length := by
  by_cases hzero : bound = 0
  · simp [hzero]
  · have hlast : bound - 1 < bound := by omega
    have hentry := data.select_block_entry_eq target (bound - 1)
    have hget :
        data.selectBlockEntries[bound - 1]? =
          some (data.routeData.selectRoute target (bound - 1)).blockIndex := by
      simpa [hdirect (bound - 1) hlast] using hentry
    have hlt := (List.getElem?_eq_some_iff.mp hget).1
    omega

theorem fixedWeightRouteFieldTableLayout_directSelectOccurrenceSlots_routePayload_length_ge
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {bound : Nat}
    (hfield : 0 < data.fieldWidth)
    (hdirect :
      forall occurrence,
        occurrence < bound ->
          data.selectBlockLocalSlot target occurrence = occurrence) :
    bound <= data.routeData.routePayload.length := by
  exact Nat.le_trans
    (fixedWeightRouteFieldTableLayout_directSelectOccurrenceSlots_entries_length_ge
      data hdirect)
    (fixedWeightRouteFieldTableLayout_selectBlockEntries_length_le_routePayload
      data hfield)

/--
No fixed-slot route-field-table family can keep the route payload `o(n)` while
using direct occurrence-indexed select slots on dense false bitvectors.

The statement targets the tempting but wrong constructor in which
`selectBlockLocalSlot false k = k`.  It forces at least `n` route payload bits
on `List.replicate n false`, contradicting the fixed-slot sampled route
overhead.  A compressed/FID select route therefore needs a Clark-style sampled
or chunked occurrence directory rather than a flat occurrence table.
-/
theorem no_fixedWeightRouteFieldTableLayoutFamily_directSelectOccurrenceSlots
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hfield :
      forall n : Nat,
        0 <
          (family.componentData (List.replicate n false)).fieldWidth)
    (hdirect :
      forall n occurrence : Nat,
        occurrence < n ->
          (family.componentData
              (List.replicate n false)).selectBlockLocalSlot
            false occurrence = occurrence) :
    False := by
  have hnoto :
      ¬ SuccinctSpace.LittleOLinear
        (fixedWeightAmbientBlockAuxiliaryOverhead slots) := by
    apply fixedWeight_notLittleOLinear_of_self_le
    intro n
    let bits : List Bool := List.replicate n false
    have hlarge :
        n <=
          (family.componentData bits).routeData.routePayload.length :=
      fixedWeightRouteFieldTableLayout_directSelectOccurrenceSlots_routePayload_length_ge
        (family.componentData bits)
        (hfield n)
        (by
          intro occurrence hocc
          simpa [bits] using hdirect n occurrence hocc)
    have hlen :
        (family.componentData bits).routeData.routePayload.length =
          fixedWeightAmbientBlockAuxiliaryOverhead slots n := by
      simpa [bits] using
        (family.componentData bits).routeData.routePayload_length_eq
    simpa [hlen] using hlarge
  exact hnoto (fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots)

/--
If two select queries in the final-route-field table layout read the same three
select slots, the layout can only return the same global select answer.

This is the small formal guardrail behind the Clark-style fork: a compact
sampled select directory needs a route evaluator between the sampled reads and
the final `(blockIndex, localOccurrence, blockStart)` triple.  Coalescing the
final-field slots themselves is not enough.
-/
theorem fixedWeightRouteFieldTableLayout_sameSelectSlots_select_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {occurrenceA occurrenceB : Nat}
    (hblock :
      data.selectBlockLocalSlot target occurrenceA =
        data.selectBlockLocalSlot target occurrenceB)
    (hlocal :
      data.selectLocalOccurrenceLocalSlot target occurrenceA =
        data.selectLocalOccurrenceLocalSlot target occurrenceB)
    (hstart :
      data.selectBlockStartLocalSlot target occurrenceA =
        data.selectBlockStartLocalSlot target occurrenceB) :
    Succinct.select target bits occurrenceA =
      Succinct.select target bits occurrenceB := by
  let routeA := data.routeData.selectRoute target occurrenceA
  let routeB := data.routeData.selectRoute target occurrenceB
  have hblockA := data.select_block_entry_eq target occurrenceA
  have hblockB := data.select_block_entry_eq target occurrenceB
  have hblockIdx : routeA.blockIndex = routeB.blockIndex := by
    rw [hblock] at hblockA
    rw [hblockA] at hblockB
    exact Option.some.inj hblockB
  have hlocalA := data.select_localOccurrence_entry_eq target occurrenceA
  have hlocalB := data.select_localOccurrence_entry_eq target occurrenceB
  have hlocalOcc : routeA.localOccurrence = routeB.localOccurrence := by
    rw [hlocal] at hlocalA
    rw [hlocalA] at hlocalB
    exact Option.some.inj hlocalB
  have hstartA := data.select_blockStart_entry_eq target occurrenceA
  have hstartB := data.select_blockStart_entry_eq target occurrenceB
  have hblockStart : routeA.blockStart = routeB.blockStart := by
    rw [hstart] at hstartA
    rw [hstartA] at hstartB
    exact Option.some.inj hstartB
  have hblockData : routeA.block = routeB.block := by
    have hgetA := routeA.block_get
    have hgetB := routeB.block_get
    rw [hblockIdx] at hgetA
    rw [hgetA] at hgetB
    exact Option.some.inj hgetB
  have hexactA := routeA.select_exact
  have hexactB := routeB.select_exact
  rw [<- hexactA, <- hexactB]
  simp [hblockData, hlocalOcc, hblockStart]

/--
Linear is eventually bounded by exponential, in the exact form used by the
sub-log decoder budget proof.
-/
private theorem scale_mul_succ_le_two_pow {scale q : Nat}
    (hlarge : 2 * scale + 1 <= q) :
    scale * (q + 1) <= 2 ^ q := by
  have hle : scale <= q := by omega
  have hqplus : q + 1 <= 2 * (q - scale) := by omega
  have hqpow : q + 1 <= 2 ^ (q - scale) :=
    Nat.le_trans hqplus (SuccinctSpace.two_mul_le_two_pow (q - scale))
  have hsc : scale <= 2 ^ scale := SuccinctSpace.nat_le_two_pow scale
  have hmul := Nat.mul_le_mul hsc hqpow
  have hpows : 2 ^ scale * 2 ^ (q - scale) = 2 ^ q := by
    rw [<- Nat.pow_add, Nat.add_sub_of_le hle]
  exact Nat.le_trans hmul (Nat.le_of_eq hpows)

/--
Dense shared-decoder bit budget at the sub-log block size.

For `B = fixedWeightSubLogChunkBlockSize n`, the shared slot range is bounded by
`2^B * (B+1)^2`, and each stored decoded word has length at most
`Nat.log2 n + 1`.
-/
def fixedWeightSubLogChunkDenseDecoderBudget (n : Nat) : Nat :=
  2 ^ fixedWeightSubLogChunkBlockSize n *
      ((fixedWeightSubLogChunkBlockSize n + 1) *
        (fixedWeightSubLogChunkBlockSize n + 1)) *
    (Nat.log2 n + 1)

/-- Number of word slots needed by the dense shared decoder at the sub-log
block size. -/
def fixedWeightSubLogChunkDenseDecoderRows (n : Nat) : Nat :=
  2 ^ fixedWeightSubLogChunkBlockSize n *
    ((fixedWeightSubLogChunkBlockSize n + 1) *
      (fixedWeightSubLogChunkBlockSize n + 1))

@[simp] theorem fixedWeightSubLogChunkDenseDecoderBudget_eq_rows_mul
    (n : Nat) :
    fixedWeightSubLogChunkDenseDecoderBudget n =
      fixedWeightSubLogChunkDenseDecoderRows n * (Nat.log2 n + 1) := by
  simp [fixedWeightSubLogChunkDenseDecoderBudget,
    fixedWeightSubLogChunkDenseDecoderRows, Nat.mul_assoc]

/--
The shared decoder slot used by any block whose length fits the sub-log block
size lies inside the dense sub-log decoder row range.
-/
theorem fixedWeightSharedDecodeSlot_lt_subLogDenseDecoderRows
    {n : Nat} {block : List Bool}
    (hlen : block.length <= fixedWeightSubLogChunkBlockSize n) :
    fixedWeightSharedDecodeSlot block.length (trueCount block)
        (fixedWeightCode block) <
      fixedWeightSubLogChunkDenseDecoderRows n := by
  let B := fixedWeightSubLogChunkBlockSize n
  let len := block.length
  let cls := trueCount block
  let code := fixedWeightCode block
  have hcls : cls <= len := by
    simpa [cls, len] using trueCount_le_length block
  have hcodeBin :
      code < binomialCount len cls := by
    simpa [code, len, cls] using fixedWeightCode_lt_binomialCount block
  have hbinPow :
      binomialCount len cls <= 2 ^ len :=
    binomialCount_le_two_pow len cls
  have hcode : code < 2 ^ len := Nat.lt_of_lt_of_le hcodeBin hbinPow
  have hpow : 2 ^ len <= 2 ^ B :=
    Nat.pow_le_pow_right (by omega : 0 < 2) (by simpa [B, len] using hlen)
  have hcoef :
      len * (len + 1) + cls + 1 <= (B + 1) * (B + 1) := by
    have hlenB : len <= B := by simpa [B, len] using hlen
    have hleft : len * (len + 1) + cls + 1 <= (len + 1) * (len + 1) := by
      have heq :
          (len + 1) * (len + 1) = len * (len + 1) + len + 1 := by
        rw [Nat.add_mul]
        simp
        omega
      rw [heq]
      omega
    have hright : (len + 1) * (len + 1) <= (B + 1) * (B + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact Nat.le_trans hleft hright
  have hslotLt :
      (len * (len + 1) + cls) * 2 ^ len + code <
        (len * (len + 1) + cls + 1) * 2 ^ len := by
    let coeff := len * (len + 1) + cls
    have hlt :
        coeff * 2 ^ len + code < coeff * 2 ^ len + 2 ^ len :=
      Nat.add_lt_add_left hcode (coeff * 2 ^ len)
    have heq : (coeff + 1) * 2 ^ len = coeff * 2 ^ len + 2 ^ len := by
      rw [Nat.add_mul]
      simp
    change coeff * 2 ^ len + code < (coeff + 1) * 2 ^ len
    rw [heq]
    exact hlt
  have hslotLe :
      (len * (len + 1) + cls + 1) * 2 ^ len <=
        ((B + 1) * (B + 1)) * 2 ^ B :=
    Nat.mul_le_mul hcoef hpow
  have hcomm :
      ((B + 1) * (B + 1)) * 2 ^ B =
        fixedWeightSubLogChunkDenseDecoderRows n := by
    simp [fixedWeightSubLogChunkDenseDecoderRows, B, Nat.mul_comm,
      Nat.mul_assoc]
  unfold fixedWeightSharedDecodeSlot
  change (len * (len + 1) + cls) * 2 ^ len + code <
    fixedWeightSubLogChunkDenseDecoderRows n
  exact Nat.lt_of_lt_of_le hslotLt (by simpa [hcomm] using hslotLe)

/--
Every block retrieved from the sub-log sentinel decomposition routes to a valid
row in the dense shared decoder table.
-/
theorem fixedWeightSubLogChunkBlocksWithSentinel_sharedDecodeSlot_lt_rows
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block) :
    fixedWeightSharedDecodeSlot block.length (trueCount block)
        (fixedWeightCode block) <
      fixedWeightSubLogChunkDenseDecoderRows bits.length := by
  exact fixedWeightSharedDecodeSlot_lt_subLogDenseDecoderRows
    (fixedWeightSubLogChunkBlocksWithSentinel_block_length_le
      (List.mem_of_getElem? hblock))

private def fixedWeightSharedDecodeLengthBase (n : Nat) : Nat :=
  n * (n + 1) * 2 ^ n

private theorem fixedWeightSharedDecodeLengthBase_mono
    {n m : Nat} (h : n <= m) :
    fixedWeightSharedDecodeLengthBase n <=
      fixedWeightSharedDecodeLengthBase m := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      simp [hn]
  | succ m ih =>
      rcases Nat.eq_or_lt_of_le h with hEq | hLt
      · subst n
        exact Nat.le_refl _
      · have hn_m : n <= m := Nat.le_of_lt_succ hLt
        have hstep :
            fixedWeightSharedDecodeLengthBase m <=
              fixedWeightSharedDecodeLengthBase (m + 1) := by
          unfold fixedWeightSharedDecodeLengthBase
          have hcoef : m * (m + 1) <= (m + 1) * (m + 2) :=
            Nat.mul_le_mul (by omega) (by omega)
          have hpow : 2 ^ m <= 2 ^ (m + 1) :=
            Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
          exact Nat.mul_le_mul hcoef hpow
        exact Nat.le_trans (ih hn_m) hstep

private theorem fixedWeightSharedDecodeSlot_lt_next_length_base
    {n k code : Nat}
    (hk : k <= n) (hcode : code < 2 ^ n) :
    fixedWeightSharedDecodeSlot n k code <
      fixedWeightSharedDecodeLengthBase (n + 1) := by
  let p := 2 ^ n
  let coeff := n * (n + 1) + k
  have hslot_lt :
      fixedWeightSharedDecodeSlot n k code < (coeff + 1) * p := by
    have hlt : coeff * p + code < coeff * p + p :=
      Nat.add_lt_add_left hcode (coeff * p)
    have heq : (coeff + 1) * p = coeff * p + p := by
      rw [Nat.add_mul]
      simp
    unfold fixedWeightSharedDecodeSlot
    change coeff * p + code < (coeff + 1) * p
    rw [heq]
    exact hlt
  have hcoeff :
      coeff + 1 <= (n + 1) * (n + 1) := by
    have heq :
        (n + 1) * (n + 1) = n * (n + 1) + n + 1 := by
      rw [Nat.add_mul]
      simp
      omega
    rw [heq]
    omega
  have hto_square :
      (coeff + 1) * p <= ((n + 1) * (n + 1)) * p :=
    Nat.mul_le_mul_right p hcoeff
  have hgap :
      ((n + 1) * (n + 1)) * 2 ^ n <=
        fixedWeightSharedDecodeLengthBase (n + 1) := by
    unfold fixedWeightSharedDecodeLengthBase
    have hcoef :
        (n + 1) * (n + 1) <= (n + 1) * (n + 2) :=
      Nat.mul_le_mul_left (n + 1) (by omega)
    have hpow : 2 ^ n <= 2 ^ (n + 1) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    exact Nat.mul_le_mul hcoef hpow
  exact Nat.lt_of_lt_of_le hslot_lt (Nat.le_trans hto_square hgap)

private theorem fixedWeightSharedDecodeSlot_length_base_le
    (n k code : Nat) :
    fixedWeightSharedDecodeLengthBase n <=
      fixedWeightSharedDecodeSlot n k code := by
  unfold fixedWeightSharedDecodeLengthBase fixedWeightSharedDecodeSlot
  have hcoef : n * (n + 1) <= n * (n + 1) + k := by omega
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ n) hcoef)
    (Nat.le_add_right _ _)

private theorem fixedWeightSharedDecodeSlot_lt_of_length_lt
    {n m k code k' code' : Nat}
    (hnm : n < m) (hk : k <= n) (hcode : code < 2 ^ n) :
    fixedWeightSharedDecodeSlot n k code <
      fixedWeightSharedDecodeSlot m k' code' := by
  have hupper :=
    fixedWeightSharedDecodeSlot_lt_next_length_base
      (n := n) (k := k) (code := code) hk hcode
  have hmono :
      fixedWeightSharedDecodeLengthBase (n + 1) <=
        fixedWeightSharedDecodeLengthBase m :=
    fixedWeightSharedDecodeLengthBase_mono (by omega)
  have hlower :=
    fixedWeightSharedDecodeSlot_length_base_le m k' code'
  exact Nat.lt_of_lt_of_le hupper (Nat.le_trans hmono hlower)

private theorem fixedWeightSharedDecodeSlot_lt_of_class_lt
    {n k k' code code' : Nat}
    (hkk : k < k') (hcode : code < 2 ^ n) :
    fixedWeightSharedDecodeSlot n k code <
      fixedWeightSharedDecodeSlot n k' code' := by
  let p := 2 ^ n
  let base := n * (n + 1)
  have hslot_lt :
      fixedWeightSharedDecodeSlot n k code < (base + k + 1) * p := by
    have hlt : (base + k) * p + code < (base + k) * p + p :=
      Nat.add_lt_add_left hcode ((base + k) * p)
    have heq : (base + k + 1) * p = (base + k) * p + p := by
      rw [Nat.add_mul]
      simp
    unfold fixedWeightSharedDecodeSlot
    change (base + k) * p + code < (base + k + 1) * p
    rw [heq]
    exact hlt
  have hnext_le : base + k + 1 <= base + k' := by omega
  have hstart_le :
      (base + k + 1) * p <= (base + k') * p :=
    Nat.mul_le_mul_right p hnext_le
  have hlower :
      (base + k') * p <= fixedWeightSharedDecodeSlot n k' code' := by
    unfold fixedWeightSharedDecodeSlot
    change (base + k') * p <= (base + k') * p + code'
    exact Nat.le_add_right _ _
  exact Nat.lt_of_lt_of_le hslot_lt (Nat.le_trans hstart_le hlower)

theorem fixedWeightSharedDecodeSlot_inj
    {n k code n' k' code' : Nat}
    (hk : k <= n) (hk' : k' <= n')
    (hcode : code < 2 ^ n) (hcode' : code' < 2 ^ n')
    (heq :
      fixedWeightSharedDecodeSlot n k code =
        fixedWeightSharedDecodeSlot n' k' code') :
    n = n' /\ k = k' /\ code = code' := by
  by_cases hn : n = n'
  · subst n'
    by_cases hclass : k = k'
    · subst k'
      constructor
      · rfl
      constructor
      · rfl
      · unfold fixedWeightSharedDecodeSlot at heq
        exact Nat.add_left_cancel heq
    · have hclass_cases := Nat.lt_or_gt_of_ne hclass
      rcases hclass_cases with hlt | hgt
      · have hslot_lt :=
          fixedWeightSharedDecodeSlot_lt_of_class_lt
            (n := n) (k := k) (k' := k') (code := code)
            (code' := code') hlt hcode
        rw [heq] at hslot_lt
        exact False.elim (Nat.lt_irrefl _ hslot_lt)
      · have hslot_lt :=
          fixedWeightSharedDecodeSlot_lt_of_class_lt
            (n := n) (k := k') (k' := k) (code := code')
            (code' := code) hgt hcode'
        rw [heq] at hslot_lt
        exact False.elim (Nat.lt_irrefl _ hslot_lt)
  · have hn_cases := Nat.lt_or_gt_of_ne hn
    rcases hn_cases with hlt | hgt
    · have hslot_lt :=
        fixedWeightSharedDecodeSlot_lt_of_length_lt
          (n := n) (m := n') (k := k) (code := code)
          (k' := k') (code' := code') hlt hk hcode
      rw [heq] at hslot_lt
      exact False.elim (Nat.lt_irrefl _ hslot_lt)
    · have hslot_lt :=
        fixedWeightSharedDecodeSlot_lt_of_length_lt
          (n := n') (m := n) (k := k') (code := code')
          (k' := k) (code' := code) hgt hk' hcode'
      rw [heq] at hslot_lt
      exact False.elim (Nat.lt_irrefl _ hslot_lt)

/-- Lookup the block stored at a shared decoder slot in a concrete block list. -/
def fixedWeightSharedDecodeLookup
    (slot : Nat) : List (List Bool) -> List Bool
  | [] => []
  | block :: rest =>
      if fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block) = slot then
        block
      else
        fixedWeightSharedDecodeLookup slot rest

theorem fixedWeightSharedDecodeLookup_length_le
    {slot blockSize : Nat} {blocks : List (List Bool)}
    (hblocks :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize) :
    (fixedWeightSharedDecodeLookup slot blocks).length <= blockSize := by
  induction blocks with
  | nil =>
      simp [fixedWeightSharedDecodeLookup]
  | cons block rest ih =>
      have hblock : block.length <= blockSize := hblocks List.mem_cons_self
      have hrest :
          forall {tail : List Bool}, List.Mem tail rest ->
            tail.length <= blockSize := by
        intro tail hmem
        exact hblocks (List.mem_cons_of_mem block hmem)
      unfold fixedWeightSharedDecodeLookup
      by_cases hslot :
          fixedWeightSharedDecodeSlot block.length (trueCount block)
              (fixedWeightCode block) = slot
      · simp [hslot, hblock]
      · simp [hslot, ih hrest]

theorem fixedWeightSharedDecodeLookup_eq_of_mem
    {slotBlock : List Bool} {slot : Nat}
    {blocks : List (List Bool)}
    (hmem : List.Mem slotBlock blocks)
    (hunique :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightSharedDecodeSlot block.length (trueCount block)
            (fixedWeightCode block) = slot ->
          block = slotBlock)
    (hslot :
      fixedWeightSharedDecodeSlot slotBlock.length (trueCount slotBlock)
          (fixedWeightCode slotBlock) = slot) :
  fixedWeightSharedDecodeLookup slot blocks = slotBlock := by
  induction blocks with
  | nil =>
      cases hmem
  | cons block rest ih =>
      unfold fixedWeightSharedDecodeLookup
      by_cases hhead :
          fixedWeightSharedDecodeSlot block.length (trueCount block)
              (fixedWeightCode block) = slot
      · have hblock : block = slotBlock :=
          hunique List.mem_cons_self hhead
        subst block
        simp [hslot]
      · have hmemRest : List.Mem slotBlock rest := by
          cases hmem with
          | head =>
              exact False.elim (hhead hslot)
          | tail _ htail =>
              exact htail
        have huniqueRest :
            forall {tail : List Bool}, List.Mem tail rest ->
              fixedWeightSharedDecodeSlot tail.length (trueCount tail)
                  (fixedWeightCode tail) = slot ->
                tail = slotBlock := by
          intro tail htail htailSlot
          exact hunique (List.mem_cons_of_mem block htail) htailSlot
        simp [hhead, ih hmemRest huniqueRest]

def fixedWeightSharedDecodeRows
    (rowCount : Nat) (blocks : List (List Bool)) : List (List Bool) :=
  (List.range rowCount).map fun slot =>
    fixedWeightSharedDecodeLookup slot blocks

@[simp] theorem fixedWeightSharedDecodeRows_length
    (rowCount : Nat) (blocks : List (List Bool)) :
    (fixedWeightSharedDecodeRows rowCount blocks).length = rowCount := by
  simp [fixedWeightSharedDecodeRows]

theorem fixedWeightSharedDecodeRows_word_length_le
    {rowCount blockSize : Nat} {blocks : List (List Bool)}
    (hblocks :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize)
    {word : List Bool}
    (hmem : List.Mem word (fixedWeightSharedDecodeRows rowCount blocks)) :
    word.length <= blockSize := by
  rcases List.mem_map.mp hmem with ⟨slot, hslotMem, rfl⟩
  exact fixedWeightSharedDecodeLookup_length_le hblocks

theorem fixedWeightSharedDecodeRows_get?_of_block
    {rowCount : Nat} {blocks : List (List Bool)}
    {blockIndex slot : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block)
    (hslot_lt : slot < rowCount)
    (hslot :
      fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block) = slot)
    (hunique :
      forall {other : List Bool}, List.Mem other blocks ->
        fixedWeightSharedDecodeSlot other.length (trueCount other)
            (fixedWeightCode other) = slot ->
          other = block) :
    (fixedWeightSharedDecodeRows rowCount blocks)[slot]? = some block := by
  have hlookup :
      fixedWeightSharedDecodeLookup slot blocks = block :=
    fixedWeightSharedDecodeLookup_eq_of_mem
      (List.mem_of_getElem? hblock) hunique hslot
  simp [fixedWeightSharedDecodeRows, List.getElem?_map,
    List.getElem?_range hslot_lt, hlookup]

def fixedWeightSharedDecodeRawPayload
    (rowCount : Nat) (blocks : List (List Bool)) : List Bool :=
  SuccinctSpace.flattenPayloadWords
    (fixedWeightSharedDecodeRows rowCount blocks)

def fixedWeightSharedDecodePaddedWords
    (rowCount wordSize : Nat) (blocks : List (List Bool)) :
    List (List Bool) :=
  let rows := fixedWeightSharedDecodeRows rowCount blocks
  let raw := SuccinctSpace.flattenPayloadWords rows
  rows ++
    SuccinctSpace.chunkPayloadWords wordSize
      (List.replicate (rowCount * wordSize - raw.length) false)

def fixedWeightSharedDecodePayload
    (rowCount wordSize : Nat) (blocks : List (List Bool)) : List Bool :=
  SuccinctSpace.flattenPayloadWords
    (fixedWeightSharedDecodePaddedWords rowCount wordSize blocks)

private theorem fixedWeightSharedDecodeRawPayload_length_le
    {rowCount wordSize blockSize : Nat} {blocks : List (List Bool)}
    (hblockSize_le_wordSize : blockSize <= wordSize)
    (hblocks :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize) :
    (fixedWeightSharedDecodeRawPayload rowCount blocks).length <=
      rowCount * wordSize := by
  unfold fixedWeightSharedDecodeRawPayload
  have hrows :
      forall {word : List Bool},
        List.Mem word (fixedWeightSharedDecodeRows rowCount blocks) ->
          word.length <= wordSize := by
    intro word hmem
    exact Nat.le_trans
      (fixedWeightSharedDecodeRows_word_length_le hblocks hmem)
      hblockSize_le_wordSize
  simpa [fixedWeightSharedDecodeRows_length] using
    SuccinctSpace.flattenPayloadWords_length_le_of_forall_length_le
      hrows

theorem fixedWeightSharedDecodePayload_length_eq
    {rowCount wordSize blockSize : Nat} {blocks : List (List Bool)}
    (hword : 0 < wordSize)
    (hblockSize_le_wordSize : blockSize <= wordSize)
    (hblocks :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize) :
    (fixedWeightSharedDecodePayload rowCount wordSize blocks).length =
      rowCount * wordSize := by
  let rows := fixedWeightSharedDecodeRows rowCount blocks
  let raw := SuccinctSpace.flattenPayloadWords rows
  have hraw :
      raw.length <= rowCount * wordSize := by
    simpa [raw, fixedWeightSharedDecodeRawPayload] using
      fixedWeightSharedDecodeRawPayload_length_le
        (rowCount := rowCount) (wordSize := wordSize)
        (blockSize := blockSize) (blocks := blocks)
        hblockSize_le_wordSize hblocks
  unfold fixedWeightSharedDecodePayload fixedWeightSharedDecodePaddedWords
  change
    (SuccinctSpace.flattenPayloadWords
      (rows ++
        SuccinctSpace.chunkPayloadWords wordSize
          (List.replicate (rowCount * wordSize - raw.length) false))).length =
      rowCount * wordSize
  rw [SuccinctSpace.flattenPayloadWords_append]
  rw [SuccinctSpace.flattenPayloadWords_chunkPayloadWords hword]
  change (raw ++
      List.replicate (rowCount * wordSize - raw.length) false).length =
    rowCount * wordSize
  simp
  omega

def fixedWeightSharedDecodeBoundedStore
    (rowCount wordSize blockSize : Nat) (blocks : List (List Bool))
    (_hword : 0 < wordSize)
    (hblockSize_le_wordSize : blockSize <= wordSize)
    (hblocks :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightSharedDecodePayload rowCount wordSize blocks) wordSize where
  store :=
    { words :=
        (fixedWeightSharedDecodePaddedWords rowCount wordSize blocks).toArray
      erases := by
        simp [fixedWeightSharedDecodePayload] }
  word_length_le := by
    intro word hmem
    have hlist :
        List.Mem word
          (fixedWeightSharedDecodePaddedWords rowCount wordSize blocks) := by
      simpa using hmem
    unfold fixedWeightSharedDecodePaddedWords at hlist
    rcases List.mem_append.mp hlist with hrow | hpad
    · exact Nat.le_trans
        (fixedWeightSharedDecodeRows_word_length_le hblocks hrow)
        hblockSize_le_wordSize
    · exact SuccinctSpace.chunkPayloadWords_word_length_le wordSize hpad

theorem fixedWeightSharedDecodeBoundedStore_get?_of_block
    {rowCount wordSize blockSize : Nat} {blocks : List (List Bool)}
    (hword : 0 < wordSize)
    (hblockSize_le_wordSize : blockSize <= wordSize)
    (hblocks :
      forall {candidate : List Bool}, List.Mem candidate blocks ->
        candidate.length <= blockSize)
    {blockIndex slot : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block)
    (hslot_lt : slot < rowCount)
    (hslot :
      fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block) = slot)
    (hunique :
      forall {other : List Bool}, List.Mem other blocks ->
        fixedWeightSharedDecodeSlot other.length (trueCount other)
            (fixedWeightCode other) = slot ->
          other = block) :
    (fixedWeightSharedDecodeBoundedStore rowCount wordSize blockSize blocks
        hword hblockSize_le_wordSize hblocks).store.words[slot]? =
      some block := by
  have hrow :
      (fixedWeightSharedDecodeRows rowCount blocks)[slot]? = some block :=
    fixedWeightSharedDecodeRows_get?_of_block hblock hslot_lt hslot hunique
  have hrowList :
      (fixedWeightSharedDecodePaddedWords rowCount wordSize blocks)[slot]? =
        some block := by
    have hslotRows :
        slot < (fixedWeightSharedDecodeRows rowCount blocks).length := by
      simpa using hslot_lt
    have hrowGet :
        (fixedWeightSharedDecodeRows rowCount blocks)[slot] = block := by
      rw [List.getElem?_eq_getElem hslotRows] at hrow
      exact Option.some.inj hrow
    unfold fixedWeightSharedDecodePaddedWords
    rw [List.getElem?_append]
    simp [hslot_lt]
    exact hrowGet
  simpa [fixedWeightSharedDecodeBoundedStore, Array.getElem?_toList]
    using hrowList

private theorem fixedWeightSharedDecodeSlot_unique_for_blocks
    {block other : List Bool}
    (heq :
      fixedWeightSharedDecodeSlot other.length (trueCount other)
          (fixedWeightCode other) =
        fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block)) :
    other = block := by
  have hotherClass : trueCount other <= other.length :=
    trueCount_le_length other
  have hblockClass : trueCount block <= block.length :=
    trueCount_le_length block
  have hotherCode :
      fixedWeightCode other < 2 ^ other.length := by
    exact Nat.lt_of_lt_of_le
      (fixedWeightCode_lt_binomialCount other)
      (binomialCount_le_two_pow other.length (trueCount other))
  have hblockCode :
      fixedWeightCode block < 2 ^ block.length := by
    exact Nat.lt_of_lt_of_le
      (fixedWeightCode_lt_binomialCount block)
      (binomialCount_le_two_pow block.length (trueCount block))
  rcases fixedWeightSharedDecodeSlot_inj
      hotherClass hblockClass hotherCode hblockCode heq with
    ⟨hlen, hclass, hcode⟩
  have hdecOther :
      fixedWeightDecode? other.length (trueCount other)
          (fixedWeightCode other) = some other :=
    fixedWeightDecode?_fixedWeightEncode?
      (fixedWeightEncode?_eq_some_fixedWeightCode other)
  have hdecBlock :
      fixedWeightDecode? block.length (trueCount block)
          (fixedWeightCode block) = some block :=
    fixedWeightDecode?_fixedWeightEncode?
      (fixedWeightEncode?_eq_some_fixedWeightCode block)
  rw [hlen, hclass, hcode, hdecBlock] at hdecOther
  cases hdecOther
  rfl

def fixedWeightSubLogSharedDecoderPayload (bits : List Bool) : List Bool :=
  fixedWeightSharedDecodePayload
    (fixedWeightSubLogChunkDenseDecoderRows bits.length)
    (Nat.log2 bits.length + 1)
    (fixedWeightSubLogChunkBlocksWithSentinel bits)

def fixedWeightSubLogSharedDecoderStore
    (bits : List Bool) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightSubLogSharedDecoderPayload bits)
      (Nat.log2 bits.length + 1) :=
  fixedWeightSharedDecodeBoundedStore
    (fixedWeightSubLogChunkDenseDecoderRows bits.length)
    (Nat.log2 bits.length + 1)
    (fixedWeightSubLogChunkBlockSize bits.length)
    (fixedWeightSubLogChunkBlocksWithSentinel bits)
    (by omega)
    (by
      unfold fixedWeightSubLogChunkBlockSize
      omega)
    (by
      intro block hmem
      exact
        fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem)

theorem fixedWeightSubLogSharedDecoderPayload_length_eq
    (bits : List Bool) :
    (fixedWeightSubLogSharedDecoderPayload bits).length =
      fixedWeightSubLogChunkDenseDecoderBudget bits.length := by
  have hlen :=
    fixedWeightSharedDecodePayload_length_eq
      (rowCount := fixedWeightSubLogChunkDenseDecoderRows bits.length)
      (wordSize := Nat.log2 bits.length + 1)
      (blockSize := fixedWeightSubLogChunkBlockSize bits.length)
      (blocks := fixedWeightSubLogChunkBlocksWithSentinel bits)
      (hword := by omega)
      (hblockSize_le_wordSize := by
        unfold fixedWeightSubLogChunkBlockSize
        omega)
      (hblocks := by
        intro block hmem
        exact
          fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem)
  simpa [fixedWeightSubLogSharedDecoderPayload,
    fixedWeightSubLogChunkDenseDecoderBudget_eq_rows_mul]
    using hlen

theorem fixedWeightSubLogSharedDecoderStore_get?_of_block
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block) :
    (fixedWeightSubLogSharedDecoderStore bits).store.words[
        fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block)]? =
      some block := by
  let slot :=
    fixedWeightSharedDecodeSlot block.length (trueCount block)
      (fixedWeightCode block)
  have hslot_lt :
      slot < fixedWeightSubLogChunkDenseDecoderRows bits.length := by
    exact
      fixedWeightSubLogChunkBlocksWithSentinel_sharedDecodeSlot_lt_rows
        hblock
  have hunique :
      forall {other : List Bool},
        List.Mem other (fixedWeightSubLogChunkBlocksWithSentinel bits) ->
          fixedWeightSharedDecodeSlot other.length (trueCount other)
              (fixedWeightCode other) = slot ->
            other = block := by
    intro other _hmem hother
    exact fixedWeightSharedDecodeSlot_unique_for_blocks hother
  simpa [fixedWeightSubLogSharedDecoderStore, slot] using
    fixedWeightSharedDecodeBoundedStore_get?_of_block
      (rowCount := fixedWeightSubLogChunkDenseDecoderRows bits.length)
      (wordSize := Nat.log2 bits.length + 1)
      (blockSize := fixedWeightSubLogChunkBlockSize bits.length)
      (blocks := fixedWeightSubLogChunkBlocksWithSentinel bits)
      (hword := by omega)
      (hblockSize_le_wordSize := by
        unfold fixedWeightSubLogChunkBlockSize
        omega)
      (hblocks := by
        intro candidate hmem
        exact
          fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem)
      hblock hslot_lt rfl hunique

private theorem fixedWeightSubLogChunkDenseDecoderBudget_littleO_core :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkDenseDecoderBudget := by
  intro scale hscale
  refine ⟨2 ^ (128 * scale + 8), ?_⟩
  intro n hn
  unfold fixedWeightSubLogChunkDenseDecoderBudget
  have hBeq :
      fixedWeightSubLogChunkBlockSize n = Nat.log2 n / 8 + 1 := rfl
  have hpos : 0 < 2 ^ (128 * scale + 8) := Nat.pow_pos (by omega)
  have hn1 : 1 <= n := Nat.le_trans hpos hn
  have hlogbig : 128 * scale + 8 <= Nat.log2 n := by
    rcases Nat.lt_or_ge (Nat.log2 n) (128 * scale + 8) with hlt | hge
    · exfalso
      have h2 : 2 ^ (Nat.log2 n + 1) <= 2 ^ (128 * scale + 8) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le h3 (Nat.le_trans h2 hn))
    · exact hge
  have hQ :
      (fixedWeightSubLogChunkBlockSize n + 1) *
          (fixedWeightSubLogChunkBlockSize n + 1) <=
        2 ^ (2 * fixedWeightSubLogChunkBlockSize n + 2) := by
    have hmul :
        (fixedWeightSubLogChunkBlockSize n + 1) *
            (fixedWeightSubLogChunkBlockSize n + 1) <=
          2 ^ (fixedWeightSubLogChunkBlockSize n + 1) *
            2 ^ (fixedWeightSubLogChunkBlockSize n + 1) :=
      Nat.mul_le_mul
        (SuccinctSpace.nat_le_two_pow
          (fixedWeightSubLogChunkBlockSize n + 1))
        (SuccinctSpace.nat_le_two_pow
          (fixedWeightSubLogChunkBlockSize n + 1))
    have heq :
        2 ^ (fixedWeightSubLogChunkBlockSize n + 1) *
            2 ^ (fixedWeightSubLogChunkBlockSize n + 1) =
          2 ^ (2 * fixedWeightSubLogChunkBlockSize n + 2) := by
      rw [<- Nat.pow_add]
      congr 1
      omega
    exact Nat.le_trans hmul (Nat.le_of_eq heq)
  have hR :
      scale * (Nat.log2 n + 1) <=
        2 ^ fixedWeightSubLogChunkBlockSize n := by
    have hq8 : 2 * (8 * scale) + 1 <= Nat.log2 n / 8 := by
      omega
    have hstep :
        (8 * scale) * (Nat.log2 n / 8 + 1) <=
          2 ^ (Nat.log2 n / 8) :=
      scale_mul_succ_le_two_pow hq8
    have hwiden : Nat.log2 n + 1 <= 8 * (Nat.log2 n / 8 + 1) := by
      omega
    have hcollapse :
        scale * (8 * (Nat.log2 n / 8 + 1)) =
          (8 * scale) * (Nat.log2 n / 8 + 1) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have hexple :
        Nat.log2 n / 8 <= fixedWeightSubLogChunkBlockSize n := by
      omega
    calc
      scale * (Nat.log2 n + 1)
          <= scale * (8 * (Nat.log2 n / 8 + 1)) :=
            Nat.mul_le_mul_left _ hwiden
      _ = (8 * scale) * (Nat.log2 n / 8 + 1) := hcollapse
      _ <= 2 ^ (Nat.log2 n / 8) := hstep
      _ <= 2 ^ fixedWeightSubLogChunkBlockSize n :=
        Nat.pow_le_pow_right (by omega) hexple
  have hexp :
      4 * fixedWeightSubLogChunkBlockSize n + 2 <= Nat.log2 n := by
    omega
  have hpow_le_n :
      2 ^ (4 * fixedWeightSubLogChunkBlockSize n + 2) <= n :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) hexp)
      (Nat.log2_self_le (by omega))
  calc
    scale *
        (2 ^ fixedWeightSubLogChunkBlockSize n *
            ((fixedWeightSubLogChunkBlockSize n + 1) *
              (fixedWeightSubLogChunkBlockSize n + 1)) *
          (Nat.log2 n + 1))
        =
      2 ^ fixedWeightSubLogChunkBlockSize n *
          ((fixedWeightSubLogChunkBlockSize n + 1) *
            (fixedWeightSubLogChunkBlockSize n + 1)) *
        (scale * (Nat.log2 n + 1)) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
    _ <=
      2 ^ fixedWeightSubLogChunkBlockSize n *
          2 ^ (2 * fixedWeightSubLogChunkBlockSize n + 2) *
        2 ^ fixedWeightSubLogChunkBlockSize n :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) hQ) hR
    _ = 2 ^ (4 * fixedWeightSubLogChunkBlockSize n + 2) := by
      rw [<- Nat.pow_add, <- Nat.pow_add]
      congr 1
      omega
    _ <= n := hpow_le_n

def fixedWeightSubLogSharedDecoderOverhead
    (wordSize : Nat -> Nat) : Nat -> Nat :=
  fun n => fixedWeightSubLogChunkDenseDecoderRows n * wordSize n

theorem fixedWeightSubLogSharedDecoderOverhead_littleO_of_wordSize_le_log
    {wordSize : Nat -> Nat}
    (hwordSize :
      forall n : Nat, wordSize n <= Nat.log2 n + 1) :
    SuccinctSpace.LittleOLinear
      (fixedWeightSubLogSharedDecoderOverhead wordSize) := by
  apply SuccinctSpace.LittleOLinear.of_le
    fixedWeightSubLogChunkDenseDecoderBudget_littleO_core
  intro n
  unfold fixedWeightSubLogSharedDecoderOverhead
  rw [fixedWeightSubLogChunkDenseDecoderBudget_eq_rows_mul]
  exact Nat.mul_le_mul_left _ (hwordSize n)

/-- Final block-local select route fields produced by a Clark-style locator. -/
structure FixedWeightSubLogClarkSelectRouteFields where
  blockIndex : Nat
  localOccurrence : Nat
  blockStart : Nat
deriving Repr, DecidableEq

def fixedWeightSubLogSelectBlockIndex
    (bits : List Bool) (idx : Nat) : Nat :=
  idx / fixedWeightSubLogChunkBlockSize bits.length

def fixedWeightSubLogSelectBlockStart
    (bits : List Bool) (idx : Nat) : Nat :=
  fixedWeightSubLogSelectBlockIndex bits idx *
    fixedWeightSubLogChunkBlockSize bits.length

def fixedWeightSubLogSelectLocalOccurrence
    (bits : List Bool) (target : Bool) (occurrence idx : Nat) : Nat :=
  occurrence -
    Succinct.rankPrefix target bits
      (fixedWeightSubLogSelectBlockStart bits idx)

/--
Translate a global selected position into the sub-log fixed-weight block route
fields consumed by the compressed/FID local decoder.
-/
def fixedWeightSubLogSelectRouteFieldsOfPosition
    (bits : List Bool) (target : Bool) (occurrence idx : Nat) :
    FixedWeightSubLogClarkSelectRouteFields where
  blockIndex := fixedWeightSubLogSelectBlockIndex bits idx
  localOccurrence :=
    fixedWeightSubLogSelectLocalOccurrence bits target occurrence idx
  blockStart := fixedWeightSubLogSelectBlockStart bits idx

/--
The position-to-route translation is semantically valid for the sub-log
sentinel block decomposition.
-/
theorem fixedWeightSubLogSelectRouteFieldsOfPosition_select_exact
    {bits : List Bool} {target : Bool} {occurrence idx : Nat}
    (hselect : Succinct.select target bits occurrence = some idx) :
    exists block,
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[
          (fixedWeightSubLogSelectRouteFieldsOfPosition
            bits target occurrence idx).blockIndex]? = some block /\
        (Succinct.select target block
            (fixedWeightSubLogSelectRouteFieldsOfPosition
              bits target occurrence idx).localOccurrence).map
            (fun offset =>
              (fixedWeightSubLogSelectRouteFieldsOfPosition
                bits target occurrence idx).blockStart + offset) =
          Succinct.select target bits occurrence := by
  let blockSize := fixedWeightSubLogChunkBlockSize bits.length
  have hblockSize : 0 < blockSize := by
    unfold blockSize
    exact fixedWeightSubLogChunkBlockSize_pos bits.length
  have hidx_lt : idx < bits.length :=
    Succinct.select_bounds hselect
  have hstart_lt :
      (idx / blockSize) * blockSize < bits.length := by
    have hstart_le : (idx / blockSize) * blockSize <= idx :=
      Nat.div_mul_le_self idx blockSize
    omega
  cases hgetOpt :
      (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? with
  | none =>
      exfalso
      have hsome :
          exists block,
            (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? =
              some block := by
        rcases
            SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
              (wordSize := blockSize) hblockSize
              (payload := bits) (i := idx / blockSize) hstart_lt with
          ⟨block, hchunk⟩
        exact ⟨block, by
          simpa [fixedWeightChunkBlocks] using hchunk⟩
      rcases hsome with ⟨block, hget⟩
      simp [hgetOpt] at hget
  | some block =>
      have hget :
          (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? =
            some block := hgetOpt
      refine ⟨block, ?_, ?_⟩
      · simpa [fixedWeightSubLogChunkBlocksWithSentinel,
          fixedWeightSubLogSelectRouteFieldsOfPosition,
          fixedWeightSubLogSelectBlockIndex, blockSize] using
          fixedWeightChunkBlocksWithSentinel_get_chunk hget
      · have hexact :=
          fixedWeightChunkBlocks_get?_select_exact_of_global_select
            hblockSize hselect hget
        rw [hselect]
        simpa [fixedWeightSubLogSelectRouteFieldsOfPosition,
          fixedWeightSubLogSelectBlockIndex,
          fixedWeightSubLogSelectBlockStart,
          fixedWeightSubLogSelectLocalOccurrence, blockSize] using hexact

def fixedWeightSubLogClarkSelectRouteOverhead : Nat -> Nat :=
  fun n =>
    GenericSelect.canonicalSparseExceptionSelectOverhead n +
      GenericSelect.canonicalSparseExceptionSelectOverhead n

theorem fixedWeightSubLogClarkSelectRouteOverhead_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogClarkSelectRouteOverhead := by
  unfold fixedWeightSubLogClarkSelectRouteOverhead
  exact
    GenericSelect.canonicalSparseExceptionSelectOverhead_littleO.add
      GenericSelect.canonicalSparseExceptionSelectOverhead_littleO

/--
Concrete sampled select-route payload: one generic sparse/dense Clark-style
source for `true` and one for `false`.

This is intentionally not the final compressed/FID payload claim: the generic
dense branch still has raw bit-word reads in its `readWords`.  The theorem
below exposes the exact route-field translation without passing through the
too-weak `ChargedSelectPositionSource` oracle.
-/
def fixedWeightSubLogClarkSelectRoutePayload
    (bits : List Bool) : List Bool :=
  (GenericSelect.sparseExceptionSelectData bits true).payload ++
    (GenericSelect.sparseExceptionSelectData bits false).payload

def fixedWeightSubLogClarkSelectRouteReadWords
    (bits : List Bool) : List (List Bool) :=
  (GenericSelect.sparseExceptionSelectData bits true).readWords ++
    (GenericSelect.sparseExceptionSelectData bits false).readWords

def fixedWeightSubLogClarkSelectRouteFieldsCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option FixedWeightSubLogClarkSelectRouteFields) :=
  Costed.map
    (fun pos? =>
      pos?.map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence))
    ((GenericSelect.sparseExceptionSelectData bits target).selectCosted
      occurrence)

theorem fixedWeightSubLogClarkSelectRoutePayload_length_le
    (bits : List Bool) :
    (fixedWeightSubLogClarkSelectRoutePayload bits).length <=
      fixedWeightSubLogClarkSelectRouteOverhead bits.length := by
  have htrue :
      (GenericSelect.sparseExceptionSelectData bits true).payload.length <=
        GenericSelect.canonicalSparseExceptionSelectOverhead
          bits.length := by
    have h := GenericSelect.sparseExceptionSelectData_profile bits true
    simpa using h.1
  have hfalse :
      (GenericSelect.sparseExceptionSelectData bits false).payload.length <=
        GenericSelect.canonicalSparseExceptionSelectOverhead
          bits.length := by
    have h := GenericSelect.sparseExceptionSelectData_profile bits false
    simpa using h.1
  simp [fixedWeightSubLogClarkSelectRoutePayload,
    fixedWeightSubLogClarkSelectRouteOverhead]
  omega

theorem fixedWeightSubLogClarkSelectRouteFieldsCosted_cost_le
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightSubLogClarkSelectRouteFieldsCosted
      bits target occurrence).cost <=
      GenericSelect.sparseDenseSelectQueryCost := by
  have h :=
    (GenericSelect.sparseExceptionSelectData bits target).selectCosted_cost_le
      occurrence
  simpa [fixedWeightSubLogClarkSelectRouteFieldsCosted] using h

theorem fixedWeightSubLogClarkSelectRouteFieldsCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightSubLogClarkSelectRouteFieldsCosted
      bits target occurrence).erase =
      (Succinct.select target bits occurrence).map
        (fixedWeightSubLogSelectRouteFieldsOfPosition
          bits target occurrence) := by
  have h :=
    (GenericSelect.sparseExceptionSelectData bits target).selectCosted_exact
      occurrence
  simpa [fixedWeightSubLogClarkSelectRouteFieldsCosted,
    Costed.erase_map] using congrArg
      (fun pos? =>
        pos?.map
          (fixedWeightSubLogSelectRouteFieldsOfPosition
            bits target occurrence)) h

theorem fixedWeightSubLogClarkSelectRouteFieldsCosted_select_exact
    {bits : List Bool} {target : Bool} {occurrence : Nat}
    {fields : FixedWeightSubLogClarkSelectRouteFields}
    (hfields :
      (fixedWeightSubLogClarkSelectRouteFieldsCosted
        bits target occurrence).erase = some fields) :
    exists block,
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[
          fields.blockIndex]? = some block /\
        (Succinct.select target block fields.localOccurrence).map
            (fun offset => fields.blockStart + offset) =
          Succinct.select target bits occurrence := by
  have herase :=
    fixedWeightSubLogClarkSelectRouteFieldsCosted_erase
      bits target occurrence
  rw [hfields] at herase
  cases hselect : Succinct.select target bits occurrence with
  | none =>
      simp [hselect] at herase
  | some idx =>
      have hfields_eq :
          fields =
            fixedWeightSubLogSelectRouteFieldsOfPosition
              bits target occurrence idx := by
        simpa [hselect] using herase
      subst fields
      simpa [hselect] using
        fixedWeightSubLogSelectRouteFieldsOfPosition_select_exact
          hselect

theorem fixedWeightSubLogClarkSelectRouteReadWords_length_le_machine
    (bits : List Bool) :
    forall {word : List Bool},
      List.Mem word (fixedWeightSubLogClarkSelectRouteReadWords bits) ->
        word.length <= SuccinctRank.machineWordBits bits.length := by
  intro word hmem
  unfold fixedWeightSubLogClarkSelectRouteReadWords at hmem
  rcases List.mem_append.mp hmem with htrue | hfalse
  · have h := GenericSelect.sparseExceptionSelectData_profile bits true
    exact h.2.2.2.2 htrue
  · have h := GenericSelect.sparseExceptionSelectData_profile bits false
    exact h.2.2.2.2 hfalse

/--
Concrete sampled select route-field profile, below the abstract
`ChargedSelectPositionSource` adapter.

It proves that the existing sparse/dense Clark-style source can be charged and
translated to valid sub-log fixed-weight block route fields.  Its `readWords`
clause is deliberately exposed because the dense generic source still reads raw
bit chunks; replacing those dense reads with packed-code/shared-decoder reads is
the remaining compressed/FID constructor step.
-/
theorem fixedWeightSubLogClarkSelectRouteFields_profile
    (bits : List Bool) :
    (fixedWeightSubLogClarkSelectRoutePayload bits).length <=
        fixedWeightSubLogClarkSelectRouteOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogClarkSelectRouteOverhead /\
      (forall target occurrence,
        (fixedWeightSubLogClarkSelectRouteFieldsCosted
          bits target occurrence).cost <=
          GenericSelect.sparseDenseSelectQueryCost) /\
      (forall target occurrence
          (fields : FixedWeightSubLogClarkSelectRouteFields),
        (fixedWeightSubLogClarkSelectRouteFieldsCosted
          bits target occurrence).erase = some fields ->
          exists block,
            (fixedWeightSubLogChunkBlocksWithSentinel bits)[
                fields.blockIndex]? = some block /\
              (Succinct.select target block fields.localOccurrence).map
                  (fun offset => fields.blockStart + offset) =
                Succinct.select target bits occurrence) /\
      forall {word : List Bool},
        List.Mem word (fixedWeightSubLogClarkSelectRouteReadWords bits) ->
          word.length <= SuccinctRank.machineWordBits bits.length := by
  exact
    ⟨fixedWeightSubLogClarkSelectRoutePayload_length_le bits,
      fixedWeightSubLogClarkSelectRouteOverhead_littleO,
      fixedWeightSubLogClarkSelectRouteFieldsCosted_cost_le bits,
      (fun target occurrence fields hfields =>
        fixedWeightSubLogClarkSelectRouteFieldsCosted_select_exact hfields),
      fixedWeightSubLogClarkSelectRouteReadWords_length_le_machine bits⟩

namespace FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily

def toSubLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hblocks :
      forall bits : List Bool,
        family.blocks bits = fixedWeightSubLogChunkBlocksWithSentinel bits)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (classLengthFieldWidth : forall _bits : List Bool, Nat)
    (hclassLengthFieldWidth_le_wordSize :
      forall bits : List Bool,
        classLengthFieldWidth bits <= family.wordSize bits.length)
    (hblockSize_lt_classLengthFieldWidthPow :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize <
          2 ^ classLengthFieldWidth bits)
    (hsubLogBlockSize_le_wordSize :
      forall bits : List Bool,
        fixedWeightSubLogChunkBlockSize bits.length <=
          family.wordSize bits.length)
    (hclassLengthOverhead_bound :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (classLengthFieldWidth bits)
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hroutePlusTable : routeCost + 5 <= queryCost) :
    FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily
      (fixedWeightAmbientBlockAuxiliaryOverhead slots)
      classLengthOverhead
      (fixedWeightSubLogSharedDecoderOverhead family.wordSize)
      routeCost queryCost :=
  family.toSplitWidthTableRAMRouteDirectoryFamily
    hclassLengthO
    (fixedWeightSubLogSharedDecoderOverhead_littleO_of_wordSize_le_log
      (by
        intro n
        let bits := List.replicate n false
        have h :=
          (family.componentData bits).routeData.wordSize_le_ambient
        simpa [bits] using h))
    classLengthFieldWidth
    hclassLengthFieldWidth_le_wordSize
    hblockSize_lt_classLengthFieldWidthPow
    (fun bits =>
      fixedWeightSharedDecodePayload
        (fixedWeightSubLogChunkDenseDecoderRows bits.length)
        (family.wordSize bits.length)
        (fixedWeightSubLogChunkBlocksWithSentinel bits))
    (fun bits =>
      fixedWeightSharedDecodeBoundedStore
        (fixedWeightSubLogChunkDenseDecoderRows bits.length)
        (family.wordSize bits.length)
        (fixedWeightSubLogChunkBlockSize bits.length)
        (fixedWeightSubLogChunkBlocksWithSentinel bits)
        (family.componentData bits).routeData.wordSize_pos
        (hsubLogBlockSize_le_wordSize bits)
        (by
          intro block hmem
          exact
            fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem))
    (by
      intro bits
      unfold fixedWeightSubLogSharedDecoderOverhead
      exact
        fixedWeightSharedDecodePayload_length_eq
          (hword := (family.componentData bits).routeData.wordSize_pos)
          (hblockSize_le_wordSize := hsubLogBlockSize_le_wordSize bits)
          (hblocks := by
            intro block hmem
            exact
              fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem))
    (by
      intro bits blockIndex block hblock
      have hblockSub :
          (fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
            some block := by
        simpa [hblocks bits] using hblock
      let slot :=
        fixedWeightSharedDecodeSlot block.length (trueCount block)
          (fixedWeightCode block)
      have hslot_lt :
          slot < fixedWeightSubLogChunkDenseDecoderRows bits.length := by
        exact
          fixedWeightSubLogChunkBlocksWithSentinel_sharedDecodeSlot_lt_rows
            hblockSub
      have hunique :
          forall {other : List Bool},
            List.Mem other (fixedWeightSubLogChunkBlocksWithSentinel bits) ->
              fixedWeightSharedDecodeSlot other.length (trueCount other)
                  (fixedWeightCode other) = slot ->
                other = block := by
        intro other _hmem hother
        exact fixedWeightSharedDecodeSlot_unique_for_blocks hother
      simpa [slot] using
        fixedWeightSharedDecodeBoundedStore_get?_of_block
          (rowCount := fixedWeightSubLogChunkDenseDecoderRows bits.length)
          (wordSize := family.wordSize bits.length)
          (blockSize := fixedWeightSubLogChunkBlockSize bits.length)
          (blocks := fixedWeightSubLogChunkBlocksWithSentinel bits)
          (hword := (family.componentData bits).routeData.wordSize_pos)
          (hblockSize_le_wordSize := hsubLogBlockSize_le_wordSize bits)
          (hblocks := by
            intro candidate hmem
            exact
              fixedWeightSubLogChunkBlocksWithSentinel_block_length_le hmem)
          hblockSub hslot_lt rfl hunique)
    hclassLengthOverhead_bound
    hroutePlusTable

theorem subLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead primaryOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hblocks :
      forall bits : List Bool,
        family.blocks bits = fixedWeightSubLogChunkBlocksWithSentinel bits)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (classLengthFieldWidth : forall _bits : List Bool, Nat)
    (hclassLengthFieldWidth_le_wordSize :
      forall bits : List Bool,
        classLengthFieldWidth bits <= family.wordSize bits.length)
    (hblockSize_lt_classLengthFieldWidthPow :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize <
          2 ^ classLengthFieldWidth bits)
    (hsubLogBlockSize_le_wordSize :
      forall bits : List Bool,
        fixedWeightSubLogChunkBlockSize bits.length <=
          family.wordSize bits.length)
    (hclassLengthOverhead_bound :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (classLengthFieldWidth bits)
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hroutePlusTable : routeCost + 5 <= queryCost)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget
            (fixedWeightSubLogChunkBlocksWithSentinel bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.compressedOverhead
          (fixedWeightAmbientBlockAuxiliaryOverhead slots)
          classLengthOverhead
          (fixedWeightSubLogSharedDecoderOverhead family.wordSize)
          primaryOverhead) /\
      forall bits : List Bool,
        let concreteFamily :=
          family.toSubLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily
            hblocks hclassLengthO classLengthFieldWidth
            hclassLengthFieldWidth_le_wordSize
            hblockSize_lt_classLengthFieldWidthPow
            hsubLogBlockSize_le_wordSize
            hclassLengthOverhead_bound
            hroutePlusTable
        let data := concreteFamily.componentData bits
        let directory := concreteFamily.directory primaryOverhead
          (by
            intro inputBits
            change
              fixedWeightBlockPayloadBudget (family.blocks inputBits) <=
                fixedWeightPayloadBudget inputBits +
                  primaryOverhead inputBits.length
            simpa [hblocks inputBits] using hprimary inputBits) bits
        data.SplitWidthTableRAMRouteDirectoryProfile /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.compressedOverhead
                (fixedWeightAmbientBlockAuxiliaryOverhead slots)
                classLengthOverhead
                (fixedWeightSubLogSharedDecoderOverhead family.wordSize)
                primaryOverhead bits.length /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.combinedAuxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessQueryCosted i).cost <= queryCost /\
              (directory.accessQueryCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankQueryCosted target pos).cost <= queryCost /\
              (directory.rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectQueryCosted target occurrence).cost <=
                queryCost /\
              (directory.selectQueryCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.word_bounded_compressed_profile_of_primary_budget
      (family.toSubLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily
        hblocks hclassLengthO classLengthFieldWidth
        hclassLengthFieldWidth_le_wordSize
        hblockSize_lt_classLengthFieldWidthPow
        hsubLogBlockSize_le_wordSize
        hclassLengthOverhead_bound
        hroutePlusTable)
      primaryOverhead hprimaryO
      (by
        intro bits
        change
          fixedWeightBlockPayloadBudget (family.blocks bits) <=
            fixedWeightPayloadBudget bits + primaryOverhead bits.length
        simpa [hblocks bits] using hprimary bits)

theorem subLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hblocks :
      forall bits : List Bool,
        family.blocks bits = fixedWeightSubLogChunkBlocksWithSentinel bits)
    (hclassLengthFieldWidth_le_wordSize :
      forall bits : List Bool,
        fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length <=
          family.wordSize bits.length)
    (hblockSize_lt_classLengthFieldWidthPow :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize <
          2 ^ fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length)
    (hsubLogBlockSize_le_wordSize :
      forall bits : List Bool,
        fixedWeightSubLogChunkBlockSize bits.length <=
          family.wordSize bits.length)
    (hroutePlusTable : routeCost + 5 <= queryCost) :
    SuccinctSpace.LittleOLinear
        (FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.compressedOverhead
          (fixedWeightAmbientBlockAuxiliaryOverhead slots)
          fixedWeightSubLogChunkClassLengthOverhead
          (fixedWeightSubLogSharedDecoderOverhead family.wordSize)
          fixedWeightSubLogChunkBlockCountBoundWithSentinel) /\
      forall bits : List Bool,
        let concreteFamily :=
          family.toSubLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily
            hblocks fixedWeightSubLogChunkClassLengthOverhead_littleO
            (fun bits => fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length)
            hclassLengthFieldWidth_le_wordSize
            hblockSize_lt_classLengthFieldWidthPow
            hsubLogBlockSize_le_wordSize
            (by
              intro inputBits
              change
                fixedWeightBlockClassLengthTableOverhead
                    (fixedWeightSubLogChunkClassLengthFieldWidthBound
                      inputBits.length)
                    (family.blocks inputBits) <=
                  fixedWeightSubLogChunkClassLengthOverhead
                    inputBits.length
              simpa [hblocks inputBits] using
                fixedWeightSubLogChunkBlockClassLengthTableOverhead_le
                  inputBits)
            hroutePlusTable
        let data := concreteFamily.componentData bits
        let directory := concreteFamily.directory
          fixedWeightSubLogChunkBlockCountBoundWithSentinel
          (by
            intro inputBits
            change
              fixedWeightBlockPayloadBudget (family.blocks inputBits) <=
                fixedWeightPayloadBudget inputBits +
                  fixedWeightSubLogChunkBlockCountBoundWithSentinel
                    inputBits.length
            simpa [hblocks inputBits] using
              fixedWeightSubLogChunkBlockPayloadBudget_le_payloadBudget_add_bound
                inputBits) bits
        data.SplitWidthTableRAMRouteDirectoryProfile /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              FixedWeightAmbientTableRAMSplitWidthRouteDirectoryFamily.compressedOverhead
                (fixedWeightAmbientBlockAuxiliaryOverhead slots)
                fixedWeightSubLogChunkClassLengthOverhead
                (fixedWeightSubLogSharedDecoderOverhead family.wordSize)
                fixedWeightSubLogChunkBlockCountBoundWithSentinel
                bits.length /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.combinedAuxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessQueryCosted i).cost <= queryCost /\
              (directory.accessQueryCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankQueryCosted target pos).cost <= queryCost /\
              (directory.rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectQueryCosted target occurrence).cost <=
                queryCost /\
              (directory.selectQueryCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    family.subLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily_profile_of_primary_budget
      hblocks
      fixedWeightSubLogChunkClassLengthOverhead_littleO
      (fun bits => fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length)
      hclassLengthFieldWidth_le_wordSize
      hblockSize_lt_classLengthFieldWidthPow
      hsubLogBlockSize_le_wordSize
      (by
        intro bits
        change
          fixedWeightBlockClassLengthTableOverhead
              (fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length)
              (family.blocks bits) <=
            fixedWeightSubLogChunkClassLengthOverhead bits.length
        simpa [hblocks bits] using
          fixedWeightSubLogChunkBlockClassLengthTableOverhead_le bits)
      hroutePlusTable
      fixedWeightSubLogChunkBlockCountBoundWithSentinel_littleO
      (by
        intro bits
        simpa using
          fixedWeightSubLogChunkBlockPayloadBudget_le_payloadBudget_add_bound
            bits)

end FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily

/--
The dense shared decoder budget for sub-log chunks is `o(n)`.

This is the concrete positive counterpart to
`no_fixedWeightLogChunk_dense_decoder_littleO`: the same dense table idea is too
large at full-log blocks, but fits the auxiliary budget after shrinking blocks.
-/
theorem fixedWeightSubLogChunkDenseDecoderBudget_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkDenseDecoderBudget := by
  intro scale hscale
  refine ⟨2 ^ (128 * scale + 8), ?_⟩
  intro n hn
  unfold fixedWeightSubLogChunkDenseDecoderBudget
  have hBeq :
      fixedWeightSubLogChunkBlockSize n = Nat.log2 n / 8 + 1 := rfl
  have hpos : 0 < 2 ^ (128 * scale + 8) := Nat.pow_pos (by omega)
  have hn1 : 1 <= n := Nat.le_trans hpos hn
  have hlogbig : 128 * scale + 8 <= Nat.log2 n := by
    rcases Nat.lt_or_ge (Nat.log2 n) (128 * scale + 8) with hlt | hge
    · exfalso
      have h2 : 2 ^ (Nat.log2 n + 1) <= 2 ^ (128 * scale + 8) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le h3 (Nat.le_trans h2 hn))
    · exact hge
  have hQ :
      (fixedWeightSubLogChunkBlockSize n + 1) *
          (fixedWeightSubLogChunkBlockSize n + 1) <=
        2 ^ (2 * fixedWeightSubLogChunkBlockSize n + 2) := by
    have hmul :
        (fixedWeightSubLogChunkBlockSize n + 1) *
            (fixedWeightSubLogChunkBlockSize n + 1) <=
          2 ^ (fixedWeightSubLogChunkBlockSize n + 1) *
            2 ^ (fixedWeightSubLogChunkBlockSize n + 1) :=
      Nat.mul_le_mul
        (SuccinctSpace.nat_le_two_pow
          (fixedWeightSubLogChunkBlockSize n + 1))
        (SuccinctSpace.nat_le_two_pow
          (fixedWeightSubLogChunkBlockSize n + 1))
    have heq :
        2 ^ (fixedWeightSubLogChunkBlockSize n + 1) *
            2 ^ (fixedWeightSubLogChunkBlockSize n + 1) =
          2 ^ (2 * fixedWeightSubLogChunkBlockSize n + 2) := by
      rw [<- Nat.pow_add]
      congr 1
      omega
    exact Nat.le_trans hmul (Nat.le_of_eq heq)
  have hR :
      scale * (Nat.log2 n + 1) <=
        2 ^ fixedWeightSubLogChunkBlockSize n := by
    have hq8 : 2 * (8 * scale) + 1 <= Nat.log2 n / 8 := by
      omega
    have hstep :
        (8 * scale) * (Nat.log2 n / 8 + 1) <=
          2 ^ (Nat.log2 n / 8) :=
      scale_mul_succ_le_two_pow hq8
    have hwiden : Nat.log2 n + 1 <= 8 * (Nat.log2 n / 8 + 1) := by
      omega
    have hcollapse :
        scale * (8 * (Nat.log2 n / 8 + 1)) =
          (8 * scale) * (Nat.log2 n / 8 + 1) := by
      simp [Nat.mul_comm, Nat.mul_left_comm]
    have hexple :
        Nat.log2 n / 8 <= fixedWeightSubLogChunkBlockSize n := by
      omega
    calc
      scale * (Nat.log2 n + 1)
          <= scale * (8 * (Nat.log2 n / 8 + 1)) :=
            Nat.mul_le_mul_left _ hwiden
      _ = (8 * scale) * (Nat.log2 n / 8 + 1) := hcollapse
      _ <= 2 ^ (Nat.log2 n / 8) := hstep
      _ <= 2 ^ fixedWeightSubLogChunkBlockSize n :=
        Nat.pow_le_pow_right (by omega) hexple
  have hexp :
      4 * fixedWeightSubLogChunkBlockSize n + 2 <= Nat.log2 n := by
    omega
  have hpow_le_n :
      2 ^ (4 * fixedWeightSubLogChunkBlockSize n + 2) <= n :=
    Nat.le_trans (Nat.pow_le_pow_right (by omega) hexp)
      (Nat.log2_self_le (by omega))
  calc
    scale *
        (2 ^ fixedWeightSubLogChunkBlockSize n *
            ((fixedWeightSubLogChunkBlockSize n + 1) *
              (fixedWeightSubLogChunkBlockSize n + 1)) *
          (Nat.log2 n + 1))
        =
      2 ^ fixedWeightSubLogChunkBlockSize n *
          ((fixedWeightSubLogChunkBlockSize n + 1) *
            (fixedWeightSubLogChunkBlockSize n + 1)) *
        (scale * (Nat.log2 n + 1)) := by
          simp [Nat.mul_comm, Nat.mul_assoc]
    _ <=
      2 ^ fixedWeightSubLogChunkBlockSize n *
          2 ^ (2 * fixedWeightSubLogChunkBlockSize n + 2) *
        2 ^ fixedWeightSubLogChunkBlockSize n :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) hQ) hR
    _ = 2 ^ (4 * fixedWeightSubLogChunkBlockSize n + 2) := by
      rw [<- Nat.pow_add, <- Nat.pow_add]
      congr 1
      omega
    _ <= n := hpow_le_n

end RankSelectSpec

namespace RankSelect

/-- Public alias for the compressed/FID sub-log block size. -/
abbrev fixedWeightSubLogChunkBlockSize :=
  RankSelectSpec.fixedWeightSubLogChunkBlockSize

/-- Public alias for the sub-log chunk-count bound. -/
abbrev fixedWeightSubLogChunkBlockCountBound :=
  RankSelectSpec.fixedWeightSubLogChunkBlockCountBound

/-- Public alias for the sub-log sentinel chunk-count bound. -/
abbrev fixedWeightSubLogChunkBlockCountBoundWithSentinel :=
  RankSelectSpec.fixedWeightSubLogChunkBlockCountBoundWithSentinel

/-- Public alias for the sub-log class/length field-width bound. -/
abbrev fixedWeightSubLogChunkClassLengthFieldWidthBound :=
  RankSelectSpec.fixedWeightSubLogChunkClassLengthFieldWidthBound

/-- Public alias for the sub-log class/length overhead. -/
abbrev fixedWeightSubLogChunkClassLengthOverhead :=
  RankSelectSpec.fixedWeightSubLogChunkClassLengthOverhead

/-- Public alias for the sub-log dense shared-decoder budget. -/
abbrev fixedWeightSubLogChunkDenseDecoderBudget :=
  RankSelectSpec.fixedWeightSubLogChunkDenseDecoderBudget

/-- Public alias for the sub-log dense shared-decoder row count. -/
abbrev fixedWeightSubLogChunkDenseDecoderRows :=
  RankSelectSpec.fixedWeightSubLogChunkDenseDecoderRows

/-- Public sub-log dense shared-decoder budget theorem. -/
theorem fixedWeightSubLogChunkDenseDecoderBudgetLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkDenseDecoderBudget := by
  exact RankSelectSpec.fixedWeightSubLogChunkDenseDecoderBudget_littleO

/-- Public sub-log decoder budget decomposition into rows times word width. -/
theorem fixedWeightSubLogChunkDenseDecoderBudgetEqRowsMul
    (n : Nat) :
    fixedWeightSubLogChunkDenseDecoderBudget n =
      fixedWeightSubLogChunkDenseDecoderRows n * (Nat.log2 n + 1) := by
  exact
    RankSelectSpec.fixedWeightSubLogChunkDenseDecoderBudget_eq_rows_mul n

/-- Public sub-log sentinel chunk-count little-o theorem. -/
theorem fixedWeightSubLogChunkBlockCountBoundWithSentinelLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkBlockCountBoundWithSentinel := by
  exact
    RankSelectSpec.fixedWeightSubLogChunkBlockCountBoundWithSentinel_littleO

/-- Public sub-log chunk-count little-o theorem. -/
theorem fixedWeightSubLogChunkBlockCountBoundLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkBlockCountBound := by
  exact RankSelectSpec.fixedWeightSubLogChunkBlockCountBound_littleO

/-- Public sub-log primary block-code budget bridge. -/
theorem fixedWeightSubLogChunkBlockPayloadBudgetLePayloadBudgetAddBound
    (bits : List Bool) :
    RankSelectSpec.fixedWeightBlockPayloadBudget
        (RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits) <=
      RankSelectSpec.fixedWeightPayloadBudget bits +
        fixedWeightSubLogChunkBlockCountBoundWithSentinel bits.length := by
  exact
    RankSelectSpec.fixedWeightSubLogChunkBlockPayloadBudget_le_payloadBudget_add_bound
      bits

/-- Public sub-log class/length field-width little-o theorem. -/
theorem fixedWeightSubLogChunkClassLengthFieldWidthBoundLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkClassLengthFieldWidthBound := by
  exact
    RankSelectSpec.fixedWeightSubLogChunkClassLengthFieldWidthBound_littleO

/-- Public sub-log class/length overhead little-o theorem. -/
theorem fixedWeightSubLogChunkClassLengthOverheadLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogChunkClassLengthOverhead := by
  exact RankSelectSpec.fixedWeightSubLogChunkClassLengthOverhead_littleO

/-- Public sub-log class/length metadata budget bridge. -/
theorem fixedWeightSubLogChunkBlockClassLengthTableOverheadLe
    (bits : List Bool) :
    RankSelectSpec.fixedWeightBlockClassLengthTableOverhead
        (fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length)
        (RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits) <=
      fixedWeightSubLogChunkClassLengthOverhead bits.length := by
  exact
    RankSelectSpec.fixedWeightSubLogChunkBlockClassLengthTableOverhead_le
      bits

/--
Public row-bound theorem for the dense shared decoder over sub-log sentinel
chunks.
-/
theorem fixedWeightSubLogChunkBlocksWithSentinelSharedDecodeSlotLtRows
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (hblock :
      (RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block) :
    RankSelectSpec.fixedWeightSharedDecodeSlot block.length
        (RankSelectSpec.trueCount block)
        (RankSelectSpec.fixedWeightCode block) <
      fixedWeightSubLogChunkDenseDecoderRows bits.length := by
  exact
    RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel_sharedDecodeSlot_lt_rows
      hblock

/-- Public non-empty charged metadata schedule theorem for layout access routes. -/
theorem fixedWeightRouteFieldTableLayoutAccessMetadataReadsNeNil
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :
    (data.routeData.accessRoute i).metadataReads ≠ [] := by
  exact
    RankSelectSpec.fixedWeightRouteFieldTableLayout_accessMetadataReads_ne_nil
      data i

/-- Public non-empty charged metadata schedule theorem for layout rank routes. -/
theorem fixedWeightRouteFieldTableLayoutRankMetadataReadsNeNil
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    (data.routeData.rankRoute target pos).metadataReads ≠ [] := by
  exact
    RankSelectSpec.fixedWeightRouteFieldTableLayout_rankMetadataReads_ne_nil
      data target pos

/-- Public non-empty charged metadata schedule theorem for layout select routes. -/
theorem fixedWeightRouteFieldTableLayoutSelectMetadataReadsNeNil
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.routeData.selectRoute target occurrence).metadataReads ≠ [] := by
  exact
    RankSelectSpec.fixedWeightRouteFieldTableLayout_selectMetadataReads_ne_nil
      data target occurrence

/-- Public payload-length identity for concrete route-field table layouts. -/
theorem fixedWeightRouteFieldTableLayoutRoutePayloadLengthEq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.routeData.routePayload.length =
      (RankSelectSpec.fixedWeightRouteFieldTableLayoutPayload
        data.fieldWidth data.accessBlockEntries data.accessOffsetEntries
        data.rankBlockEntries data.rankLocalLimitEntries
        data.rankBaseRankEntries data.selectBlockEntries
        data.selectLocalOccurrenceEntries
        data.selectBlockStartEntries).length := by
  exact
    RankSelectSpec.fixedWeightRouteFieldTableLayout_routePayload_length_eq
      data

/--
Public counting theorem: a direct occurrence-indexed select block table must
contain all queried occurrence slots.
-/
theorem fixedWeightRouteFieldTableLayoutDirectSelectOccurrenceSlotsEntriesLengthGe
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {bound : Nat}
    (hdirect :
      forall occurrence,
        occurrence < bound ->
          data.selectBlockLocalSlot target occurrence = occurrence) :
    bound <= data.selectBlockEntries.length := by
  exact
    RankSelectSpec.fixedWeightRouteFieldTableLayout_directSelectOccurrenceSlots_entries_length_ge
      data hdirect

/--
Public payload lower bound for direct occurrence-indexed select route slots.
-/
theorem fixedWeightRouteFieldTableLayoutDirectSelectOccurrenceSlotsRoutePayloadLengthGe
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {bound : Nat}
    (hfield : 0 < data.fieldWidth)
    (hdirect :
      forall occurrence,
        occurrence < bound ->
          data.selectBlockLocalSlot target occurrence = occurrence) :
    bound <= data.routeData.routePayload.length := by
  exact
    RankSelectSpec.fixedWeightRouteFieldTableLayout_directSelectOccurrenceSlots_routePayload_length_ge
      data hfield hdirect

/--
Public obstruction: fixed-slot route-field layouts cannot use direct
occurrence-indexed select slots and remain in the sampled `o(n)` route budget.
-/
theorem noFixedWeightRouteFieldTableLayoutFamilyDirectSelectOccurrenceSlots
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hfield :
      forall n : Nat,
        0 <
          (family.componentData (List.replicate n false)).fieldWidth)
    (hdirect :
      forall n occurrence : Nat,
        occurrence < n ->
          (family.componentData
              (List.replicate n false)).selectBlockLocalSlot
            false occurrence = occurrence) :
    False := by
  exact
    RankSelectSpec.no_fixedWeightRouteFieldTableLayoutFamily_directSelectOccurrenceSlots
      family hfield hdirect

/--
Public guardrail: two select queries that read the same final route-field slots
must have the same select answer.
-/
theorem fixedWeightRouteFieldTableLayoutSameSelectSlotsSelectEq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {target : Bool} {occurrenceA occurrenceB : Nat}
    (hblock :
      data.selectBlockLocalSlot target occurrenceA =
        data.selectBlockLocalSlot target occurrenceB)
    (hlocal :
      data.selectLocalOccurrenceLocalSlot target occurrenceA =
        data.selectLocalOccurrenceLocalSlot target occurrenceB)
    (hstart :
      data.selectBlockStartLocalSlot target occurrenceA =
        data.selectBlockStartLocalSlot target occurrenceB) :
    Succinct.select target bits occurrenceA =
      Succinct.select target bits occurrenceB := by
  exact
    RankSelectSpec.fixedWeightRouteFieldTableLayout_sameSelectSlots_select_eq
      data hblock hlocal hstart

/-- Public alias for concrete sub-log Clark-style route fields. -/
abbrev fixedWeightSubLogClarkSelectRouteFields :=
  RankSelectSpec.FixedWeightSubLogClarkSelectRouteFields

/-- Public alias for the sampled route payload overhead. -/
abbrev fixedWeightSubLogClarkSelectRouteOverhead :=
  RankSelectSpec.fixedWeightSubLogClarkSelectRouteOverhead

/-- Public alias for the concrete sampled route payload. -/
abbrev fixedWeightSubLogClarkSelectRoutePayload :=
  RankSelectSpec.fixedWeightSubLogClarkSelectRoutePayload

/-- Public alias for the concrete sampled route read words. -/
abbrev fixedWeightSubLogClarkSelectRouteReadWords :=
  RankSelectSpec.fixedWeightSubLogClarkSelectRouteReadWords

/-- Public alias for the charged route-field computation. -/
abbrev fixedWeightSubLogClarkSelectRouteFieldsCosted :=
  RankSelectSpec.fixedWeightSubLogClarkSelectRouteFieldsCosted

/-- Public little-o theorem for the sampled route payload budget. -/
theorem fixedWeightSubLogClarkSelectRouteOverheadLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogClarkSelectRouteOverhead := by
  exact
    RankSelectSpec.fixedWeightSubLogClarkSelectRouteOverhead_littleO

/-- Public payload bound for the sampled route payload. -/
theorem fixedWeightSubLogClarkSelectRoutePayloadLengthLe
    (bits : List Bool) :
    (fixedWeightSubLogClarkSelectRoutePayload bits).length <=
      fixedWeightSubLogClarkSelectRouteOverhead bits.length := by
  exact
    RankSelectSpec.fixedWeightSubLogClarkSelectRoutePayload_length_le bits

/-- Public exactness theorem for charged route-field computation. -/
theorem fixedWeightSubLogClarkSelectRouteFieldsCostedSelectExact
    {bits : List Bool} {target : Bool} {occurrence : Nat}
    {fields : fixedWeightSubLogClarkSelectRouteFields}
    (hfields :
      (fixedWeightSubLogClarkSelectRouteFieldsCosted
        bits target occurrence).erase = some fields) :
    exists block,
      (RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits)[
          fields.blockIndex]? = some block /\
        (Succinct.select target block fields.localOccurrence).map
            (fun offset => fields.blockStart + offset) =
          Succinct.select target bits occurrence := by
  exact
    RankSelectSpec.fixedWeightSubLogClarkSelectRouteFieldsCosted_select_exact
      hfields

/-- Public profile for the concrete sampled sub-log select-route source. -/
theorem fixedWeightSubLogClarkSelectRouteFieldsProfile
    (bits : List Bool) :
    (fixedWeightSubLogClarkSelectRoutePayload bits).length <=
        fixedWeightSubLogClarkSelectRouteOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogClarkSelectRouteOverhead /\
      (forall target occurrence,
        (fixedWeightSubLogClarkSelectRouteFieldsCosted
          bits target occurrence).cost <=
          GenericSelect.sparseDenseSelectQueryCost) /\
      (forall target occurrence
          (fields : fixedWeightSubLogClarkSelectRouteFields),
        (fixedWeightSubLogClarkSelectRouteFieldsCosted
          bits target occurrence).erase = some fields ->
          exists block,
            (RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits)[
                fields.blockIndex]? = some block /\
              (Succinct.select target block fields.localOccurrence).map
                  (fun offset => fields.blockStart + offset) =
                Succinct.select target bits occurrence) /\
      forall {word : List Bool},
        List.Mem word (fixedWeightSubLogClarkSelectRouteReadWords bits) ->
          word.length <= SuccinctRank.machineWordBits bits.length := by
  exact
    RankSelectSpec.fixedWeightSubLogClarkSelectRouteFields_profile bits

/-- Public alias for the concrete sub-log shared decoder payload. -/
abbrev fixedWeightSubLogSharedDecoderPayload :=
  RankSelectSpec.fixedWeightSubLogSharedDecoderPayload

/-- Public alias for the concrete sub-log shared decoder payload store. -/
abbrev fixedWeightSubLogSharedDecoderStore :=
  RankSelectSpec.fixedWeightSubLogSharedDecoderStore

/-- Public alias for the word-size-parametric sub-log decoder overhead. -/
abbrev fixedWeightSubLogSharedDecoderOverhead :=
  RankSelectSpec.fixedWeightSubLogSharedDecoderOverhead

/-- Public exact payload-length theorem for the concrete sub-log decoder. -/
theorem fixedWeightSubLogSharedDecoderPayloadLengthEq
    (bits : List Bool) :
    (fixedWeightSubLogSharedDecoderPayload bits).length =
      fixedWeightSubLogChunkDenseDecoderBudget bits.length := by
  exact RankSelectSpec.fixedWeightSubLogSharedDecoderPayload_length_eq bits

/-- Public exact indexed-read theorem for the concrete sub-log decoder. -/
theorem fixedWeightSubLogSharedDecoderStoreGetOfBlock
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (hblock :
      (RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block) :
    (fixedWeightSubLogSharedDecoderStore bits).store.words[
        RankSelectSpec.fixedWeightSharedDecodeSlot block.length
          (RankSelectSpec.trueCount block)
          (RankSelectSpec.fixedWeightCode block)]? =
      some block := by
  exact
    RankSelectSpec.fixedWeightSubLogSharedDecoderStore_get?_of_block hblock

/--
Public little-o theorem for the sub-log shared decoder when the word-size
discipline is bounded by the ambient `log n + 1` word.
-/
theorem fixedWeightSubLogSharedDecoderOverheadLittleOOfWordSizeLeLog
    {wordSize : Nat -> Nat}
    (hwordSize :
      forall n : Nat, wordSize n <= Nat.log2 n + 1) :
    SuccinctSpace.LittleOLinear
      (fixedWeightSubLogSharedDecoderOverhead wordSize) := by
  exact
    RankSelectSpec.fixedWeightSubLogSharedDecoderOverhead_littleO_of_wordSize_le_log
      hwordSize

/--
Public constructor alias consuming a sub-log route-field layout family with the
concrete shared decoder payload.
-/
abbrev fixedWeightRouteFieldLayoutToSubLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily :=
  @RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.toSubLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily

/--
Public profile alias for the sub-log shared-decoder split-width route-directory
constructor, conditional only on the remaining route/class-length and primary
budget obligations.
-/
abbrev fixedWeightRouteFieldLayoutSubLogSharedDecoderSplitWidthProfileOfPrimaryBudget :=
  @RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.subLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily_profile_of_primary_budget

/--
Public profile alias for the sub-log shared-decoder split-width route-directory
constructor after discharging the sub-log primary and class/length budgets.
-/
abbrev fixedWeightRouteFieldLayoutSubLogSharedDecoderSplitWidthProfile :=
  @RankSelectSpec.FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily.subLogSharedDecoderSplitWidthTableRAMRouteDirectoryFamily_profile

end RankSelect

end RMQ
