import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerSourceAddress
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReadProgram

/-!
# All-size sparse-count prelude for the reviewer memory

The reviewer payload has one content-dependent length: the sparse-relative
table.  This module recovers that length from the three rank-directory words
that precede the table in the consumed payload.  The executable surface is a
fixed request/reply protocol whose state contains only size/header scalars and
prior replies.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ## The full-tail bridge -/

/-- A local-slot number never exceeds its base occurrence. -/
theorem packedReviewerLocalSlot_le_baseOccurrence (n slot : Nat) :
    slot <= GenericSelect.localBaseOccurrence n slot := by
  let slots := GenericSelect.localSlotsPerSuper n
  let ss := GenericSelect.superStride n
  let ls := GenericSelect.localStride n
  let q := slot / slots
  let r := slot % slots
  have hss : 0 < ss := GenericSelect.superStride_pos n
  have hls : 0 < ls := GenericSelect.localStride_pos n
  have hdecomp : slot = q * slots + r := by
    have h := Nat.div_add_mod slot slots
    simpa [q, r, Nat.mul_comm] using h.symm
  have hbase :
      GenericSelect.localBaseOccurrence n slot = q * ss + r * ls := by
    simpa [q, r, slots, ss, ls] using
      GenericSelect.localBaseOccurrence_mod n slot
  have hslotsLe : slots <= ss := by
    simpa [slots, ss, ls, GenericSelect.localSlotsPerSuper] using
      (GenericSelect.selectLocalSlotsPerSuper_le_superStride
        (hsuper := hss) (hlocal := hls))
  have hq : q * slots <= q * ss := Nat.mul_le_mul_left q hslotsLe
  have hr' : r <= r * ls := by
    have : 1 <= ls := by omega
    simpa using Nat.mul_le_mul_left r this
  rw [hbase, hdecomp]
  omega

/--
Once the local-slot number has reached the total occurrence count, both ends
of its local gap clamp to `bits.length`; hence it cannot be sparse.
-/
theorem packedReviewerLocalIsSparseException_false_of_count_le
    (bits : List Bool) (target : Bool) {slot : Nat}
    (hcount : GenericSelect.occurrenceCount bits target <= slot)
    (hslot : slot < GenericSelect.localSlotCount bits target) :
    GenericSelect.localIsSparseException bits target slot = false := by
  have hslotBase : slot <= GenericSelect.localBaseOccurrence bits.length slot :=
    packedReviewerLocalSlot_le_baseOccurrence bits.length slot
  have hbaseCount :
      GenericSelect.occurrenceCount bits target <=
        GenericSelect.localBaseOccurrence bits.length slot :=
    Nat.le_trans hcount hslotBase
  have hbaseNext :=
    GenericSelect.localBaseOccurrence_le_next_base bits.length slot
  have hnextCount :
      GenericSelect.occurrenceCount bits target <=
        GenericSelect.localBaseOccurrence bits.length (slot + 1) :=
    Nat.le_trans hbaseCount hbaseNext
  have hbasePos :=
    GenericSelect.position_eq_length_of_count_le bits target hbaseCount
  have hnextPos :=
    GenericSelect.position_eq_length_of_count_le bits target hnextCount
  have hgap :=
    GenericSelect.shortSuperLocalSpan_le_next_gap bits target hslot
  rw [hbasePos, hnextPos] at hgap
  have hspan : GenericSelect.shortSuperLocalSpan bits target slot = 0 := by
    omega
  unfold GenericSelect.localIsSparseException
  simp [hspan]

/-- Appending the unreachable tail does not change the sparse-flag rank. -/
theorem packedReviewerSparseFlagRank_full_eq_count
    (bits : List Bool) (target : Bool)
    (hcount :
      GenericSelect.occurrenceCount bits target <=
        GenericSelect.localSlotCount bits target) :
    RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionFlagBits bits target)
        (GenericSelect.localSlotCount bits target) =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionFlagBits bits target)
        (GenericSelect.occurrenceCount bits target) := by
  let count := GenericSelect.occurrenceCount bits target
  let full := GenericSelect.localSlotCount bits target
  have htail : forall d,
      count + d <= full ->
        RMQ.Succinct.rankPrefix true
            (GenericSelect.sparseExceptionFlagBits bits target) (count + d) =
          RMQ.Succinct.rankPrefix true
            (GenericSelect.sparseExceptionFlagBits bits target) count := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        intro hle
        have hle' : count + d <= full := by omega
        have hslot : count + d < full := by omega
        have hget :=
          GenericSelect.sparseExceptionFlagBits_get? bits target
            (globalLocalSlot := count + d) hslot
        have hrank :=
          GenericSelect.rankPrefix_succ_eq_of_get?
            (target := true)
            (bits := GenericSelect.sparseExceptionFlagBits bits target)
            (n := count + d) hget
        have hfalse :
            GenericSelect.localIsSparseException bits target (count + d) = false :=
          packedReviewerLocalIsSparseException_false_of_count_le bits target
            (by simp [count]) hslot
        rw [show count + (d + 1) = count + d + 1 by omega]
        rw [hrank, hfalse, ih hle']
        simp
  have hfinal := htail (full - count) (by omega)
  simpa [count, full, Nat.add_sub_of_le hcount] using hfinal

/--
The stored effective sparse-flag directory has exactly the same terminal rank
as the full flag vector used to size `sparseExceptionRelativeEntries`.
-/
theorem packedReviewerSparseFlagRank_full_eq_effective
    (bits : List Bool) (target : Bool) :
    RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionFlagBits bits target)
        (GenericSelect.localSlotCount bits target) =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionEffectiveFlagBits bits target)
        (GenericSelect.sparseExceptionEffectiveLocalSlotCount bits target) := by
  by_cases hfull :
      GenericSelect.localSlotCount bits target <=
        GenericSelect.occurrenceCount bits target
  · have heff :
        GenericSelect.sparseExceptionEffectiveLocalSlotCount bits target =
          GenericSelect.localSlotCount bits target := by
      unfold GenericSelect.sparseExceptionEffectiveLocalSlotCount
      exact Nat.min_eq_left hfull
    have hpref :=
      GenericSelect.sparseExceptionEffectiveFlagBits_prefix_eq bits target
        (globalLocalSlot := GenericSelect.localSlotCount bits target)
        (by simpa [heff])
    rw [heff]
    exact hpref.symm
  · have hcount :
        GenericSelect.occurrenceCount bits target <=
          GenericSelect.localSlotCount bits target := by omega
    have heff :
        GenericSelect.sparseExceptionEffectiveLocalSlotCount bits target =
          GenericSelect.occurrenceCount bits target := by
      unfold GenericSelect.sparseExceptionEffectiveLocalSlotCount
      exact Nat.min_eq_right hcount
    have htail :=
      packedReviewerSparseFlagRank_full_eq_count bits target hcount
    have hpref :=
      GenericSelect.sparseExceptionEffectiveFlagBits_prefix_eq bits target
        (globalLocalSlot := GenericSelect.occurrenceCount bits target)
        (by simpa [heff])
    rw [heff]
    exact htail.trans hpref.symm

/--
The exact sparse-relative row count is the terminal effective-flag rank times
the size-only local stride.  This is the all-size K1 factorization.
-/
theorem packedReviewerSparseCount_eq_effectiveRank (shape : CartesianShape) :
    packedReviewerSparseCount shape =
      RMQ.Succinct.rankPrefix true
          (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
          (packedSparseSlots shape.size) *
        packedSelectLocalStride shape.size := by
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have heff :
      GenericSelect.sparseExceptionEffectiveLocalSlotCount shape.bpCode false =
        packedSparseSlots shape.size := by
    rw [← GenericSelect.sparseExceptionEffectiveFlagBits_length,
      sparseFlagBits_length_eq_packed]
  have hrank :=
    packedReviewerSparseFlagRank_full_eq_effective shape.bpCode false
  unfold packedReviewerSparseCount
  rw [GenericSelect.sparseExceptionRelativeEntries_length, hrank, heff, hlen]
  rfl

/-! ## Shape-free reply decoder -/

/-- The one word index used by all three terminal-rank reads. -/
def packedReviewerSparsePreludeWordIndex (n : Nat) : Nat :=
  packedSparseSlots n / packedSparseWordSize n

/-- The within-word prefix length at the terminal sparse-flag position. -/
def packedReviewerSparsePreludeWordOffset (n : Nat) : Nat :=
  packedSparseSlots n -
    packedReviewerSparsePreludeWordIndex n * packedSparseWordSize n

/--
Decode the sparse-relative row count from the three prior physical replies.
There is no shape, memory, store, source list, callback, or proof argument.
-/
def packedReviewerSparseCountFromReplies (n : Nat)
    (superReply blockReply flagReply : List Bool) : Nat :=
  (SuccinctSpace.bitsToNatLE superReply +
      SuccinctSpace.bitsToNatLE blockReply +
      RMQ.RAM.boolRankPrefix true flagReply
        (packedReviewerSparsePreludeWordOffset n)) *
    packedSelectLocalStride n

set_option maxHeartbeats 1000000 in
/--
The three canonical source words exist at the shape-free endpoint index, and
decoding precisely those words yields the actual reviewer sparse count.
-/
theorem packedReviewerSparsePrelude_sourceReplies_exact
    (shape : CartesianShape) :
    exists superReply blockReply flagReply,
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
          .selectSparseRankSuperTrue)[
            packedReviewerSparsePreludeWordIndex shape.size]? =
        some superReply /\
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
          .selectSparseRankBlockTrue)[
            packedReviewerSparsePreludeWordIndex shape.size]? =
        some blockReply /\
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
          .selectSparseFlagBits)[
            packedReviewerSparsePreludeWordIndex shape.size]? =
        some flagReply /\
      packedReviewerSparseCountFromReplies shape.size
          superReply blockReply flagReply =
        packedReviewerSparseCount shape := by
  let flags :=
    GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false
  let data :=
    GenericSelect.sparseExceptionEffectiveFlagRankData shape.bpCode false
  let pos := packedSparseSlots shape.size
  let index := packedReviewerSparsePreludeWordIndex shape.size
  have hposEq : pos = flags.length := by
    simp [pos, flags, sparseFlagBits_length_eq_packed]
  have hpos : pos <= flags.length := by omega
  have hwordSize : data.wordSize = packedSparseWordSize shape.size := by
    change
      GenericSelect.sparseExceptionEffectiveFlagRankWordSize
          shape.bpCode false =
        packedSparseWordSize shape.size
    exact sparseFlagRankWordSize_eq_packed shape
  have hblocks : data.blocksPerSuper = 1 := by
    change
      GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper
          shape.bpCode false = 1
    rfl
  have hindex : pos / data.wordSize = index := by
    rw [hwordSize]
    rfl
  have hsuperIndex :
      pos / data.wordSize / data.blocksPerSuper = index := by
    rw [hindex, hblocks, Nat.div_one]
  rcases data.super_present true pos hpos with ⟨super, hsuperRaw⟩
  rcases data.block_present true pos hpos with ⟨delta, hblockRaw⟩
  rcases data.word_present pos hpos with ⟨flagReply, hflagRaw⟩
  have hsuper :
      (data.superTables.entries true)[index]? = some super := by
    simpa [hsuperIndex] using hsuperRaw
  have hblock :
      (data.blockTables.entries true)[index]? = some delta := by
    simpa [hindex] using hblockRaw
  have hflag : data.bitWords.store.words[index]? = some flagReply := by
    simpa [hindex] using hflagRaw
  change data.superTrueEntries[index]? = some super at hsuper
  change data.blockTrueEntries[index]? = some delta at hblock
  have hsuperRead := data.superTables.trueTable.read_exact index
  have hblockRead := data.blockTables.trueTable.read_exact index
  rw [hsuper] at hsuperRead
  rw [hblock] at hblockRead
  cases hsuperWord : data.superTables.trueTable.store.words[index]? with
  | none =>
      simp [hsuperWord] at hsuperRead
  | some superReply =>
      have hsuperDecode :
          SuccinctSpace.bitsToNatLE superReply = super := by
        simpa [hsuperWord] using hsuperRead
      cases hblockWord : data.blockTables.trueTable.store.words[index]? with
      | none =>
          simp [hblockWord] at hblockRead
      | some blockReply =>
          have hblockDecode :
              SuccinctSpace.bitsToNatLE blockReply = delta := by
            simpa [hblockWord] using hblockRead
          have hparts :=
            data.rank_parts_exact true pos super delta flagReply hpos
              hsuperRaw hblockRaw hflagRaw
          have hparts' :
              super + delta +
                  RMQ.RAM.boolRankPrefix true flagReply
                    (pos - index * data.wordSize) =
                RMQ.Succinct.rankPrefix true flags pos := by
            simpa [hindex, data, flags] using hparts
          have hoffset :
              packedReviewerSparsePreludeWordOffset shape.size =
                pos - index * data.wordSize := by
            simp [packedReviewerSparsePreludeWordOffset,
              packedReviewerSparsePreludeWordIndex, pos, index, hwordSize]
          have hdecode :
              packedReviewerSparseCountFromReplies shape.size
                  superReply blockReply flagReply =
                packedReviewerSparseCount shape := by
            rw [packedReviewerSparseCount_eq_effectiveRank shape]
            unfold packedReviewerSparseCountFromReplies
            rw [hsuperDecode, hblockDecode, hoffset]
            simpa [flags, pos] using
              congrArg (fun rank => rank * packedSelectLocalStride shape.size)
                hparts'
          refine ⟨superReply, blockReply, flagReply, ?_, ?_, ?_, hdecode⟩
          · change data.superTables.trueTable.store.words[index]? =
              some superReply
            exact hsuperWord
          · change data.blockTables.trueTable.store.words[index]? =
              some blockReply
            exact hblockWord
          · change data.bitWords.store.words[index]? = some flagReply
            exact hflag

/-! ## Fixed first-order request/reply protocol -/

/-- The closed, content-free set of three logical prelude requests. -/
inductive PackedReviewerSparsePreludeRequest where
  | rankSuper
  | rankBlock
  | flagWord
deriving DecidableEq, Repr

def PackedReviewerSparsePreludeRequest.source :
    PackedReviewerSparsePreludeRequest ->
      ConcreteBPNativeSuccinctRMQFlatPayloadSource
  | .rankSuper => .selectSparseRankSuperTrue
  | .rankBlock => .selectSparseRankBlockTrue
  | .flagWord => .selectSparseFlagBits

def PackedReviewerSparsePreludeRequest.index
    (_request : PackedReviewerSparsePreludeRequest) (n : Nat) : Nat :=
  packedReviewerSparsePreludeWordIndex n

/--
The fixed access-prefix length before the sparse-rank superblock table.

This is deliberately written as first-order arithmetic rather than by walking
the canonical source list.  Consequently the executable controller does not
carry, inspect, or depend on a source/program list while it bootstraps the
all-size sparse count.
-/
def packedReviewerSparseRankSuperPrefixLength (n longCount : Nat) : Nat :=
  packedSourceBitLength n longCount .finalRankSuperFalse +
    packedSourceBitLength n longCount .finalRankBlockFalse +
    packedSourceBitLength n longCount .selectSuperBaseOccurrence +
    packedSourceBitLength n longCount .selectSuperBaseWordIndex +
    packedSourceBitLength n longCount .selectSuperRankBefore +
    packedSourceBitLength n longCount .selectSuperFirstOffset +
    packedSourceBitLength n longCount .selectLocalBaseOccurrence +
    packedSourceBitLength n longCount .selectLocalBaseWordIndex +
    packedSourceBitLength n longCount .selectLocalRankBefore +
    packedSourceBitLength n longCount .selectLocalFirstOffset +
    packedSourceBitLength n longCount .selectLongFlagRankSuperTrue +
    packedSourceBitLength n longCount .selectLongFlagRankBlockTrue +
    packedSourceBitLength n longCount .selectLongFlagBits +
    packedSourceBitLength n longCount .selectLongRelative

/-- The whole-payload bit offset of each of the three closed requests. -/
def PackedReviewerSparsePreludeRequest.sourceOffset
    (request : PackedReviewerSparsePreludeRequest)
    (n longCount : Nat) : Nat :=
  match request with
  | .rankSuper =>
      2 * n + packedReviewerSparseRankSuperPrefixLength n longCount
  | .rankBlock =>
      2 * n + packedReviewerSparseRankSuperPrefixLength n longCount +
        packedSourceBitLength n longCount .selectSparseRankSuperTrue
  | .flagWord =>
      2 * n + packedReviewerSparseRankSuperPrefixLength n longCount +
        packedSourceBitLength n longCount .selectSparseRankSuperTrue +
        packedSourceBitLength n longCount .selectSparseRankBlockTrue

set_option maxHeartbeats 1000000 in
/--
Proof-side drift guard: the closed arithmetic offsets are exactly the offsets
of their corresponding sources in the consumed reviewer payload.
-/
theorem packedReviewerSparsePreludeRequest_sourceOffset_eq
    (n longCount : Nat) (request : PackedReviewerSparsePreludeRequest) :
    request.sourceOffset n longCount =
      packedReviewerSourceOffset n longCount request.source := by
  cases request <;>
    simp [PackedReviewerSparsePreludeRequest.sourceOffset,
      PackedReviewerSparsePreludeRequest.source,
      packedReviewerSparseRankSuperPrefixLength,
      packedReviewerSourceOffset, packedReviewerAccessOffset,
      concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources,
      Nat.add_assoc]

/-- The three requests, in the exact rank-decomposition order. -/
def packedReviewerSparsePreludeRequests (_n : Nat) :
    List PackedReviewerSparsePreludeRequest :=
  [ .rankSuper, .rankBlock, .flagWord ]

/--
Proof-free controller state.  It contains only the public size, the decoded
header value, and replies already supplied by the external driver.
-/
inductive PackedReviewerSparsePreludeState where
  | awaitSuper (n longCount : Nat)
  | awaitBlock (n longCount : Nat) (superReply : List Bool)
  | awaitFlag (n longCount : Nat)
      (superReply blockReply : List Bool)
  | done (n longCount sparseCount : Nat)
deriving DecidableEq, Repr

/-- Initial state immediately after the one-cell `longCount` header. -/
def packedReviewerSparsePreludeInit (n longCount : Nat) :
    PackedReviewerSparsePreludeState :=
  .awaitSuper n longCount

/-- The next logical read, determined entirely by the proof-free state. -/
def packedReviewerSparsePreludeNextRequest :
    PackedReviewerSparsePreludeState ->
      Option PackedReviewerSparsePreludeRequest
  | .awaitSuper _ _ => some .rankSuper
  | .awaitBlock _ _ _ => some .rankBlock
  | .awaitFlag _ _ _ _ => some .flagWord
  | .done _ _ _ => none

/-- Consume exactly one logical reply and advance to the next fixed stage. -/
def packedReviewerSparsePreludeConsumeReply
    (state : PackedReviewerSparsePreludeState) (reply : List Bool) :
    PackedReviewerSparsePreludeState :=
  match state with
  | .awaitSuper n longCount => .awaitBlock n longCount reply
  | .awaitBlock n longCount superReply =>
      .awaitFlag n longCount superReply reply
  | .awaitFlag n longCount superReply blockReply =>
      .done n longCount
        (packedReviewerSparseCountFromReplies n superReply blockReply reply)
  | .done n longCount sparseCount => .done n longCount sparseCount

/-- The terminal decoded count, absent before all three replies arrive. -/
def packedReviewerSparsePreludeResult :
    PackedReviewerSparsePreludeState -> Option Nat
  | .done _ _ sparseCount => some sparseCount
  | _ => none

/-- The transition surface issues the fixed three-request sequence. -/
theorem packedReviewerSparsePrelude_transition_sequence
    (n longCount : Nat) (superReply blockReply flagReply : List Bool) :
    packedReviewerSparsePreludeNextRequest
        (packedReviewerSparsePreludeInit n longCount) =
          some .rankSuper /\
      packedReviewerSparsePreludeNextRequest
        (packedReviewerSparsePreludeConsumeReply
          (packedReviewerSparsePreludeInit n longCount) superReply) =
          some .rankBlock /\
      packedReviewerSparsePreludeNextRequest
        (packedReviewerSparsePreludeConsumeReply
          (packedReviewerSparsePreludeConsumeReply
            (packedReviewerSparsePreludeInit n longCount) superReply)
          blockReply) =
          some .flagWord /\
      packedReviewerSparsePreludeResult
        (packedReviewerSparsePreludeConsumeReply
          (packedReviewerSparsePreludeConsumeReply
            (packedReviewerSparsePreludeConsumeReply
              (packedReviewerSparsePreludeInit n longCount) superReply)
            blockReply)
          flagReply) =
        some (packedReviewerSparseCountFromReplies n
          superReply blockReply flagReply) := by
  simp [packedReviewerSparsePreludeInit,
    packedReviewerSparsePreludeRequests,
    packedReviewerSparsePreludeNextRequest,
    packedReviewerSparsePreludeConsumeReply,
    packedReviewerSparsePreludeResult]

/-- Any three replies put the fixed controller in its terminal state. -/
theorem packedReviewerSparsePrelude_terminates_after_three
    (n longCount : Nat) (superReply blockReply flagReply : List Bool) :
    let finalState :=
      packedReviewerSparsePreludeConsumeReply
        (packedReviewerSparsePreludeConsumeReply
          (packedReviewerSparsePreludeConsumeReply
            (packedReviewerSparsePreludeInit n longCount) superReply)
          blockReply)
        flagReply
    packedReviewerSparsePreludeNextRequest finalState = none /\
      packedReviewerSparsePreludeResult finalState =
        some (packedReviewerSparseCountFromReplies n
          superReply blockReply flagReply) := by
  simp [packedReviewerSparsePreludeInit,
    packedReviewerSparsePreludeNextRequest,
    packedReviewerSparsePreludeConsumeReply,
    packedReviewerSparsePreludeResult]

/-! ## Physical plans and the memory-only driver -/

/-- A payload range past the header is unchanged in the padded allocation. -/
theorem packedReviewerSparsePreludePayloadSlice
    (shape : CartesianShape) (j width : Nat)
    (hfit :
      j + width <=
        packedReviewerPayloadLength shape.size (longCount shape)
          (packedReviewerSparseCount shape)) :
    ((packedReviewerPaddedBits shape).drop
        (packedReviewerCellWidth shape.size + j)).take width =
      ((packedReviewerPayloadBits shape).drop j).take width := by
  have hhdr := packedReviewerHeaderBits_length shape
  have hpay := packedReviewerPayloadBits_length_eq shape
  have hjle : j <= (packedReviewerPayloadBits shape).length := by omega
  have hwle : width <= ((packedReviewerPayloadBits shape).drop j).length := by
    rw [List.length_drop]
    omega
  unfold packedReviewerPaddedBits packedReviewerSerializedBits
  rw [List.append_assoc, ← List.drop_drop]
  rw [← hhdr]
  rw [List.drop_left]
  rw [List.drop_append_of_le_length hjle,
    List.take_append_of_le_length hwle]

/-- Every live source window sits inside the actual all-size payload. -/
theorem packedReviewerSparsePreludeSourceOffset_fits
    (shape : CartesianShape)
    (source : ConcreteBPNativeSuccinctRMQFlatPayloadSource)
    (hmem :
      source ∈ concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources) :
    packedReviewerSourceOffset shape.size (longCount shape) source +
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape source).length <=
      packedReviewerPayloadLength shape.size (longCount shape)
        (packedReviewerSparseCount shape) := by
  have hfits := packedReviewerAccessOffset_fits shape source hmem
  have hlen := packedReviewerAccessLength_eq shape
  unfold packedReviewerSourceOffset packedReviewerPayloadLength
  omega

/-- The first bit of a content-free prelude request in the allocation. -/
def packedReviewerSparsePreludeRequestBitAddress (n longCount : Nat)
    (request : PackedReviewerSparsePreludeRequest) : Nat :=
  packedReviewerCellWidth n +
    request.sourceOffset n longCount +
      request.index n * packedSourceStride n request.source

/-- The closed executable address still names the exact canonical payload bit. -/
theorem packedReviewerSparsePreludeRequestBitAddress_eq_sourceOffset
    (n longCount : Nat) (request : PackedReviewerSparsePreludeRequest) :
    packedReviewerSparsePreludeRequestBitAddress n longCount request =
      packedReviewerCellWidth n +
        packedReviewerSourceOffset n longCount request.source +
          request.index n * packedSourceStride n request.source := by
  unfold packedReviewerSparsePreludeRequestBitAddress
  rw [packedReviewerSparsePreludeRequest_sourceOffset_eq]

/-- Lower one content-free request to its one-or-two-cell reviewer plan. -/
def packedReviewerSparsePreludeRequestPlan (n longCount : Nat)
    (request : PackedReviewerSparsePreludeRequest) : List Nat :=
  packedReviewerProbePlan n
    (packedReviewerSparsePreludeRequestBitAddress n longCount request)
    (packedSourceReadWidth n longCount request.source (request.index n))

/-- Issue one request only against the memory supplied by the driver. -/
def packedReviewerSparsePreludeRequestRead (n longCount : Nat)
    (memory : List (List Bool))
    (request : PackedReviewerSparsePreludeRequest) : Option (List Bool) :=
  if request.index n <
      packedSourceWordCount n longCount request.source then
    (packedFetch memory
      (packedReviewerSparsePreludeRequestPlan n longCount request)).map
        (packedReviewerDecodeSpan n
          (packedReviewerSparsePreludeRequestBitAddress n longCount request)
          (packedSourceReadWidth n longCount request.source (request.index n)))
  else
    none

/-- Each logical prelude request lowers to at most two physical cells. -/
theorem packedReviewerSparsePreludeRequestPlan_length_le_two
    (n longCount : Nat) (request : PackedReviewerSparsePreludeRequest) :
    (packedReviewerSparsePreludeRequestPlan n longCount request).length <= 2 :=
  packedReviewerProbeCount_le_two _ _ _

/-- A successful fetch witnesses allocation of every address it issued. -/
theorem packedReviewerSparsePrelude_fetch_some_address_lt
    {memory : List (List Bool)} {plan : List Nat} {cells : List (List Bool)}
    (hfetch : packedFetch memory plan = some cells)
    {address : Nat} (haddress : address ∈ plan) :
    address < memory.length := by
  induction plan generalizing cells address with
  | nil => simp at haddress
  | cons head tail ih =>
      cases hcell : packedProbeCell memory head with
      | none =>
          simp [packedFetch, hcell] at hfetch
      | some cell =>
          cases htail : packedFetch memory tail with
          | none =>
              simp [packedFetch, hcell, htail] at hfetch
          | some tailCells =>
              rcases List.mem_cons.mp haddress with rfl | htailMem
              · unfold packedProbeCell at hcell
                exact (List.getElem?_eq_some_iff.mp hcell).1
              · exact ih htail htailMem

/-- A successful request witnesses allocation of every cell in its plan. -/
theorem packedReviewerSparsePreludeRequestRead_address_lt
    {n longCount : Nat} {memory : List (List Bool)}
    {request : PackedReviewerSparsePreludeRequest} {word : List Bool}
    (hread :
      packedReviewerSparsePreludeRequestRead n longCount memory request =
        some word)
    {address : Nat}
    (haddress :
      address ∈ packedReviewerSparsePreludeRequestPlan n longCount request) :
    address < memory.length := by
  unfold packedReviewerSparsePreludeRequestRead at hread
  by_cases hindex :
      request.index n < packedSourceWordCount n longCount request.source
  · rw [if_pos hindex] at hread
    cases hfetch :
        packedFetch memory
          (packedReviewerSparsePreludeRequestPlan n longCount request) with
    | none => simp [hfetch] at hread
    | some cells =>
        exact packedReviewerSparsePrelude_fetch_some_address_lt
          hfetch haddress
  · rw [if_neg hindex] at hread
    simp at hread

set_option maxHeartbeats 1000000 in
/--
Every successful canonical word read lowers all-size to the same word fetched
from reviewer memory.  No unit-stride premise appears in this chain.
-/
theorem packedReviewerSparsePreludeRequestRead_of_some
    (shape : CartesianShape)
    (request : PackedReviewerSparsePreludeRequest)
    {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        request.source)[request.index shape.size]? = some word) :
    packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
        (packedReviewerMemory shape) request = some word := by
  have hmem :
      request.source ∈
        concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources := by
    cases request <;> decide
  have hne :
      request.source !=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative := by
    cases request <;> decide
  have hcounted : PackedSourceCounted shape.size request.source := by
    cases request <;>
      simp [PackedReviewerSparsePreludeRequest.source, PackedSourceCounted]
  have hslice := packedSourceWords_of_some shape request.source hget
  have hlt :
      request.index shape.size <
        packedSourceWordCount shape.size (longCount shape) request.source := by
    by_cases h : request.index shape.size <
        packedSourceWordCount shape.size (longCount shape) request.source
    · exact h
    · rw [packedWordSlice_of_le (by omega)] at hslice
      exact absurd hslice (by simp)
  have hword :
      word =
        (((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
            request.source).drop
          (request.index shape.size *
            packedSourceStride shape.size request.source)).take
          (packedSourceStride shape.size request.source)) := by
    rw [packedWordSlice_of_lt hlt] at hslice
    exact (Option.some.inj hslice).symm
  have hsourceLength :=
    packedSourceBitLength_eq shape request.source hne
  have hwindow :
      packedSourceReadWidth shape.size (longCount shape)
          request.source (request.index shape.size) =
        min (packedSourceStride shape.size request.source)
          ((concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
              request.source).length -
            request.index shape.size *
              packedSourceStride shape.size request.source) := by
    unfold packedSourceReadWidth
    rw [← hsourceLength]
  have hsrc :=
    packedReviewerPayload_accessSlice shape request.source hmem
  have hcontain :=
    packedReviewerSparsePreludeSourceOffset_fits shape request.source hmem
  have hoffset :
      request.sourceOffset shape.size (longCount shape) =
        packedReviewerSourceOffset shape.size (longCount shape)
          request.source :=
    packedReviewerSparsePreludeRequest_sourceOffset_eq
      shape.size (longCount shape) request
  have hwidth :=
    packedSourceStride_le_reviewerCellWidth shape.size request.source hcounted
  by_cases hzero :
      packedSourceReadWidth shape.size (longCount shape)
        request.source (request.index shape.size) = 0
  · have hempty : word = [] := by
      rw [hword]
      rw [hzero] at hwindow
      by_cases hsourceStrideZero :
          packedSourceStride shape.size request.source = 0
      · rw [hsourceStrideZero]
        simp
      · have hpast :
            (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
                request.source).length <=
              request.index shape.size *
                packedSourceStride shape.size request.source := by
          omega
        rw [List.drop_eq_nil_of_le hpast]
        simp
    have hplan :
        packedReviewerProbePlan shape.size
            (packedReviewerSparsePreludeRequestBitAddress shape.size
              (longCount shape) request) 0 = [] := by
      simp [packedReviewerProbePlan]
    unfold packedReviewerSparsePreludeRequestRead
      packedReviewerSparsePreludeRequestPlan
    rw [if_pos hlt, hzero, hplan, hempty]
    simp [packedFetch, packedReviewerDecodeSpan]
  · have hpos :
        0 < packedSourceReadWidth shape.size (longCount shape)
          request.source (request.index shape.size) := by omega
    have hminle :
        packedSourceReadWidth shape.size (longCount shape)
            request.source (request.index shape.size) <=
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
              request.source).length -
            request.index shape.size *
              packedSourceStride shape.size request.source := by
      rw [hwindow]
      omega
    have hinside :
        request.index shape.size * packedSourceStride shape.size request.source <
          (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
            request.source).length := by
      omega
    have hfit2 :
        request.sourceOffset shape.size (longCount shape) +
            request.index shape.size *
              packedSourceStride shape.size request.source +
            packedSourceReadWidth shape.size (longCount shape)
              request.source (request.index shape.size) <=
          packedReviewerPayloadLength shape.size (longCount shape)
            (packedReviewerSparseCount shape) := by
      rw [hoffset]
      omega
    have hserial :=
      packedReviewerSerialized_le_allocated shape.size (longCount shape)
        (packedReviewerSparseCount shape)
    have haddr :
        packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape) request =
          packedReviewerCellWidth shape.size +
            (request.sourceOffset shape.size (longCount shape) +
              request.index shape.size *
                packedSourceStride shape.size request.source) := by
      unfold packedReviewerSparsePreludeRequestBitAddress
      omega
    have hfitalloc :
        packedReviewerSparsePreludeRequestBitAddress shape.size
              (longCount shape) request +
            packedSourceReadWidth shape.size (longCount shape)
              request.source (request.index shape.size) <=
          packedReviewerAllocatedBits shape.size (longCount shape)
            (packedReviewerSparseCount shape) := by
      rw [haddr]
      omega
    have hwle :
        packedSourceReadWidth shape.size (longCount shape)
            request.source (request.index shape.size) <=
          packedReviewerCellWidth shape.size :=
      Nat.le_trans
        (packedSourceReadWidth_le_stride shape.size (longCount shape)
          request.source (request.index shape.size))
        hwidth
    have hdecode := packedReviewerProbePlan_decode shape hwle hfitalloc
    have hpayslice :=
      packedReviewerSparsePreludePayloadSlice shape
        (request.sourceOffset shape.size (longCount shape) +
          request.index shape.size * packedSourceStride shape.size request.source)
        (packedSourceReadWidth shape.size (longCount shape)
          request.source (request.index shape.size)) hfit2
    have hchain :
        ((packedReviewerPayloadBits shape).drop
              (request.sourceOffset shape.size (longCount shape) +
                request.index shape.size *
                  packedSourceStride shape.size request.source)).take
            (packedSourceReadWidth shape.size (longCount shape)
              request.source (request.index shape.size)) =
          word := by
      rw [hoffset]
      obtain ⟨L, hL⟩ :
          exists L,
            (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
              request.source).length = L :=
        ⟨_, rfl⟩
      rw [hL] at hsrc hwindow
      rw [hword, hwindow, ← hsrc, List.drop_take, List.drop_drop,
        List.take_take, Nat.add_comm]
    unfold packedReviewerSparsePreludeRequestRead
      packedReviewerSparsePreludeRequestPlan
    rw [if_pos hlt, hdecode, haddr, hpayslice, hchain]

/-- The physical trace issued by all three fixed logical reads. -/
def packedReviewerSparsePreludeProbePlan (n longCount : Nat) : List Nat :=
  (packedReviewerSparsePreludeRequests n).flatMap
    (packedReviewerSparsePreludeRequestPlan n longCount)

/-- Exact ordered, multiplicity-sensitive decomposition of the prelude trace. -/
theorem packedReviewerSparsePreludeProbePlan_ordered
    (n longCount : Nat) :
    packedReviewerSparsePreludeProbePlan n longCount =
      packedReviewerSparsePreludeRequestPlan n longCount .rankSuper ++
        packedReviewerSparsePreludeRequestPlan n longCount .rankBlock ++
        packedReviewerSparsePreludeRequestPlan n longCount .flagWord := by
  simp [packedReviewerSparsePreludeProbePlan,
    packedReviewerSparsePreludeRequests, List.append_assoc]

/--
An explicit ignored sparse-count parameter records the bootstrap fact: every
prelude address is fixed before that count is known.
-/
def packedReviewerSparsePreludeProbePlanAt
    (n longCount _sparseCount : Nat) : List Nat :=
  packedReviewerSparsePreludeProbePlan n longCount

theorem packedReviewerSparsePreludeProbePlan_sparseCount_independent
    (n longCount sparseCountLeft sparseCountRight : Nat) :
    packedReviewerSparsePreludeProbePlanAt n longCount sparseCountLeft =
      packedReviewerSparsePreludeProbePlanAt n longCount sparseCountRight :=
  rfl

/-- Three logical reads cost at most six physical reviewer-memory probes. -/
theorem packedReviewerSparsePreludeProbePlan_length_le_six
    (n longCount : Nat) :
    (packedReviewerSparsePreludeProbePlan n longCount).length <= 6 := by
  have hsuper :=
    packedReviewerSparsePreludeRequestPlan_length_le_two n longCount
      .rankSuper
  have hblock :=
    packedReviewerSparsePreludeRequestPlan_length_le_two n longCount
      .rankBlock
  have hflag :=
    packedReviewerSparsePreludeRequestPlan_length_le_two n longCount
      .flagWord
  unfold packedReviewerSparsePreludeProbePlan
  simp only [packedReviewerSparsePreludeRequests, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_append]
  omega

/-- Header cell zero followed by the prelude's actual physical plans. -/
def packedReviewerHeaderAndSparsePreludeProbePlan
    (n longCount : Nat) : List Nat :=
  0 :: packedReviewerSparsePreludeProbePlan n longCount

/-- The header plus all three prelude reads costs at most seven probes. -/
theorem packedReviewerHeaderAndSparsePreludeProbePlan_length_le_seven
    (n longCount : Nat) :
    (packedReviewerHeaderAndSparsePreludeProbePlan n longCount).length <= 7 := by
  have h := packedReviewerSparsePreludeProbePlan_length_le_six n longCount
  simp [packedReviewerHeaderAndSparsePreludeProbePlan]
  omega

/--
The external driver supplies replies only by issuing the three fixed reads
against the memory it is given.
-/
def packedReviewerSparsePreludeRunAgainstMemory
    (n longCount : Nat) (memory : List (List Bool)) : Option Nat := do
  let superReply <-
    packedReviewerSparsePreludeRequestRead n longCount memory
      .rankSuper
  let blockReply <-
    packedReviewerSparsePreludeRequestRead n longCount memory
      .rankBlock
  let flagReply <-
    packedReviewerSparsePreludeRequestRead n longCount memory
      .flagWord
  packedReviewerSparsePreludeResult
    (packedReviewerSparsePreludeConsumeReply
      (packedReviewerSparsePreludeConsumeReply
        (packedReviewerSparsePreludeConsumeReply
          (packedReviewerSparsePreludeInit n longCount) superReply)
        blockReply)
      flagReply)

/--
All three replies in the canonical run are fetched from reviewer memory, and
the same replies decode to the actual sparse-relative row count.
-/
theorem packedReviewerSparsePrelude_physicalReplies_exact
    (shape : CartesianShape) :
    exists superReply blockReply flagReply,
      packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
          (packedReviewerMemory shape)
          .rankSuper =
        some superReply /\
      packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
          (packedReviewerMemory shape)
          .rankBlock =
        some blockReply /\
      packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
          (packedReviewerMemory shape)
          .flagWord =
        some flagReply /\
      packedReviewerSparseCountFromReplies shape.size
          superReply blockReply flagReply =
        packedReviewerSparseCount shape := by
  rcases packedReviewerSparsePrelude_sourceReplies_exact shape with
    ⟨superReply, blockReply, flagReply, hsuperGet, hblockGet, hflagGet,
      hdecode⟩
  have hsuper :=
    packedReviewerSparsePreludeRequestRead_of_some shape
      .rankSuper hsuperGet
  have hblock :=
    packedReviewerSparsePreludeRequestRead_of_some shape
      .rankBlock hblockGet
  have hflag :=
    packedReviewerSparsePreludeRequestRead_of_some shape
      .flagWord hflagGet
  exact ⟨superReply, blockReply, flagReply,
    hsuper, hblock, hflag, hdecode⟩

/-- Every attempted prelude address is a real cell of the same reviewer memory. -/
theorem packedReviewerSparsePreludeProbePlan_address_lt_cellCount
    (shape : CartesianShape) {address : Nat}
    (haddress :
      address ∈ packedReviewerSparsePreludeProbePlan
        shape.size (longCount shape)) :
    address < packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) := by
  rcases packedReviewerSparsePrelude_physicalReplies_exact shape with
    ⟨superReply, blockReply, flagReply, hsuper, hblock, hflag, _hdecode⟩
  have hcases :
      address ∈
          packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
            .rankSuper \/
        address ∈
          packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
            .rankBlock \/
        address ∈
          packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
            .flagWord := by
    simpa [packedReviewerSparsePreludeProbePlan,
      packedReviewerSparsePreludeRequests] using haddress
  rw [← packedReviewerMemory_length shape]
  rcases hcases with hsuperAddress | hblockAddress | hflagAddress
  · exact packedReviewerSparsePreludeRequestRead_address_lt
      hsuper hsuperAddress
  · exact packedReviewerSparsePreludeRequestRead_address_lt
      hblock hblockAddress
  · exact packedReviewerSparsePreludeRequestRead_address_lt
      hflag hflagAddress

/-- Header plus prelude attempts are all allocated in the same memory. -/
theorem packedReviewerHeaderAndSparsePrelude_address_lt_cellCount
    (shape : CartesianShape) {address : Nat}
    (haddress :
      address ∈ packedReviewerHeaderAndSparsePreludeProbePlan
        shape.size (longCount shape)) :
    address < packedReviewerCellCount shape.size (longCount shape)
      (packedReviewerSparseCount shape) := by
  simp only [packedReviewerHeaderAndSparsePreludeProbePlan,
    List.mem_cons] at haddress
  rcases haddress with rfl | hprelude
  · unfold packedReviewerCellCount
    omega
  · exact
      packedReviewerSparsePreludeProbePlan_address_lt_cellCount shape hprelude

/-- The actual reviewer allocation has a machine-word-representable cell count. -/
theorem packedReviewerSparsePreludeCellCount_lt_two_pow_reviewerWidth
    (shape : CartesianShape) :
    packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape) <
      2 ^ packedReviewerCellWidth shape.size := by
  let payloadLength :=
    packedReviewerPayloadLength shape.size (longCount shape)
      (packedReviewerSparseCount shape)
  let width := packedReviewerCellWidth shape.size
  have hwidth : 0 < width := by
    simpa [width] using packedReviewerCellWidth_pos shape.size
  have hceil :
      GenericSelect.selectCeilDiv payloadLength width <= payloadLength := by
    by_cases hzero : payloadLength = 0
    · unfold GenericSelect.selectCeilDiv
      rw [hzero]
      simp only [Nat.zero_add]
      have hpred : width - 1 < width := Nat.pred_lt (Nat.ne_of_gt hwidth)
      rw [Nat.div_eq_of_lt hpred]
      omega
    · exact GenericSelect.selectCeilDiv_le_self_of_pos
        (Nat.pos_of_ne_zero hzero) hwidth
  have hpayload := packedReviewerPayloadLength_le_bound shape
  have hpow := packedReviewerCellBound_lt_two_pow_width shape.size
  unfold packedReviewerCellCount
  unfold packedReviewerCellBound at hpow
  simp only [payloadLength, width] at hceil
  omega

/-- Every header/prelude address fits the controller's address word. -/
theorem packedReviewerHeaderAndSparsePrelude_address_lt_two_pow
    (shape : CartesianShape) {address : Nat}
    (haddress :
      address ∈ packedReviewerHeaderAndSparsePreludeProbePlan
        shape.size (longCount shape)) :
    address < 2 ^ packedReviewerCellWidth shape.size :=
  Nat.lt_trans
    (packedReviewerHeaderAndSparsePrelude_address_lt_cellCount shape haddress)
    (packedReviewerSparsePreludeCellCount_lt_two_pow_reviewerWidth shape)

/-- The actual memory-only prelude run recovers the exact count at every size. -/
theorem packedReviewerSparsePreludeRunAgainstMemory_exact
    (shape : CartesianShape) :
    packedReviewerSparsePreludeRunAgainstMemory shape.size (longCount shape)
        (packedReviewerMemory shape) =
      some (packedReviewerSparseCount shape) := by
  rcases packedReviewerSparsePrelude_physicalReplies_exact shape with
    ⟨superReply, blockReply, flagReply, hsuper, hblock, hflag, hdecode⟩
  unfold packedReviewerSparsePreludeRunAgainstMemory
  simp [hsuper, hblock, hflag, hdecode,
    packedReviewerSparsePreludeInit,
    packedReviewerSparsePreludeConsumeReply,
    packedReviewerSparsePreludeResult]

/-- Trace and result are kept on one physical prelude-run object. -/
structure PackedReviewerSparsePreludeRun where
  trace : List Nat
  result : Option Nat
deriving DecidableEq, Repr

def packedReviewerSparsePreludeRun (n longCount : Nat)
    (memory : List (List Bool)) : PackedReviewerSparsePreludeRun where
  trace := packedReviewerSparsePreludeProbePlan n longCount
  result := packedReviewerSparsePreludeRunAgainstMemory n longCount memory

/-- The run object retains the exact three-site physical request order. -/
theorem packedReviewerSparsePreludeRun_trace_ordered
    (n longCount : Nat) (memory : List (List Bool)) :
    (packedReviewerSparsePreludeRun n longCount memory).trace =
      packedReviewerSparsePreludeRequestPlan n longCount .rankSuper ++
        packedReviewerSparsePreludeRequestPlan n longCount .rankBlock ++
        packedReviewerSparsePreludeRequestPlan n longCount .flagWord :=
  packedReviewerSparsePreludeProbePlan_ordered n longCount

/-- The run has no supplied store or callback hidden behind its signature. -/
theorem packedReviewerSparsePreludeRun_memory_only
    (n longCount : Nat) (memory : List (List Bool)) :
    (packedReviewerSparsePreludeRun n longCount memory).result =
      packedReviewerSparsePreludeRunAgainstMemory n longCount memory :=
  rfl

/-- Same-object capstone for this leaf: physical trace cap and exact result. -/
theorem packedReviewerSparsePreludeRun_exact_and_capped
    (shape : CartesianShape) :
    (packedReviewerSparsePreludeRun shape.size (longCount shape)
          (packedReviewerMemory shape)).result =
        some (packedReviewerSparseCount shape) /\
      (packedReviewerSparsePreludeRun shape.size (longCount shape)
          (packedReviewerMemory shape)).trace.length <= 6 := by
  exact ⟨packedReviewerSparsePreludeRunAgainstMemory_exact shape,
    packedReviewerSparsePreludeProbePlan_length_le_six
      shape.size (longCount shape)⟩

end PackedCellProbe
end SuccinctFinal
end RMQ
