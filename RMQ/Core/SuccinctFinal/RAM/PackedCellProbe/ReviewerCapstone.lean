import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerStateProof

/-!
# The Stage-F capstone and the residual liveness obligations

This module closes the Stage-F residual contract frozen in
`docs/internal/EG_CP_FINAL_FALSIFICATION_MATRIX.md` section 10.

* `PackedReviewerStageFCapstone` combines, on identical let-bound objects, the
  payload identity, the exact `header ++ buildPayload ++ final padding`
  serialization, the one cell width, the `2n + rho` allocation with its
  little-o residual, the literal memory-only run, attempted-probe
  allocation/success/backing, the ordered grouping, the derived `427` cap,
  the guarded half-open leftmost reference result, the exact-type controller
  input boundary (an equation that elaborates only at
  `Nat -> Nat -> Nat -> PackedReviewerControllerState`, plus the
  memory-only-at-the-driver run factorization), and the former length/arity
  and store-agreement facts under accurate names.
  `packedReviewerStageFCapstone_holds` inhabits it for every input and
  every endpoint pair.

* The `FG-11` header-liveness theorem is universal, not a sampled instance:
  for every shape and every valid query, replacing only the counted
  long-count header cell moves the second attempted physical address.  The
  inequality is at the address projection of one trace position, which is
  exactly the substitution the frozen row rejects an aggregate-record
  inequality for.

Nothing here weakens, restates, or replaces the accepted `R2` theorems; every
conjunct is either one of them at the same objects or a projection of the
public run certificate.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ## The combined Stage-F capstone -/

/--
The Stage-F capstone.  Every field is stated over the identical objects
`shape`, `packedReviewerMemory shape`, and the literal
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left
right`; no field is allowed to quantify over a sibling payload, store, or
run.  The conjunct list is frozen by matrix section 10.5.
-/
structure PackedReviewerStageFCapstone
    (xs : List Int) (left right : Nat) : Prop where
  payload_is_buildPayload :
    packedReviewerPayloadBits (SuccinctClassic.cartesianShape xs) =
      SuccinctClassic.buildPayload xs
  serialized_header_payload :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerSerializedBits shape =
      packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape
  padded_final_padding :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerPaddedBits shape =
        packedReviewerSerializedBits shape ++
          List.replicate
            (packedReviewerAllocatedBits shape.size (longCount shape)
                (packedReviewerSparseCount shape) -
              (packedReviewerSerializedBits shape).length) false /\
      (packedReviewerPaddedBits shape).length =
        packedReviewerAllocatedBits shape.size (longCount shape)
          (packedReviewerSparseCount shape)
  one_cell_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall cell, cell ∈ packedReviewerMemory shape ->
      cell.length = packedReviewerCellWidth shape.size
  allocation_two_n_plus_rho :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length * packedReviewerCellWidth shape.size <=
      2 * shape.size + packedReviewerRho shape.size
  rho_little_o : SuccinctSpace.LittleOLinear packedReviewerRho
  probes_backed_by_memory :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.reply = (packedReviewerMemory shape)[event.request.address]?
  probes_allocated_and_successful :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address <
            packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape) /\
          exists cell, event.reply = some cell
  ordered_grouping :
    PackedReviewerRunGrouping (SuccinctClassic.cartesianShape xs) left right
  derived_cap_427 :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace.length <= 427
  guarded_reference_result :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).terminal =
          some (SuccinctClassic.queryTraceResult xs left right).value /\
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).failed = false /\
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).state =
          .done (SuccinctClassic.queryTraceResult xs left right).value
  controller_input_boundary :
    let shape := SuccinctClassic.cartesianShape xs
    @packedReviewerController =
        (fun (n left right : Nat) => packedReviewerController n left right) /\
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right =
        packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
          (packedReviewerControllerMeasure
            (packedReviewerController shape.size left right))
          (packedReviewerController shape.size left right)
  closed_length_and_memory_arity :
    let shape := SuccinctClassic.cartesianShape xs
    (forall n longCount sparseCount : Nat,
        packedReviewerClosedPayloadLength n longCount sparseCount =
          packedReviewerPayloadLength n longCount sparseCount) /\
      (packedReviewerMemory shape).length =
        packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape)
  store_agreement_determinism :
    let shape := SuccinctClassic.cartesianShape xs
    forall memoryB : List (List Bool),
      (forall event,
        event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
          memoryB[event.request.address]? = event.reply) ->
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right =
        packedReviewerRunAgainstMemory memoryB shape.size left right

/--
Every Stage-F conjunct holds for every input list and every endpoint pair,
by projection from the public run certificate and the accepted payload,
memory, space, and agreement theorems -- there is no new execution story
here, only the one already proved for the identical objects.
-/
theorem packedReviewerStageFCapstone_holds
    (xs : List Int) (left right : Nat) :
    PackedReviewerStageFCapstone xs left right := by
  have certificate := packedReviewerRunAgainstMemory_public_certificate
    xs left right
  refine
    { payload_is_buildPayload := packedReviewerPayloadBits_eq_buildPayload xs
      serialized_header_payload := rfl
      padded_final_padding :=
        ⟨rfl, packedReviewerPaddedBits_length (SuccinctClassic.cartesianShape xs)⟩
      one_cell_width := fun cell hcell =>
        packedReviewerMemory_cell_length (SuccinctClassic.cartesianShape xs)
          hcell
      allocation_two_n_plus_rho :=
        packedReviewerMemory_length_mul_width_le
          (SuccinctClassic.cartesianShape xs)
      rho_little_o := packedReviewerRho_littleO
      probes_backed_by_memory := certificate.memory_only
      probes_allocated_and_successful := fun event hevent =>
        ⟨certificate.allocated event hevent,
          certificate.reply_success event hevent⟩
      ordered_grouping := certificate.grouping
      derived_cap_427 := certificate.trace_cap
      guarded_reference_result :=
        ⟨certificate.terminal_eq, certificate.failed_false,
          certificate.state_eq⟩
      controller_input_boundary := ⟨rfl, rfl⟩
      closed_length_and_memory_arity :=
        ⟨fun n longCount sparseCount =>
          packedReviewerClosedPayloadLength_eq n longCount sparseCount,
          packedReviewerMemory_length (SuccinctClassic.cartesianShape xs)⟩
      store_agreement_determinism := fun memoryB hagree => ?_ }
  exact packedReviewerRunAgainstMemory_eq_of_agree
    (packedReviewerMemory (SuccinctClassic.cartesianShape xs)) memoryB
    (SuccinctClassic.cartesianShape xs).size left right
    (by
      simpa [PackedReviewerMemoriesAgreeOnRun,
        packedReviewerRunAgainstMemory] using hagree)

/-! ## `FG-11` header liveness: the universal address-projection theorem

The first `.rankSuper` prelude probe reads the terminal sparse-rank super
sample.  Its bit address is the cell width plus the closed first-order access
prefix, and the prefix's only `longCount`-dependent term is the long relative
table, whose bit length is `longCount * superStride (2 * n) * packedSuperWidth
n`.  Moving the decoded count by one full cell width therefore moves the
issued cell index by at least one whole cell -- for every size, not for a
sampled one.
-/

/-- The prelude's terminal-sample index is inside the sparse-rank directory at
every size: the directory deliberately carries the end sample, so this is the
successor inequality and nothing deeper. -/
theorem packedReviewerRankSuperIndex_lt (n longCount : Nat) :
    packedReviewerSparsePreludeWordIndex n <
      packedSourceWordCount n longCount .selectSparseRankSuperTrue := by
  show packedReviewerSparsePreludeWordIndex n < packedSparseRankSlots n
  unfold packedReviewerSparsePreludeWordIndex packedSparseRankSlots
  omega

/-- The terminal sample is read at the full sparse-rank word size: the
directory has exactly `index + 1` words, so the final word is not short. -/
theorem packedReviewerRankSuperReadWidth (n longCount : Nat) :
    packedSourceReadWidth n longCount .selectSparseRankSuperTrue
        (packedReviewerSparsePreludeWordIndex n) =
      packedSparseWordSize n := by
  show min (packedSourceStride n .selectSparseRankSuperTrue)
      (packedSourceBitLength n longCount .selectSparseRankSuperTrue -
        packedReviewerSparsePreludeWordIndex n *
          packedSourceStride n .selectSparseRankSuperTrue) =
    packedSparseWordSize n
  show min (packedSparseWordSize n)
      (packedSparseRankSlots n * packedSparseWordSize n -
        packedReviewerSparsePreludeWordIndex n * packedSparseWordSize n) =
    packedSparseWordSize n
  unfold packedSparseRankSlots packedReviewerSparsePreludeWordIndex
  generalize packedSparseSlots n / packedSparseWordSize n = index
  rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
  exact Nat.min_self _

theorem packedReviewerRankSuperReadWidth_pos (n longCount : Nat) :
    0 < packedSourceReadWidth n longCount .selectSparseRankSuperTrue
        (packedReviewerSparsePreludeWordIndex n) := by
  rw [packedReviewerRankSuperReadWidth]
  exact SuccinctRank.machineWordBits_pos _

/-- A positive-width probe plan opens at the containing cell of its bit
address. -/
theorem packedReviewerProbePlan_head
    {n bit width : Nat} (hpos : 0 < width) :
    (packedReviewerProbePlan n bit width)[0]? =
      some (bit / packedReviewerCellWidth n) := by
  have hne : Not (width = 0) := by omega
  unfold packedReviewerProbePlan
  by_cases hin :
      bit % packedReviewerCellWidth n + width <= packedReviewerCellWidth n <;>
    simp [hne, hin]

/--
**The access prefix is linear in the decoded count.**  Thirteen of the
fourteen closed prefix terms are input-size-only; the long relative table
contributes exactly `longCount * (superStride (2 * n) * packedSuperWidth n)`
bits.
-/
theorem packedReviewerSparseRankSuperPrefixLength_add
    (n longCount delta : Nat) :
    packedReviewerSparseRankSuperPrefixLength n (longCount + delta) =
      packedReviewerSparseRankSuperPrefixLength n longCount +
        delta * (GenericSelect.superStride (2 * n) * packedSuperWidth n) := by
  unfold packedReviewerSparseRankSuperPrefixLength
  simp only [packedSourceBitLength, packedSourceWordCount, packedSourceStride,
    packedLongRelativeSlots]
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
  omega

/-- The `.rankSuper` bit address moves linearly with the decoded count. -/
theorem packedReviewerRankSuperBitAddress_add
    (n longCount delta : Nat) :
    packedReviewerSparsePreludeRequestBitAddress n (longCount + delta)
        .rankSuper =
      packedReviewerSparsePreludeRequestBitAddress n longCount .rankSuper +
        delta * (GenericSelect.superStride (2 * n) * packedSuperWidth n) := by
  unfold packedReviewerSparsePreludeRequestBitAddress
  show packedReviewerCellWidth n +
      (2 * n + packedReviewerSparseRankSuperPrefixLength n (longCount + delta)) +
        packedReviewerSparsePreludeWordIndex n *
          packedSourceStride n .selectSparseRankSuperTrue = _
  rw [packedReviewerSparseRankSuperPrefixLength_add n longCount delta]
  show _ = packedReviewerCellWidth n +
      (2 * n + packedReviewerSparseRankSuperPrefixLength n longCount) +
        packedReviewerSparsePreludeWordIndex n *
          packedSourceStride n .selectSparseRankSuperTrue +
      delta * (GenericSelect.superStride (2 * n) * packedSuperWidth n)
  omega

/-- The linear coefficient is never zero: a long relative row is a real machine
word. -/
theorem packedReviewerLongRelativeRowBits_pos (n : Nat) :
    0 < GenericSelect.superStride (2 * n) * packedSuperWidth n :=
  Nat.mul_pos (GenericSelect.superStride_pos (2 * n))
    (SuccinctRank.machineWordBits_pos _)

/--
**Headroom for the header mutation.**  The mutated count `longCount + w(n)`
still fits the one-cell header, because the count is at most `n`, the width is
logarithmic in the advertised bound, and the bound dominates both.
-/
theorem packedReviewerLongCount_add_width_lt_two_pow (shape : CartesianShape) :
    longCount shape + packedReviewerCellWidth shape.size <
      2 ^ packedReviewerCellWidth shape.size := by
  have hcount := longCount_le_superSlots shape
  have hslots := packedSuperSlots_le shape.size
  have hbound := packedReviewerCellBound_lt_two_pow_width shape.size
  have hwidthEq :
      packedReviewerCellWidth shape.size =
        Nat.log2 (packedReviewerCellBound shape.size + 2) + 1 := rfl
  have hboundEq :
      packedReviewerCellBound shape.size =
        2 * shape.size +
          concreteBPNativeSuccinctRMQCanonicalReviewerOverhead shape.size :=
    rfl
  have hexp :
      shape.size + concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
          shape.size <
        2 ^ (shape.size +
          concreteBPNativeSuccinctRMQCanonicalReviewerOverhead shape.size) :=
    Nat.lt_two_pow_self
  have hlog :
      Nat.log2 (packedReviewerCellBound shape.size + 2) <
        shape.size +
          concreteBPNativeSuccinctRMQCanonicalReviewerOverhead shape.size +
          2 := by
    rw [Nat.log2_lt (by omega)]
    have hpow :
        2 ^ (shape.size +
            concreteBPNativeSuccinctRMQCanonicalReviewerOverhead shape.size +
            2) =
          2 ^ (shape.size +
              concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
                shape.size) *
            (2 * 2) := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    omega
  omega

/-- Two driver steps of any run whose first two transitions are live: the
first two attempted addresses are exactly the two computed requests'. -/
theorem packedReviewerDriveAux_first_two_addresses
    (memory : List (List Bool)) (fuel : Nat)
    (state : PackedReviewerControllerState)
    {requestOne requestTwo : PackedReviewerPhysicalRequest}
    (hfuel : 2 <= fuel)
    (hresultOne : packedReviewerControllerResult state = none)
    (hrequestOne : packedReviewerNextRequest state = some requestOne)
    (hresultTwo :
      packedReviewerControllerResult
        (packedReviewerConsumeReply state (memory[requestOne.address]?)) = none)
    (hrequestTwo :
      packedReviewerNextRequest
        (packedReviewerConsumeReply state (memory[requestOne.address]?)) =
          some requestTwo) :
    ((packedReviewerDriveAgainstMemoryAux memory fuel state).trace.map
        (fun event => event.request.address))[0]? = some requestOne.address /\
      ((packedReviewerDriveAgainstMemoryAux memory fuel state).trace.map
        (fun event => event.request.address))[1]? = some requestTwo.address := by
  obtain ⟨rest, rfl⟩ : exists rest, fuel = rest + 2 :=
    ⟨fuel - 2, by omega⟩
  simp [packedReviewerDriveAgainstMemoryAux, hresultOne, hrequestOne,
    hresultTwo, hrequestTwo]

/-- The controller's structural fuel at a valid entry covers at least the
header probe and the first prelude probe. -/
theorem packedReviewerControllerMeasure_header_ge_two (n left right : Nat) :
    2 <= packedReviewerControllerMeasure (.header n left right) := by
  show 2 <= 1 + 2 * packedReviewerSparsePreludeRemaining
      (packedReviewerSparsePreludeInit n 0) +
    2 * packedReviewerWholeRemaining (packedReviewerWholeStart n left right)
  show 2 <= 1 + 2 * 3 +
    2 * packedReviewerWholeRemaining (packedReviewerWholeStart n left right)
  omega

/-- The initial prelude plan is the `.rankSuper` request plan: the guard is
satisfied at every size and every decoded count. -/
theorem packedReviewerCurrentPreludePlan_init (n longCount : Nat) :
    packedReviewerCurrentPreludePlan n longCount
        (packedReviewerSparsePreludeInit n longCount) =
      packedReviewerSparsePreludeRequestPlan n longCount .rankSuper := by
  unfold packedReviewerCurrentPreludePlan
  show (match packedReviewerSparsePreludeNextRequest
      (packedReviewerSparsePreludeInit n longCount) with
    | none => []
    | some request =>
        if request.index n <
            packedSourceWordCount n longCount request.source then
          packedReviewerSparsePreludeRequestPlan n longCount request
        else []) = _
  have hguard :
      PackedReviewerSparsePreludeRequest.index .rankSuper n <
        packedSourceWordCount n longCount
          (PackedReviewerSparsePreludeRequest.source .rankSuper) :=
    packedReviewerRankSuperIndex_lt n longCount
  simp [packedReviewerSparsePreludeInit,
    packedReviewerSparsePreludeNextRequest, hguard]

/-- The `.rankSuper` plan opens at the containing cell of its bit address. -/
theorem packedReviewerRankSuperPlan_head (n longCount : Nat) :
    (packedReviewerSparsePreludeRequestPlan n longCount .rankSuper)[0]? =
      some (packedReviewerSparsePreludeRequestBitAddress n longCount
          .rankSuper / packedReviewerCellWidth n) := by
  unfold packedReviewerSparsePreludeRequestPlan
  exact packedReviewerProbePlan_head
    (packedReviewerRankSuperReadWidth_pos n longCount)

/-- After a header reply decoding to `longCount`, the controller sits at the
first prelude probe with the `.rankSuper` plan. -/
theorem packedReviewerConsumeReply_header
    (n left right longCount : Nat) (cell : List Bool)
    (hdecode : SuccinctSpace.bitsToNatLE cell = longCount) :
    packedReviewerConsumeReply (.header n left right) (some cell) =
      .preludeProbe n left right longCount
        (packedReviewerSparsePreludeInit n longCount) 0 [] := by
  have hplan := packedReviewerCurrentPreludePlan_init n longCount
  have hhead := packedReviewerRankSuperPlan_head n longCount
  show packedReviewerNormalizePrelude
      (packedReviewerSparsePreludeRemaining
        (packedReviewerSparsePreludeInit n (SuccinctSpace.bitsToNatLE cell)))
      n left right (SuccinctSpace.bitsToNatLE cell)
      (packedReviewerSparsePreludeInit n (SuccinctSpace.bitsToNatLE cell)) = _
  rw [hdecode]
  show packedReviewerNormalizePrelude 3 n left right longCount
      (packedReviewerSparsePreludeInit n longCount) = _
  obtain ⟨head, tail, hcons⟩ :
      exists head tail,
        packedReviewerCurrentPreludePlan n longCount
          (packedReviewerSparsePreludeInit n longCount) = head :: tail := by
    cases hplanCase : packedReviewerCurrentPreludePlan n longCount
        (packedReviewerSparsePreludeInit n longCount) with
    | nil =>
        rw [hplan] at hplanCase
        rw [hplanCase] at hhead
        simp at hhead
    | cons head tail => exact ⟨head, tail, rfl⟩
  show (match packedReviewerCurrentPreludePlan n longCount
      (packedReviewerSparsePreludeInit n longCount) with
    | [] =>
        (match packedReviewerDecodePreludeReplies n longCount
            (packedReviewerSparsePreludeInit n longCount) [] with
        | none => PackedReviewerControllerState.failed
        | some reply =>
            packedReviewerNormalizePrelude 2 n left right longCount
              (packedReviewerSparsePreludeConsumeReply
                (packedReviewerSparsePreludeInit n longCount) reply))
    | _ :: _ =>
        PackedReviewerControllerState.preludeProbe n left right longCount
          (packedReviewerSparsePreludeInit n longCount) 0 []) = _
  rw [hcons]

/-- The first prelude probe's request carries the `.rankSuper` plan head as
its address. -/
theorem packedReviewerNextRequest_preludeProbe
    (n left right longCount : Nat) {address : Nat}
    (haddress :
      (packedReviewerCurrentPreludePlan n longCount
          (packedReviewerSparsePreludeInit n longCount))[0]? = some address) :
    packedReviewerNextRequest
        (.preludeProbe n left right longCount
          (packedReviewerSparsePreludeInit n longCount) 0 []) =
      some
        { origin := .sparsePrelude .rankSuper
          address := address
          ordinal := 0
          cellCount :=
            (packedReviewerCurrentPreludePlan n longCount
              (packedReviewerSparsePreludeInit n longCount)).length } := by
  show (match (packedReviewerCurrentPreludePlan n longCount
      (packedReviewerSparsePreludeInit n longCount))[0]? with
    | none => (none : Option PackedReviewerPhysicalRequest)
    | some address =>
        some
          (PackedReviewerPhysicalRequest.mk
            (PackedReviewerPhysicalOrigin.sparsePrelude
              PackedReviewerSparsePreludeRequest.rankSuper)
            address 0
            (packedReviewerCurrentPreludePlan n longCount
              (packedReviewerSparsePreludeInit n longCount)).length)) = _
  rw [haddress]

/--
**`FG-11` header liveness, universally.**  For every shape and every valid
half-open query, replacing only the counted long-count header cell -- cell
zero of the identical reviewer memory -- by the same-width encoding of
`longCount + w(n)` changes the second attempted physical address of the run.
The conclusion is an inequality between the two `trace[1]` address
projections, not between enclosing run records.
-/
theorem packedReviewerHeaderCellAddressLiveness_exact
    (shape : CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace.map
          (fun event => event.request.address))[1]? =
        some (packedReviewerSparsePreludeRequestBitAddress shape.size
          (longCount shape) .rankSuper / packedReviewerCellWidth shape.size) /\
      ((packedReviewerRunAgainstMemory
          ((packedReviewerMemory shape).set 0
            (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
              (longCount shape + packedReviewerCellWidth shape.size)))
          shape.size left right).trace.map
            (fun event => event.request.address))[1]? =
          some (packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape + packedReviewerCellWidth shape.size) .rankSuper /
              packedReviewerCellWidth shape.size) /\
      packedReviewerSparsePreludeRequestBitAddress shape.size
          (longCount shape) .rankSuper / packedReviewerCellWidth shape.size ≠
        packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape + packedReviewerCellWidth shape.size) .rankSuper /
          packedReviewerCellWidth shape.size := by
  have hvalid : left < right /\ right <= shape.size := ⟨hleft, hright⟩
  have hcontroller :
      packedReviewerController shape.size left right =
        .header shape.size left right := by
    unfold packedReviewerController
    simp [hvalid]
  have hwpos : 0 < packedReviewerCellWidth shape.size :=
    packedReviewerCellWidth_pos shape.size
  have hcanonicalCell :
      (packedReviewerMemory shape)[0]? =
        some (packedReviewerHeaderBits shape) :=
    packedReviewerMemory_header_cell shape
  have hcanonicalDecode :
      SuccinctSpace.bitsToNatLE (packedReviewerHeaderBits shape) =
        longCount shape :=
    packedReviewerHeaderBits_decode shape
  have hzero : 0 < (packedReviewerMemory shape).length := by
    rw [packedReviewerMemory_length]
    unfold packedReviewerCellCount
    omega
  have hmutatedGet :
      ((packedReviewerMemory shape).set 0
          (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
            (longCount shape + packedReviewerCellWidth shape.size)))[0]? =
        some (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
          (longCount shape + packedReviewerCellWidth shape.size)) := by
    rw [List.getElem?_set_self]
    exact hzero
  have hmutatedDecode :
      SuccinctSpace.bitsToNatLE
          (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
            (longCount shape + packedReviewerCellWidth shape.size)) =
        longCount shape + packedReviewerCellWidth shape.size :=
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt
      (packedReviewerLongCount_add_width_lt_two_pow shape)
  have hplanHeadCanonical :
      (packedReviewerCurrentPreludePlan shape.size (longCount shape)
          (packedReviewerSparsePreludeInit shape.size (longCount shape)))[0]? =
        some (packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape) .rankSuper /
          packedReviewerCellWidth shape.size) := by
    rw [packedReviewerCurrentPreludePlan_init]
    exact packedReviewerRankSuperPlan_head shape.size (longCount shape)
  have hplanHeadMutated :
      (packedReviewerCurrentPreludePlan shape.size
          (longCount shape + packedReviewerCellWidth shape.size)
          (packedReviewerSparsePreludeInit shape.size
            (longCount shape + packedReviewerCellWidth shape.size)))[0]? =
        some (packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape + packedReviewerCellWidth shape.size) .rankSuper /
          packedReviewerCellWidth shape.size) := by
    rw [packedReviewerCurrentPreludePlan_init]
    exact packedReviewerRankSuperPlan_head shape.size
      (longCount shape + packedReviewerCellWidth shape.size)
  have hne :
      packedReviewerSparsePreludeRequestBitAddress shape.size
          (longCount shape) .rankSuper / packedReviewerCellWidth shape.size ≠
        packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape + packedReviewerCellWidth shape.size) .rankSuper /
          packedReviewerCellWidth shape.size := by
    rw [packedReviewerRankSuperBitAddress_add shape.size (longCount shape)
      (packedReviewerCellWidth shape.size)]
    have hcoeff := packedReviewerLongRelativeRowBits_pos shape.size
    have hstep :
        (packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape) .rankSuper +
          packedReviewerCellWidth shape.size *
            (GenericSelect.superStride (2 * shape.size) *
              packedSuperWidth shape.size)) /
            packedReviewerCellWidth shape.size =
          packedReviewerSparsePreludeRequestBitAddress shape.size
              (longCount shape) .rankSuper /
              packedReviewerCellWidth shape.size +
            GenericSelect.superStride (2 * shape.size) *
              packedSuperWidth shape.size := by
      exact Nat.add_mul_div_left _ _ hwpos
    rw [hstep]
    omega
  refine ⟨?_, ?_, hne⟩
  · have hfirst := packedReviewerDriveAux_first_two_addresses
      (packedReviewerMemory shape)
      (packedReviewerControllerMeasure
        (packedReviewerController shape.size left right))
      (packedReviewerController shape.size left right)
      (requestOne :=
        { origin := .header, address := 0, ordinal := 0, cellCount := 1 })
      (requestTwo :=
        { origin := .sparsePrelude .rankSuper
          address :=
            packedReviewerSparsePreludeRequestBitAddress shape.size
              (longCount shape) .rankSuper / packedReviewerCellWidth shape.size
          ordinal := 0
          cellCount :=
            (packedReviewerCurrentPreludePlan shape.size (longCount shape)
              (packedReviewerSparsePreludeInit shape.size
                (longCount shape))).length })
      (by
        rw [hcontroller]
        exact packedReviewerControllerMeasure_header_ge_two
          shape.size left right)
      (by rw [hcontroller]; rfl)
      (by rw [hcontroller]; rfl)
      ?_ ?_
    · exact hfirst.2
    · show packedReviewerControllerResult
        (packedReviewerConsumeReply
          (packedReviewerController shape.size left right)
          ((packedReviewerMemory shape)[(0 : Nat)]?)) = none
      rw [hcontroller, hcanonicalCell,
        packedReviewerConsumeReply_header shape.size left right
          (longCount shape) _ hcanonicalDecode]
      rfl
    · show packedReviewerNextRequest
        (packedReviewerConsumeReply
          (packedReviewerController shape.size left right)
          ((packedReviewerMemory shape)[(0 : Nat)]?)) = _
      rw [hcontroller, hcanonicalCell,
        packedReviewerConsumeReply_header shape.size left right
          (longCount shape) _ hcanonicalDecode]
      exact packedReviewerNextRequest_preludeProbe shape.size left right
        (longCount shape) hplanHeadCanonical
  · have hfirst := packedReviewerDriveAux_first_two_addresses
      ((packedReviewerMemory shape).set 0
        (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
          (longCount shape + packedReviewerCellWidth shape.size)))
      (packedReviewerControllerMeasure
        (packedReviewerController shape.size left right))
      (packedReviewerController shape.size left right)
      (requestOne :=
        { origin := .header, address := 0, ordinal := 0, cellCount := 1 })
      (requestTwo :=
        { origin := .sparsePrelude .rankSuper
          address :=
            packedReviewerSparsePreludeRequestBitAddress shape.size
                (longCount shape + packedReviewerCellWidth shape.size)
                .rankSuper /
              packedReviewerCellWidth shape.size
          ordinal := 0
          cellCount :=
            (packedReviewerCurrentPreludePlan shape.size
              (longCount shape + packedReviewerCellWidth shape.size)
              (packedReviewerSparsePreludeInit shape.size
                (longCount shape +
                  packedReviewerCellWidth shape.size))).length })
      (by
        rw [hcontroller]
        exact packedReviewerControllerMeasure_header_ge_two
          shape.size left right)
      (by rw [hcontroller]; rfl)
      (by rw [hcontroller]; rfl)
      ?_ ?_
    · exact hfirst.2
    · show packedReviewerControllerResult
        (packedReviewerConsumeReply
          (packedReviewerController shape.size left right)
          (((packedReviewerMemory shape).set 0
            (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
              (longCount shape +
                packedReviewerCellWidth shape.size)))[(0 : Nat)]?)) = none
      rw [hcontroller, hmutatedGet,
        packedReviewerConsumeReply_header shape.size left right
          (longCount shape + packedReviewerCellWidth shape.size) _
          hmutatedDecode]
      rfl
    · show packedReviewerNextRequest
        (packedReviewerConsumeReply
          (packedReviewerController shape.size left right)
          (((packedReviewerMemory shape).set 0
            (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
              (longCount shape +
                packedReviewerCellWidth shape.size)))[(0 : Nat)]?)) = _
      rw [hcontroller, hmutatedGet,
        packedReviewerConsumeReply_header shape.size left right
          (longCount shape + packedReviewerCellWidth shape.size) _
          hmutatedDecode]
      exact packedReviewerNextRequest_preludeProbe shape.size left right
        (longCount shape + packedReviewerCellWidth shape.size)
        hplanHeadMutated

/-- The existential public form of universal header-address liveness. -/
theorem packedReviewerHeaderCellAddressLiveness
    (shape : CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    exists addressCanonical addressMutated,
      ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace.map
            (fun event => event.request.address))[1]? =
          some addressCanonical /\
      ((packedReviewerRunAgainstMemory
          ((packedReviewerMemory shape).set 0
            (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
              (longCount shape + packedReviewerCellWidth shape.size)))
          shape.size left right).trace.map
            (fun event => event.request.address))[1]? =
          some addressMutated /\
      addressCanonical ≠ addressMutated := by
  refine ⟨packedReviewerSparsePreludeRequestBitAddress shape.size
      (longCount shape) .rankSuper / packedReviewerCellWidth shape.size,
    packedReviewerSparsePreludeRequestBitAddress shape.size
        (longCount shape + packedReviewerCellWidth shape.size) .rankSuper /
      packedReviewerCellWidth shape.size, ?_⟩
  exact packedReviewerHeaderCellAddressLiveness_exact shape left right hleft hright

/-- The same inequality at the frozen projection form: `trace[1]?` first,
then the address map.  `List.getElem?_map` makes the two forms one fact. -/
theorem packedReviewerHeaderCellAddressLiveness_proj
    (shape : CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    exists addressCanonical addressMutated,
      ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace[1]?).map
            (fun event => event.request.address) =
          some addressCanonical /\
      ((packedReviewerRunAgainstMemory
          ((packedReviewerMemory shape).set 0
            (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
              (longCount shape + packedReviewerCellWidth shape.size)))
          shape.size left right).trace[1]?).map
            (fun event => event.request.address) =
          some addressMutated /\
      addressCanonical ≠ addressMutated := by
  obtain ⟨addressCanonical, addressMutated, hcanonical, hmutated, hne⟩ :=
    packedReviewerHeaderCellAddressLiveness shape left right hleft hright
  rw [List.getElem?_map] at hcanonical hmutated
  exact ⟨addressCanonical, addressMutated, hcanonical, hmutated, hne⟩

/-- The canonical run opens with the header probe at cell zero. -/
theorem packedReviewerRunOpensWithHeader
    (shape : CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace.map
          (fun event => event.request.address))[0]? = some 0 := by
  obtain ⟨addressCanonical, addressMutated, _hcanonical, _hmutated, _hne⟩ :=
    packedReviewerHeaderCellAddressLiveness shape left right hleft hright
  -- re-run the two-step opening on the canonical side only
  have hvalid : left < right /\ right <= shape.size := ⟨hleft, hright⟩
  have hcontroller :
      packedReviewerController shape.size left right =
        .header shape.size left right := by
    unfold packedReviewerController
    simp [hvalid]
  have hcanonicalCell :
      (packedReviewerMemory shape)[0]? =
        some (packedReviewerHeaderBits shape) :=
    packedReviewerMemory_header_cell shape
  have hfirst := packedReviewerDriveAux_first_two_addresses
    (packedReviewerMemory shape)
    (packedReviewerControllerMeasure
      (packedReviewerController shape.size left right))
    (packedReviewerController shape.size left right)
    (requestOne :=
      { origin := .header, address := 0, ordinal := 0, cellCount := 1 })
    (requestTwo :=
      { origin := .sparsePrelude .rankSuper
        address :=
          packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape) .rankSuper /
              packedReviewerCellWidth shape.size
        ordinal := 0
        cellCount :=
          (packedReviewerCurrentPreludePlan shape.size (longCount shape)
            (packedReviewerSparsePreludeInit shape.size
              (longCount shape))).length })
    (by
      rw [hcontroller]
      exact packedReviewerControllerMeasure_header_ge_two shape.size left right)
    (by rw [hcontroller]; rfl)
    (by rw [hcontroller]; rfl)
    ?_ ?_
  · exact hfirst.1
  · show packedReviewerControllerResult
      (packedReviewerConsumeReply
        (packedReviewerController shape.size left right)
        ((packedReviewerMemory shape)[(0 : Nat)]?)) = none
    rw [hcontroller, hcanonicalCell,
      packedReviewerConsumeReply_header shape.size left right
        (longCount shape) _ (packedReviewerHeaderBits_decode shape)]
    rfl
  · show packedReviewerNextRequest
      (packedReviewerConsumeReply
        (packedReviewerController shape.size left right)
        ((packedReviewerMemory shape)[(0 : Nat)]?)) = _
    rw [hcontroller, hcanonicalCell,
      packedReviewerConsumeReply_header shape.size left right
        (longCount shape) _ (packedReviewerHeaderBits_decode shape)]
    apply packedReviewerNextRequest_preludeProbe
    rw [packedReviewerCurrentPreludePlan_init]
    exact packedReviewerRankSuperPlan_head shape.size (longCount shape)

/-! ## `FG-14`: the boundary campaign at the one universal capstone

Every instance below is the same quantifier instantiated -- no per-size
variant, readiness dispatch, or compatibility branch exists to select.  The
threshold sizes are the ones `Boundaries.lean` locates from the geometry: the
long crossover `5487/5488/5489` and the interior-readiness window endpoints
and neighbours `1023/1024/1025` and `1329/1330/1331`.
-/

/-- Empty representation. -/
theorem packedReviewerStageFCapstone_empty :
    PackedReviewerStageFCapstone [] 0 0 :=
  packedReviewerStageFCapstone_holds [] 0 0

/-- Singleton representation, with its one valid query. -/
theorem packedReviewerStageFCapstone_singleton :
    PackedReviewerStageFCapstone [0] 0 1 :=
  packedReviewerStageFCapstone_holds [0] 0 1

/-- The first size-two Cartesian shape. -/
theorem packedReviewerStageFCapstone_sizeTwoLeft :
    PackedReviewerStageFCapstone [0, 1] 0 2 :=
  packedReviewerStageFCapstone_holds [0, 1] 0 2

/-- The second size-two Cartesian shape. -/
theorem packedReviewerStageFCapstone_sizeTwoRight :
    PackedReviewerStageFCapstone [1, 0] 0 2 :=
  packedReviewerStageFCapstone_holds [1, 0] 0 2

/-- The first size-two shape's run answers its full query at index `0`. -/
theorem packedReviewerStageFSizeTwoLeftRun :
    (packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [0, 1]))
        (SuccinctClassic.cartesianShape [0, 1]).size 0 2).terminal =
      some (some 0) := by
  have hcapstone := packedReviewerStageFCapstone_holds [0, 1] 0 2
  have hterminal := hcapstone.guarded_reference_result.1
  have hexact := SuccinctClassic.queryCosted_exact [0, 1]
    (left := 0) (len := 2) (by omega) (by simp)
  have hscan : scanWindow [0, 1] 0 2 = 0 := by decide
  rw [hscan] at hexact
  have hvalue :
      (SuccinctClassic.queryTraceResult [0, 1] 0 2).value =
        (SuccinctClassic.queryCosted [0, 1] 0 (0 + 2)).erase := rfl
  rw [hterminal, hvalue, hexact]

/-- The second size-two shape's run answers its full query at index `1`. -/
theorem packedReviewerStageFSizeTwoRightRun :
    (packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [1, 0]))
        (SuccinctClassic.cartesianShape [1, 0]).size 0 2).terminal =
      some (some 1) := by
  have hcapstone := packedReviewerStageFCapstone_holds [1, 0] 0 2
  have hterminal := hcapstone.guarded_reference_result.1
  have hexact := SuccinctClassic.queryCosted_exact [1, 0]
    (left := 0) (len := 2) (by omega) (by simp)
  have hscan : scanWindow [1, 0] 0 2 = 1 := by decide
  rw [hscan] at hexact
  have hvalue :
      (SuccinctClassic.queryTraceResult [1, 0] 0 2).value =
        (SuccinctClassic.queryCosted [1, 0] 0 (0 + 2)).erase := rfl
  rw [hterminal, hvalue, hexact]

/-- The two size-two instances really cover two distinct shapes: were the
shapes equal, the identical run object would return both `some 0` and
`some 1` for the same query. -/
theorem packedReviewerStageFCapstone_sizeTwoShapesDistinct :
    SuccinctClassic.cartesianShape [(0 : Int), 1] ≠
      SuccinctClassic.cartesianShape [(1 : Int), 0] := by
  intro heq
  have hleft := packedReviewerStageFSizeTwoLeftRun
  have hright := packedReviewerStageFSizeTwoRightRun
  rw [heq] at hleft
  rw [hleft] at hright
  simp at hright

/-- Long crossover, one below. -/
theorem packedReviewerStageFCapstone_crossover5487 :
    PackedReviewerStageFCapstone (List.replicate 5487 0) 0 5487 :=
  packedReviewerStageFCapstone_holds (List.replicate 5487 0) 0 5487

/-- Long crossover, at the recorded `5488`. -/
theorem packedReviewerStageFCapstone_crossover5488 :
    PackedReviewerStageFCapstone (List.replicate 5488 0) 0 5488 :=
  packedReviewerStageFCapstone_holds (List.replicate 5488 0) 0 5488

/-- Long crossover, one above. -/
theorem packedReviewerStageFCapstone_crossover5489 :
    PackedReviewerStageFCapstone (List.replicate 5489 0) 0 5489 :=
  packedReviewerStageFCapstone_holds (List.replicate 5489 0) 0 5489

/-- Interior-readiness window: below, both endpoints, inside neighbours, and
above -- six sizes, one quantifier. -/
theorem packedReviewerStageFCapstone_readinessWindow :
    PackedReviewerStageFCapstone (List.replicate 1023 0) 0 1023 /\
      PackedReviewerStageFCapstone (List.replicate 1024 0) 0 1024 /\
      PackedReviewerStageFCapstone (List.replicate 1025 0) 0 1025 /\
      PackedReviewerStageFCapstone (List.replicate 1329 0) 0 1329 /\
      PackedReviewerStageFCapstone (List.replicate 1330 0) 0 1330 /\
      PackedReviewerStageFCapstone (List.replicate 1331 0) 0 1331 :=
  ⟨packedReviewerStageFCapstone_holds _ 0 1023,
    packedReviewerStageFCapstone_holds _ 0 1024,
    packedReviewerStageFCapstone_holds _ 0 1025,
    packedReviewerStageFCapstone_holds _ 0 1329,
    packedReviewerStageFCapstone_holds _ 0 1330,
    packedReviewerStageFCapstone_holds _ 0 1331⟩

/-- Query-level boundary cases on the pinned fixture shape: empty range,
reversed endpoints, right endpoint out of range, left endpoint out of
range.  Each still inhabits the capstone -- the guard is inside it. -/
theorem packedReviewerStageFCapstone_invalidQueries :
    PackedReviewerStageFCapstone [7, 3, 3] 1 1 /\
      PackedReviewerStageFCapstone [7, 3, 3] 2 1 /\
      PackedReviewerStageFCapstone [7, 3, 3] 0 4 /\
      PackedReviewerStageFCapstone [7, 3, 3] 5 7 :=
  ⟨packedReviewerStageFCapstone_holds [7, 3, 3] 1 1,
    packedReviewerStageFCapstone_holds [7, 3, 3] 2 1,
    packedReviewerStageFCapstone_holds [7, 3, 3] 0 4,
    packedReviewerStageFCapstone_holds [7, 3, 3] 5 7⟩

/-- An invalid endpoint pair produces the exact terminal `.done none` run
with an empty trace, on the identical run object. -/
theorem packedReviewerStageFInvalidRunExact
    (xs : List Int) (left right : Nat)
    (hbad : Not (left < right /\ right <= (SuccinctClassic.cartesianShape xs).size)) :
    (packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
        (SuccinctClassic.cartesianShape xs).size left right).terminal =
          some none /\
      (packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
        (SuccinctClassic.cartesianShape xs).size left right).trace = [] := by
  have hcertificate :=
    packedReviewerRunAgainstMemory_invalid_certificate
      (SuccinctClassic.cartesianShape xs) left right hbad
  have htrace :=
    packedReviewerRunAgainstMemory_invalid_trace_eq_nil
      (SuccinctClassic.cartesianShape xs) left right hbad
  exact ⟨hcertificate.1, htrace⟩

/-! ### The duplicate-minimum leftmost fixture

`xs0 = [7, 3, 3]` with the full query `(0, 3)`: the minimum `3` occurs at
indices `1` and `2`, and the half-open leftmost contract selects `1`.  The
expected value comes from the independent `scanWindow` reference scan and the
`LeftmostArgMin` specification -- never from the packed implementation being
tested.
-/

/-- The reference side: the guarded trace result of the fixture is the
independent scan's answer, index `1`. -/
theorem packedReviewerStageFDuplicateMinReference :
    (SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value = some 1 := by
  have hexact := SuccinctClassic.queryCosted_exact [7, 3, 3]
    (left := 0) (len := 3) (by omega) (by simp)
  have hscan : scanWindow [7, 3, 3] 0 3 = 1 := by decide
  rw [hscan] at hexact
  have hvalue :
      (SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value =
        (SuccinctClassic.queryCosted [7, 3, 3] 0 (0 + 3)).erase := rfl
  rw [hvalue]
  exact hexact

/-- The tie policy, from the specification side: index `1` is the leftmost
argmin of the fixture window. -/
theorem packedReviewerStageFDuplicateMinLeftmost :
    LeftmostArgMin [7, 3, 3] 0 3 1 := by
  have hexact := SuccinctClassic.queryCosted_exact [7, 3, 3]
    (left := 0) (len := 3) (by omega) (by simp)
  have hscan : scanWindow [7, 3, 3] 0 3 = 1 := by decide
  exact SuccinctClassic.queryCosted_leftmost [7, 3, 3]
    (left := 0) (len := 3) (by omega) (by simp)
    (by rw [hexact, hscan])

/-- The packed run itself returns the leftmost duplicate-minimum index. -/
theorem packedReviewerStageFDuplicateMinRun :
    (packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
      some (some 1) := by
  have hcapstone := packedReviewerStageFCapstone_holds [7, 3, 3] 0 3
  have hterminal := hcapstone.guarded_reference_result.1
  rw [hterminal, packedReviewerStageFDuplicateMinReference]

/-! ### No second representation

The controller entry and the memory builder are single uniform definitions;
the readiness and crossover predicates appear only inside width and geometry
bounds, never as a dispatch that selects an alternative representation.  The
two `rfl` pins below record that uniformity as checked propositions, and the
boundary instances above all instantiate the one universal theorem.
-/

/-- The controller entry is one guard and one uniform state, at every size. -/
theorem packedReviewerControllerUniformEntry (n left right : Nat) :
    packedReviewerController n left right =
      if left < right /\ right <= n then .header n left right
      else .done none := rfl

/-- The memory builder is one chunking expression, at every shape. -/
theorem packedReviewerMemoryUniformBuilder (shape : CartesianShape) :
    packedReviewerMemory shape =
      (List.range (packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape))).map fun i =>
        ((packedReviewerPaddedBits shape).drop
          (i * packedReviewerCellWidth shape.size)).take
          (packedReviewerCellWidth shape.size) := rfl

/-! ## The pinned fixture: kernel-checked literal evaluation

Everything below evaluates the frozen matrix section 10.2 fixture
(`xs0 = [7, 3, 3]`, query `(0, 3)`) to literals with kernel-checked proofs.
`Nat.log2` is not kernel-reducible in this toolchain, so every
`log2`-carrying scalar is first pinned by `simp` over the definition
closure, and all remaining log2-free literal computation is discharged by
`decide`.  No native evaluation and no unchecked escape hatch appears.
-/

def egcpShapeLit : CartesianShape :=
  .node (.node .empty .empty) (.node .empty .empty)

def egcpAccessLit : List Bool := [false, false, false, false, false, false, false, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]

def egcpCloseLit : List Bool := [false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true, true, false, false, true, false, false, true, false, true]

def egcpFringeLit : List Bool := [false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true]

def egcpSelectLit : List Bool := [false, false, true, false, true, false, true, false]

def egcpPayloadLit : List Bool := [true, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, false]

def egcpPaddedLit : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, true, true, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false, false, false, false, false]

def egcpMemLit : List (List Bool) := [[false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [true, true, false, false, true, false, false, false, false, false, false, false, false, true, false],
  [false, false, true, true, false, false, false, false, false, false, false, false, false, false, false],
  [false, true, false, false, false, false, true, false, false, false, true, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, true, false, false, true, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, true, false, false, false, false],
  [false, true, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, true, false],
  [false, false, false, true, false, true, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false],
  [false, false, false, false, false, false, false, false, true, false, false, false, false, true, false],
  [false, false, false, false, false, false, true, false, false, false, false, true, false, false, false],
  [false, false, true, false, false, false, false, true, true, false, false, true, false, false, true],
  [false, true, false, true, false, false, false, false, true, false, false, false, true, false, false],
  [false, false, true, false, false, false, false, false, true, false, false, true, false, true, false],
  [false, true, true, false, true, false, true, true, false, true, false, true, false, false, true],
  [false, true, false, true, false, false, false, false, false, false, false, false, false, false, false]]

def egcpAddrsLit : List Nat := [0, 10, 11, 11, 2, 2, 2, 3, 3, 5, 6, 8, 1, 20, 20, 20, 20, 19, 20, 20, 19, 20, 2, 2, 2, 3, 3, 5, 7, 9, 1, 19, 20, 19, 20, 19, 19, 20, 19, 20, 1, 1, 1, 19, 1, 1, 20, 20, 19, 18, 19, 20, 1, 1, 2, 1, 18, 1, 19, 19, 20, 18, 18, 1, 1, 2, 1, 19]

def egcpDecisiveMutantCell : List Bool := [true, true, true, true, true, true, true, true, true, true, false, true, true, true, true]

section EGCPFixtureEvaluation

set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false


attribute [local simp] Nat.log2
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerMemory
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparseCount
attribute [local simp] RMQ.Cartesian.CartesianShape.bpCode
attribute [local simp] RMQ.GenericSelect.sparseExceptionRelativeEntries
attribute [local simp] RMQ.GenericSelect.localSlotCount
attribute [local simp] RMQ.GenericSelect.localSlotsPerSuper
attribute [local simp] RMQ.GenericSelect.localStride
attribute [local simp] RMQ.GenericSelect.ell
attribute [local simp] RMQ.GenericSelect.wordBits
attribute [local simp] RMQ.SuccinctRank.machineWordBits
attribute [local simp] RMQ.GenericSelect.superStride
attribute [local simp] RMQ.GenericSelect.selectLocalSlotsPerSuper
attribute [local simp] RMQ.GenericSelect.superSlotCount
attribute [local simp] RMQ.GenericSelect.occurrenceCount
attribute [local simp] RMQ.Succinct.rankPrefix
attribute [local simp] RMQ.GenericSelect.selectCeilDiv
attribute [local simp] RMQ.GenericSelect.sparseExceptionRelativeEntriesForSlot
attribute [local simp] RMQ.GenericSelect.superEndOccurrence
attribute [local simp] RMQ.GenericSelect.superBaseOccurrence
attribute [local simp] RMQ.GenericSelect.relativeOffsetsOrZero
attribute [local simp] RMQ.Succinct.select
attribute [local simp] RMQ.Succinct.selectFrom
attribute [local simp] RMQ.GenericSelect.position
attribute [local simp] RMQ.GenericSelect.localBaseOccurrence
attribute [local simp] RMQ.GenericSelect.localSlotInSuperOfGlobal
attribute [local simp] RMQ.GenericSelect.localSuperSlot
attribute [local simp] RMQ.GenericSelect.localIsSparseException
attribute [local simp] RMQ.GenericSelect.shortSuperLocalSpan
attribute [local simp] RMQ.GenericSelect.shortSuperLocalEndOccurrence
attribute [local simp] RMQ.GenericSelect.superIsLong
attribute [local simp] RMQ.GenericSelect.superSpan
attribute [local simp] RMQ.GenericSelect.superLongSpan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.longCount
attribute [local simp] RMQ.GenericSelect.longSuperFlagBits
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerCellCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerCellWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerCellBound
attribute [local simp] RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
attribute [local simp] RMQ.SuccinctClose.bpChunkSelectTableOverhead
attribute [local simp] RMQ.SuccinctClose.bpChunkSelectEntryWidth
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkBits
attribute [local simp] RMQ.SuccinctClose.bpChunkSelectRowCount
attribute [local simp] RMQ.SuccinctClose.bpFringeTableOverhead
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkEntryWidth
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkEntryBound
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkRowCount
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorOverhead
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead
attribute [local simp] RMQ.SuccinctClose.bpSparseLevelWidth
attribute [local simp] RMQ.SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead
attribute [local simp] RMQ.GenericSelect.canonicalSparseExceptionSelectOverhead
attribute [local simp] RMQ.GenericSelect.canonicalSparseExceptionDirectoryOverhead
attribute [local simp] RMQ.GenericSelect.sparseExceptionRelativeTableOverhead
attribute [local simp] RMQ.SuccinctSpace.idDivLogLogOverhead
attribute [local simp] RMQ.SuccinctSpace.logLogCubedSampledDirectoryOverhead
attribute [local simp] RMQ.GenericSelect.longSuperRelativeTableOverhead
attribute [local simp] RMQ.SuccinctFinal.relativeSplitSparseExceptionBPCloseRankOverhead
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerPayloadLength
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerAccessLength
attribute [local simp] RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSourceBitLength
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSourceBitLength
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSourceStride
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorBlockWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummaryBlockCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummaryBlockCountRaw
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummaryBase
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummaryActiveDecidable
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSlots
attribute [local simp] RMQ.SuccinctSpace.logLogSampledDirectoryOverhead
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummarySuperSlots
attribute [local simp] RMQ.SuccinctSpace.sampledDirectoryOverhead
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummarySuperCountRaw
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummaryRelativeWidthRaw
attribute [local simp] RMQ.SuccinctClose.bpSuperblockSpan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedSummaryActive
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorOffsetWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorMacroSize
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummaryRelativeWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummarySuperWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedRankBlockWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedRankWordSize
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSparseWordSize
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSparseSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLocalSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSuperSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLongFlagWordSize
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLocalWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSuperWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedBpCodeWordWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSourceWordCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorGlobalSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorMacroCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorGlobalLevelCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorLocalSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummarySuperCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedRankBlockSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedRankSuperSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSparseRelativeCapacity
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSparseRankSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLongRelativeSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLongFlagRankSlots
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedChunkCount
attribute [local simp] RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQFlatPayloadSource.toCtorIdx
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerPaddedBits
attribute [local simp] RMQ.Cartesian.CartesianShape.size
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerAllocatedBits
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSerializedBits
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerPayloadBits
attribute [local simp] RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload
attribute [local simp] RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
attribute [local simp] RMQ.SuccinctClose.bpChunkSelectTable
attribute [local simp] RMQ.SuccinctClose.bpChunkSelectEntries
attribute [local simp] RMQ.SuccinctClose.bpChunkSelectPos
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkPattern
attribute [local simp] RMQ.SuccinctSpace.natToBitsLE
attribute [local simp] RMQ.SuccinctSpace.FixedWidthNatTable.ofEntries
attribute [local simp] RMQ.SuccinctSpace.FixedWidthNatTable.ofEncodedWords
attribute [local simp] RMQ.SuccinctSpace.flattenPayloadWords
attribute [local simp] RMQ.SuccinctSpace.bitsToNatLE
attribute [local simp] RMQ.SuccinctSpace.bitToNat
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkTable
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkEntries
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkPacked
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkArgMin
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkExcessOffsetAt
attribute [local simp] RMQ.SuccinctClose.bpFringeScanArgMin
attribute [local simp] RMQ.SuccinctClose.bpFringeScanArgMinFrom
attribute [local simp] RMQ.SuccinctClose.bpFringeScanBetter
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkMinOffset
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkDeltaOffset
attribute [local simp] RMQ.SuccinctSpace.FixedWidthNatTable.payload
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorDirectory
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangeMinCostedWithStore
attribute [local simp] RMQ.SuccinctSpace.FlatWordStore.ofArray
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangeMinCostedWithRead
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithRead
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangeMinComputation
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineCrossMacroCandidateComputation
attribute [local simp] RMQ.SuccinctClose.bpCandidateMerge3?
attribute [local simp] RMQ.SuccinctClose.bpCandidateMerge?
attribute [local simp] RMQ.SuccinctClose.bpCandidateBetter
attribute [local simp] RMQ.SuccinctSpace.FlatStoreComputation.map
attribute [local simp] RMQ.SuccinctSpace.FlatStoreComputation.pure
attribute [local simp] RMQ.SuccinctSpace.FlatWordStore
attribute [local simp] RMQ.SuccinctSpace.FlatStoreComputation.bind
attribute [local simp] RMQ.SuccinctSpace.FlatStoreExecution.value
attribute [local simp] RMQ.SuccinctSpace.FlatStoreComputation.run
attribute [local simp] RMQ.SuccinctSpace.FlatStoreExecution.append
attribute [local simp] RMQ.SuccinctSpace.FlatStoreExecution.reads
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineGlobalSpanCandidateComputation
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineMinCandidateComputation
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineSummaryComputation
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.argOffset
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.argOffsetTable
attribute [local simp] RMQ.SuccinctClose.bpBlockArgMinLocalOffsetEntries
attribute [local simp] RMQ.SuccinctClose.bpBlockArgMinLocalOffset
attribute [local simp] RMQ.SuccinctClose.blockStartOf
attribute [local simp] RMQ.SuccinctClose.bpBlockArgMinPrefixPos
attribute [local simp] RMQ.SuccinctClose.bpBlockArgMinPrefixPosFrom
attribute [local simp] RMQ.SuccinctClose.bpExcessAt
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.maxRel
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.maxRelTable
attribute [local simp] RMQ.SuccinctClose.bpBlockRelativeMaxExcessEntries
attribute [local simp] RMQ.SuccinctClose.bpBlockRelativeMaxExcess
attribute [local simp] RMQ.SuccinctClose.bpBlockMaxExcess
attribute [local simp] RMQ.SuccinctClose.bpBlockExcessSamples
attribute [local simp] RMQ.SuccinctClose.natListMax
attribute [local simp] RMQ.SuccinctClose.bpRelativeExcessEntry
attribute [local simp] RMQ.SuccinctClose.bpSuperblockStartPos
attribute [local simp] RMQ.SuccinctClose.bpSuperblockStartBlock
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.minRel
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.minRelTable
attribute [local simp] RMQ.SuccinctClose.bpBlockRelativeMinExcessEntries
attribute [local simp] RMQ.SuccinctClose.bpBlockRelativeMinExcess
attribute [local simp] RMQ.SuccinctClose.bpBlockMinExcess
attribute [local simp] RMQ.SuccinctClose.natListMinFrom
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.baseline
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.baselineTable
attribute [local simp] RMQ.SuccinctClose.bpSuperblockBaselineEntries
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineReadNatComputation
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentOffsets
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorComponentStore
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmGlobalLevelMachineStore
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPSparseLevelTable.table
attribute [local simp] RMQ.SuccinctClose.bpSparseLevelEntries
attribute [local simp] RMQ.SuccinctClose.bpSparseLevelCell
attribute [local simp] RMQ.SuccinctClose.bpSparseLogSpan
attribute [local simp] RMQ.SuccinctSpace.FixedWidthNatTable.machineStore
attribute [local simp] RMQ.SuccinctSpace.fixedWidthNatTableMachineWords
attribute [local simp] RMQ.SuccinctSpace.FixedWidthNatTable.store
attribute [local simp] RMQ.SuccinctSpace.PayloadWordStore.words
attribute [local simp] RMQ.SuccinctSpace.chunkPayloadWords
attribute [local simp] RMQ.SuccinctSpace.chunkPayloadWordsFuel
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.canonicalLayout
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryRelativeWidthRaw
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBase
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuperRaw
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.macroSampleCount
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.macroSize
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.blocksPerSuper
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.blockCount
attribute [local simp] RMQ.SuccinctClose.bpSparseLevelTable
attribute [local simp] RMQ.SuccinctClose.bpSparseLevelTableOverhead
attribute [local simp] RMQ.SuccinctClose.bpSparseLevelDomain
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmLocalLevelMachineStore
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmGlobalMachineStore
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.table
attribute [local simp] RMQ.SuccinctClose.bpGlobalSparseBlockEntries
attribute [local simp] RMQ.SuccinctClose.bpGlobalSparseCellBlock
attribute [local simp] RMQ.SuccinctClose.bpRangeArgMinBlock
attribute [local simp] RMQ.SuccinctClose.bpRangeArgMinBlockFrom
attribute [local simp] RMQ.SuccinctClose.bpBetterArgMinBlock
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorGlobalTable
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.blockAddressWidth
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.globalLevelCount
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.blockSize
attribute [local simp] RMQ.SuccinctClose.concreteBPGlobalSparseBlockTable
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmLocalMachineStore
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.table
attribute [local simp] RMQ.SuccinctClose.bpLocalSparseOffsetEntries
attribute [local simp] RMQ.SuccinctClose.bpLocalSparseCellOffset
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorLocalTable
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.offsetWidth
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.levelCount
attribute [local simp] RMQ.SuccinctClose.concreteBPLocalSparseOffsetTable
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmSummaryMachineStore
attribute [local simp] RMQ.SuccinctSpace.BoundedPayloadWordStore.append
attribute [local simp] RMQ.SuccinctSpace.BoundedPayloadWordStore.store
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmSummaryTable
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.relativeWidth
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.superWidth
attribute [local simp] RMQ.SuccinctClose.RelativeRmm.Layout.superSampleCount
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.deadAddress
attribute [local simp] RMQ.SuccinctSpace.FixedWidthNatTable.machineReadComputationAt
attribute [local simp] RMQ.SuccinctSpace.FlatStoreComputation.readMany
attribute [local simp] RMQ.SuccinctSpace.FlatStoreComputation.read
attribute [local simp] RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
attribute [local simp] RMQ.SuccinctSpace.collectPayloadWords
attribute [local simp] RMQ.SuccinctSpace.fixedWidthNatTableMachineFootprintAt
attribute [local simp] RMQ.SuccinctSpace.fixedWidthNatTableMachineFootprint
attribute [local simp] RMQ.SuccinctSpace.consecutiveWordIndices
attribute [local simp] RMQ.SuccinctSpace.fixedWidthNatTableMachineChunkCount
attribute [local simp] RMQ.SuccinctClose.bpRelativeSummaryMinCandidate
attribute [local simp] RMQ.SuccinctClose.bpGlobalSparseCellSlot
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.globalBlock
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.globalLevel
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineLocalSpanCandidateComputation
attribute [local simp] RMQ.SuccinctClose.bpLocalSparseCellSlot
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.localOffset
attribute [local simp] RMQ.SuccinctClose.CanonicalRelativeRmmInteriorComponentOffsets.localLevel
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
attribute [local simp] RMQ.SuccinctSpace.FlatStoreExecution.toCosted
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangePhysicalWordsReadWithStore
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorRangeMinExecutionWithStore
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPSparseLevelTable.payload
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorQueryCost
attribute [local simp] RMQ.SuccinctClose.canonicalRelativeRmmInteriorDirectoryPayloadLength
attribute [local simp] RMQ.SuccinctClose.PayloadLiveBPRelativeRmmInteriorDirectory.payload
attribute [local simp] RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload
attribute [local simp] RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSourcePayload
attribute [local simp] RMQ.SuccinctSpace.FixedWidthRankSampleTables.falseTable
attribute [local simp] RMQ.GenericSelect.SparseExceptionDirectory.relativeTable
attribute [local simp] RMQ.GenericSelect.SparseExceptionDirectory.relativeWidth
attribute [local simp] RMQ.GenericSelect.SparseExceptionDirectory.relativeEntries
attribute [local simp] RMQ.GenericSelect.SparseExceptionDirectory.rankData
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.sparseDirectory
attribute [local simp] RMQ.GenericSelect.SparseExceptionDirectory.flagBits
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.longSuperRelativeTable
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.longSuperRelativeWidth
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.longSuperRelativeEntries
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockTables
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockFalseEntries
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockWidth
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.blockTrueEntries
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superTables
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superFalseEntries
attribute [local simp] RMQ.SuccinctSpace.FixedWidthRankSampleTables.trueTable
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superWidth
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.longFlagRankData
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.longFlagRankBlockOverhead
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.longFlagRankSuperOverhead
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.longFlagBits
attribute [local simp] RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superTrueEntries
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.localTable
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.localFieldWidth
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.localEntries
attribute [local simp] RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.firstOffsetTable
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffset
attribute [local simp] RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.rankBeforeTable
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.rankBefore
attribute [local simp] RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.baseWordIndexTable
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndex
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.superTable
attribute [local simp] RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.baseOccurrenceTable
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.superFieldWidth
attribute [local simp] RMQ.GenericSelect.SparseExceptionSelectData.superEntries
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences
attribute [local simp] RMQ.GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrence
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorBlockWidth
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockCount
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive_decidable
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummarySuperWidth
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummarySuperCountRaw
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeMinMaxArgSummaryTableActive
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorGlobalLevelCount
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorMacroCount
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorMacroSize
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBlockSize
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorLocalTable
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorOffsetWidth
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeRmmInteriorLevelCount
attribute [local simp] RMQ.SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryRelativeWidth
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummarySuperCount
attribute [local simp] RMQ.SuccinctClose.canonicalBPRelativeSummaryBlocksPerSuper
attribute [local simp] RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData
attribute [local simp] RMQ.SuccinctSelect.sparseDenseFalseSelectQueryCost
attribute [local simp] RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockWidth
attribute [local simp] RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankWordSize
attribute [local simp] RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlocksPerSuper
attribute [local simp] RMQ.SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
attribute [local simp] RMQ.SuccinctRank.canonicalRankWordBridgeOfChunksWithSentinel
attribute [local simp] RMQ.SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel
attribute [local simp] RMQ.SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock
attribute [local simp] RMQ.SuccinctRank.CanonicalRankWordBridge.bitWords
attribute [local simp] RMQ.SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
attribute [local simp] RMQ.SuccinctRank.canonicalBlockRankEntries
attribute [local simp] RMQ.SuccinctSpace.FixedWidthRankSampleTables.ofEntries
attribute [local simp] RMQ.SuccinctRank.canonicalSuperRankSampleTables
attribute [local simp] RMQ.SuccinctRank.canonicalSuperRankEntries
attribute [local simp] RMQ.SuccinctSpace.FixedWidthRankSampleTables.payload
attribute [local simp] RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankBlockOverhead
attribute [local simp] RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankSuperOverhead
attribute [local simp] RMQ.GenericSelect.sparseExceptionSelectData
attribute [local simp] RMQ.SuccinctSpace.BoundedPayloadWordStore.ofChunks
attribute [local simp] RMQ.GenericSelect.sparseExceptionDirectory
attribute [local simp] RMQ.GenericSelect.sparseExceptionRelativeTable
attribute [local simp] RMQ.GenericSelect.sparseExceptionRelativeWidth
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveFlagRankData
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveFlagRankBlockWidth
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveFlagRankWordSize
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveFlagBits
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveLocalSlotCount
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveFlagRankBlockOverhead
attribute [local simp] RMQ.GenericSelect.sparseExceptionEffectiveFlagRankSuperOverhead
attribute [local simp] RMQ.GenericSelect.localTable
attribute [local simp] RMQ.GenericSelect.localFieldWidth
attribute [local simp] RMQ.GenericSelect.localEntries
attribute [local simp] RMQ.GenericSelect.localEntry
attribute [local simp] RMQ.GenericSelect.compactLocalEntryIsLive
attribute [local simp] RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.ofEntries
attribute [local simp] RMQ.GenericSelect.longSuperRelativeTable
attribute [local simp] RMQ.GenericSelect.longSuperRelativeWidth
attribute [local simp] RMQ.GenericSelect.longSuperRelativeEntries
attribute [local simp] RMQ.GenericSelect.longSuperRelativeEntriesForSlot
attribute [local simp] RMQ.GenericSelect.superTable
attribute [local simp] RMQ.GenericSelect.superFieldWidth
attribute [local simp] RMQ.GenericSelect.superEntries
attribute [local simp] RMQ.GenericSelect.superEntry
attribute [local simp] RMQ.GenericSelect.longFlagRankData
attribute [local simp] RMQ.GenericSelect.longFlagRankBlockWidth
attribute [local simp] RMQ.GenericSelect.longFlagRankWordSize
attribute [local simp] RMQ.GenericSelect.longFlagRankBlocksPerSuper
attribute [local simp] RMQ.GenericSelect.longFlagRankBlockOverhead
attribute [local simp] RMQ.GenericSelect.longFlagRankSuperOverhead
attribute [local simp] RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout.payload
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerHeaderBits
attribute [local simp] RMQ.SuccinctClassic.cartesianShape
attribute [local simp] RMQ.Cartesian.shape
attribute [local simp] RMQ.Cartesian.shapeRange
attribute [local simp] RMQ.scanWindow
attribute [local simp] RMQ.betterIndex
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRunAgainstMemory
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerControllerMeasure
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLogicalPlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLegacyRawPlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedSourceReadPlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSourceReadWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedStridedBitAddress
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedSourceOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedAccessOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedSparseRankSuperPrefixLength
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerProbePlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPRawPlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPReadWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSourceReadWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPBitAddress
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLegacyWordCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSourceWordCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSegmentSource?
attribute [local simp] RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentSource?
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectChunkWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedSelectChunkAddress
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedSelectChunkOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedFringeOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedInteriorOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedAccessLength
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectChunkCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerFringeWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedFringeAddress
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerFringeCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerLogicalRequest.index
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedInteriorReadPlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedInteriorLocationPlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerInteriorLocation.readWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerClosedInteriorBitAddress
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerInteriorLocation.bitOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerInteriorLocation.componentBitPrefix
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorClassify
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorComponentWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedGlobalLevelWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorLayout
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSummaryBlockSizeRaw
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorTableWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLocalLevelWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedGlobalTableWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLocalTableWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedArgOffsetWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedMaxRelWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedMinRelWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedBaselineWords
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorLocation
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedEntryChunkReadWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedEntryChunkBitOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorComponentBitPrefix
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorEntryWidth
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorEntryCount
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedInteriorOffsets
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerLogicalRequest.segment
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRankNextRequest
attribute [local simp] RMQ.SuccinctClose.bpWordChunkSliceLen
attribute [local simp] RMQ.SuccinctClose.bpFringeWindowChunkValue
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkSlot
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedFringeChunkBits
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRankKind.wordSegment
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRankKind.superSegment
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRankKind.blockSegment
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRankKind.blocksPerSuper
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRankKind.wordSize
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRankQueryPos
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRankKind.bitLength
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerCandidate
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNatNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerFringeNextRequest
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkEndOff
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkStartOff
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPWindowNextRequest
attribute [local simp] RMQ.SuccinctClose.blockOfClose
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWordSelectNextRequest
attribute [local simp] RMQ.SuccinctClose.bpChunkSelectSlot
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSelectWordSize
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerEntryNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerEntryKind.segmentBase
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerCurrentPreludePlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeRequestPlan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerSparsePreludeRequest.index
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeWordIndex
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerSparsePreludeRequest.source
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeRequestBitAddress
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerSparsePreludeRequest.sourceOffset
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparseRankSuperPrefixLength
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSelectSuperStride
attribute [local simp] RMQ.GenericSelect.selectSuperSlot
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRankRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNatContinuationRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerCandidateContinuationRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNatRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerFringeRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPWindowRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWordSelectRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerEntryRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeInit
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeRemaining
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerDriveAgainstMemoryAux
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRun.trace
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRun.state
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRun.failed
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRun.terminal
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerNormalizeWhole
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLogicalDecode
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLegacyDecode
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerDecodeSpan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRankResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRankConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerRankKind.target
attribute [local simp] RMQ.SuccinctClose.bpWordRankStepDecoded
attribute [local simp] RMQ.SuccinctClose.bpChunkRankOfEntry
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerRankStartFold
attribute [local simp] RMQ.SuccinctClose.bpWordChunkCount
attribute [local simp] RMQ.SuccinctClose.bpWordRankEffLimit
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerDecodeNat
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeAfterLca
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaConsumeReply
attribute [local simp] RMQ.SuccinctClose.bpCandidateClose?
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartRightFringe
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerFringeStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedLocalBPWindowBase
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartRightWindow
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPWindowStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaSeed
attribute [local simp] RMQ.SuccinctClose.localBPSeedFromRankFalse
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartRightSeed
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaRankStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNormalize
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorFinishNat
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorStartGlobalSpan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorReadNat
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNatStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorStartLocalSpan
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorStartMinCandidate
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorFinishCandidate
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorStartGlobalTwo
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorStartLocalTwo
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerCandidateContinuation._sizeOf_inst
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerCandidateContinuation._sizeOf_1
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNatResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorNatConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartMiddle
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerInteriorStartRaw
attribute [local simp] RMQ.SuccinctClose.bpFringeCandGlobal
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartLeftFringe
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartLeftWindow
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaFinishSameFringe
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerFringeResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerFringeConsumeReply
attribute [local simp] RMQ.SuccinctClose.bpFringeChunkStepDecoded
attribute [local simp] RMQ.SuccinctClose.bpFringeMergeCand
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartSameFringe
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPWindowResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerBPWindowConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStartSameWindow
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeAfterRightSelect
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerLcaStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeAfterLeftSelect
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterDenseSecondWord
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWordSelectResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWordSelectStart
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWordSelectConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterDenseUptoRank
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterDenseBeforeRank
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterDenseFirstWord
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterSparseRank
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSelectLocalStride
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectLocalBaseOccurrence
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectSparseCompactSlot
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectLocalBasePosition
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterLongRank
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectLongCompactSlot
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectEntryBasePosition
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterLocal
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectEntryIsMarked
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSelectAfterSuper
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedSelectLocalSlotsPerSuper
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectLocalSlot
attribute [local simp] RMQ.GenericSelect.relativeSplitSelectLocalSlotInSuper
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerEntryResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerEntryConsumeReply
attribute [local simp] RMQ.GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerWholeResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeConsumeReply
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparseCountFromReplies
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeWordOffset
attribute [local simp] RMQ.RAM.boolRankPrefix
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerDecodePreludeReplies
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerNormalizePrelude
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparsePreludeResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerPhysicalRequest.address
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerNextRequest
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerControllerFailed
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerControllerResult
attribute [local simp] RMQ.SuccinctFinal.PackedCellProbe.packedReviewerController
theorem egcpShapePin : SuccinctClassic.cartesianShape [7, 3, 3] = egcpShapeLit := by
  simp +decide [egcpShapeLit]

theorem egcpSizePin : egcpShapeLit.size = 3 := by decide

attribute [local simp] egcpSizePin

theorem egcpBpCodePin : egcpShapeLit.bpCode = [true, true, false, false, true, false] := by decide

attribute [local simp] egcpBpCodePin

theorem egcpLongCountPin : longCount egcpShapeLit = 0 := by
  simp +decide

attribute [local simp] egcpLongCountPin

theorem egcpSparseCountPin : packedReviewerSparseCount egcpShapeLit = 0 := by
  simp +decide

attribute [local simp] egcpSparseCountPin

theorem egcpWidthPin : packedReviewerCellWidth 3 = 15 := by
  simp +decide

attribute [local simp] egcpWidthPin

theorem egcpChunkBitsPin : SuccinctClose.bpFringeChunkBits 6 = 1 := by
  simp +decide

attribute [local simp] egcpChunkBitsPin

theorem egcpCellCountPin : packedReviewerCellCount 3 0 0 = 22 := by
  simp +decide

attribute [local simp] egcpCellCountPin

theorem egcpAllocPin : packedReviewerAllocatedBits 3 0 0 = 330 := by
  simp +decide

attribute [local simp] egcpAllocPin

theorem egcpMeasurePin :
    packedReviewerControllerMeasure (packedReviewerController 3 0 3) = 427 := by
  simp +decide

attribute [local simp] egcpMeasurePin

/-! ### Payload components: fringe and select chunk tables (kernel route) -/

theorem egcpFringeWidthPin : SuccinctClose.bpFringeChunkEntryWidth 1 = 5 := by
  simp [SuccinctClose.bpFringeChunkEntryWidth, SuccinctClose.bpFringeChunkEntryBound]

theorem egcpFringePin : (SuccinctClose.bpFringeChunkTable 1).payload = egcpFringeLit := by
  simp only [SuccinctClose.bpFringeChunkTable, SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords, egcpFringeWidthPin]
  decide

attribute [local simp] egcpFringePin

theorem egcpSelectWidthPin : SuccinctClose.bpChunkSelectEntryWidth 1 = 2 := by
  simp [SuccinctClose.bpChunkSelectEntryWidth]

theorem egcpSelectPin :
    (SuccinctClose.bpChunkSelectTable 1 false).payload = egcpSelectLit := by
  simp only [SuccinctClose.bpChunkSelectTable, SuccinctSpace.FixedWidthNatTable.ofEntries,
    SuccinctSpace.FixedWidthNatTable.ofEncodedWords, egcpSelectWidthPin]
  decide

attribute [local simp] egcpSelectPin

/-! ### Payload component: the live-access flatMap -/

theorem egcpAccessPin :
    concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload egcpShapeLit =
      egcpAccessLit := by
  simp +decide [egcpAccessLit, List.range_succ, Function.comp]

attribute [local simp] egcpAccessPin

/-! ### Payload component: the interior close directory, one table at a time -/

theorem egcpSummaryPin :
    SuccinctClose.PayloadLiveBPRelativeMinMaxArgSummaryTable.payload
      (SuccinctClose.canonicalRelativeRmmSummaryTable egcpShapeLit) = [false, false, false, false, false, false, true, false, false, false, false, true, false, true, false, false, false, false, false, false, false, false, false, false] := by
  simp +decide [List.range_succ, Function.comp]

attribute [local simp] egcpSummaryPin

theorem egcpLocalTablePin :
    SuccinctClose.PayloadLiveBPLocalSparseOffsetTable.payload
      (SuccinctClose.canonicalRelativeRmmInteriorLocalTable egcpShapeLit) = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  simp +decide [List.range_succ, Function.comp]

attribute [local simp] egcpLocalTablePin

theorem egcpGlobalTablePin :
    SuccinctClose.PayloadLiveBPGlobalSparseBlockTable.payload
      (SuccinctClose.canonicalRelativeRmmInteriorGlobalTable egcpShapeLit) = [false] := by
  simp +decide [List.range_succ, Function.comp]

attribute [local simp] egcpGlobalTablePin

theorem egcpLocalLevelPin :
    (SuccinctClose.canonicalRelativeRmmInteriorLocalLevelTable egcpShapeLit).payload = [true, false, false, false, false, true, false, false, false, false, false, false, false, true, false, false, false, false, true, false, false, false, false, false, true, false, false, false, false, true] := by
  simp +decide [List.range_succ, Function.comp]

attribute [local simp] egcpLocalLevelPin

theorem egcpGlobalLevelPin :
    (SuccinctClose.canonicalRelativeRmmInteriorGlobalLevelTable egcpShapeLit).payload = [true, false, false, true, false, false, true, false, true] := by
  simp +decide [List.range_succ, Function.comp]

attribute [local simp] egcpGlobalLevelPin

theorem egcpClosePin :
    (SuccinctClose.canonicalRelativeRmmInteriorDirectory egcpShapeLit).payload =
      egcpCloseLit := by
  simp only [SuccinctClose.canonicalRelativeRmmInteriorDirectory,
    egcpSummaryPin, egcpLocalTablePin, egcpGlobalTablePin,
    egcpLocalLevelPin, egcpGlobalLevelPin]
  decide

attribute [local simp] egcpClosePin

/-! ### Payload, header, serialized-and-padded bits -/

theorem egcpPayloadPin : packedReviewerPayloadBits egcpShapeLit = egcpPayloadLit := by
  have h6 : SuccinctClose.bpFringeChunkBits egcpShapeLit.bpCode.length = 1 := by
    simp
  simp only [packedReviewerPayloadBits,
    concreteBPNativeSuccinctRMQCanonicalReviewerPayload,
    concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout,
    egcpAccessPin, egcpClosePin]
  rw [h6]
  simp only [egcpFringePin, egcpSelectPin, egcpBpCodePin]
  decide

attribute [local simp] egcpPayloadPin

theorem egcpHeaderPin : packedReviewerHeaderBits egcpShapeLit = [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false] := by
  simp +decide

attribute [local simp] egcpHeaderPin

theorem egcpPaddedPin : packedReviewerPaddedBits egcpShapeLit = egcpPaddedLit := by
  simp only [packedReviewerPaddedBits, packedReviewerSerializedBits,
    egcpSizePin, egcpLongCountPin, egcpSparseCountPin, egcpAllocPin,
    egcpHeaderPin, egcpPayloadPin]
  decide

attribute [local simp] egcpPaddedPin

/-! ### Deliverable 1: the packed reviewer memory, as a 22-cell width-15 literal -/

theorem egcpFixtureMemLit :
    packedReviewerMemory (RMQ.SuccinctClassic.cartesianShape [7, 3, 3]) = egcpMemLit := by
  simp only [egcpShapePin, packedReviewerMemory, egcpSizePin, egcpLongCountPin,
    egcpSparseCountPin, egcpCellCountPin, egcpWidthPin, egcpPaddedPin]
  decide

/-! ### Deliverable 3: terminal value of the canonical run -/

theorem egcpFixtureTerminal :
    (packedReviewerRunAgainstMemory egcpMemLit 3 0 3).terminal = some (some 1) := by
  simp +decide [egcpMemLit]

/-! ### Deliverable 2: the 68 attempted cell addresses, in order -/

theorem egcpFixtureTraceAddresses :
    (packedReviewerRunAgainstMemory egcpMemLit 3 0 3).trace.map
      (fun event => event.request.address) = [0, 10, 11, 11, 2, 2, 2, 3, 3, 5, 6, 8, 1, 20, 20, 20, 20, 19, 20, 20, 19, 20, 2, 2, 2, 3, 3, 5, 7, 9, 1, 19, 20, 19, 20, 19, 19, 20, 19, 20, 1, 1, 1, 19, 1, 1, 20, 20, 19, 18, 19, 20, 1, 1, 2, 1, 18, 1, 19, 19, 20, 18, 18, 1, 1, 2, 1, 19] := by
  simp +decide [egcpMemLit]

/--
The frozen `SF-FG11-HEADER` fixture instance.  On `[7, 3, 3]` with query
`(0, 3)`, replacing only header cell `0` by the commissioned same-width
`longCount + w(n)` encoding moves the second attempted physical address
from the concrete canonical cell `10` to the concrete mutated cell `37`.
-/
theorem packedReviewerHeaderCellAddressLiveness_fixture :
    ((packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace.map
          (fun event => event.request.address))[1]? = some 10 /\
      ((packedReviewerRunAgainstMemory
          ((packedReviewerMemory
              (SuccinctClassic.cartesianShape [7, 3, 3])).set 0
            (SuccinctSpace.natToBitsLE
              (packedReviewerCellWidth
                (SuccinctClassic.cartesianShape [7, 3, 3]).size)
              (longCount (SuccinctClassic.cartesianShape [7, 3, 3]) +
                packedReviewerCellWidth
                  (SuccinctClassic.cartesianShape [7, 3, 3]).size)))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace.map
            (fun event => event.request.address))[1]? = some 37 /\
      (10 : Nat) ≠ 37 := by
  have hright :
      3 <= (SuccinctClassic.cartesianShape [7, 3, 3]).size := by
    rw [egcpShapePin, egcpSizePin]
    omega
  have hcanonicalAddress :
      packedReviewerSparsePreludeRequestBitAddress
          (SuccinctClassic.cartesianShape [7, 3, 3]).size
          (longCount (SuccinctClassic.cartesianShape [7, 3, 3])) .rankSuper /
        packedReviewerCellWidth
          (SuccinctClassic.cartesianShape [7, 3, 3]).size = 10 := by
    rw [egcpShapePin, egcpSizePin, egcpLongCountPin, egcpWidthPin]
    simp +decide
  have hmutatedAddress :
      packedReviewerSparsePreludeRequestBitAddress
          (SuccinctClassic.cartesianShape [7, 3, 3]).size
          (longCount (SuccinctClassic.cartesianShape [7, 3, 3]) +
            packedReviewerCellWidth
              (SuccinctClassic.cartesianShape [7, 3, 3]).size) .rankSuper /
        packedReviewerCellWidth
          (SuccinctClassic.cartesianShape [7, 3, 3]).size = 37 := by
    rw [egcpShapePin, egcpSizePin, egcpLongCountPin, egcpWidthPin]
    simp +decide
  have hexact := packedReviewerHeaderCellAddressLiveness_exact
    (SuccinctClassic.cartesianShape [7, 3, 3]) 0 3 (by decide) hright
  rw [hcanonicalAddress, hmutatedAddress] at hexact
  exact hexact

/-! ### Deliverable 5: the decisive cell 8 is genuinely probed -/

theorem egcpFixtureDecisiveEvent :
    ∃ i : Nat, ((packedReviewerRunAgainstMemory egcpMemLit 3 0 3).trace.map
      (fun event => event.request.address))[i]? = some 8 := by
  rw [egcpFixtureTraceAddresses]
  exact ⟨11, by decide⟩

/-! ### Deliverable 4: complementing cell 8 flips the terminal answer to 2 -/

theorem egcpFixtureDecisiveMutantTerminal :
    (packedReviewerRunAgainstMemory (egcpMemLit.set 8 egcpDecisiveMutantCell) 3 0 3).terminal =
      some (some 2) := by
  simp +decide [egcpMemLit, egcpDecisiveMutantCell]

/-- The decisive probe itself, as one literal event: position `11` of the
canonical trace reads cell `8` for the `leftSelect` instruction's
`entryFirstOffset` site at segment `8`, and receives the decisive cell. -/
theorem egcpFixtureEvent11 :
    (packedReviewerRunAgainstMemory egcpMemLit 3 0 3).trace[11]? =
      some
        { request :=
            { origin :=
                PackedReviewerPhysicalOrigin.wholeQuery
                  { invocation :=
                      { instruction :=
                          PackedReviewerInstructionSite.leftSelect
                        argument := 0
                        argument2 := 0 }
                    site := PackedReviewerReadSite.entryFirstOffset
                    segment := 8
                    index := 0 }
              address := 8
              ordinal := 0
              cellCount := 1 }
          reply :=
            some
              [false, false, false, false, false, false, false, false, false,
                false, true, false, false, false, false] } := by
  simp +decide [egcpMemLit]

end EGCPFixtureEvaluation

/-! ## The checked driver prefix decomposition

`R1` requires the decisive occurrence's provenance to survive in a theorem
conclusion: the exact producing request, the controller pre-state, the
`nextRequest`/`consumeReply` transition, and a checked continuation to the
run's terminal.  The pre-state is pinned as the driver prefix fold
`packedReviewerDriveStateAt`: one `packedReviewerDriveStep` per emitted
event, each step performing exactly the driver's own transition -- consult
the controller, perform the single memory lookup, consume the reply.  The
decomposition theorem below proves this fold IS the driver's state at every
trace position, so no separately invented state can inhabit the conclusion.
-/

/-- One driver step: terminal and request-less states are fixed points;
otherwise perform the driver's single memory lookup and consume the reply. -/
def packedReviewerDriveStep (memory : List (List Bool))
    (state : PackedReviewerControllerState) : PackedReviewerControllerState :=
  match packedReviewerControllerResult state with
  | some _ => state
  | none =>
      match packedReviewerNextRequest state with
      | none => state
      | some request =>
          packedReviewerConsumeReply state (memory[request.address]?)

/-- The controller state after `i` driver steps: the checked prefix fold. -/
def packedReviewerDriveStateAt (memory : List (List Bool))
    (state : PackedReviewerControllerState) :
    Nat -> PackedReviewerControllerState
  | 0 => state
  | i + 1 =>
      packedReviewerDriveStep memory (packedReviewerDriveStateAt memory state i)

/-- The prefix fold shifts across its first step. -/
theorem packedReviewerDriveStateAt_shift
    (memory : List (List Bool)) (state : PackedReviewerControllerState) :
    forall i : Nat,
      packedReviewerDriveStateAt memory state (i + 1) =
        packedReviewerDriveStateAt memory
          (packedReviewerDriveStep memory state) i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      show packedReviewerDriveStep memory
          (packedReviewerDriveStateAt memory state (i + 1)) = _
      rw [ih]
      rfl

/-- One live driver step, unfolded: the head event is the computed request
with the driver's own memory lookup, and every projection continues from the
consumed successor state. -/
theorem packedReviewerDriveAux_succ_of_request
    (memory : List (List Bool)) (fuel : Nat)
    (state : PackedReviewerControllerState)
    {request : PackedReviewerPhysicalRequest}
    (hres : packedReviewerControllerResult state = none)
    (hreq : packedReviewerNextRequest state = some request) :
    packedReviewerDriveAgainstMemoryAux memory (fuel + 1) state =
      { terminal :=
          (packedReviewerDriveAgainstMemoryAux memory fuel
            (packedReviewerConsumeReply state
              (memory[request.address]?))).terminal
        failed :=
          (packedReviewerDriveAgainstMemoryAux memory fuel
            (packedReviewerConsumeReply state
              (memory[request.address]?))).failed
        state :=
          (packedReviewerDriveAgainstMemoryAux memory fuel
            (packedReviewerConsumeReply state
              (memory[request.address]?))).state
        trace :=
          { request := request, reply := memory[request.address]? } ::
            (packedReviewerDriveAgainstMemoryAux memory fuel
              (packedReviewerConsumeReply state
                (memory[request.address]?))).trace } := by
  simp [packedReviewerDriveAgainstMemoryAux, hres, hreq]

/-- On a live step the prefix fold advances by exactly the driver's consume. -/
theorem packedReviewerDriveStep_of_request
    (memory : List (List Bool)) (state : PackedReviewerControllerState)
    {request : PackedReviewerPhysicalRequest}
    (hres : packedReviewerControllerResult state = none)
    (hreq : packedReviewerNextRequest state = some request) :
    packedReviewerDriveStep memory state =
      packedReviewerConsumeReply state (memory[request.address]?) := by
  simp [packedReviewerDriveStep, hres, hreq]

/--
**The driver decomposition.**  At every position of the driver's trace, the
prefix fold is live (`result = none`), it computes the emitted request, the
recorded event is exactly that request with the driver's own memory lookup,
and the drive restarted at the fold with the remaining fuel reproduces the
whole run's terminal, state, and trace suffix.
-/
theorem packedReviewerDriveAux_decompose (memory : List (List Bool)) :
    forall (i fuel : Nat) (state : PackedReviewerControllerState),
      i < (packedReviewerDriveAgainstMemoryAux memory fuel state).trace.length ->
        packedReviewerControllerResult
            (packedReviewerDriveStateAt memory state i) = none /\
          (exists request,
            packedReviewerNextRequest
                (packedReviewerDriveStateAt memory state i) = some request /\
              (packedReviewerDriveAgainstMemoryAux memory fuel
                  state).trace[i]? =
                some { request := request
                       reply := memory[request.address]? }) /\
          (packedReviewerDriveAgainstMemoryAux memory (fuel - i)
              (packedReviewerDriveStateAt memory state i)).terminal =
            (packedReviewerDriveAgainstMemoryAux memory fuel state).terminal /\
          (packedReviewerDriveAgainstMemoryAux memory (fuel - i)
              (packedReviewerDriveStateAt memory state i)).state =
            (packedReviewerDriveAgainstMemoryAux memory fuel state).state /\
          (packedReviewerDriveAgainstMemoryAux memory (fuel - i)
              (packedReviewerDriveStateAt memory state i)).trace =
            (packedReviewerDriveAgainstMemoryAux memory fuel state).trace.drop
              i := by
  intro i
  induction i with
  | zero =>
      intro fuel state hlt
      match fuel with
      | 0 => simp [packedReviewerDriveAgainstMemoryAux] at hlt
      | fuel + 1 =>
          cases hres : packedReviewerControllerResult state with
          | some value =>
              rw [show (packedReviewerDriveAgainstMemoryAux memory (fuel + 1)
                  state).trace = [] by
                simp [packedReviewerDriveAgainstMemoryAux, hres]] at hlt
              simp at hlt
          | none =>
              cases hreq : packedReviewerNextRequest state with
              | none =>
                  rw [show (packedReviewerDriveAgainstMemoryAux memory
                      (fuel + 1) state).trace = [] by
                    simp [packedReviewerDriveAgainstMemoryAux, hres,
                      hreq]] at hlt
                  simp at hlt
              | some request =>
                  have hstepEq := packedReviewerDriveAux_succ_of_request
                    memory fuel state hres hreq
                  refine ⟨hres, ⟨request, hreq, ?_⟩, ?_, ?_, ?_⟩
                  · rw [hstepEq]
                    rfl
                  · rfl
                  · rfl
                  · rfl
  | succ i ih =>
      intro fuel state hlt
      match fuel with
      | 0 => simp [packedReviewerDriveAgainstMemoryAux] at hlt
      | fuel + 1 =>
          cases hres : packedReviewerControllerResult state with
          | some value =>
              rw [show (packedReviewerDriveAgainstMemoryAux memory (fuel + 1)
                  state).trace = [] by
                simp [packedReviewerDriveAgainstMemoryAux, hres]] at hlt
              simp at hlt
          | none =>
              cases hreq : packedReviewerNextRequest state with
              | none =>
                  rw [show (packedReviewerDriveAgainstMemoryAux memory
                      (fuel + 1) state).trace = [] by
                    simp [packedReviewerDriveAgainstMemoryAux, hres,
                      hreq]] at hlt
                  simp at hlt
              | some request =>
                  have hstepEq := packedReviewerDriveAux_succ_of_request
                    memory fuel state hres hreq
                  have hstep := packedReviewerDriveStep_of_request
                    memory state hres hreq
                  have hlt' :
                      i < (packedReviewerDriveAgainstMemoryAux memory fuel
                        (packedReviewerConsumeReply state
                          (memory[request.address]?))).trace.length := by
                    rw [hstepEq] at hlt
                    simpa using hlt
                  have htail := ih fuel
                    (packedReviewerConsumeReply state
                      (memory[request.address]?)) hlt'
                  have hshift :
                      packedReviewerDriveStateAt memory state (i + 1) =
                        packedReviewerDriveStateAt memory
                          (packedReviewerConsumeReply state
                            (memory[request.address]?)) i := by
                    rw [packedReviewerDriveStateAt_shift, hstep]
                  rw [hshift, Nat.succ_sub_succ]
                  obtain ⟨htailRes, ⟨tailRequest, htailReq, htailAt⟩,
                    htailTerm, htailState, htailTrace⟩ := htail
                  refine ⟨htailRes, ⟨tailRequest, htailReq, ?_⟩, ?_, ?_, ?_⟩
                  · rw [hstepEq]
                    simpa using htailAt
                  · rw [htailTerm, hstepEq]
                  · rw [htailState, hstepEq]
                  · rw [htailTrace, hstepEq]
                    rfl

/-! ## `FG-11` at the pinned fixture: value liveness, unread accept, bridge

The theorems below are stated over the real public objects --
`packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3])` and the
literal driver -- and are transported to the kernel-checked literal
evaluation through `egcpFixtureMemLit`.
-/

section EGCPStageFFixture

set_option maxRecDepth 8192

/-- The fixture shape's size, through the shape literal. -/
theorem egcpFixtureShapeSize :
    (SuccinctClassic.cartesianShape [7, 3, 3]).size = 3 := by
  rw [egcpShapePin]
  exact egcpSizePin

/--
The frozen committed replacement value for the proved-unread allocated cell
`4`.  Replay case `A02-UNREAD-CELL-EXPECTED-ACCEPT` patches exactly this
definition; the pinned run/result theorems below must keep elaborating,
because the unread-cell equality is proved through the ordered agreement
route and never inspects this value.
-/
def egcpStageFUnreadReplacementCell : List Bool :=
  List.replicate (packedReviewerCellWidth 3) true

/--
**`FG-11` decisive payload liveness.**  Mutating only consumed cell `8` of
the identical reviewer memory changes the packed run's returned answer from
`some 1` to `some 2`.  The inequality is at the `.terminal` projection of
the two runs, both proper terminal values, and the canonical side is the
guarded leftmost reference result.
-/
theorem packedReviewerDecisiveCellLiveness :
    (packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
          some (some 1) /\
      (packedReviewerRunAgainstMemory
          ((packedReviewerMemory
              (SuccinctClassic.cartesianShape [7, 3, 3])).set 8
            egcpDecisiveMutantCell)
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
        some (some 2) /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal ≠
        (packedReviewerRunAgainstMemory
            ((packedReviewerMemory
                (SuccinctClassic.cartesianShape [7, 3, 3])).set 8
              egcpDecisiveMutantCell)
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal := by
  rw [egcpFixtureShapeSize, egcpFixtureMemLit]
  refine ⟨egcpFixtureTerminal, egcpFixtureDecisiveMutantTerminal, ?_⟩
  rw [egcpFixtureTerminal, egcpFixtureDecisiveMutantTerminal]
  simp

/--
**The decisive occurrence chain (`R1`-strengthened).**  The conclusion
itself retains, on the identical canonical fixture objects: the global
trace position and event; the exact producing whole-query request, field by
field (`leftSelect` instruction with both arguments `0`, the
`entryFirstOffset` read site, segment `8`, index `0`); the physical address
`8`; the successful reply cell, which is the driver's own memory lookup;
the exact controller pre-state as the checked driver prefix fold
`packedReviewerDriveStateAt` at that position; the
`packedReviewerNextRequest`/`packedReviewerConsumeReply` transition through
that event; and a checked continuation from the post-state, with the
remaining structural fuel, to the same run's `.done (some 1)` state and
terminal -- the guarded leftmost reference result of the fixture.  Nothing
is erased into an unnamed existential: every component the frozen `R1`
contract lists is a conjunct below, and the prefix fold is proved equal to
the driver's own state at that position by
`packedReviewerDriveAux_decompose`, so no separately invented pre-state can
inhabit this type.
-/
theorem packedReviewerDecisiveCellConnection :
    exists (position : Nat) (event : PackedReviewerPhysicalEvent)
      (request : PackedReviewerLogicalRequest) (replyCell : List Bool)
      (preState postState : PackedReviewerControllerState),
      ((packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace)[position]? =
          some event /\
      position = 11 /\
      event.request.origin = PackedReviewerPhysicalOrigin.wholeQuery request /\
      request.invocation.instruction =
        PackedReviewerInstructionSite.leftSelect /\
      request.invocation.argument = 0 /\
      request.invocation.argument2 = 0 /\
      request.site = PackedReviewerReadSite.entryFirstOffset /\
      request.segment = 8 /\
      request.index = 0 /\
      event.request.address = 8 /\
      event.reply = some replyCell /\
      event.reply =
        (packedReviewerMemory
          (SuccinctClassic.cartesianShape [7, 3, 3]))[event.request.address]? /\
      preState =
        packedReviewerDriveStateAt
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (packedReviewerController
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3)
          position /\
      packedReviewerNextRequest preState = some event.request /\
      packedReviewerConsumeReply preState event.reply = postState /\
      (packedReviewerDriveAgainstMemoryAux
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (packedReviewerControllerMeasure
              (packedReviewerController
                (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) -
            (position + 1))
          postState).terminal = some (some 1) /\
      (packedReviewerDriveAgainstMemoryAux
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (packedReviewerControllerMeasure
              (packedReviewerController
                (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) -
            (position + 1))
          postState).state = .done (some 1) /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
        some (some 1) /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).state =
        .done (some 1) /\
      (SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value = some 1 := by
  have hterminalRun :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
        some (some 1) := packedReviewerDecisiveCellLiveness.1
  have hstateRun :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).state =
        .done (some 1) := by
    have hcapstone := packedReviewerStageFCapstone_holds [7, 3, 3] 0 3
    have hstateEq := hcapstone.guarded_reference_result.2.2
    rw [packedReviewerStageFDuplicateMinReference] at hstateEq
    exact hstateEq
  rw [egcpFixtureShapeSize, egcpFixtureMemLit] at hterminalRun hstateRun ⊢
  have hlen :
      (packedReviewerRunAgainstMemory egcpMemLit 3 0 3).trace.length = 68 := by
    have hmap := congrArg List.length egcpFixtureTraceAddresses
    simpa using hmap
  have hlt :
      11 < (packedReviewerDriveAgainstMemoryAux egcpMemLit
        (packedReviewerControllerMeasure (packedReviewerController 3 0 3))
        (packedReviewerController 3 0 3)).trace.length := by
    show 11 < (packedReviewerRunAgainstMemory egcpMemLit 3 0 3).trace.length
    omega
  obtain ⟨hres, ⟨request, hreq, hat⟩, hterm, hstate, _htrace⟩ :=
    packedReviewerDriveAux_decompose egcpMemLit 11
      (packedReviewerControllerMeasure (packedReviewerController 3 0 3))
      (packedReviewerController 3 0 3) hlt
  have hat' :
      (packedReviewerRunAgainstMemory egcpMemLit 3 0 3).trace[11]? =
        some { request := request, reply := egcpMemLit[request.address]? } :=
    hat
  rw [egcpFixtureEvent11] at hat'
  have hevent := Option.some.inj hat'
  have hrequestEq :
      request =
        { origin :=
            PackedReviewerPhysicalOrigin.wholeQuery
              { invocation :=
                  { instruction := PackedReviewerInstructionSite.leftSelect
                    argument := 0
                    argument2 := 0 }
                site := PackedReviewerReadSite.entryFirstOffset
                segment := 8
                index := 0 }
          address := 8
          ordinal := 0
          cellCount := 1 } :=
    (congrArg PackedReviewerPhysicalEvent.request hevent).symm
  have hreplyEq :
      egcpMemLit[request.address]? =
        some
          [false, false, false, false, false, false, false, false, false,
            false, true, false, false, false, false] :=
    (congrArg PackedReviewerPhysicalEvent.reply hevent).symm
  have hfuelSplit :
      packedReviewerControllerMeasure (packedReviewerController 3 0 3) - 11 =
        (packedReviewerControllerMeasure (packedReviewerController 3 0 3) -
          12) + 1 := by
    rw [egcpMeasurePin]
  have hstepEq := packedReviewerDriveAux_succ_of_request egcpMemLit
    (packedReviewerControllerMeasure (packedReviewerController 3 0 3) - 12)
    (packedReviewerDriveStateAt egcpMemLit
      (packedReviewerController 3 0 3) 11)
    hres hreq
  have hcontTerm :
      (packedReviewerDriveAgainstMemoryAux egcpMemLit
          (packedReviewerControllerMeasure
            (packedReviewerController 3 0 3) - 12)
          (packedReviewerConsumeReply
            (packedReviewerDriveStateAt egcpMemLit
              (packedReviewerController 3 0 3) 11)
            (egcpMemLit[request.address]?))).terminal = some (some 1) := by
    have hbridge :
        (packedReviewerDriveAgainstMemoryAux egcpMemLit
            (packedReviewerControllerMeasure
              (packedReviewerController 3 0 3) - 12)
            (packedReviewerConsumeReply
              (packedReviewerDriveStateAt egcpMemLit
                (packedReviewerController 3 0 3) 11)
              (egcpMemLit[request.address]?))).terminal =
          (packedReviewerDriveAgainstMemoryAux egcpMemLit
            (packedReviewerControllerMeasure
              (packedReviewerController 3 0 3))
            (packedReviewerController 3 0 3)).terminal := by
      have h1 := hterm
      rw [hfuelSplit, hstepEq] at h1
      exact h1
    rw [hbridge]
    exact hterminalRun
  have hcontState :
      (packedReviewerDriveAgainstMemoryAux egcpMemLit
          (packedReviewerControllerMeasure
            (packedReviewerController 3 0 3) - 12)
          (packedReviewerConsumeReply
            (packedReviewerDriveStateAt egcpMemLit
              (packedReviewerController 3 0 3) 11)
            (egcpMemLit[request.address]?))).state = .done (some 1) := by
    have hbridge :
        (packedReviewerDriveAgainstMemoryAux egcpMemLit
            (packedReviewerControllerMeasure
              (packedReviewerController 3 0 3) - 12)
            (packedReviewerConsumeReply
              (packedReviewerDriveStateAt egcpMemLit
                (packedReviewerController 3 0 3) 11)
              (egcpMemLit[request.address]?))).state =
          (packedReviewerDriveAgainstMemoryAux egcpMemLit
            (packedReviewerControllerMeasure
              (packedReviewerController 3 0 3))
            (packedReviewerController 3 0 3)).state := by
      have h1 := hstate
      rw [hfuelSplit, hstepEq] at h1
      exact h1
    rw [hbridge]
    exact hstateRun
  refine ⟨11,
    { request := request, reply := egcpMemLit[request.address]? },
    { invocation :=
        { instruction := PackedReviewerInstructionSite.leftSelect
          argument := 0
          argument2 := 0 }
      site := PackedReviewerReadSite.entryFirstOffset
      segment := 8
      index := 0 },
    [false, false, false, false, false, false, false, false, false,
      false, true, false, false, false, false],
    packedReviewerDriveStateAt egcpMemLit
      (packedReviewerController 3 0 3) 11,
    packedReviewerConsumeReply
      (packedReviewerDriveStateAt egcpMemLit
        (packedReviewerController 3 0 3) 11)
      (egcpMemLit[request.address]?),
    hat, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, hreq,
    rfl, hcontTerm, hcontState, hterminalRun, hstateRun,
    packedReviewerStageFDuplicateMinReference⟩
  · show request.origin = _
    rw [hrequestEq]
  · show request.address = 8
    rw [hrequestEq]
  · show egcpMemLit[request.address]? = some _
    rw [hreplyEq]

/-- No canonical-trace event addresses cell `4`: transported from the
literal 68-address trace. -/
theorem packedReviewerFixtureCellFourUnread :
    forall event,
      event ∈ (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace ->
        event.request.address ≠ 4 := by
  rw [egcpFixtureShapeSize, egcpFixtureMemLit]
  intro event hmem heq
  have hmap :
      event.request.address ∈
        (packedReviewerRunAgainstMemory egcpMemLit 3 0 3).trace.map
          (fun event => event.request.address) :=
    List.mem_map_of_mem hmem
  rw [egcpFixtureTraceAddresses, heq] at hmap
  exact absurd hmap (by decide)

/--
**`FG-11` unread-cell expected accept.**  Cell `4` is allocated, the
canonical run never probes it, and replacing it by ANY cell leaves the
complete run record -- terminal, failure flag, state, and ordered trace --
unchanged, through the ordered agreement route.  This is the implementation
and theorem basis for `A02-UNREAD-CELL-EXPECTED-ACCEPT`.
-/
theorem packedReviewerUnreadCellAccept :
    (4 < packedReviewerCellCount
        (SuccinctClassic.cartesianShape [7, 3, 3]).size
        (longCount (SuccinctClassic.cartesianShape [7, 3, 3]))
        (packedReviewerSparseCount
          (SuccinctClassic.cartesianShape [7, 3, 3]))) /\
      (forall event,
        event ∈ (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace ->
          event.request.address ≠ 4) /\
      (forall replacement : List Bool,
        packedReviewerRunAgainstMemory
            ((packedReviewerMemory
                (SuccinctClassic.cartesianShape [7, 3, 3])).set 4 replacement)
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 =
          packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) := by
  refine ⟨?_, packedReviewerFixtureCellFourUnread, ?_⟩
  · rw [egcpShapePin, egcpSizePin, egcpLongCountPin, egcpSparseCountPin,
      egcpCellCountPin]
    decide
  · intro replacement
    refine (packedReviewerRunAgainstMemory_eq_of_agree
      (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
      ((packedReviewerMemory
          (SuccinctClassic.cartesianShape [7, 3, 3])).set 4 replacement)
      (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 ?_).symm
    intro event hmem
    have hmem' :
        event ∈ (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace := by
      simpa [packedReviewerRunAgainstMemory] using hmem
    have hreply := packedReviewerRunAgainstMemory_memory_only
      (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
      (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 event hmem'
    have hne := packedReviewerFixtureCellFourUnread event hmem'
    rw [hreply]
    exact List.getElem?_set_ne (by omega)

/-- The pinned `A02` instance at the frozen committed replacement value. -/
theorem packedReviewerUnreadCellAcceptPinned :
    packedReviewerRunAgainstMemory
        ((packedReviewerMemory
            (SuccinctClassic.cartesianShape [7, 3, 3])).set 4
          egcpStageFUnreadReplacementCell)
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 =
      packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 :=
  packedReviewerUnreadCellAccept.2.2 egcpStageFUnreadReplacementCell

/--
**The `M06` bridge.**  No completion function of the public metadata alone
-- any `f` applied to `(n, left, right)`, which covers both the enacted
`some n` oracle and a reference-semantics oracle of the pinned query -- can
produce the terminal values of both fixture runs: the decisive-cell pair
returns `some 1` and `some 2` at the identical metadata.  This is the
checked bridge from the accepted oracle-independence predicate to the
enacted `M06` mutation predicate, at the same objects, guards, and
quantifiers as the decisive-cell theorem.
-/
theorem packedReviewerNoMetadataCompletion :
    forall f : Nat -> Nat -> Nat -> Option Nat,
      Not ((packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
              some (f (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) /\
          (packedReviewerRunAgainstMemory
              ((packedReviewerMemory
                  (SuccinctClassic.cartesianShape [7, 3, 3])).set 8
                egcpDecisiveMutantCell)
              (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
            some (f (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3)) := by
  intro f ⟨hcanonical, hmutant⟩
  obtain ⟨hone, htwo, _⟩ := packedReviewerDecisiveCellLiveness
  rw [hone] at hcanonical
  rw [htwo] at hmutant
  rw [← hcanonical] at hmutant
  simp at hmutant

end EGCPStageFFixture

end PackedCellProbe

end SuccinctFinal

end RMQ
