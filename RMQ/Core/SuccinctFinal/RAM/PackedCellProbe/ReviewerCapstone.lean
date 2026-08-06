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
  refine ⟨packedReviewerSparsePreludeRequestBitAddress shape.size
      (longCount shape) .rankSuper / packedReviewerCellWidth shape.size,
    packedReviewerSparsePreludeRequestBitAddress shape.size
        (longCount shape + packedReviewerCellWidth shape.size) .rankSuper /
      packedReviewerCellWidth shape.size, ?_, ?_, hne⟩
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

end PackedCellProbe

end SuccinctFinal

end RMQ
