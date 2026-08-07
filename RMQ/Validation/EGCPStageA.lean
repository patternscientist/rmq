import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerArchitectureCapstone

/-!
# EG-CP Stage A: the independent expected-type consumer

This is the validation root frozen by
`docs/internal/EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` (`EG-CP-A11`).  It pins the
entire combined Stage-A architecture proposition independently: the structure
`EGCPStageAArchitectureFacts` below restates every one of the thirty-nine
frozen capstone fields at its literal expected type -- object identities,
guards, width, space, header, physical probe semantics, the exact `427` cap
derivation, correctness, invalid-domain behavior, uniformity, and the
no-assumed-capstone controls -- and `egcpStageAArchitectureFactsExact`
discharges it by projection from `packedReviewerArchitectureCapstone_holds`.
The expected types are written out in full and are never obtained by printing
or querying the capstone theorem's current type, so weakening, deleting,
swapping, or reguarding a public conjunct breaks this committed file.

The module also consumes the frozen boundary campaign (empty, singleton, both
size-two shapes, the long-crossover triple, the interior-readiness six,
invalid queries, and the duplicate-minimum fixture), re-pins the frozen
`[7, 3, 3]` `(0, 3)` header-liveness `10 -> 37` fixture, the decisive-cell
occurrence chain, the unread-cell pinned instance, and kernel-checks the
small-size width literals demanded by `EG-CP-A03`.

Category discipline: `427` is an upper bound on attempted physical probes,
not an attained count; `210` is logical fuel bounding attempts, not an exact
read count (`DD-20260805-075`).  `EG-CP-A13-CAPSTONE-AUDIT` remains open and
auditor-owned; nothing in this file records architecture acceptance.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

namespace Validation

open RMQ.Cartesian

/-! ## Exact signature pins (`EG-CP-A09`, `EG-CP-A11`)

Each `def` elaborates only at the exact public type, so an added shape, list,
oracle, advice, or store parameter -- optional or not -- breaks this file.
-/

/-- The combined Stage-A proposition's exact shape. -/
def egcpStageACapstoneSignature : List Int -> Nat -> Nat -> Prop :=
  @PackedReviewerArchitectureCapstone

/-- The one query-independent width function is size-only by signature. -/
def egcpStageAWidthSignature : Nat -> Nat :=
  packedReviewerCellWidth

/-- The closed controller receives exactly the three scalars. -/
def egcpStageAControllerSignature :
    Nat -> Nat -> Nat -> PackedReviewerControllerState :=
  packedReviewerController

/-- The physical run receives memory only at the driver interface. -/
def egcpStageARunSignature :
    List (List Bool) -> Nat -> Nat -> Nat -> PackedReviewerRun :=
  packedReviewerRunAgainstMemory

/-- The memory builder is shape-to-cells with no further input. -/
def egcpStageAMemorySignature : CartesianShape -> List (List Bool) :=
  packedReviewerMemory

/-! ## The independent restatement of the combined proposition -/

/--
Independent restatement of the thirty-eight frozen Stage-A conjuncts plus
field 39 (coordinator amendment `CA-20260807-001`).  Every
field type below is written out literally; none is derived from the capstone
declaration.  Removing or weakening any capstone conjunct breaks this
structure's producer rather than being absorbed by it.
-/
structure EGCPStageAArchitectureFacts
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
  memory_uniform_builder :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerMemory shape =
      (List.range (packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape))).map fun i =>
        ((packedReviewerPaddedBits shape).drop
          (i * packedReviewerCellWidth shape.size)).take
          (packedReviewerCellWidth shape.size)
  run_factorization :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right =
      packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
        (packedReviewerControllerMeasure
          (packedReviewerController shape.size left right))
        (packedReviewerController shape.size left right)
  one_cell_width :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ cell, cell ∈ packedReviewerMemory shape ->
      cell.length = packedReviewerCellWidth shape.size
  memory_length_arity :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length =
      packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape)
  allocation_two_n_plus_rho :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length * packedReviewerCellWidth shape.size <=
      2 * shape.size + packedReviewerRho shape.size
  rho_little_o : SuccinctSpace.LittleOLinear packedReviewerRho
  closed_length :
    ∀ n' lc sc : Nat,
      packedReviewerClosedPayloadLength n' lc sc =
        packedReviewerPayloadLength n' lc sc
  width_positive :
    let shape := SuccinctClassic.cartesianShape xs
    0 < packedReviewerCellWidth shape.size
  input_size_fits_width :
    let shape := SuccinctClassic.cartesianShape xs
    shape.size < 2 ^ packedReviewerCellWidth shape.size
  width_logarithmic :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerCellWidth shape.size <=
      20 * (Nat.log2 (shape.size + 2) + 1)
  header_exactly_one_cell :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerHeaderBits shape).length =
      packedReviewerCellWidth shape.size
  header_fields_fit :
    let shape := SuccinctClassic.cartesianShape xs
    longCount shape < 2 ^ packedReviewerCellWidth shape.size /\
      packedReviewerSparseCount shape <
        2 ^ packedReviewerCellWidth shape.size
  header_cell_zero :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape)[0]? = some (packedReviewerHeaderBits shape)
  header_decodes :
    let shape := SuccinctClassic.cartesianShape xs
    SuccinctSpace.bitsToNatLE (packedReviewerHeaderBits shape) =
      longCount shape
  run_opens_with_header :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace.map
            (fun event => event.request.address))[0]? = some 0
  header_liveness :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace.map
            (fun event => event.request.address))[1]? =
          some (packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape) .rankSuper /
              packedReviewerCellWidth shape.size) /\
        ((packedReviewerRunAgainstMemory
            ((packedReviewerMemory shape).set 0
              (SuccinctSpace.natToBitsLE (packedReviewerCellWidth shape.size)
                (longCount shape + packedReviewerCellWidth shape.size)))
            shape.size left right).trace.map
              (fun event => event.request.address))[1]? =
            some (packedReviewerSparsePreludeRequestBitAddress shape.size
              (longCount shape + packedReviewerCellWidth shape.size)
                .rankSuper / packedReviewerCellWidth shape.size) /\
        packedReviewerSparsePreludeRequestBitAddress shape.size
            (longCount shape) .rankSuper /
              packedReviewerCellWidth shape.size ≠
          packedReviewerSparsePreludeRequestBitAddress shape.size
              (longCount shape + packedReviewerCellWidth shape.size)
                .rankSuper / packedReviewerCellWidth shape.size
  memory_only :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.reply = (packedReviewerMemory shape)[event.request.address]?
  probes_allocated_and_successful :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address <
            packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape) /\
          ∃ cell, event.reply = some cell
  address_machine_width :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address < 2 ^ packedReviewerCellWidth shape.size
  reply_exact_width :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event cell,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          cell.length = packedReviewerCellWidth shape.size
  ordered_grouping :
    PackedReviewerRunGrouping (SuccinctClassic.cartesianShape xs) left right
  probe_plan_crossing :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ bit width : Nat,
      packedReviewerProbePlan shape.size bit width =
        if width = 0 then []
        else if bit % packedReviewerCellWidth shape.size + width <=
            packedReviewerCellWidth shape.size then
          [bit / packedReviewerCellWidth shape.size]
        else
          [bit / packedReviewerCellWidth shape.size,
            bit / packedReviewerCellWidth shape.size + 1]
  derived_cap_le_427 :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace.length <= 427
  cap_structural_derivation :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      packedReviewerControllerMeasure
          (packedReviewerController shape.size left right) =
        1 +
          2 * packedReviewerSparsePreludeRemaining
            (packedReviewerSparsePreludeInit shape.size 0) +
          2 * packedReviewerWholeRemaining
            (packedReviewerWholeStart shape.size left right) /\
      packedReviewerSparsePreludeRemaining
          (packedReviewerSparsePreludeInit shape.size 0) = 3 /\
      packedReviewerWholeRemaining
          (packedReviewerWholeStart shape.size left right) = 210 /\
      packedReviewerControllerMeasure
          (packedReviewerController shape.size left right) = 427
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
  leftmost_tie_universal :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      ∀ index,
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).terminal = some (some index) ->
          LeftmostArgMin xs left right index
  invalid_run_exact :
    let shape := SuccinctClassic.cartesianShape xs
    ¬ (left < right ∧ right <= shape.size) ->
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).terminal = some none /\
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).failed = false /\
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).state = .done none /\
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace = []
  invalid_reference_none :
    let shape := SuccinctClassic.cartesianShape xs
    ¬ (left < right ∧ right <= shape.size) ->
      (SuccinctClassic.queryTraceResult xs left right).value = none
  controller_exact_input_boundary :
    @packedReviewerController =
      (fun (n left right : Nat) => packedReviewerController n left right)
  controller_uniform_entry :
    ∀ n' l' r' : Nat,
      packedReviewerController n' l' r' =
        if l' < r' ∧ r' <= n' then .header n' l' r' else .done none
  store_agreement_determinism :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ memoryB : List (List Bool),
      (∀ event,
        event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
          memoryB[event.request.address]? = event.reply) ->
      packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right =
        packedReviewerRunAgainstMemory memoryB shape.size left right
  reachable_state_invariant :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ i : Nat,
      i < (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace.length ->
        packedReviewerControllerResult
            (packedReviewerDriveStateAt (packedReviewerMemory shape)
              (packedReviewerController shape.size left right) i) = none /\
        (∃ request,
          packedReviewerNextRequest
              (packedReviewerDriveStateAt (packedReviewerMemory shape)
                (packedReviewerController shape.size left right) i) =
            some request /\
          (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
              shape.size left right).trace[i]? =
            some
              { request := request
                reply := (packedReviewerMemory shape)[request.address]? }) /\
        (packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
            (packedReviewerControllerMeasure
                (packedReviewerController shape.size left right) - i)
            (packedReviewerDriveStateAt (packedReviewerMemory shape)
              (packedReviewerController shape.size left right) i)).terminal =
          (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).terminal /\
        (packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
            (packedReviewerControllerMeasure
                (packedReviewerController shape.size left right) - i)
            (packedReviewerDriveStateAt (packedReviewerMemory shape)
              (packedReviewerController shape.size left right) i)).state =
          (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).state /\
        (packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
            (packedReviewerControllerMeasure
                (packedReviewerController shape.size left right) - i)
            (packedReviewerDriveStateAt (packedReviewerMemory shape)
              (packedReviewerController shape.size left right) i)).trace =
          (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).trace.drop i
  decisive_cell_liveness :
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
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal
  unread_cell_accept :
    (4 < packedReviewerCellCount
        (SuccinctClassic.cartesianShape [7, 3, 3]).size
        (longCount (SuccinctClassic.cartesianShape [7, 3, 3]))
        (packedReviewerSparseCount
          (SuccinctClassic.cartesianShape [7, 3, 3]))) /\
      (∀ event,
        event ∈ (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).trace ->
          event.request.address ≠ 4) /\
      (∀ replacement : List Bool,
        packedReviewerRunAgainstMemory
            ((packedReviewerMemory
                (SuccinctClassic.cartesianShape [7, 3, 3])).set 4 replacement)
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 =
          packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3)
  no_metadata_completion :
    ∀ f : Nat -> Nat -> Nat -> Option Nat,
      ¬ ((packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
            (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
              some (f (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3) /\
          (packedReviewerRunAgainstMemory
              ((packedReviewerMemory
                  (SuccinctClassic.cartesianShape [7, 3, 3])).set 8
                egcpDecisiveMutantCell)
              (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
            some (f (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3))
  valid_answer_is_index :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      ∃ index,
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).terminal = some (some index) /\
          (SuccinctClassic.queryTraceResult xs left right).value =
            some index /\
          LeftmostArgMin xs left right index

/-- Every independent Stage-A fact is inhabited by capstone projection. -/
theorem egcpStageAArchitectureFactsExact
    (xs : List Int) (left right : Nat) :
    EGCPStageAArchitectureFacts xs left right := by
  have capstone := packedReviewerArchitectureCapstone_holds xs left right
  exact
    { payload_is_buildPayload := capstone.payload_is_buildPayload
      serialized_header_payload := capstone.serialized_header_payload
      padded_final_padding := capstone.padded_final_padding
      memory_uniform_builder := capstone.memory_uniform_builder
      run_factorization := capstone.run_factorization
      one_cell_width := capstone.one_cell_width
      memory_length_arity := capstone.memory_length_arity
      allocation_two_n_plus_rho := capstone.allocation_two_n_plus_rho
      rho_little_o := capstone.rho_little_o
      closed_length := capstone.closed_length
      width_positive := capstone.width_positive
      input_size_fits_width := capstone.input_size_fits_width
      width_logarithmic := capstone.width_logarithmic
      header_exactly_one_cell := capstone.header_exactly_one_cell
      header_fields_fit := capstone.header_fields_fit
      header_cell_zero := capstone.header_cell_zero
      header_decodes := capstone.header_decodes
      run_opens_with_header := capstone.run_opens_with_header
      header_liveness := capstone.header_liveness
      memory_only := capstone.memory_only
      probes_allocated_and_successful :=
        capstone.probes_allocated_and_successful
      address_machine_width := capstone.address_machine_width
      reply_exact_width := capstone.reply_exact_width
      ordered_grouping := capstone.ordered_grouping
      probe_plan_crossing := capstone.probe_plan_crossing
      derived_cap_le_427 := capstone.derived_cap_le_427
      cap_structural_derivation := capstone.cap_structural_derivation
      guarded_reference_result := capstone.guarded_reference_result
      leftmost_tie_universal := capstone.leftmost_tie_universal
      invalid_run_exact := capstone.invalid_run_exact
      invalid_reference_none := capstone.invalid_reference_none
      controller_exact_input_boundary :=
        capstone.controller_exact_input_boundary
      controller_uniform_entry := capstone.controller_uniform_entry
      store_agreement_determinism := capstone.store_agreement_determinism
      reachable_state_invariant := capstone.reachable_state_invariant
      decisive_cell_liveness := capstone.decisive_cell_liveness
      unread_cell_accept := capstone.unread_cell_accept
      no_metadata_completion := capstone.no_metadata_completion
      valid_answer_is_index := capstone.valid_answer_is_index }

/-! ## Boundary campaign (`EG-CP-A08`): the one universal capstone at every
frozen boundary -- no per-size variant, readiness, or compatibility dispatch
exists to select. -/

/-- Empty representation. -/
theorem egcpStageACapstoneEmpty : PackedReviewerArchitectureCapstone [] 0 0 :=
  packedReviewerArchitectureCapstone_holds [] 0 0

/-- Singleton representation, with its one valid query. -/
theorem egcpStageACapstoneSingleton :
    PackedReviewerArchitectureCapstone [0] 0 1 :=
  packedReviewerArchitectureCapstone_holds [0] 0 1

/-- Both distinct size-two Cartesian shapes. -/
theorem egcpStageACapstoneSizeTwo :
    PackedReviewerArchitectureCapstone [0, 1] 0 2 /\
      PackedReviewerArchitectureCapstone [1, 0] 0 2 :=
  ⟨packedReviewerArchitectureCapstone_holds [0, 1] 0 2,
    packedReviewerArchitectureCapstone_holds [1, 0] 0 2⟩

/-- The two size-two shapes are distinct, witnessed by diverging answers. -/
theorem egcpStageASizeTwoDistinct :
    SuccinctClassic.cartesianShape [(0 : Int), 1] ≠
      SuccinctClassic.cartesianShape [(1 : Int), 0] :=
  packedReviewerStageFCapstone_sizeTwoShapesDistinct

/-- The long-crossover triple `5487/5488/5489`. -/
theorem egcpStageACapstoneCrossovers :
    PackedReviewerArchitectureCapstone (List.replicate 5487 0) 0 5487 /\
      PackedReviewerArchitectureCapstone (List.replicate 5488 0) 0 5488 /\
      PackedReviewerArchitectureCapstone (List.replicate 5489 0) 0 5489 :=
  ⟨packedReviewerArchitectureCapstone_holds (List.replicate 5487 0) 0 5487,
    packedReviewerArchitectureCapstone_holds (List.replicate 5488 0) 0 5488,
    packedReviewerArchitectureCapstone_holds (List.replicate 5489 0) 0 5489⟩

/-- The interior-readiness window endpoints and neighbours. -/
theorem egcpStageACapstoneReadinessWindow :
    PackedReviewerArchitectureCapstone (List.replicate 1023 0) 0 1023 /\
      PackedReviewerArchitectureCapstone (List.replicate 1024 0) 0 1024 /\
      PackedReviewerArchitectureCapstone (List.replicate 1025 0) 0 1025 /\
      PackedReviewerArchitectureCapstone (List.replicate 1329 0) 0 1329 /\
      PackedReviewerArchitectureCapstone (List.replicate 1330 0) 0 1330 /\
      PackedReviewerArchitectureCapstone (List.replicate 1331 0) 0 1331 :=
  ⟨packedReviewerArchitectureCapstone_holds (List.replicate 1023 0) 0 1023,
    packedReviewerArchitectureCapstone_holds (List.replicate 1024 0) 0 1024,
    packedReviewerArchitectureCapstone_holds (List.replicate 1025 0) 0 1025,
    packedReviewerArchitectureCapstone_holds (List.replicate 1329 0) 0 1329,
    packedReviewerArchitectureCapstone_holds (List.replicate 1330 0) 0 1330,
    packedReviewerArchitectureCapstone_holds (List.replicate 1331 0) 0 1331⟩

/-- Query-level boundary cases on the pinned fixture shape: empty range,
reversed endpoints, right endpoint out of range, left endpoint out of range. -/
theorem egcpStageACapstoneInvalidQueries :
    PackedReviewerArchitectureCapstone [7, 3, 3] 1 1 /\
      PackedReviewerArchitectureCapstone [7, 3, 3] 2 1 /\
      PackedReviewerArchitectureCapstone [7, 3, 3] 0 4 /\
      PackedReviewerArchitectureCapstone [7, 3, 3] 5 7 :=
  ⟨packedReviewerArchitectureCapstone_holds [7, 3, 3] 1 1,
    packedReviewerArchitectureCapstone_holds [7, 3, 3] 2 1,
    packedReviewerArchitectureCapstone_holds [7, 3, 3] 0 4,
    packedReviewerArchitectureCapstone_holds [7, 3, 3] 5 7⟩

/-- The duplicate-minimum fixture inhabits the capstone. -/
theorem egcpStageACapstoneDuplicateMin :
    PackedReviewerArchitectureCapstone [7, 3, 3] 0 3 :=
  packedReviewerArchitectureCapstone_holds [7, 3, 3] 0 3

/-- Invalid endpoint pairs produce the exact `.done none` run with an empty
trace, universally. -/
theorem egcpStageAInvalidRunExact :
    ∀ (xs : List Int) (left right : Nat),
      ¬ (left < right /\
          right <= (SuccinctClassic.cartesianShape xs).size) ->
        (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs).size left right).terminal =
              some none /\
          (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs).size left right).trace = [] :=
  fun xs left right hbad =>
    packedReviewerStageFInvalidRunExact xs left right hbad

/-- The duplicate-minimum fixture: independent reference value, leftmost-tie
specification, and the packed run's own terminal. -/
theorem egcpStageADuplicateMinimum :
    (SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value = some 1 /\
      LeftmostArgMin [7, 3, 3] 0 3 1 /\
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
          (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3).terminal =
        some (some 1) :=
  ⟨packedReviewerStageFDuplicateMinReference,
    packedReviewerStageFDuplicateMinLeftmost,
    packedReviewerStageFDuplicateMinRun⟩

/-- No second representation: the controller entry and the memory builder are
single uniform definitions with no size or readiness dispatch. -/
theorem egcpStageANoSecondRepresentation :
    (∀ n left right : Nat,
        packedReviewerController n left right =
          if left < right /\ right <= n then .header n left right
          else .done none) /\
      (∀ shape : CartesianShape,
        packedReviewerMemory shape =
          (List.range (packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape))).map fun i =>
            ((packedReviewerPaddedBits shape).drop
              (i * packedReviewerCellWidth shape.size)).take
              (packedReviewerCellWidth shape.size)) :=
  ⟨packedReviewerControllerUniformEntry, packedReviewerMemoryUniformBuilder⟩

/-! ## Small-size width literals (`EG-CP-A03`)

The one width function pinned at the smallest sizes, kernel-checked.
`Nat.log2` is not kernel-reducible, so each pin unfolds the width closure by
`simp` before `decide` finishes the arithmetic -- the same staged-literal
technique as the accepted fixture evaluation (`DD-20260806-077`).
-/

section EGCPStageAWidthPins

attribute [local simp] Nat.log2
attribute [local simp] RMQ.SuccinctRank.machineWordBits
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
attribute [local simp] RMQ.SuccinctSpace.logLogSampledDirectoryOverhead
attribute [local simp] RMQ.SuccinctSpace.sampledDirectoryOverhead
attribute [local simp] RMQ.GenericSelect.wordBits
attribute [local simp] RMQ.GenericSelect.ell
attribute [local simp] RMQ.GenericSelect.superStride
attribute [local simp] RMQ.GenericSelect.selectCeilDiv
attribute [local simp] RMQ.SuccinctClose.bpSuperblockSpan
attribute [local simp] RMQ.SuccinctClose.bpSparseLogSpan

/-- The empty-representation width is ten bits -- no byte or word minimum is
assumed at the bottom of the range. -/
theorem egcpStageAWidthPinZero : packedReviewerCellWidth 0 = 10 := by
  simp +decide

/-- The singleton width. -/
theorem egcpStageAWidthPinOne : packedReviewerCellWidth 1 = 14 := by
  simp +decide

/-- The size-two width -- the first size carrying two distinct shapes shares
one width, by the size-only signature. -/
theorem egcpStageAWidthPinTwo : packedReviewerCellWidth 2 = 14 := by
  simp +decide

/-- The frozen fixture width, agreeing with the accepted `egcpWidthPin`. -/
theorem egcpStageAWidthPinThree : packedReviewerCellWidth 3 = 15 := by
  simp +decide

end EGCPStageAWidthPins

/-! ## Frozen fixture re-pins (`EG-CP-A04`, `EG-CP-A10`) -/

/-- The frozen header-liveness fixture: on `[7, 3, 3]` with query `(0, 3)`,
replacing only the counted header cell moves the second attempted physical
address from cell `10` to cell `37`. -/
theorem egcpStageAHeaderLivenessFixture :
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
      (10 : Nat) ≠ 37 :=
  packedReviewerHeaderCellAddressLiveness_fixture

/-- The unread-cell expected-ACCEPT instance at the frozen committed
replacement value. -/
theorem egcpStageAUnreadCellAcceptPinned :
    packedReviewerRunAgainstMemory
        ((packedReviewerMemory
            (SuccinctClassic.cartesianShape [7, 3, 3])).set 4
          egcpStageFUnreadReplacementCell)
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 =
      packedReviewerRunAgainstMemory
        (packedReviewerMemory (SuccinctClassic.cartesianShape [7, 3, 3]))
        (SuccinctClassic.cartesianShape [7, 3, 3]).size 0 3 :=
  packedReviewerUnreadCellAcceptPinned

/-- The interior dead/sentinel address fits the modeled machine word at every
size (query-independent; instantiated through the certificate). -/
theorem egcpStageADeadAddressWidth (xs : List Int) :
    (packedInteriorOffsets (SuccinctClassic.cartesianShape xs).size).deadAddress <
      2 ^ packedReviewerCellWidth (SuccinctClassic.cartesianShape xs).size :=
  (packedReviewerRunAgainstMemory_public_certificate xs 0 0).dead_address_width

/--
The decisive occurrence chain, restated at its full literal expected type:
the producing invocation fields, the driver prefix decomposition to the
pre-state, the `nextRequest`/`consumeReply` transition, and the checked
continuation to the same run's `.done (some 1)` must all survive in the
producer's conclusion.  Weakening the producer back to an origin-erasing
proposition makes this consumer fail to elaborate.
-/
theorem egcpStageADecisiveCellConnection :
    ∃ (position : Nat) (event : PackedReviewerPhysicalEvent)
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
      (SuccinctClassic.queryTraceResult [7, 3, 3] 0 3).value = some 1 :=
  packedReviewerDecisiveCellConnection

end Validation

end PackedCellProbe

end SuccinctFinal

end RMQ
