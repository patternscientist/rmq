import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerCapstone

/-!
# The Stage-A combined architecture capstone

This module closes the Stage-A worker rung frozen in
`docs/internal/EG_CP_STAGEA_ACCEPTANCE_MATRIX.md` section 1.1.

`PackedReviewerArchitectureCapstone` combines, on the identical objects
`shape := SuccinctClassic.cartesianShape xs`,
`memory := packedReviewerMemory shape`, and the literal
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left
right`, the thirty-eight frozen fields plus field 39 added by coordinator
amendment `CA-20260807-001`: the one-object composition
(`EG-CP-A01`), the complete allocated capacity with its little-o residual
(`EG-CP-A02`), the explicit all-size width bounds (`EG-CP-A03`), the counted
header decoding and universal header-address liveness (`EG-CP-A04`), the
aligned fixed-width probe semantics with the conditional crossing expansion
(`EG-CP-A05`), the derived `427 = 1 + 2*3 + 2*210` cap (`EG-CP-A06`), the
guarded leftmost reference correctness with the universal leftmost-tie
connection (`EG-CP-A07`), the exact invalid-domain behavior (`EG-CP-A08`),
the closed controller input boundary and store-agreement determinism
(`EG-CP-A09`), and the reachable-state invariant with the frozen decisive,
unread-cell, and metadata-completion fixture controls (`EG-CP-A10`).

`packedReviewerArchitectureCapstone_holds` inhabits it for every input list
and every endpoint pair.  Every field is a checked consequence of the
accepted Stage-F implementation -- no new execution, memory, controller,
result, or cost model is introduced, and no field quantifies over a sibling
payload, store, or run.  This module deliberately contains no instance
consumption: every boundary instance and every expected-type restatement
lives in `RMQ/Validation/EGCPStageA.lean`, so a weakening of the producer
surfaces at that committed consumer.

Category discipline (`INV-CATEGORY-SEPARATION`): `427` bounds attempted
physical probes of the run and is an upper bound, not an attainment claim;
`210` is logical fuel bounding attempts, not an exact read count
(`DD-20260805-075`); allocated bits (`memory.length * w`) are distinct from
logical payload bits (`buildPayload`).
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ## Helper theorems consumed by the producer -/

/-- The charged sparse-prelude budget at the header state is exactly `3`,
structurally: the initial prelude state awaits its three discovery reads. -/
theorem packedReviewerPreludeRemaining_init_eq_three (n : Nat) :
    packedReviewerSparsePreludeRemaining
      (packedReviewerSparsePreludeInit n 0) = 3 := rfl

/-- The whole-query budget at its start state is exactly `210` for every
in-range left endpoint: the select entry chain contributes `4 + 31` and the
remaining protocol `175`.  This is the `2 * 210` term of the derived cap. -/
theorem packedReviewerWholeRemaining_start_eq_210
    (n left right : Nat) (hleft : left < n) :
    packedReviewerWholeRemaining (packedReviewerWholeStart n left right) =
      210 := by
  simp [packedReviewerWholeStart, packedReviewerWholeRemaining,
    packedReviewerSelectStart, hleft, packedReviewerSelectRemaining,
    packedReviewerEntryRemaining]

/-- The guarded reference value of an invalid endpoint pair is `none`: the
unconditional public terminal equality and the invalid-run certificate name
the same run object, so the reference value is forced. -/
theorem packedReviewerInvalidReferenceNone
    (xs : List Int) (left right : Nat)
    (hbad :
      ¬ (left < right ∧
        right <= (SuccinctClassic.cartesianShape xs).size)) :
    (SuccinctClassic.queryTraceResult xs left right).value = none := by
  have hterminal :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).terminal =
        some (SuccinctClassic.queryTraceResult xs left right).value :=
    (packedReviewerRunAgainstMemory_public_certificate xs left right).terminal_eq
  have hinvalid :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).terminal =
        some none :=
    (packedReviewerRunAgainstMemory_invalid_certificate
      (SuccinctClassic.cartesianShape xs) left right hbad).1
  rw [hterminal] at hinvalid
  exact Option.some.inj hinvalid

/--
**Universal leftmost-tie connection.**  For every valid half-open query, any
index returned by the packed run's terminal is the leftmost argmin of the
window, through the independent `scanWindow` reference specification -- never
through the implementation being tested (`INV-ORACLE-INDEPENDENCE`).
-/
theorem packedReviewerRunLeftmostTie
    (xs : List Int) (left right : Nat)
    (hleft : left < right)
    (hright : right <= (SuccinctClassic.cartesianShape xs).size)
    (index : Nat)
    (hterm :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).terminal =
        some (some index)) :
    LeftmostArgMin xs left right index := by
  have hterminal :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).terminal =
        some (SuccinctClassic.queryTraceResult xs left right).value :=
    (packedReviewerRunAgainstMemory_public_certificate xs left right).terminal_eq
  rw [hterminal] at hterm
  have hvalue :
      (SuccinctClassic.queryTraceResult xs left right).value = some index :=
    Option.some.inj hterm
  have hlenBound : right <= xs.length := by
    rwa [packedReviewerCartesianShape_size] at hright
  have hlenPos : 0 < right - left := by omega
  have hsum : left + (right - left) = right := by omega
  have hbound : left + (right - left) <= xs.length := by omega
  have hquery :
      (SuccinctClassic.queryCosted xs left (left + (right - left))).erase =
        some index := by
    rw [hsum]
    exact hvalue
  have hlm := SuccinctClassic.queryCosted_leftmost xs hlenPos hbound hquery
  rwa [hsum] at hlm

/--
**A valid query is actually answered, with an index.**  For every valid
half-open query the run's terminal is `some (some index)` -- a proper
answer, not `none` -- that index is the reference's value, and it is the
leftmost argmin of the window.

This is the valid-domain companion of `invalid_reference_none`: without it
the combined proposition pins the run to the reference without ever saying
the reference (hence the machine) produces an index at all, so a reader of
the capstone alone could not conclude that valid queries are answered.  The
index side comes from the independent `scanWindow` specification through
`SuccinctClassic.queryCosted_exact`, never from the implementation under
test (`INV-ORACLE-INDEPENDENCE`).
-/
theorem packedReviewerValidRunAnswersIndex
    (xs : List Int) (left right : Nat)
    (hleft : left < right)
    (hright : right <= (SuccinctClassic.cartesianShape xs).size) :
    ∃ index,
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).terminal =
          some (some index) /\
        (SuccinctClassic.queryTraceResult xs left right).value = some index /\
        LeftmostArgMin xs left right index := by
  have hlenBound : right <= xs.length := by
    rwa [packedReviewerCartesianShape_size] at hright
  have hlenPos : 0 < right - left := by omega
  have hsum : left + (right - left) = right := by omega
  have hbound : left + (right - left) <= xs.length := by omega
  have hexact := SuccinctClassic.queryCosted_exact xs hlenPos hbound
  rw [hsum] at hexact
  have hbridge :
      (SuccinctClassic.queryTraceResult xs left right).value =
        (SuccinctClassic.queryCosted xs left right).erase := rfl
  have hvalue :
      (SuccinctClassic.queryTraceResult xs left right).value =
        some (scanWindow xs left (right - left)) := by
    rw [hbridge]
    exact hexact
  have hterminal :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).terminal =
        some (SuccinctClassic.queryTraceResult xs left right).value :=
    (packedReviewerRunAgainstMemory_public_certificate xs left right).terminal_eq
  have hrun :
      (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).terminal =
        some (some (scanWindow xs left (right - left))) := by
    rw [hterminal, hvalue]
  exact ⟨scanWindow xs left (right - left), hrun, hvalue,
    packedReviewerRunLeftmostTie xs left right hleft hright _ hrun⟩

/--
**The reachable-state base/step/final invariant at the literal run.**  For
every position of the run's trace, the driver prefix fold
`packedReviewerDriveStateAt` is live, computes the emitted request, the
recorded event is exactly that request with the driver's own memory lookup,
and the drive restarted at the fold with the remaining measure reproduces
the run's terminal, state, and trace suffix.  This is
`packedReviewerDriveAux_decompose` instantiated at the literal public run
object, so packed execution -- not an assumed answer or a shape-generated
replay -- produces each next address, reply, state, and result.
-/
theorem packedReviewerRunReachableInvariant
    (xs : List Int) (left right : Nat) :
    ∀ i : Nat,
      i < (packedReviewerRunAgainstMemory
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right).trace.length ->
        packedReviewerControllerResult
            (packedReviewerDriveStateAt
              (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
              (packedReviewerController
                (SuccinctClassic.cartesianShape xs).size left right) i) =
          none /\
        (∃ request,
          packedReviewerNextRequest
              (packedReviewerDriveStateAt
                (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
                (packedReviewerController
                  (SuccinctClassic.cartesianShape xs).size left right) i) =
            some request /\
          (packedReviewerRunAgainstMemory
              (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
              (SuccinctClassic.cartesianShape xs).size left right).trace[i]? =
            some
              { request := request
                reply :=
                  (packedReviewerMemory
                    (SuccinctClassic.cartesianShape xs))[request.address]? }) /\
        (packedReviewerDriveAgainstMemoryAux
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (packedReviewerControllerMeasure
                (packedReviewerController
                  (SuccinctClassic.cartesianShape xs).size left right) - i)
            (packedReviewerDriveStateAt
              (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
              (packedReviewerController
                (SuccinctClassic.cartesianShape xs).size left right) i)).terminal =
          (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs).size left right).terminal /\
        (packedReviewerDriveAgainstMemoryAux
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (packedReviewerControllerMeasure
                (packedReviewerController
                  (SuccinctClassic.cartesianShape xs).size left right) - i)
            (packedReviewerDriveStateAt
              (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
              (packedReviewerController
                (SuccinctClassic.cartesianShape xs).size left right) i)).state =
          (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs).size left right).state /\
        (packedReviewerDriveAgainstMemoryAux
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (packedReviewerControllerMeasure
                (packedReviewerController
                  (SuccinctClassic.cartesianShape xs).size left right) - i)
            (packedReviewerDriveStateAt
              (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
              (packedReviewerController
                (SuccinctClassic.cartesianShape xs).size left right) i)).trace =
          (packedReviewerRunAgainstMemory
            (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs).size left right).trace.drop
            i := by
  intro i hlt
  have hlt' :
      i < (packedReviewerDriveAgainstMemoryAux
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (packedReviewerControllerMeasure
            (packedReviewerController
              (SuccinctClassic.cartesianShape xs).size left right))
          (packedReviewerController
            (SuccinctClassic.cartesianShape xs).size left right)).trace.length :=
    hlt
  obtain ⟨hres, ⟨request, hreq, hat⟩, hterm, hstate, htrace⟩ :=
    packedReviewerDriveAux_decompose
      (packedReviewerMemory (SuccinctClassic.cartesianShape xs)) i
      (packedReviewerControllerMeasure
        (packedReviewerController
          (SuccinctClassic.cartesianShape xs).size left right))
      (packedReviewerController
        (SuccinctClassic.cartesianShape xs).size left right) hlt'
  exact ⟨hres, ⟨request, hreq, hat⟩, hterm, hstate, htrace⟩

/-! ## The combined Stage-A architecture capstone -/

/--
The Stage-A combined architecture proposition.  Every field is stated over
the identical objects `shape := SuccinctClassic.cartesianShape xs`,
`packedReviewerMemory shape`, and the literal
`packedReviewerRunAgainstMemory (packedReviewerMemory shape) shape.size left
right`; no field is allowed to quantify over a sibling payload, store, or
run, and no field may be discharged from the flat `packed*` universe.  The
thirty-eight-field list is frozen by matrix section 1.1, and field 39 is
appended by coordinator amendment `CA-20260807-001` (audit finding `P3-3`)
without changing any frozen field.  Fields 36-38 pin
the frozen `[7, 3, 3]` `(0, 3)` fixture controls (decisive cell `8`, unread
cell `4`, metadata-completion bridge) inside the combined proposition, as
`EG-CP-A04`/`EG-CP-A10` demand.
-/
structure PackedReviewerArchitectureCapstone
    (xs : List Int) (left right : Nat) : Prop where
  /-- Field 1 (`EG-CP-A01`). -/
  payload_is_buildPayload :
    packedReviewerPayloadBits (SuccinctClassic.cartesianShape xs) =
      SuccinctClassic.buildPayload xs
  /-- Field 2 (`EG-CP-A01`). -/
  serialized_header_payload :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerSerializedBits shape =
      packedReviewerHeaderBits shape ++ packedReviewerPayloadBits shape
  /-- Field 3 (`EG-CP-A01`). -/
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
  /-- Field 4 (`EG-CP-A01`): the memory builder is one uniform chunking
  expression of the padded bits -- no second representation. -/
  memory_uniform_builder :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerMemory shape =
      (List.range (packedReviewerCellCount shape.size (longCount shape)
          (packedReviewerSparseCount shape))).map fun i =>
        ((packedReviewerPaddedBits shape).drop
          (i * packedReviewerCellWidth shape.size)).take
          (packedReviewerCellWidth shape.size)
  /-- Field 5 (`EG-CP-A01`/`EG-CP-A09`): the run is the literal drive of the
  closed controller against the one memory; memory reaches only the driver. -/
  run_factorization :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right =
      packedReviewerDriveAgainstMemoryAux (packedReviewerMemory shape)
        (packedReviewerControllerMeasure
          (packedReviewerController shape.size left right))
        (packedReviewerController shape.size left right)
  /-- Field 6 (`EG-CP-A02`/`EG-CP-A03`). -/
  one_cell_width :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ cell, cell ∈ packedReviewerMemory shape ->
      cell.length = packedReviewerCellWidth shape.size
  /-- Field 7 (`EG-CP-A02`). -/
  memory_length_arity :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length =
      packedReviewerCellCount shape.size (longCount shape)
        (packedReviewerSparseCount shape)
  /-- Field 8 (`EG-CP-A02`): complete allocated capacity -- header cell,
  every payload cell, and final padding at full width. -/
  allocation_two_n_plus_rho :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape).length * packedReviewerCellWidth shape.size <=
      2 * shape.size + packedReviewerRho shape.size
  /-- Field 9 (`EG-CP-A02`). -/
  rho_little_o : SuccinctSpace.LittleOLinear packedReviewerRho
  /-- Field 10 (`EG-CP-A02`). -/
  closed_length :
    ∀ n' lc sc : Nat,
      packedReviewerClosedPayloadLength n' lc sc =
        packedReviewerPayloadLength n' lc sc
  /-- Field 11 (`EG-CP-A03`): explicit all-size lower bound. -/
  width_positive :
    let shape := SuccinctClassic.cartesianShape xs
    0 < packedReviewerCellWidth shape.size
  /-- Field 12 (`EG-CP-A03`): the input size fits the width. -/
  input_size_fits_width :
    let shape := SuccinctClassic.cartesianShape xs
    shape.size < 2 ^ packedReviewerCellWidth shape.size
  /-- Field 13 (`EG-CP-A03`): explicit all-size upper bound with the literal
  coefficient `20`. -/
  width_logarithmic :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerCellWidth shape.size <=
      20 * (Nat.log2 (shape.size + 2) + 1)
  /-- Field 14 (`EG-CP-A03`/`EG-CP-A04`): the header is exactly one cell. -/
  header_exactly_one_cell :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerHeaderBits shape).length =
      packedReviewerCellWidth shape.size
  /-- Field 15 (`EG-CP-A03`): both decoded header fields fit the width. -/
  header_fields_fit :
    let shape := SuccinctClassic.cartesianShape xs
    longCount shape < 2 ^ packedReviewerCellWidth shape.size /\
      packedReviewerSparseCount shape <
        2 ^ packedReviewerCellWidth shape.size
  /-- Field 16 (`EG-CP-A04`): the header is cell zero of the one memory. -/
  header_cell_zero :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerMemory shape)[0]? = some (packedReviewerHeaderBits shape)
  /-- Field 17 (`EG-CP-A04`): the header cell decodes to the long count. -/
  header_decodes :
    let shape := SuccinctClassic.cartesianShape xs
    SuccinctSpace.bitsToNatLE (packedReviewerHeaderBits shape) =
      longCount shape
  /-- Field 18 (`EG-CP-A04`): every valid run opens with the header probe. -/
  run_opens_with_header :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      ((packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace.map
            (fun event => event.request.address))[0]? = some 0
  /-- Field 19 (`EG-CP-A04`): universal header-address liveness -- replacing
  only the counted header cell moves the second attempted physical address,
  at the address projection of trace position 1. -/
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
  /-- Field 20 (`EG-CP-A05`): memory-only replies -- every trace event's
  reply is literally the indexed cell of the one memory. -/
  memory_only :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.reply = (packedReviewerMemory shape)[event.request.address]?
  /-- Field 21 (`EG-CP-A05`): in-range totality -- every attempted probe is
  allocated and successful. -/
  probes_allocated_and_successful :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address <
            packedReviewerCellCount shape.size (longCount shape)
              (packedReviewerSparseCount shape) /\
          ∃ cell, event.reply = some cell
  /-- Field 22 (`EG-CP-A02`/`EG-CP-A03`/`EG-CP-A05`): every attempted
  address fits the modeled word, not merely the host array. -/
  address_machine_width :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address < 2 ^ packedReviewerCellWidth shape.size
  /-- Field 23 (`EG-CP-A05`): every replied cell has the exact width. -/
  reply_exact_width :
    let shape := SuccinctClassic.cartesianShape xs
    ∀ event cell,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          cell.length = packedReviewerCellWidth shape.size
  /-- Field 24 (`EG-CP-A05`/`EG-CP-A06`): order- and multiplicity-sensitive
  trace identity of the executed run. -/
  ordered_grouping :
    PackedReviewerRunGrouping (SuccinctClassic.cartesianShape xs) left right
  /-- Field 25 (`EG-CP-A05`): the conditional probe plan -- one aligned
  fixed-width read per contained span, exactly two ordered probes for an
  unaligned span crossing a cell boundary. -/
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
  /-- Field 26 (`EG-CP-A06`): the derived cap on attempted physical probes.
  Upper bound, not attainment. -/
  derived_cap_le_427 :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace.length <= 427
  /-- Field 27 (`EG-CP-A06`): the structural derivation of the exact numeral
  `427 = 1 + 2*3 + 2*210` from the run's own fuel measure -- never a stored
  numeral, input, hypothesis, or precomputed result. -/
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
  /-- Field 28 (`EG-CP-A07`): the guarded leftmost half-open reference
  result on the identical run object, unconditionally. -/
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
  /-- Field 29 (`EG-CP-A07`): the universal leftmost-tie connection through
  the independent `scanWindow` specification. -/
  leftmost_tie_universal :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      ∀ index,
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).terminal = some (some index) ->
          LeftmostArgMin xs left right index
  /-- Field 30 (`EG-CP-A08`): the exact invalid-domain run -- terminal
  `some none`, not failed, `.done none` state, empty trace. -/
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
  /-- Field 31 (`EG-CP-A08`): the reference agrees on the invalid domain, so
  the unconditional field 28 is not weakened and every field shares one
  guard. -/
  invalid_reference_none :
    let shape := SuccinctClassic.cartesianShape xs
    ¬ (left < right ∧ right <= shape.size) ->
      (SuccinctClassic.queryTraceResult xs left right).value = none
  /-- Field 32 (`EG-CP-A09`): the exact-type controller input boundary --
  this equation elaborates only at
  `Nat -> Nat -> Nat -> PackedReviewerControllerState`. -/
  controller_exact_input_boundary :
    @packedReviewerController =
      (fun (n left right : Nat) => packedReviewerController n left right)
  /-- Field 33 (`EG-CP-A09`): the controller entry is one guard and one
  uniform state at every size -- no readiness or compatibility dispatch. -/
  controller_uniform_entry :
    ∀ n' l' r' : Nat,
      packedReviewerController n' l' r' =
        if l' < r' ∧ r' <= n' then .header n' l' r' else .done none
  /-- Field 34 (`EG-CP-A09`): ordered store-agreement determinism -- equal
  replies on the run's trace determine the complete run record. -/
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
  /-- Field 35 (`EG-CP-A10`): the reachable-state base/step/final invariant
  at the literal run: every trace position is produced by the live driver
  prefix fold, and the continuation reproduces terminal, state, and trace
  suffix. -/
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
  /-- Field 36 (`EG-CP-A10`): decisive-cell corruption rejection at the
  frozen fixture -- the inequality is at the `.terminal` projection. -/
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
  /-- Field 37 (`EG-CP-A10`): the proved-unread-cell expected-ACCEPT control
  at the frozen fixture -- complete run-record equality for every
  replacement, through the ordered agreement route. -/
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
  /-- Field 38 (`EG-CP-A10`): the metadata-completion bridge -- no
  completion function of the public metadata alone produces both frozen
  fixture terminals. -/
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
  /-- Field 39 (`EG-CP-A07`, added by coordinator amendment `CA-20260807-001`
  after `AUD1` finding `P3-3`): a valid query is actually answered, with an
  index that is the leftmost argmin.  This is the valid-domain companion of
  `invalid_reference_none` (field 31); without it the combined proposition
  pins the run to the reference without ever stating that either produces an
  index.  Strengthening only: no frozen field is changed. -/
  valid_answer_is_index :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      ∃ index,
        (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
            shape.size left right).terminal = some (some index) /\
          (SuccinctClassic.queryTraceResult xs left right).value =
            some index /\
          LeftmostArgMin xs left right index

/--
Every Stage-A conjunct holds for every input list and every endpoint pair,
by projection from the public run certificate, the accepted payload, memory,
space, width, and agreement theorems, the universal header-liveness theorem,
the driver decomposition, and the frozen fixture theorems -- there is no new
execution story here, only the one already proved for the identical objects.
-/
theorem packedReviewerArchitectureCapstone_holds
    (xs : List Int) (left right : Nat) :
    PackedReviewerArchitectureCapstone xs left right := by
  have certificate := packedReviewerRunAgainstMemory_public_certificate
    xs left right
  refine
    { payload_is_buildPayload := packedReviewerPayloadBits_eq_buildPayload xs
      serialized_header_payload := rfl
      padded_final_padding :=
        ⟨rfl, packedReviewerPaddedBits_length
          (SuccinctClassic.cartesianShape xs)⟩
      memory_uniform_builder :=
        packedReviewerMemoryUniformBuilder (SuccinctClassic.cartesianShape xs)
      run_factorization := rfl
      one_cell_width := fun cell hcell =>
        packedReviewerMemory_cell_length (SuccinctClassic.cartesianShape xs)
          hcell
      memory_length_arity :=
        packedReviewerMemory_length (SuccinctClassic.cartesianShape xs)
      allocation_two_n_plus_rho :=
        packedReviewerMemory_length_mul_width_le
          (SuccinctClassic.cartesianShape xs)
      rho_little_o := packedReviewerRho_littleO
      closed_length := fun n' lc sc =>
        packedReviewerClosedPayloadLength_eq n' lc sc
      width_positive :=
        packedReviewerCellWidth_pos (SuccinctClassic.cartesianShape xs).size
      input_size_fits_width := certificate.input_size_width
      width_logarithmic := certificate.word_width_logarithmic
      header_exactly_one_cell :=
        packedReviewerHeaderBits_length (SuccinctClassic.cartesianShape xs)
      header_fields_fit := certificate.header_values_width
      header_cell_zero :=
        packedReviewerMemory_header_cell (SuccinctClassic.cartesianShape xs)
      header_decodes :=
        packedReviewerHeaderBits_decode (SuccinctClassic.cartesianShape xs)
      run_opens_with_header := fun hleft hright =>
        packedReviewerRunOpensWithHeader (SuccinctClassic.cartesianShape xs)
          left right hleft hright
      header_liveness := fun hleft hright =>
        packedReviewerHeaderCellAddressLiveness_exact
          (SuccinctClassic.cartesianShape xs) left right hleft hright
      memory_only := certificate.memory_only
      probes_allocated_and_successful := fun event hevent =>
        ⟨certificate.allocated event hevent,
          certificate.reply_success event hevent⟩
      address_machine_width := certificate.address_width
      reply_exact_width := certificate.reply_width
      ordered_grouping := certificate.grouping
      probe_plan_crossing := fun _bit _width => rfl
      derived_cap_le_427 := certificate.trace_cap
      cap_structural_derivation := fun hleft hright => ?_
      guarded_reference_result :=
        ⟨certificate.terminal_eq, certificate.failed_false,
          certificate.state_eq⟩
      leftmost_tie_universal := fun hleft hright index hterm =>
        packedReviewerRunLeftmostTie xs left right hleft hright index hterm
      invalid_run_exact := fun hbad => ?_
      invalid_reference_none := fun hbad =>
        packedReviewerInvalidReferenceNone xs left right hbad
      controller_exact_input_boundary := rfl
      controller_uniform_entry := packedReviewerControllerUniformEntry
      store_agreement_determinism := fun memoryB hagree => ?_
      reachable_state_invariant :=
        packedReviewerRunReachableInvariant xs left right
      decisive_cell_liveness := packedReviewerDecisiveCellLiveness
      unread_cell_accept := packedReviewerUnreadCellAccept
      no_metadata_completion := packedReviewerNoMetadataCompletion
      valid_answer_is_index := fun hleft hright =>
        packedReviewerValidRunAnswersIndex xs left right hleft hright }
  · -- `cap_structural_derivation`
    have hvalid :
        left < right ∧
          right <= (SuccinctClassic.cartesianShape xs).size :=
      ⟨hleft, hright⟩
    have hcontroller :
        packedReviewerController (SuccinctClassic.cartesianShape xs).size
            left right =
          .header (SuccinctClassic.cartesianShape xs).size left right := by
      unfold packedReviewerController
      rw [if_pos hvalid]
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [hcontroller]
      rfl
    · exact packedReviewerWholeRemaining_start_eq_210
        (SuccinctClassic.cartesianShape xs).size left right (by omega)
    · exact packedReviewerControllerMeasure_valid_eq_427
        (SuccinctClassic.cartesianShape xs).size left right hvalid
  · -- `invalid_run_exact`
    have hcert :=
      packedReviewerRunAgainstMemory_invalid_certificate
        (SuccinctClassic.cartesianShape xs) left right hbad
    have htrace :=
      packedReviewerRunAgainstMemory_invalid_trace_eq_nil
        (SuccinctClassic.cartesianShape xs) left right hbad
    exact ⟨hcert.1, hcert.2.1, hcert.2.2.1, htrace⟩
  · -- `store_agreement_determinism`
    exact packedReviewerRunAgainstMemory_eq_of_agree
      (packedReviewerMemory (SuccinctClassic.cartesianShape xs)) memoryB
      (SuccinctClassic.cartesianShape xs).size left right
      (by
        simpa [PackedReviewerMemoriesAgreeOnRun,
          packedReviewerRunAgainstMemory] using hagree)

end PackedCellProbe

end SuccinctFinal

end RMQ
