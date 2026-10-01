import RMQ.Core.WordRAM.Native.Lifecycle.Admission
import RMQ.Core.WordRAM.Native.Lifecycle.Run
import RMQ.Core.WordRAM.Native.Lifecycle.Observations

/-! # Computational exports for the consuming lifecycle ABI

These declarations expose the existing lifecycle evaluator. Foreign pointer
validity, reference ownership, native array capacity and compiler correctness
are outside the kernel propositions. Admission is a separate operation before
the foreign caller transfers an operational owner.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle (Owner InputModel)
open PackedWordRAM (wordWidth)

@[export rmq_lifecycle_decode_signed]
def nativeDecodeSigned (negative : Bool) (magnitude : ByteArray) : Int :=
  decodeSigned negative magnitude

@[export rmq_lifecycle_signed_format]
def nativeSignedFormat (negative : Bool) (magnitude : ByteArray) : Bool :=
  signedFormat negative magnitude

@[export rmq_lifecycle_profile]
def nativeProfile (count : Nat) : Nat := wordWidth count

@[export rmq_lifecycle_admit]
def nativeAdmit (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) : Bool :=
  buildAdmission (modelOfComparison comparison) xs count left right

@[export rmq_lifecycle_build_first]
def nativeBuildFirst (comparison : Bool) (xs : List Int) (left right : ByteArray) : Owner :=
  buildFirst (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right)

/-- Split at the actual initial owner so the native boundary can inspect and
measure construction roots before consuming them. No reference payload enters
this interface. The count is the successfully admitted decoded list length. -/
@[export rmq_lifecycle_initial]
def nativeInitial (comparison : Bool) (xs : List Int) (left right : ByteArray) : Owner :=
  PackedLifecycle.Executable.initialOwner (modelOfComparison comparison) xs
    (decodeMagnitude left) (decodeMagnitude right)

@[export rmq_lifecycle_run_first]
def nativeRunFirst (comparison : Bool) (count : Nat) (owner : Owner) : Owner :=
  runThin (cachedProgram (modelOfComparison comparison))
    (PackedLifecycle.Continuous.lifecycleBudget count) owner

/-- A bounded-call surface for testing status classification. Canonical admitted
production calls use the proved full budget; this general runner changes no
primitive and makes no claim that injected fault states are valid inputs. -/
@[export rmq_lifecycle_run_fuel]
def nativeRunFuel (comparison : Bool) (fuel : Nat) (owner : Owner) : Owner :=
  runThin (cachedProgram (modelOfComparison comparison)) fuel owner

theorem nativeRunFuel_source (comparison : Bool) (fuel : Nat) (owner : Owner) :
    nativeRunFuel comparison fuel owner =
      PackedLifecycle.runOwner
        (PackedLifecycle.Layout.program (modelOfComparison comparison)).toArray fuel owner := by
  unfold nativeRunFuel
  rw [runThin_eq_runOwner, cachedProgram_eq]

theorem nativeInitial_runFirst (comparison : Bool) (xs : List Int) (left right : ByteArray) :
    nativeRunFirst comparison xs.length (nativeInitial comparison xs left right) =
      nativeBuildFirst comparison xs left right := rfl

/-- Metadata is read from the actual produced memory, not caller duplicates. -/
@[export rmq_lifecycle_metadata]
def nativeMetadata (owner : Owner) (address : Nat) : Option Nat :=
  owner.memory.getD address none

def producedCount (owner : Owner) : Nat :=
  (nativeMetadata owner 0).getD 0

@[export rmq_lifecycle_query_admit]
def nativeQueryAdmit (owner : Owner) (left right : ByteArray) : Bool :=
  queryAdmission (wordWidth (producedCount owner)) left right

@[export rmq_lifecycle_query]
def nativeQuery (comparison : Bool) (left right : ByteArray) (owner : Owner) : Owner :=
  query (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner

/-- The answer packet stays a Nat until fixed-width byte encoding. -/
@[export rmq_lifecycle_packet]
def nativePacket (owner : Owner) : ByteArray :=
  match owner.status with
  | .halted packet => encodeEndpoint (wordWidth (producedCount owner)) packet
  | _ => ByteArray.empty

@[export rmq_lifecycle_status]
def nativeStatus (owner : Owner) : UInt8 :=
  match owner.status with
  | .running => 0
  | .halted _ => 1
  | .fault => 2

@[export rmq_lifecycle_build_first_observed]
def nativeBuildFirstObserved (comparison : Bool) (xs : List Int)
    (left right : ByteArray) : Owner × Observations.Stats :=
  Observations.buildFirst (modelOfComparison comparison) xs
    (decodeMagnitude left) (decodeMagnitude right)

@[export rmq_lifecycle_run_first_observed]
def nativeRunFirstObserved (comparison : Bool) (count : Nat)
    (owner : Owner) : Owner × Observations.Stats :=
  Observations.run (cachedProgram (modelOfComparison comparison))
    (PackedLifecycle.Continuous.lifecycleBudget count) owner

theorem nativeInitial_runFirstObserved (comparison : Bool) (xs : List Int)
    (left right : ByteArray) :
    nativeRunFirstObserved comparison xs.length (nativeInitial comparison xs left right) =
      nativeBuildFirstObserved comparison xs left right := rfl

@[export rmq_lifecycle_query_observed]
def nativeQueryObserved (comparison : Bool) (left right : ByteArray)
    (owner : Owner) : Owner × Observations.Stats :=
  Observations.query (modelOfComparison comparison) (decodeMagnitude left)
    (decodeMagnitude right) owner

/-- The ABI rejects category IDs outside 0..15 before calling this projection. -/
def observationCategories : Array PackedLifecycle.Category :=
  #[.old .read, .old .register, .old .arithmetic, .old .comparison, .old .branch,
    .old .control, .old .write, .old .allocation, .old .keyRead,
    .old .oracleComparison, .numericRelease, .keyRelease, .keyRegisterRelease,
    .requestAdmission, .controlEntry]

@[export rmq_lifecycle_observation_counter]
def nativeObservationCounter (stats : Observations.Stats) (category : UInt8) : Nat :=
  if category = 15 then stats.steps
  else stats.counts.get (observationCategories[category.toNat]?.getD (.old .read))

@[export rmq_lifecycle_observation_reads]
def nativeObservationReads (stats : Observations.Stats) : Array (Nat × Option Nat) :=
  stats.reads.toArray

def observationRouteMarks : Array Observations.RouteMark :=
  #[.compactQuery, .servicePrepare, .serviceSetup, .builder, .descriptor,
    .finalizer, .retirement, .sameBlockDecision, .crossBlockDecision,
    .interiorNonemptyDecision, .interiorEmptyDecision, .interiorReadMarker,
    .crossingSecondLoad]

@[export rmq_lifecycle_observation_route]
def nativeObservationRoute (stats : Observations.Stats) (mark : UInt8) : Nat :=
  stats.routes.get (observationRouteMarks[mark.toNat]?.getD .compactQuery)

@[export rmq_lifecycle_signature_count]
def nativeSignatureCount (comparison : Bool) (mark : UInt8) : Nat :=
  Observations.programSignatureCount (modelOfComparison comparison)
    (observationRouteMarks[mark.toNat]?.getD .compactQuery)

@[export rmq_lifecycle_encode_natural]
def nativeEncodeNatural (value : Nat) : ByteArray := encodeNatural value

/-- Borrowing/sharing this fixed code at the foreign boundary is separate from
the exclusive operational owner; it has no input-specific data. -/
@[export rmq_lifecycle_program]
def nativeProgram (comparison : Bool) : Array PackedLifecycle.Instruction :=
  cachedProgram (modelOfComparison comparison)

theorem nativeBuildFirstObserved_owner (comparison : Bool) (xs : List Int)
    (left right : ByteArray) :
    (nativeBuildFirstObserved comparison xs left right).1 =
      nativeBuildFirst comparison xs left right :=
  Observations.buildFirst_owner _ _ _ _

theorem nativeQueryObserved_owner (comparison : Bool) (left right : ByteArray)
    (owner : Owner) : (nativeQueryObserved comparison left right owner).1 =
      nativeQuery comparison left right owner :=
  Observations.query_owner _ _ _ _

theorem nativeBuildFirst_source (comparison : Bool) (xs : List Int) (left right : ByteArray) :
    nativeBuildFirst comparison xs left right =
      buildFirst (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) := rfl

theorem nativeQuery_source (comparison : Bool) (left right : ByteArray) (owner : Owner) :
    nativeQuery comparison left right owner =
      query (modelOfComparison comparison) (decodeMagnitude left) (decodeMagnitude right) owner := rfl

theorem nativeAdmit_source (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) :
    nativeAdmit comparison xs count left right = true ↔
      BuildAdmitted (modelOfComparison comparison) xs count left right :=
  buildAdmission_iff _ _ _ _ _

end RMQ.SuccinctFinal.PackedNative.Lifecycle
