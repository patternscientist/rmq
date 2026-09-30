import RMQ.Core.WordRAM.Native.Lifecycle.Codec
import RMQ.Core.WordRAM.Lifecycle.Input

/-! # Checked lifecycle input and request admission

The word model checks the existing signed biased input domain. The comparison
model accepts arbitrary finite Lean integers. Endpoint checks impose only the
modeled word representation: empty, reversed and out-of-bounds represented
intervals are executed by the lifecycle guard. Count and wire-size ceilings
are explicitly native limits and do not restrict the all-size export theorem.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle (InputModel InputDomain)
open PackedWordRAM (wordWidth)

def nativeCountLimit : Nat := 4096
def nativeMagnitudeBudget : Nat := 16777216

/-- The actual lifecycle profile has no unused high endpoint bits. Malformed
padding is a generic codec case, not a reachable native-profile case. -/
theorem word_profile_byte_aligned (count : Nat) : wordWidth count % 8 = 0 := by
  unfold wordWidth
  omega

theorem nativeCount_toUSize_exact (count : Nat) (bounded : count ≤ nativeCountLimit) :
    (USize.ofNat count).toNat = count := by
  apply USize.toNat_ofNat_of_lt_32
  change count ≤ 4096 at bounded
  omega

/-- The foreign boundary validates its byte flag before converting to Bool. -/
def modelOfComparison (comparison : Bool) : InputModel :=
  if comparison then .comparison else .word

@[simp] theorem modelOfComparison_false : modelOfComparison false = .word := rfl
@[simp] theorem modelOfComparison_true : modelOfComparison true = .comparison := rfl

def inputDomainCheck (model : InputModel) (xs : List Int) : Bool :=
  match model with
  | .word => decide (0 < wordWidth xs.length ∧ xs.length < 2 ^ wordWidth xs.length ∧
      ∀ x ∈ xs, 0 < wordWidth xs.length ∧
        -((2 ^ (wordWidth xs.length - 1) : Nat) : Int) ≤ x ∧
        x < ((2 ^ (wordWidth xs.length - 1) : Nat) : Int))
  | .comparison => true

theorem inputDomainCheck_iff (model : InputModel) (xs : List Int) :
    inputDomainCheck model xs = true ↔ InputDomain model xs := by
  cases model <;> simp [inputDomainCheck, InputDomain,
    PackedConstruction.InputFits, PackedConstruction.SignedFits]

def QueryRepresented (width : Nat) (left right : ByteArray) : Prop :=
  LimbWord.Canonical width left.data ∧ LimbWord.Canonical width right.data

instance (width : Nat) (left right : ByteArray) : Decidable (QueryRepresented width left right) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- This check is pure and requires no operational owner to be taken. -/
def queryAdmission (width : Nat) (left right : ByteArray) : Bool :=
  decide (QueryRepresented width left right)

theorem queryAdmission_iff (width : Nat) (left right : ByteArray) :
    queryAdmission width left right = true ↔ QueryRepresented width left right := by
  simp [queryAdmission]

theorem queryAdmission_success (width : Nat) (left right : ByteArray)
    (accepted : queryAdmission width left right = true) :
    left.size = LimbWord.limbCount width ∧ right.size = LimbWord.limbCount width ∧
      decodeMagnitude left < 2 ^ width ∧ decodeMagnitude right < 2 ^ width := by
  have h := (queryAdmission_iff width left right).1 accepted
  exact ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩

theorem queryAdmission_encoded (width left right : Nat)
    (hl : left < 2 ^ width) (hr : right < 2 ^ width) :
    queryAdmission width (encodeEndpoint width left) (encodeEndpoint width right) = true :=
  (queryAdmission_iff _ _ _).2
    ⟨(encodeEndpoint_canonical _ _ hl).1, (encodeEndpoint_canonical _ _ hr).1⟩

def BuildAdmitted (model : InputModel) (xs : List Int) (suppliedCount : Nat)
    (left right : ByteArray) : Prop :=
  suppliedCount = xs.length ∧ xs.length ≤ nativeCountLimit ∧
    InputDomain model xs ∧ QueryRepresented (wordWidth xs.length) left right

def buildAdmission (model : InputModel) (xs : List Int) (suppliedCount : Nat)
    (left right : ByteArray) : Bool :=
  decide (suppliedCount = xs.length ∧ xs.length ≤ nativeCountLimit) &&
    inputDomainCheck model xs && queryAdmission (wordWidth xs.length) left right

theorem buildAdmission_iff (model : InputModel) (xs : List Int) (suppliedCount : Nat)
    (left right : ByteArray) :
    buildAdmission model xs suppliedCount left right = true ↔
      BuildAdmitted model xs suppliedCount left right := by
  simp [buildAdmission, BuildAdmitted, inputDomainCheck_iff, queryAdmission_iff, and_assoc]

/-- Successful admission exposes the exact domain and endpoint arguments used
by the first lifecycle invocation, together with the actual supplied count. -/
theorem buildAdmission_success (model : InputModel) (xs : List Int) (suppliedCount : Nat)
    (left right : ByteArray)
    (accepted : buildAdmission model xs suppliedCount left right = true) :
    suppliedCount = xs.length ∧ xs.length ≤ nativeCountLimit ∧ InputDomain model xs ∧
      left.size = LimbWord.limbCount (wordWidth xs.length) ∧
      right.size = LimbWord.limbCount (wordWidth xs.length) ∧
      decodeMagnitude left < 2 ^ wordWidth xs.length ∧
      decodeMagnitude right < 2 ^ wordWidth xs.length := by
  obtain ⟨count, bounded, domain, represented⟩ := (buildAdmission_iff _ _ _ _ _).1 accepted
  exact ⟨count, bounded, domain, represented.1.1, represented.2.1,
    represented.1.2, represented.2.2⟩

theorem buildAdmission_word_bias (xs : List Int) (suppliedCount : Nat)
    (left right : ByteArray)
    (accepted : buildAdmission .word xs suppliedCount left right = true) :
    ∀ x ∈ xs, (PackedConstruction.encodeInt (wordWidth xs.length) x : Int) =
      x + ((2 ^ (wordWidth xs.length - 1) : Nat) : Int) := by
  intro x member
  have domain := (buildAdmission_success _ _ _ _ _ accepted).2.2.1
  exact PackedConstruction.encodeInt_asInt (domain.2.2 x member)

theorem buildAdmission_word_rejects (xs : List Int) (suppliedCount : Nat)
    (left right : ByteArray)
    (outside : ¬ PackedConstruction.InputFits (wordWidth xs.length) xs) :
    buildAdmission .word xs suppliedCount left right = false := by
  cases result : buildAdmission .word xs suppliedCount left right with
  | false => rfl
  | true => exact False.elim (outside (buildAdmission_success _ _ _ _ _ result).2.2.1)

/-- The foreign parser supplies exactly this sign/magnitude sequence. It does
not retain the sequence after constructing the decoded input list. -/
structure SignedBytes where
  negative : Bool
  magnitude : ByteArray

def decodeInputs (inputs : List SignedBytes) : List Int :=
  inputs.map fun input => decodeSigned input.negative input.magnitude

def NativeInputFormat (inputs : List SignedBytes) : Prop :=
  inputs.length ≤ nativeCountLimit ∧
    (∀ input ∈ inputs, SignedFormat input.negative input.magnitude) ∧
    (inputs.map fun input => input.magnitude.size).sum ≤ nativeMagnitudeBudget

instance (inputs : List SignedBytes) : Decidable (NativeInputFormat inputs) :=
  inferInstanceAs (Decidable (_ ∧ _))

def nativeInputFormat (inputs : List SignedBytes) : Bool := decide (NativeInputFormat inputs)

theorem nativeInputFormat_iff (inputs : List SignedBytes) :
    nativeInputFormat inputs = true ↔ NativeInputFormat inputs := by
  simp [nativeInputFormat]

def encodedBuildAdmission (model : InputModel) (inputs : List SignedBytes)
    (left right : ByteArray) : Bool :=
  nativeInputFormat inputs && buildAdmission model (decodeInputs inputs) inputs.length left right

@[simp] theorem decodeInputs_length (inputs : List SignedBytes) :
    (decodeInputs inputs).length = inputs.length := by simp [decodeInputs]

theorem decodeInputs_getElem? (inputs : List SignedBytes) (i : Nat) :
    (decodeInputs inputs)[i]? =
      (inputs[i]?).map (fun input => decodeSigned input.negative input.magnitude) := by
  simp [decodeInputs]

theorem decodeInputs_encoded (count : Nat) (xs : List Int)
    (fits : ∀ x ∈ xs, x.natAbs < 256 ^ count) :
    decodeInputs (xs.map (fun value =>
      (⟨signedNegative value, encodeSigned count value⟩ : SignedBytes))) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change decodeSigned (signedNegative x) (encodeSigned count x) ::
        decodeInputs (xs.map (fun value =>
          (⟨signedNegative value, encodeSigned count value⟩ : SignedBytes))) = x :: xs
      rw [decodeSigned_encodeSigned count x (fits x (by simp))]
      rw [ih (fun value member => fits value (by simp [member]))]

/-- Full successful wire admission exposes per-element format, the total-byte
ceiling, exact count, input model, and both represented endpoint bounds. -/
theorem encodedBuildAdmission_success (model : InputModel) (inputs : List SignedBytes)
    (left right : ByteArray)
    (accepted : encodedBuildAdmission model inputs left right = true) :
    inputs.length ≤ nativeCountLimit ∧
      (∀ input ∈ inputs, SignedFormat input.negative input.magnitude) ∧
      (inputs.map fun input => input.magnitude.size).sum ≤ nativeMagnitudeBudget ∧
      (decodeInputs inputs).length = inputs.length ∧
      InputDomain model (decodeInputs inputs) ∧
      QueryRepresented (wordWidth inputs.length) left right := by
  have parts : nativeInputFormat inputs = true ∧
      buildAdmission model (decodeInputs inputs) inputs.length left right = true := by
    simpa only [encodedBuildAdmission, Bool.and_eq_true] using accepted
  have format := (nativeInputFormat_iff _).1 parts.1
  have admitted := (buildAdmission_iff _ _ _ _ _).1 parts.2
  exact ⟨format.1, format.2.1, format.2.2, decodeInputs_length _, admitted.2.2.1,
    by simpa only [decodeInputs_length] using admitted.2.2.2⟩

theorem encodedBuildAdmission_iff (model : InputModel) (inputs : List SignedBytes)
    (left right : ByteArray) :
    encodedBuildAdmission model inputs left right = true ↔
      NativeInputFormat inputs ∧ InputDomain model (decodeInputs inputs) ∧
        QueryRepresented (wordWidth inputs.length) left right := by
  constructor
  · intro accepted
    have h := encodedBuildAdmission_success _ _ _ _ accepted
    exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2.2.1, h.2.2.2.2.2⟩
  · rintro ⟨format, domain, query⟩
    have admitted : BuildAdmitted model (decodeInputs inputs) inputs.length left right :=
      ⟨(decodeInputs_length inputs).symm, by simpa using format.1, domain,
        by simpa only [decodeInputs_length] using query⟩
    simp only [encodedBuildAdmission, Bool.and_eq_true]
    exact ⟨(nativeInputFormat_iff _).2 format, (buildAdmission_iff _ _ _ _ _).2 admitted⟩

/-- The C parser's format checks and this Lean admission check compose at the
same decoded list. No output equality or trusted duplicate count is assumed. -/
theorem represented_input_bridge (inputs : List SignedBytes) (model : InputModel)
    (left right : ByteArray) (format : NativeInputFormat inputs)
    (domain : inputDomainCheck model (decodeInputs inputs) = true)
    (query : queryAdmission (wordWidth inputs.length) left right = true) :
    buildAdmission model (decodeInputs inputs) inputs.length left right = true ∧
      InputDomain model (decodeInputs inputs) ∧
      decodeMagnitude left < 2 ^ wordWidth inputs.length ∧
      decodeMagnitude right < 2 ^ wordWidth inputs.length := by
  have hd := (inputDomainCheck_iff _ _).1 domain
  have hq := (queryAdmission_iff _ _ _).1 query
  refine ⟨(buildAdmission_iff _ _ _ _ _).2 ?_, hd, hq.1.2, hq.2.2⟩
  exact ⟨(decodeInputs_length inputs).symm, by simpa using format.1, hd,
    by simpa only [decodeInputs_length] using hq⟩

end RMQ.SuccinctFinal.PackedNative.Lifecycle
