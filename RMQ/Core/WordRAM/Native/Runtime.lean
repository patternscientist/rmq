import RMQ.Core.WordRAM.Native.Binary
import RMQ.Core.WordRAM.Native.Observations

/-! # Computational query boundary for loaded limb images

The image is retained between queries. Endpoint bytes have the same width as
stored words, so the API does not truncate endpoints to a host integer. The
host's allocation and fuel limits are checked separately from the abstract
all-size refinement. Native compiler/runtime and FFI assumptions are external
to these source theorems.
-/

namespace RMQ.SuccinctFinal.PackedNative
open PackedWordRAM

def nativeLimits : StorageImage.Limits :=
  ⟨134217728, 4096, 65536, 1000000, 1000000⟩

def nativeFuelLimit : Nat := 1000000

def nativeInputState (n left right : Nat) : State :=
  ⟨Registers.write (Registers.write (Registers.write (fun _ => 0) 0 left) 1 right) 2 n,
    0, .running⟩

def nativeInitialState (image : StorageImage) (left right : LimbWord.Word) : LimbMachine.State :=
  LimbMachine.State.encode image.width image.registerCount
    (nativeInputState image.inputLength (LimbWord.decode left) (LimbWord.decode right))

/-- This is the core used by the native query entry, on the arrays in the loaded
image. It does not construct a raw or limb transition list. -/
def nativeCore (image : StorageImage) (left right : LimbWord.Word) (fuel : Nat)
    (observeReads : Bool) : LimbMachine.State × Stats :=
  LimbMachine.runThin observeReads image.width image.memory image.code fuel
    (nativeInitialState image left right) {}

theorem nativeCore_source (image : StorageImage) (left right : LimbWord.Word)
    (fuel : Nat) (observeReads : Bool) :
    nativeCore image left right fuel observeReads =
      ((LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).final,
       (LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).transitions.foldl
          (LimbMachine.recordTransition observeReads) {}) :=
  LimbMachine.runThin_projection observeReads image.width image.memory image.code fuel
    (nativeInitialState image left right) {}

theorem nativeCore_no_reads (image : StorageImage) (left right : LimbWord.Word) (fuel : Nat) :
    (nativeCore image left right fuel false).2.readsRev = [] :=
  LimbMachine.runThin_no_reads image.width image.memory image.code fuel
    (nativeInitialState image left right) {}

def nativeObservationText (out : LimbMachine.State × Stats) : String :=
  let status := match out.1.status with
    | .running => "running"
    | .halted packet => "halted " ++ toString (LimbWord.decode packet)
    | .fault => "fault"
  let reads := out.2.readsRev.reverse.map fun receipt =>
    toString receipt.address ++ " " ++ match receipt.reply with
      | none => "none" | some value => toString value
  status ++ "\n" ++ toString out.2.steps ++ "\n" ++ countsText out.2.counts ++ "\n" ++
    String.intercalate "\n" reads ++ "\n"

def NativeQuerySupported (image : StorageImage) (left right : ByteArray) (fuel : Nat) : Prop :=
  0 < image.width ∧ image.width ≤ nativeLimits.maxWidth ∧
  3 ≤ image.registerCount ∧ image.registerCount ≤ nativeLimits.maxRegisters ∧
  image.inputLength < 2 ^ image.width ∧
  LimbWord.Canonical image.width left.data ∧ LimbWord.Canonical image.width right.data ∧
  fuel ≤ nativeFuelLimit

instance (image : StorageImage) (left right : ByteArray) (fuel : Nat) :
    Decidable (NativeQuerySupported image left right fuel) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Header bounds precede powers, register allocation and execution. Endpoint
lengths and high padding are checked before the endpoint is used. -/
def nativeEvaluate (image : StorageImage) (left right : ByteArray)
    (fuel : Nat) (observeReads : Bool) : Except String String := do
  if image.width = 0 ∨ nativeLimits.maxWidth < image.width ∨
      image.registerCount < 3 ∨ nativeLimits.maxRegisters < image.registerCount ∨
      nativeFuelLimit < fuel then
    throw "unsupported query domain"
  if !StorageImage.fits image.width image.inputLength ||
      !StorageImage.canonicalWord image.width left.data ||
      !StorageImage.canonicalWord image.width right.data then
    throw "noncanonical query word"
  pure (nativeObservationText (nativeCore image left.data right.data fuel observeReads))

theorem nativeEvaluate_source (image : StorageImage) (left right : ByteArray)
    (fuel : Nat) (observeReads : Bool) (h : NativeQuerySupported image left right fuel) :
    nativeEvaluate image left right fuel observeReads =
      .ok (nativeObservationText (nativeCore image left.data right.data fuel observeReads)) := by
  rcases h with ⟨hw, hwidth, hregs, hregisters, hn, hl, hr, hf⟩
  have hn' := (StorageImage.fits_iff image.width image.inputLength).2 hn
  have hl' := (StorageImage.canonicalWord_iff image.width left.data).2 hl
  have hr' := (StorageImage.canonicalWord_iff image.width right.data).2 hr
  simp [nativeEvaluate, show image.width ≠ 0 by omega,
    show ¬ nativeLimits.maxWidth < image.width by omega,
    show ¬ image.registerCount < 3 by omega,
    show ¬ nativeLimits.maxRegisters < image.registerCount by omega,
    show ¬ nativeFuelLimit < fuel by omega, hn', hl', hr']
  rfl

theorem nativeInitialState_decode (image : StorageImage) (left right : LimbWord.Word)
    (hregs : 3 ≤ image.registerCount)
    (hn : image.inputLength < 2 ^ image.width)
    (hl : LimbWord.Canonical image.width left) (hr : LimbWord.Canonical image.width right) :
    (nativeInitialState image left right).decode =
      nativeInputState image.inputLength (LimbWord.decode left) (LimbWord.decode right) := by
  apply LimbMachine.State.decode_encode
  · refine ⟨Nat.pow_pos (by decide), ?_, ?_⟩
    · intro r
      simp only [nativeInputState, Registers.write]
      split <;> try assumption
      split <;> try exact hr.2
      split <;> try exact hl.2
      exact Nat.pow_pos (by decide)
    · intro value h
      cases h
  · intro r hb
    simp [nativeInputState, Registers.write,
      show r ≠ 2 by omega, show r ≠ 1 by omega, show r ≠ 0 by omega]

end RMQ.SuccinctFinal.PackedNative
