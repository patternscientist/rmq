import RMQ.Core.WordRAM.Native.Runtime
import RMQ.Core.WordRAM.Native.Binary.Cursor

/-! # Exported computational declarations consumed by the C ABI

The build checks these actual generated C exports. The source proofs below
identify byte loading and query evaluation; they do not assert correctness of
Lean/C compilation, linking, the foreign runtime or caller pointer contracts.
-/

namespace RMQ.SuccinctFinal.PackedNative

@[export rmq_native_load]
def nativeLoadEntry (bytes : ByteArray) : Except String StorageImage :=
  match BinaryCursor.decodeSupported nativeLimits bytes with
  | some image => .ok image
  | none => .error "invalid or unsupported binary image"

theorem nativeLoadEntry_source (bytes : ByteArray) :
    nativeLoadEntry bytes =
      match StorageImage.decodeSupported nativeLimits bytes with
      | some image => .ok image
      | none => .error "invalid or unsupported binary image" := by
  unfold nativeLoadEntry
  rw [BinaryCursor.decodeSupported_eq]

@[export rmq_native_query]
def nativeQueryEntry (image : StorageImage) (left right : ByteArray)
    (fuel : Nat) (observeReads : Bool) : Except String String :=
  nativeEvaluate image left right fuel observeReads

theorem nativeQueryEntry_source (image : StorageImage) (left right : ByteArray)
    (fuel : Nat) (observeReads : Bool) (h : NativeQuerySupported image left right fuel) :
    nativeQueryEntry image left right fuel observeReads =
      .ok (nativeObservationText (nativeCore image left.data right.data fuel observeReads)) :=
  nativeEvaluate_source image left right fuel observeReads h

@[export rmq_native_word_bytes]
def nativeWordBytes (image : StorageImage) : USize :=
  (LimbWord.limbCount image.width).toUSize

theorem nativeWordBytes_exact (image : StorageImage)
    (hw : image.width ≤ nativeLimits.maxWidth) :
    (nativeWordBytes image).toNat = LimbWord.limbCount image.width ∧
      (nativeWordBytes image).toNat ≤ 512 := by
  have hb : LimbWord.limbCount image.width ≤ 512 := by
    change image.width ≤ 4096 at hw
    unfold LimbWord.limbCount
    omega
  have he : (nativeWordBytes image).toNat = LimbWord.limbCount image.width :=
    USize.toNat_ofNat_of_lt_32 (by omega)
  exact ⟨he, by rw [he]; exact hb⟩

end RMQ.SuccinctFinal.PackedNative
