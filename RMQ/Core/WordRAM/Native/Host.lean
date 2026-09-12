import RMQ.Core.WordRAM.Native.Entry
import RMQ.Core.WordRAM.Native.Machine.CodeFacts

/-! # Checked finite-host bounds at the loaded-image boundary -/
namespace RMQ.SuccinctFinal.PackedNative

theorem nativeLoadEntry_success (bytes : ByteArray) (image : StorageImage)
    (h : nativeLoadEntry bytes = .ok image) :
    bytes = image.encode ∧ image.Valid ∧ image.Supported nativeLimits := by
  unfold nativeLoadEntry at h
  cases hd : BinaryCursor.decodeSupported nativeLimits bytes with
  | none => simp [hd] at h
  | some loaded =>
    simp only [hd, Except.ok.injEq] at h
    subst loaded
    exact (BinaryCursor.decodeSupported_iff nativeLimits bytes image).1 hd

theorem nativeHostBounds (image : StorageImage) (h : image.Supported nativeLimits) :
    image.encode.size < USize.size ∧ image.registerCount < USize.size ∧
    image.code.size < USize.size ∧ image.memory.size < USize.size := by
  rcases h with ⟨hf, hw, hr, hc, hm⟩
  change image.encode.size ≤ 134217728 at hf
  change image.registerCount ≤ 65536 at hr
  change image.code.size ≤ 1000000 at hc
  change image.memory.size ≤ 1000000 at hm
  have hu := USize.le_size
  omega

theorem nativeLoadedProgram (bytes : ByteArray) (image : StorageImage)
    (h : nativeLoadEntry bytes = .ok image) :
    ∃ program : PackedWordRAM.Program,
      image.code = LimbMachine.encodeCode image.width program ∧
      ∀ instruction ∈ program, instruction.Fits image.width := by
  have hv := (StorageImage.valid_iff image).1 (nativeLoadEntry_success bytes image h).2.1
  apply LimbMachine.code_exists_program
  intro fields hfields
  obtain ⟨hs, hc, instruction, hi⟩ := hv.2.2.2.1 fields hfields
  exact ⟨instruction, LimbMachine.decodeInstruction_of_canonical _ _ _ hs hc hi⟩

/-- A successful actual array lookup has an untruncated host address. Missing
lookups remain `none`; their possibly huge Nat address is never claimed to fit. -/
theorem nativeMemoryLookup (image : StorageImage) (address : Nat) (word : LimbWord.Word)
    (hs : image.Supported nativeLimits) (hr : image.memory[address]? = some word) :
    address < image.memory.size ∧ address < USize.size ∧ address.toUSize.toNat = address := by
  obtain ⟨ha, _⟩ := Array.getElem?_eq_some_iff.mp hr
  have hu := Nat.lt_trans ha (nativeHostBounds image hs).2.2.2
  exact ⟨ha, hu, USize.toNat_ofNat_of_lt' hu⟩

theorem nativeCodeLookup (image : StorageImage) (pc : Nat) (fields : Array LimbWord.Word)
    (hs : image.Supported nativeLimits) (hr : image.code[pc]? = some fields) :
    pc < image.code.size ∧ pc < USize.size ∧ pc.toUSize.toNat = pc := by
  obtain ⟨ha, _⟩ := Array.getElem?_eq_some_iff.mp hr
  have hu := Nat.lt_trans ha (nativeHostBounds image hs).2.2.1
  exact ⟨ha, hu, USize.toNat_ofNat_of_lt' hu⟩

end RMQ.SuccinctFinal.PackedNative
