import RMQ.Core.WordRAM.Native.Lifecycle.Run

/-! # Value transport across native array replacement

A successful native copy must preserve the initialized size and each entry of
all four arrays, together with both control scalars. This interface entails
equality of Lean owner values. It asserts neither pointer equality nor native
capacity, exclusive ownership, allocation success, or correctness of C copying.
Those obligations belong to the foreign boundary and its measured controls.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle

structure ArrayCopy {α : Type} (source target : Array α) : Prop where
  size : target.size = source.size
  entry : ∀ (i : Nat) (ht : i < target.size) (hs : i < source.size), target[i] = source[i]

theorem ArrayCopy.eq {α : Type} {source target : Array α}
    (copy : ArrayCopy source target) : target = source := by
  apply Array.ext copy.size
  exact copy.entry

theorem ArrayCopy.refl {α : Type} (array : Array α) : ArrayCopy array array :=
  ⟨rfl, fun _ _ _ => rfl⟩

structure Repacked (source target : Owner) : Prop where
  regs : ArrayCopy source.regs target.regs
  memory : ArrayCopy source.memory target.memory
  keys : ArrayCopy source.keys target.keys
  keyRegs : ArrayCopy source.keyRegs target.keyRegs
  pc : target.pc = source.pc
  status : target.status = source.status

theorem Repacked.eq {source target : Owner} (copy : Repacked source target) :
    target = source := by
  rcases source with ⟨sr, sm, sk, skr, sp, ss⟩
  rcases target with ⟨tr, tm, tk, tkr, tp, ts⟩
  obtain ⟨hr, hm, hk, hkr, hp, hs⟩ := copy
  have er := hr.eq
  have em := hm.eq
  have ek := hk.eq
  have ekr := hkr.eq
  cases er
  cases em
  cases ek
  cases ekr
  cases hp
  cases hs
  rfl

theorem Repacked.refl (owner : Owner) : Repacked owner owner :=
  ⟨ArrayCopy.refl _, ArrayCopy.refl _, ArrayCopy.refl _, ArrayCopy.refl _, rfl, rfl⟩

theorem repack_transport (xs : List Int) (model : InputModel) (left right : Nat)
    (source target : Owner) (copy : Repacked source target) :
    target = source ∧ target.toState = source.toState ∧ target.status = source.status ∧
      (Ownership.Ready xs target ↔ Ownership.Ready xs source) ∧
      Ownership.capacity model target = Ownership.capacity model source ∧
      query model left right target = query model left right source := by
  rw [copy.eq]
  exact ⟨rfl, rfl, rfl, Iff.rfl, rfl, rfl⟩

end RMQ.SuccinctFinal.PackedNative.Lifecycle
