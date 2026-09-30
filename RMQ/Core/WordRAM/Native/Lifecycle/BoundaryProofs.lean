import RMQ.Core.WordRAM.Native.Lifecycle.Entry
import RMQ.Core.WordRAM.Native.Lifecycle.Contract

/-! # Exact metadata, admission, and packet boundary

The native entry points use the same produced owner and arbitrary-precision
packet as the source lifecycle. Byte canonicality and exact decoding are
derived here; neither the returned answer nor its fit is an admission premise.
The byte and owner operations still rely on the generated-code/FFI boundary.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle
open PackedWordRAM (wordWidth optionNatPacket)

theorem nativeInitial_runFirst_admitted (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativeRunFirst comparison count (nativeInitial comparison xs left right) =
      nativeBuildFirst comparison xs left right := by
  have count_eq := ((nativeAdmit_source comparison xs count left right).1 accepted).1
  rw [count_eq]
  exact nativeInitial_runFirst comparison xs left right

theorem nativeInitial_runFirstObserved_admitted (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativeRunFirstObserved comparison count (nativeInitial comparison xs left right) =
      nativeBuildFirstObserved comparison xs left right := by
  have count_eq := ((nativeAdmit_source comparison xs count left right).1 accepted).1
  rw [count_eq]
  exact nativeInitial_runFirstObserved comparison xs left right

theorem nativeMetadata_ready {xs : List Int} {owner : Owner}
    (ready : Ownership.Ready xs owner) :
    nativeMetadata owner 0 = some xs.length ∧
      nativeMetadata owner 7 = some owner.memory.size :=
  ready_metadata ready

theorem producedCount_ready {xs : List Int} {owner : Owner}
    (ready : Ownership.Ready xs owner) : producedCount owner = xs.length := by
  simp only [producedCount, (nativeMetadata_ready ready).1, Option.getD_some]

theorem buildFirst_metadata (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    producedCount (buildFirst model xs left right) = xs.length ∧
      nativeMetadata (buildFirst model xs left right) 0 = some xs.length ∧
      nativeMetadata (buildFirst model xs left right) 7 =
        some (buildFirst model xs left right).memory.size := by
  have ready : Ownership.Ready xs (buildFirst model xs left right) := by
    rw [buildFirst_eq]
    exact Ownership.ready model xs left right domain hl hr
  exact ⟨producedCount_ready ready, nativeMetadata_ready ready⟩

theorem nativeQueryAdmit_iff (xs : List Int) (owner : Owner) (left right : ByteArray)
    (ready : Ownership.Ready xs owner) :
    nativeQueryAdmit owner left right = true ↔
      LimbWord.Canonical (wordWidth xs.length) left.data ∧
        LimbWord.Canonical (wordWidth xs.length) right.data := by
  rw [nativeQueryAdmit, producedCount_ready ready]
  exact queryAdmission_iff _ _ _

/-- The packet is bounded independently of a returned owner: the valid branch
is an index plus one at most the input length, and the invalid branch is zero. -/
theorem answer_packet_fits (xs : List Int) (left right : Nat) :
    optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value <
      2 ^ wordWidth xs.length := by
  have capacity := PackedWordRAM.size_lt_wordCapacity xs.length
  rw [PackedWordRAM.queryTraceResult_value_reference]
  by_cases valid : ValidRange xs left right
  · simp only [if_pos valid, optionNatPacket, Option.map_some, Option.getD_some]
    have bounds := Cartesian.scanWindow_bounds xs left (right - left)
      (Nat.sub_pos_of_lt valid.1)
    have hleft := valid.1
    have hright := valid.2
    omega
  · simp only [if_neg valid, optionNatPacket, Option.map_none, Option.getD_none]
    omega

theorem nativePacket_exact (xs : List Int) (owner : Owner) (packet : Nat)
    (ready : Ownership.Ready xs owner) (halted : owner.status = .halted packet)
    (fits : packet < 2 ^ wordWidth xs.length) :
    nativePacket owner = encodeEndpoint (wordWidth xs.length) packet ∧
      LimbWord.Canonical (wordWidth xs.length) (nativePacket owner).data ∧
      decodeMagnitude (nativePacket owner) = packet := by
  have encoded : nativePacket owner = encodeEndpoint (wordWidth xs.length) packet := by
    simp only [nativePacket, halted, producedCount_ready ready]
  rw [encoded]
  exact ⟨rfl, encodeEndpoint_canonical _ _ fits⟩

/-- The packet refinement retains the all-size source domain. Native admission
ceilings are introduced only in the admitted ABI theorem below. -/
theorem buildFirst_packet (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    nativePacket (buildFirst model xs left right) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    LimbWord.Canonical (wordWidth xs.length) (nativePacket (buildFirst model xs left right)).data ∧
    decodeMagnitude (nativePacket (buildFirst model xs left right)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value := by
  rw [buildFirst_eq]
  exact nativePacket_exact xs _ _ (Ownership.ready model xs left right domain hl hr)
    (Ownership.halted model xs left right domain hl hr) (answer_packet_fits xs left right)

theorem query_packet (model : InputModel) (xs : List Int) (owner : Owner)
    (left right answer : Nat) (ready : Ownership.Ready xs owner)
    (halted : owner.status = .halted answer)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    nativePacket (query model left right owner) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    LimbWord.Canonical (wordWidth xs.length) (nativePacket (query model left right owner)).data ∧
    decodeMagnitude (nativePacket (query model left right owner)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value := by
  rw [query_eq]
  have reuse := ready.query model left right answer halted hl hr
  exact nativePacket_exact xs _ _ reuse.1 reuse.2.1 (answer_packet_fits xs left right)

theorem nativeBuildFirst_correct (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativeBuildFirst comparison xs left right = Ownership.owner (modelOfComparison comparison) xs
      (decodeMagnitude left) (decodeMagnitude right) ∧
    Ownership.Ready xs (nativeBuildFirst comparison xs left right) ∧
    (nativeBuildFirst comparison xs left right).status = .halted
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) := by
  obtain ⟨_, _, domain, represented⟩ := (nativeAdmit_source _ _ _ _ _).1 accepted
  have source : nativeBuildFirst comparison xs left right =
      Ownership.owner (modelOfComparison comparison) xs (decodeMagnitude left) (decodeMagnitude right) :=
    buildFirst_eq _ _ _ _
  rw [source]
  exact ⟨rfl, Ownership.ready _ _ _ _ domain represented.1.2 represented.2.2,
    Ownership.halted _ _ _ _ domain represented.1.2 represented.2.2⟩

theorem nativeBuildFirst_packet (comparison : Bool) (xs : List Int) (count : Nat)
    (left right : ByteArray) (accepted : nativeAdmit comparison xs count left right = true) :
    nativePacket (nativeBuildFirst comparison xs left right) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) ∧
    LimbWord.Canonical (wordWidth xs.length)
      (nativePacket (nativeBuildFirst comparison xs left right)).data ∧
    decodeMagnitude (nativePacket (nativeBuildFirst comparison xs left right)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value := by
  have correct := nativeBuildFirst_correct comparison xs count left right accepted
  exact nativePacket_exact xs _ _ correct.2.1 correct.2.2 (answer_packet_fits xs _ _)

theorem nativeQuery_correct (comparison : Bool) (xs : List Int) (owner : Owner)
    (left right : ByteArray) (answer : Nat) (ready : Ownership.Ready xs owner)
    (halted : owner.status = .halted answer) (accepted : nativeQueryAdmit owner left right = true) :
    Ownership.Ready xs (nativeQuery comparison left right owner) ∧
    (nativeQuery comparison left right owner).status = .halted
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) ∧
    (nativeQuery comparison left right owner).memory = owner.memory := by
  have represented := (nativeQueryAdmit_iff xs owner left right ready).1 accepted
  have reuse := ready.query (modelOfComparison comparison) (decodeMagnitude left)
    (decodeMagnitude right) answer halted represented.1.2 represented.2.2
  simp only [nativeQuery, query_eq]
  exact ⟨reuse.1, reuse.2.1, reuse.2.2.1⟩

theorem nativeQuery_packet (comparison : Bool) (xs : List Int) (owner : Owner)
    (left right : ByteArray) (answer : Nat) (ready : Ownership.Ready xs owner)
    (halted : owner.status = .halted answer) (accepted : nativeQueryAdmit owner left right = true) :
    nativePacket (nativeQuery comparison left right owner) = encodeEndpoint (wordWidth xs.length)
      (optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value) ∧
    LimbWord.Canonical (wordWidth xs.length) (nativePacket (nativeQuery comparison left right owner)).data ∧
    decodeMagnitude (nativePacket (nativeQuery comparison left right owner)) =
      optionNatPacket (SuccinctClassic.queryTraceResult xs
        (decodeMagnitude left) (decodeMagnitude right)).value := by
  have correct := nativeQuery_correct comparison xs owner left right answer ready halted accepted
  exact nativePacket_exact xs _ _ correct.1 correct.2.1 (answer_packet_fits xs _ _)

end RMQ.SuccinctFinal.PackedNative.Lifecycle
