import RMQ.Core.WordRAM.Native.CanonicalImage
import RMQ.Core.WordRAM.Native.Host

/-! # One canonical image at the execution and exported API boundaries -/

namespace RMQ.SuccinctFinal.PackedNative
open PackedWordRAM

def canonicalEndpoint (n value : Nat) : ByteArray :=
  ⟨LimbWord.encode (wordWidth n) value⟩

/-- The logged execution of the very arrays supplied to `nativeCore`.
The exported implementation uses its proved accumulator projection. -/
def canonicalExecution (xs : List Int) (left right fuel : Nat) : LimbMachine.Run :=
  let image := canonicalImage xs
  LimbMachine.run image.width image.memory image.code fuel
    (nativeInitialState image (canonicalEndpoint xs.length left).data
      (canonicalEndpoint xs.length right).data)

def canonicalObservation (xs : List Int) (left right fuel : Nat) (reads : Bool) :
    LimbMachine.State × Stats :=
  nativeCore (canonicalImage xs) (canonicalEndpoint xs.length left).data
    (canonicalEndpoint xs.length right).data fuel reads

theorem canonicalExecution_decode (xs : List Int) (left right fuel : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (canonicalExecution xs left right fuel).decode =
      run (buildMemory xs) queryProgram fuel (initialState xs.length left right) := by
  dsimp only [canonicalExecution, canonicalEndpoint]
  rw [canonical_initial_words xs left right hl hr]
  exact canonical_limb_run xs left right fuel hl hr

theorem canonicalObservation_reference (xs : List Int) (left right fuel : Nat) (reads : Bool)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    ((canonicalObservation xs left right fuel reads).1.decode,
      (canonicalObservation xs left right fuel reads).2) =
      observeRun reads (run (buildMemory xs) queryProgram fuel
        (initialState xs.length left right)) {} :=
  canonical_native_core xs left right fuel reads hl hr

theorem canonicalObservation_final (xs : List Int) (left right fuel : Nat) (reads : Bool)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (canonicalObservation xs left right fuel reads).1.decode =
      (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).final :=
  congrArg Prod.fst (canonicalObservation_reference xs left right fuel reads hl hr)

theorem canonicalObservation_steps (xs : List Int) (left right fuel : Nat) (reads : Bool)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (canonicalObservation xs left right fuel reads).2.steps =
      (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).steps := by
  have h := congrArg (fun x : State × Stats => x.2.steps)
    (canonicalObservation_reference xs left right fuel reads hl hr)
  exact h.trans (observeRun_steps _ _)

theorem canonicalObservation_category (xs : List Int) (left right fuel : Nat)
    (reads : Bool) (category : Category)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (canonicalObservation xs left right fuel reads).2.counts.get category =
      (run (buildMemory xs) queryProgram fuel
        (initialState xs.length left right)).categoryCount category := by
  have h := congrArg (fun x : State × Stats => x.2.counts.get category)
    (canonicalObservation_reference xs left right fuel reads hl hr)
  exact h.trans (observeRun_category _ _ _)

theorem canonicalObservation_reads (xs : List Int) (left right fuel : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (canonicalObservation xs left right fuel true).2.readsRev.reverse =
      (run (buildMemory xs) queryProgram fuel (initialState xs.length left right)).reads := by
  have h := congrArg (fun x : State × Stats => x.2.readsRev.reverse)
    (canonicalObservation_reference xs left right fuel true hl hr)
  exact h.trans (observeRun_reads _)

theorem canonicalObservation_halts (xs : List Int) (left right : Nat) (reads : Bool)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    (canonicalObservation xs left right queryBudget reads).1.decode.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) := by
  rw [canonicalObservation_final xs left right queryBudget reads hl hr]
  exact fullyChargedPackedQueryCapstone_holds.halt xs left right hl hr

theorem canonicalExecution_spec (xs : List Int) (left right : Nat) (hv : ValidRange xs left right) :
    (canonicalExecution xs left right queryBudget).decode.result =
      some (scanWindow xs left (right - left) + 1) := by
  obtain ⟨hl, hr⟩ := validEndpoints_fit xs left right hv
  rw [canonicalExecution_decode xs left right queryBudget hl hr]
  exact fullyChargedPackedQueryCapstone_holds.specResult xs left right hv

theorem canonicalExecution_leftmost (xs : List Int) (left right index : Nat)
    (hv : ValidRange xs left right)
    (hresult : (canonicalExecution xs left right queryBudget).decode.result = some (index + 1)) :
    LeftmostArgMin xs left right index := by
  have hscan := canonicalExecution_spec xs left right hv
  have hi : scanWindow xs left (right - left) = index := by
    rw [hresult] at hscan
    have he := Option.some.inj hscan
    omega
  apply fullyChargedPackedQueryCapstone_holds.leftmost xs left right index
  rw [fullyChargedPackedQueryCapstone_holds.natContract xs left right, if_pos hv, hi]

theorem canonical_query_supported (xs : List Int) (left right fuel : Nat)
    (hs : (canonicalImage xs).Supported nativeLimits)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (hf : fuel ≤ nativeFuelLimit) :
    NativeQuerySupported (canonicalImage xs) (canonicalEndpoint xs.length left)
      (canonicalEndpoint xs.length right) fuel := by
  refine ⟨wordWidth_pos xs.length, hs.2.1, ?_, hs.2.2.1,
    size_lt_wordCapacity xs.length, LimbWord.canonical_encode _ _ hl,
    LimbWord.canonical_encode _ _ hr, hf⟩
  change 3 ≤ queryRegisterCount
  rw [queryRegisterCount_eq]
  decide

theorem nativeLoadEntry_canonical (xs : List Int)
    (hs : (canonicalImage xs).Supported nativeLimits) :
    nativeLoadEntry (canonicalImage xs).encode = .ok (canonicalImage xs) := by
  rw [nativeLoadEntry_source, canonical_supported_roundtrip xs nativeLimits hs]

theorem nativeQueryEntry_canonical (xs : List Int) (left right fuel : Nat) (reads : Bool)
    (hs : (canonicalImage xs).Supported nativeLimits)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (hf : fuel ≤ nativeFuelLimit) :
    nativeQueryEntry (canonicalImage xs) (canonicalEndpoint xs.length left)
      (canonicalEndpoint xs.length right) fuel reads =
      .ok (nativeObservationText (canonicalObservation xs left right fuel reads)) :=
  nativeQueryEntry_source _ _ _ _ _ (canonical_query_supported xs left right fuel hs hl hr hf)

/-- A supplied store agreeing at every canonical read produces the same full
native execution, provided its stored words fit the declared word width.
Safety follows from the accepted agreement theorem, rather than an extra
caller-supplied execution-safety premise. -/
theorem canonical_supplied_memory (xs : List Int) (memory : Memory) (left right : Nat)
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length)
    (hm : ∀ value ∈ memory, value < 2 ^ wordWidth xs.length)
    (hag : ∀ receipt ∈ (canonicalExecution xs left right queryBudget).decode.reads,
      memory[receipt.address]? = (buildMemory xs)[receipt.address]?) :
    (LimbMachine.run (wordWidth xs.length) (LimbMachine.encodeMemory (wordWidth xs.length) memory)
      (canonicalImage xs).code queryBudget
      (nativeInitialState (canonicalImage xs) (canonicalEndpoint xs.length left).data
        (canonicalEndpoint xs.length right).data)).decode =
      (canonicalExecution xs left right queryBudget).decode := by
  have href := canonicalExecution_decode xs left right queryBudget hl hr
  rw [href] at hag ⊢
  have hagree := fullyChargedPackedQueryCapstone_holds.suppliedMemoryAgreement xs memory left right hag
  have hsafe : LimbMachine.RunSafe (wordWidth xs.length)
      (run memory queryProgram queryBudget (initialState xs.length left right)) := by
    rw [hagree]
    exact canonical_run_safe xs left right queryBudget hl hr
  change (LimbMachine.run (wordWidth xs.length) (LimbMachine.encodeMemory (wordWidth xs.length) memory)
    (LimbMachine.encodeCode (wordWidth xs.length) queryProgram) queryBudget
    (nativeInitialState (canonicalImage xs) (LimbWord.encode (wordWidth xs.length) left)
      (LimbWord.encode (wordWidth xs.length) right))).decode = _
  rw [canonical_initial_words xs left right hl hr,
    LimbMachine.run_reference _ _ _ _ _ _ hm (queryProgram_fits xs.length)
      canonical_destination_bound (initialState_fits xs.length left right hl hr)
      (canonical_initial_zero_tail xs.length left right) hsafe]
  exact hagree

end RMQ.SuccinctFinal.PackedNative
