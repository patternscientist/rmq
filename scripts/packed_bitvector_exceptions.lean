import RMQ.Core.WordRAM.Bitvector.Source

/-! Valid parameterized directories exercising the actual exceptional branches.
The source, compiler and physical reader are the production definitions. -/

open RMQ RMQ.PackedBitvector RMQ.SuccinctFinal.PackedWordRAM
open RMQ.GenericSelect RMQ.SuccinctSpace RMQ.SuccinctRank

namespace BV1Exceptions

def bits (target : Bool) : List Bool := [target, !target, target]

@[simp] theorem machine_bits (target : Bool) : machineWordBits (bits target).length = 2 := by
  simp [bits, machineWordBits, Nat.log2]

def offsets (target bank : Bool) : List Nat := if bank == target then [0, 2] else [1, 0]

def flagRank (flag : Bool) : TwoLevelPayloadLiveStoredWordRankData [flag] 4 4 4 := by
  cases flag
  · exact canonicalTwoLevelRankDataOfChunksExactLocalBlock [false]
      (wordSize := 1) (blocksPerSuper := 1) (superWidth := 1) (blockWidth := 1) (queryCost := 4)
      (by decide) (by simp [machineWordBits, Nat.log2]) (by decide) (by decide) (by decide) (by decide)
  · exact canonicalTwoLevelRankDataOfChunksExactLocalBlock [true]
      (wordSize := 1) (blocksPerSuper := 1) (superWidth := 1) (blockWidth := 1) (queryCost := 4)
      (by decide) (by simp [machineWordBits, Nat.log2]) (by decide) (by decide) (by decide) (by decide)

@[simp] theorem flagRank_word (flag : Bool) : (flagRank flag).wordSize = 1 := by cases flag <;> rfl
@[simp] theorem flagRank_super (flag : Bool) : (flagRank flag).superWidth = 1 := by cases flag <;> rfl
@[simp] theorem flagRank_block (flag : Bool) : (flagRank flag).blockWidth = 1 := by cases flag <;> rfl

theorem sparse_budget (n : Nat) : 512 ≤ canonicalSparseExceptionDirectoryOverhead n := by
  unfold canonicalSparseExceptionDirectoryOverhead sparseExceptionRelativeTableOverhead
  omega

theorem select_budget (n : Nat) : 512 ≤ canonicalSparseExceptionSelectOverhead n := by
  have := sparse_budget n
  unfold canonicalSparseExceptionSelectOverhead
  omega

def offsetTable (target bank : Bool) : FixedWidthNatTable (offsets target bank) 2 :=
  FixedWidthNatTable.ofEntries (offsets target bank) 2 (by
    intro value hvalue
    change value ∈ offsets target bank at hvalue
    cases target <;> cases bank <;> simp [offsets] at hvalue <;> omega)

@[simp] theorem offsetTable_length (target bank : Bool) :
    (offsetTable target bank).payload.length = 4 := by
  rw [FixedWidthNatTable.payload_length]
  cases target <;> cases bank <;> rfl

def entry (marked : Bool) : SparseDenseSelectDenseLocalEntry := ⟨0, 0, marked.toNat, 0⟩

def entryTable (marked : Bool) :
    FixedWidthSparseDenseSelectDenseLocalEntryTable [entry marked] 2 :=
  FixedWidthSparseDenseSelectDenseLocalEntryTable.ofEntries [entry marked] 2 (by
    intro e he
    have heq : e = entry marked := List.mem_singleton.mp he
    subst e
    cases marked <;> decide)

@[simp] theorem entryTable_length (marked : Bool) : (entryTable marked).payload.length = 8 := by
  rw [FixedWidthSparseDenseSelectDenseLocalEntryTable.payload_length]
  rfl

def sparseDirectory (target bank : Bool) : SparseExceptionDirectory (bits target) bank 4 4 where
  localStride := 2
  localStride_pos := by decide
  flagBits := [true]
  rankData := flagRank true
  relativeEntries := offsets target bank
  relativeWidth := 2
  relativeTable := offsetTable target bank
  rank_wordSize_le_machine := by simp
  rank_superWidth_le_machine := by simp
  rank_blockWidth_le_machine := by simp
  relativeWidth_le_machine := by simp
  payload_length_le_overhead := by
    refine Nat.le_trans ?_ (sparse_budget _)
    simp [TwoLevelPayloadLiveStoredWordRankData.auxPayload_length]

@[simp] theorem sparseDirectory_length (target bank : Bool) :
    (sparseDirectory target bank).payload.length = 13 := by
  simp [SparseExceptionDirectory.payload, sparseDirectory,
    TwoLevelPayloadLiveStoredWordRankData.auxPayload_length]

theorem occurrence_lt_two (target bank : Bool) (q : Nat)
    (hq : q < occurrenceCount (bits target) bank) : q < 2 := by
  cases target <;> cases bank <;> simp [bits, occurrenceCount, Succinct.rankPrefix] at hq <;> omega

theorem offsets_exact (target bank : Bool) (q : Nat)
    (hq : q < occurrenceCount (bits target) bank) :
    (offsets target bank)[q]? = Succinct.select bank (bits target) q := by
  have hq2 := occurrence_lt_two target bank q hq
  have hcases : q = 0 ∨ q = 1 := by omega
  rcases hcases with rfl | rfl <;> cases target <;> cases bank <;>
    simp_all [bits, offsets, occurrenceCount, Succinct.rankPrefix, Succinct.select, Succinct.selectFrom]

def data (long target bank : Bool) : SparseExceptionSelectData (bits target) bank 4 4 where
  wordSize := 1
  wordSize_pos := by decide
  wordSize_le_machine := by simp
  superStride := 2
  superStride_pos := by decide
  localStride := 2
  localStride_pos := by decide
  localSlotsPerSuper := 1
  superEntries := [entry long]
  longFlagBits := [long]
  longFlagRankSuperOverhead := 4
  longFlagRankBlockOverhead := 4
  longFlagRankData := flagRank long
  longFlagRank_wordSize_le_machine := by simp
  longFlagRank_superWidth_le_machine := by simp
  longFlagRank_blockWidth_le_machine := by simp
  longSuperRelativeEntries := offsets target bank
  localEntries := [entry true]
  superFieldWidth := 2
  longSuperRelativeWidth := 2
  localFieldWidth := 2
  superTable := entryTable long
  longSuperRelativeTable := offsetTable target bank
  localTable := entryTable true
  sparseDirectory := sparseDirectory target bank
  bitWords := BoundedPayloadWordStore.ofChunks (bits target) (by decide)
  super_read_words_length_le_machine := by
    apply FixedWidthSparseDenseSelectDenseLocalEntryTable.readWordsLengthLeMachine
    simp
  long_read_words_length_le_machine := by
    intro i word h
    rw [(offsetTable target bank).read_word_length_of_some h]
    simp
  local_read_words_length_le_machine := by
    apply FixedWidthSparseDenseSelectDenseLocalEntryTable.readWordsLengthLeMachine
    simp
  payload_length_le_overhead := by
    refine Nat.le_trans ?_ (select_budget _)
    simp [TwoLevelPayloadLiveStoredWordRankData.auxPayload_length]
  super_missing_exact := by
    intro q hmissing
    have hq : 2 ≤ q := by
      by_cases h : 2 ≤ q
      · exact h
      · have hd : q / 2 = 0 := Nat.div_eq_of_lt (by omega)
        simp [selectSuperSlot, hd] at hmissing
    cases target <;> cases bank <;>
      simp [bits, Succinct.select, Succinct.selectFrom, show q ≠ 0 by omega,
        show q - 1 ≠ 0 by omega]
  long_explicit_exact := by
    intro q super hsuper hq _hmarked
    have hd : q / 2 = 0 := Nat.div_eq_of_lt (occurrence_lt_two target bank q hq)
    have he : super = entry long := by simpa [selectSuperSlot, hd] using hsuper.symm
    subst super
    simpa [relativeSplitSelectLongCompactSlot, selectSuperSlot, hd, Succinct.rankPrefix,
      relativeSplitSelectEntryBasePosition, entry] using offsets_exact target bank q hq
  local_missing_exact := by
    intro q super hsuper hq _hmarked hmissing
    have hd : q / 2 = 0 := Nat.div_eq_of_lt (occurrence_lt_two target bank q hq)
    have he : super = entry long := by simpa [selectSuperSlot, hd] using hsuper.symm
    subst super
    simp [relativeSplitSelectLocalSlot, relativeSplitSelectLocalSlotInSuper,
      selectSuperSlot, entry, hd] at hmissing
  sparse_compact_exact := by
    intro q super loc hsuper hq _hmarked hlocal _hlocmarked
    have hd : q / 2 = 0 := Nat.div_eq_of_lt (occurrence_lt_two target bank q hq)
    have he : super = entry long := by simpa [selectSuperSlot, hd] using hsuper.symm
    subst super
    have hl : loc = entry true := by
      simpa [relativeSplitSelectLocalSlot, relativeSplitSelectLocalSlotInSuper,
        selectSuperSlot, entry, hd] using hlocal.symm
    subst loc
    rw [SparseExceptionDirectory.readCosted_exact]
    simpa [sparseDirectory, relativeSplitSelectLocalBasePosition,
      relativeSplitSelectLocalSlot, relativeSplitSelectLocalSlotInSuper,
      relativeSplitSelectLocalBaseOccurrence, relativeSplitSelectSparseCompactSlot,
      selectSuperSlot, entry, hd, Succinct.rankPrefix] using offsets_exact target bank q hq
  dense_exact := by
    intro q super loc hsuper hq _hmarked hlocal hlocmarked
    have hd : q / 2 = 0 := Nat.div_eq_of_lt (occurrence_lt_two target bank q hq)
    have he : super = entry long := by simpa [selectSuperSlot, hd] using hsuper.symm
    subst super
    have hl : loc = entry true := by
      simpa [relativeSplitSelectLocalSlot, relativeSplitSelectLocalSlotInSuper,
        selectSuperSlot, entry, hd] using hlocal.symm
    subst loc
    simp [relativeSplitSelectEntryIsMarked, entry] at hlocmarked

/-- Both banks share the scalar geometry that production setup loads. -/
theorem data_geometry (long target bank : Bool) :
    (data long target bank).wordSize = 1 ∧ (data long target bank).superStride = 2 ∧
    (data long target bank).localStride = 2 ∧ (data long target bank).localSlotsPerSuper = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem data_select_exact (long target bank : Bool) (occurrence : Nat) :
    ((data long target bank).selectCosted occurrence).erase =
      Succinct.select bank (bits target) occurrence :=
  (data long target bank).selectCosted_exact occurrence

def memory (long target : Bool) : Memory := Id.run do
  let df := data long target false
  let dt := data long target true
  let w := Experiment.width 3
  let c := SuccinctClose.bpFringeChunkBits 6
  let all := [df.bitWords.store.words] ++ Experiment.directorySegments df ++
    Experiment.directorySegments dt ++ [(SuccinctClose.bpFringeChunkTable c).store.words,
      (SuccinctClose.bpChunkSelectTable c false).store.words]
  let desc := Experiment.descriptorsFrom (207 * w) all
  let bank (bit : Bool) := [desc[0]!] ++ (desc.drop (if bit then 17 else 1)).take 16 ++
    List.replicate 4 [0, 0, 0, 0] ++ [desc[33]!, desc[34]!]
  let scalars := [occurrenceCount (bits target) false, occurrenceCount (bits target) true,
    3, 1, 1, 0, w, 0, df.wordSize, df.superStride, df.localStride, df.localSlotsPerSuper] ++
    Experiment.flagScalars df ++ [df.wordSize, 0, c] ++ Experiment.flagScalars dt
  return scalars ++ (bank false).flatten ++ (bank true).flatten ++
    denseWords w (all.flatMap Experiment.segmentBits)

def registry : List (String × Bool × Bool) :=
  [("long-super-false", true, false), ("long-super-true", true, true),
   ("sparse-local-false", false, false), ("sparse-local-true", false, true)]

def expectedNames : List String :=
  ["long-super-false", "long-super-true", "sparse-local-false", "sparse-local-true"]

def runFixture (name : String) (long target wrongRoute : Bool) : IO Bool := do
  let supplied := memory long target
  let code := PackedBitvector.program .select
  let budget := (PackedBitvector.source .select).size + 1
  let actual := runArray supplied code.toArray budget (PackedBitvector.initial .select target 1)
  let expected := ((Succinct.select target (bits target) 1).map (· + 1)).getD 0
  let packetOK := expected == 3 && actual.result == some expected &&
    actual.final.status == .halted expected && actual.final.regs 513 == expected
  let observedSegment := if long then 12 else 16
  let expectedSegment := if wrongRoute then (if long then 16 else 12) else observedSegment
  let routeLoads (segment : Nat) := actual.transitions.filter fun t =>
    t.instruction == .load 8259 8261 && t.before.regs 8192 == segment &&
      t.receipt == some ⟨t.before.regs 8261, supplied[t.before.regs 8261]?⟩ &&
      supplied[t.before.regs 8261]?.isSome
  let routeOK := !(routeLoads expectedSegment).isEmpty &&
    (routeLoads (if expectedSegment == 12 then 16 else 12)).isEmpty
  let backed := actual.reads.all fun r => r.reply == supplied[r.address]? && r.reply.isSome
  let passed := packetOK && routeOK && backed && actual.steps <= budget
  IO.println s!"BV1-EXCEPTION-DETAIL {name} packetOK={packetOK} expected={expected} actual={repr actual.result} expected-segment={expectedSegment} long-loads={(routeLoads 12).length} sparse-loads={(routeLoads 16).length} routeOK={routeOK} backed={backed} steps={actual.steps} budget={budget} wrong-route={wrongRoute}"
  IO.println s!"BV1-EXCEPTION-CASE {name} {(if passed then "PASS" else "FAIL")} version=1"
  return passed

example (long target bank : Bool) : SparseExceptionSelectData (bits target) bank 4 4 :=
  data long target bank

example (mem : Memory) (code : Program) (fuel : Nat) (state : State) :
    runArray mem code.toArray fuel state = run mem code fuel state :=
  runArray_toArray mem code fuel state

/-- The optimized evaluator executes precisely the production list-machine run. -/
theorem fixture_run_eq (long target : Bool) :
    runArray (memory long target) (PackedBitvector.program .select).toArray
      ((PackedBitvector.source .select).size + 1) (PackedBitvector.initial .select target 1) =
    run (memory long target) (PackedBitvector.program .select)
      ((PackedBitvector.source .select).size + 1) (PackedBitvector.initial .select target 1) :=
  runArray_toArray (memory long target) (PackedBitvector.program .select)
    ((PackedBitvector.source .select).size + 1) (PackedBitvector.initial .select target 1)

#print axioms data
#print axioms data_geometry
#print axioms data_select_exact
#print axioms offsets_exact
#print axioms fixture_run_eq

end BV1Exceptions

def main (args : List String) : IO UInt32 := do
  if BV1Exceptions.registry.map (·.1) != BV1Exceptions.expectedNames ||
      BV1Exceptions.expectedNames.length != 4 || BV1Exceptions.expectedNames.eraseDups.length != 4 then
    IO.eprintln "BV1-EXCEPTION-REGISTRY FAIL version=1"
    return 2
  if args == ["--startup"] then
    IO.println "BV1-EXCEPTION-STARTUP version=1 expected=4"
    return 0
  if args == ["--list"] then
    IO.println s!"BV1-EXCEPTION-REGISTRY version=1 cases={repr BV1Exceptions.expectedNames} expected=4"
    return 0
  let wrong := args.length == 3 && args[2]? == some "--wrong-route"
  let chosen := if wrong then args.take 2 else args
  let selected ← match chosen with
    | [] => pure BV1Exceptions.registry
    | ["--case", name] =>
      if BV1Exceptions.expectedNames.contains name then
        pure (BV1Exceptions.registry.filter fun f => f.1 == name)
      else IO.eprintln "BV1-EXCEPTION-SELECTOR FAIL" *> pure []
    | _ => IO.eprintln "BV1-EXCEPTION-SELECTOR FAIL" *> pure []
  if selected.isEmpty then return 2
  let mut passed := 0
  for (name, long, target) in selected do
    if ← BV1Exceptions.runFixture name long target wrong then passed := passed + 1
  IO.println s!"BV1-EXCEPTION-SUMMARY version=1 executed={selected.length} expected={selected.length} passed={passed} total=4"
  return if passed == selected.length then 0 else 1
