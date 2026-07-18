import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeSubstitution
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAMStoreParam

/-!
# Charged chunked fringe: Word-RAM trace layer (B2 wiring)

`WordRAM.TraceResult` twins of the charged chunked fringe evaluators and of
the accepted cross-block close consumer, segment-parameterized in the house
`AtSegment(s)` style.

The chunk-table reads are expressed as one `FlatStoreComputation` (the same
operational shape as the canonical interior component), so store
parametricity, read/store agreement, and read-backing come from the
computation's own `footprint_determines` / `reads_match_store` obligations,
and the emitted events are exactly one `readWord fringeSegment slot` per
visited chunk — no synthetic cost-only markers anywhere on the charged path.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-! ## The chunked fold as a flat store computation -/

/--
The charged chunked fringe fold over a flat word store: one word read per
chunk, decoded by `bitsToNatLE` into the packed entry consumed by
`bpFringeChunkStepDecoded`.
-/
def bpFringeChunkFoldComputationFrom (c : Nat) (window : List Bool)
    (relLo relHi : Nat) :
    Nat -> Nat -> (Nat × Option (Nat × Nat)) ->
      SuccinctSpace.FlatStoreComputation (Nat × Option (Nat × Nat))
  | _j, 0, st => SuccinctSpace.FlatStoreComputation.pure st
  | j, count + 1, st =>
      SuccinctSpace.FlatStoreComputation.bind
        (SuccinctSpace.FlatStoreComputation.read
          (bpFringeChunkSlot c (bpFringeWindowChunkValue c window j)
            (bpFringeChunkStartOff c relLo j)
            (bpFringeChunkEndOff c relHi j)))
        (fun word? =>
          bpFringeChunkFoldComputationFrom c window relLo relHi (j + 1)
            count
            (bpFringeChunkStepDecoded c relLo relHi j st
              (word?.map SuccinctSpace.bitsToNatLE)))

/-- Top-level fold computation (chunk `0`, seed accumulator, empty best). -/
def bpFringeChunkFoldComputation (c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) :
    SuccinctSpace.FlatStoreComputation (Nat × Option (Nat × Nat)) :=
  bpFringeChunkFoldComputationFrom c window relLo relHi 0 count (seed, none)

/--
Against the word store of any fixed-width table, the flat fold computes
exactly the value of the charged `Costed` fold on that table.
-/
theorem bpFringeChunkFoldComputationFrom_run_value
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (c : Nat) (window : List Bool) (relLo relHi : Nat) :
    forall (j count : Nat) (st : Nat × Option (Nat × Nat)),
      ((bpFringeChunkFoldComputationFrom c window relLo relHi j count
          st).run
        (SuccinctSpace.FlatWordStore.ofArray table.store.words)).value =
      (bpFringeChunkFoldCostedFrom table c window relLo relHi j count
        st).value := by
  intro j count
  induction count generalizing j with
  | zero =>
      intro st
      rfl
  | succ count ih =>
      intro st
      have hread :
          ((SuccinctSpace.FlatWordStore.ofArray table.store.words
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c window j)
                (bpFringeChunkStartOff c relLo j)
                (bpFringeChunkEndOff c relHi j))).map
              SuccinctSpace.bitsToNatLE) =
            (table.readCosted
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c window j)
                (bpFringeChunkStartOff c relLo j)
                (bpFringeChunkEndOff c relHi j))).value := by
        show (table.store.words[bpFringeChunkSlot c
            (bpFringeWindowChunkValue c window j)
            (bpFringeChunkStartOff c relLo j)
            (bpFringeChunkEndOff c relHi j)]?).map
            SuccinctSpace.bitsToNatLE = _
        exact
          (table.read_exact _).trans (table.readCosted_erase _).symm
      show
        ((bpFringeChunkFoldComputationFrom c window relLo relHi (j + 1)
            count
            (bpFringeChunkStepDecoded c relLo relHi j st
              ((SuccinctSpace.FlatWordStore.ofArray table.store.words
                (bpFringeChunkSlot c (bpFringeWindowChunkValue c window j)
                  (bpFringeChunkStartOff c relLo j)
                  (bpFringeChunkEndOff c relHi j))).map
                SuccinctSpace.bitsToNatLE))).run
          (SuccinctSpace.FlatWordStore.ofArray table.store.words)).value =
          (Costed.bind
            (table.readCosted
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c window j)
                (bpFringeChunkStartOff c relLo j)
                (bpFringeChunkEndOff c relHi j)))
            (fun entry? =>
              bpFringeChunkFoldCostedFrom table c window relLo relHi
                (j + 1) count
                (bpFringeChunkStepDecoded c relLo relHi j st
                  entry?))).value
      rw [hread, Costed.value_bind]
      exact ih (j + 1) _

/-- One recorded read per visited chunk, against any flat store. -/
theorem bpFringeChunkFoldComputationFrom_run_reads_length
    (c : Nat) (window : List Bool) (relLo relHi : Nat)
    (store : SuccinctSpace.FlatWordStore) :
    forall (j count : Nat) (st : Nat × Option (Nat × Nat)),
      ((bpFringeChunkFoldComputationFrom c window relLo relHi j count
          st).run store).reads.length = count := by
  intro j count
  induction count generalizing j with
  | zero =>
      intro st
      rfl
  | succ count ih =>
      intro st
      show
        (SuccinctSpace.FlatStoreExecution.append _ _).reads.length =
          count + 1
      simp only [SuccinctSpace.FlatStoreExecution.append,
        List.length_append]
      rw [ih (j + 1) _]
      simp only [SuccinctSpace.FlatStoreComputation.read_run,
        List.length_cons, List.length_nil]
      omega

/-- The visited footprint is exactly the chunk slot sequence. -/
theorem bpFringeChunkFoldComputationFrom_run_footprint
    (c : Nat) (window : List Bool) (relLo relHi : Nat)
    (store : SuccinctSpace.FlatWordStore) :
    forall (j count : Nat) (st : Nat × Option (Nat × Nat)),
      ((bpFringeChunkFoldComputationFrom c window relLo relHi j count
          st).run store).footprint =
        (List.range' j count).map (fun block =>
          bpFringeChunkSlot c (bpFringeWindowChunkValue c window block)
            (bpFringeChunkStartOff c relLo block)
            (bpFringeChunkEndOff c relHi block)) := by
  intro j count
  induction count generalizing j with
  | zero =>
      intro st
      rfl
  | succ count ih =>
      intro st
      show
        (SuccinctSpace.FlatStoreExecution.append _ _).footprint =
          _
      rw [SuccinctSpace.FlatStoreExecution.append_footprint]
      rw [List.range'_succ]
      simp only [List.map_cons]
      rw [ih (j + 1) _]
      rfl

/-! ## The chunked fold as a segment trace -/

/--
Canonical charged fold trace at one global segment: the flat fold executed
against the supplied table's own word store, with each recorded read
emitted as one `readWord fringeSegment slot` event.
-/
def bpFringeChunkFoldTraceResultAtSegment
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) :
    WordRAM.TraceResult (Nat × Option (Nat × Nat)) :=
  flatStoreExecutionTraceResultAtSegment fringeSegment
    ((bpFringeChunkFoldComputation c window seed relLo relHi count).run
      (SuccinctSpace.FlatWordStore.ofArray table.store.words))

/-- Supplied-store charged fold trace at one global segment. -/
def bpFringeChunkFoldTraceResultAtSegmentWithStore
    (store : WordRAM.ReadStore)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) :
    WordRAM.TraceResult (Nat × Option (Nat × Nat)) :=
  flatStoreExecutionTraceResultAtSegment fringeSegment
    ((bpFringeChunkFoldComputation c window seed relLo relHi count).run
      (flatWordStoreOfReadStore store fringeSegment))

theorem bpFringeChunkFoldTraceResultAtSegment_toCosted
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) :
    (bpFringeChunkFoldTraceResultAtSegment table fringeSegment c window
        seed relLo relHi count).toCosted =
      bpFringeChunkFoldCosted table c window seed relLo relHi count := by
  unfold bpFringeChunkFoldTraceResultAtSegment
  rw [flatStoreExecutionTraceResultAtSegment_toCosted]
  apply Costed.ext
  · exact
      bpFringeChunkFoldComputationFrom_run_value table c window relLo
        relHi 0 count (seed, none)
  · show
      ((bpFringeChunkFoldComputation c window seed relLo relHi count).run
        (SuccinctSpace.FlatWordStore.ofArray table.store.words)).reads.length =
        (bpFringeChunkFoldCosted table c window seed relLo relHi
          count).cost
    rw [bpFringeChunkFoldCosted_cost]
    exact
      bpFringeChunkFoldComputationFrom_run_reads_length c window relLo
        relHi _ 0 count (seed, none)

/--
Under supplied-store agreement with the table words on the fringe segment,
the supplied-store fold trace is exactly the canonical fold trace.
-/
theorem bpFringeChunkFoldTraceResultAtSegmentWithStore_eq_of_agree
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {store : WordRAM.ReadStore} {fringeSegment : Nat}
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          table.store.words[address]?)
    (c : Nat) (window : List Bool) (seed relLo relHi count : Nat) :
    bpFringeChunkFoldTraceResultAtSegmentWithStore store fringeSegment c
        window seed relLo relHi count =
      bpFringeChunkFoldTraceResultAtSegment table fringeSegment c window
        seed relLo relHi count := by
  unfold bpFringeChunkFoldTraceResultAtSegmentWithStore
    bpFringeChunkFoldTraceResultAtSegment
  have hstore :
      flatWordStoreOfReadStore store fringeSegment =
        SuccinctSpace.FlatWordStore.ofArray table.store.words := by
    funext address
    exact hfringe address
  rw [hstore]

/-- Store parametricity of the supplied-store fold trace. -/
theorem bpFringeChunkFoldTraceResultAtSegmentWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore} {fringeSegment : Nat}
    (hread :
      forall address,
        storeA.readWord? fringeSegment address =
          storeB.readWord? fringeSegment address)
    (c : Nat) (window : List Bool) (seed relLo relHi count : Nat) :
    bpFringeChunkFoldTraceResultAtSegmentWithStore storeA fringeSegment c
        window seed relLo relHi count =
      bpFringeChunkFoldTraceResultAtSegmentWithStore storeB fringeSegment
        c window seed relLo relHi count := by
  unfold bpFringeChunkFoldTraceResultAtSegmentWithStore
  have hstore :
      flatWordStoreOfReadStore storeA fringeSegment =
        flatWordStoreOfReadStore storeB fringeSegment := by
    funext address
    exact hread address
  rw [hstore]

/-- The supplied-store fold trace agrees with the supplying store. -/
theorem bpFringeChunkFoldTraceResultAtSegmentWithStore_matchesReadStore
    (store : WordRAM.ReadStore)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) :
    forall event,
      List.Mem event
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store
            fringeSegment c window seed relLo relHi count).trace ->
        event.matchesReadStore store := by
  exact
    flatStoreComputationTraceResultAtSegment_matchesReadStore
      (bpFringeChunkFoldComputation c window seed relLo relHi count)
      store fringeSegment

/--
Every canonical fold trace event is one fringe-segment read of the table's
own stored word at a visited (row-count-bounded) slot.
-/
theorem bpFringeChunkFoldTraceResultAtSegment_trace_forall
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord fringeSegment address
          table.store.words[address]?)) :
    forall event,
      List.Mem event
          (bpFringeChunkFoldTraceResultAtSegment table fringeSegment c
            window seed relLo relHi count).trace ->
        P event := by
  intro event hmem
  unfold bpFringeChunkFoldTraceResultAtSegment
    flatStoreExecutionTraceResultAtSegment at hmem
  simp only at hmem
  rcases List.mem_map.mp hmem with ⟨read, hreadMem, rfl⟩
  have hword :
      SuccinctSpace.FlatWordStore.ofArray table.store.words read.1 =
        read.2 :=
    (bpFringeChunkFoldComputation c window seed relLo relHi
      count).reads_match_store
      (SuccinctSpace.FlatWordStore.ofArray table.store.words)
      read.1 read.2 hreadMem
  have hwordEq : read.2 = table.store.words[read.1]? := hword.symm
  have hfoot :
      read.1 ∈
        ((bpFringeChunkFoldComputation c window seed relLo relHi
            count).run
          (SuccinctSpace.FlatWordStore.ofArray
            table.store.words)).footprint :=
    List.mem_map.mpr ⟨read, hreadMem, rfl⟩
  unfold bpFringeChunkFoldComputation at hfoot
  rw [bpFringeChunkFoldComputationFrom_run_footprint] at hfoot
  rcases List.mem_map.mp hfoot with ⟨block, _hblock, hslot⟩
  have hlt : read.1 < bpFringeChunkRowCount c := by
    rw [<- hslot]
    exact
      bpFringeChunkSlot_lt_rowCount
        (bpFringeWindowChunkValue_lt c window block)
        (bpFringeChunkStartOff_le c relLo block)
        (bpFringeChunkEndOff_le c relHi block)
  rw [hwordEq]
  exact hread read.1 hlt

theorem bpFringeChunkFoldTraceResultAtSegment_matchesReadStore
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat)
    (store : WordRAM.ReadStore)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          table.store.words[address]?) :
    forall event,
      List.Mem event
          (bpFringeChunkFoldTraceResultAtSegment table fringeSegment c
            window seed relLo relHi count).trace ->
        event.matchesReadStore store := by
  apply bpFringeChunkFoldTraceResultAtSegment_trace_forall
  intro address _hlt
  show store.readWord? fringeSegment address = table.store.words[address]?
  exact hfringe address

theorem bpFringeChunkFoldTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) :
    forall event,
      List.Mem event
          (bpFringeChunkFoldTraceResultAtSegment table fringeSegment c
            window seed relLo relHi count).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpFringeChunkFoldTraceResultAtSegment_trace_forall
  intro address _hlt
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpFringeChunkFoldTraceResultAtSegmentWithStore_trace_forall
    (store : WordRAM.ReadStore)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord fringeSegment address
          (store.readWord? fringeSegment address))) :
    forall event,
      List.Mem event
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store
            fringeSegment c window seed relLo relHi count).trace ->
        P event := by
  intro event hmem
  unfold bpFringeChunkFoldTraceResultAtSegmentWithStore
    flatStoreExecutionTraceResultAtSegment at hmem
  simp only at hmem
  rcases List.mem_map.mp hmem with ⟨read, hreadMem, rfl⟩
  have hword :
      flatWordStoreOfReadStore store fringeSegment read.1 = read.2 :=
    (bpFringeChunkFoldComputation c window seed relLo relHi
      count).reads_match_store
      (flatWordStoreOfReadStore store fringeSegment)
      read.1 read.2 hreadMem
  have hwordEq : read.2 = store.readWord? fringeSegment read.1 :=
    hword.symm
  have hfoot :
      read.1 ∈
        ((bpFringeChunkFoldComputation c window seed relLo relHi
            count).run
          (flatWordStoreOfReadStore store fringeSegment)).footprint :=
    List.mem_map.mpr ⟨read, hreadMem, rfl⟩
  unfold bpFringeChunkFoldComputation at hfoot
  rw [bpFringeChunkFoldComputationFrom_run_footprint] at hfoot
  rcases List.mem_map.mp hfoot with ⟨block, _hblock, hslot⟩
  have hlt : read.1 < bpFringeChunkRowCount c := by
    rw [<- hslot]
    exact
      bpFringeChunkSlot_lt_rowCount
        (bpFringeWindowChunkValue_lt c window block)
        (bpFringeChunkStartOff_le c relLo block)
        (bpFringeChunkEndOff_le c relHi block)
  rw [hwordEq]
  exact hread read.1 hlt

theorem bpFringeChunkFoldTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    (store : WordRAM.ReadStore)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) :
    forall event,
      List.Mem event
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store
            fringeSegment c window seed relLo relHi count).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpFringeChunkFoldTraceResultAtSegmentWithStore_trace_forall
  intro address _hlt
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

/-- A positive-count fold trace contains its first chunk-table read. -/
theorem bpFringeChunkFoldTraceResultAtSegment_head_mem
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (fringeSegment c : Nat) (window : List Bool)
    (seed relLo relHi count : Nat) (hcount : 0 < count) :
    WordRAM.TraceEvent.readWord fringeSegment
        (bpFringeChunkSlot c (bpFringeWindowChunkValue c window 0)
          (bpFringeChunkStartOff c relLo 0)
          (bpFringeChunkEndOff c relHi 0))
        table.store.words[bpFringeChunkSlot c
          (bpFringeWindowChunkValue c window 0)
          (bpFringeChunkStartOff c relLo 0)
          (bpFringeChunkEndOff c relHi 0)]? ∈
      (bpFringeChunkFoldTraceResultAtSegment table fringeSegment c window
        seed relLo relHi count).trace := by
  obtain ⟨k, rfl⟩ : ∃ k, count = k + 1 := ⟨count - 1, by omega⟩
  apply List.mem_map.mpr
  refine
    ⟨(bpFringeChunkSlot c (bpFringeWindowChunkValue c window 0)
        (bpFringeChunkStartOff c relLo 0)
        (bpFringeChunkEndOff c relHi 0),
      SuccinctSpace.FlatWordStore.ofArray table.store.words
        (bpFringeChunkSlot c (bpFringeWindowChunkValue c window 0)
          (bpFringeChunkStartOff c relLo 0)
          (bpFringeChunkEndOff c relHi 0))), ?_, rfl⟩
  show _ ∈
    (SuccinctSpace.FlatStoreExecution.append _ _).reads
  exact List.mem_append_left _ (List.mem_cons_self)

namespace ConcreteCompactBPCloseLCADirectory

/-- The four-word window trace is exactly the accepted window tick packet. -/
theorem localBPWindowBitsTraceResult_toCosted
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPWindowBitsTraceResult shape blockSize close).toCosted =
      Costed.tickValue 4 (localBPWindowBits shape blockSize close) := by
  apply Costed.ext
  · exact localBPWindowBitsTraceResult_value shape blockSize close
  · exact localBPWindowBitsTraceResult_cost shape blockSize close

theorem localBPWindowBitsTraceResultWithStore_toCosted_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (blockSize close : Nat) :
    (localBPWindowBitsTraceResultWithStore
        shape store blockSize close).toCosted =
      Costed.tickValue 4 (localBPWindowBits shape blockSize close) := by
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]
  exact localBPWindowBitsTraceResult_toCosted shape blockSize close

/-! ## Charged chunked fringe candidates at one global segment -/

/--
Charged chunked left endpoint-fringe trace: the accepted four window-word
reads at segment `0`, then one chunk-table read per visited chunk at
`fringeSegment`.
-/
def bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  let relLo := start - base
  let relHi := start + count - 1 - base
  WordRAM.TraceResult.bind
    (localBPWindowBitsTraceResult shape blockSize leftClose)
    (fun window =>
      WordRAM.TraceResult.map
        (fun st => bpFringeCandGlobal base seed start st.2)
        (bpFringeChunkFoldTraceResultAtSegment (bpFringeChunkTable c)
          fringeSegment c window seed relLo relHi
          (Nat.min (relHi / c + 1) 33)))

/-- Charged chunked right endpoint-fringe trace. -/
def bpChunkedRightFringeCandidateSeededTraceResultAtSegment
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize rightClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize rightClose
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  let relLo := start - base
  let relHi := start + count - 1 - base
  WordRAM.TraceResult.bind
    (localBPWindowBitsTraceResult shape blockSize rightClose)
    (fun window =>
      WordRAM.TraceResult.map
        (fun st => bpFringeCandGlobal base seed start st.2)
        (bpFringeChunkFoldTraceResultAtSegment (bpFringeChunkTable c)
          fringeSegment c window seed relLo relHi
          (Nat.min (relHi / c + 1) 33)))

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_refines
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose seed : Nat) :
    (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
        shape fringeSegment blockSize leftClose seed).toCosted =
      bpChunkedLeftFringeCandidateSeededCosted shape blockSize leftClose
        seed := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
    bpChunkedLeftFringeCandidateSeededCosted
  simp only [WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.map_toCosted,
    localBPWindowBitsTraceResult_toCosted,
    bpFringeChunkFoldTraceResultAtSegment_toCosted]

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegment_refines
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize rightClose seed : Nat) :
    (bpChunkedRightFringeCandidateSeededTraceResultAtSegment
        shape fringeSegment blockSize rightClose seed).toCosted =
      bpChunkedRightFringeCandidateSeededCosted shape blockSize rightClose
        seed := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegment
    bpChunkedRightFringeCandidateSeededCosted
  simp only [WordRAM.TraceResult.bind_toCosted,
    WordRAM.TraceResult.map_toCosted,
    localBPWindowBitsTraceResult_toCosted,
    bpFringeChunkFoldTraceResultAtSegment_toCosted]

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize leftClose).trace ->
          P event)
    (hfringe :
      forall address,
        address <
          bpFringeChunkRowCount (bpFringeChunkBits shape.bpCode.length) ->
        P (WordRAM.TraceEvent.readWord fringeSegment address
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)) :
    forall event,
      List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize leftClose seed).trace ->
        P event := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hbp
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegment_trace_forall
        (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length))
        fringeSegment _ _ seed _ _ _ P hfringe

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize rightClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResult shape blockSize rightClose).trace ->
          P event)
    (hfringe :
      forall address,
        address <
          bpFringeChunkRowCount (bpFringeChunkBits shape.bpCode.length) ->
        P (WordRAM.TraceEvent.readWord fringeSegment address
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)) :
    forall event,
      List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize rightClose seed).trace ->
        P event := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegment
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hbp
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegment_trace_forall
        (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length))
        fringeSegment _ _ seed _ _ _ P hfringe

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_matchesReadStore
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose seed : Nat)
    (store : WordRAM.ReadStore)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?) :
    forall event,
      List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize leftClose seed).trace ->
        event.matchesReadStore store := by
  apply bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
  · exact
      localBPWindowBitsTraceResult_matchesReadStore shape blockSize
        leftClose store hbpCode
  · intro address _hlt
    show store.readWord? fringeSegment address = _
    exact hfringe address

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegment_matchesReadStore
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize rightClose seed : Nat)
    (store : WordRAM.ReadStore)
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?) :
    forall event,
      List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize rightClose seed).trace ->
        event.matchesReadStore store := by
  apply bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
  · exact
      localBPWindowBitsTraceResult_matchesReadStore shape blockSize
        rightClose store hbpCode
  · intro address _hlt
    show store.readWord? fringeSegment address = _
    exact hfringe address

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize leftClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize leftClose seed).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_trace_forall
  · exact
      localBPWindowBitsTraceResult_no_syntheticCostOnlyPrimitive shape
        blockSize leftClose
  · intro address _hlt
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegment_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (fringeSegment : Nat)
    (blockSize rightClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize rightClose seed).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpChunkedRightFringeCandidateSeededTraceResultAtSegment_trace_forall
  · exact
      localBPWindowBitsTraceResult_no_syntheticCostOnlyPrimitive shape
        blockSize rightClose
  · intro address _hlt
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

/-! ## Supplied-store chunked fringe candidates -/

/-- Store-parameterized charged chunked left endpoint-fringe trace. -/
def bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment : Nat)
    (blockSize leftClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  let relLo := start - base
  let relHi := start + count - 1 - base
  WordRAM.TraceResult.bind
    (localBPWindowBitsTraceResultWithStore shape store blockSize leftClose)
    (fun window =>
      WordRAM.TraceResult.map
        (fun st => bpFringeCandGlobal base seed start st.2)
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store
          fringeSegment c window seed relLo relHi
          (Nat.min (relHi / c + 1) 33)))

/-- Store-parameterized charged chunked right endpoint-fringe trace. -/
def bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment : Nat)
    (blockSize rightClose seed : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize rightClose
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  let relLo := start - base
  let relHi := start + count - 1 - base
  WordRAM.TraceResult.bind
    (localBPWindowBitsTraceResultWithStore shape store blockSize rightClose)
    (fun window =>
      WordRAM.TraceResult.map
        (fun st => bpFringeCandGlobal base seed start st.2)
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store
          fringeSegment c window seed relLo relHi
          (Nat.min (relHi / c + 1) 33)))

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    {fringeSegment : Nat}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)
    (blockSize leftClose seed : Nat) :
    bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose seed =
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
        shape fringeSegment blockSize leftClose seed := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
    bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]
  simp only [bpFringeChunkFoldTraceResultAtSegmentWithStore_eq_of_agree
    (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length)) hfringe]

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_eq_of_agree
    {shape : Cartesian.CartesianShape} {store : WordRAM.ReadStore}
    {fringeSegment : Nat}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)
    (blockSize rightClose seed : Nat) :
    bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize rightClose seed =
      bpChunkedRightFringeCandidateSeededTraceResultAtSegment
        shape fringeSegment blockSize rightClose seed := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
    bpChunkedRightFringeCandidateSeededTraceResultAtSegment
  rw [localBPWindowBitsTraceResultWithStore_eq_of_agree hbpCode]
  simp only [bpFringeChunkFoldTraceResultAtSegmentWithStore_eq_of_agree
    (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length)) hfringe]

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore} {fringeSegment : Nat}
    (hbp :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hfringe :
      forall address,
        storeA.readWord? fringeSegment address =
          storeB.readWord? fringeSegment address)
    (blockSize leftClose seed : Nat) :
    bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        shape storeA fringeSegment blockSize leftClose seed =
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        shape storeB fringeSegment blockSize leftClose seed := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [localBPWindowBitsTraceResultWithStore_store_parametric shape hbp]
  simp only [bpFringeChunkFoldTraceResultAtSegmentWithStore_store_parametric
    hfringe]

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore} {fringeSegment : Nat}
    (hbp :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hfringe :
      forall address,
        storeA.readWord? fringeSegment address =
          storeB.readWord? fringeSegment address)
    (blockSize rightClose seed : Nat) :
    bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        shape storeA fringeSegment blockSize rightClose seed =
      bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        shape storeB fringeSegment blockSize rightClose seed := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [localBPWindowBitsTraceResultWithStore_store_parametric shape hbp]
  simp only [bpFringeChunkFoldTraceResultAtSegmentWithStore_store_parametric
    hfringe]

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize leftClose seed).trace ->
        event.matchesReadStore store := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPWindowBitsTraceResultWithStore_matchesReadStore
        shape store blockSize leftClose
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_matchesReadStore
        store fringeSegment _ _ seed _ _ _

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize rightClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize rightClose seed).trace ->
        event.matchesReadStore store := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPWindowBitsTraceResultWithStore_matchesReadStore
        shape store blockSize rightClose
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_matchesReadStore
        store fringeSegment _ _ seed _ _ _

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize leftClose seed).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store blockSize leftClose
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
        store fringeSegment _ _ seed _ _ _

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize rightClose seed : Nat) :
    forall event,
      List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize rightClose seed).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact
      localBPWindowBitsTraceResultWithStore_no_syntheticCostOnlyPrimitive
        shape store blockSize rightClose
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
        store fringeSegment _ _ seed _ _ _

/-! ## Chunked cross-block close consumers -/

/--
The accepted all-size structural cross-block close consumer with its two
event-silent fringe leaves replaced by the charged chunked fringe traces.
Everything else — rank seeds, interior component replay, merge — is
byte-identical to
`crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments`.
-/
def bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
          shape fringeSegment blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
                shape segments (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (bpChunkedRightFringeCandidateSeededTraceResultAtSegment
                      shape fringeSegment blockSize rightClose rightSeed)

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
      shape rankCloseTrace segments fringeSegment leftClose
      rightClose).toCosted =
      bpChunkedCrossBlockCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose := by
  unfold bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  unfold bpChunkedCrossBlockCloseCostedWithRankSeed
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_refines,
      bpChunkedRightFringeCandidateSeededTraceResultAtSegment_refines,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural_refines,
      blockSize, hmiddle]
  case neg =>
    simp [localBPSeedFromRankCloseTraceResult_refines, hrank,
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_refines,
      bpChunkedRightFringeCandidateSeededTraceResultAtSegment_refines,
      blockSize, hmiddle]

/--
Trace-level exact-value substitution at the accepted cross-block call site:
under the accepted route's own query-side facts, the chunked structural
trace returns exactly the value of the accepted structural trace
(`crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments`).
-/
theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_value_eq
    {shape : Cartesian.CartesianShape}
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    {left len leftClose rightClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseTrace pos).value =
          Succinct.rankPrefix false shape.bpCode pos)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose <
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
        shape rankCloseTrace segments fringeSegment leftClose
        rightClose).value =
      (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
        shape rankCloseTrace segments leftClose rightClose).value := by
  have hchunked :=
    congrArg Costed.value
      (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines
        shape rankCloseTrace (fun pos => (rankCloseTrace pos).toCosted)
        segments fringeSegment leftClose rightClose (fun _ => rfl))
  have haccepted :=
    congrArg Costed.value
      (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines
        shape rankCloseTrace (fun pos => (rankCloseTrace pos).toCosted)
        segments leftClose rightClose (fun _ => rfl))
  have hsub :=
    bpChunkedCrossBlockCloseCostedWithRankSeed_value_eq
      (shape := shape)
      (rankCloseCosted := fun pos => (rankCloseTrace pos).toCosted)
      (left := left) (len := len)
      (fun pos => hrankExact pos)
      hlen hbound hleft hright hcross
  calc
    (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
        shape rankCloseTrace segments fringeSegment leftClose
        rightClose).value =
        (bpChunkedCrossBlockCloseCostedWithRankSeed shape
          (fun pos => (rankCloseTrace pos).toCosted) leftClose
          rightClose).value := hchunked
    _ = (canonicalCrossBlockCloseCostedWithRankSeed shape
          (fun pos => (rankCloseTrace pos).toCosted) leftClose
          rightClose).value := hsub
    _ = (crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
          shape rankCloseTrace segments leftClose rightClose).value :=
      haccepted.symm

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace -> P event)
    (hfringeLeft :
      forall blockSize close seed event,
        List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize close seed).trace ->
          P event)
    (hfringeRight :
      forall blockSize close seed event,
        List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegment
            shape fringeSegment blockSize close seed).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
            shape segments startBlock count).trace ->
          P event) :
    forall event,
      List.Mem event
          (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
            shape rankCloseTrace segments fringeSegment leftClose
            rightClose).trace ->
        P event := by
  unfold bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  intro event hmem
  by_cases hmiddle :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose + 1 <
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact
        hfringeLeft blockSize leftClose
          (localBPSeedFromRankCloseTraceResult
            shape rankCloseTrace blockSize leftClose).value event
          (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact hinterior
        (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          leftClose + 1)
        (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose -
          blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          leftClose - 1)
        event hmem
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact
        hfringeRight blockSize rightClose
          (localBPSeedFromRankCloseTraceResult
            shape rankCloseTrace blockSize rightClose).value event
          (by simpa [blockSize] using hmem)
  · simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, hmiddle] at hmem
    rcases List.mem_append.mp hmem with hmem | htail
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize leftClose P hrank event
        (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | htail
    · exact
        hfringeLeft blockSize leftClose
          (localBPSeedFromRankCloseTraceResult
            shape rankCloseTrace blockSize leftClose).value event
          (by simpa [blockSize] using hmem)
    rcases List.mem_append.mp htail with hmem | hmem
    · exact localBPSeedFromRankCloseTraceResult_trace_forall
        shape rankCloseTrace blockSize rightClose P hrank event
        (by simpa [blockSize] using hmem)
    · exact
        hfringeRight blockSize rightClose
          (localBPSeedFromRankCloseTraceResult
            shape rankCloseTrace blockSize rightClose).value event
          (by simpa [blockSize] using hmem)

/-- Supplied-store chunked cross-block close consumer. -/
def bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  WordRAM.TraceResult.bind
    (localBPSeedFromRankCloseTraceResult
      shape rankCloseTrace blockSize leftClose)
    fun leftSeed =>
      WordRAM.TraceResult.bind
        (bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
          shape store fringeSegment blockSize leftClose leftSeed)
        fun left? =>
          WordRAM.TraceResult.bind
            (if leftBlock + 1 < rightBlock then
              concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
                shape segments store (leftBlock + 1)
                (rightBlock - leftBlock - 1)
            else
              WordRAM.TraceResult.pure none)
            fun middle? =>
              WordRAM.TraceResult.bind
                (localBPSeedFromRankCloseTraceResult
                  shape rankCloseTrace blockSize rightClose)
                fun rightSeed =>
                  WordRAM.TraceResult.map
                    (fun right? =>
                      bpCandidateClose?
                        (bpCandidateMerge3? left? middle? right?))
                    (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
                      shape store fringeSegment blockSize rightClose
                      rightSeed)

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {fringeSegment : Nat}
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore
            shape).store.words[address]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)
    (leftClose rightClose : Nat) :
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments fringeSegment store leftClose
        rightClose =
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
        shape rankCloseTrace segments fringeSegment leftClose
        rightClose := by
  unfold bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  unfold bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [blockSize, hmiddle,
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_eq_of_agree
        hbpCode hfringe,
      bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_eq_of_agree
        hbpCode hfringe,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_eq_of_agree
        shape segments hcomponent]
  case neg =>
    simp [blockSize, hmiddle,
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_eq_of_agree
        hbpCode hfringe,
      bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_eq_of_agree
        hbpCode hfringe]

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_refines_of_agree
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (rankCloseCosted : Nat -> Costed Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {fringeSegment : Nat}
    {store : WordRAM.ReadStore}
    (hbpCode :
      forall index,
        store.readWord? 0 index =
          (SuccinctSpace.chunkPayloadWords
            (SuccinctRank.machineWordBits shape.bpCode.length)
            shape.bpCode).toArray[index]?)
    (hcomponent :
      forall address,
        store.readWord? segments.canonicalComponent address =
          (canonicalRelativeRmmInteriorComponentStore
            shape).store.words[address]?)
    (hfringe :
      forall address,
        store.readWord? fringeSegment address =
          (bpFringeChunkTable
            (bpFringeChunkBits shape.bpCode.length)).store.words[address]?)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos, (rankCloseTrace pos).toCosted = rankCloseCosted pos) :
    (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
      shape rankCloseTrace segments fringeSegment store leftClose
      rightClose).toCosted =
      bpChunkedCrossBlockCloseCostedWithRankSeed
        shape rankCloseCosted leftClose rightClose := by
  rw [bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_eq_of_agree
    shape rankCloseTrace segments hbpCode hcomponent hfringe leftClose
    rightClose]
  exact
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments_refines
      shape rankCloseTrace rankCloseCosted segments fringeSegment
      leftClose rightClose hrank

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    {fringeSegment : Nat}
    {storeA storeB : WordRAM.ReadStore}
    (hbp :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hcomponent :
      forall address,
        storeA.readWord? segments.canonicalComponent address =
          storeB.readWord? segments.canonicalComponent address)
    (hfringe :
      forall address,
        storeA.readWord? fringeSegment address =
          storeB.readWord? fringeSegment address)
    (leftClose rightClose : Nat) :
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments fringeSegment storeA leftClose
        rightClose =
      bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments fringeSegment storeB leftClose
        rightClose := by
  unfold bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  by_cases hmiddle :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  case pos =>
    simp [blockSize, hmiddle,
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_store_parametric
        shape hbp hfringe,
      bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_store_parametric
        shape hbp hfringe,
      concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_store_parametric
        shape segments hcomponent]
  case neg =>
    simp [blockSize, hmiddle,
      bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_store_parametric
        shape hbp hfringe,
      bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_store_parametric
        shape hbp hfringe]

/--
Every charged chunked left-fringe invocation actually reads the fringe
chunk table: the fold visits at least one chunk on every argument.
-/
theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_fringe_mayRead
    (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose seed : Nat) :
    ∃ index word?,
      WordRAM.TraceEvent.readWord fringeSegment index word? ∈
        (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
          shape fringeSegment blockSize leftClose seed).trace := by
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let cnt :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  let relLo := start - base
  let relHi := start + cnt - 1 - base
  let window := localBPWindowBits shape blockSize leftClose
  let slot :=
    bpFringeChunkSlot c (bpFringeWindowChunkValue c window 0)
      (bpFringeChunkStartOff c relLo 0) (bpFringeChunkEndOff c relHi 0)
  have hmem :=
    bpFringeChunkFoldTraceResultAtSegment_head_mem
      (bpFringeChunkTable c) fringeSegment c window seed relLo relHi
      (Nat.min (relHi / c + 1) 33)
      (Nat.lt_min.mpr ⟨Nat.succ_pos _, by omega⟩)
  have hcand :
      WordRAM.TraceEvent.readWord fringeSegment slot
          (bpFringeChunkTable c).store.words[slot]? ∈
        (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
          shape fringeSegment blockSize leftClose seed).trace := by
    show WordRAM.TraceEvent.readWord fringeSegment slot
        (bpFringeChunkTable c).store.words[slot]? ∈
      (WordRAM.TraceResult.bind
        (localBPWindowBitsTraceResult shape blockSize leftClose)
        (fun window =>
          WordRAM.TraceResult.map
            (fun st => bpFringeCandGlobal base seed start st.2)
            (bpFringeChunkFoldTraceResultAtSegment (bpFringeChunkTable c)
              fringeSegment c window seed relLo relHi
              (Nat.min (relHi / c + 1) 33)))).trace
    rw [WordRAM.TraceResult.bind_trace]
    apply List.mem_append_right
    rw [WordRAM.TraceResult.map_trace]
    rw [localBPWindowBitsTraceResult_value]
    exact hmem
  exact ⟨slot, _, hcand⟩

/-- Window-read events belong to the charged chunked left-fringe trace. -/
theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_window_mem
    (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose seed : Nat)
    {event : WordRAM.TraceEvent}
    (hmem :
      List.Mem event
        (localBPWindowBitsTraceResult shape blockSize leftClose).trace) :
    List.Mem event
      (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
        shape fringeSegment blockSize leftClose seed).trace := by
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let cnt :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  let relLo := start - base
  let relHi := start + cnt - 1 - base
  show List.Mem event
    (WordRAM.TraceResult.bind
      (localBPWindowBitsTraceResult shape blockSize leftClose)
      (fun window =>
        WordRAM.TraceResult.map
          (fun st => bpFringeCandGlobal base seed start st.2)
          (bpFringeChunkFoldTraceResultAtSegment (bpFringeChunkTable c)
            fringeSegment c window seed relLo relHi
            (Nat.min (relHi / c + 1) 33)))).trace
  rw [WordRAM.TraceResult.bind_trace]
  exact List.mem_append_left _ hmem

/--
Every charged chunked left-fringe invocation performs a successful
chunk-table read: the visited slots are inside the stored row range.
-/
theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegment_fringe_successful_mayRead
    (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose seed : Nat) :
    ∃ index word,
      WordRAM.TraceEvent.readWord fringeSegment index (some word) ∈
        (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
          shape fringeSegment blockSize leftClose seed).trace := by
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let cnt :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  let relLo := start - base
  let relHi := start + cnt - 1 - base
  let window := localBPWindowBits shape blockSize leftClose
  let slot :=
    bpFringeChunkSlot c (bpFringeWindowChunkValue c window 0)
      (bpFringeChunkStartOff c relLo 0) (bpFringeChunkEndOff c relHi 0)
  have hsize :
      (bpFringeChunkTable c).store.words.size = bpFringeChunkRowCount c := by
    simp [bpFringeChunkTable, SuccinctSpace.FixedWidthNatTable.ofEntries,
      SuccinctSpace.FixedWidthNatTable.ofEncodedWords]
  have hslotLt : slot < (bpFringeChunkTable c).store.words.size := by
    rw [hsize]
    exact
      bpFringeChunkSlot_lt_rowCount
        (bpFringeWindowChunkValue_lt c window 0)
        (bpFringeChunkStartOff_le c relLo 0)
        (bpFringeChunkEndOff_le c relHi 0)
  have hword :
      (bpFringeChunkTable c).store.words[slot]? =
        some ((bpFringeChunkTable c).store.words[slot]'hslotLt) := by
    simp [hslotLt]
  have hmem :=
    bpFringeChunkFoldTraceResultAtSegment_head_mem
      (bpFringeChunkTable c) fringeSegment c window seed relLo relHi
      (Nat.min (relHi / c + 1) 33)
      (Nat.lt_min.mpr ⟨Nat.succ_pos _, by omega⟩)
  rw [hword] at hmem
  have hcand :
      WordRAM.TraceEvent.readWord fringeSegment slot
          (some ((bpFringeChunkTable c).store.words[slot]'hslotLt)) ∈
        (bpChunkedLeftFringeCandidateSeededTraceResultAtSegment
          shape fringeSegment blockSize leftClose seed).trace := by
    show WordRAM.TraceEvent.readWord fringeSegment slot
        (some ((bpFringeChunkTable c).store.words[slot]'hslotLt)) ∈
      (WordRAM.TraceResult.bind
        (localBPWindowBitsTraceResult shape blockSize leftClose)
        (fun window =>
          WordRAM.TraceResult.map
            (fun st => bpFringeCandGlobal base seed start st.2)
            (bpFringeChunkFoldTraceResultAtSegment (bpFringeChunkTable c)
              fringeSegment c window seed relLo relHi
              (Nat.min (relHi / c + 1) 33)))).trace
    rw [WordRAM.TraceResult.bind_trace]
    apply List.mem_append_right
    rw [WordRAM.TraceResult.map_trace]
    rw [localBPWindowBitsTraceResult_value]
    exact hmem
  exact ⟨slot, _, hcand⟩

theorem bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_trace_forall
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize leftClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize leftClose).trace ->
          P event)
    (hfringe :
      forall address,
        address <
          bpFringeChunkRowCount (bpFringeChunkBits shape.bpCode.length) ->
        P (WordRAM.TraceEvent.readWord fringeSegment address
          (store.readWord? fringeSegment address))) :
    forall event,
      List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize leftClose seed).trace ->
        P event := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hbp
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_trace_forall
        store fringeSegment _ _ seed _ _ _ P hfringe

theorem bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_trace_forall
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (fringeSegment blockSize rightClose seed : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hbp :
      forall event,
        List.Mem event
          (localBPWindowBitsTraceResultWithStore
            shape store blockSize rightClose).trace ->
          P event)
    (hfringe :
      forall address,
        address <
          bpFringeChunkRowCount (bpFringeChunkBits shape.bpCode.length) ->
        P (WordRAM.TraceEvent.readWord fringeSegment address
          (store.readWord? fringeSegment address))) :
    forall event,
      List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize rightClose seed).trace ->
        P event := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  apply WordRAM.TraceResult.bind_trace_forall
  · exact hbp
  · apply WordRAM.TraceResult.map_trace_forall
    exact
      bpFringeChunkFoldTraceResultAtSegmentWithStore_trace_forall
        store fringeSegment _ _ seed _ _ _ P hfringe

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall pos event, List.Mem event (rankCloseTrace pos).trace -> P event)
    (hfringeLeft :
      forall blockSize close seed event,
        List.Mem event
          (bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize close seed).trace ->
          P event)
    (hfringeRight :
      forall blockSize close seed event,
        List.Mem event
          (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
            shape store fringeSegment blockSize close seed).trace ->
          P event)
    (hinterior :
      forall startBlock count event,
        List.Mem event
          (concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store startBlock count).trace -> P event) :
    forall event,
      List.Mem event
          (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments fringeSegment store leftClose
            rightClose).trace ->
        P event := by
  unfold bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  apply WordRAM.TraceResult.bind_trace_forall
  case hresult =>
    exact localBPSeedFromRankCloseTraceResult_trace_forall
      shape rankCloseTrace blockSize leftClose P hrank
  case hnext =>
    apply WordRAM.TraceResult.bind_trace_forall
    case hresult =>
      exact hfringeLeft blockSize leftClose _
    case hnext =>
      apply WordRAM.TraceResult.bind_trace_forall
      case hresult =>
        by_cases hmiddle :
            blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose
        case pos =>
          simpa [blockSize, hmiddle] using
            hinterior (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)
        case neg =>
          simp [blockSize, hmiddle]
      case hnext =>
        apply WordRAM.TraceResult.bind_trace_forall
        case hresult =>
          exact localBPSeedFromRankCloseTraceResult_trace_forall
            shape rankCloseTrace blockSize rightClose P hrank
        case hnext =>
          exact WordRAM.TraceResult.map_trace_forall P _ _
            (hfringeRight blockSize rightClose _)

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          event.matchesReadStore store) :
    forall event,
      List.Mem event
          (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments fringeSegment store leftClose
            rightClose).trace ->
        event.matchesReadStore store := by
  exact
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
      shape rankCloseTrace segments fringeSegment store leftClose
      rightClose
      (fun event => event.matchesReadStore store) hrank
      (fun blockSize close seed =>
        bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_matchesReadStore
          shape store fringeSegment blockSize close seed)
      (fun blockSize close seed =>
        bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_matchesReadStore
          shape store fringeSegment blockSize close seed)
      (fun startBlock count =>
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_matchesReadStore
          shape segments store startBlock count)

theorem bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat)
    (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat)
    (hrank :
      forall pos event,
        List.Mem event (rankCloseTrace pos).trace ->
          Not event.isSyntheticCostOnlyPrimitive) :
    forall event,
      List.Mem event
          (bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
            shape rankCloseTrace segments fringeSegment store leftClose
            rightClose).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  exact
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore_trace_forall
      shape rankCloseTrace segments fringeSegment store leftClose
      rightClose
      (fun event => Not event.isSyntheticCostOnlyPrimitive) hrank
      (fun blockSize close seed =>
        bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
          shape store fringeSegment blockSize close seed)
      (fun blockSize close seed =>
        bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
          shape store fringeSegment blockSize close seed)
      (fun startBlock count =>
        concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
          shape segments store startBlock count)

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose

end RMQ
