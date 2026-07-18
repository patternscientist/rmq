import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeaves
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTrace

/-!
# Charged chunked in-word rank/select: Word-RAM trace layer (B3)

`WordRAM.TraceResult` twins of the charged chunked in-word rank/select
folds, segment-parameterized in the house `AtSegment(s)` style.  Each
charged chunk read is one genuine `readWord segment slot` event whose
recorded word is the supplied store's word and whose decoded value drives
the fold — the same operational discipline as `Program.evalR`'s `readWord`
case, generalized to the data-dependent chunk addressing.

The rank fold reads one segment (the fringe chunk table's global segment);
the select fold reads two (the rank reads route the fold, the final read
hits the select chunk table's segment).  Refinement to the M3 `Costed`
folds holds under per-segment store agreement with the honest tables, and
the canonical address bound for the select-table read is recovered from
honest-rank-table agreement (the routing count of an honest entry never
exceeds the slice length, so the occurrence argument of the select slot is
in range whenever the read fires).
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-! ## One charged chunk-table word read against a supplied store -/

/--
One charged table-word read at a global segment: the emitted event records
the supplied store's word at that address, and the returned value is its
`bitsToNatLE` decode.
-/
def bpChunkReadTraceResult (store : WordRAM.ReadStore)
    (segment i : Nat) : WordRAM.TraceResult (Option Nat) where
  value := (store.readWord? segment i).map SuccinctSpace.bitsToNatLE
  trace :=
    [WordRAM.TraceEvent.readWord segment i (store.readWord? segment i)]

theorem bpChunkReadTraceResult_toCosted_of_agree
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {store : WordRAM.ReadStore} {segment : Nat}
    (hagree :
      forall address,
        store.readWord? segment address = table.store.words[address]?)
    (i : Nat) :
    (bpChunkReadTraceResult store segment i).toCosted =
      table.readCosted i := by
  apply Costed.ext
  · show (store.readWord? segment i).map SuccinctSpace.bitsToNatLE =
      (table.readCosted i).value
    rw [hagree i]
    rfl
  · show (1 : Nat) = (table.readCosted i).cost
    simp

theorem bpChunkReadTraceResult_trace_forall
    (store : WordRAM.ReadStore) (segment i : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      P (WordRAM.TraceEvent.readWord segment i
        (store.readWord? segment i))) :
    forall event,
      List.Mem event (bpChunkReadTraceResult store segment i).trace ->
        P event := by
  intro event hmem
  cases hmem with
  | head => exact hread
  | tail _ hmem' => cases hmem'

theorem bpChunkReadTraceResult_matchesReadStore
    (store : WordRAM.ReadStore) (segment i : Nat) :
    forall event,
      List.Mem event (bpChunkReadTraceResult store segment i).trace ->
        event.matchesReadStore store := by
  apply bpChunkReadTraceResult_trace_forall
  rfl

theorem bpChunkReadTraceResult_no_syntheticCostOnlyPrimitive
    (store : WordRAM.ReadStore) (segment i : Nat) :
    forall event,
      List.Mem event (bpChunkReadTraceResult store segment i).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpChunkReadTraceResult_trace_forall
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpChunkReadTraceResult_store_parametric
    {storeA storeB : WordRAM.ReadStore} {segment : Nat}
    (hread :
      forall address,
        storeA.readWord? segment address =
          storeB.readWord? segment address)
    (i : Nat) :
    bpChunkReadTraceResult storeA segment i =
      bpChunkReadTraceResult storeB segment i := by
  unfold bpChunkReadTraceResult
  rw [hread i]

/-! ## The charged in-word rank fold as a segment trace -/

/-- Supplied-store trace twin of `bpChunkedWordRankCostedFrom`. -/
def bpChunkedWordRankTraceFromWithStore (store : WordRAM.ReadStore)
    (tableSegment c : Nat) (target : Bool) (word : List Bool) (e : Nat) :
    Nat -> Nat -> Nat -> WordRAM.TraceResult Nat
  | _j, 0, acc => WordRAM.TraceResult.pure acc
  | j, count + 1, acc =>
      WordRAM.TraceResult.bind
        (bpChunkReadTraceResult store tableSegment
          (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
            (bpWordChunkSliceLen c e j) (bpWordChunkSliceLen c e j)))
        (fun entry? =>
          bpChunkedWordRankTraceFromWithStore store tableSegment c target
            word e (j + 1) count
            (bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j)
              acc entry?))

/-- Supplied-store trace twin of `bpChunkedWordRankCosted`. -/
def bpChunkedWordRankTraceResultAtSegmentWithStore
    (store : WordRAM.ReadStore) (tableSegment c : Nat) (target : Bool)
    (word : List Bool) (limit : Nat) : WordRAM.TraceResult Nat :=
  bpChunkedWordRankTraceFromWithStore store tableSegment c target word
    (bpWordRankEffLimit word limit) 0
    (bpWordChunkCount c (bpWordRankEffLimit word limit)) 0

/--
Refinement under store agreement at the table segment: the trace fold's
Costed projection is exactly the M3 charged rank fold on the agreed table.
-/
theorem bpChunkedWordRankTraceFromWithStore_toCosted_of_agree
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {store : WordRAM.ReadStore} {tableSegment : Nat}
    (hagree :
      forall address,
        store.readWord? tableSegment address =
          table.store.words[address]?)
    (c : Nat) (target : Bool) (word : List Bool) (e : Nat) :
    forall (count j acc : Nat),
      (bpChunkedWordRankTraceFromWithStore store tableSegment c target
          word e j count acc).toCosted =
        bpChunkedWordRankCostedFrom table c target word e j count acc := by
  intro count
  induction count with
  | zero =>
      intro j acc
      rfl
  | succ count ih =>
      intro j acc
      show
        (WordRAM.TraceResult.bind
            (bpChunkReadTraceResult store tableSegment
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c e j)
                (bpWordChunkSliceLen c e j)))
            _).toCosted = _
      rw [WordRAM.TraceResult.bind_toCosted]
      rw [bpChunkReadTraceResult_toCosted_of_agree table hagree]
      show
        Costed.bind (table.readCosted _) _ =
          bpChunkedWordRankCostedFrom table c target word e j (count + 1)
            acc
      show
        Costed.bind (table.readCosted _) _ =
          Costed.bind (table.readCosted _) _
      congr 1
      funext entry?
      exact ih (j + 1) _

theorem bpChunkedWordRankTraceResultAtSegmentWithStore_toCosted_of_agree
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {store : WordRAM.ReadStore} {tableSegment : Nat}
    (hagree :
      forall address,
        store.readWord? tableSegment address =
          table.store.words[address]?)
    (c : Nat) (target : Bool) (word : List Bool) (limit : Nat) :
    (bpChunkedWordRankTraceResultAtSegmentWithStore store tableSegment c
        target word limit).toCosted =
      bpChunkedWordRankCosted table c target word limit := by
  exact
    bpChunkedWordRankTraceFromWithStore_toCosted_of_agree table hagree c
      target word _ _ 0 0

/--
Every rank-fold trace event is one table-segment read of the supplied
store's word at a row-count-bounded slot.
-/
theorem bpChunkedWordRankTraceFromWithStore_trace_forall
    (store : WordRAM.ReadStore) (tableSegment c : Nat) (target : Bool)
    (word : List Bool) (e : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord tableSegment address
          (store.readWord? tableSegment address))) :
    forall (count j acc : Nat) (event : WordRAM.TraceEvent),
      List.Mem event
          (bpChunkedWordRankTraceFromWithStore store tableSegment c
            target word e j count acc).trace ->
        P event := by
  intro count
  induction count with
  | zero =>
      intro j acc event hmem
      cases hmem
  | succ count ih =>
      intro j acc
      show
        forall event,
          List.Mem event
              (WordRAM.TraceResult.bind
                (bpChunkReadTraceResult store tableSegment
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c e j)
                    (bpWordChunkSliceLen c e j)))
                _).trace -> P event
      apply WordRAM.TraceResult.bind_trace_forall
      · apply bpChunkReadTraceResult_trace_forall
        apply hread
        exact
          bpFringeChunkSlot_lt_rowCount
            (bpFringeWindowChunkValue_lt c word j)
            (bpWordChunkSliceLen_le c e j)
            (bpWordChunkSliceLen_le c e j)
      · intro event hmem
        exact ih (j + 1) _ event hmem

theorem bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
    (store : WordRAM.ReadStore) (tableSegment c : Nat) (target : Bool)
    (word : List Bool) (limit : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hread :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord tableSegment address
          (store.readWord? tableSegment address))) :
    forall event,
      List.Mem event
          (bpChunkedWordRankTraceResultAtSegmentWithStore store
            tableSegment c target word limit).trace ->
        P event := by
  exact
    bpChunkedWordRankTraceFromWithStore_trace_forall store tableSegment c
      target word _ P hread _ 0 0

theorem bpChunkedWordRankTraceResultAtSegmentWithStore_matchesReadStore
    (store : WordRAM.ReadStore) (tableSegment c : Nat) (target : Bool)
    (word : List Bool) (limit : Nat) :
    forall event,
      List.Mem event
          (bpChunkedWordRankTraceResultAtSegmentWithStore store
            tableSegment c target word limit).trace ->
        event.matchesReadStore store := by
  apply bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
  intro address _hlt
  rfl

theorem bpChunkedWordRankTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    (store : WordRAM.ReadStore) (tableSegment c : Nat) (target : Bool)
    (word : List Bool) (limit : Nat) :
    forall event,
      List.Mem event
          (bpChunkedWordRankTraceResultAtSegmentWithStore store
            tableSegment c target word limit).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply bpChunkedWordRankTraceResultAtSegmentWithStore_trace_forall
  intro address _hlt
  simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpChunkedWordRankTraceFromWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore} {tableSegment : Nat}
    (hread :
      forall address,
        storeA.readWord? tableSegment address =
          storeB.readWord? tableSegment address)
    (c : Nat) (target : Bool) (word : List Bool) (e : Nat) :
    forall (count j acc : Nat),
      bpChunkedWordRankTraceFromWithStore storeA tableSegment c target
          word e j count acc =
        bpChunkedWordRankTraceFromWithStore storeB tableSegment c target
          word e j count acc := by
  intro count
  induction count with
  | zero =>
      intro j acc
      rfl
  | succ count ih =>
      intro j acc
      show
        WordRAM.TraceResult.bind (bpChunkReadTraceResult storeA _ _) _ =
          WordRAM.TraceResult.bind (bpChunkReadTraceResult storeB _ _) _
      rw [bpChunkReadTraceResult_store_parametric hread]
      congr 1
      funext entry?
      exact ih (j + 1) _

theorem bpChunkedWordRankTraceResultAtSegmentWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore} {tableSegment : Nat}
    (hread :
      forall address,
        storeA.readWord? tableSegment address =
          storeB.readWord? tableSegment address)
    (c : Nat) (target : Bool) (word : List Bool) (limit : Nat) :
    bpChunkedWordRankTraceResultAtSegmentWithStore storeA tableSegment c
        target word limit =
      bpChunkedWordRankTraceResultAtSegmentWithStore storeB tableSegment
        c target word limit := by
  exact
    bpChunkedWordRankTraceFromWithStore_store_parametric hread c target
      word _ _ 0 0

/-! ## The charged in-word select fold as a two-segment trace -/

/-- Supplied-store trace twin of `bpChunkedWordSelectCostedFrom`. -/
def bpChunkedWordSelectTraceFromWithStore (store : WordRAM.ReadStore)
    (rankSegment selectSegment c : Nat) (target : Bool)
    (word : List Bool) :
    Nat -> Nat -> Nat -> WordRAM.TraceResult (Option Nat)
  | _j, 0, _k => WordRAM.TraceResult.pure none
  | j, count + 1, k =>
      WordRAM.TraceResult.bind
        (bpChunkReadTraceResult store rankSegment
          (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
            (bpWordChunkSliceLen c word.length j)
            (bpWordChunkSliceLen c word.length j)))
        (fun entry? =>
          if k <
              bpChunkRankOfEntry c target
                (bpWordChunkSliceLen c word.length j)
                (entry?.getD 0) then
            WordRAM.TraceResult.map (fun sel? => some (j * c + sel?.getD 0))
              (bpChunkReadTraceResult store selectSegment
                (bpChunkSelectSlot c (bpFringeWindowChunkValue c word j)
                  k))
          else
            bpChunkedWordSelectTraceFromWithStore store rankSegment
              selectSegment c target word (j + 1) count
              (k -
                bpChunkRankOfEntry c target
                  (bpWordChunkSliceLen c word.length j)
                  (entry?.getD 0)))

/-- Supplied-store trace twin of `bpChunkedWordSelectCosted`. -/
def bpChunkedWordSelectTraceResultAtSegmentsWithStore
    (store : WordRAM.ReadStore) (rankSegment selectSegment c : Nat)
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  bpChunkedWordSelectTraceFromWithStore store rankSegment selectSegment c
    target word 0 (bpWordChunkCount c word.length) occurrence

/--
Refinement under per-segment store agreement with the honest tables: the
trace fold's Costed projection is exactly the M3 charged select fold.
-/
theorem bpChunkedWordSelectTraceFromWithStore_toCosted_of_agree
    {entriesR : List Nat} {widthR : Nat} {entriesS : List Nat}
    {widthS : Nat}
    (rankTable : SuccinctSpace.FixedWidthNatTable entriesR widthR)
    (selTable : SuccinctSpace.FixedWidthNatTable entriesS widthS)
    {store : WordRAM.ReadStore} {rankSegment selectSegment : Nat}
    (hrank :
      forall address,
        store.readWord? rankSegment address =
          rankTable.store.words[address]?)
    (hsel :
      forall address,
        store.readWord? selectSegment address =
          selTable.store.words[address]?)
    (c : Nat) (target : Bool) (word : List Bool) :
    forall (count j k : Nat),
      (bpChunkedWordSelectTraceFromWithStore store rankSegment
          selectSegment c target word j count k).toCosted =
        bpChunkedWordSelectCostedFrom rankTable selTable c target word j
          count k := by
  intro count
  induction count with
  | zero =>
      intro j k
      rfl
  | succ count ih =>
      intro j k
      show
        (WordRAM.TraceResult.bind
            (bpChunkReadTraceResult store rankSegment
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j)))
            _).toCosted = _
      rw [WordRAM.TraceResult.bind_toCosted]
      rw [bpChunkReadTraceResult_toCosted_of_agree rankTable hrank]
      show
        Costed.bind (rankTable.readCosted _) _ =
          Costed.bind (rankTable.readCosted _) _
      congr 1
      funext entry?
      by_cases hfound :
          k <
            bpChunkRankOfEntry c target
              (bpWordChunkSliceLen c word.length j) (entry?.getD 0)
      · rw [if_pos hfound, if_pos hfound]
        rw [WordRAM.TraceResult.map_toCosted]
        rw [bpChunkReadTraceResult_toCosted_of_agree selTable hsel]
      · rw [if_neg hfound, if_neg hfound]
        exact ih (j + 1) _

theorem bpChunkedWordSelectTraceResultAtSegmentsWithStore_toCosted_of_agree
    {entriesR : List Nat} {widthR : Nat} {entriesS : List Nat}
    {widthS : Nat}
    (rankTable : SuccinctSpace.FixedWidthNatTable entriesR widthR)
    (selTable : SuccinctSpace.FixedWidthNatTable entriesS widthS)
    {store : WordRAM.ReadStore} {rankSegment selectSegment : Nat}
    (hrank :
      forall address,
        store.readWord? rankSegment address =
          rankTable.store.words[address]?)
    (hsel :
      forall address,
        store.readWord? selectSegment address =
          selTable.store.words[address]?)
    (c : Nat) (target : Bool) (word : List Bool) (occurrence : Nat) :
    (bpChunkedWordSelectTraceResultAtSegmentsWithStore store rankSegment
        selectSegment c target word occurrence).toCosted =
      bpChunkedWordSelectCosted rankTable selTable c target word
        occurrence := by
  exact
    bpChunkedWordSelectTraceFromWithStore_toCosted_of_agree rankTable
      selTable hrank hsel c target word _ 0 occurrence

/--
General event shape for the supplied-store select fold: rank-segment reads
at row-count-bounded slots, plus select-segment reads of the supplied
store's words.
-/
theorem bpChunkedWordSelectTraceFromWithStore_trace_forall
    (store : WordRAM.ReadStore) (rankSegment selectSegment c : Nat)
    (target : Bool) (word : List Bool)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord rankSegment address
          (store.readWord? rankSegment address)))
    (hsel :
      forall address,
        P (WordRAM.TraceEvent.readWord selectSegment address
          (store.readWord? selectSegment address))) :
    forall (count j k : Nat) (event : WordRAM.TraceEvent),
      List.Mem event
          (bpChunkedWordSelectTraceFromWithStore store rankSegment
            selectSegment c target word j count k).trace ->
        P event := by
  intro count
  induction count with
  | zero =>
      intro j k event hmem
      cases hmem
  | succ count ih =>
      intro j k
      show
        forall event,
          List.Mem event
              (WordRAM.TraceResult.bind
                (bpChunkReadTraceResult store rankSegment
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c word.length j)
                    (bpWordChunkSliceLen c word.length j)))
                _).trace -> P event
      apply WordRAM.TraceResult.bind_trace_forall
      · apply bpChunkReadTraceResult_trace_forall
        apply hrank
        exact
          bpFringeChunkSlot_lt_rowCount
            (bpFringeWindowChunkValue_lt c word j)
            (bpWordChunkSliceLen_le c word.length j)
            (bpWordChunkSliceLen_le c word.length j)
      · by_cases hfound :
            k <
              bpChunkRankOfEntry c target
                (bpWordChunkSliceLen c word.length j)
                (((bpChunkReadTraceResult store rankSegment
                    (bpFringeChunkSlot c
                      (bpFringeWindowChunkValue c word j)
                      (bpWordChunkSliceLen c word.length j)
                      (bpWordChunkSliceLen c word.length j))).value).getD
                  0)
        · rw [if_pos hfound]
          apply WordRAM.TraceResult.map_trace_forall
          apply bpChunkReadTraceResult_trace_forall
          apply hsel
        · rw [if_neg hfound]
          intro event hmem
          exact ih (j + 1) _ event hmem

theorem bpChunkedWordSelectTraceResultAtSegmentsWithStore_matchesReadStore
    (store : WordRAM.ReadStore) (rankSegment selectSegment c : Nat)
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    forall event,
      List.Mem event
          (bpChunkedWordSelectTraceResultAtSegmentsWithStore store
            rankSegment selectSegment c target word occurrence).trace ->
        event.matchesReadStore store := by
  apply
    bpChunkedWordSelectTraceFromWithStore_trace_forall store rankSegment
      selectSegment c target word
  · intro address _hlt
    rfl
  · intro address
    rfl

theorem bpChunkedWordSelectTraceResultAtSegmentsWithStore_no_syntheticCostOnlyPrimitive
    (store : WordRAM.ReadStore) (rankSegment selectSegment c : Nat)
    (target : Bool) (word : List Bool) (occurrence : Nat) :
    forall event,
      List.Mem event
          (bpChunkedWordSelectTraceResultAtSegmentsWithStore store
            rankSegment selectSegment c target word occurrence).trace ->
        Not event.isSyntheticCostOnlyPrimitive := by
  apply
    bpChunkedWordSelectTraceFromWithStore_trace_forall store rankSegment
      selectSegment c target word
  · intro address _hlt
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]
  · intro address
    simp [WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive]

theorem bpChunkedWordSelectTraceFromWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore}
    {rankSegment selectSegment : Nat}
    (hrank :
      forall address,
        storeA.readWord? rankSegment address =
          storeB.readWord? rankSegment address)
    (hsel :
      forall address,
        storeA.readWord? selectSegment address =
          storeB.readWord? selectSegment address)
    (c : Nat) (target : Bool) (word : List Bool) :
    forall (count j k : Nat),
      bpChunkedWordSelectTraceFromWithStore storeA rankSegment
          selectSegment c target word j count k =
        bpChunkedWordSelectTraceFromWithStore storeB rankSegment
          selectSegment c target word j count k := by
  intro count
  induction count with
  | zero =>
      intro j k
      rfl
  | succ count ih =>
      intro j k
      show
        WordRAM.TraceResult.bind (bpChunkReadTraceResult storeA _ _) _ =
          WordRAM.TraceResult.bind (bpChunkReadTraceResult storeB _ _) _
      rw [bpChunkReadTraceResult_store_parametric hrank]
      congr 1
      funext entry?
      by_cases hfound :
          k <
            bpChunkRankOfEntry c target
              (bpWordChunkSliceLen c word.length j) (entry?.getD 0)
      · rw [if_pos hfound, if_pos hfound]
        rw [bpChunkReadTraceResult_store_parametric hsel]
      · rw [if_neg hfound, if_neg hfound]
        exact ih (j + 1) _

theorem bpChunkedWordSelectTraceResultAtSegmentsWithStore_store_parametric
    {storeA storeB : WordRAM.ReadStore}
    {rankSegment selectSegment : Nat}
    (hrank :
      forall address,
        storeA.readWord? rankSegment address =
          storeB.readWord? rankSegment address)
    (hsel :
      forall address,
        storeA.readWord? selectSegment address =
          storeB.readWord? selectSegment address)
    (c : Nat) (target : Bool) (word : List Bool) (occurrence : Nat) :
    bpChunkedWordSelectTraceResultAtSegmentsWithStore storeA rankSegment
        selectSegment c target word occurrence =
      bpChunkedWordSelectTraceResultAtSegmentsWithStore storeB
        rankSegment selectSegment c target word occurrence := by
  exact
    bpChunkedWordSelectTraceFromWithStore_store_parametric hrank hsel c
      target word _ 0 occurrence

/--
Canonical select-address bound: under honest-rank-table agreement, every
select-segment read the fold fires has its occurrence argument below the
routing count of an honest entry, which never exceeds the slice length, so
the select slot is row-count-bounded.
-/
theorem bpChunkedWordSelectTraceFromWithStore_trace_forall_of_honestRank
    {store : WordRAM.ReadStore} {rankSegment selectSegment c : Nat}
    (hagreeRank :
      forall address,
        store.readWord? rankSegment address =
          (bpFringeChunkTable c).store.words[address]?)
    (target : Bool) (word : List Bool)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord rankSegment address
          (store.readWord? rankSegment address)))
    (hsel :
      forall address,
        address < bpChunkSelectRowCount c ->
        P (WordRAM.TraceEvent.readWord selectSegment address
          (store.readWord? selectSegment address))) :
    forall (count j k : Nat) (event : WordRAM.TraceEvent),
      List.Mem event
          (bpChunkedWordSelectTraceFromWithStore store rankSegment
            selectSegment c target word j count k).trace ->
        P event := by
  intro count
  induction count with
  | zero =>
      intro j k event hmem
      cases hmem
  | succ count ih =>
      intro j k
      have hv := bpFringeWindowChunkValue_lt c word j
      have ht := bpWordChunkSliceLen_le c word.length j
      have hreadVal :
          (bpChunkReadTraceResult store rankSegment
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j))).value =
            some
              (bpFringeChunkPacked c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j)) := by
        show
          (store.readWord? rankSegment
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c word.length j)
                (bpWordChunkSliceLen c word.length j))).map
            SuccinctSpace.bitsToNatLE = _
        rw [hagreeRank]
        rw [(bpFringeChunkTable c).read_exact]
        exact bpFringeChunkEntries_getElem hv ht ht
      show
        forall event,
          List.Mem event
              (WordRAM.TraceResult.bind
                (bpChunkReadTraceResult store rankSegment
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c word.length j)
                    (bpWordChunkSliceLen c word.length j)))
                _).trace -> P event
      apply WordRAM.TraceResult.bind_trace_forall
      · apply bpChunkReadTraceResult_trace_forall
        apply hrank
        exact
          bpFringeChunkSlot_lt_rowCount hv ht ht
      · rw [hreadVal]
        by_cases hfound :
            k <
              bpChunkRankOfEntry c target
                (bpWordChunkSliceLen c word.length j)
                ((some
                    (bpFringeChunkPacked c
                      (bpFringeWindowChunkValue c word j)
                      (bpWordChunkSliceLen c word.length j)
                      (bpWordChunkSliceLen c word.length j))).getD 0)
        · rw [if_pos hfound]
          apply WordRAM.TraceResult.map_trace_forall
          apply bpChunkReadTraceResult_trace_forall
          apply hsel
          -- the routing count of an honest entry is at most the slice
          -- length, so the occurrence argument is in range
          have hdecoded :
              bpChunkRankOfEntry c target
                  (bpWordChunkSliceLen c word.length j)
                  (bpFringeChunkPacked c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c word.length j)
                    (bpWordChunkSliceLen c word.length j)) =
                Succinct.rankPrefix target
                  (bpFringeChunkPattern c
                    (bpFringeWindowChunkValue c word j))
                  (bpWordChunkSliceLen c word.length j) :=
            bpChunkRankOfEntry_packed c target hv ht
          have hle :=
            Succinct.rankPrefix_le_limit target
              (bpFringeChunkPattern c
                (bpFringeWindowChunkValue c word j))
              (bpWordChunkSliceLen c word.length j)
          rw [Option.getD_some] at hfound
          have hk : k <= c := by
            rw [hdecoded] at hfound
            omega
          exact bpChunkSelectSlot_lt_rowCount hv hk
        · rw [if_neg hfound]
          intro event hmem
          exact ih (j + 1) _ event hmem

theorem bpChunkedWordSelectTraceResultAtSegmentsWithStore_trace_forall_of_honestRank
    {store : WordRAM.ReadStore} {rankSegment selectSegment c : Nat}
    (hagreeRank :
      forall address,
        store.readWord? rankSegment address =
          (bpFringeChunkTable c).store.words[address]?)
    (target : Bool) (word : List Bool) (occurrence : Nat)
    (P : WordRAM.TraceEvent -> Prop)
    (hrank :
      forall address,
        address < bpFringeChunkRowCount c ->
        P (WordRAM.TraceEvent.readWord rankSegment address
          (store.readWord? rankSegment address)))
    (hsel :
      forall address,
        address < bpChunkSelectRowCount c ->
        P (WordRAM.TraceEvent.readWord selectSegment address
          (store.readWord? selectSegment address))) :
    forall event,
      List.Mem event
          (bpChunkedWordSelectTraceResultAtSegmentsWithStore store
            rankSegment selectSegment c target word occurrence).trace ->
        P event := by
  exact
    bpChunkedWordSelectTraceFromWithStore_trace_forall_of_honestRank
      hagreeRank target word P hrank hsel _ 0 occurrence

end SuccinctClose

end RMQ
