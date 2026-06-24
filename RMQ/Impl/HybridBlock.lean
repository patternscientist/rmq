import RMQ.Core.Window
import RMQ.Impl.LinearScan
import RMQ.Impl.SparseTable

/-!
# Hybrid block RMQ

This module defines the concrete hybrid query structure while reusing the
shared library pieces:
boundary scans go through `LinearScan.query`, and chunk summaries use the same
leftmost-index combination style as `SparseTable`.
-/

namespace RMQ.HybridBlock

/-- Power-of-two sparse-summary length measured in chunks. -/
def chunkSpan (k : Nat) : Nat :=
  2 ^ k

theorem chunkSpan_pos (k : Nat) :
    0 < chunkSpan k := by
  unfold chunkSpan
  exact Nat.pow_pos (by omega)

theorem chunkSpan_succ (k : Nat) :
    chunkSpan (k + 1) = chunkSpan k + chunkSpan k := by
  unfold chunkSpan
  rw [Nat.pow_succ]
  omega

/-- Public specialization: block size `floor(log2 n) + 1`. -/
def publicBlockSize (xs : List Int) : Nat :=
  Nat.log2 xs.length + 1

/-- Option-level argmin combination. `none` represents an absent subrange. -/
abbrev combineIndex := RMQ.SparseTable.combineIndex

/-- Direct scan over a half-open range. -/
def rangeScan (xs : List Int) (left right : Nat) : Option Nat :=
  RMQ.LinearScan.query xs left right

/-- Sparse-summary cell covering `chunkSpan k` consecutive full chunks. -/
def chunkCell (xs : List Int) (b : Nat) : Nat -> Nat -> Option Nat
  | 0, start =>
      if _h : 0 < b /\ start + b <= xs.length then
        rangeScan xs start (start + b)
      else
        none
  | k + 1, start =>
      combineIndex xs
        (chunkCell xs b k start)
        (chunkCell xs b k (start + chunkSpan k * b))

/-- A materialized sparse-summary row for one power-of-two chunk level. -/
def chunkRow (xs : List Int) (b k : Nat) : List (Option Nat) :=
  List.ofFn (fun i : Fin xs.length => chunkCell xs b k i.1)

/-- Flatten a materialized row lookup. Missing entries and cells are both `none`. -/
abbrev rowCell := RMQ.SparseTable.rowCell

/--
Materialized chunk sparse table.

As with `SparseTable.buildSparseTable`, this uses `xs.length + 1` rows so the
standalone library does not need heavier logarithm monotonicity lemmas.
-/
def buildChunkSparseTable (xs : List Int) (b : Nat) : List (List (Option Nat)) :=
  List.ofFn (fun k : Fin (xs.length + 1) => chunkRow xs b k.1)

/-- Fetch a materialized table row, returning an empty row if the level is absent. -/
abbrev tableRow := RMQ.SparseTable.tableRow

theorem chunkCell_leftmost_exists
    (xs : List Int) (b k start : Nat)
    (hb : 0 < b)
    (hbound : start + chunkSpan k * b <= xs.length) :
    exists idx, chunkCell xs b k start = some idx /\
      RMQ.LeftmostArgMin xs start (start + chunkSpan k * b) idx := by
  induction k generalizing start with
  | zero =>
      have hif : 0 < b /\ start + b <= xs.length := by
        constructor
        · exact hb
        · simpa [chunkSpan] using hbound
      have hValid : RMQ.ValidRange xs start (start + b) := by
        constructor <;> omega
      rcases RMQ.LinearScan.query_valid_exact xs start (start + b) hValid with
        ⟨idx, hres, harg⟩
      refine ⟨idx, ?_, ?_⟩
      · simp [chunkCell, hif, rangeScan, hres]
      · simpa [chunkSpan] using harg
  | succ k ih =>
      let p := chunkSpan k
      have hsplit : chunkSpan (k + 1) = p + p := by
        simpa [p] using chunkSpan_succ k
      have hbound_split : start + (p + p) * b <= xs.length := by
        simpa [p, hsplit] using hbound
      have hleft_bound : start + p * b <= xs.length := by
        have hp_le : p * b <= (p + p) * b :=
          Nat.mul_le_mul_right b (by omega)
        exact Nat.le_trans (Nat.add_le_add_left hp_le start) hbound_split
      have hright_bound : start + p * b + p * b <= xs.length := by
        have hrewrite : start + p * b + p * b = start + (p + p) * b := by
          rw [Nat.add_mul]
          omega
        rw [hrewrite]
        exact hbound_split
      rcases ih start hleft_bound with ⟨li, hlcell, hlarg⟩
      rcases ih (start + p * b) hright_bound with ⟨ri, hrcell, hrarg⟩
      refine ⟨RMQ.betterIndex xs li ri, ?_, ?_⟩
      · simp [chunkCell, p, hlcell, hrcell, combineIndex, RMQ.SparseTable.combineIndex,
          RMQ.combineIndex]
      · have hright_end : start + p * b + p * b =
            start + chunkSpan (k + 1) * b := by
          rw [hsplit, Nat.add_mul]
          omega
        have hrarg' :
            RMQ.LeftmostArgMin xs (start + p * b)
              (start + chunkSpan (k + 1) * b) ri := by
          simpa [p, hright_end] using hrarg
        have hcover :
            forall t, start <= t -> t < start + chunkSpan (k + 1) * b ->
              t < start + chunkSpan k * b \/ start + p * b <= t := by
          intro t _ht_left _ht_right
          by_cases ht : t < start + p * b
          · exact Or.inl (by simpa [p] using ht)
          · exact Or.inr (by omega)
        have hA_sub :
            start + chunkSpan k * b <= start + chunkSpan (k + 1) * b := by
          have hp_le : p * b <= (p + p) * b :=
            Nat.mul_le_mul_right b (by omega)
          have hadd : start + p * b <= start + (p + p) * b :=
            Nat.add_le_add_left hp_le start
          simpa [p, hsplit] using hadd
        have hB_sub : start <= start + p * b := by omega
        exact RMQ.combineLeftmost hlarg hrarg' hA_sub hB_sub hcover

private theorem chunkRow_get?_eq_chunkCell
    (xs : List Int) (b k start : Nat) (h : start < xs.length) :
    (chunkRow xs b k)[start]? = some (chunkCell xs b k start) := by
  have hrow : start < (chunkRow xs b k).length := by
    simp [chunkRow, h]
  rw [List.getElem?_eq_getElem hrow]
  unfold chunkRow
  simp

theorem chunkRow_cell_eq_chunkCell
    (xs : List Int) (b k start : Nat) (h : start < xs.length) :
    rowCell (chunkRow xs b k) start = chunkCell xs b k start := by
  change RMQ.SparseTable.rowCell (chunkRow xs b k) start = chunkCell xs b k start
  unfold RMQ.SparseTable.rowCell
  simp [chunkRow_get?_eq_chunkCell xs b k start h]

theorem tableRow_build_eq_chunkRow
    (xs : List Int) (b k : Nat) (hk : k <= xs.length) :
    tableRow (buildChunkSparseTable xs b) k = chunkRow xs b k := by
  have htab : k < (buildChunkSparseTable xs b).length := by
    simp [buildChunkSparseTable]
    omega
  change RMQ.SparseTable.tableRow (buildChunkSparseTable xs b) k = chunkRow xs b k
  unfold RMQ.SparseTable.tableRow
  rw [List.getElem?_eq_getElem htab]
  unfold buildChunkSparseTable
  rw [List.getElem_ofFn]

private theorem log2_chunk_bounds {chunks : Nat} (hchunks : 0 < chunks) :
    chunkSpan (Nat.log2 chunks) <= chunks /\
      chunks <= chunkSpan (Nat.log2 chunks) + chunkSpan (Nat.log2 chunks) := by
  have hne : Not (chunks = 0) := Nat.ne_of_gt hchunks
  have hle : 2 ^ Nat.log2 chunks <= chunks := Nat.log2_self_le hne
  have _hlt : chunks < 2 ^ (Nat.log2 chunks + 1) := Nat.lt_log2_self
  constructor
  · simpa [chunkSpan] using hle
  · unfold chunkSpan
    have hpow : 2 ^ (Nat.log2 chunks + 1) =
        2 ^ Nat.log2 chunks + 2 ^ Nat.log2 chunks := by
      rw [Nat.pow_succ]
      omega
    omega

theorem sparseChunkIntervalCover
    {start chunks p b t : Nat}
    (hchunks_le_twop : chunks <= p + p) :
    t < start + p * b \/ start + (chunks - p) * b <= t := by
  by_cases hleft : t < start + p * b
  · exact Or.inl hleft
  · have hge : start + p * b <= t := by omega
    have hchunks_sub_le_p : chunks - p <= p := by omega
    have hsub_mul_le_pmul : (chunks - p) * b <= p * b :=
      Nat.mul_le_mul_right b hchunks_sub_le_p
    have hsub_start_le_p_start :
        start + (chunks - p) * b <= start + p * b :=
      Nat.add_le_add_left hsub_mul_le_pmul start
    exact Or.inr (Nat.le_trans hsub_start_le_p_start hge)

/-- Query a supplied chunk sparse table over a nonempty run of full chunks. -/
def sparseChunkQueryFromTable
    (xs : List Int) (b : Nat) (table : List (List (Option Nat)))
    (start chunks : Nat) : Option Nat :=
  if _h : 0 < b /\ 0 < chunks /\ start + chunks * b <= xs.length then
    let k := Nat.log2 chunks
    let p := chunkSpan k
    let row := tableRow table k
    combineIndex xs
      (rowCell row start)
      (rowCell row (start + (chunks - p) * b))
  else
    none

theorem sparseChunkQuery_valid_exact
    (xs : List Int) (b : Nat) (table : List (List (Option Nat)))
    (start chunks : Nat)
    (hb : 0 < b)
    (hchunks : 0 < chunks)
    (hbound : start + chunks * b <= xs.length)
    (htable_eq : table = buildChunkSparseTable xs b) :
    exists idx, sparseChunkQueryFromTable xs b table start chunks = some idx /\
      RMQ.LeftmostArgMin xs start (start + chunks * b) idx := by
  subst table
  let k := Nat.log2 chunks
  let p := chunkSpan k
  have hif : 0 < b /\ 0 < chunks /\ start + chunks * b <= xs.length := by
    exact ⟨hb, hchunks, hbound⟩
  have hp_bounds := log2_chunk_bounds hchunks
  have hp_le_chunks : p <= chunks := by
    simpa [p, k] using hp_bounds.1
  have hchunks_le_twop : chunks <= p + p := by
    simpa [p, k] using hp_bounds.2
  have hp_pos : 0 < p := by
    unfold p
    exact chunkSpan_pos k
  have hp_mul_pos : 0 < p * b := Nat.mul_pos hp_pos hb
  have hp_mul_le_chunks_mul : p * b <= chunks * b :=
    Nat.mul_le_mul_right b hp_le_chunks
  have hleft_bound : start + p * b <= xs.length :=
    Nat.le_trans (Nat.add_le_add_left hp_mul_le_chunks_mul start) hbound
  have hsub_add : chunks - p + p = chunks := Nat.sub_add_cancel hp_le_chunks
  have hright_eq :
      start + (chunks - p) * b + p * b = start + chunks * b := by
    rw [Nat.add_assoc, ← Nat.add_mul, hsub_add]
  have hright_bound : start + (chunks - p) * b + p * b <= xs.length := by
    rw [hright_eq]
    exact hbound
  have hright_bound' :
      start + (chunks - p) * b + chunkSpan k * b <= xs.length := by
    simpa [p] using hright_bound
  have hk_le_chunks : k <= chunks := by
    unfold k
    exact Nat.log2_le_self chunks
  have hchunks_le_chunks_mul : chunks <= chunks * b :=
    Nat.le_mul_of_pos_right chunks hb
  have hk_le_table : k <= xs.length := by
    have hk_le_mul : k <= chunks * b :=
      Nat.le_trans hk_le_chunks hchunks_le_chunks_mul
    have hmul_le_len : chunks * b <= xs.length := by omega
    exact Nat.le_trans hk_le_mul hmul_le_len
  have hstart_lt : start < xs.length := by omega
  have hright_start_lt : start + (chunks - p) * b < xs.length := by omega
  rcases chunkCell_leftmost_exists xs b k start hb hleft_bound with
    ⟨li, hlcell, hlarg⟩
  rcases chunkCell_leftmost_exists xs b k (start + (chunks - p) * b) hb
      hright_bound' with
    ⟨ri, hrcell, hrarg⟩
  refine ⟨RMQ.betterIndex xs li ri, ?_, ?_⟩
  · have htable := tableRow_build_eq_chunkRow xs b k hk_le_table
    have hlrow := chunkRow_cell_eq_chunkCell xs b k start hstart_lt
    have hrrow :=
      chunkRow_cell_eq_chunkCell xs b k (start + (chunks - p) * b) hright_start_lt
    unfold sparseChunkQueryFromTable
    simp [hif, k, p, htable, hlrow, hrrow, hlcell, hrcell, combineIndex,
      RMQ.SparseTable.combineIndex, RMQ.combineIndex]
  · have hright_end :
        start + (chunks - p) * b + chunkSpan k * b = start + chunks * b := by
      simpa [p] using hright_eq
    have hrarg' :
        RMQ.LeftmostArgMin xs (start + (chunks - p) * b)
          (start + chunks * b) ri := by
      simpa [hright_end] using hrarg
    have hcover :
        forall t, start <= t -> t < start + chunks * b ->
          t < start + chunkSpan k * b \/ start + (chunks - p) * b <= t := by
      intro t _ht_left _ht_right
      simpa [p] using
        (sparseChunkIntervalCover
          (start := start) (chunks := chunks) (p := p) (b := b) (t := t)
          hchunks_le_twop)
    have hA_sub : start + chunkSpan k * b <= start + chunks * b := by
      have hadd : start + p * b <= start + chunks * b :=
        Nat.add_le_add_left hp_mul_le_chunks_mul start
      simpa [p] using hadd
    have hB_sub : start <= start + (chunks - p) * b := by omega
    exact RMQ.combineLeftmost hlarg hrarg' hA_sub hB_sub hcover

/-- Concrete hybrid state for a fixed input list. -/
structure State where
  blockSize : Nat
  table : List (List (Option Nat))

/-- Build the public hybrid state for `xs`. -/
def build (xs : List Int) : State :=
  let b := publicBlockSize xs
  { blockSize := b, table := buildChunkSparseTable xs b }

/-- Query a supplied hybrid state with boundary scans and sparse middle chunks. -/
def queryWithState
    (xs : List Int) (state : State) (left right : Nat) : Option Nat :=
  let b := state.blockSize
  if _h : RMQ.ValidRange xs left right /\ 0 < b then
    let len := right - left
    if len <= b then
      rangeScan xs left right
    else
      let leftEnd := left + b
      let tailLen := right - leftEnd
      let middleChunks := tailLen / b
      let middleEnd := leftEnd + middleChunks * b
      let leftCandidate := rangeScan xs left leftEnd
      let middleCandidate :=
        sparseChunkQueryFromTable xs b state.table leftEnd middleChunks
      let rightCandidate := rangeScan xs middleEnd right
      combineIndex xs (combineIndex xs leftCandidate middleCandidate) rightCandidate
  else
    none

/-- Public hybrid-block query over a freshly built state. -/
def query (xs : List Int) (left right : Nat) : Option Nat :=
  queryWithState xs (build xs) left right

theorem publicBlockSize_pos (xs : List Int) :
    0 < publicBlockSize xs := by
  unfold publicBlockSize
  omega

theorem queryWithState_invalid_none
    {xs : List Int} {state : State} {left right : Nat}
    (hbad : Not (RMQ.ValidRange xs left right)) :
    queryWithState xs state left right = none := by
  unfold queryWithState
  by_cases hif : RMQ.ValidRange xs left right /\ 0 < state.blockSize
  · exact False.elim (hbad hif.1)
  · simp [hif]

theorem queryWithState_eq_linear_of_small
    {xs : List Int} {state : State} {left right : Nat}
    (hValid : RMQ.ValidRange xs left right)
    (hb : 0 < state.blockSize)
    (hsmall : right - left <= state.blockSize) :
    queryWithState xs state left right = RMQ.LinearScan.query xs left right := by
  unfold queryWithState rangeScan
  let b := state.blockSize
  have hif : RMQ.ValidRange xs left right /\ 0 < b := by
    exact ⟨hValid, by simpa [b] using hb⟩
  have hsmall' : right - left <= b := by
    simpa [b] using hsmall
  have hif' : RMQ.ValidRange xs left right /\ 0 < state.blockSize := by
    exact ⟨hValid, hb⟩
  have hsmallIf : right <= state.blockSize + left := by
    omega
  simp [hif', hsmallIf]

theorem query_valid_exact
    (xs : List Int) (left right : Nat) (hValid : RMQ.ValidRange xs left right) :
    exists idx, query xs left right = some idx /\
      RMQ.LeftmostArgMin xs left right idx := by
  by_cases hsmall : right - left <= publicBlockSize xs
  · have hbState : 0 < (build xs).blockSize := by
      simp [build, publicBlockSize_pos]
    have hquery_small :
        query xs left right = RMQ.LinearScan.query xs left right := by
      unfold query
      exact queryWithState_eq_linear_of_small
        (state := build xs) hValid hbState hsmall
    rcases RMQ.LinearScan.query_valid_exact xs left right hValid with
      ⟨idx, hres, harg⟩
    refine ⟨idx, ?_, harg⟩
    rw [hquery_small, hres]
  · let b := publicBlockSize xs
    let leftEnd := left + b
    let tailLen := right - leftEnd
    let middleChunks := tailLen / b
    let middleEnd := leftEnd + middleChunks * b
    have hb : 0 < b := by
      unfold b
      exact publicBlockSize_pos xs
    have hif : RMQ.ValidRange xs left right /\ 0 < b := ⟨hValid, hb⟩
    have hlargeIf : Not (right <= b + left) := by omega
    have hleftEnd_lt_right : leftEnd < right := by
      unfold leftEnd b at *
      omega
    have hleftValid : RMQ.ValidRange xs left leftEnd := by
      constructor
      · unfold leftEnd
        omega
      · unfold leftEnd b at *
        omega
    have hchunks_mul_le_tail : middleChunks * b <= tailLen := by
      unfold middleChunks
      exact Nat.div_mul_le_self tailLen b
    have hmiddleEnd_le_right : middleEnd <= right := by
      unfold middleEnd tailLen leftEnd at *
      omega
    have hmiddleEnd_le_len : middleEnd <= xs.length := by
      omega
    have hquery_large :
        query xs left right =
          combineIndex xs
            (combineIndex xs (rangeScan xs left leftEnd)
              (sparseChunkQueryFromTable xs b (buildChunkSparseTable xs b)
                leftEnd middleChunks))
            (rangeScan xs middleEnd right) := by
      unfold query queryWithState build
      simp [b, leftEnd, tailLen, middleChunks, middleEnd, hif, hlargeIf]
    rcases RMQ.LinearScan.query_valid_exact xs left leftEnd hleftValid with
      ⟨li, hlres, hlarg⟩
    have hmiddleCase :
        RMQ.CandidateExact xs leftEnd middleEnd
          (sparseChunkQueryFromTable xs b (buildChunkSparseTable xs b)
            leftEnd middleChunks) := by
      by_cases hmiddle_zero : middleChunks = 0
      · have hmiddleEnd_eq_leftEnd : middleEnd = leftEnd := by
          unfold middleEnd
          simp [hmiddle_zero]
        have hmiddle_none :
            sparseChunkQueryFromTable xs b (buildChunkSparseTable xs b)
              leftEnd middleChunks = none := by
          unfold sparseChunkQueryFromTable
          simp [hmiddle_zero]
        exact Or.inl ⟨hmiddle_none, hmiddleEnd_eq_leftEnd.symm⟩
      · have hmiddle_pos : 0 < middleChunks := Nat.pos_of_ne_zero hmiddle_zero
        have hmiddle_bound : leftEnd + middleChunks * b <= xs.length := by
          unfold middleEnd at hmiddleEnd_le_len
          exact hmiddleEnd_le_len
        rcases sparseChunkQuery_valid_exact xs b (buildChunkSparseTable xs b)
            leftEnd middleChunks hb hmiddle_pos hmiddle_bound rfl with
          ⟨mi, hmres, hmarg⟩
        refine Or.inr ⟨mi, hmres, ?_⟩
        simpa [middleEnd] using hmarg
    have hrightCase :
        RMQ.CandidateExact xs middleEnd right (rangeScan xs middleEnd right) := by
      by_cases hright_nonempty : middleEnd < right
      · have hrightValid : RMQ.ValidRange xs middleEnd right := by
          exact ⟨hright_nonempty, hValid.2⟩
        rcases RMQ.LinearScan.query_valid_exact xs middleEnd right hrightValid with
          ⟨ri, hrres, hrarg⟩
        refine Or.inr ⟨ri, ?_, hrarg⟩
        simpa [rangeScan] using hrres
      · have hmiddleEnd_eq_right : middleEnd = right := by omega
        have hright_none : rangeScan xs middleEnd right = none := by
          unfold rangeScan
          exact RMQ.LinearScan.invalid_none (by
            intro hbad
            omega)
        exact Or.inl ⟨hright_none, hmiddleEnd_eq_right⟩
    have hleftEnd_le_middleEnd : leftEnd <= middleEnd := by
      unfold middleEnd
      omega
    rcases RMQ.combineHybridLeftmost
        (xs := xs) (left := left) (leftEnd := leftEnd)
        (middleEnd := middleEnd) (right := right) (li := li)
        (middleCandidate :=
          sparseChunkQueryFromTable xs b (buildChunkSparseTable xs b)
            leftEnd middleChunks)
        (rightCandidate := rangeScan xs middleEnd right)
        hlarg hmiddleCase hrightCase hleftEnd_le_middleEnd hmiddleEnd_le_right with
      ⟨idx, hcombined, harg⟩
    refine ⟨idx, ?_, harg⟩
    rw [hquery_large]
    simpa [rangeScan, hlres, combineIndex, RMQ.SparseTable.combineIndex,
      RMQ.combineIndex] using hcombined

theorem query_sound {xs : List Int} {left right idx : Nat}
    (hres : query xs left right = some idx) :
    RMQ.LeftmostArgMin xs left right idx := by
  by_cases hValid : RMQ.ValidRange xs left right
  · rcases query_valid_exact xs left right hValid with ⟨idx', hres', harg'⟩
    have hidx : idx = idx' := by
      have hsome : some idx = some idx' := by
        rw [<- hres, hres']
      exact Option.some.inj hsome
    simpa [hidx] using harg'
  · unfold query at hres
    have hnone := queryWithState_invalid_none (state := build xs) hValid
    rw [hnone] at hres
    contradiction

theorem query_complete {xs : List Int} {left right idx : Nat}
    (harg : RMQ.LeftmostArgMin xs left right idx) :
    query xs left right = some idx := by
  have hValid : RMQ.ValidRange xs left right := RMQ.LeftmostArgMin.valid harg
  rcases query_valid_exact xs left right hValid with ⟨idx', hres', harg'⟩
  have hidx : idx' = idx :=
    RMQ.leftmostArgMin_unique xs left right idx' idx harg' harg
  simpa [hidx] using hres'

theorem invalid_none {xs : List Int} {left right : Nat}
    (hbad : Not (RMQ.ValidRange xs left right)) :
    query xs left right = none := by
  unfold query
  exact queryWithState_invalid_none hbad

/-- Hybrid block RMQ as an explicit `RMQBackend`. -/
def backend (xs : List Int) : RMQ.RMQBackend xs where
  State := State
  build := build xs
  query := fun state => queryWithState xs state
  sound := by
    intro left right idx hres
    have hquery : query xs left right = some idx := hres
    exact query_sound hquery
  complete := by
    intro left right idx harg
    exact query_complete harg
  invalid_none := by
    intro left right hbad
    exact invalid_none hbad

end RMQ.HybridBlock
