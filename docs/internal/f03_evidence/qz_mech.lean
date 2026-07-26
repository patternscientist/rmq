import RMQ.Core.SuccinctFinalStoreParam

/-!
QZ-F03 MECHANISM THEOREMS.

Claim under attack: the prior verdict says the content-reading branch cone
(bpExcessAt, bpBetterArgMinBlock, the local/global sparse offset tables) is
"probably B, but I have not proved it".

These theorems prove the general mechanism, universally quantified over ALL
tables, ALL entry lists, ALL widths, ALL word sizes, ALL bases, ALL dead
addresses and ALL indices -- no size regime, no representative rows.
-/

open RMQ
open RMQ.SuccinctSpace

namespace QZMech

/-! ### T1. The flat-store table adapter provably ignores table CONTENTS. -/

/--
Two fixed-width tables with the SAME number of entries and the SAME width
induce the *identical* flat-store read computation, whatever their contents.

Consequence: every `entries` list appearing under
`FixedWidthNatTable.machineReadComputationAt` -- which is how
`canonicalRelativeRmmMachineReadNatComputation` reads every interior directory
table -- can influence neither the issued addresses nor the returned value.
Only `entries.length`, `width`, `wordSize`, `base`, `deadAddress`, `i` can.
-/
theorem machineReadComputationAt_content_irrelevant
    {e1 e2 : List Nat} {width : Nat}
    (t1 : FixedWidthNatTable e1 width)
    (t2 : FixedWidthNatTable e2 width)
    (hlen : e1.length = e2.length)
    (wordSize base deadAddress i : Nat) :
    t1.machineReadComputationAt wordSize base deadAddress i =
      t2.machineReadComputationAt wordSize base deadAddress i := by
  unfold FixedWidthNatTable.machineReadComputationAt
  rw [hlen]

/-- Same statement, specialised to the RMQ wrapper actually used by the route. -/
theorem canonicalReadNat_content_irrelevant
    {e1 e2 : List Nat} {width : Nat}
    (shape : Cartesian.CartesianShape)
    (t1 : FixedWidthNatTable e1 width)
    (t2 : FixedWidthNatTable e2 width)
    (hlen : e1.length = e2.length)
    (base i : Nat) :
    SuccinctClose.canonicalRelativeRmmMachineReadNatComputation shape t1 base i =
      SuccinctClose.canonicalRelativeRmmMachineReadNatComputation shape t2 base i := by
  unfold SuccinctClose.canonicalRelativeRmmMachineReadNatComputation
  exact machineReadComputationAt_content_irrelevant t1 t2 hlen _ _ _ _

/-! ### T2. The physical word count of a table is content-independent. -/

theorem chunkFuel_length_congr (wordSize : Nat) :
    forall (fuel : Nat) (p q : List Bool), p.length = q.length ->
      (chunkPayloadWordsFuel wordSize fuel p).length =
        (chunkPayloadWordsFuel wordSize fuel q).length := by
  intro fuel
  induction fuel with
  | zero => intro p q _; simp [chunkPayloadWordsFuel]
  | succ fuel ih =>
      intro p q hpq
      cases p with
      | nil =>
          cases q with
          | nil => simp [chunkPayloadWordsFuel]
          | cons b r => simp at hpq
      | cons b r =>
          cases q with
          | nil => simp at hpq
          | cons c s =>
              have hrs : r.length = s.length := by simpa using hpq
              have hdrop :
                  ((b :: r).drop wordSize).length =
                    ((c :: s).drop wordSize).length := by
                simp [List.length_drop, hpq]
              simp only [chunkPayloadWordsFuel, List.length_cons]
              rw [ih _ _ hdrop]

theorem chunkPayloadWords_length_congr
    (wordSize : Nat) (p q : List Bool) (h : p.length = q.length) :
    (chunkPayloadWords wordSize p).length =
      (chunkPayloadWords wordSize q).length := by
  unfold chunkPayloadWords
  rw [h]
  exact chunkFuel_length_congr wordSize (q.length + 1) p q h

/-- Flattening `k` words that all have the same length gives a
content-independent physical word count. -/
theorem flatMap_chunk_length_of_uniform
    (wordSize width : Nat) :
    forall ws : List (List Bool),
      (forall w, List.Mem w ws -> w.length = width) ->
        (ws.flatMap (chunkPayloadWords wordSize)).length =
          ws.length *
            (chunkPayloadWords wordSize (List.replicate width false)).length := by
  intro ws
  induction ws with
  | nil => intro _; simp
  | cons head tail ih =>
      intro huniform
      have hhead : head.length = width := huniform head (List.Mem.head _)
      have htail : forall w, List.Mem w tail -> w.length = width := by
        intro w hw; exact huniform w (List.Mem.tail _ hw)
      have hrep : (List.replicate width false).length = width := by simp
      have hheadlen :
          (chunkPayloadWords wordSize head).length =
            (chunkPayloadWords wordSize (List.replicate width false)).length :=
        chunkPayloadWords_length_congr wordSize head _ (by rw [hhead, hrep])
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [ih htail, hheadlen, Nat.succ_mul]
      omega

/-- A fixed-width table's logical word array has exactly `entries.length` words. -/
theorem store_words_size_eq_entries_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.store.words.size = entries.length := by
  have key :
      forall i : Nat,
        ((table.store.words.toList)[i]?).isSome = (entries[i]?).isSome := by
    intro i
    have h : ((table.store.words.toList)[i]?).map bitsToNatLE = entries[i]? := by
      simpa using table.read_exact i
    rw [← h]
    cases (table.store.words.toList)[i]? <;> simp
  have hlen : table.store.words.toList.length = table.store.words.size :=
    Array.length_toList
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : ((table.store.words.toList)[entries.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [key] at h2
    rw [List.getElem?_eq_none (Nat.le_refl _)] at h2
    exact Bool.noConfusion h2
  · apply Nat.le_of_not_lt
    intro hlt
    have h2 : (entries[table.store.words.toList.length]?).isSome = true := by
      rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [← key] at h2
    rw [List.getElem?_eq_none (Nat.le_refl _)] at h2
    exact Bool.noConfusion h2

/-- Every logical word of a fixed-width table has length exactly `width`. -/
theorem store_word_mem_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    {bits : List Bool} (hmem : List.Mem bits table.store.words.toList) :
    bits.length = width := by
  rcases List.getElem?_of_mem hmem with ⟨i, hi⟩
  exact table.word_length_of_get? (by simpa using hi)

/--
**The physical footprint of a fixed-width table depends only on its entry
COUNT and width -- never on the entry values.**

This is what makes the interior directory offsets
(`canonicalRelativeRmmInteriorComponentOffsets`, whose every field is a running
sum of `.machineStore.store.words.size`) content-independent, and hence what
makes `bpExcessAt`/`bpBlockArgMinLocalOffset`/`bpLocalSparseCellOffset`
build-only (verdict B) rather than a free semantic input (verdict X).
-/
theorem machineStore_words_size_content_irrelevant
    {e1 e2 : List Nat} {width wordSize : Nat}
    (t1 : FixedWidthNatTable e1 width)
    (t2 : FixedWidthNatTable e2 width)
    (hlen : e1.length = e2.length)
    (h1 : 0 < wordSize) (h2 : 0 < wordSize) :
    (t1.machineStore (wordSize := wordSize) h1).store.words.size =
      (t2.machineStore (wordSize := wordSize) h2).store.words.size := by
  have hexp :
      forall {e : List Nat} (t : FixedWidthNatTable e width) (h : 0 < wordSize),
        (t.machineStore (wordSize := wordSize) h).store.words.size =
          e.length *
            (chunkPayloadWords wordSize (List.replicate width false)).length := by
    intro e t h
    show (fixedWidthNatTableMachineWords t wordSize).toArray.size = _
    rw [Array.size_toArray]
    unfold fixedWidthNatTableMachineWords
    rw [flatMap_chunk_length_of_uniform wordSize width t.store.words.toList
      (fun w hw => store_word_mem_length t hw)]
    rw [Array.length_toList, store_words_size_eq_entries_length t]
  rw [hexp t1 h1, hexp t2 h2, hlen]

end QZMech

#print axioms QZMech.machineReadComputationAt_content_irrelevant
#print axioms QZMech.canonicalReadNat_content_irrelevant
#print axioms QZMech.machineStore_words_size_content_irrelevant
#print axioms QZMech.store_words_size_eq_entries_length
