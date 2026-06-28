import RMQ.Core.SuccinctSpace.Asymptotics

/-!
# Payload-word codecs and stores

Bit-level fixed-width codecs, payload-word chunking, and the stored-word
representation boundary shared by the succinct rank/select and BP navigation
layers.
-/

namespace RMQ

namespace SuccinctSpace

/-- Interpret one Boolean bit as a binary digit. -/
def bitToNat (bit : Bool) : Nat :=
  if bit then 1 else 0

/--
Little-endian interpretation of one machine word as a natural number.

This is a word-level decoder.  Structures using it still have to prove that the
queried word is fetched from the counted payload, rather than from an
unaccounted proof-side table.
-/
def bitsToNatLE : List Bool -> Nat
  | [] => 0
  | bit :: rest => bitToNat bit + 2 * bitsToNatLE rest

/-- Fixed-width little-endian encoding of a natural number. -/
def natToBitsLE : Nat -> Nat -> List Bool
  | 0, _ => []
  | width + 1, n =>
      decide (n % 2 = 1) :: natToBitsLE width (n / 2)

theorem natToBitsLE_length (width n : Nat) :
    (natToBitsLE width n).length = width := by
  induction width generalizing n with
  | zero =>
      simp [natToBitsLE]
  | succ width ih =>
      simp [natToBitsLE, ih]

theorem bitToNat_decide_mod_two (n : Nat) :
    bitToNat (decide (n % 2 = 1)) = n % 2 := by
  unfold bitToNat
  by_cases h : n % 2 = 1
  · simp [h]
  · have hlt : n % 2 < 2 := Nat.mod_lt n (by omega)
    have hzero : n % 2 = 0 := by omega
    simp [hzero]

theorem bitsToNatLE_natToBitsLE_of_lt
    {width n : Nat} (hbound : n < 2 ^ width) :
    bitsToNatLE (natToBitsLE width n) = n := by
  induction width generalizing n with
  | zero =>
      have hn : n = 0 := by
        simpa using hbound
      simp [natToBitsLE, bitsToNatLE, hn]
  | succ width ih =>
      have hhalf : n / 2 < 2 ^ width := by
        have hpow :
            2 ^ (width + 1) = 2 ^ width * 2 := by
          rw [Nat.pow_succ]
        have hlt : n < 2 ^ width * 2 := by
          simpa [hpow] using hbound
        exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2 hlt
      have hrec := ih hhalf
      have hdecomp : n % 2 + 2 * (n / 2) = n := by
        simpa [Nat.mul_comm] using (Nat.mod_add_div n 2)
      simp [natToBitsLE, bitsToNatLE, bitToNat_decide_mod_two,
        hrec, hdecomp]

/-- Flatten a list of payload words into the payload bitstream they store. -/
def flattenPayloadWords : List (List Bool) -> List Bool
  | [] => []
  | word :: rest => word ++ flattenPayloadWords rest

theorem flattenPayloadWords_append
    (xs ys : List (List Bool)) :
    flattenPayloadWords (xs ++ ys) =
      flattenPayloadWords xs ++ flattenPayloadWords ys := by
  induction xs with
  | nil =>
      simp [flattenPayloadWords]
  | cons word rest ih =>
      simp [flattenPayloadWords, ih, List.append_assoc]

theorem flattenPayloadWords_replicate_nil (n : Nat) :
    flattenPayloadWords (List.replicate n []) = [] := by
  induction n with
  | zero =>
      simp [flattenPayloadWords]
  | succ n ih =>
      simp [List.replicate, flattenPayloadWords, ih]

theorem flattenPayloadWords_length_of_forall_length
    {words : List (List Bool)} {width : Nat}
    (hwidth :
      forall {word : List Bool}, List.Mem word words -> word.length = width) :
    (flattenPayloadWords words).length = words.length * width := by
  induction words with
  | nil =>
      simp [flattenPayloadWords]
  | cons word rest ih =>
      have hword : word.length = width :=
        hwidth List.mem_cons_self
      have hrest :
          forall {tailWord : List Bool},
            List.Mem tailWord rest -> tailWord.length = width := by
        intro tailWord hmem
        exact hwidth (List.mem_cons_of_mem word hmem)
      simp [flattenPayloadWords, hword, ih hrest, Nat.succ_mul,
        Nat.add_comm]

/--
Fuelled fixed-size payload chunker.

The `fuel` argument keeps the definition structurally recursive.  The public
constructor below supplies enough fuel and proves that, for positive word size,
flattening the chunks recovers the original payload.
-/
def chunkPayloadWordsFuel
    (wordSize fuel : Nat) (payload : List Bool) : List (List Bool) :=
  match fuel, payload with
  | 0, _ => []
  | _ + 1, [] => []
  | fuel' + 1, bits =>
      bits.take wordSize ::
        chunkPayloadWordsFuel wordSize fuel' (bits.drop wordSize)

/-- Split payload bits into fixed-size words.  The final word may be shorter. -/
def chunkPayloadWords (wordSize : Nat) (payload : List Bool) :
    List (List Bool) :=
  chunkPayloadWordsFuel wordSize (payload.length + 1) payload

theorem flattenPayloadWords_chunkPayloadWordsFuel
    {wordSize fuel : Nat} (hword : 0 < wordSize) :
    forall payload : List Bool,
      payload.length <= fuel ->
        flattenPayloadWords
          (chunkPayloadWordsFuel wordSize fuel payload) =
          payload := by
  induction fuel with
  | zero =>
      intro payload hlen
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel, flattenPayloadWords]
      | cons bit rest =>
          simp at hlen
  | succ fuel ih =>
      intro payload hlen
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel, flattenPayloadWords]
      | cons bit rest =>
          have hdrop :
              ((bit :: rest).drop wordSize).length <= fuel := by
            rw [List.length_drop]
            omega
          have hrec := ih ((bit :: rest).drop wordSize) hdrop
          calc
            flattenPayloadWords
                (chunkPayloadWordsFuel wordSize (fuel + 1)
                  (bit :: rest)) =
              (bit :: rest).take wordSize ++
                flattenPayloadWords
                  (chunkPayloadWordsFuel wordSize fuel
                    ((bit :: rest).drop wordSize)) := by
                simp [chunkPayloadWordsFuel, flattenPayloadWords]
            _ = (bit :: rest).take wordSize ++
                (bit :: rest).drop wordSize := by
                  rw [hrec]
            _ = bit :: rest := by
                  exact List.take_append_drop wordSize (bit :: rest)

theorem flattenPayloadWords_chunkPayloadWords
    {wordSize : Nat} (hword : 0 < wordSize) (payload : List Bool) :
    flattenPayloadWords (chunkPayloadWords wordSize payload) = payload := by
  unfold chunkPayloadWords
  exact flattenPayloadWords_chunkPayloadWordsFuel hword payload (by omega)

theorem chunkPayloadWordsFuel_word_length_le
    (wordSize fuel : Nat) :
    forall {payload word : List Bool},
      List.Mem word (chunkPayloadWordsFuel wordSize fuel payload) ->
        word.length <= wordSize := by
  induction fuel with
  | zero =>
      intro payload word hmem
      simp [chunkPayloadWordsFuel] at hmem
      cases hmem
  | succ fuel ih =>
      intro payload word hmem
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel] at hmem
          cases hmem
      | cons bit rest =>
          change
            List.Mem word
              ((bit :: rest).take wordSize ::
                chunkPayloadWordsFuel wordSize fuel
                  ((bit :: rest).drop wordSize)) at hmem
          cases hmem with
          | head =>
            rw [List.length_take]
            exact Nat.min_le_left wordSize (bit :: rest).length
          | tail _ htail =>
              exact ih htail

theorem chunkPayloadWords_word_length_le
    (wordSize : Nat) {payload word : List Bool}
    (hmem : List.Mem word (chunkPayloadWords wordSize payload)) :
    word.length <= wordSize := by
  unfold chunkPayloadWords at hmem
  exact chunkPayloadWordsFuel_word_length_le
    wordSize (payload.length + 1) hmem

theorem chunkPayloadWordsFuel_get?_eq_take_drop
    {wordSize fuel : Nat} :
    forall {payload word : List Bool} {i : Nat},
      (chunkPayloadWordsFuel wordSize fuel payload)[i]? = some word ->
        word = (payload.drop (i * wordSize)).take wordSize := by
  induction fuel with
  | zero =>
      intro payload word i hget
      simp [chunkPayloadWordsFuel] at hget
  | succ fuel ih =>
      intro payload word i hget
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel] at hget
      | cons bit rest =>
          cases i with
          | zero =>
              simp [chunkPayloadWordsFuel] at hget
              simpa using hget.symm
          | succ i =>
              have htail :
                  (chunkPayloadWordsFuel wordSize fuel
                    ((bit :: rest).drop wordSize))[i]? = some word := by
                simpa [chunkPayloadWordsFuel] using hget
              have hrec := ih htail
              calc
                word = (((bit :: rest).drop wordSize).drop
                    (i * wordSize)).take wordSize := hrec
                _ = ((bit :: rest).drop ((i + 1) * wordSize)).take
                    wordSize := by
                  simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]

theorem chunkPayloadWords_get?_eq_take_drop
    {wordSize : Nat} {payload word : List Bool} {i : Nat}
    (hget : (chunkPayloadWords wordSize payload)[i]? = some word) :
    word = (payload.drop (i * wordSize)).take wordSize := by
  unfold chunkPayloadWords at hget
  exact chunkPayloadWordsFuel_get?_eq_take_drop hget

theorem chunkPayloadWordsFuel_get?_some_of_mul_lt
    {wordSize fuel : Nat} (hword : 0 < wordSize) :
    forall {payload : List Bool} {i : Nat},
      payload.length <= fuel ->
      i * wordSize < payload.length ->
        exists word,
          (chunkPayloadWordsFuel wordSize fuel payload)[i]? =
            some word := by
  induction fuel with
  | zero =>
      intro payload i hlen hi
      cases payload with
      | nil =>
          simp at hi
      | cons bit rest =>
          simp at hlen
  | succ fuel ih =>
      intro payload i hlen hi
      cases payload with
      | nil =>
          simp at hi
      | cons bit rest =>
          cases i with
          | zero =>
              refine ⟨(bit :: rest).take wordSize, ?_⟩
              simp [chunkPayloadWordsFuel]
          | succ i =>
              have hdropLen :
                  ((bit :: rest).drop wordSize).length <= fuel := by
                rw [List.length_drop]
                omega
              have hiTail :
                  i * wordSize < ((bit :: rest).drop wordSize).length := by
                rw [List.length_drop]
                have hmul :
                    (i + 1) * wordSize = i * wordSize + wordSize := by
                  simp [Nat.succ_mul]
                omega
              rcases ih hdropLen hiTail with ⟨word, hget⟩
              exact ⟨word, by simpa [chunkPayloadWordsFuel] using hget⟩

theorem chunkPayloadWords_get?_some_of_mul_lt
    {wordSize : Nat} (hword : 0 < wordSize)
    {payload : List Bool} {i : Nat}
    (hi : i * wordSize < payload.length) :
    exists word,
      (chunkPayloadWords wordSize payload)[i]? = some word := by
  unfold chunkPayloadWords
  exact chunkPayloadWordsFuel_get?_some_of_mul_lt hword (by omega) hi

theorem chunkPayloadWordsFuel_get?_none_of_length_le_mul
    {wordSize fuel : Nat} :
    forall {payload : List Bool} {i : Nat},
      payload.length <= i * wordSize ->
        (chunkPayloadWordsFuel wordSize fuel payload)[i]? = none := by
  induction fuel with
  | zero =>
      intro payload i hlen
      simp [chunkPayloadWordsFuel]
  | succ fuel ih =>
      intro payload i hlen
      cases payload with
      | nil =>
          simp [chunkPayloadWordsFuel]
      | cons bit rest =>
          cases i with
          | zero =>
              simp at hlen
          | succ i =>
              have hdropLen :
                  ((bit :: rest).drop wordSize).length <=
                    i * wordSize := by
                rw [List.length_drop]
                have hmul :
                    (i + 1) * wordSize = i * wordSize + wordSize := by
                  simp [Nat.succ_mul]
                omega
              have htail := ih hdropLen
              simpa [chunkPayloadWordsFuel] using htail

theorem chunkPayloadWords_get?_none_of_length_le_mul
    {wordSize : Nat}
    {payload : List Bool} {i : Nat}
    (hi : payload.length <= i * wordSize) :
    (chunkPayloadWords wordSize payload)[i]? = none := by
  unfold chunkPayloadWords
  exact chunkPayloadWordsFuel_get?_none_of_length_le_mul hi

theorem chunkPayloadWords_length_le_div_add_one
    {wordSize : Nat} (hword : 0 < wordSize)
    (payload : List Bool) :
    (chunkPayloadWords wordSize payload).length <=
      payload.length / wordSize + 1 := by
  have hcovered :
      payload.length <=
        (payload.length / wordSize + 1) * wordSize := by
    have hlt : payload.length <
        payload.length / wordSize * wordSize + wordSize :=
      Nat.lt_div_mul_add hword (a := payload.length)
    simpa [Nat.add_mul, Nat.one_mul] using Nat.le_of_lt hlt
  have hnone :
      (chunkPayloadWords wordSize payload)[
          payload.length / wordSize + 1]? = none :=
    chunkPayloadWords_get?_none_of_length_le_mul hcovered
  rw [List.getElem?_eq_none_iff] at hnone
  exact hnone

/--
A stored word array whose flattened word contents are exactly the counted
payload bits.

This is the first payload-live representation boundary for the succinct layer:
query procedures may read `words`, but the represented bits are tied directly to
the payload whose length is charged in space theorems.
-/
structure PayloadWordStore (payload : List Bool) where
  words : Array (List Bool)
  erases : flattenPayloadWords words.toList = payload

namespace PayloadWordStore

def readWordCosted
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    Costed (Option (List Bool)) :=
  (RAM.readArray? store.words i).toCosted

@[simp] theorem readWordCosted_erase
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    (store.readWordCosted i).erase = store.words[i]? := by
  rfl

@[simp] theorem readWordCosted_cost
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    (store.readWordCosted i).cost = 1 := by
  rfl

theorem readWordCosted_cost_le_one
    {payload : List Bool}
    (store : PayloadWordStore payload) (i : Nat) :
    (store.readWordCosted i).cost <= 1 := by
  simp

theorem payload_eq_words_join
    {payload : List Bool}
    (store : PayloadWordStore payload) :
    flattenPayloadWords store.words.toList = payload :=
  store.erases

/--
Read the full payload word array, charging one modeled read per stored word.

This is a reference readback primitive for proofs that must demonstrate payload
dependence without pretending the whole payload is one machine word.
-/
def readAllWordsCosted
    {payload : List Bool}
    (store : PayloadWordStore payload) : Costed (List (List Bool)) :=
  Costed.tickValue store.words.size store.words.toList

@[simp] theorem readAllWordsCosted_cost
    {payload : List Bool}
    (store : PayloadWordStore payload) :
    store.readAllWordsCosted.cost = store.words.size := by
  simp [readAllWordsCosted]

@[simp] theorem readAllWordsCosted_erase
    {payload : List Bool}
    (store : PayloadWordStore payload) :
    store.readAllWordsCosted.erase = store.words.toList := by
  simp [readAllWordsCosted]

theorem readAllWordsCosted_flatten_erase
    {payload : List Bool}
    (store : PayloadWordStore payload) :
    flattenPayloadWords store.readAllWordsCosted.erase = payload := by
  simpa using store.erases

end PayloadWordStore

/--
Payload store with an explicit upper bound on each stored word.

This is the representation discipline needed for broadword claims: clients can
still use `PayloadWordStore` directly for reference scaffolding, while final
succinct profiles can require this bounded wrapper to rule out one giant
payload word pretending to be a machine word.
-/
structure BoundedPayloadWordStore
    (payload : List Bool) (wordSize : Nat) where
  store : PayloadWordStore payload
  word_length_le :
    forall {word : List Bool},
      List.Mem word store.words.toList -> word.length <= wordSize

namespace BoundedPayloadWordStore

def ofChunks
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    BoundedPayloadWordStore payload wordSize where
  store :=
    { words := (chunkPayloadWords wordSize payload).toArray
      erases := by
        simpa using flattenPayloadWords_chunkPayloadWords hword payload }
  word_length_le := by
    intro word hmem
    simpa using chunkPayloadWords_word_length_le wordSize hmem

/--
Chunked payload store with empty sentinel padding.

The sentinel preserves the represented payload but gives boundary-sensitive
word-RAM clients, such as rank at an exact word boundary, concrete empty
words to read after the real chunks.
-/
def ofChunksWithSentinel
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    BoundedPayloadWordStore payload wordSize where
  store :=
    { words :=
        (chunkPayloadWords wordSize payload ++
          List.replicate (payload.length + 1) []).toArray
      erases := by
        rw [flattenPayloadWords_append,
          flattenPayloadWords_chunkPayloadWords hword payload,
          flattenPayloadWords_replicate_nil]
        simp }
  word_length_le := by
    intro word hmem
    have hlist :
        List.Mem word
          (chunkPayloadWords wordSize payload ++
            List.replicate (payload.length + 1) []) := by
      simpa using hmem
    rcases List.mem_append.mp hlist with hchunk | hsentinel
    ·
        exact chunkPayloadWords_word_length_le wordSize hchunk
    ·
        simp at hsentinel
        subst word
        simp

theorem erases
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize) :
    flattenPayloadWords store.store.words.toList = payload :=
  store.store.erases

theorem word_length_le_of_mem
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize)
    {word : List Bool}
    (hmem : List.Mem word store.store.words.toList) :
    word.length <= wordSize :=
  store.word_length_le hmem

theorem ofChunks_erases
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    flattenPayloadWords
      ((BoundedPayloadWordStore.ofChunks payload hword).store.words.toList) =
      payload := by
  exact (BoundedPayloadWordStore.ofChunks payload hword).erases

theorem ofChunks_word_length_le
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize)
    {word : List Bool}
    (hmem : List.Mem word
      (BoundedPayloadWordStore.ofChunks payload hword).store.words.toList) :
    word.length <= wordSize :=
  (BoundedPayloadWordStore.ofChunks payload hword).word_length_le hmem

theorem ofChunksWithSentinel_erases
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    flattenPayloadWords
      ((BoundedPayloadWordStore.ofChunksWithSentinel
        payload hword).store.words.toList) =
      payload := by
  exact (BoundedPayloadWordStore.ofChunksWithSentinel payload hword).erases

theorem ofChunksWithSentinel_word_length_le
    (payload : List Bool) {wordSize : Nat} (hword : 0 < wordSize)
    {word : List Bool}
    (hmem : List.Mem word
      (BoundedPayloadWordStore.ofChunksWithSentinel
        payload hword).store.words.toList) :
    word.length <= wordSize :=
  (BoundedPayloadWordStore.ofChunksWithSentinel
    payload hword).word_length_le hmem

end BoundedPayloadWordStore

end SuccinctSpace

end RMQ
