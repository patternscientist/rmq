import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeChunks

/-!
# Charged fringe chunk-table space accounting (o(n) composition)

Bit budget of the charged fringe chunk table, its `LittleOLinear` proof, the
per-source linear word-count bound feeding the reviewer capacity budget, the
word-width bound against the declared reviewer machine word, and the
committed candidate `buildPayload`/`overhead` amendment.

The public `SuccinctClassic.buildPayload` swap itself is coupled to the
wiring rung: the accepted public capstone
(`FlatPayloadStoreNoSyntheticExecutionStory`) proves
`reviewerPayload = buildPayload` by `rfl`, so amending the public definition
before the executed route reads the table would falsify a checked public
theorem while the tables are still unread.  The candidate pair below pins
the amendment shape exactly; the wiring rung performs the swap together
with the reviewer-source extension.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

theorem bpFringeChunkEntryBound_pos (c : Nat) :
    0 < bpFringeChunkEntryBound c := by
  unfold bpFringeChunkEntryBound
  exact Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))

/-- The packed entry width is at most `3c + 6` bits. -/
theorem bpFringeChunkEntryWidth_le (c : Nat) :
    bpFringeChunkEntryWidth c <= 3 * c + 6 := by
  have h1 : c + 1 <= 2 ^ (c + 1) := SuccinctSpace.nat_le_two_pow (c + 1)
  have h2 : 2 * c + 2 <= 2 ^ (c + 2) := by
    have hdouble : 2 ^ (c + 2) = 2 * 2 ^ (c + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have h3 : 2 * c + 1 <= 2 ^ (c + 2) := by omega
  have hbound : bpFringeChunkEntryBound c <= 2 ^ (3 * c + 5) := by
    unfold bpFringeChunkEntryBound
    calc
      (2 * c + 1) * ((2 * c + 2) * (c + 1)) <=
          2 ^ (c + 2) * (2 ^ (c + 2) * 2 ^ (c + 1)) :=
        Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h1)
      _ = 2 ^ (3 * c + 5) := by
        rw [<- Nat.pow_add, <- Nat.pow_add]
        congr 1
        omega
  have hlog : Nat.log2 (bpFringeChunkEntryBound c) <= 3 * c + 5 := by
    rcases Nat.lt_or_ge (3 * c + 5)
      (Nat.log2 (bpFringeChunkEntryBound c)) with hlt | hge'
    case inr => exact hge'
    exfalso
    have hge : 3 * c + 6 <= Nat.log2 (bpFringeChunkEntryBound c) := by
      omega
    have hpow :
        2 ^ (3 * c + 6) <=
          2 ^ Nat.log2 (bpFringeChunkEntryBound c) :=
      Nat.pow_le_pow_right (by omega) hge
    have hself :
        2 ^ Nat.log2 (bpFringeChunkEntryBound c) <=
          bpFringeChunkEntryBound c :=
      Nat.log2_self_le (by
        have := bpFringeChunkEntryBound_pos c
        omega)
    have hsucc : 2 ^ (3 * c + 6) = 2 * 2 ^ (3 * c + 5) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hposPow : 0 < 2 ^ (3 * c + 5) := Nat.pow_pos (by omega)
    omega
  unfold bpFringeChunkEntryWidth
  omega

/-- Row-count bound: `2^c (c+1)^2 <= 2^(3c+2)`. -/
theorem bpFringeChunkRowCount_le_two_pow (c : Nat) :
    bpFringeChunkRowCount c <= 2 ^ (3 * c + 2) := by
  have h1 : c + 1 <= 2 ^ (c + 1) := SuccinctSpace.nat_le_two_pow (c + 1)
  unfold bpFringeChunkRowCount
  calc
    2 ^ c * ((c + 1) * (c + 1)) <=
        2 ^ c * (2 ^ (c + 1) * 2 ^ (c + 1)) :=
      Nat.mul_le_mul_left (2 ^ c) (Nat.mul_le_mul h1 h1)
    _ = 2 ^ (3 * c + 2) := by
      rw [<- Nat.pow_add, <- Nat.pow_add]
      congr 1
      omega

/-- Counted table payload identity: rows times fixed width. -/
theorem bpFringeChunkTable_payload_length (c : Nat) :
    (bpFringeChunkTable c).payload.length =
      bpFringeChunkRowCount c * bpFringeChunkEntryWidth c := by
  have h := (bpFringeChunkTable c).payload_length
  rw [bpFringeChunkEntries_length] at h
  exact h

/-- Component-level exact physical erasure of the table store. -/
theorem bpFringeChunkTable_store_erases (c : Nat) :
    SuccinctSpace.flattenPayloadWords
        (bpFringeChunkTable c).store.words.toList =
      (bpFringeChunkTable c).payload :=
  (bpFringeChunkTable c).store.payload_eq_words_join

/-- Table bit budget over the public input size (`bpCode` length is `2n`). -/
def bpFringeTableOverhead (n : Nat) : Nat :=
  bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) *
    bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n))

/-- The chunk-table budget is `o(n)`. -/
theorem bpFringeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear bpFringeTableOverhead := by
  intro scale hscale
  refine ⟨2 ^ (16 * scale + 80), ?_⟩
  intro n hn
  have hpos : 0 < 2 ^ (16 * scale + 80) := Nat.pow_pos (by omega)
  have hn1 : 1 <= n := Nat.le_trans hpos hn
  have hlogbig : 16 * scale + 80 <= Nat.log2 n := by
    rcases Nat.lt_or_ge (Nat.log2 n) (16 * scale + 80) with hlt | hge
    · exfalso
      have h2 : 2 ^ (Nat.log2 n + 1) <= 2 ^ (16 * scale + 80) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
      exact Nat.lt_irrefl n (Nat.lt_of_lt_of_le h3 (Nat.le_trans h2 hn))
    · exact hge
  -- log2 (2n) <= log2 n + 1
  have hlt2n : 2 * n < 2 ^ (Nat.log2 n + 2) := by
    have h3 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    have hdouble : 2 ^ (Nat.log2 n + 2) = 2 * 2 ^ (Nat.log2 n + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega
  have hlog2n : Nat.log2 (2 * n) <= Nat.log2 n + 1 := by
    rcases Nat.lt_or_ge (Nat.log2 n + 1) (Nat.log2 (2 * n)) with hlt | hge
    · exfalso
      have hp : 2 ^ (Nat.log2 n + 2) <= 2 ^ Nat.log2 (2 * n) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hself : 2 ^ Nat.log2 (2 * n) <= 2 * n :=
        Nat.log2_self_le (by omega)
      omega
    · exact hge
  have hcle :
      bpFringeChunkBits (2 * n) <= Nat.log2 n / 8 + 2 := by
    unfold bpFringeChunkBits
    omega
  -- budget <= 2^(6c+8)
  have hwidth :=
    bpFringeChunkEntryWidth_le (bpFringeChunkBits (2 * n))
  have hwidthPow :
      3 * bpFringeChunkBits (2 * n) + 6 <=
        2 ^ (3 * bpFringeChunkBits (2 * n) + 6) :=
    SuccinctSpace.nat_le_two_pow _
  have hrows :=
    bpFringeChunkRowCount_le_two_pow (bpFringeChunkBits (2 * n))
  have hT :
      bpFringeTableOverhead n <=
        2 ^ (6 * bpFringeChunkBits (2 * n) + 8) := by
    unfold bpFringeTableOverhead
    calc
      bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) *
          bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) <=
        2 ^ (3 * bpFringeChunkBits (2 * n) + 2) *
          2 ^ (3 * bpFringeChunkBits (2 * n) + 6) :=
        Nat.mul_le_mul hrows (by omega)
      _ = 2 ^ (6 * bpFringeChunkBits (2 * n) + 8) := by
        rw [<- Nat.pow_add]
        congr 1
        omega
  have hscalePow : scale <= 2 ^ scale := SuccinctSpace.nat_le_two_pow scale
  have hexp :
      scale + (6 * bpFringeChunkBits (2 * n) + 8) <= Nat.log2 n := by
    have hq : 6 * (Nat.log2 n / 8) <= Nat.log2 n - Nat.log2 n / 4 := by
      omega
    omega
  have hchain :
      scale * bpFringeTableOverhead n <=
        2 ^ (scale + (6 * bpFringeChunkBits (2 * n) + 8)) := by
    calc
      scale * bpFringeTableOverhead n <=
          2 ^ scale * 2 ^ (6 * bpFringeChunkBits (2 * n) + 8) :=
        Nat.mul_le_mul hscalePow hT
      _ = 2 ^ (scale + (6 * bpFringeChunkBits (2 * n) + 8)) := by
        rw [<- Nat.pow_add]
  have hlogPow : 2 ^ Nat.log2 n <= n := Nat.log2_self_le (by omega)
  have hmono :
      2 ^ (scale + (6 * bpFringeChunkBits (2 * n) + 8)) <=
        2 ^ Nat.log2 n :=
    Nat.pow_le_pow_right (by omega) hexp
  omega

/--
Per-source capacity feed: the table stores one word per row, and the row
count is bounded by `64 * (n + 1)` at every size — comfortably inside the
`400000 * (n + 1)` reviewer capacity for the wiring rung's extension.
-/
theorem bpFringeChunkRowCount_le_linear (n : Nat) :
    bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) <= 64 * (n + 1) := by
  have hrows := bpFringeChunkRowCount_le_two_pow (bpFringeChunkBits (2 * n))
  have hc : bpFringeChunkBits (2 * n) = Nat.log2 (2 * n) / 8 + 1 := rfl
  have h38 : 3 * (Nat.log2 (2 * n) / 8) <= Nat.log2 (2 * n) := by omega
  have hsplit :
      2 ^ (3 * bpFringeChunkBits (2 * n) + 2) =
        32 * 2 ^ (3 * (Nat.log2 (2 * n) / 8)) := by
    rw [hc]
    rw [show 3 * (Nat.log2 (2 * n) / 8 + 1) + 2 =
      3 * (Nat.log2 (2 * n) / 8) + 5 by omega]
    rw [Nat.pow_add]
    omega
  have hmono :
      2 ^ (3 * (Nat.log2 (2 * n) / 8)) <= 2 ^ Nat.log2 (2 * n) :=
    Nat.pow_le_pow_right (by omega) h38
  cases n with
  | zero =>
      have hle := hrows
      rw [hsplit] at hle
      simp only [Nat.mul_zero] at hle ⊢
      have hlog0 : Nat.log2 0 = 0 := by simp
      rw [hlog0] at hle
      simp at hle
      omega
  | succ m =>
      have hpow2n : 2 ^ Nat.log2 (2 * (m + 1)) <= 2 * (m + 1) :=
        Nat.log2_self_le (by omega)
      have hle := hrows
      rw [hsplit] at hle
      have hstep :
          32 * 2 ^ (3 * (Nat.log2 (2 * (m + 1)) / 8)) <=
            32 * (2 * (m + 1)) := by
        have := Nat.le_trans hmono hpow2n
        omega
      omega

/--
The packed table word fits the declared reviewer machine word at every
input size.
-/
theorem bpFringeChunkEntryWidth_le_reviewerWordBits (n : Nat) :
    bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) <=
      SuccinctFinal.concreteBPNativeSuccinctRMQReviewerWordBits n := by
  have hwidth := bpFringeChunkEntryWidth_le (bpFringeChunkBits (2 * n))
  have hc : bpFringeChunkBits (2 * n) = Nat.log2 (2 * n) / 8 + 1 := rfl
  have hRWB :=
    SuccinctFinal.concreteBPNativeSuccinctRMQReviewerWordBits_eq n
  have h18 : 18 <= Nat.log2 (400000 * (n + 1)) := by
    rcases Nat.lt_or_ge (Nat.log2 (400000 * (n + 1))) 18 with hlt | hge
    · exfalso
      have h3 :
          400000 * (n + 1) < 2 ^ (Nat.log2 (400000 * (n + 1)) + 1) :=
        Nat.lt_log2_self
      have h2 :
          2 ^ (Nat.log2 (400000 * (n + 1)) + 1) <= 2 ^ 18 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hval : (2 : Nat) ^ 18 = 262144 := by decide
      have hlin : 400000 <= 400000 * (n + 1) := by
        have := Nat.mul_le_mul_left 400000 (show 1 <= n + 1 by omega)
        omega
      omega
    · exact hge
  have hmono :
      Nat.log2 (2 * n) <= Nat.log2 (400000 * (n + 1)) := by
    have h :=
      SuccinctRank.machineWordBits_mono_le
        (show 2 * n <= 400000 * (n + 1) by omega)
    unfold SuccinctRank.machineWordBits at h
    omega
  rw [hRWB]
  omega

/-! ## Committed candidate amendment (consumed by the wiring rung) -/

/-- Candidate amended overhead: accepted overhead plus the table budget. -/
def bpChunkedOverheadCandidate (n : Nat) : Nat :=
  SuccinctClassic.overhead n + bpFringeTableOverhead n

/-- Candidate amended payload: accepted payload plus the counted table. -/
def bpChunkedBuildPayloadCandidate (xs : List Int) : List Bool :=
  SuccinctClassic.buildPayload xs ++
    (bpFringeChunkTable
      (bpFringeChunkBits
        (SuccinctClassic.cartesianShape xs).bpCode.length)).payload

/-- The amended overhead stays `o(n)`. -/
theorem bpChunkedOverheadCandidate_littleO :
    SuccinctSpace.LittleOLinear bpChunkedOverheadCandidate :=
  SuccinctClassic.overhead_littleO.add bpFringeTableOverhead_littleO

/-- The amended payload keeps the public `2n + o(n)` statement shape. -/
theorem bpChunkedBuildPayloadCandidate_length (xs : List Int) :
    (bpChunkedBuildPayloadCandidate xs).length <=
      2 * xs.length + bpChunkedOverheadCandidate xs.length := by
  have hbase := SuccinctClassic.buildPayload_length xs
  have hshape :
      (SuccinctClassic.cartesianShape xs).bpCode.length =
        2 * xs.length := by
    rw [Cartesian.CartesianShape.bpCode_length]
    rw [show (SuccinctClassic.cartesianShape xs).size = xs.length from
      Cartesian.shape_size xs]
  have htable :
      (bpFringeChunkTable
        (bpFringeChunkBits
          (SuccinctClassic.cartesianShape xs).bpCode.length)).payload.length =
        bpFringeTableOverhead xs.length := by
    rw [hshape]
    exact bpFringeChunkTable_payload_length _
  unfold bpChunkedBuildPayloadCandidate bpChunkedOverheadCandidate
  rw [List.length_append]
  omega

end SuccinctClose

end RMQ
