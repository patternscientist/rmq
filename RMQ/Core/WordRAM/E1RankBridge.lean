import RMQ.Core.WordRAM.E1MachineCalculus
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedRankSelectLeafTrace

/-!
# E1 amended machine: rank-close fold bridge lemmas (M3c-1a)

Arithmetic and trace-shape bridges between the accepted charged rank fold
(`bpChunkedWordRankTraceFromWithStore`, `ChargedRankSelectTrace.lean`) and
the E1 machine's constant-form register arithmetic (frozen matrix
REQ-E1-03/04, worklog M3c step 2(a)):

* little-endian decode bridges: dropping `k` bits divides the decoded word
  by `2 ^ k`, taking `k` bits reduces it modulo `2 ^ k` — so the fold's
  window chunk value `bpFringeWindowChunkValue c word j` is exactly the
  div/mod-by-constant expression `bitsToNatLE word / 2 ^ (j * c) % 2 ^ c`
  the machine computes from its decoded word register;
* truncated-subtraction forms of `Nat.min` and `Nat.mod`, matching the
  machine's `sub`/`divConst`/`mulConst` compilation of the slice length
  `bpWordChunkSliceLen`, the 8-cap chunk count `bpWordChunkCount`, and the
  in-chunk rank decode `bpChunkRankOfEntry`;
* the option-shift decode bridge: the machine's `decodeRead` register minus
  one is exactly the fold's `(·.map bitsToNatLE).getD 0` entry decode, and
  the zero test recognizes exactly the missing word;
* positional shape of the fold: the fold's trace is the literal
  `List.range`-indexed read list (one chunk-table read per visited chunk, in
  ascending chunk order), and its value is the literal iterated accumulator
  `bpWordRankAccAt` — the two facts the machine loop invariant re-proves
  step by step through `RunsTo.iterate`;
* `iterLog` combinators aligning the loop backbone's descending-counter
  receipt concatenation with the ascending `List.range` order of the
  accepted trace.

Nothing here mentions a concrete program; the concrete rank-close block and
its `RunsTo` simulation live in `RMQ.Core.WordRAM.E1RankBlock`.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-! ## Truncated-subtraction and mod-by-constant forms -/

/-- `Nat.min` in the machine's truncated-subtraction form. -/
theorem nat_min_eq_sub_sub (a b : Nat) : Nat.min a b = a - (a - b) := by
  rcases Nat.le_total a b with h | h
  · have h1 : Nat.min a b = a := Nat.min_eq_left h
    omega
  · have h1 : Nat.min a b = b := Nat.min_eq_right h
    omega

/-- `Nat.mod` in the machine's div/mul/sub constant form. -/
theorem nat_mod_eq_sub_div_mul (a b : Nat) : a % b = a - a / b * b := by
  have h := Nat.div_add_mod a b
  have h' : a / b * b + a % b = a := by
    rw [Nat.mul_comm] at h
    exact h
  omega

/-- The slice length is two machine subtractions from `e - j * c`. -/
theorem bpWordChunkSliceLen_eq_sub (c e j : Nat) :
    bpWordChunkSliceLen c e j = c - (c - (e - j * c)) := by
  unfold bpWordChunkSliceLen
  rw [nat_min_eq_sub_sub]

/-- The 8-capped chunk count is a machine subtraction chain. -/
theorem bpWordChunkCount_eq_sub (c e : Nat) :
    bpWordChunkCount c e =
      (e - 1) / c + 1 - ((e - 1) / c + 1 - 8) := by
  unfold bpWordChunkCount
  rw [nat_min_eq_sub_sub]

/-- Inside the stored word, the effective limit is the limit itself. -/
theorem bpWordRankEffLimit_eq_of_le {word : List Bool} {limit : Nat}
    (h : limit <= word.length) :
    bpWordRankEffLimit word limit = limit := by
  unfold bpWordRankEffLimit
  exact Nat.min_eq_left h

/-- The false-target in-chunk rank decode, in the machine's literal
constant-arithmetic form. -/
theorem bpChunkRankOfEntry_false_eq (c t entry : Nat) :
    bpChunkRankOfEntry c false t entry =
      t - (entry / (c + 1) - entry / (c + 1) / (2 * c + 2) * (2 * c + 2)
            + t - c) / 2 := by
  show t - (entry / (c + 1) % (2 * c + 2) + t - c) / 2 = _
  rw [nat_mod_eq_sub_div_mul (entry / (c + 1)) (2 * c + 2)]

/-- The true-target in-chunk rank decode, in the machine's literal
constant-arithmetic form (the false chain WITHOUT the final `t -`
subtraction — one machine instruction fewer). -/
theorem bpChunkRankOfEntry_true_eq (c t entry : Nat) :
    bpChunkRankOfEntry c true t entry =
      (entry / (c + 1) - entry / (c + 1) / (2 * c + 2) * (2 * c + 2)
        + t - c) / 2 := by
  show (entry / (c + 1) % (2 * c + 2) + t - c) / 2 = _
  rw [nat_mod_eq_sub_div_mul (entry / (c + 1)) (2 * c + 2)]

/-! ## Little-endian decode bridges -/

/-- Decode of the empty word. -/
theorem bitsToNatLE_nil : bitsToNatLE ([] : List Bool) = 0 := rfl

/-- Dropping `k` bits divides the little-endian decode by `2 ^ k`. -/
theorem bitsToNatLE_drop :
    forall (k : Nat) (bits : List Bool),
      bitsToNatLE (bits.drop k) = bitsToNatLE bits / 2 ^ k
  | 0, bits => by simp
  | k + 1, [] => by simp [bitsToNatLE]
  | k + 1, b :: rest => by
      have ih := bitsToNatLE_drop k rest
      have hhead : bitsToNatLE (b :: rest) / 2 = bitsToNatLE rest := by
        show (bitToNat b + 2 * bitsToNatLE rest) / 2 = bitsToNatLE rest
        cases b <;> simp [bitToNat] <;> omega
      calc bitsToNatLE ((b :: rest).drop (k + 1))
          = bitsToNatLE (rest.drop k) := rfl
        _ = bitsToNatLE rest / 2 ^ k := ih
        _ = bitsToNatLE (b :: rest) / 2 / 2 ^ k := by rw [hhead]
        _ = bitsToNatLE (b :: rest) / 2 ^ (k + 1) := by
            rw [Nat.div_div_eq_div_mul]
            congr 1
            rw [Nat.pow_succ, Nat.mul_comm]

/-- Little-endian split: the word is its `k`-bit prefix plus `2 ^ k` times
its tail. -/
theorem bitsToNatLE_take_add_drop :
    forall (k : Nat) (bits : List Bool),
      bitsToNatLE bits =
        bitsToNatLE (bits.take k) + 2 ^ k * bitsToNatLE (bits.drop k)
  | 0, bits => by simp [bitsToNatLE_nil]
  | k + 1, [] => rfl
  | k + 1, b :: rest => by
      have ih := bitsToNatLE_take_add_drop k rest
      show bitToNat b + 2 * bitsToNatLE rest =
        bitToNat b + 2 * bitsToNatLE (rest.take k) +
          2 ^ (k + 1) * bitsToNatLE (rest.drop k)
      have hpow : (2 : Nat) ^ (k + 1) * bitsToNatLE (rest.drop k) =
          2 * (2 ^ k * bitsToNatLE (rest.drop k)) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
      rw [hpow]
      omega

/-- Taking `k` bits reduces the little-endian decode modulo `2 ^ k`. -/
theorem bitsToNatLE_take (k : Nat) (bits : List Bool) :
    bitsToNatLE (bits.take k) = bitsToNatLE bits % 2 ^ k := by
  have hsplit := bitsToNatLE_take_add_drop k bits
  have hdrop := bitsToNatLE_drop k bits
  have hdm := Nat.div_add_mod (bitsToNatLE bits) (2 ^ k)
  have hlt : bitsToNatLE (bits.take k) < 2 ^ k := by
    have h :=
      GenericSelect.bitsToNatLE_lt_two_pow_length (bits.take k)
    have hlen : (bits.take k).length <= k := by
      rw [List.length_take]
      exact Nat.min_le_left _ _
    have hmono : (2 : Nat) ^ (bits.take k).length <= 2 ^ k :=
      Nat.pow_le_pow_right (by omega) hlen
    omega
  rw [hdrop] at hsplit
  omega

/-- The fold's window chunk value is the machine's div/mod-by-constant
expression over the decoded word register. -/
theorem bpFringeWindowChunkValue_eq_div_mod (c : Nat) (word : List Bool)
    (j : Nat) :
    bpFringeWindowChunkValue c word j =
      bitsToNatLE word / 2 ^ (j * c) % 2 ^ c := by
  unfold bpFringeWindowChunkValue
  rw [bitsToNatLE_take, bitsToNatLE_drop]

/-- Advancing one chunk divides the remaining-word register by `2 ^ c`. -/
theorem div_pow_chunk_succ (W c j : Nat) :
    W / 2 ^ (j * c) / 2 ^ c = W / 2 ^ ((j + 1) * c) := by
  rw [Nat.div_div_eq_div_mul, <- Nat.pow_add]
  congr 1
  rw [Nat.succ_mul]

/-! ## Option-shift decode bridges -/

/-- The machine's decoded read register minus one is the fold's
`getD 0` entry decode. -/
theorem decodeRead_pred_eq_map_getD (w? : Option (List Bool)) :
    WordRAM.E1Machine.decodeRead w? - 1 =
      (w?.map bitsToNatLE).getD 0 := by
  cases w? with
  | none => rfl
  | some w =>
      show RMQ.WordRAM.bitsToNatLE w + 1 - 1 = bitsToNatLE w
      rw [WordRAMBridge.bitsToNatLE_eq]
      omega

/-- The machine's zero test on a decoded read register recognizes exactly
the missing word. -/
theorem decodeRead_eq_zero_iff (w? : Option (List Bool)) :
    WordRAM.E1Machine.decodeRead w? = 0 <-> w? = none := by
  cases w? with
  | none => simp
  | some w =>
      show RMQ.WordRAM.bitsToNatLE w + 1 = 0 <-> _
      simp

/-- Decode of a present word, in register terms. -/
theorem decodeRead_some_eq (w : List Bool) :
    WordRAM.E1Machine.decodeRead (some w) = bitsToNatLE w + 1 := by
  show RMQ.WordRAM.bitsToNatLE w + 1 = _
  rw [WordRAMBridge.bitsToNatLE_eq]

/-! ## Positional shape of the charged rank fold -/

/-- Chunk-table slot the fold reads at chunk `j`. -/
def bpWordRankChunkSlotAt (c : Nat) (word : List Bool) (e j : Nat) : Nat :=
  bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
    (bpWordChunkSliceLen c e j) (bpWordChunkSliceLen c e j)

/-- Chunk-table read event the fold emits at chunk `j`. -/
def bpWordRankChunkEventAt (store : WordRAM.ReadStore)
    (tableSegment c : Nat) (word : List Bool) (e j : Nat) :
    WordRAM.TraceEvent :=
  WordRAM.TraceEvent.readWord tableSegment
    (bpWordRankChunkSlotAt c word e j)
    (store.readWord? tableSegment (bpWordRankChunkSlotAt c word e j))

/-- The fold's trace is the literal ascending-chunk read list. -/
theorem bpChunkedWordRankTraceFromWithStore_trace_map
    (store : WordRAM.ReadStore) (tableSegment c : Nat) (target : Bool)
    (word : List Bool) (e : Nat) :
    forall (count j acc : Nat),
      (bpChunkedWordRankTraceFromWithStore store tableSegment c target
          word e j count acc).trace =
        (List.range count).map
          (fun d =>
            bpWordRankChunkEventAt store tableSegment c word e (j + d)) := by
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
                (bpWordChunkSliceLen c e j) (bpWordChunkSliceLen c e j)))
            _).trace = _
      show
        (bpChunkReadTraceResult store tableSegment
            (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
              (bpWordChunkSliceLen c e j) (bpWordChunkSliceLen c e j))).trace
          ++
          (bpChunkedWordRankTraceFromWithStore store tableSegment c target
            word e (j + 1) count _).trace = _
      rw [ih (j + 1)]
      rw [List.range_succ_eq_map]
      show
        bpWordRankChunkEventAt store tableSegment c word e j ::
            (List.range count).map
              (fun d =>
                bpWordRankChunkEventAt store tableSegment c word e
                  (j + 1 + d)) =
          bpWordRankChunkEventAt store tableSegment c word e (j + 0) ::
            ((List.range count).map (fun i => i + 1)).map
              (fun d =>
                bpWordRankChunkEventAt store tableSegment c word e (j + d))
      rw [List.map_map]
      have harg : j + 0 = j := rfl
      rw [harg]
      congr 1
      apply List.map_congr_left
      intro d _
      show
        bpWordRankChunkEventAt store tableSegment c word e (j + 1 + d) =
          bpWordRankChunkEventAt store tableSegment c word e (j + (d + 1))
      congr 1
      omega

/-- The literal iterated accumulator of the charged rank fold. -/
def bpWordRankAccAt (store : WordRAM.ReadStore) (tableSegment c : Nat)
    (target : Bool) (word : List Bool) (e : Nat) : Nat -> Nat
  | 0 => 0
  | j + 1 =>
      bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j)
        (bpWordRankAccAt store tableSegment c target word e j)
        ((store.readWord? tableSegment
            (bpWordRankChunkSlotAt c word e j)).map bitsToNatLE)

/-- The fold's value from chunk `j` with the iterated accumulator seeded at
`j` is the iterated accumulator at `j + count`. -/
theorem bpChunkedWordRankTraceFromWithStore_value_accAt
    (store : WordRAM.ReadStore) (tableSegment c : Nat) (target : Bool)
    (word : List Bool) (e : Nat) :
    forall (count j : Nat),
      (bpChunkedWordRankTraceFromWithStore store tableSegment c target
          word e j count
          (bpWordRankAccAt store tableSegment c target word e j)).value =
        bpWordRankAccAt store tableSegment c target word e (j + count) := by
  intro count
  induction count with
  | zero =>
      intro j
      rfl
  | succ count ih =>
      intro j
      show
        (WordRAM.TraceResult.bind
            (bpChunkReadTraceResult store tableSegment
              (bpFringeChunkSlot c (bpFringeWindowChunkValue c word j)
                (bpWordChunkSliceLen c e j) (bpWordChunkSliceLen c e j)))
            _).value = _
      show
        (bpChunkedWordRankTraceFromWithStore store tableSegment c target
            word e (j + 1) count
            (bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j)
              (bpWordRankAccAt store tableSegment c target word e j)
              ((store.readWord? tableSegment
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c e j)
                    (bpWordChunkSliceLen c e j))).map
                bitsToNatLE))).value = _
      have hstep :
          bpWordRankStepDecoded c target (bpWordChunkSliceLen c e j)
              (bpWordRankAccAt store tableSegment c target word e j)
              ((store.readWord? tableSegment
                  (bpFringeChunkSlot c
                    (bpFringeWindowChunkValue c word j)
                    (bpWordChunkSliceLen c e j)
                    (bpWordChunkSliceLen c e j))).map
                bitsToNatLE) =
            bpWordRankAccAt store tableSegment c target word e (j + 1) :=
        rfl
      rw [hstep, ih (j + 1)]
      congr 1
      omega

end SuccinctClose

namespace WordRAM

namespace E1Machine

/-! ## `iterLog` combinators (descending counter to ascending order) -/

/-- `iterLog` only inspects the log function below the counter. -/
theorem iterLog_congr {α : Type} {f g : Nat -> List α} :
    forall (n : Nat), (forall k, k < n -> f k = g k) ->
      iterLog f n = iterLog g n := by
  intro n
  induction n with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro h
      show f n ++ iterLog f n = g n ++ iterLog g n
      rw [h n (by omega), ih (fun k hk => h k (by omega))]

/-- A descending-counter singleton `iterLog` is the ascending
`List.range` map: iteration executed with remaining counter `k + 1`
contributes index `j + (n - (k + 1))`, so the concatenation is
`j, j + 1, ...` in execution order. -/
theorem iterLog_singleton_desc {α : Type} (g : Nat -> α) :
    forall (n j : Nat),
      iterLog (fun k => [g (j + (n - (k + 1)))]) n =
        (List.range n).map (fun d => g (j + d)) := by
  intro n
  induction n with
  | zero =>
      intro j
      rfl
  | succ n ih =>
      intro j
      show
        [g (j + (n + 1 - (n + 1)))] ++
            iterLog (fun k => [g (j + (n + 1 - (k + 1)))]) n =
          (List.range (n + 1)).map (fun d => g (j + d))
      have hcongr :
          iterLog (fun k => [g (j + (n + 1 - (k + 1)))]) n =
            iterLog (fun k => [g (j + 1 + (n - (k + 1)))]) n := by
        apply iterLog_congr
        intro k hk
        have harg : j + (n + 1 - (k + 1)) = j + 1 + (n - (k + 1)) := by
          omega
        rw [harg]
      rw [hcongr, ih (j + 1), List.range_succ_eq_map, List.map_cons,
        List.map_map]
      have hhead : j + (n + 1 - (n + 1)) = j + 0 := by omega
      rw [hhead]
      show g (j + 0) :: (List.range n).map (fun d => g (j + 1 + d)) =
        g (j + 0) :: (List.range n).map ((fun d => g (j + d)) ∘
          (fun i => i + 1))
      congr 1
      apply List.map_congr_left
      intro d _
      show g (j + 1 + d) = g (j + (d + 1))
      congr 1
      omega

/-- Constant-body `iterLog` length: `n` copies of the body log. -/
theorem iterLog_const_length {α : Type} (L : List α) :
    forall (n : Nat), (iterLog (fun _ => L) n).length = n * L.length := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      show (L ++ iterLog (fun _ => L) n).length = (n + 1) * L.length
      rw [List.length_append, ih, Nat.succ_mul]
      omega

/-- Category count over a constant-body `iterLog`. -/
theorem catCount_iterLog_const (L : List Category) (target : Category) :
    forall (n : Nat),
      catCount (iterLog (fun _ => L) n) target = n * catCount L target := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      show catCount (L ++ iterLog (fun _ => L) n) target = _
      have happ :
          forall (xs ys : List Category),
            catCount (xs ++ ys) target =
              catCount xs target + catCount ys target := by
        intro xs
        induction xs with
        | nil => intro ys; simp [catCount]
        | cons x rest ihx =>
            intro ys
            show (if x = target then 1 else 0) + catCount (rest ++ ys)
                target = _
            rw [ihx ys, catCount_cons]
            omega
      rw [happ, ih, Nat.succ_mul]
      omega

/-- Category count over an appended log (general splitting helper). -/
theorem catCount_append (xs ys : List Category) (target : Category) :
    catCount (xs ++ ys) target =
      catCount xs target + catCount ys target := by
  induction xs with
  | nil => simp [catCount]
  | cons x rest ih =>
      show (if x = target then 1 else 0) + catCount (rest ++ ys) target = _
      rw [ih, catCount_cons]
      omega

end E1Machine

end WordRAM

end RMQ
