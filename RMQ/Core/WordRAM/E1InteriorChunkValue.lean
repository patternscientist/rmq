import RMQ.Core.WordRAM.E1InteriorChunkFold

/-!
# E1 amended machine: THE INTERIOR CHUNK FOLD'S VALUE BRIDGE (M3d-13 item 1)

`interiorChunkFold_runsTo` (`E1InteriorChunkFold.lean:1785`) proves the
fold's RECEIPT against the route positionally -- address for address, word
for word -- but states its VALUE only in the machine's own vocabulary:
`cOut` is `(chunkRevAt wordScale (chunkAcc ...) n).2 + 1` on the good path
and `0` otherwise.  Nothing yet says that number is the number the route
decodes.

This module closes that gap.  The headline
`chunkFoldValue_eq_route_decode` equates the machine's option-shifted cell
with `fixedWidthNatTableMachineDecode` (`MachineChunkedTable.lean:215`),
THE ROUTE'S OWN DECODE FUNCTION, applied to the words the route's adapter
reads at the route's own addresses.

## Why this needed a new lemma about `bitsToNatLE`

The route's value is `bitsToNatLE` of the CONCATENATION of the chunks
(`collectPayloadWords`, `MachineChunkedTable.lean:201`).  Relating a
concatenation to its parts is `bitsToNatLE_append`, and the repository did
not have it: a search of `RMQ/Core/SuccinctSpace/` found only
`TablesRAM.lean:18` (`bitsToNatLE_eq`, the two namespaces' decoders agree)
and `WordStore.lean:53` (`bitsToNatLE_natToBitsLE_of_lt`, a round trip at
one width).  It is proved here rather than in `WordStore.lean` so that the
frozen space-side modules are untouched.

## The shape of the argument

Three facts compose.

1. `bitsToNatLE (a ++ b) = bitsToNatLE a + 2 ^ a.length * bitsToNatLE b`
   (`bitsToNatLE_append`).  With every chunk exactly `wordSize` bits this
   makes the route's value LITTLE-endian in the chunk index, base
   `2 ^ wordSize`.

2. The machine's big-endian accumulator, run through the read-free
   digit-reversal loop, is that same little-endian value
   (`chunkRevGen_chunkAcc`).  The reversal is stated on a GENERALISED
   accumulator `chunkRevGen`, carrying the partially built result as a
   parameter, because `chunkRevAt` peels a digit off the BOTTOM of the
   accumulator while `chunkAcc` builds one onto the bottom -- the two
   recursions run in opposite directions and no induction on `chunkRevAt`
   alone lines them up.  `chunkRevGen_succ_front` is the front-peeling
   identity that turns the mismatch into a single induction.

3. The two sides' recursions peel from OPPOSITE ENDS -- the route's
   address list `consecutiveWordIndices` is head-first, while `chunkAcc`
   and `chunkBad` are last-first -- so `chunkLit_succ_front` and
   `chunkBad_succ_front` convert.  These are not bookkeeping: without them
   the induction does not close.

## The width hypothesis is real, and is not discharged here

`chunkFoldValue_eq_route_decode` carries
`∀ j < n, ∀ w, store.readWord? segment (start + j) = some w → w.length = wordSize`.
That is a genuine premise, not decoration: a store whose chunks were
ragged would make the route's concatenation carry a different value than
any fixed-base digit reversal, and the machine would be wrong rather than
merely unproved.  It is sourced on the `BoundedPayloadWordStore` side and
is discharged where the fold is composed against a concrete store, not
here -- stating it explicitly is what keeps the debt visible.
-/

namespace RMQ
namespace WordRAM
namespace E1InteriorChunkValue

open E1Machine
open E1InteriorChunkFold

/-! ## `bitsToNatLE` on an append -/

/--
THE MISSING APPEND LEMMA.

Little-endian decoding splits over concatenation: the prefix contributes
its own value and the suffix is shifted by the prefix's width.  Stated for
the space-side `RMQ.SuccinctSpace.bitsToNatLE`, which is the decoder
`fixedWidthNatTableMachineDecode` uses.
-/
theorem bitsToNatLE_append (a b : List Bool) :
    RMQ.SuccinctSpace.bitsToNatLE (a ++ b) =
      RMQ.SuccinctSpace.bitsToNatLE a +
        2 ^ a.length * RMQ.SuccinctSpace.bitsToNatLE b := by
  induction a with
  | nil => simp [RMQ.SuccinctSpace.bitsToNatLE]
  | cons bit rest ih =>
      have hpow : (2 : Nat) ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
        rw [Nat.pow_succ, Nat.mul_comm]
      show RMQ.SuccinctSpace.bitToNat bit +
          2 * RMQ.SuccinctSpace.bitsToNatLE (rest ++ b) =
        RMQ.SuccinctSpace.bitToNat bit +
          2 * RMQ.SuccinctSpace.bitsToNatLE rest +
          2 ^ (rest.length + 1) * RMQ.SuccinctSpace.bitsToNatLE b
      rw [ih, hpow, Nat.mul_assoc, Nat.mul_add]
      omega

/--
A decoded word is smaller than two to its own width.  This is what makes
each chunk a legitimate base-`2 ^ wordSize` digit, and hence what makes
the digit reversal exact rather than lossy.
-/
theorem bitsToNatLE_lt_two_pow (w : List Bool) :
    RMQ.SuccinctSpace.bitsToNatLE w < 2 ^ w.length := by
  induction w with
  | nil => simp [RMQ.SuccinctSpace.bitsToNatLE]
  | cons bit rest ih =>
      have hbit : RMQ.SuccinctSpace.bitToNat bit < 2 := by
        unfold RMQ.SuccinctSpace.bitToNat
        cases bit <;> simp
      have hpow : (2 : Nat) ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
        rw [Nat.pow_succ, Nat.mul_comm]
      show RMQ.SuccinctSpace.bitToNat bit +
          2 * RMQ.SuccinctSpace.bitsToNatLE rest < 2 ^ (rest.length + 1)
      rw [hpow]
      omega

/-! ## The little-endian spec value the fold must produce -/

/--
The route's value for the first `j` chunks, little-endian in the chunk
index: chunk `k` weighs `scale ^ k`.  Defined last-first to match
`chunkAcc`'s recursion; `chunkLit_succ_front` gives the head-first form the
route's address list needs.
-/
def chunkLit (store : ReadStore) (segment scale start : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      chunkLit store segment scale start j
        + (decodeRead (store.readWord? segment (start + j)) - 1) * scale ^ j

/-- Head-first form of `chunkLit`: the first chunk is the low digit and
everything above it is the little-endian value of the rest, shifted once. -/
theorem chunkLit_succ_front (store : ReadStore) (segment scale start : Nat) :
    ∀ n : Nat,
      chunkLit store segment scale start (n + 1) =
        (decodeRead (store.readWord? segment start) - 1)
          + scale * chunkLit store segment scale (start + 1) n := by
  intro n
  induction n generalizing start with
  | zero => simp [chunkLit]
  | succ n ih =>
      have hidx : start + (n + 1) = start + 1 + n := by omega
      have hpow : scale ^ (n + 1) = scale * scale ^ n := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hstep : chunkLit store segment scale (start + 1) (n + 1)
          = chunkLit store segment scale (start + 1) n
            + (decodeRead (store.readWord? segment (start + 1 + n)) - 1)
              * scale ^ n := rfl
      have hcomm : ∀ d : Nat,
          d * (scale * scale ^ n) = scale * (d * scale ^ n) := by
        intro d
        rw [← Nat.mul_assoc, Nat.mul_comm d scale, Nat.mul_assoc]
      show chunkLit store segment scale start (n + 1)
          + (decodeRead (store.readWord? segment (start + (n + 1))) - 1)
            * scale ^ (n + 1) =
        (decodeRead (store.readWord? segment start) - 1)
          + scale * chunkLit store segment scale (start + 1) (n + 1)
      rw [ih start, hidx, hpow, hstep, Nat.mul_add, hcomm]
      omega

/-- Head-first form of `chunkBad`. -/
theorem chunkBad_succ_front (store : ReadStore) (segment start : Nat) :
    ∀ n : Nat,
      chunkBad store segment start (n + 1) =
        (if decodeRead (store.readWord? segment start) = 0 then 1 else 0)
          + chunkBad store segment (start + 1) n := by
  intro n
  induction n generalizing start with
  | zero => simp [chunkBad]
  | succ n ih =>
      have hidx : start + (n + 1) = start + 1 + n := by omega
      have hstep : chunkBad store segment (start + 1) (n + 1)
          = chunkBad store segment (start + 1) n
            + (if decodeRead (store.readWord? segment (start + 1 + n)) = 0
               then 1 else 0) := rfl
      show chunkBad store segment start (n + 1)
          + (if decodeRead (store.readWord? segment (start + (n + 1))) = 0
             then 1 else 0) =
        (if decodeRead (store.readWord? segment start) = 0 then 1 else 0)
          + chunkBad store segment (start + 1) (n + 1)
      rw [ih start, hidx, hstep]
      omega

/-! ## The digit reversal, generalised

`chunkRevAt` starts the little-endian result at `0`.  The induction that
relates it to `chunkAcc` has to peel a digit off the FRONT of the
accumulator, which pushes a digit into the result before the recursive
call, so the result cannot stay `0`.  `chunkRevGen` is the same loop with
the running result exposed.
-/

/-- The digit-reversal step iterated `j` times from an arbitrary running
result `r0`. -/
def chunkRevGen (scale acc0 r0 : Nat) : Nat → Nat × Nat
  | 0 => (acc0, r0)
  | j + 1 =>
      ((chunkRevGen scale acc0 r0 j).1 / scale,
        (chunkRevGen scale acc0 r0 j).2 * scale
          + (chunkRevGen scale acc0 r0 j).1 % scale)

/-- `chunkRevAt` is `chunkRevGen` started at result `0`. -/
theorem chunkRevAt_eq_gen (scale acc0 : Nat) :
    ∀ n : Nat, chunkRevAt scale acc0 n = chunkRevGen scale acc0 0 n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => show (_, _) = (_, _); rw [ih]

/--
THE FRONT-PEELING IDENTITY.

Running the reversal `n + 1` times from `(a, r)` is running it `n` times
from the state after one step.  `chunkRevGen`'s own recursion appends a
step at the END; this says a step may equivalently be taken at the FRONT,
which is what lets one induction consume `chunkAcc`'s outermost digit.
-/
theorem chunkRevGen_succ_front (scale a r : Nat) :
    ∀ n : Nat,
      chunkRevGen scale a r (n + 1) =
        chunkRevGen scale (a / scale) (r * scale + a % scale) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => show (_, _) = (_, _); rw [ih]

/--
THE MACHINE'S BIG-ENDIAN FOLD, REVERSED, IS THE LITTLE-ENDIAN VALUE.

Every chunk must be a genuine base-`scale` digit (`hdig`); missing chunks
satisfy this for free, since the option shift sends them to the truncated
`0 - 1 = 0`.  The `.1` component coming back `0` is the statement that the
reversal consumed the accumulator exactly -- no digit left behind.
-/
theorem chunkRevGen_chunkAcc (store : ReadStore) (segment scale start : Nat)
    (hscale : 0 < scale) :
    ∀ (n r : Nat),
      (∀ j, j < n →
        decodeRead (store.readWord? segment (start + j)) - 1 < scale) →
      chunkRevGen scale (chunkAcc store segment scale start n) r n =
        (0, r * scale ^ n + chunkLit store segment scale start n) := by
  intro n
  induction n with
  | zero =>
      intro r _
      show (chunkAcc store segment scale start 0, r) = _
      simp [chunkAcc, chunkLit]
  | succ n ih =>
      intro r hdig
      have hdn : decodeRead (store.readWord? segment (start + n)) - 1 < scale :=
        hdig n (by omega)
      rw [chunkRevGen_succ_front]
      -- the accumulator's low digit is the last chunk read
      have hacc : chunkAcc store segment scale start (n + 1)
          = (decodeRead (store.readWord? segment (start + n)) - 1)
            + scale * chunkAcc store segment scale start n := by
        show chunkAcc store segment scale start n * scale
            + (decodeRead (store.readWord? segment (start + n)) - 1) = _
        rw [Nat.mul_comm]
        omega
      have hdiv : chunkAcc store segment scale start (n + 1) / scale
          = chunkAcc store segment scale start n := by
        rw [hacc, Nat.add_mul_div_left _ _ hscale,
          Nat.div_eq_of_lt hdn]
        omega
      have hmod : chunkAcc store segment scale start (n + 1) % scale
          = decodeRead (store.readWord? segment (start + n)) - 1 := by
        rw [hacc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hdn]
      rw [hdiv, hmod,
        ih (r * scale + (decodeRead (store.readWord? segment (start + n)) - 1))
          (fun j hj => hdig j (by omega))]
      -- reconcile the two weightings of the freshly peeled digit
      have hpow : scale ^ (n + 1) = scale * scale ^ n := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hlit : chunkLit store segment scale start (n + 1)
          = chunkLit store segment scale start n
            + (decodeRead (store.readWord? segment (start + n)) - 1)
              * scale ^ n := rfl
      have hdist : (r * scale
            + (decodeRead (store.readWord? segment (start + n)) - 1))
              * scale ^ n
          = r * (scale * scale ^ n)
            + (decodeRead (store.readWord? segment (start + n)) - 1)
              * scale ^ n := by
        rw [Nat.add_mul, Nat.mul_assoc]
      simp only [Prod.mk.injEq]
      refine ⟨trivial, ?_⟩
      rw [hlit, hpow, hdist]
      omega

/-! ## The route's decode of the same words -/

/--
THE VALUE BRIDGE.

The machine's decoded cell -- big-endian Horner fold, then read-free digit
reversal, with `chunkBad` as the `some`/`none` verdict -- is exactly what
the route's `fixedWidthNatTableMachineDecode` produces from the words read
at the route's own addresses.

Both sides are computed from `store.readWord?` at the SAME addresses, so
this is a statement about the arithmetic, not about the addressing; the
addressing is `chunkEventsAt_eq_route`
(`E1InteriorChunkFold.lean:1745`).
-/
theorem chunkFoldValue_eq_route_decode
    (store : ReadStore) (segment wordSize start : Nat) :
    ∀ n : Nat,
      (∀ j, j < n → ∀ w, store.readWord? segment (start + j) = some w →
        w.length = wordSize) →
      RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
          ((RMQ.SuccinctSpace.consecutiveWordIndices start n).map
            (fun a => store.readWord? segment a)) =
        (if chunkBad store segment start n = 0 then
          some (chunkLit store segment (2 ^ wordSize) start n)
        else none) := by
  intro n
  induction n generalizing start with
  | zero =>
      intro _
      show RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode [] = _
      simp [RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode,
        RMQ.SuccinctSpace.collectPayloadWords, chunkBad, chunkLit,
        RMQ.SuccinctSpace.bitsToNatLE]
  | succ n ih =>
      intro hwidth
      have hrest : ∀ j, j < n → ∀ w,
          store.readWord? segment (start + 1 + j) = some w →
          w.length = wordSize := by
        intro j hj w hw
        have hidx : start + 1 + j = start + (j + 1) := by omega
        exact hwidth (j + 1) (by omega) w (by rw [hidx] at hw; exact hw)
      have hlist : (RMQ.SuccinctSpace.consecutiveWordIndices start (n + 1)).map
          (fun a => store.readWord? segment a) =
            store.readWord? segment start ::
              (RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                (fun a => store.readWord? segment a) := rfl
      rw [hlist, chunkBad_succ_front, chunkLit_succ_front]
      cases hhead : store.readWord? segment start with
      | none =>
          show RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
              (none :: _) = _
          simp [RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode,
            RMQ.SuccinctSpace.collectPayloadWords]
      | some w =>
          have hw : w.length = wordSize := by
            have hidx : start + 0 = start := by omega
            exact hwidth 0 (by omega) w (by rw [hidx]; exact hhead)
          -- `cases` substituted the read into the goal, so the arithmetic
          -- facts are stated on `some w`, the form the goal now carries.
          have hnz : ¬ decodeRead (some w) = 0 := by
            simp [decodeRead]
          have hdec : decodeRead (some w) - 1
              = RMQ.SuccinctSpace.bitsToNatLE w := by
            show RMQ.WordRAM.bitsToNatLE w + 1 - 1 = _
            rw [RMQ.SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
            omega
          show RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
              (some w :: _) = _
          -- unfold one layer of the route's collector, then apply the IH
          rw [show RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
              (some w ::
                (RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                  (fun a => store.readWord? segment a)) =
            ((RMQ.SuccinctSpace.collectPayloadWords
                ((RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                  (fun a => store.readWord? segment a))).map
              (fun tail => w ++ tail)).map RMQ.SuccinctSpace.bitsToNatLE from rfl]
          cases hcoll : RMQ.SuccinctSpace.collectPayloadWords
              ((RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                (fun a => store.readWord? segment a)) with
          | none =>
              have hih := ih (start := start + 1) hrest
              rw [show RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
                  ((RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                    (fun a => store.readWord? segment a)) =
                (RMQ.SuccinctSpace.collectPayloadWords
                  ((RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                    (fun a => store.readWord? segment a))).map
                  RMQ.SuccinctSpace.bitsToNatLE from rfl, hcoll] at hih
              have hbad : ¬ chunkBad store segment (start + 1) n = 0 := by
                intro hb
                rw [hb] at hih
                simp at hih
              have hcond : ¬ ((if decodeRead (some w) = 0 then 1 else 0)
                  + chunkBad store segment (start + 1) n = 0) := by
                rw [if_neg hnz]
                omega
              show (none : Option Nat) =
                (if (if decodeRead (some w) = 0 then 1 else 0)
                    + chunkBad store segment (start + 1) n = 0 then
                  some ((decodeRead (some w) - 1)
                    + 2 ^ wordSize
                      * chunkLit store segment (2 ^ wordSize) (start + 1) n)
                else none)
              rw [if_neg hcond]
          | some tail =>
              have hih := ih (start := start + 1) hrest
              rw [show RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
                  ((RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                    (fun a => store.readWord? segment a)) =
                (RMQ.SuccinctSpace.collectPayloadWords
                  ((RMQ.SuccinctSpace.consecutiveWordIndices (start + 1) n).map
                    (fun a => store.readWord? segment a))).map
                  RMQ.SuccinctSpace.bitsToNatLE from rfl, hcoll] at hih
              have hbad : chunkBad store segment (start + 1) n = 0 := by
                match hb : chunkBad store segment (start + 1) n with
                | 0 => rfl
                | k + 1 =>
                    rw [hb] at hih
                    simp at hih
              rw [if_pos hbad] at hih
              have htail : RMQ.SuccinctSpace.bitsToNatLE tail =
                  chunkLit store segment (2 ^ wordSize) (start + 1) n := by
                simpa using hih
              have hcond : (if decodeRead (some w) = 0 then 1 else 0)
                  + chunkBad store segment (start + 1) n = 0 := by
                rw [if_neg hnz, hbad]
              show some (RMQ.SuccinctSpace.bitsToNatLE (w ++ tail)) =
                (if (if decodeRead (some w) = 0 then 1 else 0)
                    + chunkBad store segment (start + 1) n = 0 then
                  some ((decodeRead (some w) - 1)
                    + 2 ^ wordSize
                      * chunkLit store segment (2 ^ wordSize) (start + 1) n)
                else none)
              rw [if_pos hcond, bitsToNatLE_append, hw, htail, hdec]

/-! ## The form `interiorChunkFold_runsTo`'s consumers need -/

/-- Every chunk the fold reads is a legitimate base-`2 ^ wordSize` digit.
A missing chunk qualifies for free: the option shift sends it to the
truncated `0 - 1 = 0`. -/
theorem chunkDigit_lt (store : ReadStore) (segment wordSize start n : Nat)
    (hwidth : ∀ j, j < n → ∀ w, store.readWord? segment (start + j) = some w →
      w.length = wordSize) :
    ∀ j, j < n →
      decodeRead (store.readWord? segment (start + j)) - 1 < 2 ^ wordSize := by
  intro j hj
  cases hread : store.readWord? segment (start + j) with
  | none => exact Nat.pow_pos (by omega)
  | some w =>
      have hw : w.length = wordSize := hwidth j hj w hread
      have hlt : RMQ.SuccinctSpace.bitsToNatLE w < 2 ^ w.length :=
        bitsToNatLE_lt_two_pow w
      have hval : decodeRead (some w) - 1 = RMQ.SuccinctSpace.bitsToNatLE w := by
        show RMQ.WordRAM.bitsToNatLE w + 1 - 1 = _
        rw [RMQ.SuccinctSpace.WordRAMBridge.bitsToNatLE_eq]
        omega
      rw [hval, ← hw]
      exact hlt

/--
THE REVERSAL PRODUCES THE ROUTE'S LITTLE-ENDIAN VALUE.

`interiorChunkFold_runsTo` leaves `(chunkRevAt ...).2` in `cOut`; this says
that number is `chunkLit`, the little-endian value of the chunks in the
route's own weighting.
-/
theorem chunkRevAt_chunkAcc_eq_chunkLit
    (store : ReadStore) (segment wordSize start n : Nat)
    (hwidth : ∀ j, j < n → ∀ w, store.readWord? segment (start + j) = some w →
      w.length = wordSize) :
    (chunkRevAt (2 ^ wordSize)
        (chunkAcc store segment (2 ^ wordSize) start n) n).2 =
      chunkLit store segment (2 ^ wordSize) start n := by
  have hscale : 0 < 2 ^ wordSize := Nat.pow_pos (by omega)
  rw [chunkRevAt_eq_gen,
    chunkRevGen_chunkAcc store segment (2 ^ wordSize) start hscale n 0
      (chunkDigit_lt store segment wordSize start n hwidth)]
  show 0 * (2 ^ wordSize) ^ n + chunkLit store segment (2 ^ wordSize) start n
    = _
  omega

/--
THE VALUE BRIDGE IN `cOut` FORM.

The left-hand side is verbatim the `cOut` clause of
`interiorChunkFold_runsTo` (`E1InteriorChunkFold.lean:1802`) at the fold's
own machine-computed start and iteration count.  The right-hand side is
the route's decode, option-shifted the same way.  A consumer of the
simulation theorem may rewrite with this and be left with a statement
purely about the route.

The width premise is indexed at the fold's own start; it is discharged
where the fold meets a concrete `BoundedPayloadWordStore`, not here.
-/
theorem interiorChunkFold_cOut_eq_routeDecode
    (store : ReadStore)
    {segment base deadAddress entriesLen chunkCount wordSize i : Nat}
    (hcap : chunkCount ≤ 8)
    (hwidth : ∀ j, j < chunkIters entriesLen chunkCount i → ∀ w,
      store.readWord? segment
          (chunkStart base deadAddress entriesLen chunkCount i + j) = some w →
        w.length = wordSize) :
    (if chunkBad store segment
          (chunkStart base deadAddress entriesLen chunkCount i)
          (chunkIters entriesLen chunkCount i) = 0 then
        (chunkRevAt (2 ^ wordSize)
          (chunkAcc store segment (2 ^ wordSize)
            (chunkStart base deadAddress entriesLen chunkCount i)
            (chunkIters entriesLen chunkCount i))
          (chunkIters entriesLen chunkCount i)).2 + 1
      else 0) =
      (match RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
          ((chunkAddrs base deadAddress entriesLen chunkCount i).map
            (fun a => store.readWord? segment a)) with
       | none => 0
       | some v => v + 1) := by
  rw [chunkAddrs_eq_consecutive hcap,
    chunkFoldValue_eq_route_decode store segment wordSize
      (chunkStart base deadAddress entriesLen chunkCount i)
      (chunkIters entriesLen chunkCount i) hwidth,
    chunkRevAt_chunkAcc_eq_chunkLit store segment wordSize
      (chunkStart base deadAddress entriesLen chunkCount i)
      (chunkIters entriesLen chunkCount i) hwidth]
  by_cases hbad : chunkBad store segment
      (chunkStart base deadAddress entriesLen chunkCount i)
      (chunkIters entriesLen chunkCount i) = 0
  · rw [if_pos hbad, if_pos hbad]
  · rw [if_neg hbad, if_neg hbad]

/-! ## The bridge, executed

The witness store of `E1InteriorChunkFold` holds ONE-BIT chunks, so
`wordSize = 1` and the fold's `wordScale = 2` is `2 ^ 1`.  These check the
bridge by kernel computation on the same fixture whose machine run
`chunkFoldWitness_path_bothPresent` (`E1InteriorChunkFold.lean:1909`)
already pins, closing the loop between the two sides on a concrete input
rather than only in the abstract.
-/

/-- The route's decode of the witness's first cell is `some 1`:
`bitsToNatLE ([true] ++ [false]) = 1`. -/
theorem witnessRouteDecode_cell0 :
    RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
        ((chunkAddrs 10 99 3 2 0).map
          (fun a => E1InteriorChunkFold.witnessStore.readWord? 0 a)) =
      some 1 := by
  decide

/-- The machine's `cOut` on that cell is `2`, the option shift of `1`, and
it agrees with the route's decode through the bridge.  Both sides are
computed, not asserted. -/
theorem witnessCOut_agrees_routeDecode_cell0 :
    (match RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
        ((chunkAddrs 10 99 3 2 0).map
          (fun a => E1InteriorChunkFold.witnessStore.readWord? 0 a)) with
     | none => 0
     | some v => v + 1) = 2 := by
  decide

/-- The wholly-missing cell decodes to `none` on the route side, matching
the machine's `cOut = 0` at `chunkFoldWitness_path_bothMissing`.  This is
the side of the bridge a value-only check cannot see, and it is the reason
the `none` arm is proved rather than assumed. -/
theorem witnessRouteDecode_cell2 :
    RMQ.SuccinctSpace.fixedWidthNatTableMachineDecode
        ((chunkAddrs 10 99 3 2 2).map
          (fun a => E1InteriorChunkFold.witnessStore.readWord? 0 a)) =
      none := by
  decide

/-! ## The bridge is not vacuous: its premises are discharged concretely

`interiorChunkFold_cOut_eq_routeDecode` carries a width premise, and a
theorem whose premises no store satisfies would prove nothing.  The three
results below discharge that premise on `E1InteriorChunkFold.witnessStore`
and then DERIVE the machine's cell from the bridge -- landing on `2`, the
value `chunkFoldWitness_path_bothPresent` (`E1InteriorChunkFold.lean:1909`)
independently obtained by RUNNING the machine.
-/

/-- The witness store's chunks for cell `0` are one bit wide, matching
`wordScale = 2 = 2 ^ 1`. -/
theorem witnessWidth_cell0 :
    ∀ j, j < chunkIters 3 2 0 → ∀ w,
      E1InteriorChunkFold.witnessStore.readWord? 0
          (chunkStart 10 99 3 2 0 + j) = some w →
        w.length = 1 := by
  intro j hj w hw
  have hiters : chunkIters 3 2 0 = 2 := rfl
  rw [hiters] at hj
  have hcase : j = 0 ∨ j = 1 := by omega
  rcases hcase with h | h
  · subst h
    have hread : E1InteriorChunkFold.witnessStore.readWord?
        0 (chunkStart 10 99 3 2 0 + 0) = some [true] := rfl
    rw [hread] at hw
    injection hw with hw'
    subst hw'
    rfl
  · subst h
    have hread : E1InteriorChunkFold.witnessStore.readWord?
        0 (chunkStart 10 99 3 2 0 + 1) = some [false] := rfl
    rw [hread] at hw
    injection hw with hw'
    subst hw'
    rfl

/--
THE BRIDGE, INSTANTIATED AND COMPUTED.

`2` is not asserted here: the left-hand side is the `cOut` expression of
`interiorChunkFold_runsTo`, rewritten by the bridge into the route's
decode, which the kernel then evaluates.  That it lands on the same `2`
the machine run produces is the executed agreement between the two sides.
-/
theorem witnessCOut_cell0_via_bridge :
    (if chunkBad E1InteriorChunkFold.witnessStore 0
          (chunkStart 10 99 3 2 0) (chunkIters 3 2 0) = 0 then
        (chunkRevAt (2 ^ 1)
          (chunkAcc E1InteriorChunkFold.witnessStore 0 (2 ^ 1)
            (chunkStart 10 99 3 2 0) (chunkIters 3 2 0))
          (chunkIters 3 2 0)).2 + 1
      else 0) = 2 := by
  rw [interiorChunkFold_cOut_eq_routeDecode
    E1InteriorChunkFold.witnessStore (wordSize := 1) (by omega)
    witnessWidth_cell0]
  decide

end E1InteriorChunkValue
end WordRAM
end RMQ
