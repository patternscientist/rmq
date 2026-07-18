import RMQ.Core.WordRAM.E1RankBridge
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedSameBlockTrace

/-!
# E1 amended machine: charged fringe fold bridge lemmas (M3d-1a)

Arithmetic bridges between the charged chunked fringe fold
(`bpFringeChunkFoldComputationFrom`, `ChargedFringeTrace.lean`, consumed by
BOTH arms of the close/LCA dispatcher after B6) and the E1 machine's
constant-form register arithmetic.

The fringe fold differs from the rank fold of `E1RankBridge.lean` in one
structural respect that drives this whole module: its window is the FOUR
payload words of `localBPWindowBits`, not a single machine word.  The decoded
window therefore does NOT fit in one modeled register, and the machine may
not hold `bitsToNatLE window` at all (REQ-E1-02 / INV-ADDRESS-WIDTH).

The resolution is a fixed-stride four-register representation:

    windowRegsValue L R0 R1 R2 R3 = R0 + 2^L * (R1 + 2^L * (R2 + 2^L * R3))

with `L` the modeled word width, each `Ri < 2 ^ L` the decode of one payload
word.  This is exact whenever every window word except possibly the LAST
present one has length exactly `L` — which is the shape of
`chunkPayloadWords`, so it is a route-side fact, discharged at canonical
instantiation (the same discipline the dense select leg uses for `hlen`).

Against that representation the fold's per-chunk advance `/ 2 ^ c` becomes a
four-register shift using only the per-shape CONSTANTS `2 ^ c` and
`2 ^ (L - c)`, so no variable-width shift is needed and the ISA's
constant-only `mulConst`/`divConst` suffice:

    R0' = R0 / 2^c + (R1 % 2^c) * 2^(L-c)
    R1' = R1 / 2^c + (R2 % 2^c) * 2^(L-c)
    R2' = R2 / 2^c + (R3 % 2^c) * 2^(L-c)
    R3' = R3 / 2^c

and the chunk value the fold reads is simply `R0 % 2^c`.

Also here: the machine's truncated-subtraction forms of the fold's chunk
start/end offsets, which are what the slot address
`bpFringeChunkSlot c v a b` is built from.

Nothing here mentions a concrete program; the fringe fold block and its
`RunsTo` simulation live in `RMQ.Core.WordRAM.E1FringeFoldBlock`.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/-! ## Little-endian concatenation -/

/-- Decoding a concatenation splits at the first list's length. -/
theorem bitsToNatLE_append :
    forall (a b : List Bool),
      bitsToNatLE (a ++ b) = bitsToNatLE a + 2 ^ a.length * bitsToNatLE b
  | [], b => by simp [bitsToNatLE_nil]
  | x :: rest, b => by
      have ih := bitsToNatLE_append rest b
      show bitToNat x + 2 * bitsToNatLE (rest ++ b) =
        bitToNat x + 2 * bitsToNatLE rest +
          2 ^ (rest.length + 1) * bitsToNatLE b
      have hp : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
        rw [Nat.pow_succ]
        omega
      rw [ih, hp, Nat.mul_assoc]
      omega

/-! ## The chunk width never exceeds the modeled word width -/

/--
A fringe chunk always fits inside one modeled machine word, at every size.

This is the side condition every four-register shift below needs (`c <= L`),
and it is unconditional: `bpFringeChunkBits m = Nat.log2 m / 8 + 1` while
`machineWordBits m = Nat.log2 m + 1`.  So the machine never has to shift by
more than a word, and `2 ^ (L - c)` is a genuine per-shape constant.
-/
theorem bpFringeChunkBits_le_machineWordBits (m : Nat) :
    bpFringeChunkBits m <= SuccinctRank.machineWordBits m := by
  unfold bpFringeChunkBits SuccinctRank.machineWordBits
  omega

/-! ## The fixed-stride four-register window representation -/

/--
Value of the machine's four window registers at stride `L` (Horner form).
This is the number the fold's `window` decodes to, provided every window word
except possibly the last present one has length exactly `L`.
-/
def windowRegsValue (L R0 R1 R2 R3 : Nat) : Nat :=
  R0 + 2 ^ L * (R1 + 2 ^ L * (R2 + 2 ^ L * R3))

/-- The four-register representation is exact for a four-word window whose
first three words are full-width. -/
theorem windowRegsValue_eq_bitsToNatLE
    {L : Nat} {w0 w1 w2 w3 : List Bool}
    (h0 : w0.length = L) (h1 : w1.length = L) (h2 : w2.length = L) :
    bitsToNatLE (w0 ++ w1 ++ w2 ++ w3) =
      windowRegsValue L (bitsToNatLE w0) (bitsToNatLE w1)
        (bitsToNatLE w2) (bitsToNatLE w3) := by
  unfold windowRegsValue
  rw [bitsToNatLE_append, bitsToNatLE_append, bitsToNatLE_append]
  simp only [List.length_append, h0, h1, h2]
  have e2 : 2 ^ (L + L) = 2 ^ L * 2 ^ L := by rw [Nat.pow_add]
  have e3 : 2 ^ (L + L + L) = 2 ^ L * (2 ^ L * 2 ^ L) := by
    rw [Nat.pow_add, Nat.pow_add, Nat.mul_assoc]
  rw [e2, e3]
  generalize (2 : Nat) ^ L = P
  simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Splitting a division by `2 ^ c` across a stride-`L` boundary. -/
theorem add_pow_div_pow {L c : Nat} (hc : c <= L) (A B : Nat) :
    (A + 2 ^ L * B) / 2 ^ c = A / 2 ^ c + 2 ^ (L - c) * B := by
  have hpow : 2 ^ L = 2 ^ c * 2 ^ (L - c) := by
    rw [<- Nat.pow_add]
    congr 1
    omega
  have hpos : 0 < 2 ^ c := Nat.pow_pos (by omega)
  have hdm := Nat.div_add_mod A (2 ^ c)
  have hlt : A % 2 ^ c < 2 ^ c := Nat.mod_lt _ hpos
  have hrewrite :
      A + 2 ^ L * B =
        2 ^ c * (A / 2 ^ c + 2 ^ (L - c) * B) + A % 2 ^ c := by
    have hexp :
        2 ^ c * (A / 2 ^ c + 2 ^ (L - c) * B) =
          2 ^ c * (A / 2 ^ c) + 2 ^ c * 2 ^ (L - c) * B := by
      rw [Nat.mul_add, Nat.mul_assoc]
    rw [hexp, <- hpow]
    omega
  rw [hrewrite, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt]
  omega

/-- A stride-`L` tail contributes nothing below `2 ^ c`. -/
theorem add_pow_mod_pow {L c : Nat} (hc : c <= L) (A B : Nat) :
    (A + 2 ^ L * B) % 2 ^ c = A % 2 ^ c := by
  have hpow : 2 ^ L = 2 ^ c * 2 ^ (L - c) := by
    rw [<- Nat.pow_add]
    congr 1
    omega
  rw [hpow, Nat.mul_assoc, Nat.mul_comm (2 ^ c), Nat.add_mul_mod_self_right]

/-- One Horner level of the constant-stride shift. -/
theorem horner_shift {L c : Nat} (hc : c <= L) (A B : Nat) :
    (A + 2 ^ L * B) / 2 ^ c =
      (A / 2 ^ c + B % 2 ^ c * 2 ^ (L - c)) + 2 ^ L * (B / 2 ^ c) := by
  have hpow : 2 ^ L = 2 ^ c * 2 ^ (L - c) := by
    rw [<- Nat.pow_add]
    congr 1
    omega
  have hdm := Nat.div_add_mod B (2 ^ c)
  have hsplit : 2 ^ (L - c) * B =
      2 ^ L * (B / 2 ^ c) + B % 2 ^ c * 2 ^ (L - c) := by
    rw [hpow]
    calc 2 ^ (L - c) * B
        = 2 ^ (L - c) * (2 ^ c * (B / 2 ^ c) + B % 2 ^ c) := by rw [hdm]
      _ = 2 ^ c * 2 ^ (L - c) * (B / 2 ^ c) + B % 2 ^ c * 2 ^ (L - c) := by
          simp [Nat.add_mul, Nat.mul_comm, Nat.mul_assoc,
            Nat.mul_left_comm]
  rw [add_pow_div_pow hc, hsplit]
  omega

/--
The machine's four-register shift computes exactly the fold's per-chunk
advance `/ 2 ^ c`, using only the per-shape constants `2 ^ c` and
`2 ^ (L - c)`.
-/
theorem windowRegsValue_shift {L c : Nat} (hc : c <= L) (R0 R1 R2 R3 : Nat) :
    windowRegsValue L R0 R1 R2 R3 / 2 ^ c =
      windowRegsValue L
        (R0 / 2 ^ c + R1 % 2 ^ c * 2 ^ (L - c))
        (R1 / 2 ^ c + R2 % 2 ^ c * 2 ^ (L - c))
        (R2 / 2 ^ c + R3 % 2 ^ c * 2 ^ (L - c))
        (R3 / 2 ^ c) := by
  unfold windowRegsValue
  rw [horner_shift hc, add_pow_mod_pow hc, horner_shift hc,
    add_pow_mod_pow hc, horner_shift hc]

/-- The chunk value the fold reads is the low `c` bits of the first
register. -/
theorem windowRegsValue_mod {L c : Nat} (hc : c <= L) (R0 R1 R2 R3 : Nat) :
    windowRegsValue L R0 R1 R2 R3 % 2 ^ c = R0 % 2 ^ c := by
  unfold windowRegsValue
  exact add_pow_mod_pow hc _ _

/--
The fold's chunk value at chunk `j`, read off the machine's four-register
window state after `j` shifts.
-/
theorem bpFringeWindowChunkValue_eq_windowRegs
    {L c : Nat} (hc : c <= L) {w0 w1 w2 w3 : List Bool}
    (R0 R1 R2 R3 : Nat) (j : Nat)
    (hstate :
      windowRegsValue L R0 R1 R2 R3 =
        bitsToNatLE (w0 ++ w1 ++ w2 ++ w3) / 2 ^ (j * c)) :
    bpFringeWindowChunkValue c (w0 ++ w1 ++ w2 ++ w3) j = R0 % 2 ^ c := by
  rw [bpFringeWindowChunkValue_eq_div_mod, <- hstate,
    windowRegsValue_mod hc]

/-! ## Machine forms of the chunk start/end offsets -/

/--
`Nat.max relLo (j * c) - j * c` is a plain truncated subtraction: the machine
never needs a `max` instruction here.
-/
theorem max_sub_eq_sub (a b : Nat) : Nat.max a b - b = a - b := by
  rcases Nat.le_total a b with h | h
  · have : Nat.max a b = b := Nat.max_eq_right h
    omega
  · have : Nat.max a b = a := Nat.max_eq_left h
    omega

/-- The chunk start offset in the machine's truncated-subtraction form. -/
theorem bpFringeChunkStartOff_eq_sub (c relLo j : Nat) :
    bpFringeChunkStartOff c relLo j =
      c - (c - (relLo - j * c)) := by
  unfold bpFringeChunkStartOff
  rw [max_sub_eq_sub, nat_min_eq_sub_sub]

/-- The chunk end offset in the machine's truncated-subtraction form. -/
theorem bpFringeChunkEndOff_eq_sub (c relHi j : Nat) :
    bpFringeChunkEndOff c relHi j =
      ((relHi + 1) - ((relHi + 1) - (j * c + c))) - j * c := by
  unfold bpFringeChunkEndOff
  rw [nat_min_eq_sub_sub]
  have hmul : (j + 1) * c = j * c + c := Nat.succ_mul j c
  rw [hmul]

/-! ## Machine form of the decoded chunk step -/

/--
The fold's decoded chunk step, written entirely in the machine's constant
div/mul/sub vocabulary.  `e` is the machine's decoded entry register
(`decodeRead - 1`, i.e. the fold's `(entry?.map bitsToNatLE).getD 0`).
-/
theorem bpFringeChunkStepDecoded_eq_machine
    (c relLo relHi j : Nat) (st : Nat × Option (Nat × Nat))
    (entry? : Option Nat) :
    bpFringeChunkStepDecoded c relLo relHi j st entry? =
      (st.1 + (entry?.getD 0) / ((c + 1) * (2 * c + 2)) - c,
        bpFringeMergeCand st.2
          (if bpFringeChunkStartOff c relLo j <
              bpFringeChunkEndOff c relHi j then
            some
              (st.1 +
                ((entry?.getD 0) / (c + 1) -
                  (entry?.getD 0) / (c + 1) / (2 * c + 2) * (2 * c + 2)) - c,
                j * c +
                  ((entry?.getD 0) - (entry?.getD 0) / (c + 1) * (c + 1)))
          else none)) := by
  unfold bpFringeChunkStepDecoded
  rw [<- nat_mod_eq_sub_div_mul, <- nat_mod_eq_sub_div_mul]

end SuccinctClose

end RMQ
