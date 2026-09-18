# NATIVE-1 byte-limb producer

Status: INCOMPLETE
Phase: LIMB_PRODUCER_CHECKED

Frozen before implementation, 2026-09-12. Governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`; starting HEAD
`c8c266f987d46284382cc93c5fa8e01bd7a9ffb9`. The canonical proof-sprint skill,
completion gate and AGENTS were read; exact-ref preflight passed with all three
actual runtime RMQ skills and required `rmq-proof-sprint`.

This bounded producer owns `Native/Limbs.lean` and this report only. The lead
owns the full acceptance matrix and downstream finite-executor/run/capstone
composition. Its 31 original rows are preserved. Parallelism: the lead handles
source instantiation and native policy repairs while this leaf owns the single
scoped Lean slot.

| ID | Exact frozen requirement | Evidence needed | Consumer | Attack | Status |
| --- | --- | --- | --- | --- | --- |
| LW-STORAGE | actual little-endian fixed-width limbs as Array UInt64 (or Array UInt8 if this materially simplifies certified binary reuse; communicate choice first), declared wordWidth dynamic, encode/decode exact for every n<2^w, encode length/rounded payload bits and canonical padding, injectivity | Array UInt8 representation, exact roundtrip under value bound, byte count ceil(w/8), padding <8, canonical decode injectivity | actual checked executor and binary loader | width 0, 168/176-bit values, nonzero padding | Open |
| LW-OPS | define checked operations matching ALL ten PackedWordRAM.ArithOp.eval operations incl Nat division/remainder/shifts/bit ops and comparison/address conversion, with explicit safety/fault predicates and exact successful decode | Existing source actually names the type Arithmetic; all-constructor theorem uses Arithmetic.eval, exact safety clauses and operation-specific failures | instruction simulation | zero divisor, underflow, oversized shift, overflow, malformed storage | Open |
| LW-NOCACHE | Strong preference concrete bounded limb storage with NO cached Nat answer/data field; decoding into temporary Nat and re-encoding is acceptable within approved compiler/BigNat trust boundary ONLY with honest conversion/internal-temporary overhead and no physical constant-time claim | definition body is Array UInt8 only; temporary decoded Nat is recomputed from cells | compiled Lean computational path | replace bytes while retaining metadata: decoder must change | Open |
| LW-CHECKS | Direct pinned compiler, -j1, task-local outputs with no mutable shared links | bounded module check, exact-type and axiom inventory; narrow trust scan and diff check | lead final certification | source mismatch and hidden assumptions reviewed by lead | Open |

Chosen signature: namespace `RMQ.SuccinctFinal.PackedNative.LimbWord`, `Word :=
Array UInt8`; `encode width value : Word`, `decode : Word -> Nat`, `Canonical
width word` requires the exact byte count and decoded value below `2^width`.
Checked arithmetic takes width, existing `Arithmetic`, and two byte words,
and returns `Except WordFault Word`. Canonical checks precede operand checks;
subtraction underflow, zero divisors and oversized shifts are rejected before
evaluation. A final result-width check rejects overflow. Comparison and address
conversion use the same decoded operands; signed input conversion rejects
negative values instead of wrapping them. The full reference is the total Nat
interpreter, so failure equality is claimed only for the declared checked domain.

Byte limbs permit exact reuse by serialization. Runtime objects and temporary
BigNat decoding/arithmetic allocations are additional storage and work beyond
the numeric payload. This is not a physical constant-time multiprecision claim.

Verification plan: only the new module and its independent typed consumers
during development, under the installed Lean 4.22 compiler and the existing
task-local import cache. Full aggregate and public claim certification remain
owned by the lead/coordinator; this leaf must not launch them.

## Checked producer evidence

The bounded LW producer now checks. The full NATIVE-1 acceptance rows remain
open until the lead composes these bytes and operations into the actual loaded
machine, canonical run and native capstone. The lead explicitly redirected this
worker on 2026-09-12 to that machine producer after finishing this evidence.

| ID | Checked evidence | Local result and remaining global consumer |
| --- | --- | --- |
| LW-STORAGE | `decode_encode width value (h : value < 2^width)` concludes `decode (encode width value) = value`. `encode_size` concludes size `(width+7)/8`. `encode_decode` concludes exact byte-array restoration for every array of that size, including malformed-padding arrays. `encode_injective` has both bounded-value premises; `decode_injective` has both exact-size premises. `canonical_padding` concludes `decode word / 2^width = 0` from Canonical. `encoded_payload_bits` bounds allocated byte bits between width and width+7. | Local checked; whole allocation identity consumed by lead's binary/machine join remains open. |
| LW-OPS | `checkedArithmetic_accepts_iff` concludes `(exists result, checkedArithmetic width op x y = .ok result) iff Canonical width x and Canonical width y and ArithmeticSafe width op (decode x) (decode y)`. `ArithmeticSafe` is precisely result bound, no subtraction underflow, positive div/mod denominator, and shift count below width. `checkedArithmetic_success` additionally gives Canonical result and `decode result = op.eval (decode x) (decode y)`. `arithmeticSafe_of_instructionSafe` consumes the actual source `Instruction.Safe`, not a parallel assumption label. All three comparisons and USize address/signed conversion have successful-decode theorems. | Local checked for every Arithmetic constructor and every width; lead must preserve these premises over the full run. |
| LW-NOCACHE | `Word := Array UInt8`, `decode word := decodeList word.toList`; `checkedArithmetic` calls `checkedNatArithmetic` on those decoded bytes. Stored Word contains no Nat or proof field. `encodeList_getElem` proves byte i is `UInt8.ofNat (value / 256^i)`; this fixes little-endian order. | Local checked; source-generated C is produced, final native linking remains lead-owned. |
| LW-CHECKS | `Limbs.lean` compiled with generated C, 13.280 seconds. `Limbs/Checks.lean` checked, 12.474 seconds, independently spelled arithmetic fields, 29 concrete checks, 14 declaration inventories. | Local pass, standard axioms only. Full aggregate intentionally not run by this leaf. |

Exact core source chain: `Word` byte array -> `decodeList` positional base-256
decode -> `checkedNatArithmetic` operand guards -> original
`PackedWordRAM.Arithmetic.eval` -> width guard -> `encode` byte array. Guard
order is explicit in the computational definition. A zero divisor and oversized
shift return their errors before arithmetic evaluation. Corrupt padding/length
returns `malformedWord` before operation dispatch. Successful subtraction is
untruncated because its underflow guard is proved false. Other reference Nat
results, including bit operations and division/remainder, are used directly.

The exact operation signature consumed by the next machine is:

```lean
checkedArithmetic_of_safe (width : Nat) (op : Arithmetic) (x y : Word)
    (hx : Canonical width x) (hy : Canonical width y)
    (h : ArithmeticSafe width op (decode x) (decode y)) :
  checkedArithmetic width op x y =
    .ok (encode width (op.eval (decode x) (decode y)))
```

`checkedArithmetic_encode_of_safe` additionally supplies the same statement for
encoded reference Nat operands, under both operand bounds and the exact source
safety clauses. `checkedComparison_of_canonical` requires positive width; a
zero-width word can represent zero only, and the unrestricted success theorem
still describes exact behavior for width zero. `checkedAddress_success` states
Canonical input, exact `address.toNat = decode word`, and `address.toNat < limit`.
Its executable guard also requires `decode word < USize.size`. This host guard
does not alter the abstract encode/decode/arithmetic domains. `checkedInt_success`
states nonnegative input, Canonical result and exact equality of the decoded Nat
cast to Int with the original signed input.

Anti-vacuity/boundary checks in `Limbs/Checks.lean` include all ten arithmetic
constructors with independent small integer results, all three comparisons,
168/176-bit roundtrips, exact 21/22-byte lengths, width-zero empty storage,
nonzero high padding, malformed empty storage, overflow, underflow, both zero
divisors, both oversized shifts, exclusive address limit, negative signed input,
signed overflow and largest accepted byte. These are kernel-checked examples;
they do not claim a new full native mutation campaign. The independently stated
success consumer explicitly includes every safety clause rather than merely
accepting `ArithmeticSafe` as an unnamed opaque package.

## Exact checks and source identity

All commands ran on this Windows worktree, starting HEAD
`c8c266f987d46284382cc93c5fa8e01bd7a9ffb9`, against uncommitted owned sources.
The direct pinned executable was
`C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe`, `-j 1`;
LEAN_PATH was this worktree's `.lake/build/lib/lean`. The existing owned-process
wrapper preserved stdout, stderr, exit and duration under a 120-second deadline.
No timeout occurred and no overlapping Lean command was launched. The slot was
released to the lead after the final checks.

| Receipt under `commands/` | Result | Meaning |
| --- | --- | --- |
| `limbs-01.json` | exit 1, 9.585s | Two local proof-script sequencing errors; repaired. |
| `limbs-02.json` | exit 1, 14.597s | Unavailable `by_contra` tactic; replaced with direct constructive contradiction facts. |
| `limbs-03.json` | exit 1, 14.334s | Needed let reduction before final conditional split; repaired. |
| `limbs-04.json` | exit 0, 13.280s | Final module and emitted C. |
| `limbs-checks-01.json` | exit 1, 10.042s | Except equality has no automatic Decidable instance; concrete examples changed to definitional equality proofs. |
| `limbs-checks-02.json` | exit 0, 12.474s | Final independent types, 29 concrete cases, 14 axiom inventories. |

The 14 inventories contain only `propext`, `Quot.sound`, `Classical.choice`.
The narrow prescribed trust/native-decision scan returned exit 1 with zero
matches. The owned-path working diff check returned zero. Files remain
uncommitted for lead integration, so committed-range/policy certification is
lead-owned and no claim of final commit certification is made here.

Source snapshots after the final checks:

- `RMQ/Core/WordRAM/Native/Limbs.lean`: 15313 bytes,
  SHA256 `06D057D0DE50E263E701D2D5FEA1A4B0E1F6C3DD9A6BFDB6F2F9EDE71A7803F1`.
- `RMQ/Core/WordRAM/Native/Limbs/Checks.lean`: 5602 bytes,
  SHA256 `C78560DBEB2076F12A5EFBBB3E9CF9389387CACCF7AB9A3F8C6B3B16EA3E643A`.

## Proof digestion and proposed design rationale

Conceptually, a word is now a fixed number of byte values. The source Nat
operations survive only as temporary computations read from those bytes. In
plain English, a successful operation cannot quietly wrap, truncate, divide by
zero, or apply a prohibited shift: it returns exactly the reference result and
the result fits the declared width. This statement is uniform in width and
therefore includes the 168/176-bit fixtures.

Live assumptions are exact canonical byte length/padding, source arithmetic
safety for the successful forward theorem, and separate finite-host bounds for
USize conversion. Lean kernel proofs establish these propositions; generated C,
the Lean compiler/runtime and external FFI remain the route's documented trusted
translation boundary. No claim is made that byte decoding, BigNat operations,
list temporaries, array headers, allocation or deallocation consume one physical
constant-time instruction. `Array UInt8` is Lean's array of finite byte values;
the theorem does not claim that the native array reserves exactly one physical
byte per element. Array slots, boxing or tagged values and headers are runtime
representation overhead beyond the proved numeric-byte capacity. The named
downstream consumer is the checked limb
instruction/full-run simulation in `Native/Machine.lean`, then the canonical
PQ1 execution capstone. A skeptical graduate student should next ask whether
that actual machine always reads these counted bytes and invokes these exact
operations; the lead assigned that producer as the next step.

Proposed DD entry for the lead's shared ledger: choose little-endian UInt8 arrays
over UInt64 arrays to reuse the exact binary byte storage without another packing
adapter. Keep no cached Nat value or proof-carried answer. Prove the canonical
representation and checked operations in Lean, allowing temporary Nat conversion
within the approved Lean-to-C route. The rejected alternative was a Nat-array
word labeled as finite without actual finite limbs. Consequences: numeric
payload width rounds to a whole byte by fewer than eight bits, while runtime
container and temporary allocations remain separate; full program/store/run
composition and marshaling still require the downstream proofs.
