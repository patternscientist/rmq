# NATIVE-1 indexed binary cursor producer

Status: INCOMPLETE
Phase: CURSOR_PRODUCER_AND_CONSUMERS_CHECKED

The lead approved this distinct leaf and report on 2026-09-12. Its contract was
first frozen, before implementation, in the successor appendix of MACHINE_LEAF.md;
that history is retained. Ownership is `Native/Binary/Cursor.lean`, subordinate
`Native/Binary/Cursor/*.lean`, and this report. Binary.lean and Binary/Codec.lean
belong to another worker and must remain untouched by this leaf. The governing
proof-sprint/preflight evidence in LIMB_WORDS.md continues to apply.

| ID | Exact frozen requirement | Evidence target | Consumer | Attack | Status |
| --- | --- | --- | --- | --- | --- |
| LC-INDEX | Need actual ByteArray+offset parser + tailrecursive array fold, proved equal/refining reference StorageImage.decodeSupported, never list reference at fullnative (rest.length per scalar => quadratic and readMany non-tail). | Runtime Parser ByteArray offset -> optional value/next offset; all count/prefix loops tail recursive; no call to list reference or repeated suffix lengths | actual binary-loaded native entry | complete 837572-instruction image and malformed length | Checked producer and typed consumers; full native replay remains lead-owned |
| LC-BOUND | Needs real byte/index+count limits beforeallocation/powers and tailrecursive countloop; retain source correspondence theorem. | Remaining bytes computed from constant-time size/offset; declared scalar/word/array byte/count bounds checked before loops/slices; width/register caps before image body | supported-host loader | oversized/truncated prefix, header, cell and arrays | Checked producer and typed consumers; full native replay remains lead-owned |
| LC-JOIN | Target efficient decode equality to decodeSupported or full sound + supportedimage roundtrip/field identity; root actual API calls yourentry only. | Exact cursor/ref-parser relation, complete supported-image decoder theorem including magic/validity/no leftovers and exact code/memory fields | nativeExecutionCapstone_holds and exported entry | source mutation removes loaded/marshaled dependency | Checked producer and typed consumers; full native replay remains lead-owned |
| LC-ALLBYTES | prove actual exportedCursordecode equals reference for allbytes+limits, include earlycountguards andtailfold; optionalhostdigitlengthbound must remain compatibleexactreference or domainexplicit. | `decode limits bytes = StorageImage.decodeSupported limits bytes` for every Limits and ByteArray | final native source chain | reject extra malformed cases without silently shrinking reference acceptance | Checked producer and typed consumers; full native replay remains lead-owned |

Proposed proof-only suffix is `bytes.data.toList.drop offset`; this is never the
runtime parser input. Prefix scanning, numeric digit accumulation and counted
Array.push folds use explicit tail recursion. Word slices are bounded by the
decoded length, available bytes and declared limb count. Full decoder reuse of
`image.valid` is an explicit final semantic check, separate from the efficient
framing parser. Optional large numeric-header temporaries remain bounded by file
bytes and must not introduce non-tail recursion.

The lead owns baseline warming and final native linkage. Every compiler check
must use the negotiated one-job slot and the task-local cache. First verify the
scalar/count and list-reference relation, then the full image consumer; reserve
large native replay for the actual compiled cursor implementation.

## Approved resource clarification

On 2026-09-12 the lead confirmed that LC-BOUND includes rejecting unsupported
scalar digit counts before numeric accumulation. The final runtime must bound
count/header digit lengths from their declared caps, and bound input-length
digits from the already checked width (512 bytes at the native width cap).
This does not weaken LC-ALLBYTES: a scalar accepted by the reference already
obeys the relevant numeric constraint; digit-count monotonicity and the final
validity check justify early rejection. The initial byte-bounded parser below
is a proof stage and is not the final host resource producer.

## Concrete module/API draft

`Cursor/Core.lean` implements `Parser alpha := ByteArray -> Nat -> Option (alpha × Nat)`,
byte access, the tail prefix scanner, downward tail digit accumulation, and a
counted tail Array.push loop. Its `Correct` proposition equates the optional
value and remaining proof suffix and additionally proves start <= next <= size.
Its `decodeByteBounded_eq` is the intermediate reference equivalence.

`Cursor.lean` adds `readScalarDigits`, `readScalarLimit`, capped words/arrays and
`readBodyCapped`. A scalar digit cap is checked before `digitsAux` is entered.
Width is checked before input length, input digits are bounded by
`max 1 (limbCount width)`, and registers are bounded before code/memory parsing.
Array count and word length caps are checked before count loops. The exported
name remains exactly `BinaryCursor.decodeSupported limits bytes`; its intended
`decodeSupported_eq` has no hypotheses and compares with the identical
`StorageImage.decodeSupported limits bytes` on every byte array and every limit.

The proof strategy uses exact scalar filter identities. Numeric count caps
already present in the reference word/array readers are moved before digit
accumulation. Input-length digit filtering is implied by final image validity,
so it changes no accepted image. The slower proof-layer decoder is not called by
the exported runtime. All definitions and propositions in this section remain
unchecked until the next negotiated compiler slot; these are interface records,
not acceptance evidence.

## Development checks

The first direct Core check (`commands/cursor-core-01.json`) returned exit 1 in
15.867 seconds, within 90 seconds. It found proof presentation errors concerning
ByteArray access views, one scalar-prefix simplification, a redundant tactic,
qualified bind notation, body-composition inference, and rewriting the reference
suffix. The second check (`cursor-core-02.json`) returned exit 1 in 8.761 seconds,
within 60 seconds; only the prefix addition permutation and explicit body bind
continuations remained. Both repairs are drafted. There was no wall timeout,
full-build fallback, or surviving owned process. The slot was released to the
lead after this bounded diagnosis. Neither failed module check is final evidence
for any acceptance row.

## Checked exact producer and generated-code review

The complete Core module subsequently passed in `cursor-core-04.json`, exit 0,
16.761 seconds under 60 seconds. A preceding `cursor-core-03.json` check returned
exit 1 in 23.527 seconds because the body guard simplified to `True ∧ True`;
adding its conjunction reduction closed that presentation issue.

The capped module passed in `cursor-02.json`, exit 0, 14.988 seconds under 60
seconds, with actual C and olean output. `cursor-01.json` first returned exit 1
in 12.911 seconds due to six remaining unfoldings of the body bind combinator;
those were repaired without changing functional definitions. There were no wall
timeouts. The slot was handed directly to the Binary worker after the check.

Checked exported proposition, with no hypotheses:

```lean
BinaryCursor.decodeSupported_eq (limits : StorageImage.Limits) (bytes : ByteArray) :
  BinaryCursor.decodeSupported limits bytes = StorageImage.decodeSupported limits bytes
```

The same exported decoder now has the exact checked success characterization:

```lean
BinaryCursor.decodeSupported limits bytes = some image ↔
  bytes = image.encode ∧ image.Valid ∧ image.Supported limits
```

The composition chain is actual capped decoder -> `readBodyCapped_eq` -> exact
capped scalar/word/array filter identities -> byte cursor `Correct.result` plus
index bounds -> `decodeByteBounded_eq` -> reference `StorageImage.decodeSupported`.
The input-length digit filter follows from the returned image's actual Valid
predicate; it is neither a new assumption nor a narrower input domain. Exact
source identity and every code/memory field follow from the reference decoder's
already checked exact-byte success theorem. Unsupported encoded images are
rejected by `decodeSupported_reject_unsupported`.

The generated C was read at the actual exported decoder, scalar-cap branch,
magic check, and tail loops. The decoder checks `lean_byte_array_size` against
the file cap before calling the magic check and `readBodyCapped`. The scalar
reader checks positive count, remaining bytes and the supplied digit cap before
calling `digitsAux`. Prefix, digit and counted-array recursive branches compile
to `goto _start`. Byte access calls `lean_byte_array_fget`. The magic check
extracts its fixed five-byte slice before converting that slice to an array/list.
The exported capped module contains no call to a list reference parser, suffix
observer, `decodeByteBounded` or uncapped body parser. Proof-view functions may
exist as unused module symbols; their existence is separate from execution of
the exported call chain. This source/C inspection is evidence within the approved
compiler/runtime boundary, not a verified-compilation theorem.

Checked source snapshots:

| File | Bytes | SHA256 |
| --- | ---: | --- |
| `Cursor/Core.lean` | 24281 | `18F42ACEE5D218DA5CB6B787E7DF25C69C572C72551E3008D1106A6CFA660E28` |
| `Cursor.lean` | 10733 | `FA032A73E3CAAB84A874D736D26CA8B833CECC526BBC880BDF09AC8647E68F45` |
| Generated `Cursor/Core.c` | 56690 | `4351C57F0382D926E2892F336E765331BC48FEEABDCCF8949CBC22C5C50B9A9E` |
| Generated `Cursor.c` | 27595 | `ABBE67E4B5F1B34E35A8557A7825924439D02B3B2EC3B7A658981D3F23BDE427` |

Independent typed consumers, concrete controls and axiom inventories in
`Cursor/Checks.lean` are still queued. The lead owns linking this exact decoder
into Entry and measuring the complete 837572-instruction binary image. These
remaining checks are not claimed from the green producer alone.

## Proof digestion and proposed design decision

The conceptual change is an execution refinement of the same binary format.
The list parser remains the mathematical reference. The exported parser reads
indices in the supplied ByteArray and accumulates counted outputs in tail loops.
It accepts and returns exactly the reference image, including every original
instruction field and memory word. Earlier header rejection is justified by
constraints that every accepted image already has.

The all-byte equality theorem has no validity, support or size premises. Its
success characterization derives validity and support from the actual parser
result. The supported-image roundtrip inherits precisely `image.Valid` and
`image.Supported limits`; it does not silently restrict the mathematical format.
The final host sets concrete limits. That finite execution domain and compiler,
BigNat, generic Array, ByteArray, allocator and FFI implementation remain the
approved runtime boundary. No theorem claims physical constant-time arithmetic,
one physical byte per generic Array UInt8 slot, or verified compilation.

Proposed DD rationale: reject length/header digit counts before constructing
large Nats; bound input digits from the checked word width; keep offset-based
byte reads and tail Array.push loops so full-code loading does not repeatedly
traverse list suffixes or recurse non-tail once per instruction. Retain a
reference-equality proof rather than defining support as whatever the new parser
accepts. A repeated-list decoder and a native-only replacement without a source
refinement were rejected because neither closes the resource/source requirement.
The semantic image validation is still one explicit final pass over the loaded
bounded arrays. The skeptical next question is whether the final Entry and DLL
actually call this exported source on the full counted image and whether the
measured memory/time agrees with these algorithmic bounds; the lead owns that
remaining integration and native replay.

## Independent final consumers and controls

`cursor-checks-02.json` passed, exit 0, 9.031 seconds under 60 seconds.
`Cursor/Checks.lean` checks eight generic expected-type consumers, 21 concrete
controls, three independent sample facts, and ten axiom inventories. The generic
consumers include the actual exported all-byte equality, supported roundtrip,
exact encoded-source/validity consequence, every supported host cap, exact indexed
scalar and capped-word correspondence, the numeric scalar filter and early digit
rejection. Concrete controls cover zero/255/256 scalars, malformed prefix,
truncation, nonminimal digits, capped words, the 50-byte image, bad magic/version,
all five host caps, early oversized-digit rejection and the native 512-byte bound.

The first consumer check, `cursor-checks-01.json`, returned exit 1 in 31.985
seconds because broad scalar simplification unfolded the logarithm while its
argument still contained indexed parser expressions, plus an unreduced record
projection in one cap contradiction. The final check exposes each literal scalar
parser equation first, then rewrites the known numeral logarithm. It does not
raise recursion/heartbeat limits or use native decision. All ten final inventories
contain only `propext`, `Classical.choice` and `Quot.sound` (some use fewer).

`Cursor/Checks.lean` is 7833 bytes, SHA256
`F7B081BA8BB3A4E11FAA1AB75660D7F24613FAD1E4745FE7EDC7EA2A07F1A0A2`.
The checked production Cursor.lean and Core.lean snapshots above are unchanged.
The repository-wide required trust and native-decision scans returned zero
matches, and `git diff --check` returned exit 0; its sole line-ending notice
concerned the lead-owned identity script. No broad gate was run by this leaf:
the lead owns the broad native build and final acceptance campaign.

The lead has also reported checked Canonical, CanonicalImage, Entry, Execution,
Capstone and 34-field Contract consumers on this exact loader source. The later
42-field contract extension and full 837572-instruction native replay remain part
of the lead's active full assignment. The bounded indexed/capped parser producer
and its local consumers are complete; no full NATIVE-1 acceptance is claimed.
