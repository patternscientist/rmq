Status: CANDIDATE_COMPLETE (owned binary proof leaf); C++ execution evidence OPEN
Phase: BINARY_PROOFS_AND_CONTROLS_CHECKED

# NATIVE-1 exact binary storage-image producer

This requirement freeze precedes Binary source edits. Owner: native_policy,
now assigned `RMQ/Core/WordRAM/Native/Binary.lean`, its `Binary/` modules and
this evidence file only. No commits or shared ledger edits. Existing canonical
rmq-proof-sprint preflight passed at governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`; current starting HEAD remains
`c8c266f987d46284382cc93c5fa8e01bd7a9ffb9`. Other agents own Limbs, Machine,
canonical composition, ABI and replay work. Their edits must be preserved.

## Frozen leaf matrix

| ID | Exact assigned requirement | Intended exact proposition / consumer | Challenge and planned evidence | Status |
| --- | --- | --- | --- | --- |
| BINARY-IMAGE | Full NATIVE-1 needs actual versioned binary image for SAME code/memory fed to limb machine. | `StorageImage` stores `LimbMachine.Code` and `LimbMachine.Memory` directly; whole-image decode/encode equality preserves each array cell. | Mutated code field, memory byte and shape must change encoding or be rejected; root's native entry consumes these exact fields. | OPEN |
| BINARY-ROUNDTRIP | Prove complete canonical encode/decode roundtrip and encode injectivity, exact code/word cells and overhead formula; decoder bounded by supplied bytes and rejects truncation/malformed version/tag/width/length/padding. | `StorageImage.decode_encode (image) (h : Valid image) : decode (encode image) = some image`; injectivity, exact projections, validity of every accepted image and exact length decomposition. | Prefix/suffix, bad magic/version, nonminimal scalar, impossible lengths, high padding, instruction tag and leftover bytes. | OPEN |
| BINARY-ALLN | A generic Option codec roundtrip helper alone is NOT endpoint. Need actual Image codec and field-byte correspondence, abstract all-size (no fixed u64 header limitation) separate finite native support predicate. | All header Nats use minimal little-endian byte digits and unbounded unary byte-length framing; no fixed header word. Exact actual image theorem consumes all nested codecs. | Header values beyond u64; zero/positive widths; no host limit in abstract canonical theorem. | OPEN |
| BINARY-BOUNDS | Native parser must test supported width/count/file limits before expensive powers/allocations; abstract roundtrip cannot silently narrow mathematical sizes tohost. | Bounded list parsing tests count against remaining bytes before iteration; native support layer checks explicit caps before body loops. | Hostile width/count values rejected before allocation and canonical power checks; no fixed hardware claim for universal theorem. | OPEN |
| BINARY-INITIAL | Add explicit `inputLength : Nat` to StorageImage header as public r2 initializer (canonical xs.length), alongside width/registerCount/code/memory. | Actual image header and codec preserve `inputLength`; no derivation from memory[0]. | Corrupt first memory cell must not change header inputLength. Root initializes r2 from this header. | OPEN |
| BINARY-VERIFY | Draft while waiting; request slot before tests. | One-job narrow Lean checks and independent exact typed consumers after Machine's slot is released. | No concurrent heavy Lean process; recorded source hashes, deadlines, output and axiom inventory. | OPEN |

Format decision, before implementation: five bytes `52 4d 51 4e 01` (hex,
ASCII RMQN followed by version1); then width, inputLength and registerCount
scalars; then code as a length-framed array of length-framed instruction-field
arrays, and memory as a length-framed word array. Each Word is its exact
little-endian UInt8 array preceded by its byte-length scalar. A scalar value
uses `k = value.log2 / 8 + 1` minimal little-endian bytes and the prefix of k
marker bytes1 followed by delimiter0, then its k digits. Thus a scalar uses
`2*k+1` bytes and supports all Nats. Redundant word-length framing is explicit
file overhead, separate from numeric payload bits and byte-rounding overhead.
No alternate instruction or memory representation is introduced.

Planned public types in `RMQ.SuccinctFinal.PackedNative`:

```lean
structure StorageImage where
  width : Nat
  inputLength : Nat
  registerCount : Nat
  code : LimbMachine.Code
  memory : LimbMachine.Memory

StorageImage.encode : StorageImage → ByteArray
StorageImage.decode : ByteArray → Option StorageImage
StorageImage.Valid : StorageImage → Prop
StorageImage.decode_encode (image : StorageImage) (h : image.Valid) :
  StorageImage.decode (StorageImage.encode image) = some image
```

The validity domain requires positive width, representable initializer/scalar
metadata, canonical word lengths/high padding and valid primitive instruction
tags/shapes. It does not assert that an arbitrary image was built from a
canonical RMQ input or that its mutable memory has correct RMQ values. The
root's canonical producer supplies that separate construction theorem.

Inherited obligations local to this producer are exact store identity,
validation reach, all-size domain, category separation, public composition and
non-vacuous malformed-input rejection. Machine execution/value dependence is
consumed downstream, not claimed by the codec alone. Full native acceptance
remains with the lead's original frozen 31-row matrix.

## Evidence and proof digestion

The actual Image implementation and its all-size, exact-byte, validation and
storage-accounting proofs are checked. All 37 independent public consumers and
concrete controls now pass. The efficient Cursor producer is separately checked
by the machine worker; native integration and final acceptance remain assigned
to the lead. The original matrix above is retained as the pre-edit requirement
freeze; the disposition below records current evidence without rewriting that
historical freeze.

### Approved framing and efficient-parser decomposition

The lead approved the complete framing above, including the redundant per-word
byte-length scalar, and confirmed that `inputLength` is an independent header
initializer rather than a value read from memory[0]. It also identified the
reference list parser's repeated suffix-length traversals and non-tail array
recursion as unsuitable for the complete native fixture. No full native test
will use that reference parser. By explicit lead assignment, the machine worker
now owns the independent `Binary/Cursor.lean` ByteArray/cursor and tail-fold
producer; this agent retains `Binary.lean` and `Binary/Codec.lean`. The native
entry must call that efficient producer and consume its checked refinement to
the image reference. This is a representation/algorithm refinement within the
approved format, not a new proof toolchain or weaker serialized-image target.

The reference Codec module has checked forward and converse scalar, Word and
array framing theorems, plus cap-to-reference parser refinement. The successful
third narrow check took 8.972 seconds and emitted only two unused-simp-argument
warnings. Earlier attempts exposed ordinary Option bind simplification and
dependent-equality name substitution errors; these were repaired without
changing the format or any target. Logs are retained at
`.lake/native1/policy/binary-codec-02.log` and `binary-codec-03.log`; subsequent
checks use the owned 120-second wrapper in `.lake/native1/binary/check.ps1`
with source hashes and complete stdout/stderr receipts. The first Codec check
failed after 7.712 seconds, before emitting an object; it is not verification
evidence. No timeout or unchanged expensive retry occurred.

The actual Image draft adds complete record encoding, exact field projections,
canonical validity, exact consumed-byte reconstruction, strict whole-input
decoding, proper-truncation rejection, raw/supported decoder compatibility,
early header/count/word-byte limits, and explicit framing/rounded-byte/numeric
bit accounting. The complete Image check below discharged those declarations.

### Complete Image check

The actual `Binary.lean` Image module checked successfully in **11.458
seconds** under an owned 120-second deadline. Receipt:
`.lake/native1/binary/binary-image-02.json`. This is a full Image proof,
including both raw and host-supported reference decoders. The first Image
attempt exited1 after49.829 seconds: routine Bool/List/Array simplification
issues and a broad-simp heartbeat limit in the file-length calculation. The
repair restricted rewriting and proved the arithmetic after structural
decomposition; no heartbeat or wall-time limit was increased. Its complete
failure receipt remains `binary-image-01.json`.

Checked conclusions include:

```lean
StorageImage.decode_encode (image : StorageImage) (h : image.Valid) :
  StorageImage.decode image.encode = some image

StorageImage.encode_injective (x y : StorageImage) (hx : x.Valid) (hy : y.Valid)
  (h : x.encode = y.encode) : x = y

StorageImage.decode_iff (bytes : ByteArray) (image : StorageImage) :
  StorageImage.decode bytes = some image ↔ bytes = image.encode ∧ image.Valid

StorageImage.decode_truncated (image : StorageImage) (initial suffix : List UInt8)
  (h : initial ++ suffix = image.encodeList) (hn : suffix ≠ []) :
  StorageImage.decode ⟨initial.toArray⟩ = none

StorageImage.decodeSupported_encode (limits : StorageImage.Limits) (image : StorageImage)
  (hv : image.Valid) (hs : image.Supported limits) :
  StorageImage.decodeSupported limits image.encode = some image

StorageImage.decodeSupported_refines (limits : StorageImage.Limits)
  (bytes : ByteArray) (image : StorageImage)
  (h : StorageImage.decodeSupported limits bytes = some image) :
  StorageImage.decode bytes = some image

StorageImage.encode_size (image : StorageImage) :
  image.encode.size = image.framingBytes + image.storedByteCount

StorageImage.encoded_bit_accounting (image : StorageImage) (h : image.Valid) :
  8 * image.encode.size = image.wordCount * image.width +
    image.wordCount * (8 * LimbWord.limbCount image.width - image.width) +
    8 * image.framingBytes
```

`decode_iff` is a strong field/byte identity statement: every accepted byte
array equals the encoder of the loaded Image, which also satisfies the
explicit validation predicate. `decoded_fields` separately projects all five
fields, including independent header inputLength and the exact nested
Machine.Code/Machine.Memory arrays. `fromReference_valid` accepts the
machine's actual `encodeCode width program` and `encodeMemory width memory`,
with ordinary positive-width/representable-header/static-code-fit/memory-fit
premises. It does not hide a second code or store construction.

The valid-image proposition is checked equivalent to positive width,
inputLength/registerCount below2^width, every instruction row containing at
most5 canonical Word cells and decoding through the real primitive parser,
and every memory Word canonical. Word canonical means exactly the rounded
byte length and numeric value below2^width, so zero high-padding is explicit.
The executable validator uses bit-length comparison instead of allocating
2^width for a hostile header; its equivalence to that numeric proposition is
proved. The supported decoder checks file size first, width/register caps
before body parsing, then each instruction/memory/field/word-length cap before
its loop or slice.

`Binary/Checks.lean` now contains independently stated consumer types for all
of these propositions, an expanded validity consumer (not only the mutable
Valid name), and a manually specified35-byte golden image. Small controls
cover176-bit words, header scalars beyond128 bits, scalar framing errors,
tag/version/magic/width/length/padding defects, trailing data and all host
limits. These consumer/control declarations await their own scheduled check.
Additional proof-only strengthening gives raw framing injectivity even before
semantic validation and explicitly proves the minimal scalar digit count.
Those additions passed the final Codec and Image checks below. They do not
change any computational encoding/decoding function.

### Final producer recheck and independent consumer preparation

The final Codec check passed in **5.376 seconds**, and the final complete Image
check passed in **5.497 seconds**, using the same owned 120-second wrapper.
Receipts are `binary-codec-final.json` and `binary-image-final.json` under
`.lake/native1/binary`. Codec emitted no diagnostics. Image emitted only three
unused simp-argument warnings. Neither command timed out or exceeded its output
limit. The source hashes pinned by both receipts are:

- `Binary/Codec.lean`: `E46F05148BB2F4D1D25C848EC804B0E2E0881EFB536F988A90AB9CB7371C11F7`.
- `Binary.lean`: `C50741D0A9AED1797919F405E8F7440410C0CD13DD2B9F299D0E6AB5E959AE16`.
- `Limbs.lean`: `06D057D0DE50E263E701D2D5FEA1A4B0E1F6C3DD9A6BFDB6F2F9EDE71A7803F1`.
- `Machine.lean`: `F5286E6B52A5C5A73571BBF831E7CA9C5D731F7F5998F3ABA724E17F7AB94B3D`.

The strengthened checked propositions are
`raw_encode_injective (x y : StorageImage) (h : x.encode = y.encode) : x = y`
without any semantic-validity premise, and
`digitCount_minimal (value : Nat) (h : value ≠ 0) :
256 ^ (digitCount value - 1) ≤ value`. Together with
`digitCount_capacity`, the latter states the exact minimal nonempty base-256
width for every positive Nat. Zero is explicitly encoded with one zero digit.

The first two Checks attempts exited normally in 4.739 and 4.554 seconds.
Their independent universal expected-type consumers elaborated and printed
only standard Lean axioms. Concrete `decide` controls stopped at the
well-founded logical `Nat.log2` definition; switching kernel reduction alone
did not solve that definitional-reduction issue. The repair evaluates its
equations with simplification and uses `fromReference_valid` for the wide
image's validity. It does not substitute native evaluation or alter any
codec/validator definition. Receipts `binary-checks-01.json` and
`binary-checks-02.json` are diagnostic failures, not passing test evidence.

### Supported-domain converse and scalar-cap proof producer

At the Cursor worker's explicit request, the proof-only module
`Binary/Bounds.lean` now supplies a direct producer for BINARY-BOUNDS. Its
planned consumers are the efficient parser's early scalar-digit caps and exact
supported-decoder domain. The source-level algorithms in Codec and Image are
unchanged. The exact new propositions are:

```lean
BinaryCodec.digitCount_mono (a b : Nat) (h : a ≤ b) :
  digitCount a ≤ digitCount b

BinaryCodec.digitCount_lt_pow (width value : Nat) (h : value < 2 ^ width) :
  digitCount value ≤ max 1 (LimbWord.limbCount width)

StorageImage.decodeSupported_supported (limits : StorageImage.Limits)
  (bytes : ByteArray) (image : StorageImage)
  (h : StorageImage.decodeSupported limits bytes = some image) :
  image.Supported limits

StorageImage.decodeSupported_iff (limits : StorageImage.Limits)
  (bytes : ByteArray) (image : StorageImage) :
  StorageImage.decodeSupported limits bytes = some image ↔
    bytes = image.encode ∧ image.Valid ∧ image.Supported limits
```

`Supported` expands to file-byte, width, register, instruction-count and
memory-word-count bounds. The independent `checkedSupportedCaps` consumer
states all five inequalities directly. The proof first establishes the actual
number of values returned by `readMany`, recovers the declared array count at
each bounded array parser, then extracts both body header caps and the outer
file-size guard. These statements await the next coordinated narrow check.

All of the Bounds statements passed in **3.617 seconds**; receipt
`.lake/native1/binary/binary-bounds-02.json` pins source SHA256
`1ADF9BE737AD6C86AAC6E5FBA75ED3384876AA029CCEFBBD76CDA03DF70C339E`.
The four axiom prints (both exact consumers and both digit-count facts) contain
only `propext` and `Quot.sound`. The first attempt exited1 after4.910 seconds
because Lean/Std requires explicit `Nat.le_trans`, rather than method notation
on these inequalities; its diagnostic receipt is `binary-bounds-01.json`.
No function, proposition, limit or trust setting changed during that repair.

The third Checks attempt exited1 after64.991 seconds with deterministic
200000-heartbeat failures in the broad simplifier, without a wall timeout or
output overflow. Its complete receipt is `binary-checks-03.json`. All intended
37 public consumer/control propositions remain unchanged. The repair replaces
the broad tactic with four private structural helpers: small-digit scalar
framing, invalid-image rejection from exact decode soundness, and
unsupported-image rejection from the just-checked cap converse. Wide-image
size uses the framing theorem; malformed cases use the specific validity
conjunct they contradict. No logarithm recursion, native decision procedure,
larger heartbeat setting or repeated unchanged check is used.

The fourth Checks attempt exited1 after66.250 seconds. The residual failures
were missing `Instruction.operands` normalization in the two byte/length
examples, unnecessary broad reduction in two wide-word rejection proofs, a
missing empty-tail scalar specialization, and an unreduced record projection
in the file-cap contradiction. `binary-checks-04.json` retains the exact
diagnostics. The current repair adds the missing structural rewrites and uses
`simpa only` for the large limb-decoding theorem; the 37 public control and
consumer propositions are unchanged. This is not a passing test receipt.

All ten bounded Binary JSON receipts available at this point, including failed
experiments, and the two early Codec transcripts were copied unchanged into
`docs/internal/extensions/native1/commands/` at the lead's request. Subsequent
receipts will be copied there as well. The three checked producer source
hashes above remain unchanged; `Checks.lean` is explicitly excluded from the
lead's verified checkpoint until its own passing receipt exists.

### Independent C++ consumer assignment

After the image proof producer, the lead assigned only
`native/packed-rmq/examples/native.cpp`, with the existing `native_main.rs`
command line and `packed_rmq.h` ABI as its fixed contract; header and shim stay
under lead ownership. The concrete acceptance IDs are CPP-CLI (same load/query
forms, argument validation, application messages and successful observations),
CPP-OWNERSHIP (one runtime and retained load result; borrowed image/text views
remain within their owners; exactly matching DLL frees on every exit), and
CPP-VERIFY (compile/link and actual ABI smoke comparisons after library
artifacts exist). No native compiler call was made before those prerequisites.

The initial C++ draft matches load/query forms, width-sized hex endpoints,
decimal overflow checks, fuel/reads/repeat limits, one loaded image across
repeated queries, UTF-8 text validation and RAII result ownership. It checks
file size before allocation and continues enforcing the file cap if the file
grows during reading. Caller input bytes are released after successful load.
Operating-system file failures use C++ standard-library diagnostics; all
application-level rejection strings match the Rust caller. The source draft
SHA256 was `9D0DFD03FF37082026122DE71186146CC395DDB31DBD859B9A265567B20A40F1`.
After the registry reviewer's exact-output request, both stdout and stderr are
put into binary mode on Windows before any output; this preserves the Rust
caller's LF observation bytes. The updated source SHA256 is
`A5BFE471012D24A68BF743F2EC76F141F5B7731E66F7002A6F2127485FBA3FAB`.
All three CPP rows remain OPEN until the actual library smoke checks run.
The registry worker independently reviewed the C++ source and found no concrete
RAII/lifetime or parser-parity defect: load ownership outlives repeated queries,
raw bytes are freed after image capture, query text is copied before release,
and decimal/hex/reads/repeat boundaries match Rust. It also confirmed binary
stream mode preserves LF. This is source-review evidence, not compile/link or
executed ABI evidence.

The lead's full binary build subsequently passed. Its durable receipt
`docs/internal/extensions/native1/commands/binary-build-20260912T111100924.json`
has `success=true`, pins the unchanged C++ SHA256 above, and records DLL linking
in37.101 seconds, the C++ import-library step in1.738 seconds, and C++17 compile
and link in5.820 seconds, all exit0. The actual C++ executable is
`.lake/native1/binary-build/packed-rmq-native-cpp.exe`. This closes the compilation
portion of CPP-VERIFY. Executed CLI/ownership observation checks remain pending
the lead's native replay; successful compilation alone does not close them.

The next concrete Checks iteration retains all 37 public IDs and universal
consumer propositions, but changes two representative malformed inputs: the
opcode99 test uses width8 instead of168, and the high-padding test uses the
forbidden bit9 in a two-byte width9 word instead of bit169 in22 bytes. The
rejection requirements are unchanged; universal accepted-image validity still
checks every word at every width, the independent roundtrip image remains
176-bit, and the wrong-length negative remains width168. These smaller
counterexamples isolate the intended defects and avoid proof normalization of
irrelevant wide constants. This concrete-parameter change is recorded rather
than represented as an unchanged test source.

The Cursor worker is refining its parser with early scalar-digit limits. The
all-Nat reference is bounded by supplied bytes but is not itself a claim that
arbitrarily large encoded header Nats are rejected before their accumulation.
Early host-limit rejection and efficient array traversal belong to that
downstream producer, whose all-byte equivalence / supported roundtrip consumes
the exact domain theorem above.

### Final owned proof/control disposition

The final focused `Binary/Checks` check passed in **6.617 seconds** at checkout
HEAD `fbd5a44f4f68c0ab1ad54fbff0cc9169000c8949`. The complete receipt, including
all input source hashes, command, owned deadline, stdout, exit and elapsed time,
is `docs/internal/extensions/native1/commands/binary-checks-06.json`. All 37
public theorem consumers/controls elaborate; the 13 printed axiom inventories
contain only `propext`, `Quot.sound`, and (for the reference construction and
numeric bit accounting) `Classical.choice`. No native decision procedure or
additional trust declaration was introduced. The compiler was released to the
lead immediately after this boundary; no owned process remained.

The preceding `binary-checks-05.json` attempt exited1 after75.384 seconds, with
one deterministic heartbeat failure in the malformed-opcode proof. All other
36 public statements elaborated. The final control uses the two-field row
`[99,0]` at width8: the row has a legal halt/jump arity, but the actual tag parser
rejects opcode99. This isolates the tag defect from an arity defect. Its proof
uses an explicit invalid-image hypothesis, exact field decoding, and the
parser's concrete equation; it does not broadly simplify the parser. No limit
was raised and no unchanged command was retried. Both attempt receipts are
retained in the commands directory, alongside all earlier bounded receipts.

Final checked owned source SHA256 values:

| Source | SHA256 |
| --- | --- |
| `Binary/Codec.lean` | `E46F05148BB2F4D1D25C848EC804B0E2E0881EFB536F988A90AB9CB7371C11F7` |
| `Binary.lean` | `C50741D0A9AED1797919F405E8F7440410C0CD13DD2B9F299D0E6AB5E959AE16` |
| `Binary/Bounds.lean` | `1ADF9BE737AD6C86AAC6E5FBA75ED3384876AA029CCEFBBD76CDA03DF70C339E` |
| `Binary/Checks.lean` | `03B4786F8AB00028B09AB6270EFE3B9CF9E178E7DB4CA4D98C98D0EEBC255CAD` |

The owned leaf is CANDIDATE_COMPLETE for BINARY-IMAGE, BINARY-ROUNDTRIP,
BINARY-ALLN, BINARY-INITIAL and BINARY-VERIFY: actual record field types and
`decoded_fields` preserve all five fields; `decode_encode`, `decode_iff` and
raw injectivity establish the complete image's two directions; the proper
prefix theorem plus named malformed controls cover the frozen rejection
surfaces; `encode_size` and `encoded_bit_accounting` charge exact cells and
framing; all-Nat scalars and the positive176-bit image retain the broad domain.
These rows still require the lead's independent reconstruction and native
consumer integration before coordinator acceptance.

BINARY-BOUNDS has a checked owned producer: `decodeSupported_iff` states exact
encoding, Valid and Supported in both directions, and `decodeSupported_supported`
exposes every finite cap after success. Early digit rejection and efficient
byte traversal are a separate assigned consumer: the machine worker reports
checked `BinaryCursor.decodeSupported_eq` for all bytes and limits and passing
typed controls. This evidence note does not substitute our reference parser
for that native algorithm. The lead must retain the exact Cursor-to-Image-to-
Machine composition in its final executable build. C++ compile/link and actual
ABI observations remain OPEN, as do all witness-export obligations in the
separate witness leaf. No full NATIVE-1 acceptance is claimed here.

### Design-decision prose for lead integration

The native image is versioned with RMQN/version1 and stores the machine's own
nested UInt8 code and memory arrays. All metadata scalars use minimal
little-endian base-256 digits with a unary byte-count prefix; array counts and
word byte lengths use the same codec. A fixed u64 header was rejected because
it would silently restrict the abstract all-size serialization theorem.
Per-word byte-length framing was retained because it permits a simple
compositional parser and an exact malformed-length rejection surface. Its
redundancy is explicitly charged as framing bytes, so this decision does not
support a claim that the native image itself meets an unchanged succinct
payload bound. A separate inputLength header preserves the actual public r2
initializer even when memory[0] is unrelated or malformed. The decoder proves
both directions of exact encoding identity and canonical validity; the host
layer adds explicit finite caps. Efficient ByteArray traversal and early
bounded scalar accumulation refine this fixed format in Cursor rather than
changing the serialized domain or introducing another executable store.

### Proof digestion

Conceptually, the codec now connects the mathematical word model to an actual
versioned byte file. A successful load determines one exact Image, and encoding
that Image reproduces the whole accepted file. The Image fields are the same
Code and Memory types consumed by the limb machine; no separately proved
scalar-memory copy stands in for them. Every loaded word has exactly the
rounded byte count and zero high padding, while instruction rows also pass the
actual primitive tag/shape parser. The header's inputLength is independent of
the first memory cell.

The live assumptions are explicit: canonical-image roundtrip assumes positive
width, representable header values, canonical stored words, and valid encoded
instruction shapes. The fromReference constructor obtains these from code
Fits and memory-value bounds. This does not prove that an arbitrary valid
image was built from the canonical RMQ input; that is the lead's separate
construction theorem. The reference list parser establishes byte semantics,
not a physical time bound. The native parser, source-to-machine execution
chain, ABI and complete fixture replay remain downstream obligations.

A skeptical reader should ask whether the efficient loaded path really returns
these exact arrays, whether early scalar limits reject only unsupported data,
whether the canonical producer supplies all Fits/value premises, and whether
the actual native entry invokes that same loaded machine. Cursor's refinement
and the lead's canonical/native composition must answer those questions. The
file-size equation also deliberately leaves Array objects, parsing
temporaries, allocator overhead and compiled BigNat arithmetic outside the
numeric payload account.
