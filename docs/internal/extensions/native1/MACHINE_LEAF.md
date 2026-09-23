# NATIVE-1 limb machine producer

Status: INCOMPLETE
Phase: MACHINE_AND_CODE_CONVERSE_CHECKED

The lead assigned this producer after the checked byte-word leaf on 2026-09-12.
The governing proof-sprint preflight and skill reads recorded in LIMB_WORDS.md
remain applicable. Source and independent typed consumers are owned only under
`Native/Machine.lean` and `Native/Machine/`; this report is the only owned prose.
Shared ledgers, canonical source and other workers' files are not owned.

| ID | Exact frozen requirement | Exact evidence target | Consumer | Attack | Status |
| --- | --- | --- | --- | --- | --- |
| LM-STORAGE | Persistent memory/reg words are Array UInt8; PC/halted packet likewise Word; persistent code stores all original numeric encoding fields as limbs, e.g abbrev Code := Array (Array Word), decode only fetched <=5-word instruction through Route.parseInstruction, encoding each Instruction.encoding word. No persistent cached Nat fields and no calling runThin/executeFinite on a fully decoded machine as the implementation. | Definitions of Memory, Code, State and direct execute/step; decode/encode identities on exact supported width and bank | full native capstone | inspect actual evaluator/storage fields, mutate stored source byte | Checked producer and typed consumers; native integration remains lead-owned |
| LM-STEP | Direct load/set/move/checkedArithmetic/comparison/branch operations on stored words; decoded values temporary. Define explicit faults for malformed/code/unsafe arithmetic; missing memory load must charge/record none and fault, missing fetch no charge/statuschange. | All nine constructors refine actual PackedWordRAM.execute on safe domain; explicit outside-domain cases | positional step/run simulation | missing fetch/load, invalid code, failed arithmetic | Checked producer and typed consumers; native integration remains lead-owned |
| LM-RUN | Quote raw full run equality (decoded final and ordered transitions) and/or explicit result/status/read/step/category projections to original run; tail runner uses actual same steps without full trace and proves log erasure. Prove code and state encoding/refinement and invariant preservation necessary for fuel induction; all9 constructors, all fuel, halted/fault status handled. | Same code/memory/state run equality for every fuel; actual tail executor projection and no-read-log theorem | nativeExecutionCapstone_holds | change decisive read/result/category; halted/fault/zero fuel; multiplicity | Checked producer and typed consumers; native integration remains lead-owned |
| LM-DOMAIN | The generic simulation domain may require canonical code/memory/state, bounded destination and original raw run's positional Instruction.Safe plus after.Fits. It must not assume canonical RMQ as unexplained safety; root will instantiate from PQ1. | Explicit current-state and every-transition bounds, same memory/code quantifiers, encode identities and safe-prefix induction | exact canonical PQ1 instantiation by lead | circular invariant or assumed final result | Checked producer and typed consumers; native integration remains lead-owned |
| LM-RUNTIME | Canonical check guards must not scan whole memory/register arrays every step in runtime; initial loader validation and local checks preserve invariants. Host usize/allocation support is root's separate boundary; abstract machine uses safe Array Nat indexing via length test before any conversion, permits missing/sentinel addresses with checked semantics. | Runtime evaluator performs local checks and bounded current-instruction decode; host domain remains separate | binary-loaded entry | hostile instruction shape and bad index | Checked producer and typed consumers; native integration remains lead-owned |

Proposed API namespace `PackedNative.LimbMachine`: Memory is Array Word, Code is
Array (Array Word), State stores limb registers, limb PC and running/halted-word/
fault status. Encoders take dynamic width and finite register capacity. Decoded
instructions and Nat scalar values are temporary values. Trace observations may
retain them, while the native tail runner retains no transition list.

The reference safety premise is every positional transition of the exact raw
`run memory program fuel state`: its instruction is Safe at its before-state and
its after-state Fits the same width. Full program encoded fields fit and writes
stay below capacity; memory words and initial state fit; registers omitted by
the finite bank are zero. This is a producer premise for the lead's PQ1 theorem,
not an assumption that the requested native result is already true.

Verification uses one-job bounded direct Lean checks of owned modules and exact
consumers. The lead currently owns the compiler slot for repaired native build;
this worker may prepare source but will not launch Lean until the slot returns.

## Source construction and checked composition

The direct machine is in namespace
`RMQ.SuccinctFinal.PackedNative.LimbMachine`. Persistent `Memory` is `Array Word`,
`Code` is `Array (Array Word)`, and `State` contains only `regs : Array Word`,
`pc : Word`, and a running/halted-word/fault status. `Word` is the preceding
leaf's `Array UInt8`. Source register reads beyond the allocated bank return an
encoded zero; the simulation requires omitted reference registers to be zero.
Destinations outside the allocated bank fault. No operation resizes that bank.

`execute` dispatches every original constructor directly. Loads use the supplied
byte memory at the decoded address and derive the actual receipt from its optional
reply. Move/constant/arithmetic/comparison write stored byte words. Arithmetic
calls the checked operation producer; PC increments use `checkedNat`; jumps and
halted packets remain byte words. Local guards check the accessed operand,
destination, result or PC. They do not scan all registers or memory. Current
instruction parsing first checks at most five fields, then checks their canonical
byte representation before invoking the existing `parseInstruction`.

`step` has three outcomes. `stopped` means no fetched instruction or an already
halted/faulted state. `rejected` means malformed PC/code and returns fault without
inventing an instruction event. `executed` retains the actual decoded instruction,
before/after byte states and optional receipt. A missing memory read is an executed
load, records `reply = none`, and faults. Arithmetic failures are executed
instructions with their original category. Detailed operation failures remain
available in `Execution.error`; persistent state records fault status.

The observational runner retains actual transitions. The production `runThin`
calls the same `step` but accumulates only `Stats`, with optional read receipts.
It never constructs a transition list. A transient current transition is consumed
at once. Six Nat counters and optional receipts are instrumentation rather than
cached machine-register values or payload bits. In false logging mode, the
read-log accumulator is unchanged for every input, including malformed machines.

The checked full-run type is:

```lean
run_reference (width capacity : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (fuel : Nat) (s : PackedWordRAM.State)
    (hm : forall value, value ∈ memory -> value < 2 ^ width)
    (hp : forall i, i ∈ program -> i.Fits width)
    (hw : forall i, i ∈ program -> i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width)
    (hz : forall r, capacity ≤ r -> s.regs r = 0)
    (hsafe : RunSafe width (PackedWordRAM.run memory program fuel s)) :
  (run width (encodeMemory width memory) (encodeCode width program) fuel
    (State.encode width capacity s)).decode =
      PackedWordRAM.run memory program fuel s
```

`RunSafe width r` expands exactly to every `t ∈ r.transitions` having
`Instruction.Safe width t.before t.instruction` and `t.after.Fits width`. It does
not assert the native result or a native refinement hypothesis. Whole-program
field fitting, destination bounds, supplied memory fitting, initial state fitting
and zero tail are separate explicit premises. Thus the reference retains total
Nat arithmetic, while the checked machine agrees on its stated safe domain.
Malformed and unsafe checked executions outside that domain retain explicit
failure behavior without an unconditional equality claim.

Composition is `execute_encode` (all nine constructors and actual receipts),
`step_encode` (actual fetch), `run_encode` (all fuel by operational induction),
then `run_reference` (decoded exact final state and full ordered transitions).
`runThin_projection` and `runThin_reference` carry that equality into the actual
production loop. The full `Run` equality entails result, final status, every
ordered attempted read/reply, step count and all six original `categoryCount`
projections. The independent consumer explicitly projects all ten of those
observation fields instead of using an aggregate counter as a substitute.

`encodeMemory_decode` proves exact loaded-memory identity from `MemoryCanonical`:
re-encoding the decoded loaded array returns that same array. `State.encode_decode`
does the same for canonical loaded registers, PC and halted packet. They feed
`run_loaded_reference` and `runThin_loaded_reference`; the latter has the same
production result/Stats equality with `observeRun` of the raw run of those decoded
loaded cells. Code identity is an explicit `code = encodeCode width program`
premise for the binary loader to discharge. This avoids silently substituting a
sibling program or memory.

The lead supplies canonical PQ1 safety from the accepted query theorem. Generic
fuel-prefix membership/safety producers are provided so the actual bounded trace
safety extends to every smaller budget. The lead handles larger fuel using the
source halt theorem. No canonical theorem or binary marshal theorem is assumed
as already finished in this report.

## Verification record in progress

One compiler owner was maintained. The lead alternated this worker's short
one-job checks with the repaired native build, registry controls and binary
producer. The direct pinned Lean 4.22 compiler and existing owned bounded-process
wrapper use this worktree's `.lake/build/lib/lean`; generated C stays under this
worktree's `.lake/build/ir`. No mutable shared cache link was introduced.

| Receipt under `commands/` | Exit, seconds, deadline | Result |
| --- | --- | --- |
| `machine-01.json` | 1, 9.298, 120s | Initial source/inference presentation errors in map identity, indexed write, and simplifier staging; repaired. |
| `machine-02.json` | 1, 8.201, 120s | Two missing explicit map arguments and indexed-write bound remained; repaired. |
| `machine-03.json` | 0, 9.644, 120s | Initial machine, all-nine constructor simulation, tail projection and no-read-log theorem checked. |
| `machine-04.json` | 1, 23.213, 90s | Full proof had three presentation issues: unreduced pair projections, Array-none premise shape, redundant final tactic; repaired. |
| `machine-05.json` | 0, 20.135, 90s | Complete full-run and loaded-byte reference theorems checked; actual C and olean emitted. |

Later invariant helpers and independent `Machine/Checks.lean` were then added;
their final check is pending the next negotiated compiler slot. The preceding
receipt does not certify those later additions. Narrow trust/native-decision
scans currently have zero matches. The final exact source hashes, final typed
consumer/axiom output and command outcomes will be appended after the checks.

Final machine/invariant check subsequently passed: `machine-06.json`, exit 0,
15.072 seconds under the 90-second deadline, with olean and C output. Independent
`Machine/Checks.lean` passed in `machine-checks-01.json`, exit 0, 9.315 seconds
under 60 seconds. It checks 22 direct machine observations, all assigned full-run
and loaded-run types, and 17 declaration inventories. Every inventory contains
only `propext`, `Classical.choice` and `Quot.sound` (some use fewer). The 168/176-bit
examples run the actual limb machine and check its decoded halted packet.

The later `Machine/CodeFacts.lean` converse producer remains in repair. Its first
two checks returned deterministic simplifier/whnf heartbeat failures at 79.841
and 71.058 seconds, both exit 1 and neither a wall-clock timeout. The third proof
strategy explicitly splits bounded instruction tag and tail shape before equality
elimination, avoiding parser simplifier unfolding. These are implementation proof
failures, not counterexamples to the theorem or a full-target obstruction. The
already checked forward code/state/run theorems remain available. Compiler slots
were released to the binary and registry workers after each bounded check window.

Checked core source snapshots: `Native/Machine.lean` is 38858 bytes,
SHA256 `F5286E6B52A5C5A73571BBF831E7CA9C5D731F7F5998F3ABA724E17F7AB94B3D`;
`Native/Machine/Checks.lean` is 7330 bytes,
SHA256 `F8B62700DFFCF1BF1948EE63BE1FFCBE5A9E10757A569E3DF8A7EEC8F27614C2`.

## Proof digestion and proposed design decision

Conceptually, this changes the executable machine representation rather than
adding a second abstract interpreter to compare with a separate native program.
In plain English, the machine reads its byte storage, executes the checked
primitive, and writes bytes back. The full proof follows those operations through
every fuel step and retains the actual read order, including failed attempts.

Live premises are the explicit word/code/register bounds and safety of the actual
raw transition prefix. Their canonical instantiation belongs to the lead's
`nativeExecutionCapstone_holds` join. Mathematical width is unrestricted; finite
host allocation/USize support is a separate API boundary. Numeric payload,
rounded byte capacity, array/list objects, temporary decoded Nats, observation
logs and modeled categories remain separate. The source-level implementation is
this Lean definition; compiler/runtime/FFI translation assumptions remain those
of the approved route. No physical constant-time claim is made for multiprecision
decoding or arithmetic.

`Array UInt8` guarantees finite byte-valued elements, not a theorem that each
runtime array slot physically occupies one byte. Lean array slots, tagged/boxed
values and object headers may add storage beyond the numeric capacity proved by
the limb layer. A packed binary file and a loaded Lean object therefore have
separate framing/container overhead accounts.

Proposed DD rationale: store every persistent program operand and state word as
canonical little-endian bytes and decode only the current instruction/operands.
Use the approved checked-versus-raw safety split. Reject malformed code before
creating a charged instruction transition, preserve a failed data load as an
actual charged load with `none`, and distinguish detailed execution errors from
the raw fault status. The rejected alternative was a persistent fully decoded
Nat machine dispatched through the old finite runner, which would not close the
finite-storage target. Consequences: the source and binary loader share byte
arrays; canonical safety must still be supplied explicitly; runtime overhead is
separate from the six modeled operation counts. The skeptical graduate student's
next question is whether the final binary-loaded entry and compiler/FFI wrapper
call this exact source and discharge its same-object safety premises; those
consumers remain lead-owned.

## Successor cursor contract frozen before implementation

The lead explicitly assigned `Native/Binary/Cursor.lean` after the machine leaf.
The binary worker retains `Binary.lean` and `Binary/Codec.lean`; no edits to those
files are authorized here. The cursor producer must close the actual efficient
ByteArray decoder and its proof connection, not merely supply a parser helper.

| ID | Exact frozen requirement | Evidence target | Consumer | Attack | Status |
| --- | --- | --- | --- | --- | --- |
| LC-INDEX | Need actual ByteArray+offset parser + tailrecursive array fold, proved equal/refining reference StorageImage.decodeSupported, never list reference at fullnative (rest.length per scalar => quadratic and readMany non-tail). | Runtime Parser ByteArray offset -> optional value/next offset; all count/prefix loops tail recursive; no call to list reference or repeated suffix lengths | actual binary-loaded native entry | complete 837572-instruction image and malformed length | Open |
| LC-BOUND | Needs real byte/index+count limits beforeallocation/powers and tailrecursive countloop; retain source correspondence theorem. | Remaining bytes computed from constant-time size/offset; declared scalar/word/array byte/count bounds checked before loops/slices; width/register caps before image body | supported-host loader | oversized/truncated prefix, header, cell and arrays | Open |
| LC-JOIN | Target efficient decode equality to decodeSupported or full sound + supportedimage roundtrip/field identity; root actual API calls yourentry only. | Exact cursor/ref-parser relation, complete supported-image decoder theorem including magic/validity/no leftovers and exact code/memory fields | nativeExecutionCapstone_holds and exported entry | source mutation removes loaded/marshaled dependency | Open |

Proposed proof-only suffix is `bytes.data.toList.drop offset`; this is never the
runtime parser input. Prefix scanning, numeric digit accumulation and counted
Array.push folds use explicit tail recursion. Word slices are bounded by the
decoded length, available bytes and declared limb count. Full decoder reuse of
`image.valid` is an explicit final semantic check, separate from the efficient
framing parser. Optional large numeric-header temporaries remain bounded by file
bytes and must not introduce non-tail recursion.

## Final converse and consumer evidence

`Machine/CodeFacts.lean` now closes the successful parser converse. The exact
checked conclusion is:

```lean
decodeInstruction width fields = .ok i →
  fields = encodeInstruction width i ∧ i.Fits width
```

It consumes the converse of the actual `Route.parseInstruction`, including every
opcode and numeric field, plus every stored word's checked canonical byte shape.
From successful decoding of every row, the checked `code_exists_program` yields:

```lean
∃ program : PackedWordRAM.Program,
  code = encodeCode width program ∧ ∀ i ∈ program, i.Fits width
```

This is a same-order exact-code witness in Prop, never a persistent decoded code
cache. The reverse bridge `decodeInstruction_of_canonical` consumes the exact
field-count bound, canonical fields and existing parser success. The lead's Host
producer uses these declarations for arbitrary successfully loaded program rows.

The third structural strategy specializes instruction tag and list shape before
parser reduction. It removed all arithmetic tactics from parser-success contexts.
`machine-codefacts-03.json` reached the end of proof checking in 7.717 seconds but
returned exit 1 because the generated-C parent directory had not been created.
After creating that owned directory, `machine-codefacts-04.json` passed, exit 0,
7.884 seconds under 60 seconds, with C and olean output. No source proof changed
between those two checks. `machine-codefacts-checks-01.json` passed, exit 0,
4.320 seconds under 45 seconds: four independent expected-type consumers and
three inventories. Each inventory contains only `propext` and `Quot.sound`.
There were no wall timeouts or surviving owned processes.

Final converse snapshots: `Machine/CodeFacts.lean` is 7126 bytes, SHA256
`94AA115EA137C32F0D11E3714A0E6C0ADD87165ED1306CDBBC22ECC4C0030C00`;
`Machine/CodeFactsChecks.lean` is 1432 bytes, SHA256
`A3AAC86CE95AF7B8F477B499D8DFD6AD8A304EDE8CEB20461054A2E0A6151ECE`.
The already checked Machine.lean and its original Checks source remain unchanged.

The bounded machine/code producer is complete and independently typed locally.
The full NATIVE-1 assignment remains INCOMPLETE while the lead links, measures and
validates the native route. No full acceptance row or native measurement is
inferred from this producer check.
