# PRE-1 contract replay design

This is the contract prerequisite replay. It does not implement or validate the
future efficient builder. The production surfaces are the construction contract
module and `scripts/preprocessing_contract_check.lean`; the runner contains no
copied Lean contract, alternate interpreter, or source-text semantic validator.

`scripts/preprocessing_contract_replay.ps1` owns one sequential mutation at a
time. The registry is `contract_cases.json`, version 1. An independent ordered
list of all 18 IDs and a frozen content SHA-256 in the runner reject missing,
extra, duplicate, reordered, or modified cases. The content hash normalizes only
CRLF to LF, because this checkout enables `core.autocrlf`; raw registry and
source hashes are also recorded. Mutation fragments adopt the source's uniform
LF or CRLF spelling, and mixed source line endings fail before mutation.
Restoration always writes the captured original bytes.

Every selected case must find exactly one registered fragment. The runner
first runs the production `preprocessing_contract_firewall.ps1` guard, then
rebuilds `RMQ.Core.WordRAM.Construction.Contract` before elaborating the direct
typed consumer, so it cannot use a stale successful consumer against an
unrebuilt mutation. A rejecting case requires a nonzero completed compiler
stage (guard or compiler) whose output contains the registered failing surface.
Each case pins `expectedStage`; consumer failures additionally pin the exact
consumer filename and one-based line, so a producer failure or another consumer
location cannot satisfy a field-dependency test. The registry self-test calls
the production verdict matcher with correct-stage/location controls and
wrong-stage, wrong-location, generic-substring, unrelated-error, timeout, and
success-versus-rejection controls. A timeout, output
limit, failure at a different surface, or failure to launch is inconclusive
evidence and makes the replay exit nonzero. The expected-accept control requires
all three stages to pass and its registered output surface to appear.

In `finally`, each case writes back the original bytes, checks the exact raw
SHA-256, checks the registry hash, reruns the guard, rebuilds the restored producer, elaborates the
restored consumer, and compares Git HEAD, status, unstaged binary diff, and
staged binary diff with the starting state. The final run also checks every
construction source and registered mutation source against its initial raw
hash. A preexisting authorized dirty worktree is recorded and must remain
identical; it is never mislabeled clean. The lead must freeze those files and
Git state while a replay runs.

The runner uses the existing `Invoke-RMQOwnedBoundedProcess` implementation for
every subprocess, including Git inspection and child script-boundary tests.
The default semantic deadline is 300 seconds, the administrative deadline is
60 seconds, and the descendant sleeper deadline is 12 seconds. These are
explicit parameters so the lead can choose an evidence-based deadline before
execution. `LEAN_NUM_THREADS=1` is passed to each sequential Lean/Lake stage;
the pinned Lake command does not support `-j`. The default executable resolves
the installed toolchain named by `lean-toolchain` directly under `ELAN_HOME`
(or the standard user `.elan` directory), avoiding an elan proxy that could
attempt a download. `-LakePath` can name the actual installed binary explicitly;
the exact command path is recorded for every stage. The lead is responsible for
ensuring that no second heavy command shares this build tree.

The process self-test uses a deliberately nonzero exit with independent stderr
and a timed-out sleeper that starts a real descendant. A missing descendant
creation is reported as uncovered/inconclusive and exits nonzero. Process
ownership is the existing Windows job or POSIX process-group implementation.
The report names the host platform actually tested and explicitly leaves the
other host branch unexecuted; deterministic launch-plan tests do not claim to
execute that branch.

The real selector parameter boundary distinguishes omission from a bound empty
string. Omission selects all frozen IDs; one exact valid ID selects one case.
Empty, whitespace, malformed, zero, unknown, missing-argument, and repeated
parameter invocations must reject before semantic execution. Boundary tests
launch a child script that calls the actual runner with literal arguments, so
PowerShell 5/7 native-argument empty-string transport cannot turn the empty test
into the omitted test. The production probe prints the exact selected IDs and
count, and the tests require both.

Run modes are deliberately named in every report:

| Mode | Purpose | Semantic execution |
| --- | --- | --- |
| `-StartupOnly` | Bounded baseline producer/consumer startup | One baseline; zero mutation cases |
| `-OnlyCase C01_REFLECTION` | Known exact focused case before a full run | Baseline plus one case and restoration |
| No mode/selector | Full frozen registry | Registry/selector/process self-tests, baseline, all 18 cases and restoration |
| `-RegistrySelfTestOnly` | Missing/extra/duplicate/reorder/version/hash rejection | None |
| `-SelectorBoundarySelfTestOnly` | Real script-boundary binding | None |
| `-DeadlineSelfTestOnly` | Exit/stderr and real descendant cleanup | None |
| `-SelectorProbeOnly` | Report selected exact IDs at the production boundary | None |

A self-test or startup PASS has its own mode and zero executed mutation cases;
it cannot close the full campaign. The full/focused report compares the
executed IDs with all selected expected IDs before reporting PASS.

Each run persists JSON stage records with command, arguments, environment,
stdout, stderr, original exit, ownership, deadline, duration, timeout and output
limit flags. It also writes case records and a final report. By default these
live in a fresh directory under `.lake/preprocessing-contract-replay`, outside
tracked evidence. An evidence directory within the repository must be under
`.lake`; the lead copies selected final evidence into the durable phase folder
after execution. This prevents the replay's own logs from changing the Git
state it checks.

Rejected alternatives were accepting any failing compiler invocation, trusting
the registry to enumerate itself, forwarding empty selectors only as native
argv, root-only timeout cleanup, and restoring source without rebuilding its
artifact. Each would make a required negative control capable of passing for
an unrelated reason. These decisions implement REPLAY-EXACT-REGISTRY,
REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE, and the contract phase's
INV-MUTATION-REPRODUCIBILITY; they do not close builder acceptance rows.

Author verification is recorded by the lead in the command ledger. Initial
script parsing succeeded under PowerShell 7.6.5 and Windows PowerShell
5.1.26100.9444. The replay owner deliberately
does not run Lean/Lake concurrently with the lead.

## Frozen expected failure surfaces

The registry pins these exact consumer locations after the final consumer
source freeze. These are expected verdicts; only the lead's production replay
establishes that the registered mutations actually reach and fail there.
`fields` below abbreviates
`((program.map (fun i => i.primitive.constants)).flatten)` only in this table.

| Case | Mutation | Exact proposition retained by the independent consumer / guard |
| --- | --- | --- |
| C01_REFLECTION | Replace reflection with `True` | For every `i s`, `bstep i s = interpretPrims i.semantics s` (consumer line 11). |
| C02_CAP | Replace workCap with `True` | For every `i : BInstr`, `i.semantics.length <= 1` (line 13). |
| C03_CONSTANTS | Replace constantCap with `True` | For every instruction `i`, primitive `p` in `i.semantics`, constant `c` in `p.constants`, and width at least 32, `c.val < 2 ^ width` (line 15). |
| C04_HEADER | Replace headerRead with `True` | For all `width xs`, the named header instruction on `wordInputState width xs` loads `xs.length` into register 1 and remains running; the same state with header memory overwritten by `none` faults (line 21). |
| C05_POINTWISE | Replace pointwise with `True` | For all `width xs i`, `encodeInput width xs (i + 1) = (xs[i]?).map (encodeInt width)` (line 24). |
| C06_ORACLE | Replace oracleControl with `True` | No `ps : List Prim` of length at most `primCap` satisfies `forall s, interpretPrims ps s = oracleSemantics s` (line 27). |
| C07_UNIFORM | Replace uniformControl with `True` | No single `program` satisfies `Uniform program bakedProgram` (line 29). |
| C08_STORE_VALUE | Replace writeValue with `True` | For every address register, value register and state with the address below `s.extent`, the store's memory at `s.regs address` is `some (s.regs value)` (line 32). |
| C09_FRESH_RESERVE | Replace freshReserve with `True` | For every state satisfying `CleanTail s` and every destination, reserve leaves memory at the old extent equal to `none` (line 35). |
| C10_CODE_ACCOUNTING | Replace codeAccounting with `True` | For every `program width`, `CodeAccounting program width (programWords program * width)` (line 38). |
| C11_FIELD_DELETE | Delete ProgramContract.uniform | For every `program family k b` and `h : ProgramContract program family k b`, `forall xs, family xs = program` (line 47). |
| C12_FIELD_WEAKEN | Replace that same field with `True` | The same quantified uniformity proposition and same `h` projection as C11 (line 47). |
| C13_SIBLING | Replace oracleControl by baked-program nonuniformity | The oracle nonreflection proposition from C06 still must hold; the different true fact does not supply it (line 27). |
| C14_ACCEPT_COMMENT | Change only top prose from certifies to records | All three stages succeed and the consumer prints `PRE1-CONTRACT-TYPED-CONSUMERS PASS`. |
| C15_CODE_ALIAS | Make CodeAccounting `True`, repair its own theorem to `True.intro` | For every `program width bits`, `CodeAccounting program width bits -> bits = fields.length * width` (line 42). Both replacements are one frozen whole-file Controls mutation. |
| C16_CODE_COUNT | Make programWords return zero | For every `program`, `programWords program = fields.length` (line 44). |
| C17_FIREWALL_IMPORT | Add RMQ.Core.Shape import to Primitive | The production firewall rejects the import at the exact Primitive path before compilation. |
| C18_PRIMITIVE_BYTES | Make the primitive constant instruction write zero | The production firewall rejects changed frozen Primitive bytes at the exact path before compilation. |

C01-C13 and C15-C16 require a consumer failure after successful firewall and
producer stages. C17-C18 require the named firewall failure. Stage provenance
is mandatory, so failure in a producer cannot close a consumer dependency row.
