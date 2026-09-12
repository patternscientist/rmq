# BV-1 normalization leaf

Status: INCOMPLETE (BV-1 composition phase). The assigned normalization leaf is
proved and checked; the full BV-1 allocation, physical execution and capstone
acceptance rows remain OPEN in the lead's matrix.

Scope: the lead explicitly assigned this independent semantic leaf, with only
`RMQ/Core/WordRAM/Bitvector/Normalization.lean` and this evidence file writable.
No claim of BV-1 completion, charged execution, allocation, or coordinator
acceptance follows from this leaf. The lead owns integration and shared ledgers.

Base/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Branch: `codex/bv-1-fully-charged-rank-select`.
Worktree: `C:\Users\poin\.codex\worktrees\c974\RMQ`.
Canonical proof-sprint preflight: PASS, with actual runtime project catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`; required
`rmq-proof-sprint`. The canonical skill, completion gate, AGENTS, roadmap,
frozen BV-1 acceptance matrix, canonical semantics and physical reader
interface were read before editing proof source.

## Frozen local acceptance matrix

This matrix is frozen before proof edits. It indexes a bounded leaf feeding
the lead's full frozen matrix; it does not replace or narrow any BV-1 row.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `LEAF-NORMALIZE` | normalization normalize b bits = bits.map (fun x => x != b); length unchanged; rankPrefix false normalized i = rankPrefix b bits i; select false normalized k = select b bits k for all List Bool, b, i,k using existing canonical List semantics (discover exact names). | Independent proof-only leaf | Unconditional equalities over `List Bool`, `Bool`, and `Nat`, using `RMQ.Succinct.rankPrefix` and `RMQ.Succinct.select`. | Generic select reader: original word -> normalized logical word -> canonical false-select semantics -> canonical selected-bit semantics. Lead must consume this chain in physical execution. | Empty/singleton/mixed words; both selected bits; prefix beyond length; occurrence past count. | Exact types below passed the final module build and independent typed projections. | Semantic leaf CLOSED; physical composition stays OPEN in BV-1. |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch; | Applies to this semantic leaf | Universal theorem with no guards or size hypotheses; select `none` cases retained. | Same normalization and source bits in every theorem. | Incorrect identity normalization for target `true` contradicts the checked singleton true-bit cases. | `rankPrefix_normalize` and `select_normalize` have precisely all displayed Bool/List/Nat quantifiers and no premises. | CLOSED for the semantic leaf. |
| `INV-SEMANTIC-NONVACUITY` | semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself; | Semantic equality applies; no machine liveness is claimed | Proof by canonical recursive definitions of rank/select, with independently fixed expected concrete answers. | No new semantic oracle or replacement reference theory. | Missing normalization changes a rank and select answer on `[true]` for target `true`. | Both universal identity-mutant propositions are kernel-refuted by retained source theorems. All semantic controls compile with `decide`. | CLOSED for semantic transport; machine liveness stays OPEN. |
| `LEAF-CHECK` | No separate Lean/Lake build while lead baseline dependency build is active: coordinate with me for build slot; can write proof then request narrow check. | Verification | Lead-granted slot, narrow module build and exact-type/axiom checks. | New normalization declarations. | A source file alone is not checked evidence. | Lead granted the slot after baseline Lake PID 24552 exited. Three bounded serial commands passed; slot released after final axiom import. | CLOSED. |

The other inherited machine/store/payload invariants remain applicable and open
in the full BV-1 matrix. This proof-only leaf defines no memory, interpreter,
charged operation, allocation, public certificate, or mutation replay, so it
cannot independently establish those invariants. It adds no trust shortcut or
new executable validation claim.

## Verification plan and command evidence

- Development: exact preflight above; focused module build in the lead-granted
  slot; in-module kernel examples for semantic boundaries and failed identity
  normalization; exact-type consumers and `#print axioms` for the semantic
  transport declarations; static scoped trust and diff checks.
- Full aggregate gates and broad capstone checks belong to the lead; this leaf
  does not change existing executable behavior and cannot certify the join.
- No Lean/Lake command will overlap the lead's baseline dependency build.
- Preflight command on Windows PowerShell: `powershell -ExecutionPolicy Bypass
  -File scripts/project_skill_preflight.ps1 -GovernanceRef
  0e6a00f654abc64f8b68988fa9675b9a839dca2f -RequiredSkills rmq-proof-sprint
  -RuntimeProjectSkills "rmq-coordinator,rmq-proof-sprint,rmq-audit-prompt"`.
  Exit 0, observed 8.08 seconds, exact HEAD above, before proof edits. All
  expected/checkout/working/runtime skill names agreed; required role present.

## Design and proof digestion

The checked normalization maps the requested Boolean
value to false while preserving positions. This permits the existing false-bit
select semantic route to serve both Boolean values. Normalization is a proof
and numeric-decoding bridge; it is not permission to retain a second input
bitvector without accounting for it. The physical consumer must produce its
normalized word from charged raw replies.

The source also retains optional absence: if the raw presence packet is zero,
the normalized packet is zero. A present word with raw packet `p` and logical
length `len` has normalized packet `2^len + 1 - p` for target true, or `p` for
target false. Complementing missing words without first checking presence would
incorrectly produce the packet of a present empty word; the optional theorem
and its cases separate these inputs.

An independent read-only review by `/root/select_inventory` confirmed the
unconditional prefix/occurrence conventions, finite-width complement formula,
and compatibility with the proposed generic-select route. It requested the
optional absence bridge, which was added. This review is source inspection,
not compilation or the mandatory full-candidate independent audit.

## Checked source interface

All declarations below are in `RMQ.PackedBitvector`. The final module build
elaborated these types without warnings.

```lean
normalize_length (target : Bool) (bits : List Bool) :
  (normalize target bits).length = bits.length

rankPrefix_normalize (target : Bool) (bits : List Bool) (limit : Nat) :
  RMQ.Succinct.rankPrefix false (normalize target bits) limit =
    RMQ.Succinct.rankPrefix target bits limit

selectFrom_normalize (target : Bool) (bits : List Bool)
    (base occurrence : Nat) :
  RMQ.Succinct.selectFrom false (normalize target bits) base occurrence =
    RMQ.Succinct.selectFrom target bits base occurrence

select_normalize (target : Bool) (bits : List Bool) (occurrence : Nat) :
  RMQ.Succinct.select false (normalize target bits) occurrence =
    RMQ.Succinct.select target bits occurrence

normalize_numeric (target : Bool) (bits : List Bool) :
  RMQ.SuccinctSpace.bitsToNatLE (normalize target bits) =
    if target then 2 ^ bits.length - 1 - RMQ.SuccinctSpace.bitsToNatLE bits
    else RMQ.SuccinctSpace.bitsToNatLE bits

normalize_numeric_packet (target : Bool) (bits : List Bool) :
  RMQ.SuccinctSpace.bitsToNatLE (normalize target bits) + 1 =
    if target then 2 ^ bits.length - RMQ.SuccinctSpace.bitsToNatLE bits
    else RMQ.SuccinctSpace.bitsToNatLE bits + 1
```

There are no premises beyond the displayed data arguments. Additional source
declarations commute normalization with optional access, take and drop, prove
involution, preserve optional-word length and packets, and refute replacing
normalization by the identity in each full universal rank/select proposition.
The checked consumer `normalization_semantics` pins length, rank and select
at the same input and target. A separate import check projected rank and select
from this theorem at explicitly written expected types, retaining arbitrary
target, source bits and natural-number arguments.

```lean
normalize_optional_numeric_packet (target : Bool) (word : Option (List Bool)) :
  ((word.map (normalize target)).map (fun bits =>
    RMQ.SuccinctSpace.bitsToNatLE bits + 1)).getD 0 =
    let packet := (word.map (fun bits =>
      RMQ.SuccinctSpace.bitsToNatLE bits + 1)).getD 0
    let len := (word.map List.length).getD 0
    if packet = 0 then 0
    else if target then 2 ^ len + 1 - packet else packet

normalization_semantics (target : Bool) (bits : List Bool) :
  (normalize target bits).length = bits.length ∧
  (∀ limit : Nat,
    RMQ.Succinct.rankPrefix false (normalize target bits) limit =
      RMQ.Succinct.rankPrefix target bits limit) ∧
  (∀ occurrence : Nat,
    RMQ.Succinct.select false (normalize target bits) occurrence =
      RMQ.Succinct.select target bits occurrence)
```

The present-word formula is applied only after the packet-zero guard. The
empty list and `none` are distinct: present `[]` has packet one, absence has
packet zero. The complement is bounded to the actual logical length, so no
claim is made about complementing alignment padding.

## Completed command ledger

All runs used Windows PowerShell, exact HEAD
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`, and the lead's working branch.
The source was uncommitted, as required by the leaf's no-commit assignment.
The task-local output tree is `.lake/build`; no shared cache link was used.

The lead reported that the `elan` shim attempted network access. Its authorized
fallback was the directly installed pinned binary
`C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lake.exe`.
All leaf Lean commands used that binary through
`docs/internal/extensions/bv1/run_command.ps1`, with `LEAN_NUM_THREADS=1`,
120-second owned-process deadlines, and kill-on-close Windows Job ownership.
The expected warm-module time was seconds after the lead's dependency build;
120 seconds allowed host scheduling margin. No timeout or retry of an unchanged
expensive command occurred.

| Stage | Exact command arguments | Duration | Exit and result | Durable evidence |
| --- | --- | --- | --- | --- |
| Development `normalization` | `build RMQ.Core.WordRAM.Bitvector.Normalization` | 9.870 s | 0; all proofs/controls passed; two unused-simp-argument warnings in `normalize_false`. | `commands/normalization.json` |
| Final leaf build `normalization-final` | `build RMQ.Core.WordRAM.Bitvector.Normalization` | 18.939 s | 0; all proofs/controls passed without Lean warnings. Material rerun cause: simplified `normalize_false` to remove both warnings. | `commands/normalization-final.json` |
| Exact-type and trust `normalization-axioms` | `env lean <temporary-directory>/bv1-normalization-exact-types.lean` | 11.490 s | 0; explicit rank/select projections passed; all ten requested axiom reports printed; no warnings or stderr. | `commands/normalization-axioms.json` |

Every runner result recorded `TimedOut=false`, `OutputLimitExceeded=false`,
`TerminatedIds=[]`, and empty subprocess stderr. The wrapper emitted only the
existing Git global-ignore access warning before each run; this did not affect
Lean or the recorded exits. No new replay runner or mutation campaign was added.

The final import printed:

- `normalize_length`, `rankPrefix_normalize`, `selectFrom_normalize`,
  `select_normalize`, `normalization_semantics`,
  `identity_rank_transport_fails`, and `identity_select_transport_fails`:
  `[propext]`.
- `normalize_numeric`, `normalize_numeric_packet`, and
  `normalize_optional_numeric_packet`: `[propext, Quot.sound]`.

Both full working-tree trust scans from AGENTS returned no matches (normal
`rg` no-match exit 1). `git diff --check` passed; its only diagnostic was the
existing LF/CRLF notice for the lead's concurrently edited `lakefile.toml`.
This leaf did not edit that file. Full builds, final committed-range checks,
strict design checks and the BV-1 exact-commit audit remain owned by the lead.
No broad gate was run for this independent semantic leaf.

Final source identity: `Normalization.lean`, 7993 bytes, SHA-256
`BA10A82917C9914E0BB11F619A15A51CFC65E2C0842C066F372339C77FF5F9D4`.

## Adversarial propositions and remaining consumer

The positive rank proposition universally quantifies `target`, `bits`, and
`limit`, comparing false-rank of `normalize target bits` to target-rank of
`bits`. The rejected identity mutation retains the same quantifiers and result
equality but replaces `normalize target bits` by `bits`.
`identity_rank_transport_fails` proves the negation of that exact mutant, using
`target=true`, `bits=[true]`, `limit=1`. The corresponding select mutation keeps
the same universal target/list/occurrence domain;
`identity_select_transport_fails` rejects it at occurrence zero. These are
retained kernel proofs, not claims based on unrecorded temporary mutations.

Plain-English result: selecting either Boolean can use false-select semantics
after a position-preserving local recoding. The reader can calculate that
recoding from a present numeric reply and its actual length, while preserving
missing replies. Live assumptions are exactly ordinary finite `List Bool`,
natural-number prefix/occurrence conventions and Lean's displayed standard
axioms; there are no readiness, shape, size, correctness or allocation premises.

Named downstream consumer: the lead's generic physical reader and generic
select execution, ultimately
`RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds`. The next skeptical
question is whether that reader computes the normalized packet through charged
primitive transitions on the same counted store. This leaf does not answer
that question; it supplies the exact semantic and scalar formulas the physical
proof must consume. Shared design/workflow/family/digestion entries and commits
are explicitly the lead's responsibility and were not edited by this worker.
