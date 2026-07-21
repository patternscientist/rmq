# E1 architecture: deep dive and final judgement

**FOR A CODEX INSTANCE ON A DIFFERENT MACHINE, WITH NO LOCAL FILESYSTEM ACCESS
BUT FULL ACCESS TO THE PUBLIC REPOSITORY ON GITHUB.** Everything below the
`## PASTE BELOW` marker is the prompt. Text above the marker is launch metadata.

## Launch metadata (do not paste)

- Recipient has **no local filesystem access**, but the repository is **public**
  and both relevant branches are now pushed. They can and should **clone and read
  the actual architecture** — this is an architecture judgement and cannot be made
  from quotations alone.
- Source facts remain quoted inline as a *guide to where to look*, with
  provenance marked, so they can spot-check the coordinator's reading rather than
  inherit it.
- A big redesign is explicitly authorised as an outcome by the project owner.

---

## PASTE BELOW

# E1 word-RAM machine: architecture deep dive and final judgement

You are being asked for a **final architecture judgement** on a component of a
Lean 4 formalization, plus whatever literature research you need to ground it.

## READ THE ACTUAL ARCHITECTURE — this is not a summary exercise

The repository is **public**. Clone it and read the real development. **A
judgement of this kind cannot be made from quotations**, and the quotations below
are a guide to where to look, not a substitute for looking.

```
git clone https://github.com/patternscientist/rmq.git
cd rmq
git checkout 8e7e3ee5bf44413fca0baace9aa565a4bb644109   # the E1 candidate
```

- **E1 candidate (the architecture under judgement):** branch
  `claude/b1-b2-charged-fringe-tables`, commit **`8e7e3ee`**.
- **Coordinator analysis** (round logs, the project digest, this prompt): branch
  `claude/rmq-formalization-coordinator-bd7045`.

**What to read, in rough order of importance:**

| What | Where |
|---|---|
| The machine: ISA, `RegFile`, `execInstr`, `FieldsFit`, `ProgramFits` | `RMQ/Core/WordRAM/E1Machine.lean` |
| The executed program and its assembly | `RMQ/Core/WordRAM/E1WholeQueryProgram.lean`, `E1WholeQueryCloseLca.lean` |
| The agreement theorem (what E1 actually proves) | `RMQ/Core/WordRAM/E1WholeQueryAgreement.lean` |
| The width development (the defective bridge) | `RMQ/Core/WordRAM/E1ReviewerWidth.lean`, `E1WholeQueryPathWidth.lean`, `E1CanonicalInteriorWidth.lean` |
| The interior dispatch — 4204 executed instructions | `RMQ/Core/WordRAM/E1InteriorDispatchCompose.lean` and `E1Interior*.lean` |
| The rejected alternative machinery | `RMQ/Core/WordRAM/Register.lean` |
| The frozen acceptance contract | `docs/internal/E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md` |
| The abstract cost model E1 must agree with | `RMQ/Core/WordRAM.lean`, `RMQ/Core/Cost.lean` |
| Public claims | `RMQ/Headlines/RMQ.lean`, `RMQ/Core/SuccinctRMQClassic.lean` |

The whole `RMQ/` tree is ~216 files / ~170k lines; the `E1*` files are the
relevant subset. Build if useful: `lake build RMQ` (Lean 4, no Mathlib).

**Treat this document as evidence from a party with a known error rate, not as
ground truth.** Provenance is marked below so you can spot-check rather than
inherit. Where the coordinator's reading and the source disagree, **the source
wins and we want to know.**

**Provenance is marked throughout:**
- **[READ]** — quoted directly from source by the coordinator writing this.
- **[SCOUT]** — established by a subagent that read source; the coordinator
  spot-verified the load-bearing parts, noted where.
- **[INFERRED]** — reasoning, not reading.

Honest calibration: in this session the coordinator made ~6 claims that turned
out false and were caught by reading source, and one scout confidently analysed
the *wrong program* before being redirected. Distrust accordingly.

---

## 1. The governing goal

The project's north star, in the owner's words: obtain the strongest version of
this work with **"technically justifiable but reviewers have to spend brainpower
auditing the justification as opposed to pattern matching against precedent"
MINIMIZED.**

That phrasing is the decision criterion for everything below. An option that is
technically superior but forces a reviewer to audit a bespoke justification may
lose to an option that is slightly weaker but instantly recognisable.

**A large redesign is explicitly on the table.** The owner has authorised it if
it is genuinely the best option. Do not anchor on the incremental repair because
it is cheaper — say so if a redesign is right.

## 2. What the project is, and what E1 is

The project mechanizes a **succinct range-minimum-query (RMQ) structure** in
Lean 4, with no Mathlib and no `sorry`/`axiom`/`native_decide`.

Given a list of integers, it builds a Cartesian tree, encodes it as a
balanced-parentheses bit string of length exactly `2n`, appends four index
tables, and answers "which index holds the leftmost minimum of `[l, r)`" by
reading from that flat bit payload. Headline claims: payload length
`≤ 2n + overhead(n)` with `overhead` proved `o(n)`; and a **query cost bound**.

**E1 is the reference word-RAM machine.** Its purpose is to make the cost claim
operational rather than definitional — to show a real small-step machine
executes the query with the claimed number of memory reads, rather than the cost
being a number attached to an abstract object.

### The two constants — not the same quantity

- **`210`** bounds **charged memory reads** in the route's trace. Algebra:
  `2*35 + (2*11 + 2*37 + 33) + 11 = 210`. **[READ]**
- **`11886`** bounds **machine steps** of the E1 program. Separately derived.
  **[READ]**

No theorem relates the numerals. The source states this explicitly in two
places. **[READ]**

### Why the cost model is unusual, and why E1 exists

The trace event vocabulary has exactly four constructors and **none of them is
arithmetic, comparison, or branching** — so those operations are free in the
cost model. There is a theorem `map_cost (f : α → β) (x : Costed α) :
(map f x).cost = x.cost`: an arbitrary function applied to a costed value costs
zero. **[READ]**

So `210` counts *memory accesses*, not operations — an I/O-complexity-style
statement, not a running-time bound. **E1's `11886` step bound is what closes
that gap**: on a concrete machine where arithmetic and branching are not free.
Together they support "constant query time"; neither does alone.

## 3. The E1 machine as it exists today

### The instruction set — 12 constructors **[READ]**

```
readMem (dst segment addrReg : Nat)   -- R dst := decode(store[segment][R addrReg]); emits a read event
const   (dst value : Nat)
move    (dst src : Nat)
add     (dst src₁ src₂ : Nat)         -- R dst := R src₁ + R src₂
sub     (dst src₁ src₂ : Nat)         -- truncated Nat subtraction
mulConst(dst src k : Nat)             -- R dst := R src * k
divConst(dst src k : Nat)             -- R dst := R src / k
natLt / natLe / natEq (dst src₁ src₂) -- R dst := if ... then 1 else 0
brNZ    (cond target : Nat)           -- if R cond ≠ 0 jump to absolute index target
halt
```

`execInstr` is a **single non-recursive `match`**; only the outer `run` loop
recurses, on a fuel counter. It returns `State × Category × Option TraceEvent` —
the `Option` means a step emitting two events is *untypeable*. **[READ]**

### The register file **[READ]**

```lean
-- RMQ/Core/WordRAM/E1Machine.lean:55
def RegFile := Nat → Nat
```

**Unbounded natural numbers.** `sub`'s docstring says truncated subtraction is
chosen as "matching the route's `Nat` arithmetic" — the machine was deliberately
built to mirror the abstract route's `Nat` semantics.

### What the machine proves **[READ]**

The agreement theorem (`E1WholeQueryAgreement.lean:111`): for every integer list
and every valid range, the program run against the structure's own bit store —

- **halts**;
- `decodePacket (final.regs regOut) = (queryCosted xs left right).value` — same answer;
- produces a read log **positionally equal** to the route's trace (element by
  element, not as a set or multiset);
- `catCount cats .memoryRead = (queryCosted xs left right).cost` — read count
  **equal**, not merely bounded.

Plus `≤ 11886` steps, unconditionally, all shapes and queries.

## 4. THE DEFECT

An external audit found, and its coordinator confirmed, the following.

### The width predicate bounds encoded fields, not runtime values **[READ]**

```lean
-- RMQ/Core/WordRAM/E1Machine.lean:536
| .readMem dst segment addrReg =>
    dst < 2 ^ w ∧ segment < 2 ^ w ∧ addrReg < 2 ^ w
```

`addrReg` is the **register index**. But execution reads the register's
**contents**:

```lean
-- RMQ/Core/WordRAM/E1Machine.lean:164
| .readMem dst segment addrReg =>
    let address := s.regs addrReg
    let word? := store.readWord? segment address
```

Since `RegFile := Nat → Nat`, nothing bounds `s.regs addrReg`. Kernel-checked
counterexample: `.readMem 0 0 0` satisfies `FieldsFit w` while register 0 holds
`2^w`, so the emitted read address is `2^w`, not `< 2^w`.

### The frozen invariant names a bridge that does not exist **[READ]**

Acceptance matrix, line 83, verbatim:

> `INV-ADDRESS-WIDTH | Every executed address/operand (including guard
> comparisons and dead branches) fits the modeled word width via REQ-E1-02's
> exhaustive predicate. | Open`

Two things matter. It demands **every executed operand** — not just addresses,
also comparison inputs and dead-branch machinery. And it names REQ-E1-02's
predicate (`FieldsFit`) as the mechanism, **which is exactly the false bridge**.

**Its status is `Open`, not `Satisfied`.** No acceptance ever rested on it. The
matrix did not lie; the rung did not meet its contract.

### Severity assessment **[INFERRED, coordinator]**

- **Nothing false was accepted.** Every existing theorem — value agreement,
  positional receipt equality, `210`, `≤ 11886` — is **true** under the current
  `Nat` semantics, and none depends on the address-width invariant.
- **The fix is additive.** Nothing gets un-proved.
- What is missing is the **word-RAM interpretation**: the claim that registers
  fit in `Θ(log n)` bits, i.e. that this is a machine rather than an unbounded
  register machine that happens to compute the right thing.

## 5. What two scouts established

### Scout A: does the canonical run ever overflow? **NO** **[SCOUT]**

*(First pass analysed the wrong program — `assembledValidPath`, whose interior
hole is `[]` and which appears only in width files. The coordinator caught this
against source: the executed program threads a **4204-instruction** interior
dispatch. Redirected; the verdict below is the corrected pass.)*

**[READ, coordinator-verified]** The executed program:
`wholeQueryProgram = programSkeleton n (wholeQueryValidPath shape noneExit)`;
`wholeQueryValidPath → closeLcaProgramAt → closeLcaCrossArm`, which threads
`canonicalInteriorDispatchBlock shape (A + 4 + 176)` — **length 4204** — into
the cross-block arm. The cross arm is 4574 = 370 + 4204, so the interior is the
bulk of it.

**[SCOUT]** Over the whole executed program, every value-growing instruction
(`add`, `mulConst` — `sub`/`divConst` only shrink) falls into one of five safe
families:

1. **floor-realign** `⌊x/k⌋·k ≤ x`;
2. **`(v/D)·M ≤ v`** where `M ≤ D` by domain definition;
3. **big-endian Horner** reconstruction — max intermediate = the final
   reconstructed value;
4. **`index·stride`** yielding a bounded address/slot/position;
5. **`base + offset`**.

**Neither dangerous pattern occurs anywhere**: no capacity-scale value
multiplied by `k ≥ 2`, no `address + address`. Max register value is `O(size)`
(value-slopes `≤ ~17`); the capacity envelope is `400000·(n+1)`, slope 400000.

`deadAddress` — emitted as a read event **regardless of read success** — is
**proven** `< capacity` (`deadAddress_le`, `deadAddress_lt`,
`E1CanonicalInteriorWidth.lean:138,146`; coordinator verified these theorems
exist).

### The one load-bearing gap, verified absent **[SCOUT + coordinator-verified]**

The verdict is a **derived** result, not a checked invariant. Most interior
products reduce to already-proven width lemmas. But the sharpest site —
`mulConst tP sBlock blockSize` (`E1InteriorMinCandidate.lean:237`) — is linear
**only because** the decoded argmin offset is `< macroSize`, i.e.
`sBlock ≤ blockCount`. On loose bounds it would be `8·size²` — quadratic,
exceeding capacity for `size > ~50000`.

**The coordinator grepped for this bound and it does not exist as a checked
theorem.** So one nameable lemma would make the whole thing unconditional:

> `decodedInteriorCell < capacity` on the canonical store
> (equivalently `sBlock ≤ blockCount`, `levelCell < levelCount·D`)

Every interior product then reduces to it plus the proven width bounds.

**[INFERRED]** If that lemma were *false*, the route's own argmin correctness
would be broken — which is heavily tested elsewhere — so the risk it is false is
low. But it must be **proved**, not assumed.

### Scout B: is there reusable overflow machinery? **NO — REBUILD** **[SCOUT]**

`RMQ/Core/WordRAM/Register.lean` (39KB) defines `NatValuesFitInBits`, a `NatExpr`
arithmetic algebra, and `NatExpr.NoOverflow` with preservation lemmas. It is
**not usable** for E1:

- Its `RegFile` is an **`Array`-backed structure** with typed banks; E1's is
  `Nat → Nat`. Different types, no conversion. **No E1 file imports it.**
- **The two operations that matter are punts.** `add_noOverflow_of_eval` and
  `mul_noOverflow_of_eval` take the result-fit **as a hypothesis** and only
  rewrite `eval`. Zero content exactly where overflow would happen.
- The lemmas that do close (`sub`/`div`/`min`) are one-line `Nat` monotonicity
  facts, cheaper to inline than to reflect through `NatExpr`.

The certificate must instead reuse **E1's own capacity-envelope machinery**
(`lt_capacity_of_le_linear`, `WordAddressesStructure`, the proven width bounds).

## 6. The options as currently understood

**Option 1 — Intrinsic bounded words.** Registers become `Fin (2^w)` or a
width-indexed word type; arithmetic closed at width `w` with explicit wrapping;
conversion to `Nat` only at memory lookup. Boundedness is definitional.

*Concern raised:* the route computes in `Nat`. Wrapping semantics means machine
arithmetic no longer definitionally equals route arithmetic, so every
correctness theorem acquires a no-wrap side condition — unless a single
no-overflow bridge theorem discharges it once. Also `w = shapeWidth shape` is
shape-dependent, so the register *type* depends on a computed width — dependent
typing in a Mathlib-free development where `omega` is the workhorse and does not
reason about `Fin`.

**Option 2 — `StateFits w` on `Nat` registers.** Keep `Nat`; add a fit
predicate; prove it for the initial state and preserved by every step.

*Established defect:* as a **blanket** claim over arbitrary `ProgramFits`
programs this is **false** — values `< 2^w` are not closed under `Nat` addition
or multiplication. It is only sound as a statement about the **canonical run**.

**Option 3 — Two-layer (the current converged position).** Keep the `Nat`
machine as the proof-friendly reference interpreter. Additionally define a
conventional bounded-word machine. Prove a canonical-run fit certificate, then
**one whole-run refinement theorem** transporting final output, ordered read
log, category log, `210` reads and `11886` steps. The public theorem exhibits
the bounded machine; no caller-supplied fit premise.

**Option 4 — Something else, including a substantial redesign.** Explicitly in
scope. See §8.

## 7. The coordinator's current recommendation, and its weak points

**Recommendation: Option 3, sequenced — fit certificate first, then the bounded
machine and bridge.**

Reasoning:
- The certificate is **mandatory under every option** and is the real work.
- Scout A says **no overflow exists**, so the exact simulation into `Fin (2^w)`
  is observation-preserving. The bounded machine is **buildable**; no arithmetic
  repair and no width widening are needed.
- Under the north star, `Fin (2^w)` registers pattern-match as a word-RAM
  machine where "`Nat` registers plus a 200-line invariant" does not.
- `210` is a route-trace theorem and is **never at risk**; what is at stake is
  transporting it onto a bounded machine.

**Where this recommendation is weak, stated honestly:**

1. **Nobody has priced the second machine.** "Build a bounded word-RAM and prove
   whole-run refinement" is one sentence hiding possibly a large amount of work
   in a Mathlib-free setting.
2. **The `Fin` + dependent-width concern was raised and never resolved** — only
   set aside because the certificate comes first either way.
3. **The deeper question was never asked: is E1 at this ambition level the right
   investment at all?** E1 is the single most expensive component of the project
   (119 design-decision entries on one day, ~25 parallel work lanes). It is now
   revealing a category of gaps — static certificates taken to imply dynamic
   properties — that will cost more to close.

## 8. What we need you to determine

### The core question

**What should be done with E1, given the north star?** Adopt Option 3 as
described, modify it, or replace it. If a substantial redesign is genuinely best
— including reducing E1's ambition, or rebuilding its machine on a different
foundation — say so plainly and argue it. **Do not anchor on the incremental
repair because it is cheaper.**

### The hypothesis we most want tested

**[INFERRED, and we may be wrong]** There may be no precedent to pattern-match
against here at all. A systematic literature search established that the closest
prior work — Tanaka/Affeldt/Garrigue's Coq succinct-structure line (ICFEM 2016,
JIP 2018, ITP 2019) — **does not machine-check a cost model at all**. ICFEM
benchmarks running extracted OCaml; ITP 2019 argues constant time informally
from "a constant number of rank and select operations"; JIP 2018 proves exact
bit-examination counts in Coq but takes the `O(n)`/`O(1)` step in prose, using
"bits examined" as a domain proxy rather than a machine model.

If that is right, then **for the cost-model claim specifically there is no
precedent shape to match**, and the north star's "pattern-match against
precedent" lever may be partly unavailable — we are in "justify it" territory
regardless of which option we choose. That would change the calculus: if a
reviewer must audit the justification either way, the cheaper and more
transparent option may beat the more impressive one.

**Test this.** If instead there IS a recognised formal word-RAM model that
reviewers would pattern-match, that is decisive in the other direction, and
aligning E1 with it may be the redesign worth doing.

### Research directions

1. **Is there a standard, recognised formalized word-RAM (or RAM) machine model
   in any proof assistant** — Lean/Mathlib, Coq/Rocq, Isabelle/AFP, HOL4, ACL2 —
   that E1 could align with or instantiate? Complexity-theory formalizations,
   cost-instrumented semantics, resource-aware program logics. If one exists and
   is recognised, aligning with it may beat any bespoke design.
2. **What machine model do succinct-structure and algorithm-verification papers
   actually assume**, and how do they justify constant-time claims? What does a
   referee in that community expect to see?
3. **Is "registers are `Nat` with a proved bound" vs "registers are `Fin (2^w)`"
   a distinction this literature cares about**, or is it invisible at review
   level? This is the crux of Option 1-vs-2 and we are guessing.
4. **How do existing formalizations handle the transdichotomous word-RAM's
   `w = Θ(log n)` dependence** — where the word width depends on the input size?
   That is precisely what makes a bounded register type dependently-typed here,
   and it is the main technical objection to Option 1.
5. **Cost-model precedent**: is counting *memory accesses* (our `210`) rather
   than operations a recognised model with a name a reviewer knows (I/O
   complexity, cell-probe, external memory)? If our `210` is really a
   **cell-probe** bound, saying so may buy more recognition than any machine
   work — cell-probe is a standard model with its own literature.

**Point 5 may be the highest-leverage item in this document.** If the cost claim
can be stated in an existing named model, the machine's job shrinks.

### Specific questions to answer

1. **Adopt, modify, or replace Option 3?** Concrete recommendation.
2. **Is the two-layer approach worth its cost**, or does the fit certificate on
   the `Nat` machine already deliver enough — given that we must justify rather
   than pattern-match either way?
3. **Is the dependent-width `Fin (2^w)` concern real** in a Mathlib-free Lean 4
   development, or overstated?
4. **Should E1's ambition be reduced?** Is there a smaller object that delivers
   most of the reviewer value?
5. **Would aligning with an existing formal machine model be better** than either
   option, and is a suitable one available?
6. **What must be true for the `210`/`11886` pair to be defensible** as a
   constant-query-time claim, and does the current or proposed architecture
   deliver it?
7. **Sequencing and gating** — what must be proved before anything else starts.
8. **What could still be wrong** in the picture above that we have not
   considered, given that we cannot see what you can research.

## 9. Constraints that do not move

- No `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe`,
  `implemented_by`. **No Mathlib** — `set`, `norm_num`, `by_contra`, `ring`,
  `nlinarith`, `interval_cases` do not exist; `omega` atom-abstracts products.
- No asserted constants; every literal derived.
- Frozen requirement text is never edited — amendments require owner approval.
- **The repair must not add a caller-supplied "all runtime values happen to fit"
  hypothesis.** Any invariant must be intrinsic to the accepted construction or
  derived from its canonical initial state and transition semantics.
- Claims must not be weakened to make them provable.

## 10. Output

1. **Your recommendation**, stated first, in a sentence.
2. **The reasoning**, including where you disagree with §7 and why.
3. **Research findings** — every literature claim with a citation you actually
   retrieved. Mark verbatim quotations with page numbers. **Search snippets
   fabricate plausible citations; do not rely on them.**
4. **Answers to the eight questions in §8.**
5. **A frozen repair contract** if you can specify one: what gets proved, in
   what order, what the public theorem says at the end.
6. **What you could not determine**, and what you would need.

Where you rely on a fact from this document that you could not verify, say so —
it may be wrong, and several things in it have already been corrected once.

**Finally: you can read the source, so read it.** If your judgement rests on how
the architecture is actually shaped — how the program is assembled, how the width
development is structured, how much of the tree a change would touch, whether the
ISA is the right one — those are answerable by reading `8e7e3ee`, and an answer
grounded in the real development is worth far more than one grounded in this
summary. Two specific things worth forming your own view on, because the
coordinator's account of them is the least verified part of this document:

1. **How much would each option actually cost?** Nobody has priced the second
   machine, or a redesign. You can see the tree; estimate it.
2. **Is the ISA right?** Twelve constructors, `Nat` registers, one non-recursive
   `match`, `Option TraceEvent` so two events per step is untypeable. If a
   different machine shape would be both more recognisable and cheaper to prove
   about, that is exactly the redesign we are asking you to consider.
