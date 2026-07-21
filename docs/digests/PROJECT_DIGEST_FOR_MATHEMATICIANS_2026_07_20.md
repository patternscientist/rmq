# What this project has built, for mathematicians who do not work on data structures

*Written 2026-07-20. Every claim below is anchored to a checked theorem or is
marked as unproved. Where the project's own documents overstate something, this
document says so.*

---

## 1. The problem

Given a finite sequence of integers `x₀, …, x₍ₙ₋₁₎`, a **range minimum query**
asks: for a range `[l, r)`, which index holds the smallest value? (Ties broken
leftward, so the answer is unique.)

Answering by scanning is `O(n)` per query. Precomputing all answers costs
`Θ(n²)` space. The interesting question sits between: **how little can you store
and still answer in constant time?**

There is a hard floor. The answer depends only on the *ordering* of the sequence,
and the relevant combinatorial structure — the Cartesian tree — is counted by the
Catalan numbers, so `log₂ Cₙ ≈ 2n − O(log n)` bits are information-theoretically
necessary. A structure is called **succinct** when it meets that floor up to a
lower-order term: `2n + o(n)` bits.

The classical result (Fischer & Heun, 2011) achieves `2n + O(n log log n / log n)`
bits with constant-time queries. It is a paper proof.

**This project's object is a machine-checked version of that kind of statement.**
Not the same bound — the difference is discussed in §6 — but the same *shape* of
claim, with every step verified by a proof assistant rather than by a reader.

---

## 2. The object

The construction is a chain of four maps. Each is an ordinary total function; none
carries hidden data.

### 2.1 Sequence → tree

The **Cartesian tree** of a sequence: the root is the position of the leftmost
minimum; the left subtree is built from everything strictly before it, the right
subtree from everything strictly after. Recursion bottoms out at the empty
sequence.

The point of this tree is a reduction that a mathematician will recognise
immediately: **the leftmost argmin of `[l, r)` is exactly the lowest common
ancestor of the two endpoints** in this tree. So range minimum becomes an
ancestry question, and ancestry questions have compact encodings.

One thing worth flagging, because it is unusual and it matters for reading the
theorems. The type of shapes is a **bare binary tree with no invariants**:

```lean
inductive CartesianShape where
  | empty
  | node (left right : CartesianShape)
```

Every binary tree is a well-formed shape. There are no proof-carrying fields.
Well-formedness — being *the* Cartesian tree of some sequence — is a separate
predicate. This matters because it means the encoding theorems below are about
all binary trees, not about a subclass carved out by hypotheses.

The tree universe is not vacuous: every shape is realised by an actual integer
list, and that is proved (`Shape.lean:1075`).

### 2.2 Tree → bit string

The **balanced-parentheses encoding**: traverse depth-first, emit `1` on descent,
recurse left, emit `0` on the matching ascent, recurse right.

```lean
def bpCode : CartesianShape → List Bool
  | empty        => []
  | node l r     => true :: l.bpCode ++ false :: r.bpCode
```

A tree with `n` nodes gives **exactly `2n` bits** — proved by structural
induction (`Shape.lean:51`). This is the `2n` of the headline. Note that it is
*definitional*: the encoding emits two bits per node by construction. It is not
an achievement, it is the choice of encoding.

### 2.3 Bit string → payload

The stored object is `bpCode` followed by four index tables:

```
payload = bpCode ++ accessTable ++ closeTable ++ fringeTable ++ selectChunkTable
```

The tables exist because reading the answer out of a raw parenthesis string
requires navigation — finding the match of a given parenthesis, counting
parentheses in a prefix — and doing that in constant time requires precomputation.
The tables *are* the `o(n)` term.

### 2.4 Payload → machine words

The bit string is chopped into fixed-width words. A theorem confirms that
concatenating the words returns the payload exactly, so the word view adds no
hidden storage (`ReviewerPhysical.lean:829`).

---

## 3. What is proved

### 3.1 The main theorem

Informally: **there is a function `overhead : ℕ → ℕ` which is `o(n)`, such that
for every finite integer sequence:**

- the stored bit string has length **at most `2n + overhead(n)`**;
- every query costs **at most 210** (see §4 — this number does not mean what it
  looks like);
- invalid ranges return nothing;
- valid ranges return **exactly the leftmost argmin**;
- the whole execution reads from **one query-independent flat bit store**.

Quantification is universal over all integer lists and all index pairs. **There is
no size threshold, no restriction to a family of shapes, and no hypothesis other
than the two that define a nonempty in-range query.** This was checked
specifically, because a hidden size premise is the most common way such a theorem
gets weaker than it looks: the underlying cost lemma has zero hypotheses, and the
one place a size premise does appear deeper in the development is off the live
path and discharged by case analysis rather than assumed.

**What the theorem does not say.** It is an inequality, not an equality. **Nothing
claims the structure attains `2n + o(n)`** — only that it is bounded by it. There
is no tightness or optimality claim about the construction, and a search for such
language finds none.

It also says nothing about the cost of *building* the structure. The classical
result claims linear-time construction; this project claims nothing about
construction at all.

### 3.2 The `o(n)` predicate

```lean
def LittleOLinear (f : Nat → Nat) : Prop :=
  ∀ scale : Nat, 0 < scale →
    ∃ threshold : Nat, ∀ n : Nat, threshold ≤ n → scale * f n ≤ n
```

This is the standard `∀ε>0 ∃N ∀n≥N, f(n) ≤ εn`, with `scale = 1/ε` ranging over
positive integers — cofinal in the positive reals, so no strength is lost. It is
the only definition of that name in the repository. **This part is clean and
requires no caveat.**

### 3.3 The machine

The above describes an abstract model. A natural objection is that the model might
be a fiction — that "cost" is a number attached to a mathematical object with no
operational meaning.

The answer is a theorem, and it is stronger than the project's own documents
advertise. For every integer list and every valid range, a fixed **5,646-instruction
small-step machine**, run against the structure's own bit store:

- **halts**;
- outputs **the same answer** as the abstract construction;
- produces a read log that is **positionally the same list** as the abstract
  trace — element by element, not as a set or multiset;
- performs a number of memory reads **equal** — not merely bounded by — the
  abstract cost.

Separately, the machine's step count is **at most 11,886** on every shape and
every query, unconditionally.

So the abstract model is not a fiction. A concrete machine realises it exactly.

### 3.4 The lower bound

There is also a converse: **any exact fixed-length encoding of the RMQ state needs
at least `2n − 1.5·log₂(2n+1) − 1.5` bits.** The logarithmic coefficient is
exactly right against `log₂ Cₙ`; about two bits of additive constant are given
away.

Two restrictions, both of which the project's own naming obscures. First, the
quantification is over **fixed-length encodings only** — every shape of size `n`
must encode to exactly the same number of bits. Variable-length and prefix-free
codes are not covered. Second, the theorem's witness at `2n` bits is a **trivial
structure** that stores the tree code and answers by linear scan. So the sandwich
closes tightly against *that*, not against the succinct construction. A reader who
pairs the word "tight" in the theorem's name with the `2n + o(n)` upper bound will
infer something that is not proved.

---

## 4. The cost model, which is the subtlest thing here

The number `210` is the most misreadable object in this project, and the
misreading is natural.

**What is counted.** The model records an execution as a list of events, and cost
is the length of that list. The event vocabulary has exactly four constructors,
and — this is the crux — **none of them is arithmetic, comparison, branching, or
dispatch.** The only events are memory reads and two in-word primitives.

The consequence is stated outright in the source, in the form of a theorem that a
mathematician will find startling:

```lean
@[simp] theorem map_cost (f : α → β) (x : Costed α) : (map f x).cost = x.cost
```

**An arbitrary function applied to a costed value costs zero.**

So the correct reading is: **210 bounds memory accesses, not operations.** It is a
statement in the style of I/O complexity — how many times the algorithm reaches
into the stored bit string — not a running-time bound. Asserting "constant query
time" on the strength of 210 alone would be wrong, and the source says so.

**This is what the machine is for.** The 11,886 bound counts *instruction steps*
on a concrete machine where arithmetic and branching are not free. The two numbers
are not comparable and no theorem relates them; what is proved is that the *same
execution* admits both descriptions. **Together** they support "constant query
time." Neither does alone.

One refinement: on the live route the trace collapses to memory reads only, so the
two in-word primitives — which would otherwise be unit-cost assumptions smuggled
into the model — do not occur.

**Word width.** The machine word is `Θ(log n)`, as the transdichotomous model
requires. But the theorem carrying that name proves only the upper direction, with
a factor of 20 of slack and a ~19-bit additive constant. A sentence asserting
`w = Θ(log n)` and citing it covers only the `O`.

---

## 5. How it got here

*This section is the most credible content in the project, because it is mostly a
record of the project proving itself wrong.*

The design-decision log runs to 176 dated entries over **twelve calendar days**,
119 of them on a single day. The project is about five weeks older than its own
record, and that earlier period is not recoverable.

### The constant that got worse on purpose

The headline cost has taken these values in order:

`196727` → `65585` → `4144` → `328` → `76` → `142` → `207` → `210`

The natural reading — four improvements, then three regressions — is exactly
backwards, and understanding why is most of understanding the project.

The **decreases are accounting corrections**. The first summed the costs of
branches the algorithm takes mutually exclusively. Later ones came from a sharper
bound, then from rebuilding the structure so one uniform procedure handles all
sizes, then from measuring the actual machine rather than a conservative envelope.

The **increases are not corrections at all.** Nothing was found to be wrong. What
changed is what the model charges for:

- `76 → 142`: a subroutine extracting a minimum had been free. It stopped being
  free.
- `142 → 207`: two primitives — find the k-th set bit in a word, count set bits in
  a prefix — had been unit-cost *axioms of the model*. They were replaced by
  explicit table lookups, which are themselves charged.
- `207 → 210`: an internal cap moved from 30 to 33, because the recharged
  operation added a read to a branch with **zero slack** — the old cap was exactly
  attained, so the extra read had nowhere to hide.

The number got 2.8× worse while the artifact got strictly more honest. **A
formalization whose numbers only ever improve should be suspected of moving its
goalposts. This one has the opposite problem, which is the better problem.**

### The one genuine mistake

At one point the true value was found to be `213`, not the `210` already frozen
and propagated. The cause was a width fact nobody had checked: at one input size a
stored value needed 15 bits against a 13-bit word, so each access cost two reads.

Two ways out: migrate to `213`, or tighten the width so one read suffices. The
project tightened, and the recorded reason is about the historical record rather
than about cost — a retired constant must have been *true once*, and `210` had
never described a real machine. The width bound turned out to have been "slack by
construction, not by necessity."

### The pivot

The largest change came from a **kernel-verified impossibility proof**. The target
had been: a machine with a familiar instruction set, simulating the query, with a
single step bound valid at every input size. A worker proved that target
unprovable *because false* — for any proposed bound, one can construct an input
whose inner loop exceeds it.

The proof is of a *conjunction*: an all-size literal step cap and an unbounded
local-iteration count cannot coexist. So the repair could not be to weaken the
bound; it had to **eliminate the clause's subject**. The composite instructions
hiding the unbounded loop were removed and replaced with charged table lookups.

The obvious alternative — add a bespoke one-step instruction that does the
expensive thing — was considered and rejected in writing, as "exactly the
precedent-free justification the project goal minimizes."

### The pattern that recurs

A dozen times, a hypothesis that looked merely *unproved* turned out to be
*unsatisfiable where it was meant to be used*. The record's own diagnosis:

> a premise that is merely UNPROVED and a premise that is UNSATISFIABLE look
> identical at the definition site, and both look like diligence.

One instance shows how an honest process still admits a defect. A lemma assumed
two memory images agreed at every address, and someone had supplied a genuine
satisfiability witness. But the witness was a store holding *one* table — exactly
the case where the assumption is harmless. In the real setting the store is a
concatenation, so past the end of one table it still answers, with the next
table's contents. Evaluated at the smallest input, the assumption was wrong about
twenty-nine addresses.

The lesson recorded was not "check assumptions." It was that satisfiability and
vacuity are the same question asked from opposite ends, and answering only one is
what lets both defects through.

### Three transferable rules

**No output is not evidence.** A script writing a proof file hit an encoding error
on a mathematical symbol *after* opening the file, truncating it to zero bytes. An
empty file of this kind compiles silently and successfully; several subsequent
"green" runs were vacuous. Rule: absence of error is inconclusive until the
input's byte count is checked.

**A proof can be vacuous and still compile.** The response was to demand, for each
accepted claim, evidence that a deliberately broken version is *rejected* — after
discovering a case where the acceptance test and the rejection test used different
predicates.

**Make properties structural, not claimed.** The reference implementation used to
check the machine was moved into a module with no import lines at all.
Independence stopped being an assertion and became a fact about the file, because
"only reviewer attention stood in the way, and this campaign has repeatedly found
that reviewer attention is the weakest link available."

---

## 6. Where this sits relative to existing work

The design-decision record — 9,899 lines — contains **zero** occurrences of "prior
art" or "novelty". The competitive question was first asked on 2026-07-20, and the
answer was uncomfortable.

**Succinct structures have been mechanized before.** Tanaka, Affeldt and Garrigue
(ICFEM 2016) formalized Jacobson's rank structure in Coq, extracted running OCaml,
and benchmarked it. Their abstract: *"To the best of our knowledge, this is the
first application of formal verification to succinct data structures."* A follow-up
(ITP 2019) formalized succinct trees and proves an encoding occupies exactly
`2n − 1` bits.

So two claims are unavailable, and this project does **not claim** either of
them: priority over the earlier Coq mechanizations of succinct structures, and
originality for the exact `2n` encoding theorem, which already exists.

**What has not been done is the asymptotic step.** Across three papers and both
resource axes, that line mechanizes *exact closed-form quantities* — directory
sizes, encoding lengths, counts of bits examined — and takes every asymptotic step
in prose. The relevant sentence in ICFEM 2016 sits immediately after a Coq lemma:
*"When n is large, we observe that m ∼ p, thus the whole expression is
asymptotically equal to n/log₂n, as desired."* That inference is the reader's, not
the proof assistant's. Searching their artifact for asymptotic vocabulary returns
nothing, and the 2019 conclusion states that a framework for space and time
complexity remains to be defined.

The surviving novelty is therefore about **method**: a machine-checked `∀ε ∃N`
statement rather than an exact formula plus a human's asymptotic reading of it. Two
further differences are checkable rather than rhetorical — the prior development
declares twelve axioms where this one declares none beyond Lean's own, and neither
prior work mechanizes a cost model at all.

A forward citation search establishes that this line **stopped**: the complete set
of works citing either paper is three of the same group's own follow-ups and three
unrelated papers. No mechanized range-minimum structure of any kind was found in
any proof assistant.

**One word to avoid: "end-to-end."** There is no theorem here about the cost of
building the structure, and the prior work extracts and runs real code. On that
axis the earlier work goes further.

---

## 7. What is weak

**Nothing has been externally audited at the current state.** Blind audits exist,
but they belong to the era when the constant was `76`; it has moved twice since.
Every claim after the pivot is self-certified.

**The `o(n)` term dwarfs the `2n` term at every size that will ever exist.** This
is the most serious issue, and it is arithmetic rather than opinion. Modelling the
definitions exactly gives `overhead(n) / 2n ≈ 6600` at `n = 10³`, ≈ 7100 at `10⁶`,
≈ 4900 at `10⁹`. The crossover where the "lower-order" term is genuinely lower
order requires roughly `n > 2^(2^512)`. **The theorem is true and the asymptotic is
real, but "2n + o(n)" will mislead anyone who assumes the `o(n)` is small.**

Three qualifications, all of which matter:

1. It is an **upper bound with no matching witness**. Nobody has shown the actual
   structure ever attains that envelope, so the gap may be an artifact of the
   analysis rather than a property of the object. Settling that is a concrete open
   question: exhibit a family of inputs on which the structure really is that
   large, or tighten the analysis.
2. The single worst component has now been **proved empty for every input below
   `2⁹⁶`** — that is, on every input that can physically be constructed. It is
   required for the all-size statement and inert at all reachable sizes.
3. The parameters were chosen for **provability, not for the structure being
   good**. One bound charges 512 where about 3 is true. Individually defensible;
   collectively they are why the envelope is so much larger than the thing it
   bounds.

Point 2 deserves a comment rather than a defence. It is an odd property for a data
structure to have, and the honest description is that the all-size statement
quantifies over sizes nobody will reach and the component exists to make it true
there. **It is also a fact only formalization would have surfaced** — an informal
treatment would never have noticed that one of its components is dead at every
practical size.

**No construction-time or construction-space theorem exists.**

**Four specific defects found while writing this document**, all now recorded:
the "two-sided" capstone theorem uses a *different* overhead function from the
headline upper bound; that same two-sided theorem is arithmetically vacuous, its
content following from `4n ≤ 4n` regardless of any Catalan estimate; no theorem
composes the machine result with the 210 bound, so the sentence "the machine
performs at most 210 charged reads" is nowhere stated despite both halves being
present; and a paper-facing document still advertises the retired constant `142`.

**A naming caution.** The module called "model adequacy" contains 39 fields, and
**not one mentions a machine, an instruction, or a step.** It establishes that the
cost model does not cheat — cost equals trace length, every event is real, reads
match the store. That is valuable and it is not the same as faithfulness to a
machine. The machine-faithfulness claim lives elsewhere and is the one to point at.

---

## 8. Summary judgement

What is genuinely established: a machine-checked succinct RMQ structure over
arbitrary integer lists, with a correct leftmost-argmin contract, a standard
`o(n)` space statement, a memory-access bound of 210, and — unusually — a concrete
small-step machine proved to realise the abstract model exactly, positionally, and
without axioms.

What is not established: that the space envelope is tight or competitive; that the
structure can be built efficiently; that the query is constant-*time* in any sense
stronger than the conjunction of the two bounds in §4; and, until an external audit
happens, that any of the above survives adversarial reading by someone who did not
write it.
