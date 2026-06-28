# Deep Project Digestion: 2026-06-28

**Audience.** A mathematically mature reader -- say, a math PhD -- who knows what a
theorem prover is and can read a Lean signature, but who is *not* assumed to know
any data-structures vocabulary: not RMQ, LCA, Cartesian tree, rank/select,
balanced parentheses, succinctness, the word-RAM model, amortized analysis, or
union-find; and not the formalization slang either: monad, payload, refinement,
proof-only field, trust base. Every such term is explained before it is used.

**Status.** This describes `main` at `da19fb3` on 2026-06-28. It is a *teaching* document.
The Lean source, the build, and the `#print axioms` scripts are the source of
truth; where this prose and the Lean disagree, the Lean wins.

**How to read it.** Part I is the mathematical story (the RMQ theorem and its
matching lower bound). Part II is the modeling vocabulary you need to read the
claims *honestly* -- what "cost" means, what is and isn't counted. Part III is the
shared toolkit and the three newer spokes. Part IV is the candid status: what is
proved, what is explicitly not, and the open frontiers. A literature map and a
skeptical-questions section close it out.

---

## 0. One paragraph

This repository is a machine-checked account, in the Lean theorem prover, of a
classic result in data structures: you can preprocess an array of `n` numbers
into a bit-string of `2n + o(n)` bits so that the "where is the minimum of this
sub-array?" question is answered, for *every* sub-array, by a fixed-size
computation -- and `2n` bits is, up to lower-order terms, unavoidable. The project
then reuses the same Lean machinery to start three further verified
data-structure "spokes" (rank/select, balanced-parentheses navigation,
union-find). The unusual feature, compared to a paper proof, is that the
*modeling assumptions* -- what counts as one step, what counts as one stored bit --
are written down as explicit Lean objects and audited, rather than left to the
reader's good faith.

---

# Part I -- The mathematical story

## 1. What problem is being solved

Fix a finite list of integers, say

```
xs = [3, 1, 4, 1, 5]
```

A **range-minimum query** (RMQ) names a contiguous sub-range and asks for the
position of the smallest value in it. This project uses **half-open** ranges
`[left, right)` (includes `left`, excludes `right`) and the **leftmost** tie
rule: if the minimum value occurs more than once, return the smallest index that
attains it. So:

```
query [0, 4)  -> index 1   (values 3,1,4,1; min value 1 first occurs at index 1)
query [2, 5)  -> index 3   (values 4,1,5;   min value 1 occurs at index 3)
```

In Lean (`RMQ/Core/Spec.lean`), a query is *valid* when it is nonempty and inside
the list, and the correct answer is captured by a predicate `LeftmostArgMin`:

```lean
abbrev ValidRange (xs : List Int) (left right : Nat) : Prop :=
  left < right /\ right <= xs.length

def LeftmostArgMin (xs : List Int) (left right idx : Nat) : Prop :=
  left < right /\ right <= xs.length /\
    left <= idx /\ idx < right /\
      exists v, xs[idx]? = some v /\
        (forall j w, left <= j -> j < right -> xs[j]? = some w -> v <= w) /\   -- v is minimal
        (forall j w, left <= j -> j < idx  -> xs[j]? = some w -> v <  w)        -- strictly, to the left
```

Read the two quantified clauses as: the value `v` at `idx` is `<=` every value in
the range (it is a minimum), and it is *strictly* `<` every value to its left
inside the range (so `idx` is the *leftmost* minimum). The file proves this
answer is unique (`leftmostArgMin_unique`): a specification is only useful if it
pins down exactly one correct answer, and this one does.

So far this is only a definition of "the right answer." Computing it once is
trivial: scan the range. The theorem is about something else.

## 2. Why this is a theorem, not a programming trick

The interesting object is not a single answer but a **two-phase data structure**:

1. a *preprocessing* phase that looks at `xs` once and produces some stored
   representation; followed by
2. a *query* phase that, given any valid `[left, right)`, returns the correct
   index using only a fixed, bounded amount of work -- crucially, work that does
   *not* grow with the size of the range.

A naive scan re-reads up to `n` cells per query. The claim here is that after
cheap preprocessing, every query is answered in a bounded number of steps
regardless of how wide the range is, and the stored representation is
astonishingly small. Two things make this a genuine theorem:

- **Optimal-leading-order space.** The representation uses `2n + o(n)` bits,
  where `o(n)` is the usual "grows strictly slower than `n`" notation
  (formally below). And a matching lower bound shows the leading `2n` cannot be
  reduced. So this is not merely "small," it is *leading-order optimal*.
- **You may discard the values.** The representation does not store the integers
  at all. It stores only the *shape* of the array (defined next). Two arrays with
  the same shape have identical RMQ answers for every range. That the comparison
  structure of an array is fully captured by an order-theoretic shape -- and that
  the shape is what RMQ depends on -- is the mathematical content.

The Lean development encodes phase (1)/(2) as an explicit interface so that "an
RMQ implementation" is a precise object, not an informal idea. In
`RMQ/Core/Backend.lean`:

```lean
structure RMQBackend (xs : List Int) where
  State  : Type
  build  : State
  query  : State -> Nat -> Nat -> Option Nat
  sound        : query build left right = some idx -> LeftmostArgMin xs left right idx
  complete     : LeftmostArgMin xs left right idx -> query build left right = some idx
  invalid_none : Not (ValidRange xs left right) -> query build left right = none
```

A `RMQBackend` is "any data structure that provably answers RMQ correctly":
`build` is the preprocessed state, `query` answers, and the three proof fields say
the answers are sound (never wrong), complete (always found), and that invalid
queries are rejected. We call such an interface a **contract**. A pleasant
consequence proved in the file (`queryBuilt_eq`) is that *any two* backends for
the same list give identical answers -- the contract is tight enough to determine
behavior, so the many different implementations in the repo (linear scan, sparse
table, Fischer-Heun-style tables, the succinct one) are interchangeable black
boxes at the contract level. The repository contains many such backends; the
headline one is the succinct backend of Part I, section 4.

## 3. The shape that determines every answer: Cartesian trees and LCA

Given an array, its **Cartesian tree** is built recursively: the root is the
position of the leftmost minimum of the whole array; its left child is the
Cartesian tree of everything to the left of that position, and its right child is
the Cartesian tree of everything to the right. For `xs = [3,1,4,1,5]`: the
leftmost minimum is the `1` at index `1`, so it is the root; the left subtree
comes from `[3]`; the right subtree comes from `[4,1,5]`, whose leftmost minimum
is the `1` at index `3`, and so on.

The **shape** of the Cartesian tree (its branching structure, forgetting the
actual values) is the object the data structure stores. The bridge theorem is:

> The RMQ answer for a range `[left, right)` is the **lowest common ancestor**
> (LCA) -- the deepest tree node that is an ancestor of both endpoints -- of the
> two endpoint nodes in the Cartesian tree, read off with the same leftmost-tie
> convention.

"Deepest" means furthest from the root. The intuition: the leftmost minimum of
any sub-range is exactly the highest (closest to the root) Cartesian-tree node
sitting between the endpoints, and that node is their LCA. Because LCA depends
only on the tree's shape, the integer values are no longer needed once the shape
is known. This RMQ<->LCA correspondence is the classical bridge of Gabow-Bentley-
Tarjan and, in the modern constant-time form, Bender-Farach-Colton (see the
literature map, section 18). The Lean development carries it through explicit
Cartesian-tree, Euler-tour, and rose-tree modules, with the final shape-facing
query theorem assembled in `RMQ/Core/SuccinctFinal.lean`.

## 4. The upper bound: `2n + o(n)` bits, `O(1)` modeled query

To store a tree shape in few bits the project uses **balanced parentheses**.
Any rooted tree with `n` nodes can be written as a balanced string of `n`
opening and `n` closing brackets (visit the root, emit `(`, recurse on children,
emit `)`), i.e. exactly `2n` bits. This `2n`-bit string is the *only* substantial
thing stored. Everything else -- the navigation tables -- is provably `o(n)`.

The public headline theorem has a short alias in `RMQ/Headlines.lean`:

```lean
RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
  := RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
```

Unpacked, for an input of size `n` it asserts a conjunction; the parts that
matter here are:

- **Exact space.** The stored payload has length exactly
  `2*n + overhead n`, where `overhead` is a fixed function proved to be `o(n)`:

  ```lean
  (concreteBPNativeSuccinctRMQPayload accessFamily shape).length
    = 2 * n + concreteBPNativeSuccinctRMQOverhead genericSparseExceptionBPCloseAccessOverhead n
  ```

- **Exactness.** Every valid query returns the same index as the reference scan
  over a canonical representative array of that shape:

  ```lean
  (concreteBPNativeSuccinctRMQQueryCosted accessFamily shape left (left + len)).erase
    = some (scanWindow shape.representative left len)
  ```

  `scanWindow` is the brute-force leftmost-minimum; `.erase` (defined in Part II)
  drops cost bookkeeping and keeps the answer. So this line says: the clever
  succinct query *equals* the reference slow query, on every valid input.

- **Constant modeled query cost.** The same query, measured in the project's cost
  model (Part II), is bounded by a fixed constant independent of `n` and of the
  range width.

The phrase **succinct** means exactly this regime: storing the *information-
theoretic* amount of data (here `2n` bits, plus a sublinear `o(n)` of navigation
overhead) while still answering queries quickly -- as opposed to a fast structure
that uses, say, `O(n log n)` bits. The succinct-tree techniques are due to
Jacobson and to Munro-Raman; see section 18.

### What `o(n)` means here, precisely

`o(n)` is not folklore in this repo; it is a Lean predicate. Overhead functions
`f : Nat -> Nat` are required to satisfy a "little-o of linear" property whose
content is the usual one: for every multiplicative slack you like, `f n` is
eventually below `n` by that factor (equivalently `f n / n -> 0`). A *constant*
function satisfies it, which is fine -- but the headline overhead is genuinely
growing (it is built from `n / polyloglog n`-style terms), so the `o(n)` claim is
not vacuously met by a constant. This matters: a fake "succinct" theorem could
hide linear data inside an overhead that is secretly `Theta(n)`; the `o(n)` predicate,
*proved* for the concrete overhead, rules that out.

## 5. The lower bound, and why it matches

Why can't one do better than `2n` leading bits? Counting. An exact RMQ structure
that works for *all* arrays of length `n` must, in particular, be able to
distinguish any two arrays whose RMQ answer-tables differ -- and arrays with
different Cartesian-tree shapes do differ. The number of distinct shapes (binary
tree shapes on `n` nodes) is the `n`-th **Catalan number** `C_n`, and

```
log2 C_n  =  2n - 1.5 * log2 n - O(1).
```

Any lossless fixed-length encoding of `n`-node shapes therefore needs at least
`log2 C_n` bits, i.e. `2n` to leading order. The public lower-bound alias is

```lean
RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack
  := RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack
```

It is stated in a *doubled integer* form (everything multiplied through by 2) so
that the public statement avoids rational coefficients like `1.5`; informally it
is the familiar `2n - 1.5 log n - O(1)` bound. The Lean proof builds the counting
argument (a Remy-style insertion count for the Catalan growth) rather than citing
it.

The match is at leading order, and the document is careful about this: the upper
bound *stores* `2n + o(n)`; the lower bound *forbids* beating `2n`; together they
pin the dominant term, not every lower-order term. That honest gap -- `o(n)` of
slack above, a `1.5 log n` correction below -- is exactly the usual sense in
which a succinct structure is called space-optimal.

---

# Part II -- How to read the claims honestly

A succinct-data-structure theorem is only as meaningful as its cost and space
*models*. The most common way such a theorem can be quietly wrong is to smuggle
real work into a place the model does not charge for. This project's design -- and
much of its docs -- is organized around making those places visible. Read this
part before trusting any "constant time" or "`2n` bits" phrase.

## 6. Three things never to conflate

- **Total correctness:** does the returned answer equal the reference answer?
  (A statement about values.)
- **Modeled complexity:** how many *abstract operations* does the cost model
  count for a query? (A statement about a counter.)
- **Executable runtime:** how fast does Lean's compiled code actually run? (A
  statement about hardware. **The project makes no such claim.**)

The theorems here are about the first two only. In particular `O(1)` query is a
statement about a counter in a model, not a wall-clock or a Lean-`List` runtime
claim. Lean's `List` has linear-time indexing; the value-level specifications use
`List` for clarity and are explicitly *not* asserting that those reference
computations are fast.

## 7. `Costed`: pairing a value with a cost (no monad background needed)

The cost carrier is tiny (`RMQ/Core/Cost.lean`):

```lean
structure Costed (a : Type u) where
  value : a
  cost  : Nat
```

A `Costed a` is "a value, together with a natural number we are calling its
cost." Two operations are central:

- `erase x := x.value` forgets the cost and keeps the value. Correctness theorems
  are phrased about `erase` (the answer), cost theorems about `cost`.
- `bind x f` means "do `x`, feed its value into `f`, and **add the two costs.**"

If you have seen monads, `Costed` is the writer monad over `(Nat, +)` and `bind`
is its sequencing. If you have not: read `bind` as "do this, then do
that, and total up the cost," and read nothing more into it. `pure x` is a
zero-cost value; `tick n` adds `n` to the cost and returns nothing. That is the
entire vocabulary.

By itself `Costed` is only bookkeeping -- nothing stops someone writing
`tickValue 1 (expensiveAnswer)`, claiming cost `1` for an expensive computation.
That loophole is closed by the next layer.

## 8. `RAM.Exec`: a trace model you cannot cheat

`RMQ/Core/RAM.lean` defines a small **word-RAM-style** model. "Word-RAM" is the
usual model for this area: memory is an array of fixed-width machine words
(think: `log n`-bit integers), and a small set of primitive operations on words --
read, write, compare, branch, and bit-level `rank`/`select` on one word -- each
count as one step. It is the model in which "constant-time bit navigation" is the
normal claim for succinct structures.

Here it is a *trace* model:

```lean
inductive Op | branch | read | write | compare | alloc | wordRank | wordSelect
structure Exec (a : Type u) where
  private mk ::            -- the constructor is PRIVATE
  value : a
  trace : List Op
def steps (x : Exec a) := x.trace.length
```

An `Exec a` is a value together with the *list of primitive operations* used to
produce it; its cost (`steps`) is the length of that list. The single most
important word is `private`: client code cannot fabricate an `Exec` by pairing an
arbitrary value with a short trace. It must build programs out of the typed
primitives (`readArray?`, `compareLtInt`, the word `rank`/`select` ops, ...), each
of which appends exactly one real operation. So the step count cannot be gamed;
it reflects the operations actually performed. `toCosted` then forgets the trace
shape into a `Costed` whose `cost` is the genuine step count.

A **word-RAM assumption**, in this repo, is a precise and visible hypothesis: a
bounded-word read/compare/branch or one-word `rank`/`select` costs one modeled
step *provided the theorem has proved the read comes from counted payload and the
word fits the declared word-size bound*. It is the usual assumption in
succinct-structure papers, but kept in the open (in theorem names and docs)
instead of being implicit.

## 9. Payload bits vs proof-only fields: the anti-oracle line

Lean structures can carry *proofs* as fields, not only data. A field might
certify "this table is sorted" or "this lookup equals the spec." Those proof
fields are indispensable for verification but are **not stored bits** of the
modeled data structure. The project draws a hard line:

| category | what it is |
| --- | --- |
| **payload bits** | modeled stored bits a theorem explicitly counts: the `2n` parenthesis bits, rank/select directory bits, route tables, bounded payload words. |
| **proof-only fields** | invariants, exactness proofs, side conditions -- used by Lean to verify, never counted as storage. |
| **modeled cost** | the `Nat` from `Costed` / the trace length from `RAM.Exec`. |
| **(non-claim) runtime** | nothing about Lean's compiled execution speed. |

This is the line that defends against the classic failure mode: hide a semantic
**oracle** (a field or callback that simply *contains the answer*, computed for
free) and then "read" it in one charged step. The repo's space theorems count
the payload; the query theorems read from that counted payload through the
charged `RAM.Exec` primitives; and several intermediate interfaces are
deliberately labeled *weak composition surfaces* until a concrete
payload-backed inhabitant is supplied -- i.e. the docs say plainly "this is a
shape, not yet a real construction" rather than dressing up an oracle.

## 10. The trust base

What does a green checkmark here actually depend on? (`docs/TRUST_BASE.md`,
`docs/TRUST_AUDIT_PACKET.md`.)

- **Pinned, Mathlib-free.** Lean 4.22.0 (`lean-toolchain`), using only Lean/Std
  plus the `omega` arithmetic tactic. No Mathlib dependency. (A deliberate
  current engineering choice, not a permanent stance -- it keeps the dependency
  surface tiny, at the cost of re-deriving some basic lemmas.)
- **Hygiene-scanned.** The gate (`scripts/gate.ps1`, also run in CI) rejects
  `sorry`, `admit`, custom `axiom`, `unsafe`, `opaque`, `partial`, `extern`,
  `noncomputable`, `implemented_by`, `native_decide`, `Lean.ofReduceBool`, and
  `import Mathlib` in checked source.
- **Axiom-audited.** Curated `#print axioms` scripts (one per spoke) confirm the
  load-bearing theorems depend only on Lean's three ordinary foundational
  axioms -- `propext`, `Quot.sound`, `Classical.choice` -- and in particular *not*
  on `sorryAx`. There are no project-specific axioms in the checked surface.
- **Anti-vacuity linted.** A dedicated lint guards against the degenerate
  "succinct" or "constant-cost" statements that would be true for vacuous
  reasons.

So "verified" here means: assuming Lean's kernel and those three ordinary
axioms, and assuming the stated word-RAM cost model, the theorems hold -- with the
modeling assumptions themselves written down and checked rather than assumed.

---

# Part III -- The shared toolkit and the new spokes

The RMQ proof needed two reusable gadgets -- rank/select and balanced-parenthesis
navigation -- and these have been factored out into standalone, separately
checkable spokes. A fourth spoke, union-find, is a first step beyond succinct
structures. Each spoke has its own import root and its own axiom-check script.

## 11. Rank/select and balanced parentheses (what they are)

Over a bit-string `b`:

- **rank**`(b, i)` = the number of 1-bits (or 0-bits) in the first `i` positions.
- **select**`(b, k)` = the position of the `k`-th 1-bit (or 0-bit).

These are inverse-flavored operations, and they are the workhorses of succinct
structures: with rank/select you can navigate a balanced-parenthesis string --
jump from an opening bracket to its matching close, find a parent or the LCA --
without expanding the tree into pointers. The classical result (Jacobson; Clark;
Munro) is that a length-`n` bit-string can be augmented with `o(n)` extra bits to
answer rank and select in `O(1)` word-RAM time.

In the RMQ capstone, the query route is exactly such navigation over the `2n`-bit
shape. Conceptually, to answer `[left, right)` the final query
(`concreteBPNativeSuccinctRMQQueryCosted`, with its proof
`..._exact`):

1. uses select to find the close-bracket of the node for endpoint `left`;
2. uses select to find the close-bracket of the node for endpoint `right - 1`;
3. uses a compact close/LCA directory to find the close-bracket of their LCA;
4. uses rank to convert that bracket position back into an array index.

Each step is a bounded number of charged word operations over counted payload --
that is where the `O(1)` modeled query cost comes from, and where the anti-oracle
discipline of section 9 does its work.

## 12. The rank/select spoke, and the compressed/FID frontier

The plain-bitvector spoke is *complete* and is a headline in its own right:

```lean
RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery          -- access, rank, select
RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery  -- + machine-word-bounded reads
```

It proves `access`/`rank`/`select` with `n + o(n)` stored bits and constant
modeled query cost for an arbitrary bit-string -- the building block the RMQ
capstone consumes.

The **active frontier** is *compressed* rank/select, also called a **fully
indexable dictionary (FID)**. The idea (Raman-Raman-Rao, "RRR"): if a length-`n`
bit-string has only `k` ones, there are only `C(n,k)` such strings, so its
information content is `log2 C(n,k)` bits, which is *below* `n` when `k` is far
from `n/2`. A compressed structure should approach that entropy, not merely `n`.

What is **proved now** is the *primary enumerative budget* and its supporting
facts -- and, importantly, it is genuinely entropy-based, not `n` relabeled. In
`RMQ/Core/RankSelectCompressed.lean`, `binomialCount` is the real binomial
coefficient (defined by Pascal's recurrence), and the per-class budget is

```lean
fixedWeightPayloadBudget bits := Nat.log2 (binomialCount bits.length (trueCount bits)) + 1
```

i.e. `ceil(log2 C(n,k))`. The current public results prove that splitting the string
into sentinel log-sized chunks and storing one fixed-weight code per chunk stays
within the global entropy budget plus `o(n)`:

```lean
RMQ.RankSelect.fixedWeightBlockPayloadBudgetLePayloadBudgetFlattenAddBlocks
RMQ.RankSelect.fixedWeightLogChunkBlockPayloadBudgetLePayloadBudgetAddBound
RMQ.RankSelect.fixedWeightAmbientTableRAMLogChunkSplitWidthRouteDirectoryFamilyWordBoundedCompressedProfile
```

The frontier also includes two **negative** results, which is what keeps the
remaining gap honest (an open gap with no obstruction can look like routine
engineering; a stated obstruction shows where the difficulty is):

```lean
RMQ.RankSelect.noFixedWeightLogChunkDenseDecoderLittleO              -- a dense all-codes decoder table is NOT o(n)
RMQ.RankSelect.noFixedWeightAmbientTableRAMLogChunkRouteDirectoryFamilyRouteWidthClassLength  -- padding class/length to route width is ruled out
```

What is **not yet proved** is the *positive constructor*: a single concrete FID
family that simultaneously achieves the entropy space bound, charges its queries
against counted payload, and uses a genuinely sublinear shared decoder. The space
accounting is done; the end-to-end constant-time compressed dictionary is open.
This is stated as such in `docs/RANK_SELECT_FRONTIER.md`.

## 13. The balanced-parentheses navigation spoke

This spoke (`import RMQBPNavigation`) packages the tree-navigation layer the RMQ
capstone uses -- the close/LCA directory and the bridge between close-bracket
positions and array indices via rank/select:

```lean
RMQ.BPNavigation.compactCloseDirectoryProfile
RMQ.BPNavigation.shapeAccessCloseRankProfile
```

It is deliberately *not* a full balanced-parentheses tree-navigation library (no
general `enclose`, sibling, degree, etc.); it exposes exactly the operations the
RMQ theorem needs, proved against the counted payload.

## 14. The union-find spoke, and the broader direction

**Union-find** maintains a partition of `{0, ..., size-1}` into disjoint sets under
two operations: `find` (which set is `x` in? -- return a canonical representative)
and `union` (merge the sets of `x` and `y`). It is the first spoke that is *not*
about succinct space; it is about *amortized time*, a different kind of theorem,
and a natural next target for a "verified data structures" library.

The layering mirrors the RMQ contract idea:

- **Abstract spec** (`RMQ/Core/UnionFind.lean`): a `State` is a representative
  function `repr : Nat -> Nat` on `{x < size}`, with `SamePartition` the
  equivalence "these two states encode the same partition." This is the
  value-level "what is correct."
- **Concrete forest** (`RMQ/Core/UnionFind/Forest.lean`): sets are represented by
  a **parent-pointer forest** -- each element points at a parent; a root points at
  itself and names its set. `find` walks to the root. The refinement theorem
  `parentForestRefinement_profile` proves the executable forest agrees with the
  abstract spec. ("Refinement" = a concrete implementation provably matches an
  abstract specification.)
- **Path compression**: a real `find` rewrites every node on the walked path to
  point straight at the root, flattening the tree for next time. The repo proves
  this preserves the partition and records exact facts about the visited path
  (`fullCompressionRepresentationBackend_profile`).

The headline difficulty in union-find is the **amortized** running time. *Amortized*
analysis bounds the *average* cost over a sequence of operations, even when
individual operations are occasionally expensive, via the **potential method**:
keep a nonnegative "potential" (stored analysis credit) that expensive operations
draw down and cheap ones replenish, so that *actual + delta potential* is small per
operation. The classical result (Tarjan) is that union-by-rank with path
compression runs in `O(alpha(n))` amortized time per operation, where `alpha` is the
inverse Ackermann function -- effectively constant.

This spoke builds the *scaffolding* of that argument and is candid that it is
scaffolding. It proves the genuine structural invariant `2^rank <= mass` (a root
of rank `r` has a subtree of at least `2^r` elements, hence `rank <= log2 size`),
and it climbs a ladder of potential-method checkpoints -- zero-potential, rank-gap,
log-rank, rank-bucket, rank-slack, and a multilevel "Tarjan-level" schedule built
from iterated logarithms (`tarjanLevelIter`, `tarjanRankLevel`) toward
`fullCompressionTarjanLevelIndexAmortizedBackend_profile`.

What makes this honest rather than hand-wavy is a *self-diagnostic theorem*:

```lean
RMQ.UnionFind.Forest.ParentForest.NoCompressionRankedMassBackendState
  .tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le
```

It proves that, under the natural gap condition, the current multilevel
"level-index" potential *equals* the ordinary rank-slack potential -- i.e. the
present design, despite its Tarjan-shaped names, collapses back to plain rank
slack and therefore cannot by itself yield the inverse-Ackermann bound. The repo
contains a proof of its own current limitation. So: union-by-rank, path
compression, and a ladder of real amortized bounds are proved; the
inverse-Ackermann theorem is **not**, and the obstruction to the present approach
is itself a theorem. This is the `docs/UNION_FIND_FRONTIER.md` story.

---

# Part IV -- Status, honesty, and orientation

## 15. What is proved, what is not claimed, the live frontiers

**Proved (public):**

- exact RMQ semantics (half-open ranges, leftmost-tie), with uniqueness;
- many exact RMQ and LCA backends under one shared contract (linear scan, sparse
  table, hybrid/recursive-hybrid, microtables, Fischer-Heun-style, the succinct
  one), all interchangeable by `queryBuilt_eq`;
- the BP-native succinct RMQ capstone: `2n + o(n)` payload, exact answers,
  constant modeled query cost;
- the matching leading RMQ lower bound via Catalan counting (`2n - 1.5 log n`);
- standalone plain-bitvector rank/select, `n + o(n)`, constant modeled cost;
- compressed/FID *budget* and *split-width route-directory* frontier theorems,
  plus two negative results;
- the balanced-parentheses close/LCA navigation the capstone needs;
- union-find abstract spec, forest refinement, path compression, and a ladder of
  rank-slack / Tarjan-level amortized checkpoints.

**Not claimed:**

- no statement about Lean's native/compiled runtime;
- proof-only fields are not counted as stored payload;
- the compressed/FID rank/select *constructor* is not complete (only the budget +
  obstructions);
- the BP-navigation spoke is not a complete tree-navigation API;
- union-find does **not** prove the inverse-Ackermann (`O(alpha(n))`) bound, and a
  theorem records why the current residual design is insufficient;
- the union-find model is a functional forest, not yet a mutable-array
  implementation;
- `VerifiedDS` is not yet a separate mature package.

**Active frontiers (theorem-shaped, not project chores):**

1. **A concrete compressed/FID family.** Instantiate the split-width log-chunk
   route-directory family with concrete charged route payloads and a genuinely
   sublinear shared decoder, and prove a uniform constant modeled query bound --
   closing the gap between the proved entropy *budget* and an end-to-end
   compressed dictionary.
2. **A real inverse-Ackermann residual.** Replace the collapsing residual
   (the self-diagnostic above) with a recursively-bucketed / Ackermann-indexed
   residual counter, and bound both find and union credits by the intended
   `alpha`-style quantities.
3. **(Presentation, not correctness)** A flatter payload-only restatement of the
   capstone for external readers.

## 16. Assumptions ledger

| layer | payload bits | proof-only fields | modeled cost | runtime non-claim |
| --- | --- | --- | --- | --- |
| RMQ reference spec | -- (value-level spec) | `LeftmostArgMin`, uniqueness | -- | the reference scan is not a fast-runtime claim |
| RMQ capstone | `2n` BP bits + counted rank/select + close-nav payload | shape/balance/exactness/lower-bound proofs | constant bound over `concreteBPNativeSuccinctRMQQueryCosted` | not a compiled executable |
| plain rank/select | stored bits + Jacobson/Clark `o(n)` aux | directory correctness | constant access/rank/select | not a `List`-indexing claim |
| compressed/FID frontier | fixed-weight codes, route/class tables, shared decoder -- only when a profile counts them | family premises, route equations | profiles charge route/local reads; final constant query needs the concrete family | full-payload readback is not the final story |
| BP navigation | counted close-directory + rank/select words | balance, close exactness, LCA bridge | modeled table/word reads | not a complete BP library |
| union-find forest | parent/rank/mass are forest representation data | `RootMassInvariant`, `RankPowerMassInvariant`, potential-drop lemmas | `Costed` trace lengths + potential inequalities | not a mutable-array implementation |
| Tarjan scaffold | no new serialized payload | level schedules, potentials, residual defs | cross-level potential pays part of find cost | not inverse-Ackermann |

## 17. Why is the repo still called RMQ? What is `VerifiedDS`?

The RMQ theorem stack is the stable, citable artifact, and most theorem names are
RMQ-shaped; renaming now would churn references for little gain while the new
spokes' APIs are still settling. So the repository keeps the `RMQ` name, and
`VerifiedDS.lean` is a deliberately thin **facade**: it imports the five public
roots (`RMQ`, `RMQHub`, `RMQRankSelect`, `RMQBPNavigation`, `RMQUnionFind`) and
does nothing else, signaling the broader "verified data structures" direction
without forcing a namespace migration. (`docs/REPOSITORY_STRATEGY.md` is the long
form.) The import roots:

```lean
import RMQ              -- RMQ/LCA family + succinct RMQ capstone
import RMQHub           -- reusable cost / RAM / refinement / table / lower-bound layers
import RMQRankSelect    -- standalone rank/select spoke
import RMQBPNavigation  -- balanced-parentheses navigation spoke
import RMQUnionFind     -- union-find spec + forest-refinement spoke
import VerifiedDS       -- thin facade over all of the above
```

## 18. Literature map

The mathematics is established; the contribution is the end-to-end Lean
connection with visible model assumptions. For a reader who wants the classical
sources behind each piece:

- **RMQ <-> LCA, and constant-time RMQ.** Gabow, Bentley, Tarjan (1984), scaling
  and range queries; Bender & Farach-Colton, *The LCA problem revisited* (2000),
  the modern `O(n)`-prep / `O(1)`-query RMQ via +/-1-RMQ on Euler tours.
- **Cartesian trees.** Vuillemin (1980).
- **Succinct trees / balanced parentheses.** Jacobson, *Space-efficient static
  trees and graphs* (1989); Munro & Raman, *Succinct representation of balanced
  parentheses and static trees* (2001).
- **rank/select in `o(n)` extra bits.** Jacobson (1989); Clark, *Compact pat
  trees* (1996); Munro (1996).
- **Compressed bitvectors / FID.** Raman, Raman & Rao, *Succinct indexable
  dictionaries...* (2002) -- the "RRR" entropy bound `log2 C(n,k) + o(n)`.
- **Fischer-Heun RMQ.** Fischer & Heun, *Space-efficient preprocessing schemes
  for RMQ...* (2011) -- the in-place succinct RMQ this repo's Fischer-Heun-style
  backends echo.
- **Union-find / inverse Ackermann.** Tarjan, *Efficiency of a good but not
  linear set union algorithm* (1975); the `O(alpha(n))` amortized bound this spoke is
  scaffolding toward.

(These are the usual attributions for the techniques; this document names them
so the proof's routine steps are recognizable as known results rather than
appearing novel. The Lean code re-derives, rather than imports, this material.)

## 19. Skeptical questions

**If the Cartesian shape determines RMQ, why is rank/select needed at all?**
The shape determines the *answer*; rank/select and BP navigation are *how* you
read the answer out of a `2n`-bit string in constant modeled time without
rebuilding the tree or scanning the range.

**Does `2n + o(n)` secretly include the correctness proofs?** No. It counts
modeled payload bits. The Lean proof fields certify the structure but are not
serialized storage in the space account (section 9).

**Can the cost model hide an expensive computation in one charged step?** That is
the exact risk the design polices. The `RAM.Exec` constructor is private, so
costs reflect real primitives; the final RMQ path reads from concrete
payload-backed components; and interfaces that are *not* yet payload-backed are
labeled weak rather than charged as if they were. A residual trust assumption
remains -- the word-RAM costing of one-word `rank`/`select` -- and it is stated, not
hidden.

**Did the compressed/FID theorem close?** No. The entropy *budget* and the
log-chunk bridge are proved (with two obstruction results), but the concrete
constant-time compressed *constructor* is open.

**Did union-find reach Tarjan / inverse-Ackermann?** No. Union-by-rank, path
compression, and several amortized bounds are proved; a self-diagnostic theorem
shows the current residual potential collapses to rank slack, so the present
design cannot reach `O(alpha(n))` without a new residual index.

**Is "first verified RMQ/..." being claimed?** No first-ever claims are made here.
The framing is: a faithful, model-transparent, end-to-end Lean connection of
known theory, plus genuine (and honestly-scoped) new frontier work on the spokes.

**Could a grad student give a talk from this?** That is the intended bar. The
proved core (Parts I-II), the spoke status (Part III), and the explicit frontiers
(section 15) are enough to present the result *and* take questions about what is and is
not established -- which, per the modeling-honesty goal, is the point.

---

## Appendix A. Stress-test loop (how this document was hardened)

This digest was put through an adversarial-classroom loop before finalizing: six
reviewer roles each tried to break the explanation, objections were collected,
and the text was revised until the only remaining objections were genuine
research frontiers (section 15), not gaps in the writing. The rounds below are an honest
record of what changed; they are a description of the editing process, not
independently verifiable claims about the code (for those, see the gate and the
axiom scripts).

**Round 1 -- unexplained vocabulary.**
- *Data-structures novice:* RMQ, LCA, Cartesian tree, rank/select, succinct,
  word-RAM, amortized, union-find were used before definition. -> Every term now
  has a plain-English definition at first use; a worked `[3,1,4,1,5]` example
  anchors RMQ.
- *Lean/formalization novice:* `Costed`, `erase`, `bind`, `RAM.Exec`, payload,
  proof-only field, contract, refinement appeared as jargon. -> Part II now
  introduces each before reliance, and `bind` is explained without requiring
  monads.
- *Cost-model skeptic:* "constant time" was ambiguous. -> section 6 separates
  correctness / modeled cost / runtime, and the runtime non-claim is repeated in
  the ledger.

**Round 2 -- significance and honesty.**
- *Skeptical mathematician:* the first draft asserted the lower/upper match
  without saying *in what sense*. -> section 5 states the match is at leading order and
  names the `o(n)` / `1.5 log n` gap explicitly; the `o(n)` predicate is
  explained as non-vacuous (section 4).
- *Library-maintainer skeptic:* were the abstractions (contract, spoke,
  facade) motivated or clutter? -> section 2 motivates the contract via `queryBuilt_eq`;
  section 17 explains the `VerifiedDS` facade and the RMQ name.
- *Cost-model skeptic (return):* what stops an oracle? -> section 9 and the private
  `RAM.Exec` constructor (section 8) are now explicit, and the frontier sections name
  which interfaces are *not* yet payload-backed.

**Round 3 -- frontier accuracy and literature.**
- *Skeptical mathematician:* the compressed/FID and Tarjan gaps sounded like
  routine engineering. -> section 12 and section 14 now cite the *negative* results and the
  union-find *self-diagnostic* collapse theorem, so the difficulty is visible.
- *Grad-student explainer:* the "what's next" items read as chores, and the
  classical results were uncited (risking the impression they are novel). -> section 15
  recasts frontiers as theorem targets; section 18 adds the literature map (Bender-
  Farach-Colton, Jacobson, Munro-Raman, RRR, Fischer-Heun, Tarjan).

**Fixedpoint.** Remaining objections are the two open research frontiers
(a concrete compressed/FID family; an inverse-Ackermann residual), now stated in
the main text, the ledger, the skeptical questions, and the frontier list -- not
defects in the explanation.
