# W20 U2 Positional-Provenance and Source-Reachability Scout

## Status and scope

- Report-local status: complete read-only architecture audit.
- U2/W19 status: **open; repair required**. This report does not implement Lean,
  does not certify the proposed witness constructions, and does not declare U2
  complete.
- Audited commit: `af8791150b64038e9c0776e3639634f1d83518ea`.
- Scout branch: `codex/rmq-u2-provenance-reachability-scout`.
- Source policy: all Lean and existing documentation were read-only. This file
  is the only permitted repository edit.
- Checklist: `rmq-proof-sprint`, used as a proof-architecture and downstream-
  consumption checklist rather than an implementation workflow.

The strongest clean W19 target has two different directions that must meet at
one indexed operational relation:

1. **Forward occurrence provenance.** Every indexed read occurrence in a
   whole-query trace, including failed reads, is tied to one indexed local
   instruction occurrence at the actual folded-prefix state and to one indexed
   component occurrence with the exact invocation parameters used by that
   instruction.
2. **Reverse source reachability.** Every counted `ReviewerSource` has at least
   one **successful** occurrence in some valid guarded top-level `List Int`
   query. The fresh segment-21 mutation has no occurrence under the same
   operational relation.

The second statement must be existential across inputs and valid queries. It is
false if strengthened to every shape or every query: the empty shape has no
valid query, and the long, sparse, and dense select branches are mutually
exclusive at one selected occurrence.

The source audit found credible valid-query constructions for every one of the
20 constructors. Small witnesses cover dense select, final rank, shared BP, and
canonical interior. Explicit very-large Cartesian shapes cover the long and
sparse select branches. However, the repository currently proves none of the
all-source reverse statement at valid top level. In particular, the large long
and sparse constructions below are proof obligations, not landed Lean
evidence. W19 should formalize them before any public all-source reachability
claim is accepted.

## Executive verdict

W18 made a real forward improvement: an emitted **event value** now resolves to
an instruction evaluated at an actual folded-prefix state. It did not preserve
which occurrence of an equal repeated event was produced. Its reverse positive
predicate and mutation predicate are also different:

- positive `P_source`: an isolated component attempted read for a counted
  source;
- mutation `Q`: absence of a read in an arbitrary instruction evaluation at an
  arbitrary state;
- forward `P_event`: event-value membership in an already-existing whole-query
  trace, followed by actual-prefix-state and component-path evidence.

No theorem identifies `P_source` with `Q`. `Q` does not itself require a closed-
program instruction occurrence, a folded-prefix state, or a valid query. The
comment at `RMQ/Core/SuccinctFinalRAM.lean:6545-6546` and any prose calling the
fresh mutation the “same operational producer mechanism” are therefore too
strong.

The W18 consumer chain is structurally complete for those W18 predicates. That
is precisely why W19 cannot close by adding nearby aliases. It must replace the
load-bearing adequacy fields and paper conjunctions with the occurrence-
preserving and same-relation forms.

## 1. Exact W18 contracts

### 1.1 Positive source predicate `P_source`

The exact positive reverse-liveness predicate is
`ReviewerSource.HasProducerMayPath`:

```lean
def ReviewerSource.HasProducerMayPath
    (shape : Cartesian.CartesianShape) (source : ReviewerSource) : Prop :=
  ∃ leaf : ReviewerReadLeaf,
  ∃ segment index : Nat,
  ∃ word? : Option WordRAM.Word,
    concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ∧
    ReviewerProducerReadPath shape leaf segment index word?
```

Source: `RMQ/Core/SuccinctFinalRAM.lean:5860-5868`.

Its theorem is:

```lean
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path
    (shape : Cartesian.CartesianShape) (source : ReviewerSource)
    (_hcounted : source.Counted) : source.HasProducerMayPath shape
```

Source: `RMQ/Core/SuccinctFinalRAM.lean:5870-5874`.

The quantifier order is therefore:

```text
forall shape, forall source,
  source.Counted ->
    exists leaf, segment, index, word?, source-map equality and component path.
```

It has no `left`, `right`, `ValidRange`, program, instruction occurrence,
folded state, global trace, or global/local occurrence position. Because
`word?` is arbitrary, it proves an attempted read and permits `none`.

The proof constructs isolated zero-parameter calls: super/local/flag/rank
slots at zero, dense select at `(basePosition, baseOccurrence, q) = (0,0,0)`,
and canonical interior at `(startBlock,count) = (0,1)`
(`RMQ/Core/SuccinctFinalRAM.lean:5875-5997`). Those are useful component facts;
they are not top-level invocation witnesses.

### 1.2 Strongest W18 forward predicate `P_event`

W18 separately defines:

```lean
def ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop :=
  ∀ {segment index : Nat} {word? : Option WordRAM.Word},
    WordRAM.TraceEvent.readWord segment index word? ∈
        (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
          shape left right).trace ->
      ∃ source : ReviewerSource,
      ∃ leaf : ReviewerReadLeaf,
      ∃ instr : WholeQueryInstr,
      ∃ preState : WholeQueryState,
      ∃ before after : WholeQueryProgram,
        concreteBPNativeSuccinctRMQWholeQueryProgram =
            before ++ instr :: after ∧
        preState =
          (WholeQueryProgram.evalGlobalWordTrace
            shape left right before WholeQueryState.empty).value ∧
        source.ProducedReadBy
          shape left right instr preState segment index word? ∧
        instr.reviewerReadLeaf? = some leaf ∧
        ReviewerProducerReadPath shape leaf segment index word? ∧
        source.Counted
```

Source: `RMQ/Core/SuccinctFinalRAM.lean:6642-6663`; the checked theorem is
`concreteBPNativeSuccinctRMQWholeQueryProducerProvenance_checked` at lines
`6665-6672`.

`ReviewerSource.ProducedReadBy` contains the segment-to-source equality,
segment-to-region equality, and membership of the same event value in the
instruction-local trace (`RMQ/Core/SuccinctFinalRAM.lean:6561-6577`).
`WholeQueryProgram.ProducesEvent` establishes the real prefix state
(`RMQ/Core/SuccinctFinalRAM.lean:3855-3925`).

This is quantified for every raw `shape,left,right`, without a validity
premise, but it begins with `List.Mem`. It retains neither the global trace
position nor the instruction-local trace position. Two equal events at
different positions can share one receipt.

The list-facing theorem adds a `ValidRange xs left right` premise and projects
the same raw predicate; it does not strengthen the occurrence identity
(`RMQ/Core/SuccinctRMQClassic.lean:788-797`).

### 1.3 Mutation predicate `Q`

The mutation carrier and predicate are:

```lean
structure ReviewerUnusedSourceMutation where
  segment : Nat
  allegedLeaf : ReviewerReadLeaf

def ReviewerUnusedSourceMutation.HasOperationalProducer
    (candidate : ReviewerUnusedSourceMutation) : Prop :=
  ∃ shape : Cartesian.CartesianShape,
  ∃ left right : Nat,
  ∃ instr : WholeQueryInstr,
  ∃ preState : WholeQueryState,
  ∃ index : Nat,
  ∃ word? : Option WordRAM.Word,
    instr.reviewerReadLeaf? = some candidate.allegedLeaf ∧
    WordRAM.TraceEvent.readWord candidate.segment index word? ∈
      (instr.evalGlobalWordTrace shape left right preState).trace
```

Source: `RMQ/Core/SuccinctFinalRAM.lean:6520-6543`.

The fresh candidate is segment `21` with alleged leaf `.canonicalClose`, and
the theorem proves its negation:

```lean
def concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource :=
  { segment := 21, allegedLeaf := .canonicalClose }

theorem concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer :
  ¬ concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.HasOperationalProducer
```

Source: `RMQ/Core/SuccinctFinalRAM.lean:6526-6559`.

Under the negation, the domain is
`not exists shape,left,right,instr,preState,index,word?`. It does not require:

- `instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram`;
- an instruction position;
- `preState` to be the fold of the preceding program prefix;
- a valid guarded list query; or
- a global trace occurrence.

It is stronger as a negative fact than “no valid whole-query occurrence,” but
it is not the same predicate as the accepted-source theorem.

### 1.4 Why `P_source` and `Q` are not interchangeable

| Axis | `P_source` | `Q` |
| --- | --- | --- |
| Carrier | `ReviewerSource` | `ReviewerUnusedSourceMutation` |
| Shape | fixed universally by theorem | existential inside predicate |
| Query | absent | arbitrary `left,right` |
| State/instruction | absent | arbitrary state and instruction |
| Source map | required | absent, necessarily so for segment 21 |
| Leaf | existential | alleged leaf fixed by candidate |
| Evidence | `ReviewerProducerReadPath` component membership | instruction-local trace membership |
| Program occurrence | absent | absent |
| Valid public query | absent | absent |
| Occurrence positions | absent | absent |

The repository records the mismatch explicitly in
`docs/internal/DESIGN_DECISIONS.md:1930-1992`,
`docs/FAMILY_SUMMARY.md:16-25`, and
`docs/internal/RMQ_FINAL_ROADMAP.md:124-175`.

## 2. Semantic ladder W19 must preserve

| Level | Exact meaning | Current evidence | What it does not imply |
| --- | --- | --- | --- |
| Component attempted-read | A component trace contains `readWord ... word?`, where `word?` may be `none`. | `ReviewerProducerReadPath`; `HasProducerMayPath`. | Successful storage access or top-level invocation. |
| Component successful read | A component trace contains `readWord ... (some word)`. | Successful-read backing theorems exist in the physical/store layer. | That every counted source succeeds, or that this component was reached by a valid whole query. |
| Arbitrary instruction trace | Some `WholeQueryInstr.evalGlobalWordTrace` at an arbitrary state contains an event. | Mutation `Q`. | Membership in the closed program, actual prefix state, or valid-query reachability. |
| Valid-query reachability | The guarded `SuccinctClassic.queryTraceResult xs left right`, under `ValidRange xs left right`, contains the occurrence. | No reverse all-source theorem. | Occurrence provenance unless positions and embeddings are retained. |
| Event-value membership | `event ∈ trace`. | W18 `P_event`. | Which equal occurrence, instruction occurrence, or component occurrence produced it. |
| Indexed occurrence provenance | Global position, instruction position, folded prefix state, local position, component position, and offset equations all agree. | Missing W19 object. | Nothing weaker should be advertised as positional provenance. |

`ValidRange xs left right` is exactly `left < right ∧ right ≤ xs.length`
(`RMQ/Core/Spec.lean:13-15`). Invalid public queries are guarded to a pure
`none` result with empty trace (`RMQ/Core/SuccinctRMQClassic.lean:128-153` and
`194-215`). Raw shape execution is not a substitute for this domain.

## 3. All 20 `ReviewerSource` constructors

The constructor universe is exactly the 20 cases at
`RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean:24-45`, in the same order as
the physical manifest at lines `48-68`. The logical segment map is at lines
`83-106`. There are 21 logical segments because `sharedBPCode` is used at both
segments `0` and `19`.

### 3.1 Witness families

The following abbreviations describe audit constructions, not new Lean
definitions.

- **D (dense tiny):** `xs = [7]`, valid query `[0,1)`. Its shape has
  `bpCode = [true,false]`. Both select instructions request false occurrence
  zero. The super is short, the local block is non-sparse, and the dense packed
  BP path is taken. LCA returns `some`, so final rank executes.
- **C (canonical interior):** strictly increasing `xs` of length `16`, valid
  query `[0,16)`. The right-chain BP word is `()^16`; endpoint closes are at
  positions `1` and `31`. The raw canonical block size is
  `2 * (log2 16 + 1) = 10`, so endpoint blocks are `0` and `3` and the positive
  middle interior call reaches segment `20`. The branch definitions are in
  `RMQ/Core/SuccinctClose/ConcreteDirectoryRAM.lean:2312-2328` and
  `2346-2368`.
- **L (long super):** let `N = 2^128`. Choose the explicit size-`N` Cartesian
  shape whose BP word is `()` followed by `(` repeated `N-1` times and `)`
  repeated `N-1` times. Let `xs := shape.representative`; then
  `Cartesian.shape xs = shape` and `xs.length = N` by
  `RMQ/Core/Shape.lean:966-977` and `1075-1152`. Query `[0,1)` is valid.
  The BP length is `2^129`, so `wordBits = 130`, `ell = 8`,
  `superStride = 16900`, and `superLongSpan = 17,576,000`
  (`RMQ/Core/GenericSelect/Params.lean:18-34`). False occurrence zero is at
  position `1`; later occurrences in super slot zero lie beyond position `N`,
  so that slot is long under the strict predicate at
  `RMQ/Core/GenericSelect/Slots.lean:97-104`.
- **S (short-super sparse local):** again let `N = 2^128`, and choose the
  Cartesian shape with BP word
  `()` ++ `(`^131 ++ `)`^131 ++ `()`^(N-132). Use its representative and query
  `[0,1)`. Here `localStride = 2`. The first two false positions are `1` and
  `133`, so the local span is `133 > wordBits = 130`. The 16,900th false is at
  position `33,799`, far below `superLongSpan = 17,576,000`, so the super is
  short while local slot zero is a sparse exception. This is exactly the
  strict condition in `localIsSparseException`
  (`RMQ/Core/GenericSelect/Slots.lean:851-868`).

The select evaluator gives the route directly:

- every in-domain select first reads the four-field super entry
  (`RMQ/Core/GenericSelect/RAM.lean:1843-1848`);
- a marked long super reads long-flag rank and the long-relative entry
  (lines `1852-1867`);
- a short super reads the four-field local entry (lines `1868-1874`);
- a marked local entry reads the sparse directory, otherwise it reads packed BP
  words (lines `1875-1894`).

The closed controller is exactly two selects, LCA, guarded final rank, and
output (`RMQ/Core/SuccinctFinalRAM.lean:4156-4165`).

### 3.2 Constructor-by-constructor verdict

“Reachable” below is the audit's mathematical/source-control-flow verdict.
“Checked gap” states what Lean still lacks. For L and S, the verdict is
conditional on formalizing the explicit shape arithmetic and lifting the
component occurrence through the closed program; it must remain open in the
acceptance matrix until then.

| # | Constructor | Segment(s) | Valid top-level route | Attempt/success and checked verdict |
| ---: | --- | ---: | --- | --- |
| 1 | `sharedBPCode` | `0`, `19` | D: dense select reads packed BP at `0`; the guarded final rank also uses the same source at `19`. | Reachable and successful on an in-domain packed word. W18 proves only an isolated dense attempt; no reverse valid-query theorem. |
| 2 | `finalRankSuperFalse` | `17` | D: valid LCA produces `answerClose = some _`; instruction four executes false-rank. | Reachable; expected successful built super-rank read. Not packaged as a valid-query source witness. |
| 3 | `finalRankBlockFalse` | `18` | Same D final-rank invocation. | Reachable; expected successful built block-rank read. Same checked gap. |
| 4 | `selectSuperBaseOccurrence` | `1` | D: an in-domain select reads super slot zero. | Reachable and successful built-field read; current reverse theorem is component-only. |
| 5 | `selectSuperBaseWordIndex` | `2` | Same D super-table invocation. | Same. |
| 6 | `selectSuperRankBefore` | `3` | Same D super-table invocation. | Same. |
| 7 | `selectSuperFirstOffset` | `4` | Same D super-table invocation. | Same. |
| 8 | `selectLocalBaseOccurrence` | `5` | D: sole super is short; local slot zero is read. | Reachable and successful built-field read; no valid-query reverse theorem. |
| 9 | `selectLocalBaseWordIndex` | `6` | Same D local-table invocation. | Same. |
| 10 | `selectLocalRankBefore` | `7` | Same D local-table invocation. | Same. |
| 11 | `selectLocalFirstOffset` | `8` | Same D local-table invocation. | Same. |
| 12 | `selectLongFlagRankSuperTrue` | `9` | L: selected occurrence zero lies in marked long super zero; long-flag rank executes. | Constructively reachable; successful rank-table slot is expected. No checked Cartesian/List/top-level witness. |
| 13 | `selectLongFlagRankBlockTrue` | `10` | Same L long-flag-rank invocation. | Same. |
| 14 | `selectLongFlagBits` | `11` | Same L long-flag-rank invocation. | Same. |
| 15 | `selectLongRelative` | `12` | L: after the long-flag rank, compact long-relative slot zero is read. | Constructively reachable and expected successful; no checked top-level witness. |
| 16 | `selectSparseRankSuperTrue` | `13` | S: short super plus sparse local zero enters the sparse directory. | Constructively reachable; expected successful sparse-rank read. No checked top-level witness. |
| 17 | `selectSparseRankBlockTrue` | `14` | Same S sparse-directory invocation. | Same. |
| 18 | `selectSparseFlagBits` | `15` | Same S sparse-directory invocation. | Same. |
| 19 | `selectSparseRelative` | `16` | S: compact sparse-relative slot zero is read after sparse-flag rank. | Constructively reachable and expected successful; no checked top-level witness. |
| 20 | `canonicalClose` | `20` | C: distant close blocks make the LCA instruction execute a positive middle canonical-interior query. | Reachable; expected successful canonical-interior read. Current W18 witness is only direct `(0,1)` component invocation. |

The conservative formal verdict is therefore:

- **proved now:** every constructor has an isolated possible component
  attempted read (`HasProducerMayPath`);
- **source-audited small valid routes:** sources 1-11, 17-20;
- **explicit but unformalized large valid routes:** sources 12-19;
- **not proved now:** every counted source has any valid top-level occurrence,
  or a successful one.

This split is important. A typed 20-case enumeration, a total segment map, and
a component call for each letter do not prove reverse top-level liveness.

## 4. Minimal W19 Lean signatures

These are recommended signatures, not implementations. Names are provisional;
the dependency and quantifier structure is the contract.

### 4.1 Occurrence-preserving program production

```lean
structure WholeQueryProgram.ProducedOccurrence
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (init : WholeQueryState)
    (globalPos : Nat) (event : WordRAM.TraceEvent) where
  instrPos localPos : Nat
  instr : WholeQueryInstr
  preState : WholeQueryState
  before after : WholeQueryProgram
  program_eq : program = before ++ instr :: after
  instrPos_eq : instrPos = before.length
  preState_eq :
    preState =
      (evalGlobalWordTrace shape left right before init).value
  global_get :
    (evalGlobalWordTrace shape left right program init).trace[globalPos]? =
      some event
  local_get :
    (instr.evalGlobalWordTrace shape left right preState).trace[localPos]? =
      some event
  globalPos_eq :
    globalPos =
      (evalGlobalWordTrace shape left right before init).trace.length +
        localPos
```

The `globalPos_eq` field, or a theorem-equivalent list decomposition, is
essential. Independent global and local `get? = some event` equations are still
vulnerable to substitution between equal repeated events.

The forward capstone should start from indexed lookup:

```lean
def ConcreteBPNativeSuccinctRMQWholeQueryIndexedProducerProvenance
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop :=
  ∀ (globalPos : Nat) {segment index : Nat} {word? : Option WordRAM.Word},
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
      shape left right).trace[globalPos]? =
        some (.readWord segment index word?) ->
      ∃ source leaf,
        source.Counted ∧
        concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
          some source ∧
        ∃ produced : WholeQueryProgram.ProducedOccurrence
          shape left right
          concreteBPNativeSuccinctRMQWholeQueryProgram
          WholeQueryState.empty globalPos
          (.readWord segment index word?),
        ∃ componentPos,
          ReviewerProducerInvocationPath
            produced leaf segment index word? componentPos
```

The core theorem can remain raw-shape/all-queries, because it is conditional on
an occurrence already in the raw trace. The public List theorem must consume it
only under `ValidRange`.

### 4.2 Invocation-specific component path

Current `ReviewerProducerReadPath` has useful constructor parameters but the
public proposition existentially erases them. The constructors carry:

```text
selectSuper:        slot
selectLongRank:     pos
selectLongRelative: base, slot
selectLocal:        slot
selectSparse:       base, localSlot, localOccurrence
selectDense:        basePosition, baseOccurrence, q
lcaRank:            pos
lcaBP:              blockSize, close
lcaInterior:        startBlock, count
finalRank:          pos
```

Source: `RMQ/Core/SuccinctFinalRAM.lean:5278-5341`.

W19 needs a dependent relation parameterized by the produced instruction
occurrence, not only by `shape,leaf,segment,index,word?`:

```lean
inductive ReviewerProducerInvocationPath
    {shape left right globalPos event}
    (produced : WholeQueryProgram.ProducedOccurrence
      shape left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty globalPos event) :
    ReviewerReadLeaf -> Nat -> Nat -> Option WordRAM.Word -> Nat -> Prop
```

Each constructor must retain:

1. the exact component invocation parameters listed above;
2. equations tying them to `produced.instr`, `left`, `right`, and
   `produced.preState` (for example, the actual select argument is
   `idx.eval left right preState`);
3. a component trace position and indexed `get?` equation; and
4. an offset/decomposition equation embedding that component occurrence at
   `produced.localPos` in the complete instruction trace.

`InvokedBy` or the embedding relation must be defined by evaluator cases. It
must not be a caller-supplied proof field whose premise already asserts the
desired local event. Otherwise the new type can retain parameter names while
remaining a letter-complete oracle.

### 4.3 One common positive/mutation relation

The carrier should be a segment/leaf claim, not a unique owner function:
segments `17`-`19` can be used inside LCA and by final rank, and shared BP has
select, rank, and canonical-close consumers.

```lean
structure ReviewerReadClaim where
  segment : Nat
  leaf : ReviewerReadLeaf

def ReviewerReadClaim.HasValidWholeQueryOccurrence
    (claim : ReviewerReadClaim) (word? : Option WordRAM.Word) : Prop :=
  ∃ (xs : List Int) (left right globalPos componentPos index : Nat),
    ValidRange xs left right ∧
    ∃ produced : WholeQueryProgram.ProducedOccurrence
      (SuccinctClassic.cartesianShape xs) left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty globalPos
      (.readWord claim.segment index word?),
      produced.instr.reviewerReadLeaf? = some claim.leaf ∧
      ReviewerProducerInvocationPath
        produced claim.leaf claim.segment index word? componentPos
```

The final syntax of the last two fields may differ, but the indices and
evaluator-derived embeddings may not disappear.

Use that one relation literally on both sides:

```lean
theorem counted_source_has_successful_valid_occurrence
    (source : ReviewerSource) (hcounted : source.Counted) :
    ∃ claim word,
      concreteBPNativeSuccinctRMQReviewerSegmentSource? claim.segment =
        some source ∧
      claim.HasValidWholeQueryOccurrence (some word)

theorem fresh_segment21_has_no_valid_occurrence :
  ¬ ∃ word?,
    concreteBPNativeSuccinctRMQFreshUnusedClaim.HasValidWholeQueryOccurrence
      word?
```

The positive theorem instantiates the common relation at `some word`, while the
mutation rules out every `word?`, hence both successful and failed occurrences.

If W19 intentionally chooses only component may-read, then define a common
`HasComponentAttempt` claim predicate and use it for both positive and
mutation theorems. That weaker contract can be true, but public wording must
say component may-read and must not claim valid top-level source liveness.

### 4.4 Shared-BP consumers

Retain a relational theorem, now through the same valid-occurrence carrier:

```lean
theorem shared_bp_consumer_has_valid_occurrence
    (consumer : ReviewerSharedBPConsumer) :
    ∃ word?,
      ({ segment := consumer.segment, leaf := consumer.leaf } :
        ReviewerReadClaim).HasValidWholeQueryOccurrence word?
```

This prevents a source witness at segment `0` from being joined to an unrelated
canonical-close or rank label.

## 5. Required regressions and boundary tests

### 5.1 Repeated equal event

The minimum adversarial fixture is `xs = [7]`, query `[0,1)`.

The closed program's first instruction selects `.inputLeft`; the second selects
`.sub .inputRight (.const 1)` (`RMQ/Core/SuccinctFinalRAM.lean:4157-4164`). On
this query both evaluate to index zero. An in-domain select necessarily begins
with the same super-table read
(`RMQ/Core/GenericSelect/RAM.lean:1835-1848`). Thus the two instruction
occurrences append equal select traces at distinct global positions.

The regression must exhibit both receipts:

```text
instruction position 0, global position g0, local position l
instruction position 1, global position g1, local position l
g0 != g1
```

and prove each global position equals its own preceding-prefix trace length plus
its local position. Merely proving the event value is a member twice is not
enough.

Also test `[7,7]` over every valid interval. Equal input values exercise the
leftmost RMQ policy but must not be confused with equal trace-event identity.

### 5.2 Tiny and invalid boundaries

- empty list: there is no valid query, so it cannot witness reverse source
  reachability;
- singleton `[7]`, `[0,1)`: repeated select occurrence, dense/shared BP,
  same-close LCA, and final rank;
- size two in both Cartesian orientations: `[0,1)`, `[1,2)`, and `[0,2)`;
- empty range, reversed range, and out-of-bounds range: public guarded trace is
  empty and the reachability predicate must be false;
- raw invalid execution versus public guard: the existing validator explicitly
  detects that the raw evaluator may differ from guarded invalid semantics
  (`RMQ/Validation/SuccinctClassic.lean:212-236`);
- `superSpan = superLongSpan` and `superLongSpan + 1`;
- `shortSuperLocalSpan = wordBits` and `wordBits + 1`; both classifications use
  strict inequalities;
- segment `0`/`19` shared-source alias, segment `20` canonical interior, and
  fresh segment `21`;
- for every fixture, separate `word? = none` attempted reads from `some word`
  successful reads.

The large L/S proofs should be symbolic. Constructing a literal list of length
`2^128` is neither required nor appropriate; use the explicit Cartesian shape,
`CartesianShape.representative`, and structural/arithmetic theorems.

## 6. Required downstream consumer chain

The existing W18 chain is exact and must be migrated in place.

### 6.1 Core and final adequacy

Current core surface:

- `ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance` and `_checked` at
  `RMQ/Core/SuccinctFinalRAM.lean:6642-6672`.

Current final-adequacy fields in
`RMQ/Core/SuccinctFinalModelAdequacy.lean`:

- `canonical_counted_sources_have_producer_may_path`, lines `80-82`;
- `all_shared_bp_dependencies_have_producer_path`, lines `83-85`;
- `fresh_unused_source_rejected_by_producer`, lines `86-87`;
- `every_emitted_read_has_producer_provenance`, lines `114-115`.

They are populated directly at lines `282-303`.

W19 must replace these with indexed forward provenance, successful valid-query
source reachability, same-relation shared-BP reachability, and same-relation
fresh rejection. Keeping the old fields as accurately named compatibility
facts is fine; they cannot remain the load-bearing acceptance fields.

### 6.2 `List Int` validity boundary

`FlatPayloadStoreNoSyntheticExecutionStory` validity-gates raw adequacy at
`RMQ/Core/SuccinctRMQClassic.lean:597-604`.
`flatPayloadStoreNoSyntheticExecutionStory_producerProvenance_of_valid`
projects W18 at lines `779-797`. The reverse P/shared facts are separately
lifted at lines `799-814`.

Required W19 consumers should have theorem shapes such as:

```lean
theorem flatPayloadStoreNoSyntheticExecutionStory_indexedProducerProvenance_of_valid
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    ConcreteBPNativeSuccinctRMQWholeQueryIndexedProducerProvenance
      (cartesianShape xs) left right

theorem reviewerCountedSource_successfulValidOccurrence
    (source : ReviewerSource) (hcounted : source.Counted) :
    ∃ claim occurrence word, ...
```

The invalid packet must continue to prove empty public traces and must make
`HasValidWholeQueryOccurrence` impossible for invalid ranges.

### 6.3 Headlines and paper root

`RMQ/Headlines/RMQ.lean` currently consumes:

- valid producer provenance at lines `92-99`;
- counted-source P at lines `141-144`;
- shared BP at lines `145-147`;
- mutation Q at line `148`;
- all four proofs in the paper-theorem constructor at lines `174-192`.

The standalone W18 aliases are at lines `270-286`. `RMQPaper.lean:1` imports
`RMQ.Headlines.RMQ`, so the paper root inherits exactly this chain.

W19 closure requires:

```text
indexed core occurrence theorem
  -> final model-adequacy field
  -> valid List Int projection
  -> headline alias and direct paper-main conjunction
  -> RMQPaper import

same ReviewerReadClaim.HasValidWholeQueryOccurrence
  -> all-counted successful reachability
  -> shared-BP consumer reachability
  -> fresh segment-21 rejection
  -> final adequacy / List theorem / paper-main conjunction
```

New axiom-check entries and claim-document rows should follow on the
implementation branch. This scout may not edit those files.

## 7. Requirement-by-requirement verdict

| Requirement | Current truth | W19 verdict / exact closure condition |
| --- | --- | --- |
| W18 `REQ-02.a` actual-prefix producer | True at event-value membership. | Keep as helper; replace as public evidence with indexed global/local/component positions and offset equations. Calling the current packet “occurrence-level” is false. |
| W18 `REQ-02.b` all counted sources | True only for isolated component attempted-read. | Insufficient for valid-query source liveness. Prove one successful valid whole-query occurrence per counted source, existential across inputs/queries. |
| `REQ-02.b.shared` | True as same-event component path. | Strengthen each consumer to the common valid-occurrence relation; do not infer unique ownership. |
| Occurrence preservation | Missing. | Global index, instruction index, local index, component index, and both embedding offsets are mandatory. Independent equal-value lookups fail the singleton mutation. |
| Invocation preservation | Missing from the public witness. | Retain every concrete constructor parameter and equations to the actual instruction/state computation. Parameter names without equations are letter-complete only. |
| Same positive/mutation relation | Failed. | Positive and fresh negative must use the exact same defined `HasValidWholeQueryOccurrence` (or an explicitly weaker common component-attempt predicate). |
| Valid-query domain | Missing from reverse P and Q. | Quantify a real `xs,left,right` with `ValidRange`; raw invalid traces cannot witness reachability. |
| Successful source use | Missing. | Positive reverse liveness must exhibit `some word`; forward provenance still covers both `some` and `none`. |
| All 20 constructors | Component attempted paths proved. | Small routes are source-clear; L/S long and sparse routes require checked structural witnesses. No all-source valid-query theorem exists now. |
| Fresh segment 21 | `not Q` is true. | Does not close parity because Q differs from P. Reprove absence using the same claim relation. |
| Repeated equal event | Untested by W18 membership. | Singleton two-select regression with distinct instruction/global positions is mandatory. |
| Tiny/invalid boundaries | Guarded invalid packet exists. | Connect it explicitly to absence of `HasValidWholeQueryOccurrence`; include empty/singleton/two-node tests. |
| `REQ-06.a` downstream consumption | Complete for W18 predicates. | Replace adequacy fields and paper conjunctions. Adding sibling wrappers is not consumption. |
| `REQ-06.b` inventories | Complete for W18 names. | Print the indexed core theorem, common positive/negative relation theorems, List projection, and headline/paper declarations. |
| Paper wording | Mostly admits W19 gap. | Reserve “occurrence-level” and “top-level reachability” for the new checked relations. Current headline comment at `RMQ/Headlines/RMQ.lean:268-271` should say event-value provenance until migrated. |

### False or underspecified requirement forms

The following must be rejected or rewritten:

1. **“Every source is reachable for every shape/query.”** False on empty and
   small shapes and incompatible with select branch exclusivity.
2. **“All 20 occur in one query.”** False in spirit and unnecessary: one
   selected occurrence cannot simultaneously take long, sparse, and dense
   branches.
3. **“A global and local lookup of the same value preserves occurrence.”**
   False under repeated equal events unless an offset/decomposition equation
   joins them.
4. **“Q is a closed-program producer predicate.”** False: Q ranges over an
   arbitrary instruction and state.
5. **“Same mechanism” with P=`HasProducerMayPath` and Q=`HasOperationalProducer`.**
   False: their carriers, quantifiers, and evidence differ.
6. **“Every segment has a source, therefore every source is used.”** False;
   total map coverage is not reverse reachability.
7. **“Every constructor has a component call, therefore every source is live.”**
   False without actual invocation and a valid top-level occurrence.
8. **“Invocation parameters are retained” merely because they occur inside an
   existential path constructor.** Underspecified unless they are exposed and
   equated to the producing instruction's computed arguments.
9. **“Successful-read provenance” as a replacement for all-read provenance.**
   Insufficient: failed attempts remain trace occurrences and must have indexed
   forward provenance.
10. **“New theorem exists” without replacing final adequacy/List/headline/paper
    consumers.** A letter-complete sibling, not W19 closure.

## 8. Proof risks and recommended order

1. Prove a generic indexed trace-append/get theorem and
   `evalGlobalWordTrace_event_at_producer`. Do not begin with 20 source cases.
2. Refine the instruction-to-component trace decomposition so it returns
   component positions, invocation data, and exact offsets. This is the hard
   reusable join.
3. Build the indexed forward capstone and consume it immediately in final
   adequacy and the valid List projection.
4. Define `ReviewerReadClaim.HasValidWholeQueryOccurrence` once.
5. Land D and C as small checked witness families, including success.
6. Formalize L and S symbolically through explicit Cartesian shapes and
   `CartesianShape.shape_representative`; do not materialize enormous lists.
7. Prove the all-counted successful reachability theorem by cases on
   `ReviewerSource`, using D/L/S/C.
8. Reprove fresh segment 21 and shared-BP consumer coverage with the same
   relation.
9. Replace the final adequacy, List, headline, and paper-main consumers; only
   then update the acceptance matrix and public claim docs.

Main proof risks:

- trace offsets through nested `bind`/append layers;
- repeated equal reads inside one instruction as well as across instructions;
- exposing currently private component trace-decomposition helpers;
- tying LCA interior `startBlock,count` to the actual selected closes;
- strict classification boundary arithmetic for L and S;
- proving all cited table reads return `some`, not merely emitting an attempted
  read;
- avoiding proof elaboration that tries to normalize lists of size `2^128`;
- preserving relational shared ownership for segments `17`-`19` and BP
  segments `0`/`19`.

No cost, payload-bit, physical-store, word-width, or executable-runtime claim
needs to change for this W19 repair. This is a semantic provenance and consumer-
closure migration.

## 9. Proof digestion

### Conceptual change required

W18 says, in effect, “this read value appears in the global trace, and some
actual folded instruction trace contains the same value.” W19 must say “the
read at this exact global position is the event at this exact local and
component position of this exact invocation.” It must also turn a manifest of
possible component calls into a manifest of sources that are demonstrably used
by at least one valid public query.

### Plain-English meaning

After the proposed W19 contract lands, a reviewer can point to any trace entry
and follow a positional receipt back through the program and component call.
They can also ask why each payload source is present and receive a real valid-
query execution that successfully reads it. Adding a plausible but unused
source fails the same test used to accept the real sources.

### Live assumptions

- The explicit D and C routes must be checked as successful occurrences.
- The L and S Cartesian constructions and their strict span arithmetic must be
  formalized.
- Invocation-specific component embeddings must expose exact trace offsets.
- The current physical/store/cost/space/width packets remain unchanged and are
  not being re-audited as W19 proof obligations here.

### Skeptical graduate-student question

Can Lean produce, for each of the 20 constructors, a valid `List Int` query and
an indexed `some word` occurrence whose program, instruction, local component,
and invocation-parameter receipts all compose—then reject segment 21 by the
very same relation? Until the answer is a checked theorem consumed by the paper
root, U2 remains open.

## 10. Next theorem-shaped target

The first target should be the reusable forward join, not a documentation or
manifest wrapper:

```lean
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_at_producer_provenance
    (shape : Cartesian.CartesianShape) (left right globalPos : Nat)
    {segment index : Nat} {word? : Option WordRAM.Word}
    (hget :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace[globalPos]? =
          some (.readWord segment index word?)) :
    ∃ source leaf produced,
      source.Counted ∧
      concreteBPNativeSuccinctRMQReviewerSegmentSource? segment = some source ∧
      ReviewerProducerInvocationPath
        produced leaf source segment index word?
```

Its acceptance test is the singleton repeated-select regression: the two equal
events must yield different instruction/global receipts. The next join after
that is the all-20 theorem through the common valid-occurrence relation, using
D/L/S/C and requiring `some word`.

## 11. Verification policy for this scout

This is a report-only branch. No Lean file, theorem inventory, public claim
document, or digestion log is permitted to change. Consequently no public
digestion update is appropriate here. Finalization must confirm:

```powershell
git diff --check
git status --short
git diff --name-only af8791150b64038e9c0776e3639634f1d83518ea..HEAD
```

and the commit must contain only
`docs/internal/U2_POSITIONAL_PROVENANCE_SCOUT.md`.
