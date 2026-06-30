# Rank/Select Compressed/FID Digest (2026-06-29)

Base: `main` at `af897e1` ("Promote compressed FID rank-select capstone").

Audience: mathematically mature reader. No data-structures, monad, or
proof-technique background is assumed. Everything specific is defined on first
use.

This digest explains the landed fixed-weight compressed/FID rank/select
capstone, how it differs from the plain Jacobson/Clark spoke, why "fixed-weight
payload" is genuinely *compression*, and why the Word-RAM interpreter plan
(`docs/internal/WORD_RAM_INTERPRETER_REFINEMENT_PLAN.md`) is the next hardening
layer rather than a fix.

Theorem of record:
`RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile`
(headline alias `RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile`).
The pointwise component theorem remains
`RMQ.RankSelect.compressedFIDFixedWeightConstantQueryProfile`.

## 0. First-contact vocabulary

- **Bitvector**: a finite string of bits, `bits : List Bool`, of length `n`.
  Write `k` for its number of `1`s (its *weight*, `trueCount bits`).
- **The three dictionary queries**, for a chosen bit value `b ∈ {0,1}`:
  - `access i` — the bit at position `i`;
  - `rank b i` — how many `b`-bits occur strictly before position `i`;
  - `select b j` — the position of the `j`-th `b`-bit.
- **Index / "directory"**: a stored bit string (the *payload*) together with a
  fixed recipe that answers the three queries by *reading the payload*.
- **Payload bits**: the bits actually stored and read. The project deliberately
  separates these from proof-only data (certificates, function fields).
- **Modeled cost**: a query's cost is the number of unit-cost primitive steps
  (indexed payload reads, fixed word operations) in the project's RAM/`Costed`
  model. It is *not* Lean runtime and *not* CPU time.

## 1. What the theorem says

For **every** bitvector `bits` (length `n`, weight `k`):

1. **Space.** The stored payload has length
   `≤ fixedWeightPayloadBudget bits + overhead(n)`, where
   `fixedWeightPayloadBudget bits = ⌊log₂ C(n,k)⌋ + 1`
   (`C(n,k)` is the binomial coefficient, defined by Pascal's recurrence as
   `binomialCount`), and `overhead` is **sublinear**: formally `LittleOLinear`,
   i.e. for every constant `c` there is a threshold past which `c·overhead(n) ≤ n`.
2. **Exactness.** `access`, `rank b`, and `select b` return exactly the
   reference answers (`bits[i]?`, `Succinct.rankPrefix`, `Succinct.select`), for
   both `b = 0` and `b = 1`.
3. **Time.** Each query costs at most one **fixed constant**
   `compressedFIDFixedWeightQueryCost`, independent of `n`.

In one line: **store `⌈log₂ C(n,k)⌉ + o(n)` bits and answer all three queries
exactly in constant modeled time.** This is the classical Raman–Raman–Rao (RRR)
*fully indexable dictionary* (FID) result. The contribution here is a
machine-checked, payload-accounted proof of it — not a new algorithm or bound.

Faithful caveats. The public statement is now a reusable **family** profile over
all `bits`, with overhead a function of `n = bits.length` only. The cost is
**modeled** (see section 4), and every individual directory is still available
through the pointwise theorem above.

## 2. How it differs from plain Jacobson/Clark

The plain spoke `RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery` stores the `n`
input bits **verbatim** plus an `o(n)` auxiliary structure: payload `n + o(n)`,
the same three exact queries, the same constant modeled cost. Its primary term is
`n` regardless of `k`.

The compressed/FID capstone is **deliberately parallel** and changes exactly one
thing: it replaces that primary `n` with the entropy `⌊log₂ C(n,k)⌋ + 1`. The
exact queries, the `o(n)` auxiliary (a *different*, construction-specific
sublinear function — not literally the same `o(n)` as the plain spoke), and the
constant modeled cost all keep the same shape.

Because `C(n,k) ≤ 2ⁿ`, the entropy term never exceeds `n` asymptotically; when
`k` is bounded away from `n/2` it is strictly — often dramatically — smaller
(for `k = O(1)`, `log₂ C(n,k) = O(log n)`). Near `k ≈ n/2` the saving is only the
lower-order `O(log n)` term. So "compressed" means: **pay for the information
content, not the length.**

## 3. Why fixed-weight payload means compression

"Fixed-weight" names the *coding universe*, not a restriction on the input. Given
an input of weight `k`, consider all length-`n` bitvectors of that **same** weight
`k`. There are exactly `C(n,k)` of them. Naming one element of a `C(n,k)`-element
set takes `⌈log₂ C(n,k)⌉` bits — the information-theoretic floor.

The construction stores precisely that. It fixes a canonical enumeration of the
weight-`k` universe and records the input's **index** in that enumeration as a
binary number:

- `fixedWeightEncode?` / `fixedWeightDecode?` are the rank / unrank maps, proved
  mutually inverse (`fixedWeightCodecRoundTrip`, `fixedWeightDecodeEqSomeIff`);
- `fixedWeightCode` is the index, proved `< C(n,k)` and `< 2^(budget)`;
- `fixedWeightPackedPayload` writes it in **exactly** `⌊log₂ C(n,k)⌋ + 1` bits,
  reading back to the index and decoding to the original vector
  (`fixedWeightPackedPayloadProfile`).

This is enumerative (arithmetic) coding specialized to the constant-weight code:
zero redundancy up to the `+1` rounding bit. That is the precise sense in which
"fixed-weight payload" *is* compression — the primary payload is the entropy of
the weight-`k` universe.

The non-obvious part — the actual FID content — is keeping queries fast **without
decoding the whole index**. The construction:

- cuts the vector into **sub-logarithmic** blocks (≈ `(log₂ n)/c` bits each);
- stores each block's small enumerative code, plus its weight ("class") and
  length in a **narrow** per-block table (`log log n`-scale fields);
- shares **one** universal decode table across all blocks of a given
  length/weight; and
- adds two-level navigation so a single query reads only `O(1)` blocks/words.

The sub-log block size is essential: it forces the shared decode table and the
per-block metadata to be `o(n)`. The repository records the matching impossibility
results for the naive designs — `noFixedWeightLogChunkDenseDecoderLittleO` (a
dense decode table at full-log block size is *not* `o(n)`) and
`fixedWeightLogChunkRouteWidthClassLengthOverheadNotLittleO` (padding the
class/length fields to the wide route width is already linear) — so the chosen
narrow, sub-log design is not arbitrary.

## 4. Why the Word-RAM interpreter plan is the next hardening layer

The constant-cost claim lives in a **modeled** layer: a `Costed` value is a pair
`(answer, cost)`, and the RAM substrate charges indexed reads and fixed word
operations as unit cost. This is the standard succinct-data-structure accounting,
and the construction is already **anti-oracle disciplined**: queries read
width-bounded, payload-only stores; exactness is *derived from* those charged
reads; and several tempting shortcuts are formally ruled out (the
`noFixedWeight…` obstruction theorems; the recorded
`chargedSelectPositionSource_allows_empty_select_oracle` pitfall).

But the cost is a **projection, not an execution**. Nothing in the *type* of a
`Costed` value forces the answer to have been computed from the reads:
`Costed.tickValue` can pair any cost with any value, and `RAM.Exec` keeps a value
beside its trace. A determined skeptic can still ask: *are the answers genuinely
produced by reading the counted payload, or could a proof consult the original
vector and merely charge a plausible cost?*

The Word-RAM interpreter plan answers this **by construction**. It adds a small
first-order instruction language with a deterministic interpreter
`eval : Program → Store → Result` over a **payload-only** memory (finite segments
with explicit width/word bounds, no proof fields), proves
`eval(p,s).toCosted.cost = trace.length` and that the interpreter can read *only*
payload, and then proves each existing query equal to / refined by such a program.
The direction is fixed — `Program → eval → Costed`, never `Costed → Program` —
precisely so the oracle escape cannot reappear.

After that layer, the headline strengthens from "a costed function has the right
answer and cost" to "a fixed program that can only touch counted payload memory
produces the answer in that many steps." It is **hardening, not repair**: the
existing theorems stay true; the interpreter makes the "O(1)-from-payload-reads"
claim true by construction rather than by disciplined convention — the same
refinement pattern as CompCert, CakeML, and the Isabelle/CoqEAL refinement
stacks.

## One-line takeaways

- **Theorem**: per bitvector, payload `log₂ C(n,k) + o(n)`, exact
  access/rank/select, constant modeled query — a verified RRR/FID result.
- **vs plain**: same theorem shape with the primary `n` replaced by entropy
  `log₂ C(n,k)`.
- **Compression**: the payload is the index of the input among the `C(n,k)`
  vectors of its own weight — the entropy floor.
- **Next**: a Word-RAM interpreter so the answer is *executed* from payload, not
  just costed.

## Adversarial classroom loop (record)

Run inline against the five reviewer personas of the digestion protocol
(`docs/DIGESTION_LOG.md`): drafted, attacked from each perspective, and revised.
This pass was run by the author rather than by separate reviewer agents; it can
be re-run with independent agent skeptics for an external check.

Holes raised and resolved in revision:

- *Mathematically mature reader.* "Is `⌊log₂ C(n,k)⌋ + 1` the entropy or an
  off-by-one?" → stated explicitly that `log₂ C(n,k)` is the floor and `+1` is the
  rounding bit (zero redundancy up to one bit). "Is the `o(n)` here the same as the
  plain spoke's?" → no; flagged it as a different, construction-specific sublinear
  function.
- *Data-structures researcher.* "This is RRR/FID — a known result." → reframed the
  contribution as the *formalization*, not a new bound (matches `WHAT_IS_PROVED.md`
  non-claims). "Does 'fixed-weight' restrict the input?" → clarified it names the
  coding universe and adapts to each input's own weight `k`. "Both `b=0` and `b=1`?"
  → yes, queries quantify over `target : Bool`.
- *Cost-model skeptic.* "Modeled `O(1)` can be faked via `tickValue`." → that is
  exactly §4; stated the present anti-oracle discipline and the obstruction
  theorems, and that execution-backing is explicitly the *next* layer, not a
  current claim.
- *Lean/library maintainer.* "Is the stated theorem faithful?" → the five
  conjuncts (entropy-budget payload bound, `LittleOLinear` overhead, and the three
  exact-plus-cost-bounded query clauses) are taken directly from
  `compressedFIDFixedWeightFamilyProfile`; noted that the pointwise theorem is
  still available as the one-bitvector component.
- *Audience explainer.* "One-line version?" → added the takeaways block.

Stable: a reader can now state the theorem, its scope (modeled cost,
formalization-of-RRR), the compression mechanism, and the live nonclaim
(execution-backing) without reading the Lean proof.
