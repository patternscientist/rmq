# LB-1 frozen prompt requirements

Base and workflow governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.

These requirement paragraphs are copied verbatim from the delegated contract. No proof edits preceded this file or the acceptance matrix. Evidence and statuses may change; requirements may change only by an explicit coordinator amendment.

## REQ-LB-COUNT

Define payload-only exact RMQ encodings by bitstrings of length at most B, allowing length to be observed. Prove the finite cardinal bound 2^(B+1)-1 and shape injectivity from valid half-open leftmost answers. Derive the coefficient-correct doubled Catalan lower bound at 2*(B+1), or a strictly sharper bound proved from the same model.

## REQ-LB-PQ1

Serialize the actual PQ1 buildMemory cells at wordWidth n, fixed for each n, and prove serialization injective on finite word lists with entries below 2^wordWidth(n), allocation encoding injective on size-n Cartesian shapes, and the decoder's exact RMQ contract using only serialized cells, n, endpoints and n-only fixed advice. The decoder must not retain xs or an uncounted shape. Distinct List Int inputs with the same shape intentionally share memory: no value-list injectivity is asserted. Address variable allocation length explicitly; plain zero padding is not injective.

## REQ-LB-MODEL

Prove a worst-case-over-inputs lower bound on a uniform allocation budget and a two-sided comparison with the actual PQ1 2n+rho(n) allocation. Separate payload, fixed code, scratch and external n/advice conventions. Do not equate a fixed-length encoding with a variable-length one or assert the lower bound for every individual input.

## REQ-LB-CONSUMER

One checked capstone/typed consumer must compose the generic counting theorem, exact decoder and actual allocation object; independently expand its predicates to exclude vacuous domains and proof-only decoding oracles.

## CHK-LB-CONTROLS

Persist empty/singleton, equal-key/leftmost, all-zero/empty-string collision, null/wrong-answer decoder, deleted exactness, permitted n-only advice and rejected input/shape-dependent advice controls. A mutation must fail the same proposition as the positive theorem, not merely change a surrounding log or a declaration name.

## REPLAY-EXACT-REGISTRY

any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure.

## REPLAY-SELECTOR-NONVACUITY

omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing.

## REPLAY-SUBPROCESS-DEADLINE

run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed.
