# RMQ program plan — defect species record

Companion to `RMQ_PROGRAM_PLAN_v14.md`.

## What this file does and does not contain

It records **the kinds of defect** the adversarial audits of this plan found, so a future revision can be checked against them. It contains **no
per-revision attribution table**, deliberately.

The first version of this file had one. **The following account of it is
UNVERIFIABLE by the same argument this file goes on to make — that file exists on
no ref.** It is kept because the lesson does not depend on the details: two of
its rows were wrong on measurement — it charged a revision with a miscitation that revision had in
fact *diagnosed*, and it claimed "five consecutive revisions" failed a rule
where the true figure was three, non-consecutive. Three of its four
carry-ranges for false universals were also overstated.

That is the same error again, in the file created to prevent it. No ordinal is
given, per species 3 below.
The conclusion is structural, not motivational: **claims about which revision of this plan
said what cannot be checked against any committed artifact** -- the revisions
v2 through v13 exist on no ref, so the only witnesses are other uncommitted
files. **The revision at the current pin IS committed** (`RMQ_PROGRAM_PLAN.md`,
H item 5), which changes this going forward and not backward: a future claim
about what this revision said is checkable; every claim about v2-v13 is not.
Some are checkable against the uncommitted files themselves -- A.3's ten
non-goals and A.4's six DD entries were both re-derived from v2 that way -- and
the point is that maintaining a table of them has repeatedly produced false
claims, not that every such claim is beyond reach.
So they are not maintained.

If a specific revision's text is ever needed, read that file. Do not write down
what it said.

## The defect species, and how each was caught

**1. A checker narrowed rather than fixed, while its commit message says the
kind is addressed.** The citation checker's worst case was narrowed twice by
successive audits, and a third then found field *assignments*
(`name :=`) still counting as declaration sites — a sequence
`WORKFLOW_DESIGN_DECISIONS.md:10075-10078` records as "the third round in which
the citation checker was narrowed rather than fixed". Each round's write-up claimed the
kind was closed. Caught only by an adversary constructing a new input.

**2. A patch that silently matches nothing and reports success.** Three in one
round: a `-like` pattern where backslash is not an escape; a filter on the wrong
enumeration; a CRLF/LF mismatch. Each printed "patched" and changed nothing. The
fix is to assert the search text is present before writing.

**3. A hand-maintained tally beside the list it tracks.** Rots exactly like a
line pointer when the list grows. Observed on the citation-rot list, the audit
counts, and the obligation count. The fix is to name artifacts instead of
counting them, or to give no number at all.

**4. An over-broad universal, asserted in the paragraph convicting a predecessor
of the same thing.** No count is given, per species 3. The instances found:
"Every SHA below…", "Every misquotation…", "every version since…", and a
superlative attributing an "only mechanism" claim to a section that contains no
such item. Each was written to summarise a
pattern and overshot the evidence assembled beside it.

**5. A quotation stopped one clause before the text that refutes the
surrounding claim.** Twice against `wf3_attack.json`'s `best` field, at the
clause naming an obligation neither contract contains.

**6. A line pointer rotting in the revision whose purpose was repairing a stale
pin.** `gate.ps1:117`/`:120-124` were correct at one pin and stale at the next,
in the sentence offering them as corroboration.

**7. A rule stated and violated in the same passage.** "No other status is
permitted" was violated twice over nine days. A stale-list prohibition was
stated inside the stale list. A no-revision-commentary rule was stated as
accomplished in a document that still carried many instances of it.

**8. Scripted editing damaging prose.** Clause-deletion by regex left six broken
sentences, one of which asserted a *new* false claim about the repository by
orphaning a predicate onto the wrong subject. Bulk edits to prose need reading
afterwards, not just measuring.

## The one mechanism worth carrying forward

A false accusation entered this plan because an audit finding was adopted
without being checked. The report said a predecessor was right and that two
later revisions had truncated a quotation; the quoted text was confirmed to
exist, and the check stopped there. Nobody counted the underlying tags.
Counting them showed the opposite.

**The quotation was verified and the arithmetic was not.**

It happened again, and was caught in time. A later report called a claim about
v3 contradicted, citing a sentence in v4 that does say what the report said it
says. v4 was wrong about v3, and v3 was in the same directory. **The citation
was verified and the referent was not.**

That extends the standing rule — a claim is worth what was measured — to
findings **received**, not only repairs made. An auditor's conclusion is an
input to be checked, not an output to be adopted. The plan reproduces this account at §A.2b, both instances and both epigrams,
because it is a method rule
rather than history. Several of the species above are also stated as rules in §J — the
citation-checker progression, the no-op patches, the tally species, the
line-pointer species, and the permitted-status violation — so this file and §J
deliberately overlap where the lesson is a rule; they diverge where it is
history, which stays here.
