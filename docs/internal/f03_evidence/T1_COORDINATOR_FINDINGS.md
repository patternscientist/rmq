# T1 coordinator findings — read before proving a table-reader lemma

Written 2026-07-26 by C06, mid-campaign. `origin/main` = `db43b25`.

## The reusable core is already proved, and it is `rfl`

`RMQ/Core/SuccinctSpace/WordStoreRAM.lean:26-29`:

```lean
def readProgram
    {payload : List Bool} (_store : PayloadWordStore payload) (i : Nat) :
    WordRAM.Program .optWord :=
  WordRAM.Program.readWord 0 i
```

**The store is bound as `_store` — unused.** The emitted program is literally
`readWord 0 i`, independent of the payload. This is the same mechanism that
closed the interior cone (`machineReadComputationAt`'s unused `_table`), and
every fixed-width table read funnels through it (`TablesRAM.lean:53-57`,
`:145-149`).

Verified in `scratchpad/t1_readprogram_core.lean`, all three by `rfl`, and
`#print axioms` reports **"does not depend on any axioms"** for each — not even
`propext`:

```lean
theorem payloadWordStore_readProgram_content_irrelevant
    {p1 p2 : List Bool} (s1 : PayloadWordStore p1) (s2 : PayloadWordStore p2)
    (i : Nat) : s1.readProgram i = s2.readProgram i := rfl

theorem fixedWidthNatTable_readProgram_content_irrelevant
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1) (t2 : FixedWidthNatTable e2 w2) (i : Nat) :
    t1.readProgram i = t2.readProgram i := rfl        -- widths need not agree

theorem fixedWidthOptionNatTable_readProgram_content_irrelevant
    {e1 e2 : List (Option Nat)} {w : Nat}
    (t1 : FixedWidthOptionNatTable e1 w) (t2 : FixedWidthOptionNatTable e2 w)
    (i : Nat) : t1.readProgram i = t2.readProgram i := rfl
```

Namespaces: the structures live in `RMQ.SuccinctSpace`, **not**
`RMQ.SuccinctSpace.WordRAMBridge` (`Tables.lean:23`, `:223`) — that mistake costs
a round-trip.

## What this does and does not settle

**Settles: the ADDRESS half.** No table's contents can influence an issued
address, at any depth, in any reader that goes through `readProgram`. Do not
re-derive this.

**Does NOT settle: the DECODE half.** `readTraceResultRelabeledWithStore`
(`GenericSelect/RAMStoreParam.lean:258`) wraps the program in
`WordRAM.TraceResult.ofProgramWithStore` and then decodes the reply. Decoding
uses `width` (e.g. `Program.mapOptWordOptionNat width`), so a reader lemma still
needs the widths to agree. For `sparseExceptionSelectData` those widths are
`f bits.length` (`Source.lean:2375-2383`), so this is a size-only obligation, not
a content one — but it must be discharged, not assumed.

**Also does not settle** the entry-list LENGTH obligations, which remain the
genuinely open part of T1 — in particular `longSuperRelativeEntries` and
`sparseDirectory.relativeEntries`, empty in every executable regime precisely
because `superIsLong` never fires below n ≈ 13,276.

## The structural claim to lean on

At `ChargedRankSelectLeafTrace.lean:1176` the long/sparse branch tests
`relativeSplitSelectEntryIsMarked super`, where `super` is bound from
`data.superTable.readTraceResultRelabeledWithStore … store …` — a decoded PROBE
REPLY, not `superIsLong`. Confirm it, then use it: it means the frontier
predicate never appears in the trace function at all, only in table
construction.
