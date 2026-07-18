import RMQ.Core.WordRAM.E1RankBlock
import RMQ.Core.WordRAM.E1QueryProgram
import RMQ.Core.GenericSelect.RAMStoreParam

/-!
# E1 amended machine: select-close read sub-blocks (M3c-5a)

Worklog RESUME steps 2 and 3: the entry-table 4-read sub-block and the
relative-offset read sub-block consumed by the select-close dispatch
(`bpChunkedSelectTraceResultWithStore`, `ChargedRankSelectLeafTrace.lean`).

Route side, the accepted 4-read evaluator
`FixedWidthSparseDenseSelectDenseLocalEntryTable.
readTraceResultRelabeledWithStore` (`GenericSelect/RAMStoreParam.lean`) is
four `TraceResult.ofProgramWithStore (singletonSegmentMap fieldSeg dead)
store (table.readProgram i)` binds ending in `entryOfFields`, and each
bind's trace reduces definitionally to one `readWord fieldSeg i` event
against the supplied store with the field decoded by `bitsToNatLE`.  This
module derives those reductions (`ofProgramWithStore_natTable_trace/
_value`, `entryRead_trace_eq/_value_eq`, `relativeRead_trace_eq/
_value_eq`) and provides the machine sub-blocks:

* `entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4` — 12 instructions: four
  `readMem`s (slot index in `rP`, field destinations parametric so the
  dispatch can instantiate the super bank `30..33` and the local bank
  `34..37`), then the none-test sum (`const`/`natEq`/`add` chain leaving
  the miss indicator in `rA`: zero iff every field read succeeded);
* `entryReadBlock_runsTo` — exact-fuel simulation: receipts POSITIONALLY
  EQUAL to `entryFieldEvents` (= the accepted entry-table read trace by
  `entryRead_trace_eq`), the four shifted field decodes
  (`decodeRead` convention) parked in the destination registers, the miss
  indicator in `rA`, everything outside the write set preserved;
* `relativeReadBlock A S` — 4 instructions (read at `rSlot`, present test,
  packet assembly `base + offset + 1` from `xBPos`) with
  `relativeReadBlock_runsTo` delivering the accepted relative-offset read
  value under `decodePacket` in `rT`;
* width certificates `entryReadBlock_fits` / `relativeReadBlock_fits`
  (constructor-exhaustive, REQ-E1-02 consumption);
* decode connectors `entryOfFields_decode_some/_decode_none`,
  `missSum_eq_zero_iff`, `relativeSplitSelectEntryIsMarked_iff` for the
  dispatch's option tests and marked tests.

Register-allocation decision (recorded as DD-20260718-007): the frozen
EXTENSION BANK `28..39` holds the dispatch state that must survive the
hosted component folds (whose preservation guarantees cover `28 <= r`):
`xIdx/xQ = 28/29` (query occurrence index and occurrence), super entry
fields `xSF1..xSF4 = 30..33`, local entry fields `xLF1..xLF4 = 34..37`,
`xBPos/xBOcc = 38/39` (branch base position/occurrence).  Field registers
hold the SHIFTED `decodeRead` encode (`0` = missing, `field + 1` =
present), so the dispatch's none-propagation and marked tests are ordinary
register comparisons.
-/

namespace RMQ
namespace WordRAM
namespace E1SelectBridge

open E1Machine
open E1RankBlock
open RMQ.GenericSelect

/-! ## Frozen extension bank (28..39, DD-20260718-007)

Dispatch state that survives every hosted component fold: the seeded rank
blocks preserve `r <= 8 ∨ 28 <= r`, the atomic fold and select fold
preserve their write-set complements, all of which include `28 <= r`. -/

/-- Query occurrence index `idx` (dispatch input). -/
abbrev xIdx : Nat := 28
/-- Query occurrence `q = queryOccurrence idx`. -/
abbrev xQ : Nat := 29
/-- Super entry field `baseOccurrence` (shifted `decodeRead` encode). -/
abbrev xSF1 : Nat := 30
/-- Super entry field `baseWordIndex` (shifted). -/
abbrev xSF2 : Nat := 31
/-- Super entry field `rankBefore` (shifted). -/
abbrev xSF3 : Nat := 32
/-- Super entry field `firstOffset` (shifted). -/
abbrev xSF4 : Nat := 33
/-- Local entry field `baseOccurrence` (shifted). -/
abbrev xLF1 : Nat := 34
/-- Local entry field `baseWordIndex` (shifted). -/
abbrev xLF2 : Nat := 35
/-- Local entry field `rankBefore` (shifted). -/
abbrev xLF3 : Nat := 36
/-- Local entry field `firstOffset` (shifted). -/
abbrev xLF4 : Nat := 37
/-- Branch base position. -/
abbrev xBPos : Nat := 38
/-- Branch base occurrence. -/
abbrev xBOcc : Nat := 39

/-! ## Route-side reduction: the relabeled store-parametric read atoms -/

/-- One relabeled fixed-width-table read against the supplied store is one
`readWord` event at the mapped segment. -/
theorem ofProgramWithStore_natTable_trace
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (S dead : Nat) (store : ReadStore) (i : Nat) :
    (TraceResult.ofProgramWithStore (singletonSegmentMap S dead) store
        (table.readProgram i)).trace =
      [TraceEvent.readWord S i (store.readWord? S i)] := rfl

/-- One relabeled fixed-width-table read decodes the fetched word by
`bitsToNatLE`. -/
theorem ofProgramWithStore_natTable_value
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (S dead : Nat) (store : ReadStore) (i : Nat) :
    (TraceResult.ofProgramWithStore (singletonSegmentMap S dead) store
        (table.readProgram i)).value =
      (store.readWord? S i).map bitsToNatLE := rfl

/-- The four entry-table field read events, in evaluator order. -/
def entryFieldEvents (store : ReadStore) (S1 S2 S3 S4 i : Nat) :
    List TraceEvent :=
  [ .readWord S1 i (store.readWord? S1 i)
  , .readWord S2 i (store.readWord? S2 i)
  , .readWord S3 i (store.readWord? S3 i)
  , .readWord S4 i (store.readWord? S4 i) ]

/-- The accepted entry-table 4-read trace is exactly the four field read
events against the supplied store at the layout's segments. -/
theorem entryRead_trace_eq
    {entries : List SparseDenseSelectDenseLocalEntry} {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
    (store : ReadStore) (i : Nat) :
    (table.readTraceResultRelabeledWithStore layout store i).trace =
      entryFieldEvents store layout.baseOccurrence layout.baseWordIndex
        layout.rankBefore layout.firstOffset i := rfl

/-- The accepted entry-table 4-read value is `entryOfFields` over the four
`bitsToNatLE` field decodes of the supplied store's words. -/
theorem entryRead_value_eq
    {entries : List SparseDenseSelectDenseLocalEntry} {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable entries fieldWidth)
    (layout : SparseDenseEntryTableTraceSegmentBases)
    (store : ReadStore) (i : Nat) :
    (table.readTraceResultRelabeledWithStore layout store i).value =
      FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
        ((store.readWord? layout.baseOccurrence i).map bitsToNatLE)
        ((store.readWord? layout.baseWordIndex i).map bitsToNatLE)
        ((store.readWord? layout.rankBefore i).map bitsToNatLE)
        ((store.readWord? layout.firstOffset i).map bitsToNatLE) := rfl

/-- The accepted relative-offset read trace is one `readWord` event at the
relative segment. -/
theorem relativeRead_trace_eq
    {entries : List Nat} {width : Nat} (S dead : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (store : ReadStore) (base slot : Nat) :
    (relativeOffsetReadTraceResultRelabeledWithStore S dead table store
        base slot).trace =
      [TraceEvent.readWord S slot (store.readWord? S slot)] := rfl

/-- The accepted relative-offset read value is the base-shifted
`bitsToNatLE` decode of the supplied store's word. -/
theorem relativeRead_value_eq
    {entries : List Nat} {width : Nat} (S dead : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (store : ReadStore) (base slot : Nat) :
    (relativeOffsetReadTraceResultRelabeledWithStore S dead table store
        base slot).value =
      ((store.readWord? S slot).map bitsToNatLE).map
        (fun offset => base + offset) := rfl

/-! ## Decode connectors (shifted field registers vs `entryOfFields`) -/

/-- When every field read succeeds (nonzero shifted decode), the entry is
present with each field one below its shifted register value. -/
theorem entryOfFields_decode_some
    {w1? w2? w3? w4? : Option Word}
    (h1 : decodeRead w1? ≠ 0) (h2 : decodeRead w2? ≠ 0)
    (h3 : decodeRead w3? ≠ 0) (h4 : decodeRead w4? ≠ 0) :
    FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
        (w1?.map bitsToNatLE) (w2?.map bitsToNatLE)
        (w3?.map bitsToNatLE) (w4?.map bitsToNatLE) =
      some
        { baseOccurrence := decodeRead w1? - 1
          baseWordIndex := decodeRead w2? - 1
          rankBefore := decodeRead w3? - 1
          firstOffset := decodeRead w4? - 1 } := by
  cases w1? with
  | none => exact absurd rfl h1
  | some w1 =>
      cases w2? with
      | none => exact absurd rfl h2
      | some w2 =>
          cases w3? with
          | none => exact absurd rfl h3
          | some w3 =>
              cases w4? with
              | none => exact absurd rfl h4
              | some w4 =>
                  simp [FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields,
                    decodeRead]

/-- When any field read fails (zero shifted decode), the entry is absent. -/
theorem entryOfFields_decode_none
    {w1? w2? w3? w4? : Option Word}
    (h : decodeRead w1? = 0 ∨ decodeRead w2? = 0 ∨
      decodeRead w3? = 0 ∨ decodeRead w4? = 0) :
    FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
        (w1?.map bitsToNatLE) (w2?.map bitsToNatLE)
        (w3?.map bitsToNatLE) (w4?.map bitsToNatLE) = none := by
  cases w1? <;> cases w2? <;> cases w3? <;> cases w4? <;>
    simp [FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields] <;>
    simp [decodeRead] at h

/-- The miss-indicator sum is zero exactly when every shifted field decode
is nonzero (every field read succeeded). -/
theorem missSum_eq_zero_iff (d1 d2 d3 d4 : Nat) :
    (if d1 = 0 then 1 else 0) + (if d2 = 0 then 1 else 0) +
        (if d3 = 0 then 1 else 0) + (if d4 = 0 then 1 else 0) = 0 ↔
      (d1 ≠ 0 ∧ d2 ≠ 0 ∧ d3 ≠ 0 ∧ d4 ≠ 0) := by
  by_cases h1 : d1 = 0 <;> by_cases h2 : d2 = 0 <;>
    by_cases h3 : d3 = 0 <;> by_cases h4 : d4 = 0 <;>
    simp [h1, h2, h3, h4]

/-- The marked test on an entry is an ordinary nonzero test on its
`rankBefore` field. -/
theorem relativeSplitSelectEntryIsMarked_iff
    (entry : SparseDenseSelectDenseLocalEntry) :
    relativeSplitSelectEntryIsMarked entry = true ↔
      entry.rankBefore ≠ 0 := by
  simp [relativeSplitSelectEntryIsMarked, bne]

/-! ## Entry-table 4-read machine sub-block -/

/--
The entry-table 4-read sub-block: read the four field tables at the slot
index in `rP` into the parametric destination registers `F1..F4` (shifted
`decodeRead` encode), then compute the miss indicator into `rA` (zero iff
every field read succeeded) using scratch `rB`/`rT`.
-/
def entryReadBlock (S1 S2 S3 S4 F1 F2 F3 F4 : Nat) : List Instr :=
  [ .readMem F1 S1 rP
  , .readMem F2 S2 rP
  , .readMem F3 S3 rP
  , .readMem F4 S4 rP
  , .const rB 0
  , .natEq rA F1 rB
  , .natEq rT F2 rB
  , .add rA rA rT
  , .natEq rT F3 rB
  , .add rA rA rT
  , .natEq rT F4 rB
  , .add rA rA rT ]

@[simp] theorem entryReadBlock_length (S1 S2 S3 S4 F1 F2 F3 F4 : Nat) :
    (entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4).length = 12 := rfl

/-- Frozen category log of the entry-table 4-read sub-block. -/
def entryReadCats : List Category :=
  [ .memoryRead, .memoryRead, .memoryRead, .memoryRead
  , .registerWrite, .comparison, .comparison, .arithmetic
  , .comparison, .arithmetic, .comparison, .arithmetic ]

@[simp] theorem entryReadCats_length : entryReadCats.length = 12 := rfl

theorem entryReadBlock_straight (S1 S2 S3 S4 F1 F2 F3 F4 : Nat) :
    ∀ instr ∈ entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4,
      instr.isStraight = true := by
  intro instr hi
  simp only [entryReadBlock, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl <;> rfl

/--
Exact-fuel simulation of the entry-table 4-read sub-block: from block
entry with the slot index in `rP`, the hosted block runs to `A + 12` with

* receipts POSITIONALLY EQUAL to `entryFieldEvents store S1 S2 S3 S4 i`
  (= the accepted entry-table read trace by `entryRead_trace_eq`),
* the four shifted field decodes in the destination registers,
* the miss indicator in `rA` (zero iff every field read succeeded, via
  `missSum_eq_zero_iff`),
* the frozen category log `entryReadCats`, and
* every register outside `{F1, F2, F3, F4, rT, rA, rB}` preserved.

The destination registers are parametric (dispatch instantiates the super
bank `30..33` and the local bank `34..37`); they must be pairwise distinct
extension-bank registers (`28 ≤ F`).
-/
theorem entryReadBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {A S1 S2 S3 S4 F1 F2 F3 F4 : Nat}
    (hhost : HostedAt program A (entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4))
    (hF1 : 28 ≤ F1) (hF2 : 28 ≤ F2) (hF3 : 28 ≤ F3) (hF4 : 28 ≤ F4)
    (h12 : F1 ≠ F2) (h13 : F1 ≠ F3) (h14 : F1 ≠ F4)
    (h23 : F2 ≠ F3) (h24 : F2 ≠ F4) (h34 : F3 ≠ F4)
    (regsA : RegFile) (i : Nat) (hIdx : regsA rP = i) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regsA, A, false⟩ ⟨regsF, A + 12, false⟩
        (entryFieldEvents store S1 S2 S3 S4 i) entryReadCats ∧
      regsF F1 = decodeRead (store.readWord? S1 i) ∧
      regsF F2 = decodeRead (store.readWord? S2 i) ∧
      regsF F3 = decodeRead (store.readWord? S3 i) ∧
      regsF F4 = decodeRead (store.readWord? S4 i) ∧
      regsF rA =
        ((if decodeRead (store.readWord? S1 i) = 0 then 1 else 0) +
          (if decodeRead (store.readWord? S2 i) = 0 then 1 else 0) +
          (if decodeRead (store.readWord? S3 i) = 0 then 1 else 0) +
          (if decodeRead (store.readWord? S4 i) = 0 then 1 else 0)) ∧
      (∀ r, r ≠ F1 → r ≠ F2 → r ≠ F3 → r ≠ F4 → r ≠ 19 → r ≠ 22 →
        r ≠ 23 → regsF r = regsA r) := by
  have e11 : F1 ≠ 19 := by omega
  have e12 : F1 ≠ 22 := by omega
  have e13 : F1 ≠ 23 := by omega
  have e21 : F2 ≠ 19 := by omega
  have e22 : F2 ≠ 22 := by omega
  have e23 : F2 ≠ 23 := by omega
  have e31 : F3 ≠ 19 := by omega
  have e32 : F3 ≠ 22 := by omega
  have e33 : F3 ≠ 23 := by omega
  have e41 : F4 ≠ 19 := by omega
  have e42 : F4 ≠ 22 := by omega
  have e43 : F4 ≠ 23 := by omega
  have a1 : (10 : Nat) ≠ F1 := by omega
  have a2 : (10 : Nat) ≠ F2 := by omega
  have a3 : (10 : Nat) ≠ F3 := by omega
  have hrun := RunsTo.straight store
    (entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4)
    (entryReadBlock_straight S1 S2 S3 S4 F1 F2 F3 F4) A hhost regsA
  obtain ⟨regsF, hregsF⟩ :
      ∃ x, straightRegs store (entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4)
        regsA = x := ⟨_, rfl⟩
  rw [hregsF] at hrun
  have hreads :
      straightReads store (entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4)
          regsA =
        entryFieldEvents store S1 S2 S3 S4 i := by
    simp [entryReadBlock, straightReads_cons, straightStepEvent,
      straightStepRegs, RegFile.write, entryFieldEvents, rP,
      a1, a2, a3, hIdx]
  rw [hreads] at hrun
  have hcats :
      (entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4).map Instr.category =
        entryReadCats := rfl
  rw [hcats, entryReadBlock_length] at hrun
  have hV1 : regsF F1 = decodeRead (store.readWord? S1 i) := by
    rw [← hregsF]
    simp [entryReadBlock, straightRegs_cons, straightStepRegs,
      RegFile.write, rP, rA, rB, rT, e11, e12, e13, h12, h13, h14,
      a1, a2, a3, hIdx]
  have hV2 : regsF F2 = decodeRead (store.readWord? S2 i) := by
    rw [← hregsF]
    simp [entryReadBlock, straightRegs_cons, straightStepRegs,
      RegFile.write, rP, rA, rB, rT, e21, e22, e23, h23, h24,
      a1, a2, a3, hIdx]
  have hV3 : regsF F3 = decodeRead (store.readWord? S3 i) := by
    rw [← hregsF]
    simp [entryReadBlock, straightRegs_cons, straightStepRegs,
      RegFile.write, rP, rA, rB, rT, e31, e32, e33, h34,
      a1, a2, a3, hIdx]
  have hV4 : regsF F4 = decodeRead (store.readWord? S4 i) := by
    rw [← hregsF]
    simp [entryReadBlock, straightRegs_cons, straightStepRegs,
      RegFile.write, rP, rA, rB, rT, e41, e42, e43,
      a1, a2, a3, hIdx]
  have hVA : regsF rA =
      ((if decodeRead (store.readWord? S1 i) = 0 then 1 else 0) +
        (if decodeRead (store.readWord? S2 i) = 0 then 1 else 0) +
        (if decodeRead (store.readWord? S3 i) = 0 then 1 else 0) +
        (if decodeRead (store.readWord? S4 i) = 0 then 1 else 0)) := by
    rw [← hregsF]
    simp [entryReadBlock, straightRegs_cons, straightStepRegs,
      RegFile.write, rP, rA, rB, rT,
      e13, e22, e23, e31, e32, e33, e41, e42, e43,
      h12, h13, h14, h23, h24, h34, a1, a2, a3, hIdx]
  have hpres : ∀ r, r ≠ F1 → r ≠ F2 → r ≠ F3 → r ≠ F4 → r ≠ 19 →
      r ≠ 22 → r ≠ 23 → regsF r = regsA r := by
    intro r hr1 hr2 hr3 hr4 hr5 hr6 hr7
    rw [← hregsF]
    apply straightRegs_preserves
    intro instr hi
    simp only [entryReadBlock, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl <;> simp [Instr.writesTo, rA, rB, rT] <;> omega
  exact ⟨regsF, hrun, hV1, hV2, hV3, hV4, hVA, hpres⟩

/-- Constructor-exhaustive width certificate for the entry-table 4-read
sub-block (REQ-E1-02 consumption): register numerals `10/19/22/23` fit via
the bank bound, the parametric field segments and destinations fit by
hypothesis, and the only immediate is `0`. -/
theorem entryReadBlock_fits {w S1 S2 S3 S4 F1 F2 F3 F4 : Nat}
    (hreg : 28 ≤ 2 ^ w)
    (hS1 : S1 < 2 ^ w) (hS2 : S2 < 2 ^ w)
    (hS3 : S3 < 2 ^ w) (hS4 : S4 < 2 ^ w)
    (hF1 : F1 < 2 ^ w) (hF2 : F2 < 2 ^ w)
    (hF3 : F3 < 2 ^ w) (hF4 : F4 < 2 ^ w) :
    ∀ instr ∈ entryReadBlock S1 S2 S3 S4 F1 F2 F3 F4,
      instr.FieldsFit w := by
  intro instr hmem
  simp only [entryReadBlock, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl <;>
    simp only [Instr.FieldsFit, rP, rA, rB, rT] <;> omega

/-! ## Relative-offset read machine sub-block -/

/--
The relative-offset read sub-block at block base `A`, relative table at
segment `S`: read at the compact slot in `rSlot` into `rT`, test presence,
and assemble the answer packet `base + offset + 1` from the base position
in `xBPos` (option-shift `decodePacket` convention; a failed read leaves
the `none` packet `0`).
-/
def relativeReadBlock (A S : Nat) : List Instr :=
  [ .readMem rT S rSlot
  , .brNZ rT (A + 3)
  , .brNZ rOne (A + 4)
  , .add rT xBPos rT ]

@[simp] theorem relativeReadBlock_length (A S : Nat) :
    (relativeReadBlock A S).length = 4 := rfl

/-- Frozen category log of the relative-offset read sub-block: one read,
the presence branch, then the packet add (present) or the skip branch
(absent). -/
def relativeReadCats (present : Bool) : List Category :=
  if present then [.memoryRead, .branch, .arithmetic]
  else [.memoryRead, .branch, .branch]

@[simp] theorem relativeReadCats_length (present : Bool) :
    (relativeReadCats present).length = 3 := by
  cases present <;> rfl

/--
Exact-fuel simulation of the relative-offset read sub-block: from block
entry with the compact slot in `rSlot`, the base position in `xBPos`, and
the pinned `1` in `rOne`, the hosted block runs to `A + 4` with

* receipts POSITIONALLY EQUAL to the accepted relative-offset read trace
  (one `readWord` at segment `S`, by `relativeRead_trace_eq`),
* the accepted read's value under `decodePacket` in `rT`
  (`relativeRead_value_eq`),
* the frozen category log `relativeReadCats`, and
* every register other than `rT` preserved.

The presence test is a machine `brNZ` on the shifted read decode (no
meta-level guard).
-/
theorem relativeReadBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A S : Nat}
    (hhost : HostedAt program A (relativeReadBlock A S))
    (regsA : RegFile) (base : Nat)
    (hBase : regsA xBPos = base) (hOne : regsA rOne = 1) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regsA, A, false⟩ ⟨regsF, A + 4, false⟩
        [TraceEvent.readWord S (regsA rSlot)
          (store.readWord? S (regsA rSlot))]
        (relativeReadCats (store.readWord? S (regsA rSlot)).isSome) ∧
      E1Query.decodePacket (regsF rT) =
        ((store.readWord? S (regsA rSlot)).map bitsToNatLE).map
          (fun offset => base + offset) ∧
      (∀ r, r ≠ 19 → regsF r = regsA r) := by
  have h0 : program[A]? = some (.readMem rT S rSlot) := hhost.head
  have h1 : program[A + 1]? = some (.brNZ rT (A + 3)) := hhost.tail.head
  have h2 : program[A + 2]? = some (.brNZ rOne (A + 4)) :=
    hhost.tail.tail.head
  have h3 : program[A + 3]? = some (.add rT xBPos rT) :=
    hhost.tail.tail.tail.head
  have hread := RunsTo.readMem (store := store)
    (s := ⟨regsA, A, false⟩) rfl h0
  cases hw : store.readWord? S (regsA rSlot) with
  | none =>
      rw [hw] at hread
      have hbr1 := RunsTo.brNZ_not_taken (store := store)
        (s := ⟨regsA.write rT (decodeRead none), A + 1, false⟩) rfl h1
        (by simp)
      have hbr2 := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsA.write rT (decodeRead none), A + 2, false⟩) rfl h2
        (by
          show regsA.write rT (decodeRead none) rOne ≠ 0
          rw [RegFile.write_other _ _ (by decide)]
          simp [hOne])
      have hall := hread.trans (hbr1.trans hbr2)
      refine ⟨regsA.write rT (decodeRead none), ?_, ?_, ?_⟩
      · simpa [relativeReadCats] using hall
      · simp [E1Query.decodePacket, decodeRead]
      · intro r hr
        exact RegFile.write_other _ _ (by
          simp only [rT]
          omega)
  | some word =>
      rw [hw] at hread
      have hbr1 := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsA.write rT (decodeRead (some word)), A + 1, false⟩)
        rfl h1
        (by
          show regsA.write rT (decodeRead (some word)) rT ≠ 0
          rw [RegFile.write_same]
          simp [decodeRead])
      have hadd := RunsTo.add (store := store)
        (s := ⟨regsA.write rT (decodeRead (some word)), A + 3, false⟩)
        rfl h3
      have hall := hread.trans (hbr1.trans hadd)
      refine ⟨(regsA.write rT (decodeRead (some word))).write rT
          ((regsA.write rT (decodeRead (some word))) xBPos +
            (regsA.write rT (decodeRead (some word))) rT), ?_, ?_, ?_⟩
      · simpa [relativeReadCats] using hall
      · show E1Query.decodePacket
            ((regsA.write rT (decodeRead (some word))).write rT
              ((regsA.write rT (decodeRead (some word))) xBPos +
                (regsA.write rT (decodeRead (some word))) rT) rT) = _
        rw [RegFile.write_same, RegFile.write_same,
          RegFile.write_other _ _ (by decide), hBase]
        have harith :
            base + decodeRead (some word) =
              (base + bitsToNatLE word) + 1 := by
          simp [decodeRead]
          omega
        rw [harith]
        simp
      · intro r hr
        have hne : r ≠ rT := by
          simp only [rT]
          omega
        rw [RegFile.write_other _ _ hne, RegFile.write_other _ _ hne]

/-- Constructor-exhaustive width certificate for the relative-offset read
sub-block (REQ-E1-02 consumption): register numerals `19/21/24/38` fit via
the extension-bank bound, the segment fits by hypothesis, and the branch
targets are inside the block. -/
theorem relativeReadBlock_fits {w A S : Nat}
    (hreg : 40 ≤ 2 ^ w) (hS : S < 2 ^ w) (hA : A + 4 < 2 ^ w) :
    ∀ instr ∈ relativeReadBlock A S, instr.FieldsFit w := by
  intro instr hmem
  simp only [relativeReadBlock, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;>
    simp only [Instr.FieldsFit, rT, rSlot, rOne, xBPos] <;> omega

end E1SelectBridge
end WordRAM
end RMQ
