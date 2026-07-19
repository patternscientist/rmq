import RMQ.Core.WordRAM.E1InteriorMerge

/-! # E1 amended machine: the interior's TWO-SPAN BLOCKS (#4 and #5)

`canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`
(`InteriorDirectory.lean:2351`) and its global twin
`canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation` (`:2376`)
have ONE shape between them:

    FlatStoreComputation.bind (readNat LEVELTABLE OFFSET n) fun cell =>
      match cell with
      | some value =>
          let level := value / D
          let span  := value % D
          let rightStart := start + n - span
          bind (SPAN start level) fun left =>
            map (fun right => bpCandidateMerge? left right)
              (SPAN rightStart level)
      | none => FlatStoreComputation.pure none

They differ in the level table, its domain `D`, the span table, the slot
map and the block offset.  Both slot maps are `A + level * M + start` for
a caller-supplied `A` and a program constant `M`:

* local  -- `bpLocalSparseCellSlot macroSize levelCount macroIdx localStart
  level = macroIdx * (levelCount * macroSize) + level * macroSize +
  localStart`, so `A = macroIdx * (levelCount * macroSize)`, `M = macroSize`,
  `start = localStart`;
* global -- `bpGlobalSparseCellSlot macroSampleCount macroStart level =
  level * macroSampleCount + macroStart`, so `A = 0`,
  `M = macroSampleCount`, `start = macroStart`.

So ONE parametric block covers both, exactly as `spanBlock` covers `#2`
and `#3`, and the two route computations are its instantiations.

## The level read is the UNCONDITIONAL HEAD

The route binds the level read FIRST and only then dispatches; both span
reads are inside its `some` arm.  The block therefore places the staged
level read at `Q + 1`, before the arm selector, and neither span block
can be reached without it.  Encoding any other order does not produce a
wrong answer that a receipt would catch -- it produces a whnf heartbeat
timeout during elaboration, which is why the order is stated here rather
than discovered.

## The `none` arm skips 456 instructions

`Q + 42`'s target is `Q + 509`, the block's own exit -- past BOTH span
blocks, the shuttle and the merge.  The same defect the span block's own
`none` arm has (DD-20260719-050) recurs here one level up and with a
larger blast radius: an arm that branched past only the first span block
would run the second span read, the shuttle and the merge, returning
`some` where the route returns `none` AND emitting a read the route never
made.  `twoSpanNoneArm_discriminates` below separates them, and records
which checks cannot.

DD-20260719-053.
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace RMQ
namespace WordRAM
namespace E1InteriorTwoSpan

open E1Machine
open RMQ.SuccinctClose
open E1FringeFoldBlock (bestOfRegs)
open E1CandMerge3 (mMV mMP)
open E1InteriorReadBlock (iIdx)
open E1InteriorSummaryGroup (TableGeom SummaryLayout canonicalSummaryLayout
  summaryStage geomEvents geomCats geomCell)
open E1InteriorMinCandidate (cellOpt)
open E1InteriorSpanBlock (pSlot pOff spanBlock spanEvents spanCats spanValue
  SpanUntouched)
open E1InteriorMerge (qLV qLP mergeBlock mergeCats MergeUntouched mergeShuttle
  ShuttleUntouched)

/-! ## Registers

The interior's third new bank.  `75..84` (merge), `89..99` (chunk fold),
`105..117` (summary + min-candidate), `118..122` (span block) and
`123..126` (two-way merge) are taken; this block opens at `127`.

`tA`, `tStart`, `tN` and `tOff` are INPUTS the caller writes; the rest is
scratch.  None of the four inputs is written by the block, which is what
lets `#6`-`#9` re-use them across a chained call. -/

/-- Input: the slot base.  `macroIdx * (levelCount * macroSize)` for the
local twin, `0` for the global one. -/
abbrev tA : Nat := 127

/-- Input: the left span's start.  `localStart` local, `macroStart` global. -/
abbrev tStart : Nat := 128

/-- Input: the level table's slot.  `count` local, `macroSpanCount` global. -/
abbrev tN : Nat := 129

/-- Input: the span block's additive block offset, forwarded to `pOff`. -/
abbrev tOff : Nat := 130

/-- The decoded level cell, option-shifted (`0` = `none`, `v + 1` = `some v`). -/
abbrev tCell : Nat := 131

/-- Scratch: the decoded level. -/
abbrev tLvl : Nat := 132

/-- Scratch: the span, then the RIGHT span's start. -/
abbrev tRS : Nat := 133

/-- Scratch: the unshifted cell, then `A + level * M`, which must survive
BOTH span blocks -- it is the shared prefix of the two slots. -/
abbrev tT : Nat := 134

/-- Constant `1`: the unshift operand, and the condition register making
the `none` arm's jump unconditional. -/
abbrev tOne : Nat := 135

/-! ## The route's own derived quantities

Spelled as the ROUTE spells them -- `v % D`, not the machine's
`v - v / D * D` -- so that the value and receipt clauses below are
statements about the route's arithmetic and the bridge is discharged once,
inside the proof, rather than at every call site. -/

/-- `rightLocalStart` / `rightMacroStart`: `start + n - span`. -/
def twoSpanRight (D start n v : Nat) : Nat := start + n - v % D

/-- The LEFT span's slot: `A + level * M + start`. -/
def twoSpanLeftSlot (A M D start v : Nat) : Nat := A + v / D * M + start

/-- The RIGHT span's slot: the same, at the right start. -/
def twoSpanRightSlot (A M D start n v : Nat) : Nat :=
  A + v / D * M + twoSpanRight D start n v

/-- The one arithmetic bridge between the route's `%` and the machine's
`divConst`/`mulConst`/`sub`.  There is no modulus instruction, so the span
is computed as `v - v / D * D`; this is the only place the two spellings
meet. -/
theorem mod_eq_sub_div_mul (v D : Nat) : v % D = v - v / D * D := by
  have h : v % D + D * (v / D) = v := Nat.mod_add_div v D
  have h2 : D * (v / D) = v / D * D := Nat.mul_comm _ _
  omega

/-! ## The block -/

/-- The arm selector and the decode, at `Q + 40 .. Q + 52`.

`Q + 42`'s target is `Q + 509`, the block's own exit -- past both span
blocks, the shuttle and the merge.  That numeral is the whole content of
the `none` arm's correctness, and `twoSpanNoneArm_discriminates` is its
fixture. -/
def twoSpanArms (M D Q : Nat) : List Instr :=
  [ Instr.brNZ tCell (Q + 43)     -- Q+40  level cell present? -> decode
  , Instr.const mMV 0             -- Q+41  none arm: the result IS none
  , Instr.brNZ tOne (Q + 509)     -- Q+42  none arm: past ALL of it
  , Instr.sub tT tCell tOne       -- Q+43  value := cell - 1
  , Instr.divConst tLvl tT D      -- Q+44  level := value / D
  , Instr.mulConst tRS tLvl D     -- Q+45  level * D
  , Instr.sub tRS tT tRS          -- Q+46  span := value - level * D
  , Instr.add tT tStart tN        -- Q+47  start + n
  , Instr.sub tRS tT tRS          -- Q+48  rightStart := start + n - span
  , Instr.mulConst tT tLvl M      -- Q+49  level * M
  , Instr.add tT tA tT            -- Q+50  A + level * M   (kept across both)
  , Instr.add pSlot tT tStart     -- Q+51  LEFT slot
  , Instr.move pOff tOff ]        -- Q+52  the span blocks' block offset

@[simp] theorem twoSpanArms_length (M D Q : Nat) :
    (twoSpanArms M D Q).length = 13 := rfl

/-- THE TWO-SPAN BLOCK, parametric in the level geometry `GL`, the span
geometry `GS`, the level stride `M` and the domain `D` (509 instructions,
exit `Q + 509` on BOTH arms).

One staged level read, the arm selector and decode, the span block, the
shuttle, the right slot, the span block again, and the two-way merge.
`#4` and `#5` are this block at two geometry pairs.

`pOff` is written ONCE, at `Q + 52`: the span block preserves it
(`SpanUntouched 119`), so the second run inherits it rather than being
handed it again. -/
def twoSpanBlock (L : SummaryLayout) (GL GS : TableGeom)
    (M D blockSize blocksPerSuper Q : Nat) : List Instr :=
  (Instr.const tOne 1 ::
      summaryStage (Instr.move iIdx tN) L.segment GL.base L.deadAddress
        GL.entriesLen GL.chunkCount L.wordScale tCell (Q + 1)) ++
    (twoSpanArms M D Q ++
      (spanBlock L GS blockSize blocksPerSuper (Q + 53) ++
        (mergeShuttle ++
          (Instr.add pSlot tT tRS ::
            (spanBlock L GS blockSize blocksPerSuper (Q + 278) ++
              mergeBlock (Q + 500))))))

@[simp] theorem twoSpanBlock_length (L : SummaryLayout) (GL GS : TableGeom)
    (M D blockSize blocksPerSuper Q : Nat) :
    (twoSpanBlock L GL GS M D blockSize blocksPerSuper Q).length = 509 := by
  simp [twoSpanBlock]

/-! ## Receipt, charge log and value, as functions of the decoded level cell -/

/-- The level cell this block decodes at slot `n`, option-shifted. -/
def levelCell (shape : Cartesian.CartesianShape) (GL : TableGeom)
    (n : Nat) : Nat :=
  geomCell (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    (canonicalSummaryLayout shape) GL n

/-- The block's receipt: the level read, then -- ON THE `some` ARM ONLY --
the two span blocks' receipts, in the route's bind order. -/
def twoSpanEvents (shape : Cartesian.CartesianShape) (GL GS : TableGeom)
    (A M D start n off : Nat) : List TraceEvent :=
  geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) GL n ++
    (match cellOpt (levelCell shape GL n) with
      | none => []
      | some v =>
          spanEvents shape GS (twoSpanLeftSlot A M D start v) off ++
            spanEvents shape GS (twoSpanRightSlot A M D start n v) off)

/-- The block's charge log.  The two arms differ in LENGTH as well as in
content, so this is not a numeral. -/
def twoSpanCats (shape : Cartesian.CartesianShape) (GL GS : TableGeom)
    (A M D start n off : Nat) : List Category :=
  Category.registerWrite ::
    (geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) GL Category.registerWrite n ++
      (match cellOpt (levelCell shape GL n) with
        | none => [Category.branch, Category.registerWrite, Category.branch]
        | some v =>
            [Category.branch, Category.arithmetic, Category.arithmetic,
              Category.arithmetic, Category.arithmetic, Category.arithmetic,
              Category.arithmetic, Category.arithmetic, Category.arithmetic,
              Category.arithmetic, Category.registerWrite] ++
              (spanCats shape GS (twoSpanLeftSlot A M D start v) off ++
                ([Category.registerWrite, Category.registerWrite,
                    Category.arithmetic] ++
                  (spanCats shape GS (twoSpanRightSlot A M D start n v) off ++
                    mergeCats
                      (spanValue shape GS (twoSpanLeftSlot A M D start v) off)
                      (spanValue shape GS
                        (twoSpanRightSlot A M D start n v) off))))))

/-- The block's value: the two spans merged on the `some` arm, `none` on
the `none` arm. -/
def twoSpanValue (shape : Cartesian.CartesianShape) (GL GS : TableGeom)
    (A M D start n off : Nat) : Option (Nat × Nat) :=
  match cellOpt (levelCell shape GL n) with
  | none => none
  | some v =>
      bpCandidateMerge? (spanValue shape GS (twoSpanLeftSlot A M D start v) off)
        (spanValue shape GS (twoSpanRightSlot A M D start n v) off)

/-- What the two-span block LEAVES ALONE: what its four components leave
alone, minus the two span-block inputs it writes and its own five scratch
slots.

The four INPUTS `tA`, `tStart`, `tN`, `tOff` are deliberately absent: the
block never writes them, and `#6`-`#9` chain two of these blocks with only
some inputs rewritten between, so claiming them here is what makes that
chaining provable rather than re-established each time. -/
abbrev TwoSpanUntouched (r : Nat) : Prop :=
  SpanUntouched r ∧ MergeUntouched r ∧ ShuttleUntouched r ∧
    r ≠ pSlot ∧ r ≠ pOff ∧ r ≠ tCell ∧ r ≠ tLvl ∧ r ≠ tRS ∧ r ≠ tT ∧
    r ≠ tOne

/-- THE FOUR CROSS-BLOCK-ARM OPERANDS SURVIVE THE WHOLE TWO-SPAN BLOCK. -/
theorem twoSpanUntouched_at_crossBlockArm_operands :
    TwoSpanUntouched 70 ∧ TwoSpanUntouched 71 ∧ TwoSpanUntouched 75 ∧
      TwoSpanUntouched 76 :=
  ⟨⟨E1InteriorSpanBlock.spanUntouched_at_crossBlockArm_operands.1,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩,
    ⟨E1InteriorSpanBlock.spanUntouched_at_crossBlockArm_operands.2.1,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩,
    ⟨E1InteriorSpanBlock.spanUntouched_at_crossBlockArm_operands.2.2.1,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩,
    ⟨E1InteriorSpanBlock.spanUntouched_at_crossBlockArm_operands.2.2.2,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide⟩⟩

/-- A two-span-preserved register is preserved by the span block, so a
chained caller can compose the two certificates without re-deciding. -/
theorem twoSpanUntouched_span {r : Nat} (h : TwoSpanUntouched r) :
    SpanUntouched r := h.1

/-- **THE WHOLE WRITE SET LIES BELOW `136`.**

Stated once so a combiner built on top of this block can carry its own
register bank across a sub-leg without re-deciding ten conjuncts at every
use.  `136` is not arbitrary: it is one past `tOne`, the highest register
this block writes.

THE NUMERALS ARE SPELLED OUT rather than left as the register abbrevs
because `omega` collects an `abbrev` as an OPAQUE ATOM -- it reports "a
possible counterexample may satisfy `a >= 136` where `a := iIdx`" -- so a
proof written against the names fails while the identical proof against
the numerals succeeds by defeq.  Each `show` below is the same
proposition as the conjunct it discharges. -/
theorem twoSpanUntouched_of_ge {r : Nat} (h : 136 ≤ r) :
    TwoSpanUntouched r :=
  ⟨⟨⟨⟨Or.inr (show 99 < r by omega), show r ≠ 85 by omega,
        show r ≠ 101 by omega, show r ≠ 102 by omega,
        show r ≠ 103 by omega, show r ≠ 104 by omega⟩,
      show r ≠ 77 by omega, show r ≠ 78 by omega,
      Or.inr (show 117 < r by omega)⟩,
    show r ≠ 120 by omega, show r ≠ 121 by omega, show r ≠ 122 by omega,
    show r ≠ 100 by omega⟩,
  ⟨show r ≠ 77 by omega, show r ≠ 78 by omega, show r ≠ 125 by omega,
    show r ≠ 126 by omega⟩,
  ⟨show r ≠ 123 by omega, show r ≠ 124 by omega⟩,
  show r ≠ 118 by omega, show r ≠ 119 by omega, show r ≠ 131 by omega,
  show r ≠ 132 by omega, show r ≠ 133 by omega, show r ≠ 134 by omega,
  show r ≠ 135 by omega⟩

/-- **AND `qLV`/`qLP` ARE INSIDE IT.**

`twoSpanBlock` contains a `mergeShuttle` and a `mergeBlock`, so it WRITES
the two-way merge's left-stash pair.  A caller that stashes a candidate
there and then runs a two-span sub-leg loses it.

This is recorded as a theorem rather than a comment because the natural
combiner design -- stash into `qLV`/`qLP`, run the next sub-leg, merge --
is WRONG for exactly this reason, and nothing about the block's type says
so.  `E1_LIVE_STATE.md` §2's "chaining does need a two-instruction
shuttle, which exists" is true one level down and NOT sufficient one level
up: each nesting level needs its own stash pair. -/
theorem twoSpanUntouched_excludes_mergeStash :
    ¬ TwoSpanUntouched E1InteriorMerge.qLV ∧
      ¬ TwoSpanUntouched E1InteriorMerge.qLP :=
  ⟨fun h => absurd h.2.2.1.1 (by decide),
    fun h => absurd h.2.2.1.2 (by decide)⟩

/-! ## Exact simulation -/

/--
EXACT SIMULATION OF THE TWO-SPAN BLOCK, PARAMETRIC IN BOTH GEOMETRIES.

Both arms exit at `Q + 509`.  The receipt is the level read's route
events followed, ON THE `some` ARM ONLY, by the two span blocks' receipts
in the route's bind order -- left then right, which is the order
`FlatStoreComputation.bind` fixes at `InteriorDirectory.lean:2367`.

The value is the route's own `bpCandidateMerge?` of the two span values,
NOT the block's arithmetic, for the reason DD-20260719-050 and
DD-20260719-052 record.

NO STORE HYPOTHESIS AND NO VALIDITY HYPOTHESIS.  The premises are the
hosting, the four caller inputs, and the two geometries' chunk-count
bounds -- the same facts the level stage and the span blocks each need.
-/
theorem twoSpanBlock_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {GL GS : TableGeom} {M D Q A start n off : Nat} {regs : RegFile}
    (hHost : HostedAt program Q
      (twoSpanBlock (canonicalSummaryLayout shape) GL GS M D
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper Q))
    (hA : regs tA = A) (hStart : regs tStart = start) (hN : regs tN = n)
    (hOff : regs tOff = off)
    (hLPos : 0 < GL.chunkCount) (hLCap : GL.chunkCount ≤ 8)
    (hSPos : 0 < GS.chunkCount) (hSCap : GS.chunkCount ≤ 8) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 509, false⟩
          (twoSpanEvents shape GL GS A M D start n off)
          (twoSpanCats shape GL GS A M D start n off) ∧
        bestOfRegs (regs' mMV) (regs' mMP) =
          twoSpanValue shape GL GS A M D start n off ∧
        (∀ r, TwoSpanUntouched r → regs' r = regs r) := by
  -- hosting, peeled in the block's own append order
  have hPre : HostedAt program Q
      (Instr.const tOne 1 ::
        summaryStage (Instr.move iIdx tN)
          (canonicalSummaryLayout shape).segment GL.base
          (canonicalSummaryLayout shape).deadAddress GL.entriesLen
          GL.chunkCount (canonicalSummaryLayout shape).wordScale tCell
          (Q + 1)) := hHost.append_left
  have hR1 : HostedAt program (Q + 40)
      (twoSpanArms M D Q ++
        (spanBlock (canonicalSummaryLayout shape) GS
            (RelativeRmm.canonicalLayout shape).blockSize
            (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 53) ++
          (mergeShuttle ++
            (Instr.add pSlot tT tRS ::
              (spanBlock (canonicalSummaryLayout shape) GS
                  (RelativeRmm.canonicalLayout shape).blockSize
                  (RelativeRmm.canonicalLayout shape).blocksPerSuper
                  (Q + 278) ++
                mergeBlock (Q + 500)))))) := by
    have h := hHost.append_right (code₁ := Instr.const tOne 1 ::
      summaryStage (Instr.move iIdx tN)
        (canonicalSummaryLayout shape).segment GL.base
        (canonicalSummaryLayout shape).deadAddress GL.entriesLen
        GL.chunkCount (canonicalSummaryLayout shape).wordScale tCell (Q + 1))
    simpa using h
  have hArms : HostedAt program (Q + 40) (twoSpanArms M D Q) := hR1.append_left
  have hR2 : HostedAt program (Q + 53)
      (spanBlock (canonicalSummaryLayout shape) GS
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 53) ++
        (mergeShuttle ++
          (Instr.add pSlot tT tRS ::
            (spanBlock (canonicalSummaryLayout shape) GS
                (RelativeRmm.canonicalLayout shape).blockSize
                (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 278) ++
              mergeBlock (Q + 500))))) := by
    have h := hR1.append_right (code₁ := twoSpanArms M D Q)
    have harith : Q + 40 + (twoSpanArms M D Q).length = Q + 53 := by simp
    rwa [harith] at h
  have hSpanL : HostedAt program (Q + 53)
      (spanBlock (canonicalSummaryLayout shape) GS
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 53)) :=
    hR2.append_left
  have hR3 : HostedAt program (Q + 275)
      (mergeShuttle ++
        (Instr.add pSlot tT tRS ::
          (spanBlock (canonicalSummaryLayout shape) GS
              (RelativeRmm.canonicalLayout shape).blockSize
              (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 278) ++
            mergeBlock (Q + 500)))) := by
    have h := hR2.append_right
      (code₁ := spanBlock (canonicalSummaryLayout shape) GS
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 53))
    have harith : Q + 53 +
        (spanBlock (canonicalSummaryLayout shape) GS
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper
          (Q + 53)).length = Q + 275 := by simp
    rwa [harith] at h
  have hShuttle : HostedAt program (Q + 275) mergeShuttle := hR3.append_left
  have hR4 : HostedAt program (Q + 277)
      (Instr.add pSlot tT tRS ::
        (spanBlock (canonicalSummaryLayout shape) GS
            (RelativeRmm.canonicalLayout shape).blockSize
            (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 278) ++
          mergeBlock (Q + 500))) := by
    have h := hR3.append_right (code₁ := mergeShuttle)
    have harith : Q + 275 + mergeShuttle.length = Q + 277 := by simp
    rwa [harith] at h
  have hAddR : program[Q + 277]? = some (Instr.add pSlot tT tRS) := hR4.head
  have hR5 : HostedAt program (Q + 278)
      (spanBlock (canonicalSummaryLayout shape) GS
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 278) ++
        mergeBlock (Q + 500)) := by
    have h := hR4.tail
    have harith : Q + 277 + 1 = Q + 278 := by omega
    rwa [harith] at h
  have hSpanR : HostedAt program (Q + 278)
      (spanBlock (canonicalSummaryLayout shape) GS
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 278)) :=
    hR5.append_left
  have hMerge : HostedAt program (Q + 500) (mergeBlock (Q + 500)) := by
    have h := hR5.append_right
      (code₁ := spanBlock (canonicalSummaryLayout shape) GS
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 278))
    have harith : Q + 278 +
        (spanBlock (canonicalSummaryLayout shape) GS
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper
          (Q + 278)).length = Q + 500 := by simp
    rwa [harith] at h
  -- the thirteen arm fetches
  have hf : ∀ (k m : Nat) (instr : Instr), k < 13 →
      (twoSpanArms M D Q)[k]? = some instr → Q + 40 + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hArms k hk, hget]
  have f40 : program[Q + 40]? = some (Instr.brNZ tCell (Q + 43)) :=
    hf 0 _ _ (by omega) rfl (by omega)
  have f41 : program[Q + 41]? = some (Instr.const mMV 0) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have f42 : program[Q + 42]? = some (Instr.brNZ tOne (Q + 509)) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have f43 : program[Q + 43]? = some (Instr.sub tT tCell tOne) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have f44 : program[Q + 44]? = some (Instr.divConst tLvl tT D) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have f45 : program[Q + 45]? = some (Instr.mulConst tRS tLvl D) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have f46 : program[Q + 46]? = some (Instr.sub tRS tT tRS) :=
    hf 6 _ _ (by omega) rfl (by omega)
  have f47 : program[Q + 47]? = some (Instr.add tT tStart tN) :=
    hf 7 _ _ (by omega) rfl (by omega)
  have f48 : program[Q + 48]? = some (Instr.sub tRS tT tRS) :=
    hf 8 _ _ (by omega) rfl (by omega)
  have f49 : program[Q + 49]? = some (Instr.mulConst tT tLvl M) :=
    hf 9 _ _ (by omega) rfl (by omega)
  have f50 : program[Q + 50]? = some (Instr.add tT tA tT) :=
    hf 10 _ _ (by omega) rfl (by omega)
  have f51 : program[Q + 51]? = some (Instr.add pSlot tT tStart) :=
    hf 11 _ _ (by omega) rfl (by omega)
  have f52 : program[Q + 52]? = some (Instr.move pOff tOff) :=
    hf 12 _ _ (by omega) rfl (by omega)
  -- the unit seed and the level stage
  have hStep0 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨regs, Q, false⟩ ⟨regs.write tOne 1, Q + 1, false⟩ []
      [Category.registerWrite] :=
    RunsTo.const (by simp) (by simpa using hPre.head)
  have hStage : HostedAt program (Q + 1)
      (summaryStage (Instr.move iIdx tN)
        (canonicalSummaryLayout shape).segment GL.base
        (canonicalSummaryLayout shape).deadAddress GL.entriesLen
        GL.chunkCount (canonicalSummaryLayout shape).wordScale tCell
        (Q + 1)) := hPre.tail
  have hF1 : program[Q + 1]? = some (Instr.move iIdx tN) := hStage.head
  have hHead : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨regs.write tOne 1, Q + 1, false⟩
      ⟨(regs.write tOne 1).write iIdx ((regs.write tOne 1) tN),
        Q + 1 + 1, false⟩ [] [Category.registerWrite] :=
    RunsTo.move (s := ⟨regs.write tOne 1, Q + 1, false⟩) rfl hF1
  have hIdx : ((regs.write tOne 1).write iIdx ((regs.write tOne 1) tN))
      iIdx = n := by
    rw [RegFile.write_same, RegFile.write_other _ _ (by decide)]
    exact hN
  obtain ⟨regs2, hStageRun, hCell, hStagePres⟩ :=
    E1InteriorSummaryGroup.summaryStage_runsTo
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hStage hHead hIdx
      hLPos hLCap
  have hCell' : regs2 tCell = levelCell shape GL n := hCell
  -- INTO GEOM VOCABULARY, BY DEFEQ, ONCE (see `E1InteriorSpanBlock.lean:335`)
  have hStageRun' : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨regs.write tOne 1, Q + 1, false⟩ ⟨regs2, Q + 40, false⟩
      (geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) GL n)
      (geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) GL Category.registerWrite n) :=
    hStageRun
  -- the caller's four inputs and the unit survive the stage
  have hOne2 : regs2 tOne = 1 := by
    rw [hStagePres tOne (by decide)]
    rw [RegFile.write_other _ _ (by decide), RegFile.write_same]
  have hA2 : regs2 tA = A := by
    rw [hStagePres tA (by decide)]
    rw [RegFile.write_other _ _ (by decide),
      RegFile.write_other _ _ (by decide)]
    exact hA
  have hStart2 : regs2 tStart = start := by
    rw [hStagePres tStart (by decide)]
    rw [RegFile.write_other _ _ (by decide),
      RegFile.write_other _ _ (by decide)]
    exact hStart
  have hN2 : regs2 tN = n := by
    rw [hStagePres tN (by decide)]
    rw [RegFile.write_other _ _ (by decide),
      RegFile.write_other _ _ (by decide)]
    exact hN
  have hOff2 : regs2 tOff = off := by
    rw [hStagePres tOff (by decide)]
    rw [RegFile.write_other _ _ (by decide),
      RegFile.write_other _ _ (by decide)]
    exact hOff
  -- what survives as far as the arm selector; both arms extend it
  have hBase : ∀ r, TwoSpanUntouched r → regs2 r = regs r := by
    intro r hr
    rw [hStagePres r ⟨hr.1.1.1.1, hr.2.2.2.2.2.1⟩,
      RegFile.write_other _ _ hr.1.1.1.2.1,
      RegFile.write_other _ _ hr.2.2.2.2.2.2.2.2.2]
  cases hc : levelCell shape GL n with
  | zero =>
      -- THE `none` ARM: result `none`, past ALL 456 remaining instructions
      have hCell0 : regs2 tCell = 0 := by rw [hCell']; exact hc
      have hb40 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 40, false⟩ ⟨regs2, Q + 41, false⟩ []
          [Category.branch] := by
        have h := RunsTo.brNZ_not_taken
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨regs2, Q + 40, false⟩ : State)) rfl f40 (by simpa using hCell0)
        simpa using h
      have hc41 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 41, false⟩ ⟨regs2.write mMV 0, Q + 42, false⟩ []
          [Category.registerWrite] := by
        have h := RunsTo.const
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨regs2, Q + 41, false⟩ : State)) rfl f41
        simpa using h
      have hOne3 : (regs2.write mMV 0) tOne = 1 := by
        rw [RegFile.write_other _ _ (by decide)]; exact hOne2
      have hb42 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2.write mMV 0, Q + 42, false⟩
          ⟨regs2.write mMV 0, Q + 509, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ_taken
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨regs2.write mMV 0, Q + 42, false⟩ : State)) rfl f42
          (by simp [hOne3])
        simpa using h
      refine ⟨regs2.write mMV 0, ?_, ?_, ?_⟩
      · have h := ((hStep0.trans hStageRun').trans hb40).trans
          (hc41.trans hb42)
        simpa [twoSpanEvents, twoSpanCats, hc, List.append_assoc] using h
      · rw [RegFile.write_same]
        simp [twoSpanValue, hc]
      · intro r hr
        rw [RegFile.write_other _ _ hr.2.1.1]
        exact hBase r hr
  | succ v =>
      -- THE `some` ARM
      have hCellS : regs2 tCell = v + 1 := by rw [hCell']; exact hc
      have hb40 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 40, false⟩ ⟨regs2, Q + 43, false⟩ []
          [Category.branch] := by
        have h := RunsTo.brNZ_taken
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨regs2, Q + 40, false⟩ : State)) rfl f40 (by simp [hCellS])
        simpa using h
      -- Q+43 .. Q+52, ten steps
      obtain ⟨a3, ha3⟩ : ∃ z : RegFile, z = regs2.write tT v := ⟨_, rfl⟩
      have s43 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs2, Q + 43, false⟩ ⟨a3, Q + 44, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.sub
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨regs2, Q + 43, false⟩ : State)) rfl f43
        simpa [ha3, hCellS, hOne2] using h
      have ha3T : a3 tT = v := by simp [ha3]
      obtain ⟨a4, ha4⟩ : ∃ z : RegFile, z = a3.write tLvl (v / D) := ⟨_, rfl⟩
      have s44 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a3, Q + 44, false⟩ ⟨a4, Q + 45, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.divConst
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a3, Q + 44, false⟩ : State)) rfl f44
        simpa [ha4, ha3T] using h
      have ha4L : a4 tLvl = v / D := by simp [ha4]
      have ha4T : a4 tT = v := by
        rw [ha4, RegFile.write_other _ _ (by decide)]; exact ha3T
      obtain ⟨a5, ha5⟩ : ∃ z : RegFile, z = a4.write tRS (v / D * D) := ⟨_, rfl⟩
      have s45 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a4, Q + 45, false⟩ ⟨a5, Q + 46, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.mulConst
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a4, Q + 45, false⟩ : State)) rfl f45
        simpa [ha5, ha4L] using h
      have ha5T : a5 tT = v := by
        rw [ha5, RegFile.write_other _ _ (by decide)]; exact ha4T
      have ha5R : a5 tRS = v / D * D := by simp [ha5]
      obtain ⟨a6, ha6⟩ : ∃ z : RegFile, z = a5.write tRS (v - v / D * D) :=
        ⟨_, rfl⟩
      have s46 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a5, Q + 46, false⟩ ⟨a6, Q + 47, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.sub
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a5, Q + 46, false⟩ : State)) rfl f46
        simpa [ha6, ha5T, ha5R] using h
      have ha6L : a6 tLvl = v / D := by
        rw [ha6, RegFile.write_other _ _ (by decide), ha5,
          RegFile.write_other _ _ (by decide)]; exact ha4L
      have ha6R : a6 tRS = v % D := by
        rw [mod_eq_sub_div_mul]; simp [ha6]
      have ha6S : a6 tStart = start := by
        rw [ha6, RegFile.write_other _ _ (by decide), ha5,
          RegFile.write_other _ _ (by decide), ha4,
          RegFile.write_other _ _ (by decide), ha3,
          RegFile.write_other _ _ (by decide)]
        exact hStart2
      have ha6N : a6 tN = n := by
        rw [ha6, RegFile.write_other _ _ (by decide), ha5,
          RegFile.write_other _ _ (by decide), ha4,
          RegFile.write_other _ _ (by decide), ha3,
          RegFile.write_other _ _ (by decide)]
        exact hN2
      have ha6A : a6 tA = A := by
        rw [ha6, RegFile.write_other _ _ (by decide), ha5,
          RegFile.write_other _ _ (by decide), ha4,
          RegFile.write_other _ _ (by decide), ha3,
          RegFile.write_other _ _ (by decide)]
        exact hA2
      have ha6O : a6 tOff = off := by
        rw [ha6, RegFile.write_other _ _ (by decide), ha5,
          RegFile.write_other _ _ (by decide), ha4,
          RegFile.write_other _ _ (by decide), ha3,
          RegFile.write_other _ _ (by decide)]
        exact hOff2
      obtain ⟨a7, ha7⟩ : ∃ z : RegFile, z = a6.write tT (start + n) := ⟨_, rfl⟩
      have s47 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a6, Q + 47, false⟩ ⟨a7, Q + 48, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.add
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a6, Q + 47, false⟩ : State)) rfl f47
        simpa [ha7, ha6S, ha6N] using h
      have ha7T : a7 tT = start + n := by simp [ha7]
      have ha7R : a7 tRS = v % D := by
        rw [ha7, RegFile.write_other _ _ (by decide)]; exact ha6R
      obtain ⟨a8, ha8⟩ : ∃ z : RegFile,
          z = a7.write tRS (start + n - v % D) := ⟨_, rfl⟩
      have s48 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a7, Q + 48, false⟩ ⟨a8, Q + 49, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.sub
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a7, Q + 48, false⟩ : State)) rfl f48
        simpa [ha8, ha7T, ha7R] using h
      have ha8L : a8 tLvl = v / D := by
        rw [ha8, RegFile.write_other _ _ (by decide), ha7,
          RegFile.write_other _ _ (by decide)]; exact ha6L
      have ha8R : a8 tRS = twoSpanRight D start n v := by simp [ha8, twoSpanRight]
      obtain ⟨a9, ha9⟩ : ∃ z : RegFile, z = a8.write tT (v / D * M) := ⟨_, rfl⟩
      have s49 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a8, Q + 49, false⟩ ⟨a9, Q + 50, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.mulConst
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a8, Q + 49, false⟩ : State)) rfl f49
        simpa [ha9, ha8L] using h
      have ha9T : a9 tT = v / D * M := by simp [ha9]
      have ha9A : a9 tA = A := by
        rw [ha9, RegFile.write_other _ _ (by decide), ha8,
          RegFile.write_other _ _ (by decide), ha7,
          RegFile.write_other _ _ (by decide)]
        exact ha6A
      obtain ⟨a10, ha10⟩ : ∃ z : RegFile,
          z = a9.write tT (A + v / D * M) := ⟨_, rfl⟩
      have s50 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a9, Q + 50, false⟩ ⟨a10, Q + 51, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.add
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a9, Q + 50, false⟩ : State)) rfl f50
        simpa [ha10, ha9A, ha9T] using h
      have ha10T : a10 tT = A + v / D * M := by simp [ha10]
      have ha10S : a10 tStart = start := by
        rw [ha10, RegFile.write_other _ _ (by decide), ha9,
          RegFile.write_other _ _ (by decide), ha8,
          RegFile.write_other _ _ (by decide), ha7,
          RegFile.write_other _ _ (by decide)]
        exact ha6S
      obtain ⟨a11, ha11⟩ : ∃ z : RegFile,
          z = a10.write pSlot (A + v / D * M + start) := ⟨_, rfl⟩
      have s51 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a10, Q + 51, false⟩ ⟨a11, Q + 52, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.add
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a10, Q + 51, false⟩ : State)) rfl f51
        simpa [ha11, ha10T, ha10S] using h
      have ha11O : a11 tOff = off := by
        rw [ha11, RegFile.write_other _ _ (by decide), ha10,
          RegFile.write_other _ _ (by decide), ha9,
          RegFile.write_other _ _ (by decide), ha8,
          RegFile.write_other _ _ (by decide), ha7,
          RegFile.write_other _ _ (by decide)]
        exact ha6O
      obtain ⟨a12, ha12⟩ : ∃ z : RegFile, z = a11.write pOff off := ⟨_, rfl⟩
      have s52 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a11, Q + 52, false⟩ ⟨a12, Q + 53, false⟩ []
          [Category.registerWrite] := by
        have h := RunsTo.move
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨a11, Q + 52, false⟩ : State)) rfl f52
        simpa [ha12, ha11O] using h
      -- the LEFT span block
      have ha12Slot : a12 pSlot = twoSpanLeftSlot A M D start v := by
        rw [ha12, RegFile.write_other _ _ (by decide), ha11,
          RegFile.write_same, twoSpanLeftSlot]
      have ha12Off : a12 pOff = off := by simp [ha12]
      obtain ⟨bL, hbLrun, hbLval, hbLpres⟩ :=
        E1InteriorSpanBlock.spanBlock_runsTo shape (G := GS) hSpanL
          ha12Slot ha12Off hSPos hSCap
      have hbLrun' : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨a12, Q + 53, false⟩ ⟨bL, Q + 275, false⟩
          (spanEvents shape GS (twoSpanLeftSlot A M D start v) off)
          (spanCats shape GS (twoSpanLeftSlot A M D start v) off) := by
        have harith : Q + 53 + 222 = Q + 275 := by omega
        rwa [harith] at hbLrun
      -- the shuttle
      obtain ⟨bS, hbSrun, hbSLV, hbSLP, _, _, hbSpres⟩ :=
        E1InteriorMerge.mergeShuttle_runsTo
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) hShuttle bL
          (bL mMV) (bL mMP) rfl rfl
      have hbSrun' : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨bL, Q + 275, false⟩ ⟨bS, Q + 277, false⟩ []
          [Category.registerWrite, Category.registerWrite] := by
        have harith : Q + 275 + 2 = Q + 277 := by omega
        rwa [harith] at hbSrun
      -- the RIGHT slot, then the RIGHT span block
      have hbST : bS tT = A + v / D * M := by
        rw [hbSpres tT (by decide), hbLpres tT (by decide), ha12,
          RegFile.write_other _ _ (by decide), ha11,
          RegFile.write_other _ _ (by decide)]
        exact ha10T
      have hbSR : bS tRS = twoSpanRight D start n v := by
        rw [hbSpres tRS (by decide), hbLpres tRS (by decide)]
        rw [ha12, RegFile.write_other _ _ (by decide), ha11,
          RegFile.write_other _ _ (by decide), ha10,
          RegFile.write_other _ _ (by decide), ha9,
          RegFile.write_other _ _ (by decide)]
        exact ha8R
      have hbSOff : bS pOff = off := by
        rw [hbSpres pOff (by decide), hbLpres pOff (by decide)]
        exact ha12Off
      obtain ⟨cR, hcR⟩ : ∃ z : RegFile,
          z = bS.write pSlot (twoSpanRightSlot A M D start n v) := ⟨_, rfl⟩
      have s277 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨bS, Q + 277, false⟩ ⟨cR, Q + 278, false⟩ []
          [Category.arithmetic] := by
        have h := RunsTo.add
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨bS, Q + 277, false⟩ : State)) rfl hAddR
        simpa [hcR, hbST, hbSR, twoSpanRightSlot] using h
      have hcRSlot : cR pSlot = twoSpanRightSlot A M D start n v := by
        simp [hcR]
      have hcROff : cR pOff = off := by
        rw [hcR, RegFile.write_other _ _ (by decide)]; exact hbSOff
      obtain ⟨bR, hbRrun, hbRval, hbRpres⟩ :=
        E1InteriorSpanBlock.spanBlock_runsTo shape (G := GS) hSpanR
          hcRSlot hcROff hSPos hSCap
      have hbRrun' : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨cR, Q + 278, false⟩ ⟨bR, Q + 500, false⟩
          (spanEvents shape GS (twoSpanRightSlot A M D start n v) off)
          (spanCats shape GS (twoSpanRightSlot A M D start n v) off) := by
        have harith : Q + 278 + 222 = Q + 500 := by omega
        rwa [harith] at hbRrun
      -- the stashed left candidate survives the right span block
      have hbRLV : bR qLV = bL mMV := by
        rw [hbRpres qLV (by decide)]
        rw [hcR, RegFile.write_other _ _ (by decide)]
        exact hbSLV
      have hbRLP : bR qLP = bL mMP := by
        rw [hbRpres qLP (by decide)]
        rw [hcR, RegFile.write_other _ _ (by decide)]
        exact hbSLP
      -- the merge
      obtain ⟨bM, hbMrun, hbMval, hbMpres⟩ :=
        E1InteriorMerge.mergeBlock_runsTo
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) hMerge bR
          (bL mMV) (bL mMP) (bR mMV) (bR mMP) hbRLV hbRLP rfl rfl
      have hbMrun' : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨bR, Q + 500, false⟩ ⟨bM, Q + 509, false⟩ []
          (mergeCats (spanValue shape GS (twoSpanLeftSlot A M D start v) off)
            (spanValue shape GS (twoSpanRightSlot A M D start n v) off)) := by
        have harith : Q + 500 + 9 = Q + 509 := by omega
        rw [harith, hbLval, hbRval] at hbMrun
        exact hbMrun
      refine ⟨bM, ?_, ?_, ?_⟩
      · have h := ((((((((((((((hStep0.trans hStageRun').trans hb40).trans
          s43).trans s44).trans s45).trans s46).trans s47).trans s48).trans
          s49).trans s50).trans s51).trans s52).trans hbLrun').trans
          (((hbSrun'.trans s277).trans hbRrun').trans hbMrun'))
        simpa [twoSpanEvents, twoSpanCats, hc, List.append_assoc] using h
      · rw [hbMval, hbLval, hbRval]
        simp [twoSpanValue, hc]
      · intro r hr
        rw [hbMpres r hr.2.1, hbRpres r hr.1]
        rw [hcR, RegFile.write_other _ _ hr.2.2.2.1]
        rw [hbSpres r hr.2.2.1, hbLpres r hr.1]
        rw [ha12, RegFile.write_other _ _ hr.2.2.2.2.1]
        rw [ha11, RegFile.write_other _ _ hr.2.2.2.1]
        rw [ha10, RegFile.write_other _ _ hr.2.2.2.2.2.2.2.2.1]
        rw [ha9, RegFile.write_other _ _ hr.2.2.2.2.2.2.2.2.1]
        rw [ha8, RegFile.write_other _ _ hr.2.2.2.2.2.2.2.1]
        rw [ha7, RegFile.write_other _ _ hr.2.2.2.2.2.2.2.2.1]
        rw [ha6, RegFile.write_other _ _ hr.2.2.2.2.2.2.2.1]
        rw [ha5, RegFile.write_other _ _ hr.2.2.2.2.2.2.2.1]
        rw [ha4, RegFile.write_other _ _ hr.2.2.2.2.2.2.1]
        rw [ha3, RegFile.write_other _ _ hr.2.2.2.2.2.2.2.2.1]
        exact hBase r hr

/-! ## THE TWO INSTANTIATIONS: `#4` AND `#5`

`twoSpanBlock` is parametric in the level geometry, the span geometry,
the level stride and the domain.  The two route computations it covers
are its instantiations at the two pairs below.

The level geometries are DEFINED by the §4 recipe -- each field is the
ROUTE's own quantity -- so `geomRouteDecode_eq_readComputation_value`'s
three hypotheses are `rfl` and `hvalid`/`hentries` are the SAME
proposition, one validity split discharging both.  `entriesLen` is
`bpSparseLevelEntries`' length at the table's own domain, which is
exactly the entry list `PayloadLiveBPSparseLevelTable` carries
(`SparseLevelTable.lean:169`). -/

/-- Read geometry of the interior's LOCAL level/span table, the table
`canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation` reads. -/
def localLevelGeom (shape : Cartesian.CartesianShape) : TableGeom :=
  { base := (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
  , entriesLen :=
      (bpSparseLevelEntries
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSize)).length
  , chunkCount :=
      SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (bpSparseLevelWidth
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize))
        (SuccinctRank.machineWordBits shape.bpCode.length) }

/-- Read geometry of the interior's GLOBAL level/span table. -/
def globalLevelGeom (shape : Cartesian.CartesianShape) : TableGeom :=
  { base := (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel
  , entriesLen :=
      (bpSparseLevelEntries
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)).length
  , chunkCount :=
      SuccinctSpace.fixedWidthNatTableMachineChunkCount
        (bpSparseLevelWidth
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount))
        (SuccinctRank.machineWordBits shape.bpCode.length) }

/-- `#4`'s level cap, as `twoSpanBlock_runsTo` carries it. -/
theorem localLevelGeom_cap (shape : Cartesian.CartesianShape) :
    (localLevelGeom shape).chunkCount ≤ 8 :=
  E1InteriorChunkCap.chunkCount_le_eight_localLevelWidth shape

/-- `#4`'s level positivity. -/
theorem localLevelGeom_pos (shape : Cartesian.CartesianShape) :
    0 < (localLevelGeom shape).chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_localLevelWidth shape

/-- `#5`'s level cap. -/
theorem globalLevelGeom_cap (shape : Cartesian.CartesianShape) :
    (globalLevelGeom shape).chunkCount ≤ 8 :=
  E1InteriorChunkCap.chunkCount_le_eight_globalLevelWidth shape

/-- `#5`'s level positivity. -/
theorem globalLevelGeom_pos (shape : Cartesian.CartesianShape) :
    0 < (globalLevelGeom shape).chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_globalLevelWidth shape

/-- The cell bridge at `#4`'s level geometry, UNCONDITIONAL IN `slot`.

This is where `hexact_localLevel_concrete` -- which did not exist before
this session -- is consumed.  The valid case is the substantive one; the
invalid case has a vacuous premise. -/
theorem geomCell_localLevel_eq_routeDecode
    (shape : Cartesian.CartesianShape) (i : Nat) :
    E1InteriorSummaryGroup.geomCell
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) (localLevelGeom shape) i =
      E1InteriorSummaryGroup.geomRouteDecode
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) (localLevelGeom shape) i := by
  by_cases hvalid : i < (localLevelGeom shape).entriesLen
  · exact E1InteriorSummaryGroup.geomCell_eq_routeDecode shape _ i
      (localLevelGeom_cap shape)
      (E1InteriorStoreConcrete.hexact_localLevel_concrete rfl hvalid hvalid)
  · exact E1InteriorSummaryGroup.geomCell_eq_routeDecode_of_invalid shape _ i
      (localLevelGeom_cap shape) hvalid

/-- The cell bridge at `#5`'s level geometry.  UNCONDITIONAL IN `slot`. -/
theorem geomCell_globalLevel_eq_routeDecode
    (shape : Cartesian.CartesianShape) (i : Nat) :
    E1InteriorSummaryGroup.geomCell
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) (globalLevelGeom shape) i =
      E1InteriorSummaryGroup.geomRouteDecode
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) (globalLevelGeom shape) i := by
  by_cases hvalid : i < (globalLevelGeom shape).entriesLen
  · exact E1InteriorSummaryGroup.geomCell_eq_routeDecode shape _ i
      (globalLevelGeom_cap shape)
      (E1InteriorStoreConcrete.hexact_globalLevel_concrete rfl hvalid hvalid)
  · exact E1InteriorSummaryGroup.geomCell_eq_routeDecode_of_invalid shape _ i
      (globalLevelGeom_cap shape) hvalid

/-- The two level geometries' bases, as the route spells them.  Needed so
`cases` can align the machine-side and route-side scrutinees
SYNTACTICALLY; they are `rfl`, but defeq is not enough for `cases`. -/
@[simp] theorem localLevelGeom_base (shape : Cartesian.CartesianShape) :
    (localLevelGeom shape).base =
      (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel := rfl

@[simp] theorem globalLevelGeom_base (shape : Cartesian.CartesianShape) :
    (globalLevelGeom shape).base =
      (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel := rfl

/-- `#4`'s level cell IS the value of the read computation the route runs,
option shift INVERTED -- stated on `cellOpt`, the form `twoSpanValue`
dispatches on.  No validity, cap or store hypothesis survives. -/
theorem cellOpt_levelCell_localLevel
    (shape : Cartesian.CartesianShape) (i : Nat) :
    cellOpt (levelCell shape (localLevelGeom shape) i) =
      ((canonicalRelativeRmmMachineReadNatComputation shape
            (canonicalRelativeRmmInteriorLocalLevelTable shape).table
            (localLevelGeom shape).base i).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).value := by
  unfold levelCell
  rw [geomCell_localLevel_eq_routeDecode,
    E1InteriorSummaryGroup.geomRouteDecode_eq_readComputation_value shape _
      (canonicalRelativeRmmInteriorLocalLevelTable shape).table _ _ i rfl rfl
      rfl,
    E1InteriorMinCandidate.cellOpt_optShift]

/-- `#5`'s level cell, on the same terms. -/
theorem cellOpt_levelCell_globalLevel
    (shape : Cartesian.CartesianShape) (i : Nat) :
    cellOpt (levelCell shape (globalLevelGeom shape) i) =
      ((canonicalRelativeRmmMachineReadNatComputation shape
            (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
            (globalLevelGeom shape).base i).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).value := by
  unfold levelCell
  rw [geomCell_globalLevel_eq_routeDecode,
    E1InteriorSummaryGroup.geomRouteDecode_eq_readComputation_value shape _
      (canonicalRelativeRmmInteriorGlobalLevelTable shape).table _ _ i rfl rfl
      rfl,
    E1InteriorMinCandidate.cellOpt_optShift]

/-! ### The slot maps, at the two instantiations

`#4`'s is `rfl`; `#5`'s needs `Nat.zero_add` SUBSTANTIVELY, because
`Nat.add` recurses on its second argument so `0 + x` does not reduce.
This is the §4 gotcha at exactly the instantiation it was predicted for --
the global twin's slot base is `0`. -/

@[simp] theorem twoSpanLeftSlot_local (shape : Cartesian.CartesianShape)
    (macroIdx localStart v : Nat) :
    twoSpanLeftSlot
        (macroIdx * ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize))
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        localStart v =
      bpLocalSparseCellSlot (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount macroIdx localStart
        (v / bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSize) := rfl

@[simp] theorem twoSpanRightSlot_local (shape : Cartesian.CartesianShape)
    (macroIdx localStart count v : Nat) :
    twoSpanRightSlot
        (macroIdx * ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize))
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        localStart count v =
      bpLocalSparseCellSlot (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).levelCount macroIdx
        (localStart + count -
          v % bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSize)
        (v / bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSize) := rfl

@[simp] theorem twoSpanLeftSlot_global (shape : Cartesian.CartesianShape)
    (macroStart v : Nat) :
    twoSpanLeftSlot 0 (RelativeRmm.canonicalLayout shape).macroSampleCount
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)
        macroStart v =
      bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount macroStart
        (v / bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) := by
  unfold twoSpanLeftSlot bpGlobalSparseCellSlot
  rw [Nat.zero_add]

@[simp] theorem twoSpanRightSlot_global (shape : Cartesian.CartesianShape)
    (macroStart macroSpanCount v : Nat) :
    twoSpanRightSlot 0
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)
        macroStart macroSpanCount v =
      bpGlobalSparseCellSlot
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        (macroStart + macroSpanCount -
          v % bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount)
        (v / bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount) := by
  unfold twoSpanRightSlot twoSpanRight bpGlobalSparseCellSlot
  rw [Nat.zero_add]

/-- **`#4` INSTANTIATED.** The two-span block's value function, at the
LOCAL level and span geometries and at the route's own parameters, IS the
value of `canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation`.

NO VALIDITY, CAP OR STORE HYPOTHESIS. -/
theorem twoSpanValue_local_eq_routeValue
    (shape : Cartesian.CartesianShape) (macroIdx localStart count : Nat) :
    twoSpanValue shape (localLevelGeom shape)
        (E1InteriorSpanBlock.localSpanGeom shape)
        (macroIdx * ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize))
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        localStart count
        (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize) =
      ((canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
            macroIdx localStart count).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).value := by
  unfold twoSpanValue
    canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation
  rw [cellOpt_levelCell_localLevel, localLevelGeom_base]
  cases hcell : ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorLocalLevelTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).localLevel
        count).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape).segment)).value with
  | none =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell]
      rfl
  | some v =>
      simp only [FlatStoreComputation.bind, FlatStoreComputation.map,
        FlatStoreExecution.append, hcell, twoSpanLeftSlot_local,
        twoSpanRightSlot_local]
      rw [E1InteriorSpanBlock.spanValue_localSpan_eq_routeValue,
        E1InteriorSpanBlock.spanValue_localSpan_eq_routeValue]
      rfl

/-- **`#5` INSTANTIATED.** The global twin, at slot base `0` and block
offset `0`. -/
theorem twoSpanValue_global_eq_routeValue
    (shape : Cartesian.CartesianShape) (macroStart macroSpanCount : Nat) :
    twoSpanValue shape (globalLevelGeom shape)
        (E1InteriorSpanBlock.globalSpanGeom shape) 0
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)
        macroStart macroSpanCount 0 =
      ((canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation shape
            macroStart macroSpanCount).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).value := by
  unfold twoSpanValue
    canonicalRelativeRmmMachineGlobalTwoSpanCandidateComputation
  rw [cellOpt_levelCell_globalLevel, globalLevelGeom_base]
  cases hcell : ((canonicalRelativeRmmMachineReadNatComputation shape
        (canonicalRelativeRmmInteriorGlobalLevelTable shape).table
        (canonicalRelativeRmmInteriorComponentOffsets shape).globalLevel
        macroSpanCount).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape).segment)).value with
  | none =>
      simp only [FlatStoreComputation.bind, FlatStoreExecution.append, hcell]
      rfl
  | some v =>
      simp only [FlatStoreComputation.bind, FlatStoreComputation.map,
        FlatStoreExecution.append, hcell, twoSpanLeftSlot_global,
        twoSpanRightSlot_global]
      rw [E1InteriorSpanBlock.spanValue_globalSpan_eq_routeValue,
        E1InteriorSpanBlock.spanValue_globalSpan_eq_routeValue]
      rfl

/-! ## THE `none` ARM'S DISCRIMINATORS, AND WHERE THE RECEIPT'S POWER
COMES FROM (DD-20260719-054)

RIGHT SHAPE, WRONG CONTENT again -- `some` where the route is `none` --
but this block admits TWO such impostors that fall on OPPOSITE SIDES OF
THE RECEIPT BOUNDARY, and the pair is the point.

`spanNoneArm_discriminates` (`E1InteriorSpanBlock.lean:540`) established
that a receipt cannot reject a `none`-arm impostor; `mergePos_discriminates`
(`E1InteriorMerge.lean:501`) established that a category log cannot reject
an operand-level one.  Read together those invite the conclusion that the
receipt is simply the weaker instrument.  IT IS NOT: what decides the
matter is whether the code the impostor wrongly falls into CONTAINS A
READ.  Both impostors below are the same defect -- a wrong `none`-arm
branch target -- at two of this block's own live numerals:

* **A**, target `Q + 275` -- past only the FIRST span block, landing on
  the shuttle.  The tail it then runs contains the SECOND SPAN READ, so
  the impostor emits a read event the route never emitted.  **The receipt
  catches this one.**
* **B**, target `Q + 500` -- straight to the merge, skipping both span
  blocks.  `mergeBlock_readFree` (`E1InteriorMerge.lean:115`) makes that
  tail read-free, so the receipt and the read count are IDENTICAL to the
  correct arm's.  **The receipt is formally incapable of catching this
  one**, and it is the more dangerous of the two precisely because it is
  the quieter: it merges a STALE left candidate left in `qLV`/`qLP` by a
  previous call and returns it where the route returns `none`.

Both are caught by the positional category log and by the value.  The
fixture runs all three arms and states each non-entailment. -/

/-- The empty store.  No arm may depend on the store, and using the empty
one makes that manifest -- the read at index `4` still EMITS its event,
which is the whole content of impostor A's visibility. -/
def twoSpanStore : ReadStore := ⟨fun _ _ => none⟩

/-- THE THREE ARMS, DIFFERING IN ONE NUMERAL.

Index `0` sets the result to `none`; index `1` jumps to `target`.  Indices
`2`-`3` are the shuttle, `4` stands in for the second span block's READ,
`5`-`6` for its result, `7`-`15` are the REAL two-way merge at its own
base `7`, and `16` halts.

`target = 16` is the correct arm -- past everything, as `Q + 509` is.
`target = 2` is impostor A (lands on the shuttle, as `Q + 275` would);
`target = 7` is impostor B (lands on the merge, as `Q + 500` would). -/
def twoSpanNoneProgram (target : Nat) : E1Machine.Program :=
  [ Instr.const mMV 0
  , Instr.brNZ tOne target
  , Instr.move qLV mMV
  , Instr.move qLP mMP
  , Instr.readMem tCell 0 pSlot
  , Instr.const mMV 7
  , Instr.const mMP 3 ] ++ (mergeBlock 7 ++ [Instr.halt])

/-- `tOne` carries the unconditional-jump condition; `qLV`/`qLP` hold the
STALE left candidate a previous call left behind, which is what impostor
B returns. -/
def twoSpanRegs : RegFile := fun r =>
  if r = tOne then 1
  else if r = qLV then 9
  else if r = qLP then 4
  else 0

/-- The arm's value, in the form the combiners consume. -/
def twoSpanOut (target : Nat) : Option (Nat × Nat) :=
  let final :=
    (E1Machine.run twoSpanStore (twoSpanNoneProgram target) 40
      ⟨twoSpanRegs, 0, false⟩).final.regs
  bestOfRegs (final mMV) (final mMP)

/-- The arm's receipt. -/
def twoSpanReadLog (target : Nat) : List TraceEvent :=
  (E1Machine.run twoSpanStore (twoSpanNoneProgram target) 40
    ⟨twoSpanRegs, 0, false⟩).readLog

/-- The arm's charge log. -/
def twoSpanCatLog (target : Nat) : List Category :=
  (E1Machine.run twoSpanStore (twoSpanNoneProgram target) 40
    ⟨twoSpanRegs, 0, false⟩).catLog

/-- The correct arm returns `none`, which is the route's value on the
`none` arm (`InteriorDirectory.lean:2373`, `:2398`). -/
theorem twoSpanOut_correct : twoSpanOut 16 = none := by rfl

/-- Impostor A returns the second span's stand-in result. -/
theorem twoSpanOut_impostorA : twoSpanOut 2 = some (6, 3) := by rfl

/-- Impostor B returns the STALE left candidate -- a value assembled from
a register the route never wrote on this arm. -/
theorem twoSpanOut_impostorB : twoSpanOut 7 = some (8, 4) := by rfl

/-- THE DISCRIMINATORS: both wrong targets are WRONG, not merely
differently spelled. -/
theorem twoSpanNoneArm_discriminates :
    twoSpanOut 16 ≠ twoSpanOut 2 ∧ twoSpanOut 16 ≠ twoSpanOut 7 :=
  ⟨by decide, by decide⟩

/-- **THE RECEIPT CATCHES A.**  The tail impostor A falls into contains
the second span read, so its receipt carries an event the correct arm's
does not. -/
theorem twoSpanNoneArm_receipt_catches_impostorA :
    twoSpanReadLog 16 ≠ twoSpanReadLog 2 := by decide

/-- **THE RECEIPT IS BLIND TO B**, and this is the sharp half of the
pair: the merge is read-free, so skipping straight to it leaves the
receipt EXACTLY the correct arm's -- both empty, so the read COUNT does
not separate them either.  A receipt equation is formally incapable of
rejecting impostor B. -/
theorem twoSpanNoneArm_receipt_blind_to_impostorB :
    twoSpanReadLog 16 = twoSpanReadLog 7 ∧ twoSpanReadLog 16 = [] :=
  ⟨by rfl, by rfl⟩

/-- What catches BOTH besides the value: the positional category log.
Recorded so the boundary is exact rather than implied. -/
theorem twoSpanNoneArm_catLogs_differ :
    twoSpanCatLog 16 ≠ twoSpanCatLog 2 ∧ twoSpanCatLog 16 ≠ twoSpanCatLog 7 :=
  ⟨by decide, by decide⟩

/-- NON-ENTAILMENT: the exit code separates nothing -- all three halt. -/
theorem twoSpanNoneArm_all_halt :
    (E1Machine.run twoSpanStore (twoSpanNoneProgram 16) 40
        ⟨twoSpanRegs, 0, false⟩).final.halted = true ∧
      (E1Machine.run twoSpanStore (twoSpanNoneProgram 2) 40
        ⟨twoSpanRegs, 0, false⟩).final.halted = true ∧
      (E1Machine.run twoSpanStore (twoSpanNoneProgram 7) 40
        ⟨twoSpanRegs, 0, false⟩).final.halted = true :=
  ⟨by rfl, by rfl, by rfl⟩

/-! ### The preservation clause, EXECUTED

`twoSpanBlock_runsTo`'s third clause is run here on the same fixture,
with the four cross-block-arm operands seeded with DISTINCT MARKS so that
survival is discriminating rather than trivially true at zero. -/

/-- The fixture's register file with `70`, `71`, `75`, `76` marked. -/
def twoSpanRegsMarked : RegFile := fun r =>
  if r = 70 then 91
  else if r = 71 then 92
  else if r = 75 then 93
  else if r = 76 then 94
  else twoSpanRegs r

/-- The four operands as the run leaves them. -/
def twoSpanOperands (target : Nat) : List Nat :=
  let final :=
    (E1Machine.run twoSpanStore (twoSpanNoneProgram target) 40
      ⟨twoSpanRegsMarked, 0, false⟩).final.regs
  [final 70, final 71, final 75, final 76]

/-- EXECUTED: the marks survive the correct arm intact. -/
theorem twoSpanOperands_preserved_correct :
    twoSpanOperands 16 = [91, 92, 93, 94] := by rfl

/-- EXECUTED, AND THE LAST NON-ENTAILMENT: they survive BOTH impostors,
so preservation separates neither.  Collecting the instruments: for
impostor B, receipt, read count, exit code and preservation ALL agree
with the correct arm; only the category log and the value reject it. -/
theorem twoSpanOperands_preserved_impostors :
    twoSpanOperands 2 = [91, 92, 93, 94] ∧
      twoSpanOperands 7 = [91, 92, 93, 94] :=
  ⟨by rfl, by rfl⟩

end E1InteriorTwoSpan
end WordRAM
end RMQ
