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

end E1InteriorTwoSpan
end WordRAM
end RMQ
