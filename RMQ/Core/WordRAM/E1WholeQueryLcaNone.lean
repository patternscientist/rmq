import RMQ.Core.WordRAM.E1WholeQueryProgram

/-!
# `.lcaNone` ON THE SAME-BLOCK ARM: SETTLED BY PROOF, NOT ASSUMED

**THE QUESTION.** `WholeQueryBranch` (`E1RouteDecomposition.lean:208`) has
four constructors and the whole-query composition executes three of them.
`.lcaNone` has NO machine stage at all.  Two readings were open, and the
previous lane correctly declined to guess between them:

* `.lcaNone` is UNREACHABLE at these arms -- then the branch is discharged
  by vacuity, and **a vacuous premise owes a witness of vacuity on the same
  terms**, so the unreachability is itself a proof obligation;
* `.lcaNone` is REACHABLE -- then a dispatch stage is owed and the
  composition is incomplete.

**THE ANSWER, ON THE SAME-BLOCK ARM: UNREACHABLE, AND HERE IS THE
WITNESS.**  `wholeQueryBranch_ne_lcaNone_of_sameBlock` below.

**THE RISK THE PREVIOUS LANE NAMED WAS REAL AND IS DISPOSED OF HERE.**  It
observed that an arm theorem stated as `some (regsF fRes) = arm.value`
PRESUPPOSES the arm's value is `some`, so the someness might be an artefact
of how the theorem was stated rather than a fact about the machine.  It is
not.  Every hypothesis on the chain that produces that conclusion was
inspected:

* `closeLcaProgramAt_runsTo_same` (`E1WholeQueryCloseLca.lean:191`) --
  `hHost`, `regs`, `hClose`, `hRight`, `hsame`.  `hsame` is a BLOCK-INDEX
  equation; the other four are hosting and register content.
* `sameBlockLegProgramAt_runsTo_canonical` (`E1SameBlockLeg.lean:805`) and
  `sameBlockLeg_runsTo_canonical` (`:453`) -- hosting and register facts
  only.

**NOT ONE OF THEM IS `Option`-SHAPED.**  There is no `arm.value = some x`,
no `isSome`, no `Nat`-valued input standing in for a decoded answer.  The
someness is therefore DERIVED by the machine's own execution, not assumed
by the statement, and the presupposition worry does not apply.

**THE WITNESS IS FOUND AT THE TARGET, NOT CONSTRUCTED FOR THE PREMISE.**
This module does not manufacture a hosting or a register file to
instantiate the arm theorem -- doing so would be a witness built FOR a
premise.  It consumes `wholeQueryProgram_runsTo_sameBlock`
(`E1WholeQueryProgram.lean:1034`), which is already stated and proven at
the REAL `wholeQueryProgram shape n` running from `initialState`, and
reads the someness off its second conjunct.

`n` is instantiated at `right`, so `hbound : right ≤ n` is `Nat.le_refl`
and neither `n` nor `hbound` appears in either statement below.  The four
hypotheses that remain are not decorative: `hleftVal` and `hrightVal` are
exactly the conditions under which `wholeQueryBranch` REACHES its third
scrutinee at all, and `hsame` is the arm selector.

**SCOPE, STATED HONESTLY.  THIS SETTLES THE SAME-BLOCK ARM ONLY.**  On the
CROSS arm the same argument is not available today: the cross arm theorem
concludes someness of `crossBlockArmSpec … ⟨dispatchRouteValue …,
dispatchEvents …⟩ … .value`, and identifying THAT with the route's
`bpChunkedCrossBlockClose…` still needs the interior reconciliation
recorded in `E1WholeQueryProgram.lean`'s scope note.  So `.lcaNone` on the
cross arm is NOT settled here and must not be assumed either way -- the
same discipline that produced this module's answer.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine
open E1SameBlockArm
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-- **THE CLOSE/LCA LEG ANSWERS `some` ON THE SAME-BLOCK ARM.**

Read off the second conjunct of `wholeQueryProgram_runsTo_sameBlock`, then
carried from the machine's arm object to the ROUTE's own close/LCA leg by
the three rewrites that were built for exactly this crossing:
`lcaLeg_eq_withStore_at_globalReadStore` (`E1WholeQueryObjects.lean:110`)
puts the route's leg in store-parametric form at the global store,
`lcaLeg_of_sameBlock` (`E1WholeQueryLcaLeg.lean:64`) selects the same-block
arm under `hsame`, and `lcaLeg_sameBlock_rankSeed_eq`
(`E1WholeQueryLcaLeg.lean:132`) identifies the rank seed the two sides
spell differently.

The conclusion is about the ROUTE object, so nothing machine-side survives
into it. -/
theorem sameBlockLcaLeg_value_eq_some (shape : Cartesian.CartesianShape)
    {left right cl cr : Nat}
    (hlt : left < right)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some cl)
    (hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = some cr)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    ∃ answerClose : Nat,
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape cl cr).value = some answerClose := by
  obtain ⟨_regsF, answerClose, _hrun, hval, _hout⟩ :=
    wholeQueryProgram_runsTo_sameBlock shape (n := right) hlt
      (Nat.le_refl right) hleftVal hrightVal hsame
  refine ⟨answerClose, ?_⟩
  rw [lcaLeg_eq_withStore_at_globalReadStore,
    lcaLeg_of_sameBlock shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      cl cr hsame,
    lcaLeg_sameBlock_rankSeed_eq]
  exact hval.symm

/-- **THE VACUITY WITNESS: `.lcaNone` IS UNREACHABLE ON THE SAME-BLOCK
ARM.**

Stated POSITIVELY first -- the branch is `.full` -- because a bare
`≠ .lcaNone` would leave open which constructor it is, and the positive
form is what the composition actually consumes. -/
theorem wholeQueryBranch_eq_full_of_sameBlock
    (shape : Cartesian.CartesianShape) {left right cl cr : Nat}
    (hlt : left < right)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some cl)
    (hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = some cr)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    ∃ answerClose : Nat,
      wholeQueryBranch shape left right = .full cl cr answerClose := by
  obtain ⟨answerClose, hlca⟩ :=
    sameBlockLcaLeg_value_eq_some shape hlt hleftVal hrightVal hsame
  exact ⟨answerClose,
    wholeQueryBranch_eq_full shape left right hleftVal hrightVal hlca⟩

/-- **`.lcaNone` IS NOT TAKEN.**  The corollary in the form the obligation
was posed in: on the same-block arm the route's branch is never
`.lcaNone`, so the missing machine stage is owed to NOTHING and the
composition is not incomplete on this arm.

This is the witness of vacuity that the vacuous branch owes.  It is stated
on the SAME TERMS as the branch it discharges -- same `shape`, same
`left`/`right`, same select values, same arm condition -- rather than at a
fixture or a specialisation. -/
theorem wholeQueryBranch_ne_lcaNone_of_sameBlock
    (shape : Cartesian.CartesianShape) {left right cl cr : Nat}
    (hlt : left < right)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some cl)
    (hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = some cr)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    wholeQueryBranch shape left right ≠ .lcaNone cl cr := by
  obtain ⟨answerClose, hfull⟩ :=
    wholeQueryBranch_eq_full_of_sameBlock shape hlt hleftVal hrightVal hsame
  rw [hfull]
  intro h
  exact WholeQueryBranch.noConfusion h

/-- **ANTI-VACUITY FOR THE VACUITY WITNESS ITSELF.**

A theorem saying "this branch never fires" is worth nothing if its own
hypotheses can never be met -- it would then be vacuous in exactly the way
it claims to dispose of.  `.lcaNone`'s constructor is REACHABLE as a term
and its route value IS `none`, so the branch being excluded is a real
branch of a real datatype and not a dead constructor; and
`wholeQueryBranch_eq_lcaNone` (`E1RouteDecomposition.lean:260`) shows the
route does produce it whenever the LCA leg answers `none`.

What the theorem above establishes is therefore substantive: the
same-block ARM is where that `none` cannot happen, not that the
constructor is unreachable everywhere. -/
theorem lcaNone_is_a_real_branch (shape : Cartesian.CartesianShape)
    (cl cr : Nat) :
    wholeQueryBranchValue shape (.lcaNone cl cr) = none := rfl

end E1Query
end WordRAM
end RMQ
