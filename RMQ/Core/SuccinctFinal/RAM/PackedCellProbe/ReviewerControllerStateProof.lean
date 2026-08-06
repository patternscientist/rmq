import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerProof
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerAtomicStateProof
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerInteriorStateProof

/-!
# Canonically reachable reviewer-controller state bounds

`ReviewerControllerProof` defines the exhaustive proof-side inventories for
the first-order controller state.  This module supplies the deliberately
separate reachability argument: only prefixes obtained by repeatedly answering
the controller's emitted request from `packedReviewerMemory shape` are claimed
to fit the fixed state-machine envelope.  In particular, the recursive
continuation datatypes remain unrestricted outside that operational domain.

## Frozen acceptance matrix

* `RCS-01` -- "Prove every `PackedReviewerCanonicalReachable shape left right
  state` actual controller prefix satisfies
  `PackedReviewerControllerStateMachineFits shape.size state`."  The planned
  evidence is the checked type of
  `packedReviewerCanonicalReachable_state_machine_fits`, consumed by
  `packedReviewerReachableStateCertificate_of_reachable` on the identical
  `shape`, endpoints, state, and reachability witness.  The anti-vacuity
  challenge is an arbitrarily deep hand-built candidate continuation; it is
  excluded only once that theorem requires the inductive canonical-memory
  reachability witness.
* `RCS-02` -- "Define explicit finite register/buffer/cardinality and recursive
  continuation-depth inventories, prove literal bounds for every canonically
  reachable state, and expose one public certificate/bundle theorem over
  actual canonical controller prefixes."  The inventories and literal
  `512`/`212`/`1`/`3` bounds are the imported
  `PackedReviewerControllerStateMachineFits` projections.  This module's
  certificate repeats those exact propositions as typed public fields; the
  canonical-start inhabitant is a pending acceptance item until its constructor
  theorem elaborates below.
* `RCS-03` -- "Include finite phase/control tag fit if needed."  The
  certificate projects the exact phase-tag and control-field propositions and
  the constructor-exhaustive nested tag inventory for Entry, Rank,
  WordSelect, Fringe, BPWindow, InteriorNat, both continuation languages,
  Interior, Select, LCA, Whole, and SparsePrelude.
* `RCS-04` -- "The theorem must be inhabited/load-bearing, not declaration
  theater, and cover actual transitions against `packedReviewerMemory`; do not
  assert arbitrary recursive continuations are bounded."  The certificate
  already retains `PackedReviewerCanonicalReachable` itself.  Closure requires
  the still-pending constructor from an actual witness and the concrete start
  certificate; their declarations alone are not counted as evidence.
* `INV-STORE-IDENTITY` -- the transition reply in the retained reachability
  witness is definitionally
  `(packedReviewerMemory shape)[request.address]?`; no sibling store occurs.
* `INV-SEMANTIC-NONVACUITY` -- the accepted predicate is canonical operational
  reachability, not `True` or a constructor inventory.  Removing a canonical
  reply step prevents construction of the successor witness.
* `INV-WORD-WIDTH`, `INV-ALL-SIZE`, `INV-PROOF-SEPARATION`, and
  `INV-CATEGORY-SEPARATION` -- the proof quantifies over every shape and keeps
  reply-word, scalar, wide-buffer, continuation, and control bounds in their
  distinct imported fields; it does not alter executable state.
* `INV-CERTIFICATE-ANTI-BYPASS` --
  `packedReviewerReachableStateCertificate_requiredFacts` projects every
  advertised field at the exact objects, giving validation an independent
  expected proposition to pin.

Verification ledger (source-only until the shared Lean process is released):
the development check is the focused elaboration of this file; final static
checks are the required hygiene scan and `git diff --check`.  A broad build is
disproportionate for this one new downstream proof module and remains owned by
the integrating coordinator.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ## Exhaustive nested constructor tags -/

/-- Static constructor code for the four-field entry reader. -/
def packedReviewerEntryStateTagCode : PackedReviewerEntryState -> Nat
  | .baseOccurrence .. => 0
  | .baseWordIndex .. => 1
  | .rankBefore .. => 2
  | .firstOffset .. => 3
  | .done .. => 4

/-- Static constructor code for the rank reader/fold. -/
def packedReviewerRankStateTagCode : PackedReviewerRankState -> Nat
  | .superSample .. => 0
  | .blockSample .. => 1
  | .word .. => 2
  | .fold .. => 3
  | .done .. => 4

/-- Static constructor code for the charged in-word select fold. -/
def packedReviewerWordSelectStateTagCode : PackedReviewerWordSelectState -> Nat
  | .rankChunk .. => 0
  | .selectChunk .. => 1
  | .done .. => 2

/-- Static constructor code for the charged fringe fold. -/
def packedReviewerFringeStateTagCode : PackedReviewerFringeState -> Nat
  | .chunk .. => 0
  | .done .. => 1

/-- Static constructor code for the four-word BP-window reader. -/
def packedReviewerBPWindowStateTagCode : PackedReviewerBPWindowState -> Nat
  | .read .. => 0
  | .done .. => 1

/-- Static constructor code for one segment-20 fixed-width read. -/
def packedReviewerInteriorNatStateTagCode :
    PackedReviewerInteriorNatState -> Nat
  | .read .. => 0
  | .done .. => 1

/-- Static constructor code for every candidate-continuation frame. -/
def packedReviewerCandidateContinuationTagCode :
    PackedReviewerCandidateContinuation -> Nat
  | .finish => 0
  | .localTwoLeft .. => 1
  | .localTwoRight .. => 2
  | .globalTwoLeft .. => 3
  | .globalTwoRight .. => 4
  | .adjacentLeft .. => 5
  | .adjacentRight .. => 6
  | .leftMiddleLeft .. => 7
  | .leftMiddleMiddle .. => 8
  | .crossLeft .. => 9
  | .crossMiddle .. => 10
  | .crossRight .. => 11

/-- Static constructor code for every pending interior-Nat action. -/
def packedReviewerInteriorNatContinuationTagCode :
    PackedReviewerInteriorNatContinuation -> Nat
  | .summaryBaseline .. => 0
  | .summaryMin .. => 1
  | .summaryMax .. => 2
  | .summaryArg .. => 3
  | .localOffset .. => 4
  | .globalBlock .. => 5
  | .localLevel .. => 6
  | .globalLevel .. => 7

/-- Static constructor code for the normalized interior controller. -/
def packedReviewerInteriorStateTagCode : PackedReviewerInteriorState -> Nat
  | .readNat .. => 0
  | .done .. => 1

/-- Static constructor code for the close-select controller. -/
def packedReviewerSelectStateTagCode : PackedReviewerSelectState -> Nat
  | .superEntry .. => 0
  | .localEntry .. => 1
  | .longRank .. => 2
  | .longRelative .. => 3
  | .sparseRank .. => 4
  | .sparseRelative .. => 5
  | .denseFirstWord .. => 6
  | .denseBeforeRank .. => 7
  | .denseUptoRank .. => 8
  | .denseFirstSelect .. => 9
  | .denseSecondWord .. => 10
  | .denseSecondSelect .. => 11
  | .done .. => 12

/-- Static constructor code for the close/LCA controller. -/
def packedReviewerLcaStateTagCode : PackedReviewerLcaState -> Nat
  | .sameSeed .. => 0
  | .sameWindow .. => 1
  | .sameFringe .. => 2
  | .leftSeed .. => 3
  | .leftWindow .. => 4
  | .leftFringe .. => 5
  | .middle .. => 6
  | .rightSeed .. => 7
  | .rightWindow .. => 8
  | .rightFringe .. => 9
  | .done .. => 10

/-- Static constructor code for the whole-query logical controller. -/
def packedReviewerWholeStateTagCode : PackedReviewerWholeState -> Nat
  | .leftSelect .. => 0
  | .rightSelect .. => 1
  | .lcaClose .. => 2
  | .finalRank .. => 3
  | .done .. => 4

/-- Static constructor code for the fixed K1 sparse-count prelude. -/
def packedReviewerSparsePreludeStateTagCode :
    PackedReviewerSparsePreludeState -> Nat
  | .awaitSuper .. => 0
  | .awaitBlock .. => 1
  | .awaitFlag .. => 2
  | .done .. => 3

theorem packedReviewerEntryStateTagCode_fits
    (n : Nat) (state : PackedReviewerEntryState) :
    PackedReviewerNatFits n (packedReviewerEntryStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerEntryStateTagCode]

theorem packedReviewerRankStateTagCode_fits
    (n : Nat) (state : PackedReviewerRankState) :
    PackedReviewerNatFits n (packedReviewerRankStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerRankStateTagCode]

theorem packedReviewerWordSelectStateTagCode_fits
    (n : Nat) (state : PackedReviewerWordSelectState) :
    PackedReviewerNatFits n (packedReviewerWordSelectStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerWordSelectStateTagCode]

theorem packedReviewerFringeStateTagCode_fits
    (n : Nat) (state : PackedReviewerFringeState) :
    PackedReviewerNatFits n (packedReviewerFringeStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerFringeStateTagCode]

theorem packedReviewerBPWindowStateTagCode_fits
    (n : Nat) (state : PackedReviewerBPWindowState) :
    PackedReviewerNatFits n (packedReviewerBPWindowStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerBPWindowStateTagCode]

theorem packedReviewerInteriorNatStateTagCode_fits
    (n : Nat) (state : PackedReviewerInteriorNatState) :
    PackedReviewerNatFits n
      (packedReviewerInteriorNatStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerInteriorNatStateTagCode]

theorem packedReviewerCandidateContinuationTagCode_fits
    (n : Nat) (continuation : PackedReviewerCandidateContinuation) :
    PackedReviewerNatFits n
      (packedReviewerCandidateContinuationTagCode continuation) := by
  apply packedReviewerFiniteControlCode_fits
  cases continuation <;> simp [packedReviewerCandidateContinuationTagCode]

theorem packedReviewerInteriorNatContinuationTagCode_fits
    (n : Nat) (continuation : PackedReviewerInteriorNatContinuation) :
    PackedReviewerNatFits n
      (packedReviewerInteriorNatContinuationTagCode continuation) := by
  apply packedReviewerFiniteControlCode_fits
  cases continuation <;>
    simp [packedReviewerInteriorNatContinuationTagCode]

theorem packedReviewerInteriorStateTagCode_fits
    (n : Nat) (state : PackedReviewerInteriorState) :
    PackedReviewerNatFits n (packedReviewerInteriorStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerInteriorStateTagCode]

theorem packedReviewerSelectStateTagCode_fits
    (n : Nat) (state : PackedReviewerSelectState) :
    PackedReviewerNatFits n (packedReviewerSelectStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerSelectStateTagCode]

theorem packedReviewerLcaStateTagCode_fits
    (n : Nat) (state : PackedReviewerLcaState) :
    PackedReviewerNatFits n (packedReviewerLcaStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerLcaStateTagCode]

theorem packedReviewerWholeStateTagCode_fits
    (n : Nat) (state : PackedReviewerWholeState) :
    PackedReviewerNatFits n (packedReviewerWholeStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerWholeStateTagCode]

theorem packedReviewerSparsePreludeStateTagCode_fits
    (n : Nat) (state : PackedReviewerSparsePreludeState) :
    PackedReviewerNatFits n
      (packedReviewerSparsePreludeStateTagCode state) := by
  apply packedReviewerFiniteControlCode_fits
  cases state <;> simp [packedReviewerSparsePreludeStateTagCode]

/-- Every currently retained candidate frame, including all outer frames. -/
def packedReviewerCandidateContinuationTagCodes :
    PackedReviewerCandidateContinuation -> List Nat
  | .finish => [0]
  | .localTwoLeft _ _ _ _ _ outer =>
      1 :: packedReviewerCandidateContinuationTagCodes outer
  | .localTwoRight _ outer =>
      2 :: packedReviewerCandidateContinuationTagCodes outer
  | .globalTwoLeft _ _ _ _ outer =>
      3 :: packedReviewerCandidateContinuationTagCodes outer
  | .globalTwoRight _ outer =>
      4 :: packedReviewerCandidateContinuationTagCodes outer
  | .adjacentLeft _ _ _ outer =>
      5 :: packedReviewerCandidateContinuationTagCodes outer
  | .adjacentRight _ outer =>
      6 :: packedReviewerCandidateContinuationTagCodes outer
  | .leftMiddleLeft _ _ _ outer =>
      7 :: packedReviewerCandidateContinuationTagCodes outer
  | .leftMiddleMiddle _ outer =>
      8 :: packedReviewerCandidateContinuationTagCodes outer
  | .crossLeft _ _ _ _ outer =>
      9 :: packedReviewerCandidateContinuationTagCodes outer
  | .crossMiddle _ _ _ _ _ outer =>
      10 :: packedReviewerCandidateContinuationTagCodes outer
  | .crossRight _ _ outer =>
      11 :: packedReviewerCandidateContinuationTagCodes outer

/-- The pending Nat action followed by all retained candidate frames. -/
def packedReviewerInteriorNatContinuationTagCodes :
    PackedReviewerInteriorNatContinuation -> List Nat
  | .summaryBaseline _ _ outer =>
      0 :: packedReviewerCandidateContinuationTagCodes outer
  | .summaryMin _ _ _ outer =>
      1 :: packedReviewerCandidateContinuationTagCodes outer
  | .summaryMax _ _ _ _ outer =>
      2 :: packedReviewerCandidateContinuationTagCodes outer
  | .summaryArg _ _ _ _ _ outer =>
      3 :: packedReviewerCandidateContinuationTagCodes outer
  | .localOffset _ _ _ _ outer =>
      4 :: packedReviewerCandidateContinuationTagCodes outer
  | .globalBlock _ _ _ outer =>
      5 :: packedReviewerCandidateContinuationTagCodes outer
  | .localLevel _ _ _ _ outer =>
      6 :: packedReviewerCandidateContinuationTagCodes outer
  | .globalLevel _ _ _ outer =>
      7 :: packedReviewerCandidateContinuationTagCodes outer

def packedReviewerInteriorStateTagCodes :
    PackedReviewerInteriorState -> List Nat
  | .readNat _ read continuation =>
      0 :: packedReviewerInteriorNatStateTagCode read ::
        packedReviewerInteriorNatContinuationTagCodes continuation
  | .done _ => [1]

def packedReviewerSelectStateTagCodes : PackedReviewerSelectState -> List Nat
  | .superEntry _ _ _ entry => [0, packedReviewerEntryStateTagCode entry]
  | .localEntry _ _ _ _ _ entry => [1, packedReviewerEntryStateTagCode entry]
  | .longRank _ _ _ _ rank => [2, packedReviewerRankStateTagCode rank]
  | .longRelative .. => [3]
  | .sparseRank _ _ _ _ _ _ rank => [4, packedReviewerRankStateTagCode rank]
  | .sparseRelative .. => [5]
  | .denseFirstWord .. => [6]
  | .denseBeforeRank _ _ _ _ _ _ rank =>
      [7, packedReviewerRankStateTagCode rank]
  | .denseUptoRank _ _ _ _ _ _ _ rank =>
      [8, packedReviewerRankStateTagCode rank]
  | .denseFirstSelect _ _ _ select =>
      [9, packedReviewerWordSelectStateTagCode select]
  | .denseSecondWord .. => [10]
  | .denseSecondSelect _ _ _ select =>
      [11, packedReviewerWordSelectStateTagCode select]
  | .done .. => [12]

def packedReviewerLcaStateTagCodes : PackedReviewerLcaState -> List Nat
  | .sameSeed _ _ _ _ rank => [0, packedReviewerRankStateTagCode rank]
  | .sameWindow _ _ _ _ _ window =>
      [1, packedReviewerBPWindowStateTagCode window]
  | .sameFringe _ _ _ _ _ _ _ fringe =>
      [2, packedReviewerFringeStateTagCode fringe]
  | .leftSeed _ _ _ _ rank => [3, packedReviewerRankStateTagCode rank]
  | .leftWindow _ _ _ _ _ window =>
      [4, packedReviewerBPWindowStateTagCode window]
  | .leftFringe _ _ _ _ _ _ _ fringe =>
      [5, packedReviewerFringeStateTagCode fringe]
  | .middle _ _ _ _ _ interior =>
      6 :: packedReviewerInteriorStateTagCodes interior
  | .rightSeed _ _ _ _ _ _ rank => [7, packedReviewerRankStateTagCode rank]
  | .rightWindow _ _ _ _ _ _ _ window =>
      [8, packedReviewerBPWindowStateTagCode window]
  | .rightFringe _ _ _ _ _ _ _ _ _ fringe =>
      [9, packedReviewerFringeStateTagCode fringe]
  | .done .. => [10]

def packedReviewerWholeStateTagCodes : PackedReviewerWholeState -> List Nat
  | .leftSelect _ _ _ select =>
      0 :: packedReviewerSelectStateTagCodes select
  | .rightSelect _ _ _ _ select =>
      1 :: packedReviewerSelectStateTagCodes select
  | .lcaClose _ _ _ _ _ lca => 2 :: packedReviewerLcaStateTagCodes lca
  | .finalRank _ _ _ _ rank => [3, packedReviewerRankStateTagCode rank]
  | .done .. => [4]

/--
All nested constructor tags physically retained by one controller state.  The
top-level phase tag stays in its pre-existing separate certificate field.
-/
def packedReviewerControllerNestedTagCodes :
    PackedReviewerControllerState -> List Nat
  | .preludeReady _ _ _ _ prelude
  | .preludeProbe _ _ _ _ prelude _ _ =>
      [packedReviewerSparsePreludeStateTagCode prelude]
  | .wholeReady _ _ _ _ _ _ whole
  | .wholeProbe _ _ _ _ _ _ whole _ _ =>
      packedReviewerWholeStateTagCodes whole
  | _ => []

private theorem packedReviewerCandidateContinuationTagCodes_lt_sixteen
    (continuation : PackedReviewerCandidateContinuation) :
    forall code, code ∈ packedReviewerCandidateContinuationTagCodes continuation ->
      code < 16 := by
  induction continuation <;>
    simp_all [packedReviewerCandidateContinuationTagCodes]

private theorem packedReviewerTagCons_lt_sixteen
    (head : Nat) (tail : List Nat) (hhead : head < 16)
    (htail : forall code, code ∈ tail -> code < 16) :
    forall code, code ∈ head :: tail -> code < 16 := by
  intro code hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact hhead
  · exact htail code hmem

private theorem packedReviewerEntryStateTagCode_lt_sixteen
    (state : PackedReviewerEntryState) :
    packedReviewerEntryStateTagCode state < 16 := by
  cases state <;> simp [packedReviewerEntryStateTagCode]

private theorem packedReviewerRankStateTagCode_lt_sixteen
    (state : PackedReviewerRankState) :
    packedReviewerRankStateTagCode state < 16 := by
  cases state <;> simp [packedReviewerRankStateTagCode]

private theorem packedReviewerWordSelectStateTagCode_lt_sixteen
    (state : PackedReviewerWordSelectState) :
    packedReviewerWordSelectStateTagCode state < 16 := by
  cases state <;> simp [packedReviewerWordSelectStateTagCode]

private theorem packedReviewerFringeStateTagCode_lt_sixteen
    (state : PackedReviewerFringeState) :
    packedReviewerFringeStateTagCode state < 16 := by
  cases state <;> simp [packedReviewerFringeStateTagCode]

private theorem packedReviewerBPWindowStateTagCode_lt_sixteen
    (state : PackedReviewerBPWindowState) :
    packedReviewerBPWindowStateTagCode state < 16 := by
  cases state <;> simp [packedReviewerBPWindowStateTagCode]

private theorem packedReviewerInteriorNatStateTagCode_lt_sixteen
    (state : PackedReviewerInteriorNatState) :
    packedReviewerInteriorNatStateTagCode state < 16 := by
  cases state <;> simp [packedReviewerInteriorNatStateTagCode]

private theorem packedReviewerSparsePreludeStateTagCode_lt_sixteen
    (state : PackedReviewerSparsePreludeState) :
    packedReviewerSparsePreludeStateTagCode state < 16 := by
  cases state <;> simp [packedReviewerSparsePreludeStateTagCode]

private theorem packedReviewerInteriorNatContinuationTagCodes_lt_sixteen
    (continuation : PackedReviewerInteriorNatContinuation) :
    forall code,
      code ∈ packedReviewerInteriorNatContinuationTagCodes continuation ->
        code < 16 := by
  cases continuation <;>
    simp only [packedReviewerInteriorNatContinuationTagCodes] <;>
    apply packedReviewerTagCons_lt_sixteen <;>
    first
    | omega
    | exact packedReviewerCandidateContinuationTagCodes_lt_sixteen _

private theorem packedReviewerInteriorStateTagCodes_lt_sixteen
    (state : PackedReviewerInteriorState) :
    forall code, code ∈ packedReviewerInteriorStateTagCodes state -> code < 16 := by
  cases state with
  | readNat invocation read continuation =>
      simp only [packedReviewerInteriorStateTagCodes]
      apply packedReviewerTagCons_lt_sixteen
      · omega
      · apply packedReviewerTagCons_lt_sixteen
        · exact packedReviewerInteriorNatStateTagCode_lt_sixteen read
        · exact
            packedReviewerInteriorNatContinuationTagCodes_lt_sixteen
              continuation
  | done value =>
      simp [packedReviewerInteriorStateTagCodes]

private theorem packedReviewerSelectStateTagCodes_lt_sixteen
    (state : PackedReviewerSelectState) :
    forall code, code ∈ packedReviewerSelectStateTagCodes state -> code < 16 := by
  cases state <;>
    simp [packedReviewerSelectStateTagCodes,
      packedReviewerEntryStateTagCode_lt_sixteen,
      packedReviewerRankStateTagCode_lt_sixteen,
      packedReviewerWordSelectStateTagCode_lt_sixteen]

private theorem packedReviewerLcaStateTagCodes_lt_sixteen
    (state : PackedReviewerLcaState) :
    forall code, code ∈ packedReviewerLcaStateTagCodes state -> code < 16 := by
  cases state with
  | middle invocation n leftClose rightClose left interior =>
      simp only [packedReviewerLcaStateTagCodes]
      exact packedReviewerTagCons_lt_sixteen 6
        (packedReviewerInteriorStateTagCodes interior) (by omega)
        (packedReviewerInteriorStateTagCodes_lt_sixteen interior)
  | sameSeed invocation n leftClose rightClose rank
  | leftSeed invocation n leftClose rightClose rank =>
      simp [packedReviewerLcaStateTagCodes,
        packedReviewerRankStateTagCode_lt_sixteen]
  | sameWindow invocation n leftClose rightClose seed window
  | leftWindow invocation n leftClose rightClose seed window =>
      simp [packedReviewerLcaStateTagCodes,
        packedReviewerBPWindowStateTagCode_lt_sixteen]
  | sameFringe invocation n leftClose rightClose seed base start fringe
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      simp [packedReviewerLcaStateTagCodes,
        packedReviewerFringeStateTagCode_lt_sixteen]
  | rightSeed invocation n leftClose rightClose left middle rank =>
      simp [packedReviewerLcaStateTagCodes,
        packedReviewerRankStateTagCode_lt_sixteen]
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      simp [packedReviewerLcaStateTagCodes,
        packedReviewerBPWindowStateTagCode_lt_sixteen]
  | rightFringe invocation n leftClose rightClose seed base start left middle
      fringe =>
      simp [packedReviewerLcaStateTagCodes,
        packedReviewerFringeStateTagCode_lt_sixteen]
  | done value =>
      simp [packedReviewerLcaStateTagCodes]

private theorem packedReviewerWholeStateTagCodes_lt_sixteen
    (state : PackedReviewerWholeState) :
    forall code, code ∈ packedReviewerWholeStateTagCodes state -> code < 16 := by
  cases state with
  | leftSelect n left right select =>
      simp only [packedReviewerWholeStateTagCodes]
      exact packedReviewerTagCons_lt_sixteen 0
        (packedReviewerSelectStateTagCodes select) (by omega)
        (packedReviewerSelectStateTagCodes_lt_sixteen select)
  | rightSelect n left right leftClose select =>
      simp only [packedReviewerWholeStateTagCodes]
      exact packedReviewerTagCons_lt_sixteen 1
        (packedReviewerSelectStateTagCodes select) (by omega)
        (packedReviewerSelectStateTagCodes_lt_sixteen select)
  | lcaClose n left right leftClose rightClose lca =>
      simp only [packedReviewerWholeStateTagCodes]
      exact packedReviewerTagCons_lt_sixteen 2
        (packedReviewerLcaStateTagCodes lca) (by omega)
        (packedReviewerLcaStateTagCodes_lt_sixteen lca)
  | finalRank n left right answerClose rank =>
      simp [packedReviewerWholeStateTagCodes,
        packedReviewerRankStateTagCode_lt_sixteen]
  | done value =>
      simp [packedReviewerWholeStateTagCodes]

private theorem packedReviewerControllerNestedTagCodes_lt_sixteen
    (state : PackedReviewerControllerState) :
    forall code, code ∈ packedReviewerControllerNestedTagCodes state ->
      code < 16 := by
  cases state with
  | preludeReady n left right longCount prelude
  | preludeProbe n left right longCount prelude next replies =>
      simp [packedReviewerControllerNestedTagCodes,
        packedReviewerSparsePreludeStateTagCode_lt_sixteen]
  | wholeReady n left right longCount sparseCount steps whole
  | wholeProbe n left right longCount sparseCount steps whole next replies =>
      simpa [packedReviewerControllerNestedTagCodes] using
        packedReviewerWholeStateTagCodes_lt_sixteen whole
  | header n left right
  | done value
  | failed =>
      simp [packedReviewerControllerNestedTagCodes]

/-- Every retained nested branch/jump tag fits the modeled word, at every size. -/
theorem packedReviewerControllerNestedTagCodes_fits
    (n : Nat) (state : PackedReviewerControllerState) :
    forall code, code ∈ packedReviewerControllerNestedTagCodes state ->
      PackedReviewerNatFits n code := by
  intro code hmem
  apply packedReviewerFiniteControlCode_fits
  exact packedReviewerControllerNestedTagCodes_lt_sixteen state code hmem

/-! ## Structural cardinality bounds -/

private theorem packedReviewerOptionNatFields_length_le_one
    (value : Option Nat) :
    (packedReviewerOptionNatFields value).length <= 1 := by
  cases value <;> simp [packedReviewerOptionNatFields]

private theorem packedReviewerCandidateNatFields_length_le_two
    (value : PackedReviewerCandidate) :
    (packedReviewerCandidateNatFields value).length <= 2 := by
  cases value with
  | none => simp [packedReviewerCandidateNatFields]
  | some value =>
      rcases value with ⟨value, index⟩
      simp [packedReviewerCandidateNatFields]

private theorem packedReviewerEntryValueNatFields_length_le_four
    (value : Option GenericSelect.SparseDenseSelectDenseLocalEntry) :
    (packedReviewerEntryValueNatFields value).length <= 4 := by
  cases value <;> simp [packedReviewerEntryValueNatFields]

private theorem packedReviewerEntryStateNatFields_length_le_six
    (state : PackedReviewerEntryState) :
    (packedReviewerEntryStateNatFields state).length <= 6 := by
  cases state with
  | baseOccurrence invocation kind index =>
      simp [packedReviewerEntryStateNatFields,
        packedReviewerInvocationNatFields]
  | baseWordIndex invocation kind index baseOccurrence =>
      cases baseOccurrence <;>
        simp [packedReviewerEntryStateNatFields,
          packedReviewerInvocationNatFields,
          packedReviewerOptionNatFields]
  | rankBefore invocation kind index baseOccurrence baseWordIndex =>
      cases baseOccurrence <;> cases baseWordIndex <;>
        simp [packedReviewerEntryStateNatFields,
          packedReviewerInvocationNatFields,
          packedReviewerOptionNatFields]
  | firstOffset invocation kind index baseOccurrence baseWordIndex
      rankBefore =>
      cases baseOccurrence <;> cases baseWordIndex <;> cases rankBefore <;>
        simp [packedReviewerEntryStateNatFields,
          packedReviewerInvocationNatFields,
          packedReviewerOptionNatFields]
  | done value =>
      cases value <;>
        simp [packedReviewerEntryStateNatFields,
          packedReviewerEntryValueNatFields]

private theorem packedReviewerRankStateNatFields_length_le_eight
    (state : PackedReviewerRankState) :
    (packedReviewerRankStateNatFields state).length <= 8 := by
  cases state with
  | superSample invocation kind n pos =>
      simp [packedReviewerRankStateNatFields,
        packedReviewerInvocationNatFields]
  | blockSample invocation kind n pos superSample =>
      cases superSample <;>
        simp [packedReviewerRankStateNatFields,
          packedReviewerInvocationNatFields,
          packedReviewerOptionNatFields]
  | word invocation kind n pos superSample blockSample =>
      cases superSample <;> cases blockSample <;>
        simp [packedReviewerRankStateNatFields,
          packedReviewerInvocationNatFields,
          packedReviewerOptionNatFields]
  | fold invocation kind n word effectiveLimit j remaining acc base =>
      simp [packedReviewerRankStateNatFields,
        packedReviewerInvocationNatFields]
  | done value =>
      simp [packedReviewerRankStateNatFields]

private theorem packedReviewerWordSelectStateNatFields_length_le_six
    (state : PackedReviewerWordSelectState) :
    (packedReviewerWordSelectStateNatFields state).length <= 6 := by
  cases state with
  | rankChunk invocation n target word j remaining occurrence
  | selectChunk invocation n target word j remaining occurrence =>
      simp [packedReviewerWordSelectStateNatFields,
        packedReviewerInvocationNatFields]
  | done value =>
      cases value <;>
        simp [packedReviewerWordSelectStateNatFields,
          packedReviewerOptionNatFields]

private theorem packedReviewerFringeStateNatFields_length_le_ten
    (state : PackedReviewerFringeState) :
    (packedReviewerFringeStateNatFields state).length <= 10 := by
  cases state with
  | chunk invocation n window relLo relHi j remaining state =>
      rcases state with ⟨seed, candidate⟩
      have hcandidate :=
        packedReviewerCandidateNatFields_length_le_two candidate
      simp [packedReviewerFringeStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | done state =>
      rcases state with ⟨seed, candidate⟩
      have hcandidate :=
        packedReviewerCandidateNatFields_length_le_two candidate
      simp [packedReviewerFringeStateNatFields] at *
      omega

private theorem packedReviewerBPWindowStateNatFields_length_le_six
    (state : PackedReviewerBPWindowState) :
    (packedReviewerBPWindowStateNatFields state).length <= 6 := by
  cases state <;>
    simp [packedReviewerBPWindowStateNatFields,
      packedReviewerInvocationNatFields]

private theorem packedReviewerInteriorNatStateNatFields_length_le_six
    (state : PackedReviewerInteriorNatState) :
    (packedReviewerInteriorNatStateNatFields state).length <= 6 := by
  cases state with
  | read invocation n start next remaining repliesRev =>
      simp [packedReviewerInteriorNatStateNatFields,
        packedReviewerInvocationNatFields]
  | done value =>
      cases value <;>
        simp [packedReviewerInteriorNatStateNatFields,
          packedReviewerOptionNatFields]

/--
The recursive candidate inventory grows by at most six scalars per retained
continuation frame.  This theorem deliberately relates size to depth; it does
not bound the depth of an arbitrary continuation.
-/
private theorem packedReviewerCandidateContinuationNatFields_length_le
    (continuation : PackedReviewerCandidateContinuation) :
    (packedReviewerCandidateContinuationNatFields continuation).length <=
      6 * packedReviewerCandidateContinuationDepth continuation := by
  induction continuation with
  | finish =>
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth]
  | localTwoLeft n macroIdx localStart count encoded outer ih =>
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | localTwoRight left outer ih =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | globalTwoLeft n macroStart macroSpanCount encoded outer ih =>
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | globalTwoRight left outer ih =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | adjacentLeft n macroStart rightCount outer ih =>
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | adjacentRight left outer ih =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | leftMiddleLeft n macroStart middleCount outer ih =>
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | leftMiddleMiddle left outer ih =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | crossLeft n macroStart middleCount rightCount outer ih =>
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | crossMiddle n macroStart middleCount rightCount left outer ih =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega
  | crossRight left middle outer ih =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      have hmiddle := packedReviewerCandidateNatFields_length_le_two middle
      simp [packedReviewerCandidateContinuationNatFields,
        packedReviewerCandidateContinuationDepth] at *
      omega

private theorem packedReviewerInteriorNatContinuationNatFields_length_le
    (continuation : PackedReviewerInteriorNatContinuation) :
    (packedReviewerInteriorNatContinuationNatFields continuation).length <=
      6 * packedReviewerInteriorNatContinuationDepth continuation := by
  cases continuation with
  | summaryBaseline n block outer =>
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega
  | summaryMin n block baseline outer =>
      have hbase := packedReviewerOptionNatFields_length_le_one baseline
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega
  | summaryMax n block baseline minRel outer =>
      have hbase := packedReviewerOptionNatFields_length_le_one baseline
      have hmin := packedReviewerOptionNatFields_length_le_one minRel
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega
  | summaryArg n block baseline minRel maxRel outer =>
      have hbase := packedReviewerOptionNatFields_length_le_one baseline
      have hmin := packedReviewerOptionNatFields_length_le_one minRel
      have hmax := packedReviewerOptionNatFields_length_le_one maxRel
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega
  | localOffset n macroIdx localStart level outer =>
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega
  | globalBlock n macroStart level outer =>
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega
  | localLevel n macroIdx localStart count outer =>
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega
  | globalLevel n macroStart macroSpanCount outer =>
      have houter :=
        packedReviewerCandidateContinuationNatFields_length_le outer
      simp [packedReviewerInteriorNatContinuationNatFields,
        packedReviewerInteriorNatContinuationDepth] at *
      omega

private theorem packedReviewerInteriorStateNatFields_length_le
    (state : PackedReviewerInteriorState) :
    (packedReviewerInteriorStateNatFields state).length <=
      8 + 6 * packedReviewerInteriorStateContinuationDepth state := by
  cases state with
  | readNat invocation read continuation =>
      have hread := packedReviewerInteriorNatStateNatFields_length_le_six read
      have hcontinuation :=
        packedReviewerInteriorNatContinuationNatFields_length_le continuation
      simp [packedReviewerInteriorStateNatFields,
        packedReviewerInteriorStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | done value =>
      have hvalue := packedReviewerCandidateNatFields_length_le_two value
      simp [packedReviewerInteriorStateNatFields,
        packedReviewerInteriorStateContinuationDepth] at *
      omega

private theorem packedReviewerSelectStateNatFields_length_le_thirty_two
    (state : PackedReviewerSelectState) :
    (packedReviewerSelectStateNatFields state).length <= 32 := by
  cases state with
  | superEntry invocation n index entry =>
      have hentry := packedReviewerEntryStateNatFields_length_le_six entry
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | localEntry invocation n index localSlot super entry =>
      have hsuper :=
        packedReviewerEntryValueNatFields_length_le_four (some super)
      have hentry := packedReviewerEntryStateNatFields_length_le_six entry
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | longRank invocation n index super rank =>
      have hsuper :=
        packedReviewerEntryValueNatFields_length_le_four (some super)
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | longRelative invocation base slot =>
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields]
  | sparseRank invocation n index localSlot super loc rank =>
      have hsuper :=
        packedReviewerEntryValueNatFields_length_le_four (some super)
      have hloc :=
        packedReviewerEntryValueNatFields_length_le_four (some loc)
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | sparseRelative invocation base slot =>
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields]
  | denseFirstWord invocation n index basePosition baseOccurrence =>
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields]
  | denseBeforeRank invocation n index basePosition baseOccurrence word rank =>
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | denseFirstSelect invocation n baseWord select =>
      have hselect :=
        packedReviewerWordSelectStateNatFields_length_le_six select
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | denseSecondWord invocation n index basePosition baseOccurrence beforeFirst
      uptoFirst =>
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields]
  | denseSecondSelect invocation n baseWord select =>
      have hselect :=
        packedReviewerWordSelectStateNatFields_length_le_six select
      simp [packedReviewerSelectStateNatFields,
        packedReviewerInvocationNatFields] at *
      omega
  | done value =>
      have hvalue := packedReviewerOptionNatFields_length_le_one value
      simp [packedReviewerSelectStateNatFields] at *
      omega

private theorem packedReviewerLcaStateNatFields_length_le
    (state : PackedReviewerLcaState) :
    (packedReviewerLcaStateNatFields state).length <=
      32 + 6 * packedReviewerLcaStateContinuationDepth state := by
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | sameWindow invocation n leftClose rightClose seed window =>
      have hwindow := packedReviewerBPWindowStateNatFields_length_le_six window
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      have hfringe := packedReviewerFringeStateNatFields_length_le_ten fringe
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | leftSeed invocation n leftClose rightClose rank =>
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | leftWindow invocation n leftClose rightClose seed window =>
      have hwindow := packedReviewerBPWindowStateNatFields_length_le_six window
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      have hfringe := packedReviewerFringeStateNatFields_length_le_ten fringe
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | middle invocation n leftClose rightClose left interior =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      have hinterior := packedReviewerInteriorStateNatFields_length_le interior
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | rightSeed invocation n leftClose rightClose left middle rank =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      have hmiddle := packedReviewerCandidateNatFields_length_le_two middle
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      have hmiddle := packedReviewerCandidateNatFields_length_le_two middle
      have hwindow := packedReviewerBPWindowStateNatFields_length_le_six window
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | rightFringe invocation n leftClose rightClose seed base start left middle
      fringe =>
      have hleft := packedReviewerCandidateNatFields_length_le_two left
      have hmiddle := packedReviewerCandidateNatFields_length_le_two middle
      have hfringe := packedReviewerFringeStateNatFields_length_le_ten fringe
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth,
        packedReviewerInvocationNatFields] at *
      omega
  | done value =>
      have hvalue := packedReviewerOptionNatFields_length_le_one value
      simp [packedReviewerLcaStateNatFields,
        packedReviewerLcaStateContinuationDepth] at *
      omega

private theorem packedReviewerWholeStateNatFields_length_le
    (state : PackedReviewerWholeState) :
    (packedReviewerWholeStateNatFields state).length <=
      40 + 6 * packedReviewerWholeStateContinuationDepth state := by
  cases state with
  | leftSelect n left right select =>
      have hselect :=
        packedReviewerSelectStateNatFields_length_le_thirty_two select
      simp [packedReviewerWholeStateNatFields,
        packedReviewerWholeStateContinuationDepth] at *
      omega
  | rightSelect n left right leftClose select =>
      have hleft := packedReviewerOptionNatFields_length_le_one leftClose
      have hselect :=
        packedReviewerSelectStateNatFields_length_le_thirty_two select
      simp [packedReviewerWholeStateNatFields,
        packedReviewerWholeStateContinuationDepth] at *
      omega
  | lcaClose n left right leftClose rightClose lca =>
      have hlca := packedReviewerLcaStateNatFields_length_le lca
      simp [packedReviewerWholeStateNatFields,
        packedReviewerWholeStateContinuationDepth] at *
      omega
  | finalRank n left right answerClose rank =>
      have hrank := packedReviewerRankStateNatFields_length_le_eight rank
      simp [packedReviewerWholeStateNatFields,
        packedReviewerWholeStateContinuationDepth] at *
      omega
  | done value =>
      have hvalue := packedReviewerOptionNatFields_length_le_one value
      simp [packedReviewerWholeStateNatFields,
        packedReviewerWholeStateContinuationDepth] at *
      omega

private theorem packedReviewerSparsePreludeStateNatFields_length_le_three
    (state : PackedReviewerSparsePreludeState) :
    (packedReviewerSparsePreludeStateNatFields state).length <= 3 := by
  cases state <;> simp [packedReviewerSparsePreludeStateNatFields]

/--
The scalar inventory is structurally small once an operational proof supplies
the continuation-depth bound.  No reachability or arbitrary-depth assertion is
hidden in this lemma.
-/
theorem packedReviewerControllerStateNatFields_length_le_of_depth
    (state : PackedReviewerControllerState)
    (hdepth : packedReviewerControllerStateContinuationDepth state <= 3) :
    (packedReviewerControllerStateNatFields state).length <= 512 := by
  cases state with
  | header n left right =>
      simp [packedReviewerControllerStateNatFields]
  | preludeReady n left right longCount prelude =>
      have hprelude :=
        packedReviewerSparsePreludeStateNatFields_length_le_three prelude
      simp [packedReviewerControllerStateNatFields] at *
      omega
  | preludeProbe n left right longCount prelude nextOrdinal repliesRev =>
      have hprelude :=
        packedReviewerSparsePreludeStateNatFields_length_le_three prelude
      simp [packedReviewerControllerStateNatFields] at *
      omega
  | wholeReady n left right longCount sparseCount logicalStepsLeft whole =>
      have hwhole := packedReviewerWholeStateNatFields_length_le whole
      simp [packedReviewerControllerStateNatFields,
        packedReviewerControllerStateContinuationDepth] at *
      omega
  | wholeProbe n left right longCount sparseCount logicalStepsAfterReply whole
      nextOrdinal repliesRev =>
      have hwhole := packedReviewerWholeStateNatFields_length_le whole
      simp [packedReviewerControllerStateNatFields,
        packedReviewerControllerStateContinuationDepth] at *
      omega
  | done value =>
      have hvalue := packedReviewerOptionNatFields_length_le_one value
      simp [packedReviewerControllerStateNatFields] at *
      omega
  | failed =>
      simp [packedReviewerControllerStateNatFields]

/-! ## Structural word- and wide-buffer cardinalities -/

private theorem packedReviewerFilterMapId_length_le
    (replies : List (Option (List Bool))) :
    (replies.filterMap id).length <= replies.length := by
  induction replies with
  | nil => simp
  | cons reply replies ih =>
      cases reply with
      | none =>
          simp
          omega
      | some word =>
          simpa using ih

private theorem packedReviewerRankStateWordFields_length_le_one
    (state : PackedReviewerRankState) :
    (packedReviewerRankStateWordFields state).length <= 1 := by
  cases state <;> simp [packedReviewerRankStateWordFields]

private theorem packedReviewerWordSelectStateWordFields_length_le_one
    (state : PackedReviewerWordSelectState) :
    (packedReviewerWordSelectStateWordFields state).length <= 1 := by
  cases state <;> simp [packedReviewerWordSelectStateWordFields]

private theorem packedReviewerBPWindowStateWordFields_length_le_four
    (state : PackedReviewerBPWindowState)
    (hcontrol : packedReviewerBPWindowStateControlBounds state) :
    (packedReviewerBPWindowStateWordFields state).length <= 4 := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      simp [packedReviewerBPWindowStateControlBounds,
        packedReviewerBPWindowStateWordFields] at *
      omega
  | done bits =>
      simp [packedReviewerBPWindowStateWordFields]

private theorem packedReviewerInteriorNatStateWordFields_length_le_two_ten
    (state : PackedReviewerInteriorNatState)
    (hcontrol : packedReviewerInteriorNatStateControlBounds state) :
    (packedReviewerInteriorNatStateWordFields state).length <= 210 := by
  cases state with
  | read invocation n start next remaining repliesRev =>
      have hfilter := packedReviewerFilterMapId_length_le repliesRev
      simp [packedReviewerInteriorNatStateControlBounds,
        packedReviewerInteriorNatStateWordFields] at *
      omega
  | done value =>
      simp [packedReviewerInteriorNatStateWordFields]

private theorem packedReviewerInteriorStateWordFields_length_le_two_ten
    (state : PackedReviewerInteriorState)
    (hcontrol : packedReviewerInteriorStateControlBounds state) :
    (packedReviewerInteriorStateWordFields state).length <= 210 := by
  cases state with
  | readNat invocation read continuation =>
      exact
        packedReviewerInteriorNatStateWordFields_length_le_two_ten read hcontrol
  | done value =>
      simp [packedReviewerInteriorStateWordFields]

private theorem packedReviewerSelectStateWordFields_length_le_two
    (state : PackedReviewerSelectState)
    (hcontrol : packedReviewerSelectStateControlBounds state) :
    (packedReviewerSelectStateWordFields state).length <= 2 := by
  cases state with
  | longRank invocation n index super rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerSelectStateWordFields]
      omega
  | sparseRank invocation n index localSlot super loc rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerSelectStateWordFields]
      omega
  | denseBeforeRank invocation n index basePosition baseOccurrence word rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerSelectStateWordFields] at *
      omega
  | denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerSelectStateWordFields] at *
      omega
  | denseFirstSelect invocation n baseWord select =>
      have hselect :=
        packedReviewerWordSelectStateWordFields_length_le_one select
      simp [packedReviewerSelectStateWordFields]
      omega
  | denseSecondSelect invocation n baseWord select =>
      have hselect :=
        packedReviewerWordSelectStateWordFields_length_le_one select
      simp [packedReviewerSelectStateWordFields]
      omega
  | _ => simp [packedReviewerSelectStateWordFields]

private theorem packedReviewerLcaStateWordFields_length_le_two_ten
    (state : PackedReviewerLcaState)
    (hcontrol : packedReviewerLcaStateControlBounds state) :
    (packedReviewerLcaStateWordFields state).length <= 210 := by
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerLcaStateWordFields]
      omega
  | sameWindow invocation n leftClose rightClose seed window =>
      have hwindow :=
        packedReviewerBPWindowStateWordFields_length_le_four window hcontrol
      simp [packedReviewerLcaStateWordFields] at *
      omega
  | leftSeed invocation n leftClose rightClose rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerLcaStateWordFields]
      omega
  | leftWindow invocation n leftClose rightClose seed window =>
      have hwindow :=
        packedReviewerBPWindowStateWordFields_length_le_four window hcontrol
      simp [packedReviewerLcaStateWordFields] at *
      omega
  | middle invocation n leftClose rightClose left interior =>
      exact
        packedReviewerInteriorStateWordFields_length_le_two_ten interior hcontrol
  | rightSeed invocation n leftClose rightClose left middle rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerLcaStateWordFields]
      omega
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      have hwindow :=
        packedReviewerBPWindowStateWordFields_length_le_four window hcontrol
      simp [packedReviewerLcaStateWordFields] at *
      omega
  | _ => simp [packedReviewerLcaStateWordFields]

private theorem packedReviewerWholeStateWordFields_length_le_two_ten
    (state : PackedReviewerWholeState)
    (hcontrol : packedReviewerWholeStateControlBounds state) :
    (packedReviewerWholeStateWordFields state).length <= 210 := by
  cases state with
  | leftSelect n left right select =>
      have hselect :=
        packedReviewerSelectStateWordFields_length_le_two select hcontrol
      simp [packedReviewerWholeStateWordFields] at *
      omega
  | rightSelect n left right leftClose select =>
      have hselect :=
        packedReviewerSelectStateWordFields_length_le_two select hcontrol
      simp [packedReviewerWholeStateWordFields] at *
      omega
  | lcaClose n left right leftClose rightClose lca =>
      exact packedReviewerLcaStateWordFields_length_le_two_ten lca hcontrol
  | finalRank n left right answerClose rank =>
      have hrank := packedReviewerRankStateWordFields_length_le_one rank
      simp [packedReviewerWholeStateWordFields] at *
      omega
  | done value =>
      simp [packedReviewerWholeStateWordFields]

private theorem packedReviewerSparsePreludeStateWordFields_length_le_two
    (state : PackedReviewerSparsePreludeState) :
    (packedReviewerSparsePreludeStateWordFields state).length <= 2 := by
  cases state <;> simp [packedReviewerSparsePreludeStateWordFields]

/-- The literal 212-word envelope follows from the separate control bounds. -/
theorem packedReviewerControllerStateWordFields_length_le_of_control
    (state : PackedReviewerControllerState)
    (hcontrol : packedReviewerControllerStateControlBounds state) :
    (packedReviewerControllerStateWordFields state).length <= 212 := by
  cases state with
  | header n left right =>
      simp [packedReviewerControllerStateWordFields]
  | preludeReady n left right longCount prelude =>
      have hprelude :=
        packedReviewerSparsePreludeStateWordFields_length_le_two prelude
      simp [packedReviewerControllerStateWordFields] at *
      omega
  | preludeProbe n left right longCount prelude nextOrdinal repliesRev =>
      have hprelude :=
        packedReviewerSparsePreludeStateWordFields_length_le_two prelude
      simp [packedReviewerControllerStateControlBounds,
        packedReviewerControllerStateWordFields] at *
      omega
  | wholeReady n left right longCount sparseCount logicalStepsLeft whole =>
      have hwhole :=
        packedReviewerWholeStateWordFields_length_le_two_ten whole hcontrol.2.2
      simp [packedReviewerControllerStateWordFields] at *
      omega
  | wholeProbe n left right longCount sparseCount logicalStepsAfterReply whole
      nextOrdinal repliesRev =>
      have hwhole :=
        packedReviewerWholeStateWordFields_length_le_two_ten whole
          hcontrol.2.2.2.2
      simp [packedReviewerControllerStateControlBounds,
        packedReviewerControllerStateWordFields] at *
      omega
  | done value =>
      simp [packedReviewerControllerStateWordFields]
  | failed =>
      simp [packedReviewerControllerStateWordFields]

private theorem packedReviewerFringeStateWideFields_length_le_one
    (state : PackedReviewerFringeState) :
    (packedReviewerFringeStateWideFields state).length <= 1 := by
  cases state <;> simp [packedReviewerFringeStateWideFields]

private theorem packedReviewerBPWindowStateWideFields_length_le_one
    (state : PackedReviewerBPWindowState) :
    (packedReviewerBPWindowStateWideFields state).length <= 1 := by
  cases state <;> simp [packedReviewerBPWindowStateWideFields]

private theorem packedReviewerLcaStateWideFields_length_le_one
    (state : PackedReviewerLcaState) :
    (packedReviewerLcaStateWideFields state).length <= 1 := by
  cases state with
  | sameWindow invocation n leftClose rightClose seed window =>
      exact packedReviewerBPWindowStateWideFields_length_le_one window
  | leftWindow invocation n leftClose rightClose seed window =>
      exact packedReviewerBPWindowStateWideFields_length_le_one window
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      exact packedReviewerBPWindowStateWideFields_length_le_one window
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      exact packedReviewerFringeStateWideFields_length_le_one fringe
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      exact packedReviewerFringeStateWideFields_length_le_one fringe
  | rightFringe invocation n leftClose rightClose seed base start left middle
      fringe =>
      exact packedReviewerFringeStateWideFields_length_le_one fringe
  | _ => simp [packedReviewerLcaStateWideFields]

private theorem packedReviewerWholeStateWideFields_length_le_one
    (state : PackedReviewerWholeState) :
    (packedReviewerWholeStateWideFields state).length <= 1 := by
  cases state with
  | lcaClose n left right leftClose rightClose lca =>
      exact packedReviewerLcaStateWideFields_length_le_one lca
  | _ => simp [packedReviewerWholeStateWideFields]

/-- Wide BP data is represented by at most one explicit four-word buffer. -/
theorem packedReviewerControllerStateWideFields_length_le_one
    (state : PackedReviewerControllerState) :
    (packedReviewerControllerStateWideFields state).length <= 1 := by
  cases state with
  | wholeReady n left right longCount sparseCount logicalStepsLeft whole =>
      exact packedReviewerWholeStateWideFields_length_le_one whole
  | wholeProbe n left right longCount sparseCount logicalStepsAfterReply whole
      nextOrdinal repliesRev =>
      exact packedReviewerWholeStateWideFields_length_le_one whole
  | _ => simp [packedReviewerControllerStateWideFields]

/-! ## The operational core of the fixed-state envelope -/

/--
Only these five facts depend on operational reachability.  Phase fit and all
three inventory cardinalities are structural consequences proved above.
-/
private structure PackedReviewerControllerStateCoreFits
    (n : Nat) (state : PackedReviewerControllerState) : Prop where
  scalar_fields :
    forall value, value ∈ packedReviewerControllerStateNatFields state ->
      PackedReviewerNatFits n value
  word_fields :
    forall word, word ∈ packedReviewerControllerStateWordFields state ->
      PackedReviewerWordFits n word
  wide_fields :
    forall bits, bits ∈ packedReviewerControllerStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth n
  continuation_depth :
    packedReviewerControllerStateContinuationDepth state <= 3
  control_fields : packedReviewerControllerStateControlBounds state

/-- Assemble the imported exhaustive envelope from its operational core. -/
private theorem packedReviewerControllerStateMachineFits_of_core
    {n : Nat} {state : PackedReviewerControllerState}
    (hcore : PackedReviewerControllerStateCoreFits n state) :
    PackedReviewerControllerStateMachineFits n state := by
  refine
    { phase_tag := packedReviewerControllerStatePhaseCode_fits n state
      scalar_register_count :=
        packedReviewerControllerStateNatFields_length_le_of_depth state
          hcore.continuation_depth
      scalar_fields := hcore.scalar_fields
      word_buffer := ?_
      wide_buffer_count :=
        packedReviewerControllerStateWideFields_length_le_one state
      wide_fields := hcore.wide_fields
      continuation_depth := hcore.continuation_depth
      control_fields := hcore.control_fields }
  exact ⟨packedReviewerControllerStateWordFields_length_le_of_control state
      hcore.control_fields, hcore.word_fields⟩

/-! ## Reusable scalar-width consequences -/

private theorem packedReviewerNatFits_of_le_input
    (n value : Nat) (hvalue : value <= n) :
    PackedReviewerNatFits n value := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth n
  omega

private theorem packedReviewerNatFits_of_le_two_mul_add_one
    (n value : Nat) (hvalue : value <= 2 * n + 1) :
    PackedReviewerNatFits n value := by
  have hbound := packedTwoMul_le_reviewerBound n
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

private theorem packedReviewerCellWidth_lt_two_pow (n : Nat) :
    packedReviewerCellWidth n < 2 ^ packedReviewerCellWidth n := by
  have hpositive : 0 < packedReviewerCellBound n + 2 := by omega
  have hwidthBound :
      packedReviewerCellWidth n <= packedReviewerCellBound n + 2 := by
    exact GenericSelect.machineWordBits_le_self_of_pos hpositive
  have hcapacity := packedReviewerCellBound_lt_two_pow_width n
  omega

private theorem PackedReviewerWordFits.length_fits
    {n : Nat} {word : List Bool} (hword : PackedReviewerWordFits n word) :
    PackedReviewerNatFits n word.length := by
  have hcapacity := packedReviewerCellWidth_lt_two_pow n
  exact Nat.lt_of_le_of_lt hword hcapacity

private theorem packedReviewerDecodeNat_fits
    {n : Nat} {reply : Option (List Bool)}
    (hreply : forall word, reply = some word -> PackedReviewerWordFits n word) :
    forall value, packedReviewerDecodeNat reply = some value ->
      PackedReviewerNatFits n value := by
  intro value hvalue
  cases reply with
  | none => simp [packedReviewerDecodeNat] at hvalue
  | some word =>
      have hword := hreply word rfl
      have hdecoded := hword.value_lt_two_pow
      have heq : SuccinctSpace.bitsToNatLE word = value := by
        simpa [packedReviewerDecodeNat] using hvalue
      rw [← heq]
      exact hdecoded

/-! ## Scalar preservation for the four-field entry leaf -/

private theorem packedReviewerInvocationNatFields_fit
    {n : Nat} {invocation : PackedReviewerInvocation}
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits n operand) :
    forall value, value ∈ packedReviewerInvocationNatFields invocation ->
      PackedReviewerNatFits n value := by
  simpa [packedReviewerInvocationNatFields,
    packedReviewerInvocationOperands] using hinvocation

/-- The entry start stores exactly its bounded invocation and table index. -/
private theorem packedReviewerEntryStart_scalar_fits
    {n : Nat} (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerEntryKind) (index : Nat)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits n operand)
    (hindex : PackedReviewerNatFits n index) :
    forall value,
      value ∈ packedReviewerEntryStateNatFields
        (.baseOccurrence invocation kind index) ->
      PackedReviewerNatFits n value := by
  intro value hmem
  simp only [packedReviewerEntryStateNatFields, List.mem_append,
    List.mem_singleton] at hmem
  rcases hmem with hinvocationField | rfl
  · exact packedReviewerInvocationNatFields_fit hinvocation value
      hinvocationField
  · exact hindex

/--
One entry reply only appends its decoded scalar; when the fourth field closes
the entry, every retained record field came from one of those four decoded
options.  This subset lemma records that fact independently of word width.
-/
private theorem packedReviewerEntryConsumeReply_natFields_subset
    (state : PackedReviewerEntryState) (reply : Option (List Bool)) :
    forall value,
      value ∈ packedReviewerEntryStateNatFields
          (packedReviewerEntryConsumeReply state reply) ->
        value ∈ packedReviewerEntryStateNatFields state ∨
          packedReviewerDecodeNat reply = some value := by
  cases state with
  | baseOccurrence invocation kind index =>
      cases hdecoded : packedReviewerDecodeNat reply <;>
        simp [packedReviewerEntryConsumeReply,
          packedReviewerEntryStateNatFields,
          packedReviewerOptionNatFields, hdecoded, eq_comm, or_assoc]
  | baseWordIndex invocation kind index baseOccurrence =>
      cases baseOccurrence <;>
        cases hdecoded : packedReviewerDecodeNat reply <;>
        simp [packedReviewerEntryConsumeReply,
          packedReviewerEntryStateNatFields,
          packedReviewerOptionNatFields, hdecoded, eq_comm, or_assoc]
  | rankBefore invocation kind index baseOccurrence baseWordIndex =>
      cases baseOccurrence <;> cases baseWordIndex <;>
        cases hdecoded : packedReviewerDecodeNat reply <;>
        simp [packedReviewerEntryConsumeReply,
          packedReviewerEntryStateNatFields,
          packedReviewerOptionNatFields, hdecoded, eq_comm, or_assoc]
  | firstOffset invocation kind index baseOccurrence baseWordIndex rankBefore =>
      cases baseOccurrence <;> cases baseWordIndex <;> cases rankBefore <;>
        cases hdecoded : packedReviewerDecodeNat reply <;>
        simp [packedReviewerEntryConsumeReply,
          packedReviewerEntryStateNatFields,
          packedReviewerEntryValueNatFields,
          packedReviewerOptionNatFields,
          GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields,
          hdecoded, eq_comm, or_assoc] <;>
        (intro value hmem; exact Or.inr (Or.inr hmem))
  | done result =>
      intro value hmem
      exact Or.inl (by
        simpa [packedReviewerEntryConsumeReply] using hmem)

/-- Entry scalar width is preserved by every canonical one-word reply. -/
private theorem packedReviewerEntryConsumeReply_scalar_fits
    {n : Nat} {state : PackedReviewerEntryState}
    {reply : Option (List Bool)}
    (hstate :
      forall value, value ∈ packedReviewerEntryStateNatFields state ->
        PackedReviewerNatFits n value)
    (hreply :
      forall word, reply = some word -> PackedReviewerWordFits n word) :
    forall value,
      value ∈ packedReviewerEntryStateNatFields
        (packedReviewerEntryConsumeReply state reply) ->
      PackedReviewerNatFits n value := by
  intro value hmem
  rcases packedReviewerEntryConsumeReply_natFields_subset state reply value
      hmem with hold | hdecoded
  · exact hstate value hold
  · exact packedReviewerDecodeNat_fits hreply value hdecoded

/-! ### Exact canonical entry phases -/

private theorem packedReviewerDenseEntryTable_trace_value
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (index : Nat) :
    (table.readTraceResultRelabeled layout index).value = entries[index]? := by
  have hrefine :=
    table.readTraceResultRelabeled_refines_interpretedCosted layout index
  calc
    (table.readTraceResultRelabeled layout index).value =
        (table.readInterpretedCosted index).value := by
      simpa [WordRAM.TraceResult.toCosted] using
        congrArg Costed.value hrefine
    _ = entries[index]? := by
      simpa [Costed.erase] using table.readInterpretedCosted_erase index

private theorem packedReviewerCanonicalSuperTableWithStore_eq
    (shape : CartesianShape) (index : Nat) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).superTable.readTraceResultRelabeledWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout.superTable
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) index =
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).superTable.readTraceResultRelabeled
      concreteBPNativeSelectCloseTraceSegmentLayout.superTable index :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode
      false).superTable.readTraceResultRelabeledWithStore_eq_of_pullback
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseOccurrence
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superBaseWordIndex
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superRankBefore
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_superFirstOffset
      shape)
    index

private theorem packedReviewerCanonicalLocalTableWithStore_eq
    (shape : CartesianShape) (index : Nat) :
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).localTable.readTraceResultRelabeledWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout.localTable
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) index =
    (GenericSelect.sparseExceptionSelectData shape.bpCode
        false).localTable.readTraceResultRelabeled
      concreteBPNativeSelectCloseTraceSegmentLayout.localTable index :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode
      false).localTable.readTraceResultRelabeledWithStore_eq_of_pullback
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseOccurrence
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localBaseWordIndex
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localRankBefore
      shape)
    (concreteBPNativeSuccinctRMQGlobalReadStore_pullback_localFirstOffset
      shape)
    index

private theorem packedReviewerCanonicalEntryRead_value
    (shape : CartesianShape) (kind : PackedReviewerEntryKind) (index : Nat) :
    (packedSelectEntryRead
      (match kind with
      | .super => concreteBPNativeSelectCloseTraceSegmentLayout.superTable
      | .local => concreteBPNativeSelectCloseTraceSegmentLayout.localTable)
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) index).value =
    match kind with
    | .super => (GenericSelect.superEntries shape.bpCode false)[index]?
    | .local => (GenericSelect.localEntries shape.bpCode false)[index]? := by
  let data := GenericSelect.sparseExceptionSelectData shape.bpCode false
  cases kind with
  | super =>
      have hstore := packedReviewerCanonicalSuperTableWithStore_eq shape index
      have hvalue := packedReviewerDenseEntryTable_trace_value
        data.superTable
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable index
      rw [show packedSelectEntryRead
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) index =
          data.superTable.readTraceResultRelabeledWithStore
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) index by
        exact (packedSelectEntryRead_eq data.superTable
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) index).symm]
      rw [hstore]
      simpa [data, GenericSelect.sparseExceptionSelectData] using hvalue
  | «local» =>
      have hstore := packedReviewerCanonicalLocalTableWithStore_eq shape index
      have hvalue := packedReviewerDenseEntryTable_trace_value
        data.localTable
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable index
      rw [show packedSelectEntryRead
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) index =
          data.localTable.readTraceResultRelabeledWithStore
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) index by
        exact (packedSelectEntryRead_eq data.localTable
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) index).symm]
      rw [hstore]
      simpa [data, GenericSelect.sparseExceptionSelectData] using hvalue

private theorem packedReviewerCanonicalEntryOfFields_eq
    (shape : CartesianShape) (kind : PackedReviewerEntryKind) (index : Nat) :
    GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
      (packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          kind.segmentBase index))
      (packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (kind.segmentBase + 1) index))
      (packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (kind.segmentBase + 2) index))
      (packedReviewerDecodeNat
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (kind.segmentBase + 3) index)) =
    match kind with
    | .super => (GenericSelect.superEntries shape.bpCode false)[index]?
    | .local => (GenericSelect.localEntries shape.bpCode false)[index]? := by
  have hdecode : SuccinctSpace.bitsToNatLE = WordRAM.bitsToNatLE :=
    funext fun word =>
      (SuccinctSpace.WordRAMBridge.bitsToNatLE_eq word).symm
  have hvalue := packedReviewerCanonicalEntryRead_value shape kind index
  cases kind <;>
    simpa [packedSelectEntryRead, packedReviewerDecodeNat,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      WordRAM.TraceResult.bind_value, WordRAM.TraceResult.map_value,
      WordRAM.TraceResult.ofProgramWithStore,
      WordRAM.TraceResult.relabelReadSegmentsWith,
      WordRAM.TraceResult.ofResult, WordRAM.Program.evalR,
      WordRAM.ReadStore.pullback, WordRAM.singletonSegmentMap,
      PackedReviewerEntryKind.segmentBase, concreteBPNativeDeadTraceSegment,
      hdecode] using hvalue

/-- Exact one-of-five phase grammar for a four-field canonical entry read. -/
private inductive PackedReviewerCanonicalEntryState
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerEntryKind) (index : Nat) :
    PackedReviewerEntryState -> Prop where
  | baseOccurrence :
      PackedReviewerCanonicalEntryState shape invocation kind index
        (.baseOccurrence invocation kind index)
  | baseWordIndex :
      PackedReviewerCanonicalEntryState shape invocation kind index
        (.baseWordIndex invocation kind index
          (packedReviewerDecodeNat
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              kind.segmentBase index)))
  | rankBefore :
      PackedReviewerCanonicalEntryState shape invocation kind index
        (.rankBefore invocation kind index
          (packedReviewerDecodeNat
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              kind.segmentBase index))
          (packedReviewerDecodeNat
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              (kind.segmentBase + 1) index)))
  | firstOffset :
      PackedReviewerCanonicalEntryState shape invocation kind index
        (.firstOffset invocation kind index
          (packedReviewerDecodeNat
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              kind.segmentBase index))
          (packedReviewerDecodeNat
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              (kind.segmentBase + 1) index))
          (packedReviewerDecodeNat
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              (kind.segmentBase + 2) index)))
  | done :
      PackedReviewerCanonicalEntryState shape invocation kind index
        (.done
          (match kind with
          | .super => (GenericSelect.superEntries shape.bpCode false)[index]?
          | .local => (GenericSelect.localEntries shape.bpCode false)[index]?))

private theorem PackedReviewerCanonicalEntryState.consume
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {kind : PackedReviewerEntryKind} {index : Nat}
    {state : PackedReviewerEntryState}
    (hstate :
      PackedReviewerCanonicalEntryState shape invocation kind index state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerEntryNextRequest state = some request) :
    PackedReviewerCanonicalEntryState shape invocation kind index
      (packedReviewerEntryConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases hstate with
  | baseOccurrence =>
      have hrequestEq :
          request =
            { invocation := invocation
              site := .entryBaseOccurrence
              segment := kind.segmentBase
              index := index } := by
        simpa [packedReviewerEntryNextRequest] using hrequest.symm
      subst request
      simpa [packedReviewerEntryConsumeReply] using
        (PackedReviewerCanonicalEntryState.baseWordIndex
          (shape := shape) (invocation := invocation) (kind := kind)
          (index := index))
  | baseWordIndex =>
      have hrequestEq :
          request =
            { invocation := invocation
              site := .entryBaseWordIndex
              segment := kind.segmentBase + 1
              index := index } := by
        simpa [packedReviewerEntryNextRequest] using hrequest.symm
      subst request
      simpa [packedReviewerEntryConsumeReply] using
        (PackedReviewerCanonicalEntryState.rankBefore
          (shape := shape) (invocation := invocation) (kind := kind)
          (index := index))
  | rankBefore =>
      have hrequestEq :
          request =
            { invocation := invocation
              site := .entryRankBefore
              segment := kind.segmentBase + 2
              index := index } := by
        simpa [packedReviewerEntryNextRequest] using hrequest.symm
      subst request
      simpa [packedReviewerEntryConsumeReply] using
        (PackedReviewerCanonicalEntryState.firstOffset
          (shape := shape) (invocation := invocation) (kind := kind)
          (index := index))
  | firstOffset =>
      have hrequestEq :
          request =
            { invocation := invocation
              site := .entryFirstOffset
              segment := kind.segmentBase + 3
              index := index } := by
        simpa [packedReviewerEntryNextRequest] using hrequest.symm
      subst request
      simpa [packedReviewerEntryConsumeReply,
        packedReviewerCanonicalEntryOfFields_eq] using
        (PackedReviewerCanonicalEntryState.done
          (shape := shape) (invocation := invocation) (kind := kind)
          (index := index))
  | done =>
      simp [packedReviewerEntryNextRequest] at hrequest

private theorem PackedReviewerCanonicalEntryState.scalar_fields
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {kind : PackedReviewerEntryKind} {index : Nat}
    {state : PackedReviewerEntryState}
    (hstate :
      PackedReviewerCanonicalEntryState shape invocation kind index state)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : PackedReviewerNatFits shape.size index) :
    forall value, value ∈ packedReviewerEntryStateNatFields state ->
      PackedReviewerNatFits shape.size value := by
  have hstart := packedReviewerEntryStart_scalar_fits invocation kind index
    hinvocation hindex
  have hreply (request : PackedReviewerLogicalRequest) :
      forall word,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index = some word ->
          PackedReviewerWordFits shape.size word := by
    intro word hread
    exact packedReviewerGlobalReadStore_word_fits shape request word hread
  cases hstate with
  | baseOccurrence => exact hstart
  | baseWordIndex =>
      exact packedReviewerEntryConsumeReply_scalar_fits hstart
        (hreply
          { invocation := invocation
            site := .entryBaseOccurrence
            segment := kind.segmentBase
            index := index })
  | rankBefore =>
      have h1 := packedReviewerEntryConsumeReply_scalar_fits hstart
        (hreply
          { invocation := invocation
            site := .entryBaseOccurrence
            segment := kind.segmentBase
            index := index })
      exact packedReviewerEntryConsumeReply_scalar_fits h1
        (hreply
          { invocation := invocation
            site := .entryBaseWordIndex
            segment := kind.segmentBase + 1
            index := index })
  | firstOffset =>
      have h1 := packedReviewerEntryConsumeReply_scalar_fits hstart
        (hreply
          { invocation := invocation
            site := .entryBaseOccurrence
            segment := kind.segmentBase
            index := index })
      have h2 := packedReviewerEntryConsumeReply_scalar_fits h1
        (hreply
          { invocation := invocation
            site := .entryBaseWordIndex
            segment := kind.segmentBase + 1
            index := index })
      exact packedReviewerEntryConsumeReply_scalar_fits h2
        (hreply
          { invocation := invocation
            site := .entryRankBefore
            segment := kind.segmentBase + 2
            index := index })
  | done =>
      have h1 := packedReviewerEntryConsumeReply_scalar_fits hstart
        (hreply
          { invocation := invocation
            site := .entryBaseOccurrence
            segment := kind.segmentBase
            index := index })
      have h2 := packedReviewerEntryConsumeReply_scalar_fits h1
        (hreply
          { invocation := invocation
            site := .entryBaseWordIndex
            segment := kind.segmentBase + 1
            index := index })
      have h3 := packedReviewerEntryConsumeReply_scalar_fits h2
        (hreply
          { invocation := invocation
            site := .entryRankBefore
            segment := kind.segmentBase + 2
            index := index })
      simpa [packedReviewerEntryConsumeReply,
        packedReviewerCanonicalEntryOfFields_eq] using
        packedReviewerEntryConsumeReply_scalar_fits h3
          (hreply
            { invocation := invocation
              site := .entryFirstOffset
              segment := kind.segmentBase + 3
              index := index })

private theorem PackedReviewerCanonicalEntryState.result_eq
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {kind : PackedReviewerEntryKind} {index : Nat}
    {state : PackedReviewerEntryState}
    (hstate :
      PackedReviewerCanonicalEntryState shape invocation kind index state)
    {value : Option GenericSelect.SparseDenseSelectDenseLocalEntry}
    (hresult : packedReviewerEntryResult state = some value) :
    value =
      match kind with
      | .super => (GenericSelect.superEntries shape.bpCode false)[index]?
      | .local => (GenericSelect.localEntries shape.bpCode false)[index]? := by
  cases kind <;> cases hstate <;>
    simp [packedReviewerEntryResult] at hresult ⊢ <;>
    exact hresult.symm

private theorem PackedReviewerCanonicalEntryState.requests_fit
    {shape : CartesianShape} {invocation : PackedReviewerInvocation}
    {kind : PackedReviewerEntryKind} {index : Nat}
    {state : PackedReviewerEntryState}
    (hstate :
      PackedReviewerCanonicalEntryState shape invocation kind index state)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : PackedReviewerNatFits shape.size index) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerEntryNextRequest packedReviewerEntryConsumeReply
      (packedReviewerEntryRemaining state) state := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let s0 : PackedReviewerEntryState :=
    .baseOccurrence invocation kind index
  let q0 : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .entryBaseOccurrence
      segment := kind.segmentBase
      index := index }
  let s1 := packedReviewerEntryConsumeReply s0
    (store.readWord? q0.segment q0.index)
  let q1 : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .entryBaseWordIndex
      segment := kind.segmentBase + 1
      index := index }
  let s2 := packedReviewerEntryConsumeReply s1
    (store.readWord? q1.segment q1.index)
  let q2 : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .entryRankBefore
      segment := kind.segmentBase + 2
      index := index }
  let s3 := packedReviewerEntryConsumeReply s2
    (store.readWord? q2.segment q2.index)
  let q3 : PackedReviewerLogicalRequest :=
    { invocation := invocation
      site := .entryFirstOffset
      segment := kind.segmentBase + 3
      index := index }
  let s4 := packedReviewerEntryConsumeReply s3
    (store.readWord? q3.segment q3.index)
  have h0 :
      PackedReviewerRequestsFitFrom shape.size store
        packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 4 s0 := by
    simpa [store, s0] using
      packedReviewerEntryStart_requests_fit shape invocation kind index
        hinvocation hindex
  have hq0 : packedReviewerEntryNextRequest s0 = some q0 := by
    simp [s0, q0, packedReviewerEntryNextRequest]
  have h1 := (PackedReviewerRequestsFitFrom.step shape.size store
    packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 3 s0 q0
    h0 hq0).2
  have hq1 : packedReviewerEntryNextRequest s1 = some q1 := by
    simp [s1, s0, q0, q1, packedReviewerEntryConsumeReply,
      packedReviewerEntryNextRequest]
  have h2 := (PackedReviewerRequestsFitFrom.step shape.size store
    packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 2 s1 q1
    h1 hq1).2
  have hq2 : packedReviewerEntryNextRequest s2 = some q2 := by
    simp [s2, s1, s0, q0, q1, q2, packedReviewerEntryConsumeReply,
      packedReviewerEntryNextRequest]
  have h3 := (PackedReviewerRequestsFitFrom.step shape.size store
    packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 1 s2 q2
    h2 hq2).2
  have hq3 : packedReviewerEntryNextRequest s3 = some q3 := by
    simp [s3, s2, s1, s0, q0, q1, q2, q3,
      packedReviewerEntryConsumeReply, packedReviewerEntryNextRequest]
  have h4 := (PackedReviewerRequestsFitFrom.step shape.size store
    packedReviewerEntryNextRequest packedReviewerEntryConsumeReply 0 s3 q3
    h3 hq3).2
  cases hstate with
  | baseOccurrence => simpa [store, s0, packedReviewerEntryRemaining] using h0
  | baseWordIndex =>
      simpa [store, s1, s0, q0, packedReviewerEntryConsumeReply,
        packedReviewerEntryRemaining] using h1
  | rankBefore =>
      simpa [store, s2, s1, s0, q0, q1,
        packedReviewerEntryConsumeReply, packedReviewerEntryRemaining] using h2
  | firstOffset =>
      simpa [store, s3, s2, s1, s0, q0, q1, q2,
        packedReviewerEntryConsumeReply, packedReviewerEntryRemaining] using h3
  | done =>
      simpa [store, s4, s3, s2, s1, s0, q0, q1, q2, q3,
        packedReviewerEntryConsumeReply, packedReviewerEntryRemaining,
        packedReviewerCanonicalEntryOfFields_eq] using h4

private theorem packedReviewerSelectMachineWidth_le_cellWidth
    (shape : CartesianShape) :
    SuccinctRank.machineWordBits shape.bpCode.length <=
      packedReviewerCellWidth shape.size := by
  apply packedReviewerMachineWordBits_le_cellWidth
  rw [CartesianShape.bpCode_length]
  have htwo := packedTwoMul_le_reviewerBound shape.size
  omega

private theorem packedReviewerCanonicalEntryValue_scalar_fields
    (shape : CartesianShape) (kind : PackedReviewerEntryKind) (index : Nat)
    (entry : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hget :
      (match kind with
      | .super => (GenericSelect.superEntries shape.bpCode false)[index]?
      | .local => (GenericSelect.localEntries shape.bpCode false)[index]?) =
        some entry) :
    forall value,
      value ∈ packedReviewerEntryValueNatFields (some entry) ->
        PackedReviewerNatFits shape.size value := by
  have hmachine := packedReviewerSelectMachineWidth_le_cellWidth shape
  cases kind with
  | super =>
      let table := GenericSelect.superTable shape.bpCode false
      have hfields := table.entry_fields_lt hget
      have hwidth : GenericSelect.superFieldWidth shape.bpCode <=
          packedReviewerCellWidth shape.size := by
        simpa [GenericSelect.superFieldWidth, GenericSelect.wordBits] using
          hmachine
      have hpow : 2 ^ GenericSelect.superFieldWidth shape.bpCode <=
          2 ^ packedReviewerCellWidth shape.size :=
        Nat.pow_le_pow_right (by omega) hwidth
      intro value hmem
      simp [packedReviewerEntryValueNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Nat.lt_of_lt_of_le hfields.1 hpow
      · exact Nat.lt_of_lt_of_le hfields.2.1 hpow
      · exact Nat.lt_of_lt_of_le hfields.2.2.1 hpow
      · exact Nat.lt_of_lt_of_le hfields.2.2.2 hpow
  | «local» =>
      let table := GenericSelect.localTable shape.bpCode false
      have hfields := table.entry_fields_lt hget
      have hwidth : GenericSelect.localFieldWidth shape.bpCode <=
          packedReviewerCellWidth shape.size := by
        exact Nat.le_trans
          (GenericSelect.sparseExceptionRelativeWidth_le_machine shape.bpCode)
          hmachine
      have hpow : 2 ^ GenericSelect.localFieldWidth shape.bpCode <=
          2 ^ packedReviewerCellWidth shape.size :=
        Nat.pow_le_pow_right (by omega) hwidth
      intro value hmem
      simp [packedReviewerEntryValueNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact Nat.lt_of_lt_of_le hfields.1 hpow
      · exact Nat.lt_of_lt_of_le hfields.2.1 hpow
      · exact Nat.lt_of_lt_of_le hfields.2.2.1 hpow
      · exact Nat.lt_of_lt_of_le hfields.2.2.2 hpow

/-! ### Canonical select-entry geometry -/

private structure PackedReviewerCanonicalSuperGeometry
    (shape : CartesianShape) (index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry) : Prop where
  index_lt : index < shape.size
  get_eq :
    (GenericSelect.superEntries shape.bpCode false)[
      GenericSelect.selectSuperSlot index
        (packedSelectSuperStride shape.size)]? = some super

private theorem PackedReviewerCanonicalSuperGeometry.slot_fits
    {shape : CartesianShape} {index : Nat}
    {super : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalSuperGeometry shape index super) :
    PackedReviewerNatFits shape.size
      (GenericSelect.selectSuperSlot index
        (packedSelectSuperStride shape.size)) := by
  have hslotLe :
      GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) <= index := by
    unfold GenericSelect.selectSuperSlot
    exact Nat.div_le_self _ _
  exact Nat.lt_of_le_of_lt hslotLe
    (Nat.lt_trans h.index_lt
      (packedReviewerInputSize_lt_two_pow_cellWidth shape.size))

private theorem PackedReviewerCanonicalSuperGeometry.entry_eq
    {shape : CartesianShape} {index : Nat}
    {super : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalSuperGeometry shape index super) :
    super =
      GenericSelect.superEntry shape.bpCode false
        (GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size)) := by
  let slot := GenericSelect.selectSuperSlot index
    (packedSelectSuperStride shape.size)
  have hslot : slot < GenericSelect.superSlotCount shape.bpCode false := by
    have hlen := (List.getElem?_eq_some_iff.mp h.get_eq).1
    simpa [slot, GenericSelect.superEntries_length] using hlen
  have hbuilt := GenericSelect.superEntries_get? shape.bpCode false
    (superSlot := slot) hslot
  have hget := h.get_eq
  rw [hbuilt] at hget
  exact (Option.some.inj hget).symm

private theorem PackedReviewerCanonicalSuperGeometry.entry_scalar_fields
    {shape : CartesianShape} {index : Nat}
    {super : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalSuperGeometry shape index super) :
    forall value,
      value ∈ packedReviewerEntryValueNatFields (some super) ->
        PackedReviewerNatFits shape.size value := by
  apply packedReviewerCanonicalEntryValue_scalar_fields shape .super
    (GenericSelect.selectSuperSlot index
      (packedSelectSuperStride shape.size)) super
  exact h.get_eq

private theorem PackedReviewerCanonicalSuperGeometry.baseOccurrence_le
    {shape : CartesianShape} {index : Nat}
    {super : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalSuperGeometry shape index super) :
    super.baseOccurrence <= index := by
  rw [h.entry_eq]
  simp only [GenericSelect.superEntry, packedSelectSuperStride]
  simpa [GenericSelect.selectSuperSlot, CartesianShape.bpCode_length] using
    Nat.div_mul_le_self index (GenericSelect.superStride (2 * shape.size))

private theorem PackedReviewerCanonicalSuperGeometry.basePosition_eq
    {shape : CartesianShape} {index : Nat}
    {super : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalSuperGeometry shape index super) :
    GenericSelect.relativeSplitSelectEntryBasePosition
        (packedSelectWordSize shape.size) super =
      GenericSelect.position shape.bpCode false super.baseOccurrence := by
  rw [h.entry_eq]
  let slot := GenericSelect.selectSuperSlot index
    (packedSelectSuperStride shape.size)
  let baseOccurrence := slot * GenericSelect.superStride shape.bpCode.length
  let basePosition := GenericSelect.position shape.bpCode false baseOccurrence
  let wordSize := GenericSelect.wordBits shape.bpCode.length
  have hmod :
      basePosition / wordSize * wordSize +
          (basePosition - basePosition / wordSize * wordSize) =
        basePosition := by
    have hle := Nat.div_mul_le_self basePosition wordSize
    omega
  simpa [GenericSelect.relativeSplitSelectEntryBasePosition,
    GenericSelect.superEntry, packedSelectWordSize, packedSelectSuperStride,
    slot, baseOccurrence, basePosition, wordSize, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc, CartesianShape.bpCode_length] using hmod

private theorem PackedReviewerCanonicalSuperGeometry.basePosition_fits
    {shape : CartesianShape} {index : Nat}
    {super : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalSuperGeometry shape index super) :
    PackedReviewerNatFits shape.size
      (GenericSelect.relativeSplitSelectEntryBasePosition
        (packedSelectWordSize shape.size) super) := by
  rw [h.basePosition_eq]
  apply packedReviewerNatFits_of_le_two_mul_add_one
  have hposition := GenericSelect.position_le_length shape.bpCode false
    super.baseOccurrence
  have hlength : shape.bpCode.length <= 2 * shape.size + 1 := by
    simp [CartesianShape.bpCode_length]
  exact Nat.le_trans hposition hlength

private structure PackedReviewerCanonicalLocalGeometry
    (shape : CartesianShape) (index : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry) : Prop where
  super_geometry : PackedReviewerCanonicalSuperGeometry shape index super
  super_short : GenericSelect.relativeSplitSelectEntryIsMarked super = false
  get_eq :
    (GenericSelect.localEntries shape.bpCode false)[
      GenericSelect.relativeSplitSelectLocalSlot index
        (packedSelectSuperStride shape.size)
        (packedSelectLocalSlotsPerSuper shape.size)
        (packedSelectLocalStride shape.size) super]? = some loc

private theorem PackedReviewerCanonicalLocalGeometry.facts
    {shape : CartesianShape} {index : Nat}
    {super loc : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalLocalGeometry shape index super loc) :
    let localSlot :=
      GenericSelect.relativeSplitSelectLocalSlot index
        (packedSelectSuperStride shape.size)
        (packedSelectLocalSlotsPerSuper shape.size)
        (packedSelectLocalStride shape.size) super
    localSlot < GenericSelect.localSlotCount shape.bpCode false /\
      localSlot <
        GenericSelect.sparseExceptionEffectiveLocalSlotCount
          shape.bpCode false /\
      GenericSelect.compactLocalEntryIsLive shape.bpCode false localSlot = true /\
      GenericSelect.localSuperSlot shape.bpCode.length localSlot =
        GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) /\
      GenericSelect.localBaseOccurrence shape.bpCode.length localSlot <=
        index := by
  have hvalid :
      index < GenericSelect.occurrenceCount shape.bpCode false := by
    simpa [packedSelectOccurrenceCount_eq_size shape] using
      h.super_geometry.index_lt
  have hsuperGet :
      (GenericSelect.superEntries shape.bpCode false)[
        GenericSelect.selectSuperSlot index
          (GenericSelect.superStride shape.bpCode.length)]? = some super := by
    simpa [packedSelectSuperStride, CartesianShape.bpCode_length] using
      h.super_geometry.get_eq
  have hfacts := GenericSelect.localSlot_facts shape.bpCode false index super
    hsuperGet hvalid h.super_short
  simpa [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
    packedSelectLocalStride, CartesianShape.bpCode_length] using
    And.intro hfacts.1
      (And.intro hfacts.2.1
        (And.intro hfacts.2.2.1
          (And.intro hfacts.2.2.2.1 hfacts.2.2.2.2.1)))

private theorem PackedReviewerCanonicalLocalGeometry.entry_eq
    {shape : CartesianShape} {index : Nat}
    {super loc : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalLocalGeometry shape index super loc) :
    let localSlot :=
      GenericSelect.relativeSplitSelectLocalSlot index
        (packedSelectSuperStride shape.size)
        (packedSelectLocalSlotsPerSuper shape.size)
        (packedSelectLocalStride shape.size) super
    loc = GenericSelect.localEntry shape.bpCode false localSlot := by
  let localSlot :=
    GenericSelect.relativeSplitSelectLocalSlot index
      (packedSelectSuperStride shape.size)
      (packedSelectLocalSlotsPerSuper shape.size)
      (packedSelectLocalStride shape.size) super
  have hslot := h.facts.1
  have hbuilt := GenericSelect.localEntries_get? shape.bpCode false
    (globalLocalSlot := localSlot) hslot
  have hget := h.get_eq
  rw [hbuilt] at hget
  exact (Option.some.inj hget).symm

private theorem PackedReviewerCanonicalLocalGeometry.entry_scalar_fields
    {shape : CartesianShape} {index : Nat}
    {super loc : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalLocalGeometry shape index super loc) :
    forall value,
      value ∈ packedReviewerEntryValueNatFields (some loc) ->
        PackedReviewerNatFits shape.size value := by
  apply packedReviewerCanonicalEntryValue_scalar_fields shape .local
    (GenericSelect.relativeSplitSelectLocalSlot index
      (packedSelectSuperStride shape.size)
      (packedSelectLocalSlotsPerSuper shape.size)
      (packedSelectLocalStride shape.size) super) loc
  exact h.get_eq

private theorem PackedReviewerCanonicalLocalGeometry.localSlot_fits
    {shape : CartesianShape} {index : Nat}
    {super loc : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalLocalGeometry shape index super loc) :
    PackedReviewerNatFits shape.size
      (GenericSelect.relativeSplitSelectLocalSlot index
        (packedSelectSuperStride shape.size)
        (packedSelectLocalSlotsPerSuper shape.size)
        (packedSelectLocalStride shape.size) super) := by
  have heffective := h.facts.2.1
  unfold GenericSelect.sparseExceptionEffectiveLocalSlotCount at heffective
  have hcount :
      GenericSelect.occurrenceCount shape.bpCode false = shape.size :=
    packedSelectOccurrenceCount_eq_size shape
  have hltCount :
      GenericSelect.relativeSplitSelectLocalSlot index
          (packedSelectSuperStride shape.size)
          (packedSelectLocalSlotsPerSuper shape.size)
          (packedSelectLocalStride shape.size) super <
        GenericSelect.occurrenceCount shape.bpCode false :=
    (Nat.lt_min.mp heffective).2
  rw [hcount] at hltCount
  exact packedReviewerNatFits_of_le_input shape.size _
    (Nat.le_of_lt hltCount)

private theorem PackedReviewerCanonicalLocalGeometry.baseOccurrence_eq
    {shape : CartesianShape} {index : Nat}
    {super loc : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalLocalGeometry shape index super loc) :
    let localSlot :=
      GenericSelect.relativeSplitSelectLocalSlot index
        (packedSelectSuperStride shape.size)
        (packedSelectLocalSlotsPerSuper shape.size)
        (packedSelectLocalStride shape.size) super
    GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc =
      GenericSelect.localBaseOccurrence shape.bpCode.length localSlot := by
  let localSlot :=
    GenericSelect.relativeSplitSelectLocalSlot index
      (packedSelectSuperStride shape.size)
      (packedSelectLocalSlotsPerSuper shape.size)
      (packedSelectLocalStride shape.size) super
  change
    GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc =
      GenericSelect.localBaseOccurrence shape.bpCode.length localSlot
  have hsuperEq := h.super_geometry.entry_eq
  have hlocEq :
      loc = GenericSelect.localEntry shape.bpCode false localSlot := by
    simpa [localSlot] using h.entry_eq
  have hsame :
      GenericSelect.localSuperSlot shape.bpCode.length localSlot =
        GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) := by
    simpa [localSlot] using h.facts.2.2.2.1
  have hlive :
      GenericSelect.compactLocalEntryIsLive shape.bpCode false localSlot =
        true := by
    simpa [localSlot] using h.facts.2.2.1
  have hsame' :
      localSlot / GenericSelect.localSlotsPerSuper shape.bpCode.length =
        GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) := by
    simpa [GenericSelect.localSuperSlot] using hsame
  rw [hlocEq, hsuperEq]
  have hexact := GenericSelect.localBaseOccurrence_exact shape.bpCode false
    localSlot hlive
  rw [hsame'] at hexact
  simpa [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
    CartesianShape.bpCode_length, GenericSelect.localSuperSlot] using hexact

private theorem PackedReviewerCanonicalLocalGeometry.basePosition_eq
    {shape : CartesianShape} {index : Nat}
    {super loc : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalLocalGeometry shape index super loc) :
    let localSlot :=
      GenericSelect.relativeSplitSelectLocalSlot index
        (packedSelectSuperStride shape.size)
        (packedSelectLocalSlotsPerSuper shape.size)
        (packedSelectLocalStride shape.size) super
    GenericSelect.relativeSplitSelectLocalBasePosition
        (packedSelectWordSize shape.size) super loc =
      GenericSelect.position shape.bpCode false
        (GenericSelect.localBaseOccurrence shape.bpCode.length localSlot) := by
  let localSlot :=
    GenericSelect.relativeSplitSelectLocalSlot index
      (packedSelectSuperStride shape.size)
      (packedSelectLocalSlotsPerSuper shape.size)
      (packedSelectLocalStride shape.size) super
  change
    GenericSelect.relativeSplitSelectLocalBasePosition
        (packedSelectWordSize shape.size) super loc =
      GenericSelect.position shape.bpCode false
        (GenericSelect.localBaseOccurrence shape.bpCode.length localSlot)
  have hsuperEq := h.super_geometry.entry_eq
  have hlocEq :
      loc = GenericSelect.localEntry shape.bpCode false localSlot := by
    simpa [localSlot] using h.entry_eq
  have hsame :
      GenericSelect.localSuperSlot shape.bpCode.length localSlot =
        GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) := by
    simpa [localSlot] using h.facts.2.2.2.1
  have hlive :
      GenericSelect.compactLocalEntryIsLive shape.bpCode false localSlot =
        true := by
    simpa [localSlot] using h.facts.2.2.1
  have hsame' :
      localSlot / GenericSelect.localSlotsPerSuper shape.bpCode.length =
        GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) := by
    simpa [GenericSelect.localSuperSlot] using hsame
  rw [hlocEq, hsuperEq]
  have hexact := GenericSelect.localBasePosition_exact shape.bpCode false
    localSlot hlive
  rw [hsame'] at hexact
  simpa [packedSelectWordSize, packedSelectSuperStride,
    packedSelectLocalSlotsPerSuper, CartesianShape.bpCode_length,
    GenericSelect.localSuperSlot] using hexact

private theorem PackedReviewerCanonicalLocalGeometry.base_fields_fit
    {shape : CartesianShape} {index : Nat}
    {super loc : GenericSelect.SparseDenseSelectDenseLocalEntry}
    (h : PackedReviewerCanonicalLocalGeometry shape index super loc) :
    PackedReviewerNatFits shape.size
        (GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc) /\
      PackedReviewerNatFits shape.size
        (GenericSelect.relativeSplitSelectLocalBasePosition
          (packedSelectWordSize shape.size) super loc) := by
  constructor
  · rw [h.baseOccurrence_eq]
    apply packedReviewerNatFits_of_le_input
    exact Nat.le_trans (h.facts).2.2.2.2
      (Nat.le_of_lt h.super_geometry.index_lt)
  · rw [h.basePosition_eq]
    apply packedReviewerNatFits_of_le_two_mul_add_one
    have hposition := GenericSelect.position_le_length shape.bpCode false
      (GenericSelect.localBaseOccurrence shape.bpCode.length
        (GenericSelect.relativeSplitSelectLocalSlot index
          (packedSelectSuperStride shape.size)
          (packedSelectLocalSlotsPerSuper shape.size)
          (packedSelectLocalStride shape.size) super))
    have hlength : shape.bpCode.length <= 2 * shape.size + 1 := by
      simp [CartesianShape.bpCode_length]
    exact Nat.le_trans hposition hlength

/-! ## Exact physical reply-prefix contract -/

/-- Fetching a successful prefix and one successful final cell composes. -/
private theorem packedFetch_append_singleton_of_some
    (memory : List (List Bool)) (addressPrefix : List Nat)
    (address : Nat) (cells : List (List Bool)) (cell : List Bool)
    (hprefix : packedFetch memory addressPrefix = some cells)
    (hcell : packedProbeCell memory address = some cell) :
    packedFetch memory (addressPrefix ++ [address]) =
      some (cells ++ [cell]) := by
  induction addressPrefix generalizing cells with
  | nil =>
      simp [packedFetch] at hprefix
      subst cells
      simp [packedFetch, hcell]
  | cons head tail ih =>
      cases hhead : packedProbeCell memory head with
      | none => simp [packedFetch, hhead] at hprefix
      | some headCell =>
          cases htail : packedFetch memory tail with
          | none => simp [packedFetch, hhead, htail] at hprefix
          | some tailCells =>
              have hcells : cells = headCell :: tailCells := by
                simpa [packedFetch, hhead, htail] using hprefix.symm
              subst cells
              simp [packedFetch, hhead, ih tailCells htail]

/--
An in-flight physical plan prefix.  `consumed` and `rest` retain the exact
ordered decomposition, while `cells` is the successful canonical-memory fetch
of `consumed`.  The executable controller stores that same list in reverse
order, exactly as pinned by `replies_eq`.
-/
private structure PackedReviewerProbePrefix
    (memory : List (List Bool)) (plan : List Nat)
    (next : Nat) (repliesRev : List (List Bool)) where
  consumed : List Nat
  rest : List Nat
  cells : List (List Bool)
  plan_eq : plan = consumed ++ rest
  next_eq : next = consumed.length
  replies_eq : repliesRev.reverse = cells
  fetch_eq : packedFetch memory consumed = some cells

private def packedReviewerProbePrefix_zero
    (memory : List (List Bool)) (plan : List Nat) :
    PackedReviewerProbePrefix memory plan 0 [] := by
  exact
    { consumed := []
      rest := plan
      cells := []
      plan_eq := by simp
      next_eq := by simp
      replies_eq := by simp
      fetch_eq := by simp [packedFetch] }

/-- Extend the exact prefix by the literal next allocated canonical cell. -/
private def PackedReviewerProbePrefix.advance
    {memory : List (List Bool)} {plan : List Nat}
    {next : Nat} {repliesRev : List (List Bool)}
    (hprefix : PackedReviewerProbePrefix memory plan next repliesRev)
    (address : Nat) (tail : List Nat) (cell : List Bool)
    (hnextRest : hprefix.rest = address :: tail)
    (hcell : packedProbeCell memory address = some cell) :
    PackedReviewerProbePrefix memory plan (next + 1) (cell :: repliesRev) := by
  have hplan := hprefix.plan_eq
  have hnext := hprefix.next_eq
  have hreplies := hprefix.replies_eq
  have hfetch := hprefix.fetch_eq
  refine
    { consumed := hprefix.consumed ++ [address]
      rest := tail
      cells := hprefix.cells ++ [cell]
      plan_eq := ?_
      next_eq := ?_
      replies_eq := ?_
      fetch_eq := ?_ }
  · exact hplan.trans (by
      rw [hnextRest]
      simp [List.append_assoc])
  · calc
      next + 1 = hprefix.consumed.length + 1 :=
        congrArg (fun value => value + 1) hnext
      _ = (hprefix.consumed ++ [address]).length := by simp
  · simp [hreplies]
  · exact packedFetch_append_singleton_of_some memory hprefix.consumed
      address hprefix.cells cell hfetch hcell

/-- A completed prefix is the exact full-plan fetch in controller order. -/
private theorem PackedReviewerProbePrefix.fetch_eq_of_rest_nil
    {memory : List (List Bool)} {plan : List Nat}
    {next : Nat} {repliesRev : List (List Bool)}
    (hprefix : PackedReviewerProbePrefix memory plan next repliesRev)
    (hrest : hprefix.rest = []) :
    packedFetch memory plan = some repliesRev.reverse := by
  rw [hprefix.plan_eq, hrest]
  simpa [hprefix.replies_eq] using hprefix.fetch_eq

private theorem packedFetch_length_of_some
    (memory : List (List Bool)) (plan : List Nat)
    (cells : List (List Bool))
    (hfetch : packedFetch memory plan = some cells) :
    cells.length = plan.length := by
  induction plan generalizing cells with
  | nil =>
      simp [packedFetch] at hfetch
      subst cells
      rfl
  | cons address rest ih =>
      cases hcell : packedProbeCell memory address with
      | none => simp [packedFetch, hcell] at hfetch
      | some cell =>
          cases hrest : packedFetch memory rest with
          | none => simp [packedFetch, hcell, hrest] at hfetch
          | some cellsRest =>
              have hcells : cells = cell :: cellsRest := by
                simpa [packedFetch, hcell, hrest] using hfetch.symm
              subst cells
              simp [ih cellsRest hrest]

private theorem packedFetch_cell_mem_of_some
    (memory : List (List Bool)) (plan : List Nat)
    (cells : List (List Bool))
    (hfetch : packedFetch memory plan = some cells) :
    forall cell, cell ∈ cells -> cell ∈ memory := by
  induction plan generalizing cells with
  | nil =>
      simp [packedFetch] at hfetch
      subst cells
      simp
  | cons address rest ih =>
      cases hcell : packedProbeCell memory address with
      | none => simp [packedFetch, hcell] at hfetch
      | some headCell =>
          cases hrest : packedFetch memory rest with
          | none => simp [packedFetch, hcell, hrest] at hfetch
          | some tailCells =>
              have hcells : cells = headCell :: tailCells := by
                simpa [packedFetch, hcell, hrest] using hfetch.symm
              subst cells
              intro cell hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with rfl | htail
              · exact List.mem_of_getElem? (by
                  simpa [packedProbeCell] using hcell)
              · exact ih tailCells hrest cell htail

private theorem packedFetch_probeCell_of_get?
    (memory : List (List Bool)) (plan : List Nat)
    (cells : List (List Bool)) (position address : Nat)
    (hfetch : packedFetch memory plan = some cells)
    (hget : plan[position]? = some address) :
    exists cell, packedProbeCell memory address = some cell := by
  induction plan generalizing position cells with
  | nil => simp at hget
  | cons head tail ih =>
      cases hhead : packedProbeCell memory head with
      | none => simp [packedFetch, hhead] at hfetch
      | some headCell =>
          cases htail : packedFetch memory tail with
          | none => simp [packedFetch, hhead, htail] at hfetch
          | some tailCells =>
              cases position with
              | zero =>
                  simp at hget
                  subst address
                  exact ⟨headCell, hhead⟩
              | succ position =>
                  simp at hget
                  exact ih tailCells position htail hget

private theorem PackedReviewerProbePrefix.replies_length
    {memory : List (List Bool)} {plan : List Nat}
    {next : Nat} {repliesRev : List (List Bool)}
    (hprefix : PackedReviewerProbePrefix memory plan next repliesRev) :
    repliesRev.length = next := by
  have hlength := packedFetch_length_of_some memory hprefix.consumed
    hprefix.cells hprefix.fetch_eq
  rw [hprefix.next_eq, ← hlength, ← hprefix.replies_eq]
  simp

private theorem PackedReviewerProbePrefix.replies_word_fits
    {shape : CartesianShape} {plan : List Nat}
    {next : Nat} {repliesRev : List (List Bool)}
    (hprefix :
      PackedReviewerProbePrefix (packedReviewerMemory shape) plan next
        repliesRev) :
    forall word, word ∈ repliesRev -> PackedReviewerWordFits shape.size word := by
  intro word hmem
  have hcells : word ∈ hprefix.cells := by
    rw [← hprefix.replies_eq]
    simpa using hmem
  have hmemory := packedFetch_cell_mem_of_some
    (packedReviewerMemory shape) hprefix.consumed hprefix.cells
    hprefix.fetch_eq word hcells
  exact Nat.le_of_eq (packedReviewerMemory_cell_length shape hmemory)

private theorem PackedReviewerProbePrefix.advance_head
    {memory : List (List Bool)} {plan : List Nat}
    {next : Nat} {repliesRev : List (List Bool)}
    (hprefix : PackedReviewerProbePrefix memory plan next repliesRev)
    (allCells : List (List Bool))
    (hfull : packedFetch memory plan = some allCells)
    (address : Nat) (tail : List Nat)
    (hrest : hprefix.rest = address :: tail) :
    exists cell,
      packedProbeCell memory address = some cell /\
        exists nextPrefix :
          PackedReviewerProbePrefix memory plan (next + 1)
            (cell :: repliesRev),
          nextPrefix.rest = tail := by
  have hget : plan[next]? = some address := by
    have hplan := hprefix.plan_eq
    have hnext := hprefix.next_eq
    simpa [hplan, hnext, hrest]
  rcases packedFetch_probeCell_of_get? memory plan allCells next address
      hfull hget with ⟨cell, hcell⟩
  let nextPrefix := hprefix.advance address tail cell hrest hcell
  refine ⟨cell, hcell, nextPrefix, ?_⟩
  rfl

/-! ## Lifting nested protocol invariants into controller states -/

private structure PackedReviewerWholeStateCoreFits
    (n : Nat) (state : PackedReviewerWholeState) : Prop where
  scalar_fields :
    forall value, value ∈ packedReviewerWholeStateNatFields state ->
      PackedReviewerNatFits n value
  word_fields :
    forall word, word ∈ packedReviewerWholeStateWordFields state ->
      PackedReviewerWordFits n word
  wide_fields :
    forall bits, bits ∈ packedReviewerWholeStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth n
  continuation_depth :
    packedReviewerWholeStateContinuationDepth state <= 3
  control_fields : packedReviewerWholeStateControlBounds state

private structure PackedReviewerSparsePreludeStateCoreFits
    (n : Nat) (state : PackedReviewerSparsePreludeState) : Prop where
  scalar_fields :
    forall value,
      value ∈ packedReviewerSparsePreludeStateNatFields state ->
        PackedReviewerNatFits n value
  word_fields :
    forall word,
      word ∈ packedReviewerSparsePreludeStateWordFields state ->
        PackedReviewerWordFits n word
  remaining : packedReviewerSparsePreludeRemaining state <= 3

/-! ### Canonical K1 prelude phase -/

/-- The three exact logical K1 replies used by the canonical memory run. -/
private structure PackedReviewerCanonicalPreludeReplies
    (shape : CartesianShape) where
  superReply : List Bool
  blockReply : List Bool
  flagReply : List Bool
  super_read :
    packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
        (packedReviewerMemory shape) .rankSuper = some superReply
  block_read :
    packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
        (packedReviewerMemory shape) .rankBlock = some blockReply
  flag_read :
    packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
        (packedReviewerMemory shape) .flagWord = some flagReply
  decode_eq :
    packedReviewerSparseCountFromReplies shape.size
      superReply blockReply flagReply = packedReviewerSparseCount shape

private theorem packedReviewerCanonicalPreludeReplies_exists
    (shape : CartesianShape) :
    Nonempty (PackedReviewerCanonicalPreludeReplies shape) := by
  rcases packedReviewerSparsePrelude_physicalReplies_exact shape with
    ⟨superReply, blockReply, flagReply, hsuper, hblock, hflag, hdecode⟩
  exact ⟨
    { superReply := superReply
      blockReply := blockReply
      flagReply := flagReply
      super_read := hsuper
      block_read := hblock
      flag_read := hflag
      decode_eq := hdecode }⟩

/-- Exact logical prelude prefixes, before physical one/two-cell lowering. -/
private inductive PackedReviewerCanonicalPreludeState
    (shape : CartesianShape)
    (replies : PackedReviewerCanonicalPreludeReplies shape) :
    PackedReviewerSparsePreludeState -> Prop where
  | awaitSuper :
      PackedReviewerCanonicalPreludeState shape replies
        (.awaitSuper shape.size (longCount shape))
  | awaitBlock :
      PackedReviewerCanonicalPreludeState shape replies
        (.awaitBlock shape.size (longCount shape) replies.superReply)
  | awaitFlag :
      PackedReviewerCanonicalPreludeState shape replies
        (.awaitFlag shape.size (longCount shape)
          replies.superReply replies.blockReply)
  | done :
      PackedReviewerCanonicalPreludeState shape replies
        (.done shape.size (longCount shape)
          (packedReviewerSparseCount shape))

private theorem packedReviewerCanonicalPreludeState_start
    (shape : CartesianShape)
    (replies : PackedReviewerCanonicalPreludeReplies shape) :
    PackedReviewerCanonicalPreludeState shape replies
      (packedReviewerSparsePreludeInit shape.size (longCount shape)) := by
  simpa [packedReviewerSparsePreludeInit] using
    (PackedReviewerCanonicalPreludeState.awaitSuper (shape := shape)
      (replies := replies))

/-- Consuming the exact canonical logical reply advances one exact K1 phase. -/
private theorem PackedReviewerCanonicalPreludeState.consume
    {shape : CartesianShape}
    {replies : PackedReviewerCanonicalPreludeReplies shape}
    {state : PackedReviewerSparsePreludeState}
    (hstate : PackedReviewerCanonicalPreludeState shape replies state)
    {request : PackedReviewerSparsePreludeRequest} {word : List Bool}
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (hread :
      packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
          (packedReviewerMemory shape) request = some word) :
    PackedReviewerCanonicalPreludeState shape replies
      (packedReviewerSparsePreludeConsumeReply state word) := by
  cases hstate with
  | awaitSuper =>
      have hrequestEq : request = .rankSuper := by
        simpa [packedReviewerSparsePreludeNextRequest] using hrequest.symm
      subst request
      rw [replies.super_read] at hread
      have hword : word = replies.superReply := Option.some.inj hread.symm
      subst word
      simpa [packedReviewerSparsePreludeConsumeReply] using
        (PackedReviewerCanonicalPreludeState.awaitBlock (shape := shape)
          (replies := replies))
  | awaitBlock =>
      have hrequestEq : request = .rankBlock := by
        simpa [packedReviewerSparsePreludeNextRequest] using hrequest.symm
      subst request
      rw [replies.block_read] at hread
      have hword : word = replies.blockReply := Option.some.inj hread.symm
      subst word
      simpa [packedReviewerSparsePreludeConsumeReply] using
        (PackedReviewerCanonicalPreludeState.awaitFlag (shape := shape)
          (replies := replies))
  | awaitFlag =>
      have hrequestEq : request = .flagWord := by
        simpa [packedReviewerSparsePreludeNextRequest] using hrequest.symm
      subst request
      rw [replies.flag_read] at hread
      have hword : word = replies.flagReply := Option.some.inj hread.symm
      subst word
      simpa [packedReviewerSparsePreludeConsumeReply, replies.decode_eq] using
        (PackedReviewerCanonicalPreludeState.done (shape := shape)
          (replies := replies))
  | done =>
      simp [packedReviewerSparsePreludeNextRequest] at hrequest

/-- Every scalar retained by an exact K1 logical prefix fits one reviewer word. -/
private theorem PackedReviewerCanonicalPreludeState.scalar_fields
    {shape : CartesianShape}
    {replies : PackedReviewerCanonicalPreludeReplies shape}
    {state : PackedReviewerSparsePreludeState}
    (hstate : PackedReviewerCanonicalPreludeState shape replies state) :
    forall value,
      value ∈ packedReviewerSparsePreludeStateNatFields state ->
        PackedReviewerNatFits shape.size value := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  have hlong := longCount_lt_two_pow_reviewerWidth shape
  have hsparse := packedReviewerSparseCount_lt_two_pow shape
  cases hstate with
  | awaitSuper | awaitBlock | awaitFlag =>
      intro value hmem
      simp [packedReviewerSparsePreludeStateNatFields] at hmem
      rcases hmem with rfl | rfl
      · exact hn
      · exact hlong
  | done =>
      intro value hmem
      simp [packedReviewerSparsePreludeStateNatFields] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hn
      · exact hlong
      · exact hsparse

private theorem PackedReviewerCanonicalPreludeState.remaining_le_three
    {shape : CartesianShape}
    {replies : PackedReviewerCanonicalPreludeReplies shape}
    {state : PackedReviewerSparsePreludeState}
    (hstate : PackedReviewerCanonicalPreludeState shape replies state) :
    packedReviewerSparsePreludeRemaining state <= 3 := by
  cases hstate <;> simp [packedReviewerSparsePreludeRemaining]

private theorem packedReviewerCanonicalPreludeRequestRead_word_fits
    (shape : CartesianShape) (request : PackedReviewerSparsePreludeRequest)
    (word : List Bool)
    (hread :
      packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
          (packedReviewerMemory shape) request = some word) :
    PackedReviewerWordFits shape.size word := by
  have hcounted : PackedSourceCounted shape.size request.source := by
    cases request <;>
      simp [PackedReviewerSparsePreludeRequest.source, PackedSourceCounted]
  unfold packedReviewerSparsePreludeRequestRead at hread
  by_cases hindex :
      request.index shape.size <
        packedSourceWordCount shape.size (longCount shape) request.source
  · rw [if_pos hindex] at hread
    cases hfetch :
        packedFetch (packedReviewerMemory shape)
          (packedReviewerSparsePreludeRequestPlan shape.size
            (longCount shape) request) with
    | none => simp [hfetch] at hread
    | some cells =>
        have hword :
            packedReviewerDecodeSpan shape.size
                (packedReviewerSparsePreludeRequestBitAddress shape.size
                  (longCount shape) request)
                (packedSourceReadWidth shape.size (longCount shape)
                  request.source (request.index shape.size)) cells = word := by
          simpa [hfetch] using hread
        rw [← hword]
        exact Nat.le_trans
          (packedReviewerDecodeSpan_length_le shape.size _
            (packedSourceReadWidth shape.size (longCount shape)
              request.source (request.index shape.size)) cells)
          (Nat.le_trans
            (packedSourceReadWidth_le_stride shape.size (longCount shape)
              request.source (request.index shape.size))
            (packedSourceStride_le_reviewerCellWidth shape.size
              request.source hcounted))
  · rw [if_neg hindex] at hread
    simp at hread

private theorem PackedReviewerCanonicalPreludeReplies.super_word_fits
    {shape : CartesianShape}
    (replies : PackedReviewerCanonicalPreludeReplies shape) :
    PackedReviewerWordFits shape.size replies.superReply :=
  packedReviewerCanonicalPreludeRequestRead_word_fits shape .rankSuper
    replies.superReply replies.super_read

private theorem PackedReviewerCanonicalPreludeReplies.block_word_fits
    {shape : CartesianShape}
    (replies : PackedReviewerCanonicalPreludeReplies shape) :
    PackedReviewerWordFits shape.size replies.blockReply :=
  packedReviewerCanonicalPreludeRequestRead_word_fits shape .rankBlock
    replies.blockReply replies.block_read

private theorem PackedReviewerCanonicalPreludeReplies.flag_word_fits
    {shape : CartesianShape}
    (replies : PackedReviewerCanonicalPreludeReplies shape) :
    PackedReviewerWordFits shape.size replies.flagReply :=
  packedReviewerCanonicalPreludeRequestRead_word_fits shape .flagWord
    replies.flagReply replies.flag_read

private theorem PackedReviewerCanonicalPreludeState.core_fits
    {shape : CartesianShape}
    {replies : PackedReviewerCanonicalPreludeReplies shape}
    {state : PackedReviewerSparsePreludeState}
    (hstate : PackedReviewerCanonicalPreludeState shape replies state) :
    PackedReviewerSparsePreludeStateCoreFits shape.size state := by
  refine
    { scalar_fields := hstate.scalar_fields
      word_fields := ?_
      remaining := hstate.remaining_le_three }
  cases hstate with
  | awaitSuper =>
      simp [packedReviewerSparsePreludeStateWordFields]
  | awaitBlock =>
      intro word hmem
      simp [packedReviewerSparsePreludeStateWordFields] at hmem
      subst word
      exact replies.super_word_fits
  | awaitFlag =>
      intro word hmem
      simp [packedReviewerSparsePreludeStateWordFields] at hmem
      rcases hmem with rfl | rfl
      · exact replies.super_word_fits
      · exact replies.block_word_fits
  | done =>
      simp [packedReviewerSparsePreludeStateWordFields]

private theorem PackedReviewerCanonicalPreludeState.request_read
    {shape : CartesianShape}
    {replies : PackedReviewerCanonicalPreludeReplies shape}
    {state : PackedReviewerSparsePreludeState}
    (hstate : PackedReviewerCanonicalPreludeState shape replies state)
    {request : PackedReviewerSparsePreludeRequest}
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request) :
    exists word,
      packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
          (packedReviewerMemory shape) request = some word := by
  cases hstate with
  | awaitSuper =>
      have hrequestEq : request = .rankSuper := by
        simpa [packedReviewerSparsePreludeNextRequest] using hrequest.symm
      subst request
      exact ⟨replies.superReply, replies.super_read⟩
  | awaitBlock =>
      have hrequestEq : request = .rankBlock := by
        simpa [packedReviewerSparsePreludeNextRequest] using hrequest.symm
      subst request
      exact ⟨replies.blockReply, replies.block_read⟩
  | awaitFlag =>
      have hrequestEq : request = .flagWord := by
        simpa [packedReviewerSparsePreludeNextRequest] using hrequest.symm
      subst request
      exact ⟨replies.flagReply, replies.flag_read⟩
  | done =>
      simp [packedReviewerSparsePreludeNextRequest] at hrequest

private theorem PackedReviewerCanonicalPreludeState.result_eq
    {shape : CartesianShape}
    {replies : PackedReviewerCanonicalPreludeReplies shape}
    {state : PackedReviewerSparsePreludeState}
    (hstate : PackedReviewerCanonicalPreludeState shape replies state)
    {sparseCount : Nat}
    (hresult : packedReviewerSparsePreludeResult state = some sparseCount) :
    sparseCount = packedReviewerSparseCount shape := by
  cases hstate <;>
    simp [packedReviewerSparsePreludeResult] at hresult
  exact hresult.symm

/-- A successful full physical plan decodes to its exact logical K1 word. -/
private theorem packedReviewerDecodePreludeReplies_eq_of_request_read
    (n longCount : Nat) (memory : List (List Bool))
    (state : PackedReviewerSparsePreludeState)
    (request : PackedReviewerSparsePreludeRequest)
    (cells : List (List Bool)) (word : List Bool)
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (hfetch :
      packedFetch memory
        (packedReviewerSparsePreludeRequestPlan n longCount request) =
          some cells)
    (hread :
      packedReviewerSparsePreludeRequestRead n longCount memory request =
        some word) :
    packedReviewerDecodePreludeReplies n longCount state cells = some word := by
  by_cases hindex :
      request.index n <
        packedSourceWordCount n longCount request.source
  · have hword :
        packedReviewerDecodeSpan n
            (packedReviewerSparsePreludeRequestBitAddress n longCount request)
            (packedSourceReadWidth n longCount request.source
              (request.index n)) cells = word := by
      unfold packedReviewerSparsePreludeRequestRead at hread
      rw [if_pos hindex, hfetch] at hread
      simpa using hread
    simp [packedReviewerDecodePreludeReplies, hrequest, hindex, hword]
  · unfold packedReviewerSparsePreludeRequestRead at hread
    rw [if_neg hindex] at hread
    simp at hread

private theorem packedReviewerCurrentPreludePlan_eq_requestPlan_of_read
    (n longCount : Nat) (memory : List (List Bool))
    (state : PackedReviewerSparsePreludeState)
    (request : PackedReviewerSparsePreludeRequest) (word : List Bool)
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (hread :
      packedReviewerSparsePreludeRequestRead n longCount memory request =
        some word) :
    packedReviewerCurrentPreludePlan n longCount state =
      packedReviewerSparsePreludeRequestPlan n longCount request := by
  unfold packedReviewerSparsePreludeRequestRead at hread
  by_cases hindex :
      request.index n <
        packedSourceWordCount n longCount request.source
  · simp [packedReviewerCurrentPreludePlan, hrequest, hindex]
  · rw [if_neg hindex] at hread
    simp at hread

private theorem packedReviewerCurrentPreludePlan_fetch_of_read
    (n longCount : Nat) (memory : List (List Bool))
    (state : PackedReviewerSparsePreludeState)
    (request : PackedReviewerSparsePreludeRequest) (word : List Bool)
    (hrequest : packedReviewerSparsePreludeNextRequest state = some request)
    (hread :
      packedReviewerSparsePreludeRequestRead n longCount memory request =
        some word) :
    exists cells,
      packedFetch memory
        (packedReviewerCurrentPreludePlan n longCount state) = some cells := by
  have hplan := packedReviewerCurrentPreludePlan_eq_requestPlan_of_read
    n longCount memory state request word hrequest hread
  unfold packedReviewerSparsePreludeRequestRead at hread
  by_cases hindex :
      request.index n <
        packedSourceWordCount n longCount request.source
  · rw [if_pos hindex] at hread
    cases hfetch :
        packedFetch memory
          (packedReviewerSparsePreludeRequestPlan n longCount request) with
    | none => simp [hfetch] at hread
    | some cells =>
        exact ⟨cells, by simpa [hplan] using hfetch⟩
  · rw [if_neg hindex] at hread
    simp at hread

private theorem packedReviewerLogicalDecode_eq_globalReadStore_of_fetch
    (shape : CartesianShape) (request : PackedReviewerLogicalRequest)
    (cells : List (List Bool))
    (hfetch :
      packedFetch (packedReviewerMemory shape)
          (packedReviewerLogicalPlan shape.size (longCount shape)
            (packedReviewerSparseCount shape) request) = some cells) :
    packedReviewerLogicalDecode shape.size (longCount shape)
        (packedReviewerSparseCount shape) request cells =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index := by
  have hread := packedReviewerLogicalRead_eq_globalReadStore shape request
  unfold packedReviewerLogicalRead at hread
  rw [hfetch] at hread
  exact hread

private theorem packedReviewerHeader_core_fits
    {n left right : Nat}
    (hn : PackedReviewerNatFits n n)
    (hleft : PackedReviewerNatFits n left)
    (hright : PackedReviewerNatFits n right) :
    PackedReviewerControllerStateCoreFits n (.header n left right) := by
  refine
    { scalar_fields := ?_
      word_fields := ?_
      wide_fields := ?_
      continuation_depth := ?_
      control_fields := ?_ }
  · intro value hmem
    simp [packedReviewerControllerStateNatFields] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hn
    · exact hleft
    · exact hright
  · simp [packedReviewerControllerStateWordFields]
  · simp [packedReviewerControllerStateWideFields]
  · simp [packedReviewerControllerStateContinuationDepth]
  · simp [packedReviewerControllerStateControlBounds]

private theorem packedReviewerDone_core_fits
    {n : Nat} {value : Option Nat}
    (hvalue : forall index, value = some index -> PackedReviewerNatFits n index) :
    PackedReviewerControllerStateCoreFits n (.done value) := by
  refine
    { scalar_fields := ?_
      word_fields := ?_
      wide_fields := ?_
      continuation_depth := ?_
      control_fields := ?_ }
  · intro index hmem
    cases value with
    | none =>
        simp [packedReviewerControllerStateNatFields,
          packedReviewerOptionNatFields] at hmem
    | some value =>
        simp [packedReviewerControllerStateNatFields,
          packedReviewerOptionNatFields] at hmem
        subst index
        exact hvalue value rfl
  · simp [packedReviewerControllerStateWordFields]
  · simp [packedReviewerControllerStateWideFields]
  · simp [packedReviewerControllerStateContinuationDepth]
  · simp [packedReviewerControllerStateControlBounds]

private theorem packedReviewerFailed_core_fits
    (n : Nat) : PackedReviewerControllerStateCoreFits n .failed := by
  refine
    { scalar_fields := ?_
      word_fields := ?_
      wide_fields := ?_
      continuation_depth := ?_
      control_fields := ?_ } <;>
    simp [packedReviewerControllerStateNatFields,
      packedReviewerControllerStateWordFields,
      packedReviewerControllerStateWideFields,
      packedReviewerControllerStateContinuationDepth,
      packedReviewerControllerStateControlBounds]

private theorem packedReviewerPreludeProbe_core_fits
    {n left right longCount nextOrdinal : Nat}
    {prelude : PackedReviewerSparsePreludeState}
    {repliesRev : List (List Bool)}
    (hn : PackedReviewerNatFits n n)
    (hleft : PackedReviewerNatFits n left)
    (hright : PackedReviewerNatFits n right)
    (hlongCount : PackedReviewerNatFits n longCount)
    (hnext : nextOrdinal < 2)
    (hrepliesLength : repliesRev.length = nextOrdinal)
    (hreplies : forall word, word ∈ repliesRev -> PackedReviewerWordFits n word)
    (hprelude : PackedReviewerSparsePreludeStateCoreFits n prelude) :
    PackedReviewerControllerStateCoreFits n
      (.preludeProbe n left right longCount prelude nextOrdinal repliesRev) := by
  refine
    { scalar_fields := ?_
      word_fields := ?_
      wide_fields := ?_
      continuation_depth := ?_
      control_fields := ?_ }
  · intro value hmem
    simp only [packedReviewerControllerStateNatFields, List.mem_append,
      List.mem_cons, List.mem_singleton] at hmem
    rcases hmem with hfixed | hnested
    rcases hfixed with rfl | rfl | rfl | rfl | rfl | hnil
    · exact hn
    · exact hleft
    · exact hright
    · exact hlongCount
    · exact packedReviewerFixedScalar_fits n value (by omega)
    · simp at hnil
    · exact hprelude.scalar_fields value hnested
  · intro word hmem
    simp only [packedReviewerControllerStateWordFields,
      List.mem_append] at hmem
    rcases hmem with hreply | hnested
    · exact hreplies word hreply
    · exact hprelude.word_fields word hnested
  · simp [packedReviewerControllerStateWideFields]
  · simp [packedReviewerControllerStateContinuationDepth]
  · exact ⟨hprelude.remaining, hnext, hrepliesLength⟩

private theorem packedReviewerWholeProbe_core_fits
    {n left right longCount sparseCount logicalStepsAfterReply nextOrdinal : Nat}
    {whole : PackedReviewerWholeState}
    {repliesRev : List (List Bool)}
    (hn : PackedReviewerNatFits n n)
    (hleft : PackedReviewerNatFits n left)
    (hright : PackedReviewerNatFits n right)
    (hlongCount : PackedReviewerNatFits n longCount)
    (hsparseCount : PackedReviewerNatFits n sparseCount)
    (hsteps : logicalStepsAfterReply <= 210)
    (hremaining : packedReviewerWholeRemaining whole <= 210)
    (hnext : nextOrdinal < 2)
    (hrepliesLength : repliesRev.length = nextOrdinal)
    (hreplies : forall word, word ∈ repliesRev -> PackedReviewerWordFits n word)
    (hwhole : PackedReviewerWholeStateCoreFits n whole) :
    PackedReviewerControllerStateCoreFits n
      (.wholeProbe n left right longCount sparseCount logicalStepsAfterReply
        whole nextOrdinal repliesRev) := by
  refine
    { scalar_fields := ?_
      word_fields := ?_
      wide_fields := ?_
      continuation_depth := hwhole.continuation_depth
      control_fields :=
        ⟨hsteps, hremaining, hnext, hrepliesLength, hwhole.control_fields⟩ }
  · intro value hmem
    simp only [packedReviewerControllerStateNatFields, List.mem_append,
      List.mem_cons, List.mem_singleton] at hmem
    rcases hmem with hfixed | hnested
    rcases hfixed with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | hnil
    · exact hn
    · exact hleft
    · exact hright
    · exact hlongCount
    · exact hsparseCount
    · exact
        packedReviewerFixedScalar_fits n value (by omega)
    · exact packedReviewerFixedScalar_fits n value (by omega)
    · simp at hnil
    · exact hwhole.scalar_fields value hnested
  · intro word hmem
    simp only [packedReviewerControllerStateWordFields,
      List.mem_append] at hmem
    rcases hmem with hreply | hnested
    · exact hreplies word hreply
    · exact hwhole.word_fields word hnested
  · exact hwhole.wide_fields

/-! ## Reply-buffer and fixed-counter preservation for atomic protocols -/

private theorem packedReviewerFlattenPayloadWords_length_le
    (n : Nat) (words : List (List Bool))
    (hwords : forall word, word ∈ words -> PackedReviewerWordFits n word) :
    (SuccinctSpace.flattenPayloadWords words).length <=
      words.length * packedReviewerCellWidth n := by
  induction words with
  | nil => simp [SuccinctSpace.flattenPayloadWords]
  | cons word words ih =>
      have hword := hwords word List.mem_cons_self
      have hwordLength :
          word.length <= packedReviewerCellWidth n := hword
      have htail :
          forall tail, tail ∈ words -> PackedReviewerWordFits n tail := by
        intro tail hmem
        exact hwords tail (List.mem_cons_of_mem word hmem)
      have hrec := ih htail
      simp only [SuccinctSpace.flattenPayloadWords, List.length_append,
        List.length_cons]
      rw [Nat.add_mul]
      omega

private structure PackedReviewerRankStorageFits
    (n : Nat) (state : PackedReviewerRankState) : Prop where
  word_fields :
    forall word, word ∈ packedReviewerRankStateWordFields state ->
      PackedReviewerWordFits n word
  counter_sum :
    match state with
    | .fold _ _ _ _ _ j remaining _ _ => j + remaining <= 8
    | _ => True

private theorem PackedReviewerRankStorageFits.control_fields
    {n : Nat} {state : PackedReviewerRankState}
    (hstate : PackedReviewerRankStorageFits n state) :
    packedReviewerRankStateControlBounds state := by
  cases state with
  | superSample invocation kind stateN pos =>
      simp [packedReviewerRankStateControlBounds]
  | blockSample invocation kind stateN pos superSample =>
      simp [packedReviewerRankStateControlBounds]
  | word invocation kind stateN pos superSample blockSample =>
      simp [packedReviewerRankStateControlBounds]
  | fold invocation kind stateN word effectiveLimit j remaining acc base =>
      have hsum := hstate.counter_sum
      simp only [packedReviewerRankStateControlBounds]
      omega
  | done value => simp [packedReviewerRankStateControlBounds]

private theorem packedReviewerRankStart_storage_fits
    (n stateN : Nat) (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (position : Nat) :
    PackedReviewerRankStorageFits n
      (.superSample invocation kind stateN position) := by
  refine
    { word_fields := ?_
      counter_sum := trivial }
  intro word hmem
  simp [packedReviewerRankStateWordFields] at hmem

private theorem packedReviewerRankStartFold_storage_fits
    {n stateN : Nat} (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (word : List Bool)
    (effectiveLimit base : Nat)
    (hword : PackedReviewerWordFits n word) :
    PackedReviewerRankStorageFits n
      (packedReviewerRankStartFold invocation kind stateN word effectiveLimit
        base) := by
  let effective :=
    SuccinctClose.bpWordRankEffLimit word effectiveLimit
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits stateN) effective
  have hcount : count <= 8 := by
    exact SuccinctClose.bpWordChunkCount_le_eight _ _
  by_cases hzero : count = 0
  · have heq :
        packedReviewerRankStartFold invocation kind stateN word effectiveLimit
            base = .done base := by
      simp [packedReviewerRankStartFold, effective, count, hzero]
    rw [heq]
    constructor <;> simp [packedReviewerRankStateWordFields]
  · have heq :
        packedReviewerRankStartFold invocation kind stateN word effectiveLimit
            base =
          .fold invocation kind stateN word effective 0 count 0 base := by
      simp [packedReviewerRankStartFold, effective, count, hzero]
    rw [heq]
    refine ⟨?_, ?_⟩
    · intro stored hmem
      simp [packedReviewerRankStateWordFields] at hmem
      subst stored
      exact hword
    · simpa [count] using hcount

private theorem packedReviewerRankConsumeReply_storage_fits
    {n : Nat} {state : PackedReviewerRankState}
    {reply : Option (List Bool)}
    (hstate : PackedReviewerRankStorageFits n state)
    (hreply : forall word, reply = some word -> PackedReviewerWordFits n word) :
    PackedReviewerRankStorageFits n
      (packedReviewerRankConsumeReply state reply) := by
  cases state with
  | superSample invocation kind stateN pos =>
      constructor <;>
        simp [packedReviewerRankConsumeReply,
          packedReviewerRankStateWordFields]
  | blockSample invocation kind stateN pos superSample =>
      constructor <;>
        simp [packedReviewerRankConsumeReply,
          packedReviewerRankStateWordFields]
  | word invocation kind stateN pos superSample blockSample =>
      cases superSample with
      | none =>
          constructor <;>
            simp [packedReviewerRankConsumeReply,
              packedReviewerRankStateWordFields]
      | some super =>
        cases blockSample with
        | none =>
          constructor <;>
            simp [packedReviewerRankConsumeReply,
              packedReviewerRankStateWordFields]
        | some block =>
          cases reply with
          | none =>
              constructor <;>
                simp [packedReviewerRankConsumeReply,
                  packedReviewerRankStateWordFields]
          | some word =>
              have hword := hreply word rfl
              simpa [packedReviewerRankConsumeReply] using
                (packedReviewerRankStartFold_storage_fits
                  (n := n) (stateN := stateN) invocation kind word
                  (packedReviewerRankQueryPos kind stateN pos -
                    packedReviewerRankQueryPos kind stateN pos /
                        kind.wordSize stateN * kind.wordSize stateN)
                  (super + block) hword)
  | fold invocation kind stateN word effectiveLimit j remaining acc base =>
      have hstored : PackedReviewerWordFits n word := by
        apply hstate.word_fields
        simp [packedReviewerRankStateWordFields]
      cases remaining with
      | zero =>
          constructor <;>
            simp [packedReviewerRankConsumeReply,
              packedReviewerRankStateWordFields]
      | succ remaining =>
          by_cases hlast : remaining = 0
          · subst remaining
            constructor <;>
              simp [packedReviewerRankConsumeReply,
                packedReviewerRankStateWordFields]
          · let acc' :=
              SuccinctClose.bpWordRankStepDecoded
                (packedFringeChunkBits stateN) kind.target
                (SuccinctClose.bpWordChunkSliceLen
                  (packedFringeChunkBits stateN) effectiveLimit j)
                acc (packedReviewerDecodeNat reply)
            have heq :
                packedReviewerRankConsumeReply
                    (.fold invocation kind stateN word effectiveLimit j
                      (remaining + 1) acc base) reply =
                  .fold invocation kind stateN word effectiveLimit (j + 1)
                    remaining acc' base := by
              simp [packedReviewerRankConsumeReply, acc', hlast]
            rw [heq]
            refine ⟨?_, ?_⟩
            · intro stored hmem
              simp [packedReviewerRankStateWordFields] at hmem
              subst stored
              exact hstored
            · have hsum := hstate.counter_sum
              omega
  | done value =>
      simpa [packedReviewerRankConsumeReply] using hstate

private structure PackedReviewerWordSelectStorageFits
    (n : Nat) (state : PackedReviewerWordSelectState) : Prop where
  word_fields :
    forall word, word ∈ packedReviewerWordSelectStateWordFields state ->
      PackedReviewerWordFits n word
  counter_sum :
    match state with
    | .rankChunk _ _ _ _ j remaining _
    | .selectChunk _ _ _ _ j remaining _ => j + remaining <= 8
    | .done _ => True

private theorem PackedReviewerWordSelectStorageFits.control_fields
    {n : Nat} {state : PackedReviewerWordSelectState}
    (hstate : PackedReviewerWordSelectStorageFits n state) :
    packedReviewerWordSelectStateControlBounds state := by
  cases state with
  | rankChunk invocation stateN target word j remaining occurrence
  | selectChunk invocation stateN target word j remaining occurrence =>
      have hsum := hstate.counter_sum
      simp only [packedReviewerWordSelectStateControlBounds]
      omega
  | done value => simp [packedReviewerWordSelectStateControlBounds]

private theorem packedReviewerWordSelectStart_storage_fits
    {n stateN : Nat} (invocation : PackedReviewerInvocation)
    (target : Bool) (word : List Bool) (occurrence : Nat)
    (hword : PackedReviewerWordFits n word) :
    PackedReviewerWordSelectStorageFits n
      (packedReviewerWordSelectStart invocation stateN target word
        occurrence) := by
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits stateN) word.length
  have hcount : count <= 8 :=
    SuccinctClose.bpWordChunkCount_le_eight _ _
  by_cases hzero : count = 0
  · have heq :
        packedReviewerWordSelectStart invocation stateN target word
            occurrence = .done none := by
      simp [packedReviewerWordSelectStart, count, hzero]
    rw [heq]
    constructor <;> simp [packedReviewerWordSelectStateWordFields]
  · have heq :
        packedReviewerWordSelectStart invocation stateN target word
            occurrence =
          .rankChunk invocation stateN target word 0 count occurrence := by
      simp [packedReviewerWordSelectStart, count, hzero]
    rw [heq]
    refine ⟨?_, ?_⟩
    · intro stored hmem
      simp [packedReviewerWordSelectStateWordFields] at hmem
      subst stored
      exact hword
    · simpa [count] using hcount

private theorem packedReviewerWordSelectConsumeReply_storage_fits
    {n : Nat} {state : PackedReviewerWordSelectState}
    {reply : Option (List Bool)}
    (hstate : PackedReviewerWordSelectStorageFits n state) :
    PackedReviewerWordSelectStorageFits n
      (packedReviewerWordSelectConsumeReply state reply) := by
  cases state with
  | rankChunk invocation stateN target word j remaining occurrence =>
      have hword : PackedReviewerWordFits n word := by
        apply hstate.word_fields
        simp [packedReviewerWordSelectStateWordFields]
      let rank :=
        SuccinctClose.bpChunkRankOfEntry (packedFringeChunkBits stateN)
          target
          (SuccinctClose.bpWordChunkSliceLen
            (packedFringeChunkBits stateN) word.length j)
          ((packedReviewerDecodeNat reply).getD 0)
      by_cases hoccurrence : occurrence < rank
      · have heq :
            packedReviewerWordSelectConsumeReply
                (.rankChunk invocation stateN target word j remaining
                  occurrence) reply =
              .selectChunk invocation stateN target word j remaining
                occurrence := by
          simp [packedReviewerWordSelectConsumeReply, rank, hoccurrence]
        rw [heq]
        refine ⟨?_, ?_⟩
        · intro stored hmem
          simp [packedReviewerWordSelectStateWordFields] at hmem
          subst stored
          exact hword
        · exact hstate.counter_sum
      · cases remaining with
        | zero =>
            have heq :
                packedReviewerWordSelectConsumeReply
                    (.rankChunk invocation stateN target word j 0 occurrence)
                    reply = .done none := by
              simp [packedReviewerWordSelectConsumeReply, rank, hoccurrence]
            rw [heq]
            constructor <;> simp [packedReviewerWordSelectStateWordFields]
        | succ remaining =>
            by_cases hlast : remaining = 0
            · subst remaining
              have heq :
                  packedReviewerWordSelectConsumeReply
                      (.rankChunk invocation stateN target word j 1 occurrence)
                      reply = .done none := by
                simp [packedReviewerWordSelectConsumeReply, rank, hoccurrence]
              rw [heq]
              constructor <;> simp [packedReviewerWordSelectStateWordFields]
            · have heq :
                  packedReviewerWordSelectConsumeReply
                      (.rankChunk invocation stateN target word j
                        (remaining + 1) occurrence) reply =
                    .rankChunk invocation stateN target word (j + 1)
                      remaining (occurrence - rank) := by
                simp [packedReviewerWordSelectConsumeReply, rank, hoccurrence,
                  hlast]
              rw [heq]
              refine ⟨?_, ?_⟩
              · intro stored hmem
                simp [packedReviewerWordSelectStateWordFields] at hmem
                subst stored
                exact hword
              · have hsum := hstate.counter_sum
                omega
  | selectChunk invocation stateN target word j remaining occurrence =>
      constructor <;>
        simp [packedReviewerWordSelectConsumeReply,
          packedReviewerWordSelectStateWordFields]
  | done value =>
      simpa [packedReviewerWordSelectConsumeReply] using hstate

private structure PackedReviewerFringeStorageFits
    (n : Nat) (state : PackedReviewerFringeState) : Prop where
  wide_fields :
    forall bits, bits ∈ packedReviewerFringeStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth n
  counter_sum :
    match state with
    | .chunk _ _ _ _ _ j remaining _ => j + remaining <= 33
    | .done _ => True

private theorem PackedReviewerFringeStorageFits.control_fields
    {n : Nat} {state : PackedReviewerFringeState}
    (hstate : PackedReviewerFringeStorageFits n state) :
    packedReviewerFringeStateControlBounds state := by
  cases state with
  | chunk invocation stateN window relLo relHi j remaining foldState =>
      have hsum := hstate.counter_sum
      simp only [packedReviewerFringeStateControlBounds]
      omega
  | done value => simp [packedReviewerFringeStateControlBounds]

private theorem packedReviewerFringeStart_storage_fits
    {n : Nat} (invocation : PackedReviewerInvocation)
    (window : List Bool) (seed relLo relHi count : Nat)
    (hwindow : window.length <= 4 * packedReviewerCellWidth n)
    (hcount : count <= 33) :
    PackedReviewerFringeStorageFits n
      (packedReviewerFringeStart invocation n window seed relLo relHi count) := by
  unfold packedReviewerFringeStart
  split
  · constructor <;> simp [packedReviewerFringeStateWideFields]
  · refine ⟨?_, ?_⟩
    · intro bits hmem
      simp [packedReviewerFringeStateWideFields] at hmem
      subst bits
      exact hwindow
    · simp
      exact hcount

private theorem packedReviewerFringeConsumeReply_storage_fits
    {n : Nat} {state : PackedReviewerFringeState}
    {reply : Option (List Bool)}
    (hstate : PackedReviewerFringeStorageFits n state) :
    PackedReviewerFringeStorageFits n
      (packedReviewerFringeConsumeReply state reply) := by
  cases state with
  | chunk invocation stateN window relLo relHi j remaining foldState =>
      have hwindow : window.length <= 4 * packedReviewerCellWidth n := by
        apply hstate.wide_fields
        simp [packedReviewerFringeStateWideFields]
      cases remaining with
      | zero =>
          constructor <;>
            simp [packedReviewerFringeConsumeReply,
              packedReviewerFringeStateWideFields]
      | succ remaining =>
          by_cases hlast : remaining = 0
          · subst remaining
            constructor <;>
              simp [packedReviewerFringeConsumeReply,
                packedReviewerFringeStateWideFields]
          · let nextState :=
              SuccinctClose.bpFringeChunkStepDecoded
                (packedFringeChunkBits stateN) relLo relHi j foldState
                (packedReviewerDecodeNat reply)
            have heq :
                packedReviewerFringeConsumeReply
                    (.chunk invocation stateN window relLo relHi j
                      (remaining + 1) foldState) reply =
                  .chunk invocation stateN window relLo relHi (j + 1)
                    remaining nextState := by
              simp [packedReviewerFringeConsumeReply, nextState, hlast]
            rw [heq]
            refine ⟨?_, ?_⟩
            · intro bits hmem
              simp [packedReviewerFringeStateWideFields] at hmem
              subst bits
              exact hwindow
            · have hsum := hstate.counter_sum
              omega
  | done value =>
      simpa [packedReviewerFringeConsumeReply] using hstate

private structure PackedReviewerBPWindowStorageFits
    (n : Nat) (state : PackedReviewerBPWindowState) : Prop where
  word_fields :
    forall word, word ∈ packedReviewerBPWindowStateWordFields state ->
      PackedReviewerWordFits n word
  wide_fields :
    forall bits, bits ∈ packedReviewerBPWindowStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth n
  counter_exact :
    match state with
    | .read _ _ _ _ next wordsRev =>
        next <= 4 ∧ wordsRev.length = next
    | .done _ => True

private theorem PackedReviewerBPWindowStorageFits.control_fields
    {n : Nat} {state : PackedReviewerBPWindowState}
    (hstate : PackedReviewerBPWindowStorageFits n state) :
    packedReviewerBPWindowStateControlBounds state := by
  cases state <;>
    simpa [packedReviewerBPWindowStateControlBounds] using hstate.counter_exact

private theorem packedReviewerBPWindowStart_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (blockSize close : Nat) :
    PackedReviewerBPWindowStorageFits n
      (packedReviewerBPWindowStart invocation n blockSize close) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [packedReviewerBPWindowStart,
      packedReviewerBPWindowStateWordFields,
      packedReviewerBPWindowStateWideFields]

private theorem packedReviewerBPWindowConsumeReply_storage_fits
    {n : Nat} {state : PackedReviewerBPWindowState}
    {reply : Option (List Bool)} {request : PackedReviewerLogicalRequest}
    (hstate : PackedReviewerBPWindowStorageFits n state)
    (hrequest : packedReviewerBPWindowNextRequest state = some request)
    (hreply : forall word, reply = some word -> PackedReviewerWordFits n word) :
    PackedReviewerBPWindowStorageFits n
      (packedReviewerBPWindowConsumeReply state reply) := by
  cases state with
  | read invocation stateN blockSize close next wordsRev =>
      have hwords :
          forall word, word ∈ wordsRev -> PackedReviewerWordFits n word := by
        intro word hmem
        apply hstate.word_fields word
        simpa [packedReviewerBPWindowStateWordFields] using hmem
      let supplied := reply.getD []
      have hsupplied : PackedReviewerWordFits n supplied := by
        cases reply with
        | none => simp [supplied, PackedReviewerWordFits]
        | some word => simpa [supplied] using hreply word rfl
      have hnewWords :
          forall word, word ∈ supplied :: wordsRev ->
            PackedReviewerWordFits n word := by
        intro word hmem
        rcases List.mem_cons.mp hmem with rfl | htail
        · exact hsupplied
        · exact hwords word htail
      have hnext : next < 4 := by
        by_cases hlt : next < 4
        · exact hlt
        · simp [packedReviewerBPWindowNextRequest, hlt] at hrequest
      by_cases hlast : next + 1 = 4
      · have hreverse :
            forall word, word ∈ (supplied :: wordsRev).reverse ->
              PackedReviewerWordFits n word := by
          intro word hmem
          exact hnewWords word (by simpa [or_comm] using hmem)
        have hflatten :=
          packedReviewerFlattenPayloadWords_length_le n
            (supplied :: wordsRev).reverse hreverse
        have hlength : (supplied :: wordsRev).reverse.length = 4 := by
          simp [hstate.counter_exact.2, hlast]
        rw [hlength] at hflatten
        have heq :
            packedReviewerBPWindowConsumeReply
                (.read invocation stateN blockSize close next wordsRev) reply =
              .done
                (SuccinctSpace.flattenPayloadWords
                  (supplied :: wordsRev).reverse) := by
          simp [packedReviewerBPWindowConsumeReply, supplied, hlast]
        rw [heq]
        refine ⟨?_, ?_, trivial⟩
        · simp [packedReviewerBPWindowStateWordFields]
        · intro bits hmem
          simp [packedReviewerBPWindowStateWideFields] at hmem
          subst bits
          simpa [List.reverse_cons] using hflatten
      · have heq :
            packedReviewerBPWindowConsumeReply
                (.read invocation stateN blockSize close next wordsRev) reply =
              .read invocation stateN blockSize close (next + 1)
                (supplied :: wordsRev) := by
          simp [packedReviewerBPWindowConsumeReply, supplied, hlast]
        rw [heq]
        refine ⟨?_, ?_, ?_⟩
        · intro word hmem
          exact hnewWords word
            (by simpa [packedReviewerBPWindowStateWordFields] using hmem)
        · simp [packedReviewerBPWindowStateWideFields]
        · exact ⟨by omega, by simp [hstate.counter_exact.2]⟩
  | done bits =>
      simp [packedReviewerBPWindowNextRequest] at hrequest

private structure PackedReviewerInteriorNatStorageFits
    (n : Nat) (state : PackedReviewerInteriorNatState) : Prop where
  word_fields :
    forall word, word ∈ packedReviewerInteriorNatStateWordFields state ->
      PackedReviewerWordFits n word
  counter_exact :
    match state with
    | .read _ _ _ next remaining repliesRev =>
        next + remaining <= 210 ∧ repliesRev.length = next
    | .done _ => True

private theorem PackedReviewerInteriorNatStorageFits.control_fields
    {n : Nat} {state : PackedReviewerInteriorNatState}
    (hstate : PackedReviewerInteriorNatStorageFits n state) :
    packedReviewerInteriorNatStateControlBounds state := by
  cases state with
  | read invocation stateN start next remaining repliesRev =>
      have hsum := hstate.counter_exact.1
      have hlength := hstate.counter_exact.2
      simp [packedReviewerInteriorNatStateControlBounds]
      exact ⟨by omega, by omega, hlength⟩
  | done value => trivial

private theorem packedReviewerInteriorNatStart_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (entryCount width base index : Nat)
    (hcount :
      SuccinctSpace.fixedWidthNatTableMachineChunkCount width
          (packedBpCodeWordWidth n) <= 210) :
    PackedReviewerInteriorNatStorageFits n
      (packedReviewerInteriorNatStart invocation n entryCount width base index) := by
  let wordSize := packedBpCodeWordWidth n
  let count :=
    SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize
  have hcount' : count <= 210 := by
    simpa [count, wordSize] using hcount
  by_cases hindex : index < entryCount
  · by_cases hzero : count = 0
    · have heq :
          packedReviewerInteriorNatStart invocation n entryCount width base
              index =
            .done (SuccinctSpace.fixedWidthNatTableMachineDecode []) := by
        simp [packedReviewerInteriorNatStart, wordSize, count, hindex, hzero]
      rw [heq]
      constructor <;> simp [packedReviewerInteriorNatStateWordFields]
    · have heq :
          packedReviewerInteriorNatStart invocation n entryCount width base
              index =
            .read invocation n (base + index * count) 0 count [] := by
        simp [packedReviewerInteriorNatStart, wordSize, count, hindex, hzero]
      rw [heq]
      refine ⟨?_, ?_⟩
      · simp [packedReviewerInteriorNatStateWordFields]
      · exact ⟨by simpa using hcount', rfl⟩
  · have heq :
        packedReviewerInteriorNatStart invocation n entryCount width base
            index =
          .read invocation n (packedInteriorOffsets n).deadAddress 0 1 [] := by
      simp [packedReviewerInteriorNatStart, wordSize, count, hindex]
    rw [heq]
    refine ⟨?_, ?_⟩
    · simp [packedReviewerInteriorNatStateWordFields]
    · exact ⟨by omega, rfl⟩

private theorem packedReviewerInteriorNatConsumeReply_storage_fits
    {n : Nat} {state : PackedReviewerInteriorNatState}
    {reply : Option (List Bool)}
    (hstate : PackedReviewerInteriorNatStorageFits n state)
    (hreply : forall word, reply = some word -> PackedReviewerWordFits n word) :
    PackedReviewerInteriorNatStorageFits n
      (packedReviewerInteriorNatConsumeReply state reply) := by
  cases state with
  | read invocation stateN start next remaining repliesRev =>
      have hwords :
          forall word,
            word ∈ repliesRev.filterMap id -> PackedReviewerWordFits n word :=
        hstate.word_fields
      have hnewWords :
          forall word,
            word ∈ (reply :: repliesRev).filterMap id ->
              PackedReviewerWordFits n word := by
        intro word hmem
        cases reply with
        | none =>
            change word ∈ repliesRev.filterMap id at hmem
            exact hwords word hmem
        | some supplied =>
            change word ∈ supplied :: repliesRev.filterMap id at hmem
            rcases List.mem_cons.mp hmem with hhead | htail
            · subst word
              exact hreply supplied rfl
            · exact hwords word htail
      cases remaining with
      | zero =>
          have heq :
              packedReviewerInteriorNatConsumeReply
                  (.read invocation stateN start next 0 repliesRev) reply =
                .done
                  (SuccinctSpace.fixedWidthNatTableMachineDecode
                    (reply :: repliesRev).reverse) := by
            simp [packedReviewerInteriorNatConsumeReply]
          rw [heq]
          constructor <;> simp [packedReviewerInteriorNatStateWordFields]
      | succ remaining =>
          by_cases hlast : remaining = 0
          · subst remaining
            have heq :
                packedReviewerInteriorNatConsumeReply
                    (.read invocation stateN start next 1 repliesRev) reply =
                  .done
                    (SuccinctSpace.fixedWidthNatTableMachineDecode
                      (reply :: repliesRev).reverse) := by
              simp [packedReviewerInteriorNatConsumeReply]
            rw [heq]
            constructor <;> simp [packedReviewerInteriorNatStateWordFields]
          · have heq :
              packedReviewerInteriorNatConsumeReply
                  (.read invocation stateN start next (remaining + 1)
                    repliesRev) reply =
                .read invocation stateN start (next + 1) remaining
                  (reply :: repliesRev) := by
              simp [packedReviewerInteriorNatConsumeReply, hlast]
            rw [heq]
            refine ⟨?_, ?_⟩
            · intro word hmem
              exact hnewWords word
                (by simpa [packedReviewerInteriorNatStateWordFields] using hmem)
            · have hsum := hstate.counter_exact.1
              have hlength := hstate.counter_exact.2
              exact ⟨by omega, by simp [hlength]⟩
  | done value =>
      exact hstate

private theorem packedReviewerMachineChunkCount_le_eight
    (width wordSize : Nat) (hwordSize : 0 < wordSize)
    (hwidth : width <= 7 * wordSize) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize <= 8 := by
  have hdiv : width / wordSize <= 7 := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm] using hwidth
  unfold SuccinctSpace.fixedWidthNatTableMachineChunkCount
  split <;> omega

private theorem packedReviewerInteriorNatStart_storage_fits_of_width
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (entryCount width base index : Nat)
    (hwidth : width <= 7 * packedBpCodeWordWidth shape.size) :
    PackedReviewerInteriorNatStorageFits shape.size
      (packedReviewerInteriorNatStart invocation shape.size entryCount width
        base index) := by
  apply packedReviewerInteriorNatStart_storage_fits
  exact Nat.le_trans
    (packedReviewerMachineChunkCount_le_eight width
      (packedBpCodeWordWidth shape.size)
      (packedBpCodeWordWidth_pos shape.size) hwidth)
    (by omega)

private theorem packedReviewerInteriorRelativeWidth_le_seven
    (shape : CartesianShape) :
    (packedInteriorLayout shape.size).relativeWidth <=
      7 * packedBpCodeWordWidth shape.size := by
  simpa [packedBpCodeWordWidth, packedInteriorLayout_eq,
    CartesianShape.bpCode_length] using
    SuccinctClose.canonicalRelativeRmmRelativeWidth_le_seven_machine shape

private theorem packedReviewerInteriorOffsetWidth_le_seven
    (shape : CartesianShape) :
    (packedInteriorLayout shape.size).offsetWidth <=
      7 * packedBpCodeWordWidth shape.size := by
  simpa [packedBpCodeWordWidth, packedInteriorLayout_eq,
    CartesianShape.bpCode_length] using
    SuccinctClose.canonicalRelativeRmmOffsetWidth_le_seven_machine shape

private theorem packedReviewerInteriorBlockWidth_le_seven
    (shape : CartesianShape) :
    (packedInteriorLayout shape.size).blockAddressWidth <=
      7 * packedBpCodeWordWidth shape.size := by
  simpa [packedBpCodeWordWidth, packedInteriorLayout_eq,
    CartesianShape.bpCode_length] using
    SuccinctClose.canonicalRelativeRmmBlockWidth_le_seven_machine shape

private theorem packedReviewerInteriorLocalLevelWidth_le_seven
    (shape : CartesianShape) :
    SuccinctClose.bpSparseLevelWidth
        (SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout shape.size).macroSize) <=
      7 * packedBpCodeWordWidth shape.size := by
  simpa [packedBpCodeWordWidth, packedInteriorLayout_eq,
    CartesianShape.bpCode_length] using
    SuccinctClose.bpSparseLevelLocalWidth_le_seven_machine shape

private theorem packedReviewerInteriorGlobalLevelWidth_le_seven
    (shape : CartesianShape) :
    SuccinctClose.bpSparseLevelWidth
        (SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout shape.size).macroSampleCount) <=
      7 * packedBpCodeWordWidth shape.size := by
  simpa [packedBpCodeWordWidth, packedInteriorLayout_eq,
    CartesianShape.bpCode_length] using
    SuccinctClose.bpSparseLevelGlobalWidth_le_seven_machine shape

/-! ## Reply-buffer and counter preservation for composed protocols -/

private def PackedReviewerSelectStorageFits
    (n : Nat) : PackedReviewerSelectState -> Prop
  | .superEntry _ stateN _ _
  | .localEntry _ stateN _ _ _ _
  | .denseFirstWord _ stateN _ _ _
  | .denseSecondWord _ stateN _ _ _ _ _ => stateN = n
  | .longRank _ stateN _ _ rank
  | .sparseRank _ stateN _ _ _ _ rank =>
      stateN = n ∧ PackedReviewerRankStorageFits n rank
  | .denseBeforeRank _ stateN _ _ _ word rank
  | .denseUptoRank _ stateN _ _ _ _ word rank =>
      stateN = n ∧ PackedReviewerWordFits n word ∧
        PackedReviewerRankStorageFits n rank
  | .denseFirstSelect _ stateN _ select
  | .denseSecondSelect _ stateN _ select =>
      stateN = n ∧ PackedReviewerWordSelectStorageFits n select
  | _ => True

private theorem PackedReviewerSelectStorageFits.word_fields
    {n : Nat} {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectStorageFits n state) :
    forall word, word ∈ packedReviewerSelectStateWordFields state ->
      PackedReviewerWordFits n word := by
  cases state <;>
    simp [PackedReviewerSelectStorageFits,
      packedReviewerSelectStateWordFields] at *
  all_goals
    first
    | exact hstate.2.word_fields
    | exact ⟨hstate.2.1, hstate.2.2.word_fields⟩

private theorem PackedReviewerSelectStorageFits.control_fields
    {n : Nat} {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectStorageFits n state) :
    packedReviewerSelectStateControlBounds state := by
  cases state <;>
    simp [PackedReviewerSelectStorageFits,
      packedReviewerSelectStateControlBounds] at *
  all_goals
    first
    | exact hstate.2.control_fields
    | exact hstate.2.2.control_fields

private theorem packedReviewerSelectStart_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index : Nat) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectStart invocation n index) := by
  simp only [packedReviewerSelectStart]
  split <;> simp [PackedReviewerSelectStorageFits]

private theorem packedReviewerSelectAfterSuper_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index : Nat)
    (super : Option GenericSelect.SparseDenseSelectDenseLocalEntry) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterSuper invocation n index super) := by
  cases super with
  | none =>
      simp [packedReviewerSelectAfterSuper, PackedReviewerSelectStorageFits]
  | some entry =>
      simp only [packedReviewerSelectAfterSuper]
      split
      · refine ⟨rfl, ?_⟩
        exact packedReviewerRankStart_storage_fits n n invocation .selectLong
          (GenericSelect.selectSuperSlot index (packedSelectSuperStride n))
      · simp [PackedReviewerSelectStorageFits]

private theorem packedReviewerSelectAfterLocal_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index localSlot : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (loc : Option GenericSelect.SparseDenseSelectDenseLocalEntry) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterLocal invocation n index localSlot super loc) := by
  cases loc with
  | none =>
      simp [packedReviewerSelectAfterLocal, PackedReviewerSelectStorageFits]
  | some entry =>
      simp only [packedReviewerSelectAfterLocal]
      split
      · refine ⟨rfl, ?_⟩
        exact packedReviewerRankStart_storage_fits n n invocation .selectSparse
          localSlot
      · simp [PackedReviewerSelectStorageFits]

private theorem packedReviewerSelectAfterLongRank_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (exceptionRank : Nat) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterLongRank invocation n index super
        exceptionRank) := by
  simp [packedReviewerSelectAfterLongRank, PackedReviewerSelectStorageFits]

private theorem packedReviewerSelectAfterSparseRank_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index localSlot : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (exceptionRank : Nat) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterSparseRank invocation n index localSlot super loc
        exceptionRank) := by
  simp [packedReviewerSelectAfterSparseRank, PackedReviewerSelectStorageFits]

private theorem packedReviewerSelectAfterDenseUptoRank_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index : Nat)
    (basePosition baseOccurrence beforeFirst : Nat) (word : List Bool)
    (uptoFirst : Nat) (hword : PackedReviewerWordFits n word) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterDenseUptoRank invocation n index basePosition
        baseOccurrence beforeFirst word uptoFirst) := by
  simp only [packedReviewerSelectAfterDenseUptoRank]
  split
  · let select :=
      packedReviewerWordSelectStart invocation n false word
        (beforeFirst + (index - baseOccurrence))
    have hselect : PackedReviewerWordSelectStorageFits n select := by
      simpa [select] using
        packedReviewerWordSelectStart_storage_fits invocation false word
          (beforeFirst + (index - baseOccurrence)) hword
    cases hresult : packedReviewerWordSelectResult select with
    | none =>
        simpa [hresult, PackedReviewerSelectStorageFits, select] using
          (show n = n ∧ PackedReviewerWordSelectStorageFits n select from
            ⟨rfl, hselect⟩)
    | some value =>
        simp [select, hresult, PackedReviewerSelectStorageFits]
  · simp [PackedReviewerSelectStorageFits]

private theorem packedReviewerSelectAfterDenseBeforeRank_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index : Nat)
    (basePosition baseOccurrence : Nat) (word : List Bool)
    (beforeFirst : Nat) (hword : PackedReviewerWordFits n word) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterDenseBeforeRank invocation n index basePosition
        baseOccurrence word beforeFirst) := by
  let rank :=
    packedReviewerRankStartFold invocation .close n word word.length 0
  have hrank : PackedReviewerRankStorageFits n rank := by
    simpa [rank] using
      packedReviewerRankStartFold_storage_fits invocation .close word
        word.length 0 hword
  simp only [packedReviewerSelectAfterDenseBeforeRank]
  cases hresult : packedReviewerRankResult rank with
  | some uptoFirst =>
      simpa [rank, hresult] using
        packedReviewerSelectAfterDenseUptoRank_storage_fits n invocation index
          basePosition baseOccurrence beforeFirst word uptoFirst hword
  | none =>
      simpa [rank, hresult, PackedReviewerSelectStorageFits] using
        (show n = n ∧ PackedReviewerWordFits n word ∧
            PackedReviewerRankStorageFits n rank from
          ⟨rfl, hword, hrank⟩)

private theorem packedReviewerSelectAfterDenseFirstWord_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index : Nat)
    (basePosition baseOccurrence : Nat) (reply : Option (List Bool))
    (hreply : forall word, reply = some word -> PackedReviewerWordFits n word) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterDenseFirstWord invocation n index basePosition
        baseOccurrence reply) := by
  cases reply with
  | none =>
      simp [packedReviewerSelectAfterDenseFirstWord,
        PackedReviewerSelectStorageFits]
  | some word =>
      have hword := hreply word rfl
      let rank :=
        packedReviewerRankStartFold invocation .close n word
          (basePosition - basePosition / packedSelectWordSize n *
            packedSelectWordSize n) 0
      have hrank : PackedReviewerRankStorageFits n rank := by
        simpa [rank] using
          packedReviewerRankStartFold_storage_fits invocation .close word
            (basePosition - basePosition / packedSelectWordSize n *
              packedSelectWordSize n) 0 hword
      simp only [packedReviewerSelectAfterDenseFirstWord]
      cases hresult : packedReviewerRankResult rank with
      | some beforeFirst =>
          simpa [rank, hresult] using
            packedReviewerSelectAfterDenseBeforeRank_storage_fits n invocation
              index basePosition baseOccurrence word beforeFirst hword
      | none =>
          simpa [rank, hresult, PackedReviewerSelectStorageFits] using
            (show n = n ∧ PackedReviewerWordFits n word ∧
                PackedReviewerRankStorageFits n rank from
              ⟨rfl, hword, hrank⟩)

private theorem packedReviewerSelectAfterDenseSecondWord_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (index : Nat)
    (basePosition baseOccurrence beforeFirst uptoFirst : Nat)
    (reply : Option (List Bool))
    (hreply : forall word, reply = some word -> PackedReviewerWordFits n word) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectAfterDenseSecondWord invocation n index basePosition
        baseOccurrence beforeFirst uptoFirst reply) := by
  cases reply with
  | none =>
      simp [packedReviewerSelectAfterDenseSecondWord,
        PackedReviewerSelectStorageFits]
  | some word =>
      have hword := hreply word rfl
      let select :=
        packedReviewerWordSelectStart invocation n false word
          (index - baseOccurrence - (uptoFirst - beforeFirst))
      have hselect : PackedReviewerWordSelectStorageFits n select := by
        simpa [select] using
          packedReviewerWordSelectStart_storage_fits invocation false word
            (index - baseOccurrence - (uptoFirst - beforeFirst)) hword
      simp only [packedReviewerSelectAfterDenseSecondWord]
      cases hresult : packedReviewerWordSelectResult select with
      | none =>
          simpa [select, hresult, PackedReviewerSelectStorageFits] using
            (show n = n ∧ PackedReviewerWordSelectStorageFits n select from
              ⟨rfl, hselect⟩)
      | some value =>
          simp [select, hresult, PackedReviewerSelectStorageFits]

private theorem packedReviewerSelectConsumeReply_storage_fits
    {n : Nat} {state : PackedReviewerSelectState}
    {reply : Option (List Bool)}
    (hstate : PackedReviewerSelectStorageFits n state)
    (hreply : forall word, reply = some word -> PackedReviewerWordFits n word) :
    PackedReviewerSelectStorageFits n
      (packedReviewerSelectConsumeReply state reply) := by
  cases state with
  | superEntry invocation stateN index entry =>
      subst stateN
      simp only [packedReviewerSelectConsumeReply]
      split
      · apply packedReviewerSelectAfterSuper_storage_fits
      · simp [PackedReviewerSelectStorageFits]
  | localEntry invocation stateN index localSlot super entry =>
      subst stateN
      simp only [packedReviewerSelectConsumeReply]
      split
      · apply packedReviewerSelectAfterLocal_storage_fits
      · simp [PackedReviewerSelectStorageFits]
  | longRank invocation stateN index super rank =>
      have hn := hstate.1
      subst stateN
      have hrank := packedReviewerRankConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerSelectConsumeReply]
      split
      · apply packedReviewerSelectAfterLongRank_storage_fits
      · exact ⟨rfl, hrank⟩
  | longRelative invocation base slot =>
      simp [packedReviewerSelectConsumeReply, PackedReviewerSelectStorageFits]
  | sparseRank invocation stateN index localSlot super loc rank =>
      have hn := hstate.1
      subst stateN
      have hrank := packedReviewerRankConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerSelectConsumeReply]
      split
      · apply packedReviewerSelectAfterSparseRank_storage_fits
      · exact ⟨rfl, hrank⟩
  | sparseRelative invocation base slot =>
      simp [packedReviewerSelectConsumeReply, PackedReviewerSelectStorageFits]
  | denseFirstWord invocation stateN index basePosition baseOccurrence =>
      subst stateN
      exact packedReviewerSelectAfterDenseFirstWord_storage_fits n invocation
        index basePosition baseOccurrence reply hreply
  | denseBeforeRank invocation stateN index basePosition baseOccurrence word
        rank =>
      have hn := hstate.1
      subst stateN
      have hrank :=
        packedReviewerRankConsumeReply_storage_fits hstate.2.2 hreply
      simp only [packedReviewerSelectConsumeReply]
      split
      · apply packedReviewerSelectAfterDenseBeforeRank_storage_fits
        exact hstate.2.1
      · exact ⟨rfl, hstate.2.1, hrank⟩
  | denseUptoRank invocation stateN index basePosition baseOccurrence
        beforeFirst word rank =>
      have hn := hstate.1
      subst stateN
      have hrank :=
        packedReviewerRankConsumeReply_storage_fits hstate.2.2 hreply
      simp only [packedReviewerSelectConsumeReply]
      split
      · apply packedReviewerSelectAfterDenseUptoRank_storage_fits
        exact hstate.2.1
      · exact ⟨rfl, hstate.2.1, hrank⟩
  | denseFirstSelect invocation stateN baseWord select =>
      have hn := hstate.1
      subst stateN
      have hselect :=
        packedReviewerWordSelectConsumeReply_storage_fits
          (reply := reply) hstate.2
      simp only [packedReviewerSelectConsumeReply]
      split
      · simp [PackedReviewerSelectStorageFits]
      · exact ⟨rfl, hselect⟩
  | denseSecondWord invocation stateN index basePosition baseOccurrence
        beforeFirst uptoFirst =>
      subst stateN
      exact packedReviewerSelectAfterDenseSecondWord_storage_fits n invocation
        index basePosition baseOccurrence beforeFirst uptoFirst reply hreply
  | denseSecondSelect invocation stateN baseWord select =>
      have hn := hstate.1
      subst stateN
      have hselect :=
        packedReviewerWordSelectConsumeReply_storage_fits
          (reply := reply) hstate.2
      simp only [packedReviewerSelectConsumeReply]
      split
      · simp [PackedReviewerSelectStorageFits]
      · exact ⟨rfl, hselect⟩
  | done value =>
      simp [packedReviewerSelectConsumeReply, PackedReviewerSelectStorageFits]

/-! ## Reachable continuation grammar -/

/--
The recursive continuation type is intentionally larger than the controller's
operational grammar.  These constructor-sensitive side conditions describe
exactly the amount of outer stack on which a transition may install another
two-stage child.
-/
private def PackedReviewerCandidateContinuationSafe :
    PackedReviewerCandidateContinuation -> Prop
  | .finish => True
  | .localTwoLeft _ _ _ _ _ outer
  | .localTwoRight _ outer
  | .globalTwoLeft _ _ _ _ outer
  | .globalTwoRight _ outer =>
      PackedReviewerCandidateContinuationSafe outer ∧
        packedReviewerCandidateContinuationDepth outer <= 1
  | .adjacentLeft _ _ _ outer
  | .leftMiddleLeft _ _ _ outer
  | .crossLeft _ _ _ _ outer
  | .crossMiddle _ _ _ _ _ outer =>
      PackedReviewerCandidateContinuationSafe outer ∧
        packedReviewerCandidateContinuationDepth outer = 0
  | .adjacentRight _ outer
  | .leftMiddleMiddle _ outer
  | .crossRight _ _ outer =>
      PackedReviewerCandidateContinuationSafe outer ∧
        packedReviewerCandidateContinuationDepth outer <= 1

private theorem PackedReviewerCandidateContinuationSafe.depth_le_two
    {continuation : PackedReviewerCandidateContinuation}
    (hcontinuation : PackedReviewerCandidateContinuationSafe continuation) :
    packedReviewerCandidateContinuationDepth continuation <= 2 := by
  cases continuation <;>
    simp [PackedReviewerCandidateContinuationSafe,
      packedReviewerCandidateContinuationDepth] at * <;>
    omega

private def PackedReviewerInteriorNatContinuationSafe :
    PackedReviewerInteriorNatContinuation -> Prop
  | .localLevel _ _ _ _ outer
  | .globalLevel _ _ _ outer =>
      PackedReviewerCandidateContinuationSafe outer ∧
        packedReviewerCandidateContinuationDepth outer <= 1
  | .summaryBaseline _ _ outer
  | .summaryMin _ _ _ outer
  | .summaryMax _ _ _ _ outer
  | .summaryArg _ _ _ _ _ outer
  | .localOffset _ _ _ _ outer
  | .globalBlock _ _ _ outer =>
      PackedReviewerCandidateContinuationSafe outer

private theorem PackedReviewerInteriorNatContinuationSafe.depth_le_three
    {continuation : PackedReviewerInteriorNatContinuation}
    (hcontinuation : PackedReviewerInteriorNatContinuationSafe continuation) :
    packedReviewerInteriorNatContinuationDepth continuation <= 3 := by
  cases continuation <;>
    simp [PackedReviewerInteriorNatContinuationSafe,
      packedReviewerInteriorNatContinuationDepth] at *
  all_goals
    first
    | omega
    | have houter :=
        PackedReviewerCandidateContinuationSafe.depth_le_two
          (by assumption)
      omega

private def PackedReviewerCandidateContinuationSizeConsistent
    (expected : Nat) : PackedReviewerCandidateContinuation -> Prop
  | .finish => True
  | .localTwoLeft n _ _ _ _ outer
  | .globalTwoLeft n _ _ _ outer
  | .adjacentLeft n _ _ outer
  | .leftMiddleLeft n _ _ outer
  | .crossLeft n _ _ _ outer
  | .crossMiddle n _ _ _ _ outer =>
      n = expected ∧
        PackedReviewerCandidateContinuationSizeConsistent expected outer
  | .localTwoRight _ outer
  | .globalTwoRight _ outer
  | .adjacentRight _ outer
  | .leftMiddleMiddle _ outer
  | .crossRight _ _ outer =>
      PackedReviewerCandidateContinuationSizeConsistent expected outer

private def PackedReviewerInteriorNatContinuationSizeConsistent
    (expected : Nat) : PackedReviewerInteriorNatContinuation -> Prop
  | .summaryBaseline n _ outer
  | .summaryMin n _ _ outer
  | .summaryMax n _ _ _ outer
  | .summaryArg n _ _ _ _ outer
  | .localOffset n _ _ _ outer
  | .globalBlock n _ _ outer
  | .localLevel n _ _ _ outer
  | .globalLevel n _ _ outer =>
      n = expected ∧
        PackedReviewerCandidateContinuationSizeConsistent expected outer

private def PackedReviewerInteriorNatStateSizeConsistent
    (expected : Nat) : PackedReviewerInteriorNatState -> Prop
  | .read _ n _ _ _ _ => n = expected
  | .done _ => True

private structure PackedReviewerInteriorStorageFits
    (n : Nat) (state : PackedReviewerInteriorState) : Prop where
  word_fields :
    forall word, word ∈ packedReviewerInteriorStateWordFields state ->
      PackedReviewerWordFits n word
  continuation_safe :
    match state with
    | .readNat _ _ continuation =>
        PackedReviewerInteriorNatContinuationSafe continuation
    | .done _ => True
  counter_sum :
    match state with
    | .readNat _ (.read _ _ _ next remaining repliesRev) _ =>
        next + remaining <= 210 ∧ repliesRev.length = next
    | _ => True
  size_consistent :
    match state with
    | .readNat _ read continuation =>
        PackedReviewerInteriorNatStateSizeConsistent n read ∧
          PackedReviewerInteriorNatContinuationSizeConsistent n continuation
    | .done _ => True
  counter_fields : packedReviewerInteriorStateControlBounds state

private theorem PackedReviewerInteriorStorageFits.continuation_depth
    {n : Nat} {state : PackedReviewerInteriorState}
    (hstate : PackedReviewerInteriorStorageFits n state) :
    packedReviewerInteriorStateContinuationDepth state <= 3 := by
  cases state with
  | readNat invocation read continuation =>
      exact
        PackedReviewerInteriorNatContinuationSafe.depth_le_three
          hstate.continuation_safe
  | done value =>
      simp [packedReviewerInteriorStateContinuationDepth]

private def PackedReviewerInteriorContinuationShapeSafe :
    PackedReviewerInteriorState -> Prop
  | .readNat _ _ continuation =>
      PackedReviewerInteriorNatContinuationSafe continuation
  | .done _ => True

private theorem packedReviewerInteriorFinishCandidate_shape_safe
    (invocation : PackedReviewerInvocation) (value : PackedReviewerCandidate)
    (continuation : PackedReviewerCandidateContinuation)
    (hcontinuation :
      PackedReviewerCandidateContinuationSafe continuation) :
    PackedReviewerInteriorContinuationShapeSafe
      (packedReviewerInteriorFinishCandidate invocation value continuation) := by
  induction continuation generalizing value with
  | finish =>
      simp [packedReviewerInteriorFinishCandidate,
        PackedReviewerInteriorContinuationShapeSafe]
  | localTwoLeft n macroIdx localStart count encoded outer ih =>
      have houter := hcontinuation.1
      have houterDepth := hcontinuation.2
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalSpan,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe,
        PackedReviewerCandidateContinuationSafe,
        houter, houterDepth]
  | localTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
  | globalTwoLeft n macroStart macroSpanCount encoded outer ih =>
      have houter := hcontinuation.1
      have houterDepth := hcontinuation.2
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalSpan,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe,
        PackedReviewerCandidateContinuationSafe,
        houter, houterDepth]
  | globalTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
  | adjacentLeft n macroStart rightCount outer ih =>
      have houter := hcontinuation.1
      have houterDepth := hcontinuation.2
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe,
        PackedReviewerCandidateContinuationSafe,
        packedReviewerCandidateContinuationDepth,
        houter, houterDepth]
  | adjacentRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
  | leftMiddleLeft n macroStart middleCount outer ih =>
      have houter := hcontinuation.1
      have houterDepth := hcontinuation.2
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe,
        PackedReviewerCandidateContinuationSafe,
        packedReviewerCandidateContinuationDepth,
        houter, houterDepth]
  | leftMiddleMiddle left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
  | crossLeft n macroStart middleCount rightCount outer ih =>
      have houter := hcontinuation.1
      have houterDepth := hcontinuation.2
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartGlobalTwo,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe,
        PackedReviewerCandidateContinuationSafe,
        packedReviewerCandidateContinuationDepth,
        houter, houterDepth]
  | crossMiddle n macroStart middleCount rightCount left outer ih =>
      have houter := hcontinuation.1
      have houterDepth := hcontinuation.2
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe,
        PackedReviewerCandidateContinuationSafe,
        packedReviewerCandidateContinuationDepth,
        houter, houterDepth]
  | crossRight left middle outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge3? left middle value)
          hcontinuation.1

private theorem packedReviewerInteriorFinishNat_shape_safe
    (invocation : PackedReviewerInvocation) (value : Option Nat)
    (continuation : PackedReviewerInteriorNatContinuation)
    (hcontinuation : PackedReviewerInteriorNatContinuationSafe continuation) :
    PackedReviewerInteriorContinuationShapeSafe
      (packedReviewerInteriorFinishNat invocation value continuation) := by
  cases continuation with
  | summaryBaseline n block outer =>
      simpa [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe] using hcontinuation
  | summaryMin n block baseline outer =>
      simpa [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe] using hcontinuation
  | summaryMax n block baseline minRel outer =>
      simpa [packedReviewerInteriorFinishNat,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe] using hcontinuation
  | summaryArg n block baseline minRel maxRel outer =>
      apply packedReviewerInteriorFinishCandidate_shape_safe
      simpa [PackedReviewerInteriorNatContinuationSafe] using hcontinuation
  | localOffset n macroIdx localStart level outer =>
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_shape_safe
          simpa [PackedReviewerInteriorNatContinuationSafe] using hcontinuation
      | some offset =>
          simpa [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            PackedReviewerInteriorContinuationShapeSafe,
            PackedReviewerInteriorNatContinuationSafe] using hcontinuation
  | globalBlock n macroStart level outer =>
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_shape_safe
          simpa [PackedReviewerInteriorNatContinuationSafe] using hcontinuation
      | some block =>
          simpa [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartMinCandidate,
            packedReviewerInteriorReadNat,
            PackedReviewerInteriorContinuationShapeSafe,
            PackedReviewerInteriorNatContinuationSafe] using hcontinuation
  | localLevel n macroIdx localStart count outer =>
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_shape_safe
          exact hcontinuation.1
      | some encoded =>
          have houter := hcontinuation.1
          have houterDepth := hcontinuation.2
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartLocalSpan,
            packedReviewerInteriorReadNat,
            PackedReviewerInteriorContinuationShapeSafe,
            PackedReviewerInteriorNatContinuationSafe,
            PackedReviewerCandidateContinuationSafe,
            houter, houterDepth]
  | globalLevel n macroStart macroSpanCount outer =>
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_shape_safe
          exact hcontinuation.1
      | some encoded =>
          have houter := hcontinuation.1
          have houterDepth := hcontinuation.2
          simp [packedReviewerInteriorFinishNat,
            packedReviewerInteriorStartGlobalSpan,
            packedReviewerInteriorReadNat,
            PackedReviewerInteriorContinuationShapeSafe,
            PackedReviewerInteriorNatContinuationSafe,
            PackedReviewerCandidateContinuationSafe,
            houter, houterDepth]

private theorem packedReviewerInteriorNormalize_shape_safe
    (fuel : Nat) (state : PackedReviewerInteriorState)
    (hstate : PackedReviewerInteriorContinuationShapeSafe state) :
    PackedReviewerInteriorContinuationShapeSafe
      (packedReviewerInteriorNormalize fuel state) := by
  induction fuel generalizing state with
  | zero => simpa [packedReviewerInteriorNormalize]
  | succ fuel ih =>
      cases state with
      | done value =>
          simp [packedReviewerInteriorNormalize,
            PackedReviewerInteriorContinuationShapeSafe]
      | readNat invocation read continuation =>
          cases hresult : packedReviewerInteriorNatResult read with
          | none =>
              simpa [packedReviewerInteriorNormalize, hresult,
                PackedReviewerInteriorContinuationShapeSafe] using hstate
          | some value =>
              have hnext :=
                packedReviewerInteriorFinishNat_shape_safe invocation value
                  continuation hstate
              simpa only [packedReviewerInteriorNormalize, hresult] using
                ih (packedReviewerInteriorFinishNat invocation value continuation)
                  hnext

private theorem packedReviewerInteriorStartRaw_shape_safe
    (invocation : PackedReviewerInvocation) (n startBlock count : Nat) :
    PackedReviewerInteriorContinuationShapeSafe
      (packedReviewerInteriorStartRaw invocation n startBlock count) := by
  simp only [packedReviewerInteriorStartRaw]
  split
  · simp [PackedReviewerInteriorContinuationShapeSafe]
  · split
    · simp [packedReviewerInteriorStartLocalTwo,
        packedReviewerInteriorReadNat,
        PackedReviewerInteriorContinuationShapeSafe,
        PackedReviewerInteriorNatContinuationSafe,
        PackedReviewerCandidateContinuationSafe,
        packedReviewerCandidateContinuationDepth]
    · split
      · simp [packedReviewerInteriorStartLocalTwo,
          packedReviewerInteriorReadNat,
          PackedReviewerInteriorContinuationShapeSafe,
          PackedReviewerInteriorNatContinuationSafe,
          PackedReviewerCandidateContinuationSafe,
          packedReviewerCandidateContinuationDepth]
      · split
        · simp [packedReviewerInteriorStartLocalTwo,
            packedReviewerInteriorReadNat,
            PackedReviewerInteriorContinuationShapeSafe,
            PackedReviewerInteriorNatContinuationSafe,
            PackedReviewerCandidateContinuationSafe,
            packedReviewerCandidateContinuationDepth]
        · simp [packedReviewerInteriorStartLocalTwo,
            packedReviewerInteriorReadNat,
            PackedReviewerInteriorContinuationShapeSafe,
            PackedReviewerInteriorNatContinuationSafe,
            PackedReviewerCandidateContinuationSafe,
            packedReviewerCandidateContinuationDepth]

private theorem packedReviewerInteriorStart_shape_safe
    (invocation : PackedReviewerInvocation) (n startBlock count : Nat) :
    PackedReviewerInteriorContinuationShapeSafe
      (packedReviewerInteriorStart invocation n startBlock count) := by
  apply packedReviewerInteriorNormalize_shape_safe
  exact packedReviewerInteriorStartRaw_shape_safe invocation n startBlock count

private theorem packedReviewerInteriorConsumeReply_shape_safe
    (state : PackedReviewerInteriorState) (reply : Option (List Bool))
    (hstate : PackedReviewerInteriorContinuationShapeSafe state) :
    PackedReviewerInteriorContinuationShapeSafe
      (packedReviewerInteriorConsumeReply state reply) := by
  cases state with
  | done value => simpa [packedReviewerInteriorConsumeReply]
  | readNat invocation read continuation =>
      cases hresult : packedReviewerInteriorNatResult
          (packedReviewerInteriorNatConsumeReply read reply) with
      | none =>
          simpa [packedReviewerInteriorConsumeReply, hresult,
            PackedReviewerInteriorContinuationShapeSafe] using hstate
      | some value =>
          have hnext :=
            packedReviewerInteriorFinishNat_shape_safe invocation value
              continuation hstate
          simpa only [packedReviewerInteriorConsumeReply, hresult] using
            packedReviewerInteriorNormalize_shape_safe
              (packedReviewerInteriorRemaining
                  (packedReviewerInteriorFinishNat invocation value continuation) +
                1)
              (packedReviewerInteriorFinishNat invocation value continuation)
              hnext

private theorem packedReviewerInteriorReadState_storage_fits
    {n : Nat} (invocation : PackedReviewerInvocation)
    (read : PackedReviewerInteriorNatState)
    (continuation : PackedReviewerInteriorNatContinuation)
    (hread : PackedReviewerInteriorNatStorageFits n read)
    (hcontinuation :
      PackedReviewerInteriorNatContinuationSafe continuation)
    (hreadSize : PackedReviewerInteriorNatStateSizeConsistent n read)
    (hcontinuationSize :
      PackedReviewerInteriorNatContinuationSizeConsistent n continuation) :
    PackedReviewerInteriorStorageFits n
      (.readNat invocation read continuation) := by
  refine ⟨?_, hcontinuation, ?_, ⟨hreadSize, hcontinuationSize⟩, ?_⟩
  · intro word hmem
    apply hread.word_fields word
    simpa [packedReviewerInteriorStateWordFields] using hmem
  · cases read with
    | read readInvocation stateN start next remaining repliesRev =>
        exact hread.counter_exact
    | done value => trivial
  · exact hread.control_fields

private theorem packedReviewerInteriorReadNat_storage_fits_of_width
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (entryCount width base index : Nat)
    (continuation : PackedReviewerInteriorNatContinuation)
    (hwidth : width <= 7 * packedBpCodeWordWidth shape.size)
    (hcontinuation :
      PackedReviewerInteriorNatContinuationSafe continuation)
    (hcontinuationSize :
      PackedReviewerInteriorNatContinuationSizeConsistent shape.size
        continuation) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorReadNat invocation shape.size entryCount width base
        index continuation) := by
  apply packedReviewerInteriorReadState_storage_fits
  · exact packedReviewerInteriorNatStart_storage_fits_of_width shape invocation
      entryCount width base index hwidth
  · exact hcontinuation
  · simp only [packedReviewerInteriorNatStart]
    split
    · split <;>
        simp [PackedReviewerInteriorNatStateSizeConsistent]
    · simp [PackedReviewerInteriorNatStateSizeConsistent]
  · exact hcontinuationSize

private theorem packedReviewerInteriorStartMinCandidate_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (block : Nat) (outer : PackedReviewerCandidateContinuation)
    (houter : PackedReviewerCandidateContinuationSafe outer)
    (houterSize :
      PackedReviewerCandidateContinuationSizeConsistent shape.size outer) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorStartMinCandidate invocation shape.size block
        outer) := by
  apply packedReviewerInteriorReadNat_storage_fits_of_width
  · omega
  · simpa [PackedReviewerInteriorNatContinuationSafe] using houter
  · simp [PackedReviewerInteriorNatContinuationSizeConsistent, houterSize]

private theorem packedReviewerInteriorStartLocalSpan_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroIdx localStart level : Nat)
    (outer : PackedReviewerCandidateContinuation)
    (houter : PackedReviewerCandidateContinuationSafe outer)
    (houterSize :
      PackedReviewerCandidateContinuationSizeConsistent shape.size outer) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorStartLocalSpan invocation shape.size macroIdx
        localStart level outer) := by
  apply packedReviewerInteriorReadNat_storage_fits_of_width
  · exact packedReviewerInteriorOffsetWidth_le_seven shape
  · simpa [PackedReviewerInteriorNatContinuationSafe] using houter
  · simp [PackedReviewerInteriorNatContinuationSizeConsistent, houterSize]

private theorem packedReviewerInteriorStartGlobalSpan_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroStart level : Nat) (outer : PackedReviewerCandidateContinuation)
    (houter : PackedReviewerCandidateContinuationSafe outer)
    (houterSize :
      PackedReviewerCandidateContinuationSizeConsistent shape.size outer) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorStartGlobalSpan invocation shape.size macroStart
        level outer) := by
  apply packedReviewerInteriorReadNat_storage_fits_of_width
  · exact packedReviewerInteriorBlockWidth_le_seven shape
  · simpa [PackedReviewerInteriorNatContinuationSafe] using houter
  · simp [PackedReviewerInteriorNatContinuationSizeConsistent, houterSize]

private theorem packedReviewerInteriorStartLocalTwo_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroIdx localStart count : Nat)
    (outer : PackedReviewerCandidateContinuation)
    (houter : PackedReviewerCandidateContinuationSafe outer)
    (houterDepth : packedReviewerCandidateContinuationDepth outer <= 1)
    (houterSize :
      PackedReviewerCandidateContinuationSizeConsistent shape.size outer) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorStartLocalTwo invocation shape.size macroIdx
        localStart count outer) := by
  apply packedReviewerInteriorReadNat_storage_fits_of_width
  · exact packedReviewerInteriorLocalLevelWidth_le_seven shape
  · simpa [PackedReviewerInteriorNatContinuationSafe] using
      And.intro houter houterDepth
  · simp [PackedReviewerInteriorNatContinuationSizeConsistent, houterSize]

private theorem packedReviewerInteriorStartGlobalTwo_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (macroStart macroSpanCount : Nat)
    (outer : PackedReviewerCandidateContinuation)
    (houter : PackedReviewerCandidateContinuationSafe outer)
    (houterDepth : packedReviewerCandidateContinuationDepth outer <= 1)
    (houterSize :
      PackedReviewerCandidateContinuationSizeConsistent shape.size outer) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorStartGlobalTwo invocation shape.size macroStart
        macroSpanCount outer) := by
  apply packedReviewerInteriorReadNat_storage_fits_of_width
  · exact packedReviewerInteriorGlobalLevelWidth_le_seven shape
  · simpa [PackedReviewerInteriorNatContinuationSafe] using
      And.intro houter houterDepth
  · simp [PackedReviewerInteriorNatContinuationSizeConsistent, houterSize]

private theorem packedReviewerInteriorFinishCandidate_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (value : PackedReviewerCandidate)
    (continuation : PackedReviewerCandidateContinuation)
    (hcontinuation : PackedReviewerCandidateContinuationSafe continuation)
    (hcontinuationSize :
      PackedReviewerCandidateContinuationSizeConsistent shape.size
        continuation) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorFinishCandidate invocation value continuation) := by
  induction continuation generalizing value with
  | finish =>
      simp only [packedReviewerInteriorFinishCandidate]
      refine ⟨?_, trivial, trivial, trivial, trivial⟩
      simp [packedReviewerInteriorFinishCandidate,
        packedReviewerInteriorStateWordFields]
  | localTwoLeft n macroIdx localStart count encoded outer ih =>
      have hn := hcontinuationSize.1
      subst n
      simp only [packedReviewerInteriorFinishCandidate]
      apply packedReviewerInteriorStartLocalSpan_storage_fits
      · simpa [PackedReviewerCandidateContinuationSafe] using hcontinuation
      · simpa [PackedReviewerCandidateContinuationSizeConsistent] using
          hcontinuationSize
  | localTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
          hcontinuationSize
  | globalTwoLeft n macroStart macroSpanCount encoded outer ih =>
      have hn := hcontinuationSize.1
      subst n
      simp only [packedReviewerInteriorFinishCandidate]
      apply packedReviewerInteriorStartGlobalSpan_storage_fits
      · simpa [PackedReviewerCandidateContinuationSafe] using hcontinuation
      · simpa [PackedReviewerCandidateContinuationSizeConsistent] using
          hcontinuationSize
  | globalTwoRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
          hcontinuationSize
  | adjacentLeft n macroStart rightCount outer ih =>
      have hn := hcontinuationSize.1
      subst n
      have houter : PackedReviewerCandidateContinuationSafe outer :=
        hcontinuation.1
      have houterDepth :
          packedReviewerCandidateContinuationDepth outer = 0 :=
        hcontinuation.2
      simp only [packedReviewerInteriorFinishCandidate]
      apply packedReviewerInteriorStartLocalTwo_storage_fits
      · simp [PackedReviewerCandidateContinuationSafe, houter,
          houterDepth]
      · simp [packedReviewerCandidateContinuationDepth, houterDepth]
      · simp [PackedReviewerCandidateContinuationSizeConsistent,
          hcontinuationSize.2]
  | adjacentRight left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
          hcontinuationSize
  | leftMiddleLeft n macroStart middleCount outer ih =>
      have hn := hcontinuationSize.1
      subst n
      have houter : PackedReviewerCandidateContinuationSafe outer :=
        hcontinuation.1
      have houterDepth :
          packedReviewerCandidateContinuationDepth outer = 0 :=
        hcontinuation.2
      simp only [packedReviewerInteriorFinishCandidate]
      apply packedReviewerInteriorStartGlobalTwo_storage_fits
      · simp [PackedReviewerCandidateContinuationSafe, houter,
          houterDepth]
      · simp [packedReviewerCandidateContinuationDepth, houterDepth]
      · simp [PackedReviewerCandidateContinuationSizeConsistent,
          hcontinuationSize.2]
  | leftMiddleMiddle left outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge? left value) hcontinuation.1
          hcontinuationSize
  | crossLeft n macroStart middleCount rightCount outer ih =>
      have hn := hcontinuationSize.1
      subst n
      have houter : PackedReviewerCandidateContinuationSafe outer :=
        hcontinuation.1
      have houterDepth :
          packedReviewerCandidateContinuationDepth outer = 0 :=
        hcontinuation.2
      simp only [packedReviewerInteriorFinishCandidate]
      apply packedReviewerInteriorStartGlobalTwo_storage_fits
      · simp [PackedReviewerCandidateContinuationSafe, houter,
          houterDepth]
      · simp [packedReviewerCandidateContinuationDepth, houterDepth]
      · simpa [PackedReviewerCandidateContinuationSizeConsistent] using
          hcontinuationSize
  | crossMiddle n macroStart middleCount rightCount left outer ih =>
      have hn := hcontinuationSize.1
      subst n
      have houter : PackedReviewerCandidateContinuationSafe outer :=
        hcontinuation.1
      have houterDepth :
          packedReviewerCandidateContinuationDepth outer = 0 :=
        hcontinuation.2
      simp only [packedReviewerInteriorFinishCandidate]
      apply packedReviewerInteriorStartLocalTwo_storage_fits
      · simp [PackedReviewerCandidateContinuationSafe, houter,
          houterDepth]
      · simp [packedReviewerCandidateContinuationDepth, houterDepth]
      · simp [PackedReviewerCandidateContinuationSizeConsistent,
          hcontinuationSize.2]
  | crossRight left middle outer ih =>
      simpa [packedReviewerInteriorFinishCandidate] using
        ih (SuccinctClose.bpCandidateMerge3? left middle value) hcontinuation.1
          hcontinuationSize

private theorem packedReviewerInteriorFinishNat_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (value : Option Nat) (continuation : PackedReviewerInteriorNatContinuation)
    (hcontinuation : PackedReviewerInteriorNatContinuationSafe continuation)
    (hcontinuationSize :
      PackedReviewerInteriorNatContinuationSizeConsistent shape.size
        continuation) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorFinishNat invocation value continuation) := by
  cases continuation with
  | summaryBaseline n block outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      apply packedReviewerInteriorReadNat_storage_fits_of_width
      · exact packedReviewerInteriorRelativeWidth_le_seven shape
      · simpa [PackedReviewerInteriorNatContinuationSafe] using hcontinuation
      · simp [PackedReviewerInteriorNatContinuationSizeConsistent,
          hcontinuationSize.2]
  | summaryMin n block baseline outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      apply packedReviewerInteriorReadNat_storage_fits_of_width
      · exact packedReviewerInteriorRelativeWidth_le_seven shape
      · simpa [PackedReviewerInteriorNatContinuationSafe] using hcontinuation
      · simp [PackedReviewerInteriorNatContinuationSizeConsistent,
          hcontinuationSize.2]
  | summaryMax n block baseline minRel outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      apply packedReviewerInteriorReadNat_storage_fits_of_width
      · exact packedReviewerInteriorRelativeWidth_le_seven shape
      · simpa [PackedReviewerInteriorNatContinuationSafe] using hcontinuation
      · simp [PackedReviewerInteriorNatContinuationSizeConsistent,
          hcontinuationSize.2]
  | summaryArg n block baseline minRel maxRel outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      apply packedReviewerInteriorFinishCandidate_storage_fits
      · simpa [PackedReviewerInteriorNatContinuationSafe] using hcontinuation
      · exact hcontinuationSize.2
  | localOffset n macroIdx localStart level outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_storage_fits
          · simpa [PackedReviewerInteriorNatContinuationSafe] using
              hcontinuation
          · exact hcontinuationSize.2
      | some offset =>
          apply packedReviewerInteriorStartMinCandidate_storage_fits
          · simpa [PackedReviewerInteriorNatContinuationSafe] using
              hcontinuation
          · exact hcontinuationSize.2
  | globalBlock n macroStart level outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_storage_fits
          · simpa [PackedReviewerInteriorNatContinuationSafe] using
              hcontinuation
          · exact hcontinuationSize.2
      | some block =>
          apply packedReviewerInteriorStartMinCandidate_storage_fits
          · simpa [PackedReviewerInteriorNatContinuationSafe] using
              hcontinuation
          · exact hcontinuationSize.2
  | localLevel n macroIdx localStart count outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_storage_fits
          · exact hcontinuation.1
          · exact hcontinuationSize.2
      | some encoded =>
          apply packedReviewerInteriorStartLocalSpan_storage_fits
          · simpa [PackedReviewerCandidateContinuationSafe] using hcontinuation
          · simp [PackedReviewerCandidateContinuationSizeConsistent,
              hcontinuationSize.2]
  | globalLevel n macroStart macroSpanCount outer =>
      simp only [packedReviewerInteriorFinishNat]
      have hn := hcontinuationSize.1
      subst n
      cases value with
      | none =>
          apply packedReviewerInteriorFinishCandidate_storage_fits
          · exact hcontinuation.1
          · exact hcontinuationSize.2
      | some encoded =>
          apply packedReviewerInteriorStartGlobalSpan_storage_fits
          · simpa [PackedReviewerCandidateContinuationSafe] using hcontinuation
          · simp [PackedReviewerCandidateContinuationSizeConsistent,
              hcontinuationSize.2]

private theorem packedReviewerInteriorNormalize_storage_fits
    (shape : CartesianShape) (fuel : Nat) (state : PackedReviewerInteriorState)
    (hstate : PackedReviewerInteriorStorageFits shape.size state) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorNormalize fuel state) := by
  induction fuel generalizing state with
  | zero => simpa [packedReviewerInteriorNormalize]
  | succ fuel ih =>
      cases state with
      | done value =>
          simpa [packedReviewerInteriorNormalize] using hstate
      | readNat invocation read continuation =>
          cases hresult : packedReviewerInteriorNatResult read with
          | none =>
              simpa [packedReviewerInteriorNormalize, hresult] using hstate
          | some value =>
              have hnext :=
                packedReviewerInteriorFinishNat_storage_fits shape invocation
                  value continuation hstate.continuation_safe
                  hstate.size_consistent.2
              simpa only [packedReviewerInteriorNormalize, hresult] using
                ih (packedReviewerInteriorFinishNat invocation value continuation)
                  hnext

private theorem packedReviewerInteriorStartRaw_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock count : Nat) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorStartRaw invocation shape.size startBlock count) := by
  simp only [packedReviewerInteriorStartRaw]
  split
  · refine ⟨?_, trivial, trivial, trivial, trivial⟩
    simp [packedReviewerInteriorStateWordFields]
  · split
    · apply packedReviewerInteriorStartLocalTwo_storage_fits
      · simp [PackedReviewerCandidateContinuationSafe]
      · simp [packedReviewerCandidateContinuationDepth]
      · simp [PackedReviewerCandidateContinuationSizeConsistent]
    · split
      · apply packedReviewerInteriorStartLocalTwo_storage_fits
        · simp [PackedReviewerCandidateContinuationSafe,
            packedReviewerCandidateContinuationDepth]
        · simp [packedReviewerCandidateContinuationDepth]
        · simp [PackedReviewerCandidateContinuationSizeConsistent]
      · split
        · apply packedReviewerInteriorStartLocalTwo_storage_fits
          · simp [PackedReviewerCandidateContinuationSafe,
              packedReviewerCandidateContinuationDepth]
          · simp [packedReviewerCandidateContinuationDepth]
          · simp [PackedReviewerCandidateContinuationSizeConsistent]
        · apply packedReviewerInteriorStartLocalTwo_storage_fits
          · simp [PackedReviewerCandidateContinuationSafe,
              packedReviewerCandidateContinuationDepth]
          · simp [packedReviewerCandidateContinuationDepth]
          · simp [PackedReviewerCandidateContinuationSizeConsistent]

private theorem packedReviewerInteriorStart_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (startBlock count : Nat) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorStart invocation shape.size startBlock count) := by
  apply packedReviewerInteriorNormalize_storage_fits
  exact packedReviewerInteriorStartRaw_storage_fits shape invocation startBlock
    count

private theorem packedReviewerInteriorNatConsumeReply_size_consistent
    {n : Nat} (state : PackedReviewerInteriorNatState)
    (reply : Option (List Bool))
    (hstate : PackedReviewerInteriorNatStateSizeConsistent n state) :
    PackedReviewerInteriorNatStateSizeConsistent n
      (packedReviewerInteriorNatConsumeReply state reply) := by
  cases state with
  | done value =>
      simp [packedReviewerInteriorNatConsumeReply,
        PackedReviewerInteriorNatStateSizeConsistent]
  | read invocation stateN start next remaining repliesRev =>
      subst stateN
      cases remaining with
      | zero =>
          simp [packedReviewerInteriorNatConsumeReply,
            PackedReviewerInteriorNatStateSizeConsistent]
      | succ remaining =>
          by_cases hlast : remaining = 0 <;>
            simp [packedReviewerInteriorNatConsumeReply, hlast,
              PackedReviewerInteriorNatStateSizeConsistent]

private theorem packedReviewerInteriorConsumeReply_storage_fits
    (shape : CartesianShape) (state : PackedReviewerInteriorState)
    (reply : Option (List Bool))
    (hstate : PackedReviewerInteriorStorageFits shape.size state)
    (hreply : forall word, reply = some word ->
      PackedReviewerWordFits shape.size word) :
    PackedReviewerInteriorStorageFits shape.size
      (packedReviewerInteriorConsumeReply state reply) := by
  cases state with
  | done value =>
      simpa [packedReviewerInteriorConsumeReply] using hstate
  | readNat invocation read continuation =>
      have hread : PackedReviewerInteriorNatStorageFits shape.size read := by
        refine ⟨?_, ?_⟩
        · intro word hmem
          apply hstate.word_fields word
          simpa [packedReviewerInteriorStateWordFields] using hmem
        · cases read with
          | read readInvocation stateN start next remaining repliesRev =>
              exact hstate.counter_sum
          | done value => trivial
      have hread' :=
        packedReviewerInteriorNatConsumeReply_storage_fits hread hreply
      have hreadSize' :=
        packedReviewerInteriorNatConsumeReply_size_consistent read reply
          hstate.size_consistent.1
      cases hresult : packedReviewerInteriorNatResult
          (packedReviewerInteriorNatConsumeReply read reply) with
      | none =>
          simpa [packedReviewerInteriorConsumeReply, hresult] using
            packedReviewerInteriorReadState_storage_fits invocation
              (packedReviewerInteriorNatConsumeReply read reply) continuation
              hread' hstate.continuation_safe hreadSize'
              hstate.size_consistent.2
      | some value =>
          have hnext :=
            packedReviewerInteriorFinishNat_storage_fits shape invocation value
              continuation hstate.continuation_safe hstate.size_consistent.2
          simpa only [packedReviewerInteriorConsumeReply, hresult] using
            packedReviewerInteriorNormalize_storage_fits shape
              (packedReviewerInteriorRemaining
                  (packedReviewerInteriorFinishNat invocation value continuation) +
                1)
              (packedReviewerInteriorFinishNat invocation value continuation)
              hnext

private def PackedReviewerLcaContinuationShapeSafe :
    PackedReviewerLcaState -> Prop
  | .middle _ _ _ _ _ interior =>
      PackedReviewerInteriorContinuationShapeSafe interior
  | _ => True

private theorem PackedReviewerLcaContinuationShapeSafe.depth_le_three
    {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaContinuationShapeSafe state) :
    packedReviewerLcaStateContinuationDepth state <= 3 := by
  cases state <;>
    simp [PackedReviewerLcaContinuationShapeSafe,
      packedReviewerLcaStateContinuationDepth] at *
  case middle invocation n leftClose rightClose left interior =>
    cases interior with
    | readNat readInvocation read continuation =>
        exact
          PackedReviewerInteriorNatContinuationSafe.depth_le_three hstate
    | done value =>
        simp [packedReviewerInteriorStateContinuationDepth]

private theorem packedReviewerLcaStart_shape_safe
    (n leftClose rightClose : Nat) :
    PackedReviewerLcaContinuationShapeSafe
      (packedReviewerLcaStart n leftClose rightClose) := by
  simp only [packedReviewerLcaStart]
  split <;> simp [PackedReviewerLcaContinuationShapeSafe]

private theorem packedReviewerLcaStartMiddle_shape_safe
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose : Nat) (left : PackedReviewerCandidate) :
    PackedReviewerLcaContinuationShapeSafe
      (packedReviewerLcaStartMiddle invocation n leftClose rightClose left) := by
  simp only [packedReviewerLcaStartMiddle]
  split
  · split
    · simp [packedReviewerLcaStartRightSeed,
        PackedReviewerLcaContinuationShapeSafe]
    · simpa [PackedReviewerLcaContinuationShapeSafe] using
        packedReviewerInteriorStart_shape_safe invocation n
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n) leftClose + 1)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n) rightClose -
            SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n) leftClose - 1)
  · simp [packedReviewerLcaStartRightSeed,
      PackedReviewerLcaContinuationShapeSafe]

private theorem packedReviewerLcaConsumeReply_shape_safe
    (state : PackedReviewerLcaState) (reply : Option (List Bool))
    (hstate : PackedReviewerLcaContinuationShapeSafe state) :
    PackedReviewerLcaContinuationShapeSafe
      (packedReviewerLcaConsumeReply state reply) := by
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      simp only [packedReviewerLcaConsumeReply]
      split <;>
        simp [packedReviewerLcaStartSameWindow,
          PackedReviewerLcaContinuationShapeSafe]
  | sameWindow invocation n leftClose rightClose seed window =>
      simp only [packedReviewerLcaConsumeReply]
      split <;>
        simp [packedReviewerLcaStartSameFringe,
          PackedReviewerLcaContinuationShapeSafe]
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      simp only [packedReviewerLcaConsumeReply]
      split <;> simp [PackedReviewerLcaContinuationShapeSafe]
  | leftSeed invocation n leftClose rightClose rank =>
      simp only [packedReviewerLcaConsumeReply]
      split <;>
        simp [packedReviewerLcaStartLeftWindow,
          PackedReviewerLcaContinuationShapeSafe]
  | leftWindow invocation n leftClose rightClose seed window =>
      simp only [packedReviewerLcaConsumeReply]
      split <;>
        simp [packedReviewerLcaStartLeftFringe,
          PackedReviewerLcaContinuationShapeSafe]
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      simp only [packedReviewerLcaConsumeReply]
      split
      · exact packedReviewerLcaStartMiddle_shape_safe invocation n leftClose
          rightClose _
      · simp [PackedReviewerLcaContinuationShapeSafe]
  | middle invocation n leftClose rightClose left interior =>
      simp only [packedReviewerLcaConsumeReply]
      split
      · simp [packedReviewerLcaStartRightSeed,
          PackedReviewerLcaContinuationShapeSafe]
      · simpa [PackedReviewerLcaContinuationShapeSafe] using
          packedReviewerInteriorConsumeReply_shape_safe interior reply hstate
  | rightSeed invocation n leftClose rightClose left middle rank =>
      simp only [packedReviewerLcaConsumeReply]
      split <;>
        simp [packedReviewerLcaStartRightWindow,
          PackedReviewerLcaContinuationShapeSafe]
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      simp only [packedReviewerLcaConsumeReply]
      split <;>
        simp [packedReviewerLcaStartRightFringe,
          PackedReviewerLcaContinuationShapeSafe]
  | rightFringe invocation n leftClose rightClose seed base start left middle
        fringe =>
      simp only [packedReviewerLcaConsumeReply]
      split <;> simp [PackedReviewerLcaContinuationShapeSafe]
  | done value =>
      simp [packedReviewerLcaConsumeReply,
        PackedReviewerLcaContinuationShapeSafe]

private def PackedReviewerLcaStorageFits
    (n : Nat) : PackedReviewerLcaState -> Prop
  | .sameSeed _ stateN _ _ rank
  | .leftSeed _ stateN _ _ rank
  | .rightSeed _ stateN _ _ _ _ rank =>
      stateN = n ∧ PackedReviewerRankStorageFits n rank
  | .sameWindow _ stateN _ _ _ window
  | .leftWindow _ stateN _ _ _ window
  | .rightWindow _ stateN _ _ _ _ _ window =>
      stateN = n ∧ PackedReviewerBPWindowStorageFits n window
  | .sameFringe _ stateN _ _ _ _ _ fringe
  | .leftFringe _ stateN _ _ _ _ _ fringe
  | .rightFringe _ stateN _ _ _ _ _ _ _ fringe =>
      stateN = n ∧ PackedReviewerFringeStorageFits n fringe
  | .middle _ stateN _ _ _ interior =>
      stateN = n ∧ PackedReviewerInteriorStorageFits n interior
  | .done _ => True

private theorem PackedReviewerLcaStorageFits.word_fields
    {n : Nat} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaStorageFits n state) :
    forall word, word ∈ packedReviewerLcaStateWordFields state ->
      PackedReviewerWordFits n word := by
  cases state <;>
    simp [PackedReviewerLcaStorageFits,
      packedReviewerLcaStateWordFields] at *
  all_goals
    first
    | exact hstate.2.word_fields
    | intro word hmem
      contradiction

private theorem PackedReviewerLcaStorageFits.wide_fields
    {n : Nat} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaStorageFits n state) :
    forall bits, bits ∈ packedReviewerLcaStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth n := by
  cases state <;>
    simp [PackedReviewerLcaStorageFits,
      packedReviewerLcaStateWideFields] at *
  all_goals
    first
    | exact hstate.2.wide_fields
    | intro bits hmem
      contradiction

private theorem PackedReviewerLcaStorageFits.control_fields
    {n : Nat} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaStorageFits n state) :
    packedReviewerLcaStateControlBounds state := by
  cases state <;>
    simp [PackedReviewerLcaStorageFits,
      packedReviewerLcaStateControlBounds] at *
  all_goals
    first
    | exact hstate.2.control_fields
    | exact hstate.2.counter_fields
    | trivial

private theorem PackedReviewerLcaStorageFits.continuation_depth
    {n : Nat} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaStorageFits n state) :
    packedReviewerLcaStateContinuationDepth state <= 3 := by
  cases state <;>
    simp [PackedReviewerLcaStorageFits,
      packedReviewerLcaStateContinuationDepth] at *
  case middle invocation stateN leftClose rightClose left interior =>
    exact hstate.2.continuation_depth

private theorem packedReviewerLcaRankStart_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation) (pos : Nat) :
    PackedReviewerRankStorageFits n
      (packedReviewerLcaRankStart invocation n pos) := by
  simpa [packedReviewerLcaRankStart] using
    packedReviewerRankStart_storage_fits n n invocation .close pos

private theorem packedReviewerLcaStart_storage_fits
    (n leftClose rightClose : Nat) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStart n leftClose rightClose) := by
  simp only [packedReviewerLcaStart]
  split <;>
    exact ⟨rfl, packedReviewerLcaRankStart_storage_fits n _ _⟩

private theorem packedReviewerLcaStartSameWindow_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (leftClose rightClose rankFalse : Nat) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStartSameWindow invocation n leftClose rightClose
        rankFalse) := by
  simpa [packedReviewerLcaStartSameWindow, PackedReviewerLcaStorageFits] using
    (show n = n ∧ PackedReviewerBPWindowStorageFits n
        (packedReviewerBPWindowStart invocation n
          (packedSummaryBlockSizeRaw n) leftClose) from
      ⟨rfl, packedReviewerBPWindowStart_storage_fits n invocation
        (packedSummaryBlockSizeRaw n) leftClose⟩)

private theorem packedReviewerLcaStartSameFringe_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (window : List Bool)
    (hwindow : window.length <= 4 * packedReviewerCellWidth n) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStartSameFringe invocation n leftClose rightClose seed
        window) := by
  simp only [packedReviewerLcaStartSameFringe]
  refine ⟨rfl, ?_⟩
  apply packedReviewerFringeStart_storage_fits
  · exact hwindow
  · exact Nat.min_le_right _ 33

private theorem packedReviewerLcaStartLeftWindow_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (leftClose rightClose rankFalse : Nat) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStartLeftWindow invocation n leftClose rightClose
        rankFalse) := by
  simpa [packedReviewerLcaStartLeftWindow, PackedReviewerLcaStorageFits] using
    (show n = n ∧ PackedReviewerBPWindowStorageFits n
        (packedReviewerBPWindowStart invocation n
          (packedSummaryBlockSizeRaw n) leftClose) from
      ⟨rfl, packedReviewerBPWindowStart_storage_fits n invocation
        (packedSummaryBlockSizeRaw n) leftClose⟩)

private theorem packedReviewerLcaStartLeftFringe_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (window : List Bool)
    (hwindow : window.length <= 4 * packedReviewerCellWidth n) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStartLeftFringe invocation n leftClose rightClose seed
        window) := by
  simp only [packedReviewerLcaStartLeftFringe]
  refine ⟨rfl, ?_⟩
  apply packedReviewerFringeStart_storage_fits
  · exact hwindow
  · exact Nat.min_le_right _ 33

private theorem packedReviewerLcaStartRightSeed_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (left middle : PackedReviewerCandidate) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStartRightSeed invocation n leftClose rightClose left
        middle) := by
  simpa [packedReviewerLcaStartRightSeed, PackedReviewerLcaStorageFits] using
    (show n = n ∧ PackedReviewerRankStorageFits n
        (packedReviewerLcaRankStart invocation n
          (packedLocalBPWindowBase n (packedSummaryBlockSizeRaw n)
            rightClose)) from
      ⟨rfl, packedReviewerLcaRankStart_storage_fits n invocation
        (packedLocalBPWindowBase n (packedSummaryBlockSizeRaw n) rightClose)⟩)

private theorem packedReviewerLcaStartMiddle_storage_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (left : PackedReviewerCandidate) :
    PackedReviewerLcaStorageFits shape.size
      (packedReviewerLcaStartMiddle invocation shape.size leftClose rightClose
        left) := by
  simp only [packedReviewerLcaStartMiddle]
  split
  · let interior :=
      packedReviewerInteriorStart invocation shape.size
        (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            leftClose + 1)
        (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            rightClose -
          SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            leftClose - 1)
    have hinterior : PackedReviewerInteriorStorageFits shape.size interior := by
      simpa [interior] using
        packedReviewerInteriorStart_storage_fits shape invocation
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              leftClose + 1)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              rightClose -
            SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              leftClose - 1)
    cases hresult : packedReviewerInteriorResult interior with
    | some middle =>
        simpa [interior, hresult] using
          packedReviewerLcaStartRightSeed_storage_fits shape.size invocation
            leftClose rightClose left middle
    | none =>
        simpa [interior, hresult, PackedReviewerLcaStorageFits] using
          (show shape.size = shape.size ∧
              PackedReviewerInteriorStorageFits shape.size interior from
            ⟨rfl, hinterior⟩)
  · exact packedReviewerLcaStartRightSeed_storage_fits shape.size invocation
      leftClose rightClose left none

private theorem packedReviewerLcaStartRightWindow_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (leftClose rightClose rankFalse : Nat)
    (left middle : PackedReviewerCandidate) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStartRightWindow invocation n leftClose rightClose
        rankFalse left middle) := by
  simpa [packedReviewerLcaStartRightWindow, PackedReviewerLcaStorageFits] using
    (show n = n ∧ PackedReviewerBPWindowStorageFits n
        (packedReviewerBPWindowStart invocation n
          (packedSummaryBlockSizeRaw n) rightClose) from
      ⟨rfl, packedReviewerBPWindowStart_storage_fits n invocation
        (packedSummaryBlockSizeRaw n) rightClose⟩)

private theorem packedReviewerLcaStartRightFringe_storage_fits
    (n : Nat) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (left middle : PackedReviewerCandidate)
    (window : List Bool)
    (hwindow : window.length <= 4 * packedReviewerCellWidth n) :
    PackedReviewerLcaStorageFits n
      (packedReviewerLcaStartRightFringe invocation n leftClose rightClose seed
        left middle window) := by
  simp only [packedReviewerLcaStartRightFringe]
  refine ⟨rfl, ?_⟩
  apply packedReviewerFringeStart_storage_fits
  · exact hwindow
  · exact Nat.min_le_right _ 33

private theorem packedReviewerBPWindowResult_mem_wideFields
    (state : PackedReviewerBPWindowState) {bits : List Bool}
    (hresult : packedReviewerBPWindowResult state = some bits) :
    bits ∈ packedReviewerBPWindowStateWideFields state := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      simp [packedReviewerBPWindowResult] at hresult
  | done stored =>
      simp [packedReviewerBPWindowResult] at hresult
      subst bits
      simp [packedReviewerBPWindowStateWideFields]

private theorem packedReviewerLcaConsumeReply_storage_fits
    (shape : CartesianShape) (state : PackedReviewerLcaState)
    (reply : Option (List Bool)) (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerLcaNextRequest state = some request)
    (hstate : PackedReviewerLcaStorageFits shape.size state)
    (hreply : forall word, reply = some word ->
      PackedReviewerWordFits shape.size word) :
    PackedReviewerLcaStorageFits shape.size
      (packedReviewerLcaConsumeReply state reply) := by
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      have hn := hstate.1
      subst n
      have hrank := packedReviewerRankConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerLcaConsumeReply]
      split
      · apply packedReviewerLcaStartSameWindow_storage_fits
      · exact ⟨rfl, hrank⟩
  | sameWindow invocation n leftClose rightClose seed window =>
      have hn := hstate.1
      subst n
      have hwindowRequest :
          packedReviewerBPWindowNextRequest window = some request := by
        simpa [packedReviewerLcaNextRequest] using hrequest
      have hwindow :=
        packedReviewerBPWindowConsumeReply_storage_fits hstate.2
          hwindowRequest hreply
      simp only [packedReviewerLcaConsumeReply]
      cases hresult : packedReviewerBPWindowResult
          (packedReviewerBPWindowConsumeReply window reply) with
      | none => exact ⟨rfl, hwindow⟩
      | some bits =>
          apply packedReviewerLcaStartSameFringe_storage_fits
          exact hwindow.wide_fields bits
            (packedReviewerBPWindowResult_mem_wideFields _ hresult)
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      have hn := hstate.1
      subst n
      have hfringe :=
        packedReviewerFringeConsumeReply_storage_fits (reply := reply) hstate.2
      simp only [packedReviewerLcaConsumeReply]
      split
      · simp [PackedReviewerLcaStorageFits]
      · exact ⟨rfl, hfringe⟩
  | leftSeed invocation n leftClose rightClose rank =>
      have hn := hstate.1
      subst n
      have hrank := packedReviewerRankConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerLcaConsumeReply]
      split
      · apply packedReviewerLcaStartLeftWindow_storage_fits
      · exact ⟨rfl, hrank⟩
  | leftWindow invocation n leftClose rightClose seed window =>
      have hn := hstate.1
      subst n
      have hwindowRequest :
          packedReviewerBPWindowNextRequest window = some request := by
        simpa [packedReviewerLcaNextRequest] using hrequest
      have hwindow :=
        packedReviewerBPWindowConsumeReply_storage_fits hstate.2
          hwindowRequest hreply
      simp only [packedReviewerLcaConsumeReply]
      cases hresult : packedReviewerBPWindowResult
          (packedReviewerBPWindowConsumeReply window reply) with
      | none => exact ⟨rfl, hwindow⟩
      | some bits =>
          apply packedReviewerLcaStartLeftFringe_storage_fits
          exact hwindow.wide_fields bits
            (packedReviewerBPWindowResult_mem_wideFields _ hresult)
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      have hn := hstate.1
      subst n
      have hfringe :=
        packedReviewerFringeConsumeReply_storage_fits (reply := reply) hstate.2
      simp only [packedReviewerLcaConsumeReply]
      split
      · apply packedReviewerLcaStartMiddle_storage_fits shape
      · exact ⟨rfl, hfringe⟩
  | middle invocation n leftClose rightClose left interior =>
      have hn := hstate.1
      subst n
      have hinterior := packedReviewerInteriorConsumeReply_storage_fits shape
        interior reply hstate.2 hreply
      simp only [packedReviewerLcaConsumeReply]
      split
      · apply packedReviewerLcaStartRightSeed_storage_fits
      · exact ⟨rfl, hinterior⟩
  | rightSeed invocation n leftClose rightClose left middle rank =>
      have hn := hstate.1
      subst n
      have hrank := packedReviewerRankConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerLcaConsumeReply]
      split
      · apply packedReviewerLcaStartRightWindow_storage_fits
      · exact ⟨rfl, hrank⟩
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      have hn := hstate.1
      subst n
      have hwindowRequest :
          packedReviewerBPWindowNextRequest window = some request := by
        simpa [packedReviewerLcaNextRequest] using hrequest
      have hwindow :=
        packedReviewerBPWindowConsumeReply_storage_fits hstate.2
          hwindowRequest hreply
      simp only [packedReviewerLcaConsumeReply]
      cases hresult : packedReviewerBPWindowResult
          (packedReviewerBPWindowConsumeReply window reply) with
      | none => exact ⟨rfl, hwindow⟩
      | some bits =>
          apply packedReviewerLcaStartRightFringe_storage_fits
          exact hwindow.wide_fields bits
            (packedReviewerBPWindowResult_mem_wideFields _ hresult)
  | rightFringe invocation n leftClose rightClose seed base start left middle
        fringe =>
      have hn := hstate.1
      subst n
      have hfringe :=
        packedReviewerFringeConsumeReply_storage_fits (reply := reply) hstate.2
      simp only [packedReviewerLcaConsumeReply]
      split
      · simp [PackedReviewerLcaStorageFits]
      · exact ⟨rfl, hfringe⟩
  | done value =>
      simp [packedReviewerLcaConsumeReply, PackedReviewerLcaStorageFits]

private def PackedReviewerWholeContinuationShapeSafe :
    PackedReviewerWholeState -> Prop
  | .lcaClose _ _ _ _ _ lca => PackedReviewerLcaContinuationShapeSafe lca
  | _ => True

private theorem PackedReviewerWholeContinuationShapeSafe.depth_le_three
    {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeContinuationShapeSafe state) :
    packedReviewerWholeStateContinuationDepth state <= 3 := by
  cases state with
  | leftSelect n left right select =>
      simp [packedReviewerWholeStateContinuationDepth]
  | rightSelect n left right leftClose select =>
      simp [packedReviewerWholeStateContinuationDepth]
  | lcaClose n left right leftClose rightClose lca =>
      exact PackedReviewerLcaContinuationShapeSafe.depth_le_three hstate
  | finalRank n left right answerClose rank =>
      simp [packedReviewerWholeStateContinuationDepth]
  | done value =>
      simp [packedReviewerWholeStateContinuationDepth]

private theorem packedReviewerWholeStart_shape_safe
    (n left right : Nat) :
    PackedReviewerWholeContinuationShapeSafe
      (packedReviewerWholeStart n left right) := by
  simp [packedReviewerWholeStart,
    PackedReviewerWholeContinuationShapeSafe]

private theorem packedReviewerWholeAfterRightSelect_shape_safe
    (n left right : Nat) (leftClose rightClose : Option Nat) :
    PackedReviewerWholeContinuationShapeSafe
      (packedReviewerWholeAfterRightSelect n left right leftClose rightClose) := by
  cases leftClose with
  | none =>
      simp [packedReviewerWholeAfterRightSelect,
        PackedReviewerWholeContinuationShapeSafe]
  | some leftValue =>
      cases rightClose with
      | none =>
          simp [packedReviewerWholeAfterRightSelect,
            PackedReviewerWholeContinuationShapeSafe]
      | some rightValue =>
          simpa [packedReviewerWholeAfterRightSelect,
            PackedReviewerWholeContinuationShapeSafe] using
            packedReviewerLcaStart_shape_safe n leftValue rightValue

private theorem packedReviewerWholeConsumeReply_shape_safe
    (state : PackedReviewerWholeState) (reply : Option (List Bool))
    (hstate : PackedReviewerWholeContinuationShapeSafe state) :
    PackedReviewerWholeContinuationShapeSafe
      (packedReviewerWholeConsumeReply state reply) := by
  cases state with
  | leftSelect n left right select =>
      simp only [packedReviewerWholeConsumeReply]
      split <;>
        simp [packedReviewerWholeAfterLeftSelect,
          PackedReviewerWholeContinuationShapeSafe]
  | rightSelect n left right leftClose select =>
      simp only [packedReviewerWholeConsumeReply]
      split
      · apply packedReviewerWholeAfterRightSelect_shape_safe
      · simp [PackedReviewerWholeContinuationShapeSafe]
  | lcaClose n left right leftClose rightClose lca =>
      simp only [packedReviewerWholeConsumeReply]
      cases hresult : packedReviewerLcaResult
          (packedReviewerLcaConsumeReply lca reply) with
      | none =>
          simpa [hresult, PackedReviewerWholeContinuationShapeSafe] using
            packedReviewerLcaConsumeReply_shape_safe lca reply hstate
      | some answerClose =>
          cases answerClose <;>
            simp [hresult, packedReviewerWholeAfterLca,
              PackedReviewerWholeContinuationShapeSafe]
  | finalRank n left right answerClose rank =>
      simp only [packedReviewerWholeConsumeReply]
      split <;> simp [PackedReviewerWholeContinuationShapeSafe]
  | done value =>
      simp [packedReviewerWholeConsumeReply,
        PackedReviewerWholeContinuationShapeSafe]

private def PackedReviewerWholeStorageFits
    (n : Nat) : PackedReviewerWholeState -> Prop
  | .leftSelect stateN _ _ select
  | .rightSelect stateN _ _ _ select =>
      stateN = n ∧ PackedReviewerSelectStorageFits n select
  | .lcaClose stateN _ _ _ _ lca =>
      stateN = n ∧ PackedReviewerLcaStorageFits n lca
  | .finalRank stateN _ _ _ rank =>
      stateN = n ∧ PackedReviewerRankStorageFits n rank
  | .done _ => True

private theorem PackedReviewerWholeStorageFits.word_fields
    {n : Nat} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeStorageFits n state) :
    forall word, word ∈ packedReviewerWholeStateWordFields state ->
      PackedReviewerWordFits n word := by
  cases state <;>
    simp [PackedReviewerWholeStorageFits,
      packedReviewerWholeStateWordFields] at *
  all_goals
    first
    | exact hstate.2.word_fields
    | intro word hmem
      contradiction

private theorem PackedReviewerWholeStorageFits.wide_fields
    {n : Nat} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeStorageFits n state) :
    forall bits, bits ∈ packedReviewerWholeStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth n := by
  cases state <;>
    simp [PackedReviewerWholeStorageFits,
      packedReviewerWholeStateWideFields] at *
  all_goals
    first
    | exact hstate.2.wide_fields
    | intro bits hmem
      contradiction

private theorem PackedReviewerWholeStorageFits.control_fields
    {n : Nat} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeStorageFits n state) :
    packedReviewerWholeStateControlBounds state := by
  cases state <;>
    simp [PackedReviewerWholeStorageFits,
      packedReviewerWholeStateControlBounds] at *
  all_goals
    first
    | exact hstate.2.control_fields
    | trivial

private theorem PackedReviewerWholeStorageFits.continuation_depth
    {n : Nat} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeStorageFits n state) :
    packedReviewerWholeStateContinuationDepth state <= 3 := by
  cases state with
  | leftSelect stateN left right select =>
      simp [packedReviewerWholeStateContinuationDepth]
  | rightSelect stateN left right leftClose select =>
      simp [packedReviewerWholeStateContinuationDepth]
  | lcaClose stateN left right leftClose rightClose lca =>
      exact hstate.2.continuation_depth
  | finalRank stateN left right answerClose rank =>
      simp [packedReviewerWholeStateContinuationDepth]
  | done value =>
      simp [packedReviewerWholeStateContinuationDepth]

private theorem packedReviewerWholeStart_storage_fits
    (n left right : Nat) :
    PackedReviewerWholeStorageFits n
      (packedReviewerWholeStart n left right) := by
  refine ⟨rfl, ?_⟩
  exact packedReviewerSelectStart_storage_fits n
    { instruction := .leftSelect, argument := left } left

private theorem packedReviewerWholeAfterLeftSelect_storage_fits
    (n left right : Nat) (leftClose : Option Nat) :
    PackedReviewerWholeStorageFits n
      (packedReviewerWholeAfterLeftSelect n left right leftClose) := by
  refine ⟨rfl, ?_⟩
  exact packedReviewerSelectStart_storage_fits n
    { instruction := .rightSelect, argument := right - 1 } (right - 1)

private theorem packedReviewerWholeAfterRightSelect_storage_fits
    (n left right : Nat) (leftClose rightClose : Option Nat) :
    PackedReviewerWholeStorageFits n
      (packedReviewerWholeAfterRightSelect n left right leftClose rightClose) := by
  cases leftClose with
  | none =>
      simp [packedReviewerWholeAfterRightSelect,
        PackedReviewerWholeStorageFits]
  | some leftValue =>
      cases rightClose with
      | none =>
          simp [packedReviewerWholeAfterRightSelect,
            PackedReviewerWholeStorageFits]
      | some rightValue =>
          simpa [packedReviewerWholeAfterRightSelect,
            PackedReviewerWholeStorageFits] using
            (show n = n ∧ PackedReviewerLcaStorageFits n
                (packedReviewerLcaStart n leftValue rightValue) from
              ⟨rfl,
                packedReviewerLcaStart_storage_fits n leftValue rightValue⟩)

private theorem packedReviewerWholeAfterLca_storage_fits
    (n left right : Nat) (answerClose : Option Nat) :
    PackedReviewerWholeStorageFits n
      (packedReviewerWholeAfterLca n left right answerClose) := by
  cases answerClose with
  | none =>
      simp [packedReviewerWholeAfterLca, PackedReviewerWholeStorageFits]
  | some answer =>
      refine ⟨rfl, ?_⟩
      constructor <;>
        simp [packedReviewerWholeAfterLca,
          PackedReviewerRankStorageFits,
          packedReviewerRankStateWordFields]

private theorem packedReviewerWholeConsumeReply_storage_fits
    (shape : CartesianShape) (state : PackedReviewerWholeState)
    (reply : Option (List Bool)) (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerWholeNextRequest state = some request)
    (hstate : PackedReviewerWholeStorageFits shape.size state)
    (hreply : forall word, reply = some word ->
      PackedReviewerWordFits shape.size word) :
    PackedReviewerWholeStorageFits shape.size
      (packedReviewerWholeConsumeReply state reply) := by
  cases state with
  | leftSelect n left right select =>
      have hn := hstate.1
      subst n
      have hselect :=
        packedReviewerSelectConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerWholeConsumeReply]
      split
      · apply packedReviewerWholeAfterLeftSelect_storage_fits
      · exact ⟨rfl, hselect⟩
  | rightSelect n left right leftClose select =>
      have hn := hstate.1
      subst n
      have hselect :=
        packedReviewerSelectConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerWholeConsumeReply]
      split
      · apply packedReviewerWholeAfterRightSelect_storage_fits
      · exact ⟨rfl, hselect⟩
  | lcaClose n left right leftClose rightClose lca =>
      have hn := hstate.1
      subst n
      have hlcaRequest :
          packedReviewerLcaNextRequest lca = some request := by
        simpa [packedReviewerWholeNextRequest] using hrequest
      have hlca := packedReviewerLcaConsumeReply_storage_fits shape lca reply
        request hlcaRequest hstate.2 hreply
      simp only [packedReviewerWholeConsumeReply]
      split
      · apply packedReviewerWholeAfterLca_storage_fits
      · exact ⟨rfl, hlca⟩
  | finalRank n left right answerClose rank =>
      have hn := hstate.1
      subst n
      have hrank := packedReviewerRankConsumeReply_storage_fits hstate.2 hreply
      simp only [packedReviewerWholeConsumeReply]
      split
      · simp [PackedReviewerWholeStorageFits]
      · exact ⟨rfl, hrank⟩
  | done value =>
      simp [packedReviewerWholeConsumeReply, PackedReviewerWholeStorageFits]

/-! ## Coupled scalar and request-prefix invariant -/

/-! ### Strict descent of structural request budgets -/

/-- One emitted entry-field request consumes exactly one structural slot. -/
private theorem packedReviewerEntryRemaining_consume_le
    (state : PackedReviewerEntryState) (reply : Option (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerEntryNextRequest state = some request) :
    packedReviewerEntryRemaining
          (packedReviewerEntryConsumeReply state reply) + 1 <=
      packedReviewerEntryRemaining state := by
  cases state <;>
    simp [packedReviewerEntryNextRequest, packedReviewerEntryConsumeReply,
      packedReviewerEntryRemaining] at hrequest ⊢

/--
One emitted Rank request strictly decreases its worst-case budget.  The word
phase may jump directly into a shorter charged fold, hence the deliberately
weak inequality rather than an equality.
-/
private theorem packedReviewerRankStartFold_remaining_le_eight
    (invocation : PackedReviewerInvocation) (kind : PackedReviewerRankKind)
    (n : Nat) (word : List Bool) (limit base : Nat) :
    packedReviewerRankRemaining
      (packedReviewerRankStartFold invocation kind n word limit base) <= 8 := by
  let effectiveLimit := SuccinctClose.bpWordRankEffLimit word limit
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) effectiveLimit
  have hcount : count <= 8 :=
    SuccinctClose.bpWordChunkCount_le_eight _ _
  change packedReviewerRankRemaining
    (if count = 0 then
      PackedReviewerRankState.done base
    else
      PackedReviewerRankState.fold invocation kind n word effectiveLimit 0
        count 0 base) <= 8
  by_cases hzero : count = 0
  · simp [hzero, packedReviewerRankRemaining]
  · simpa [hzero, packedReviewerRankRemaining] using hcount

private theorem packedReviewerRankRemaining_consume_le
    (state : PackedReviewerRankState) (reply : Option (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerRankNextRequest state = some request) :
    packedReviewerRankRemaining
          (packedReviewerRankConsumeReply state reply) + 1 <=
      packedReviewerRankRemaining state := by
  cases state with
  | superSample invocation kind n pos =>
      simp [packedReviewerRankConsumeReply, packedReviewerRankRemaining]
  | blockSample invocation kind n pos superSample =>
      simp [packedReviewerRankConsumeReply, packedReviewerRankRemaining]
  | word invocation kind n pos superSample blockSample =>
      cases superSample with
      | none =>
          simp [packedReviewerRankConsumeReply, packedReviewerRankRemaining]
      | some superValue =>
          cases blockSample with
          | none =>
              simp [packedReviewerRankConsumeReply,
                packedReviewerRankRemaining]
          | some blockValue =>
              cases reply with
              | none =>
                  simp [packedReviewerRankConsumeReply,
                    packedReviewerRankRemaining]
              | some word =>
                  let q := packedReviewerRankQueryPos kind n pos
                  let limit := q - q / kind.wordSize n * kind.wordSize n
                  have hnext :=
                    packedReviewerRankStartFold_remaining_le_eight invocation
                      kind n word limit (superValue + blockValue)
                  simpa [packedReviewerRankConsumeReply,
                    packedReviewerRankRemaining, q, limit] using
                    (show packedReviewerRankRemaining
                          (packedReviewerRankStartFold invocation kind n word
                            limit (superValue + blockValue)) + 1 <= 9 by
                      omega)
  | fold invocation kind n word effectiveLimit j remaining acc base =>
      cases remaining with
      | zero =>
          simp [packedReviewerRankNextRequest] at hrequest
      | succ remaining =>
          cases remaining with
          | zero =>
              simp [packedReviewerRankConsumeReply,
                packedReviewerRankRemaining]
          | succ remaining =>
              simp [packedReviewerRankConsumeReply,
                packedReviewerRankRemaining]
  | done value =>
      simp [packedReviewerRankNextRequest] at hrequest

/-- A fresh in-word select fold uses at most eight rank reads and one select. -/
private theorem packedReviewerWordSelectStart_remaining_le_nine
    (invocation : PackedReviewerInvocation) (n : Nat) (target : Bool)
    (word : List Bool) (occurrence : Nat) :
    packedReviewerWordSelectRemaining
      (packedReviewerWordSelectStart invocation n target word occurrence) <= 9 := by
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) word.length
  have hcount : count <= 8 :=
    SuccinctClose.bpWordChunkCount_le_eight _ _
  change packedReviewerWordSelectRemaining
    (if count = 0 then
      PackedReviewerWordSelectState.done none
    else
      PackedReviewerWordSelectState.rankChunk invocation n target word 0 count
        occurrence) <= 9
  by_cases hzero : count = 0
  · simp [hzero, packedReviewerWordSelectRemaining]
  · simpa [hzero, packedReviewerWordSelectRemaining] using
      Nat.add_le_add_right hcount 1

/-- One emitted in-word select request strictly decreases its budget. -/
private theorem packedReviewerWordSelectRemaining_consume_le
    (state : PackedReviewerWordSelectState) (reply : Option (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerWordSelectNextRequest state = some request) :
    packedReviewerWordSelectRemaining
          (packedReviewerWordSelectConsumeReply state reply) + 1 <=
      packedReviewerWordSelectRemaining state := by
  cases state with
  | rankChunk invocation n target word j remaining occurrence =>
      cases remaining with
      | zero =>
          simp [packedReviewerWordSelectNextRequest] at hrequest
      | succ remaining =>
          let c := packedFringeChunkBits n
          let rank :=
            SuccinctClose.bpChunkRankOfEntry c target
              (SuccinctClose.bpWordChunkSliceLen c word.length j)
              ((packedReviewerDecodeNat reply).getD 0)
          by_cases hoccurrence : occurrence < rank
          · simp [packedReviewerWordSelectConsumeReply,
              packedReviewerWordSelectRemaining, c, rank, hoccurrence]
          · cases remaining with
            | zero =>
                simp [packedReviewerWordSelectConsumeReply,
                  packedReviewerWordSelectRemaining, c, rank, hoccurrence]
            | succ remaining =>
                simp [packedReviewerWordSelectConsumeReply,
                  packedReviewerWordSelectRemaining, c, rank, hoccurrence]
  | selectChunk invocation n target word j remaining occurrence =>
      simp [packedReviewerWordSelectConsumeReply,
        packedReviewerWordSelectRemaining]
  | done value =>
      simp [packedReviewerWordSelectNextRequest] at hrequest

private theorem packedReviewerSelectAfterDenseUptoRank_remaining_le_ten
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence beforeFirst : Nat) (word : List Bool)
    (uptoFirst : Nat) :
    packedReviewerSelectRemaining
      (packedReviewerSelectAfterDenseUptoRank invocation n index basePosition
        baseOccurrence beforeFirst word uptoFirst) <= 10 := by
  simp only [packedReviewerSelectAfterDenseUptoRank]
  split
  · let select :=
      packedReviewerWordSelectStart invocation n false word
        (beforeFirst + (index - baseOccurrence))
    cases hresult : packedReviewerWordSelectResult select with
    | none =>
        have hselect :=
          packedReviewerWordSelectStart_remaining_le_nine invocation n false
            word (beforeFirst + (index - baseOccurrence))
        simpa [packedReviewerSelectRemaining, select, hresult] using
          (show packedReviewerWordSelectRemaining
                (packedReviewerWordSelectStart invocation n false word
                  (beforeFirst + (index - baseOccurrence))) <= 10 by
            omega)
    | some value =>
        simp [packedReviewerSelectRemaining, select, hresult]
  · simp [packedReviewerSelectRemaining]

private theorem packedReviewerSelectAfterDenseBeforeRank_remaining_le_eighteen
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence : Nat) (word : List Bool)
    (beforeFirst : Nat) :
    packedReviewerSelectRemaining
      (packedReviewerSelectAfterDenseBeforeRank invocation n index
        basePosition baseOccurrence word beforeFirst) <= 18 := by
  let rank :=
    packedReviewerRankStartFold invocation .close n word word.length 0
  have hrank : packedReviewerRankRemaining rank <= 8 := by
    simpa [rank] using
      packedReviewerRankStartFold_remaining_le_eight invocation .close n word
        word.length 0
  unfold packedReviewerSelectAfterDenseBeforeRank
  cases hresult : packedReviewerRankResult rank with
  | none =>
      simpa [rank, hresult, packedReviewerSelectRemaining] using
        Nat.add_le_add_right hrank 10
  | some uptoFirst =>
      have hnext :=
        packedReviewerSelectAfterDenseUptoRank_remaining_le_ten invocation n
          index basePosition baseOccurrence beforeFirst word uptoFirst
      simpa [rank, hresult] using
        (show packedReviewerSelectRemaining
              (packedReviewerSelectAfterDenseUptoRank invocation n index
                basePosition baseOccurrence beforeFirst word uptoFirst) <= 18 by
          omega)

private theorem packedReviewerSelectAfterDenseFirstWord_remaining_le_twentySix
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence : Nat) (reply : Option (List Bool)) :
    packedReviewerSelectRemaining
      (packedReviewerSelectAfterDenseFirstWord invocation n index basePosition
        baseOccurrence reply) <= 26 := by
  cases reply with
  | none =>
      simp [packedReviewerSelectAfterDenseFirstWord,
        packedReviewerSelectRemaining]
  | some word =>
      let limit :=
        basePosition - basePosition / packedSelectWordSize n *
          packedSelectWordSize n
      let rank :=
        packedReviewerRankStartFold invocation .close n word limit 0
      have hrank : packedReviewerRankRemaining rank <= 8 := by
        simpa [rank] using
          packedReviewerRankStartFold_remaining_le_eight invocation .close n
            word limit 0
      simp only [packedReviewerSelectAfterDenseFirstWord]
      cases hresult : packedReviewerRankResult rank with
      | none =>
          simpa [limit, rank, hresult, packedReviewerSelectRemaining] using
            Nat.add_le_add_right hrank 18
      | some beforeFirst =>
          have hnext :=
            packedReviewerSelectAfterDenseBeforeRank_remaining_le_eighteen
              invocation n index basePosition baseOccurrence word beforeFirst
          simpa [limit, rank, hresult] using
            (show packedReviewerSelectRemaining
                  (packedReviewerSelectAfterDenseBeforeRank invocation n index
                    basePosition baseOccurrence word beforeFirst) <= 26 by
              omega)

private theorem packedReviewerSelectAfterDenseSecondWord_remaining_le_nine
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence beforeFirst uptoFirst : Nat)
    (reply : Option (List Bool)) :
    packedReviewerSelectRemaining
      (packedReviewerSelectAfterDenseSecondWord invocation n index
        basePosition baseOccurrence beforeFirst uptoFirst reply) <= 9 := by
  cases reply with
  | none =>
      simp [packedReviewerSelectAfterDenseSecondWord,
        packedReviewerSelectRemaining]
  | some word =>
      let occurrence :=
        index - baseOccurrence - (uptoFirst - beforeFirst)
      let select :=
        packedReviewerWordSelectStart invocation n false word occurrence
      have hselect : packedReviewerWordSelectRemaining select <= 9 := by
        simpa [select] using
          packedReviewerWordSelectStart_remaining_le_nine invocation n false
            word occurrence
      simp only [packedReviewerSelectAfterDenseSecondWord]
      cases hresult : packedReviewerWordSelectResult select with
      | none =>
          simpa [occurrence, select, hresult, packedReviewerSelectRemaining]
            using hselect
      | some value =>
          simp [occurrence, select, hresult, packedReviewerSelectRemaining]

private theorem packedReviewerEntryResult_some_remaining_eq_zero
    {state : PackedReviewerEntryState}
    {value : Option GenericSelect.SparseDenseSelectDenseLocalEntry}
    (hresult : packedReviewerEntryResult state = some value) :
    packedReviewerEntryRemaining state = 0 := by
  cases state <;>
    simp [packedReviewerEntryResult, packedReviewerEntryRemaining] at hresult ⊢

private theorem packedReviewerRankResult_some_remaining_eq_zero
    {state : PackedReviewerRankState} {value : Nat}
    (hresult : packedReviewerRankResult state = some value) :
    packedReviewerRankRemaining state = 0 := by
  cases state <;>
    simp [packedReviewerRankResult, packedReviewerRankRemaining] at hresult ⊢

private theorem packedReviewerWordSelectResult_some_remaining_eq_zero
    {state : PackedReviewerWordSelectState} {value : Option Nat}
    (hresult : packedReviewerWordSelectResult state = some value) :
    packedReviewerWordSelectRemaining state = 0 := by
  cases state <;>
    simp [packedReviewerWordSelectResult,
      packedReviewerWordSelectRemaining] at hresult ⊢

/-- Every emitted close-select request strictly decreases its structural budget. -/
private theorem packedReviewerSelectRemaining_consume_le
    (state : PackedReviewerSelectState) (reply : Option (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerSelectNextRequest state = some request) :
    packedReviewerSelectRemaining
          (packedReviewerSelectConsumeReply state reply) + 1 <=
      packedReviewerSelectRemaining state := by
  cases state with
  | superEntry invocation n index entry =>
      have hentryRequest :
          packedReviewerEntryNextRequest entry = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hentry :=
        packedReviewerEntryRemaining_consume_le entry reply request
          hentryRequest
      cases hresult : packedReviewerEntryResult
          (packedReviewerEntryConsumeReply entry reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using
            Nat.add_le_add_right hentry 31
      | some superValue =>
          have hdone :=
            packedReviewerEntryResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerEntryRemaining entry := by
            omega
          cases superValue with
          | none =>
              simp [packedReviewerSelectConsumeReply, hresult,
                packedReviewerSelectAfterSuper,
                packedReviewerSelectRemaining]
          | some super =>
              by_cases hmarked :
                  GenericSelect.relativeSplitSelectEntryIsMarked super
              · simp [packedReviewerSelectConsumeReply, hresult,
                  packedReviewerSelectAfterSuper, hmarked,
                  packedReviewerSelectRemaining, packedReviewerRankRemaining]
                <;> omega
              · simpa [packedReviewerSelectConsumeReply, hresult,
                  packedReviewerSelectAfterSuper, hmarked,
                  packedReviewerSelectRemaining,
                  packedReviewerEntryRemaining] using
                  Nat.add_le_add_right hpositive 31
  | localEntry invocation n index localSlot super entry =>
      have hentryRequest :
          packedReviewerEntryNextRequest entry = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hentry :=
        packedReviewerEntryRemaining_consume_le entry reply request
          hentryRequest
      cases hresult : packedReviewerEntryResult
          (packedReviewerEntryConsumeReply entry reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using
            Nat.add_le_add_right hentry 27
      | some localValue =>
          have hdone :=
            packedReviewerEntryResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerEntryRemaining entry := by
            omega
          cases localValue with
          | none =>
              simp [packedReviewerSelectConsumeReply, hresult,
                packedReviewerSelectAfterLocal,
                packedReviewerSelectRemaining]
          | some loc =>
              by_cases hmarked :
                  GenericSelect.relativeSplitSelectEntryIsMarked loc
              · simp [packedReviewerSelectConsumeReply, hresult,
                  packedReviewerSelectAfterLocal, hmarked,
                  packedReviewerSelectRemaining, packedReviewerRankRemaining]
                <;> omega
              · simp [packedReviewerSelectConsumeReply, hresult,
                  packedReviewerSelectAfterLocal, hmarked,
                  packedReviewerSelectRemaining]
                <;> omega
  | longRank invocation n index super rank =>
      have hrankRequest :
          packedReviewerRankNextRequest rank = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hrank :=
        packedReviewerRankRemaining_consume_le rank reply request hrankRequest
      cases hresult : packedReviewerRankResult
          (packedReviewerRankConsumeReply rank reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using
            Nat.add_le_add_right hrank 1
      | some exceptionRank =>
          have hdone :=
            packedReviewerRankResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerRankRemaining rank := by omega
          simp [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectAfterLongRank,
            packedReviewerSelectRemaining]
          omega
  | longRelative invocation base slot =>
      simp [packedReviewerSelectConsumeReply, packedReviewerSelectRemaining]
  | sparseRank invocation n index localSlot super loc rank =>
      have hrankRequest :
          packedReviewerRankNextRequest rank = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hrank :=
        packedReviewerRankRemaining_consume_le rank reply request hrankRequest
      cases hresult : packedReviewerRankResult
          (packedReviewerRankConsumeReply rank reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using
            Nat.add_le_add_right hrank 1
      | some exceptionRank =>
          have hdone :=
            packedReviewerRankResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerRankRemaining rank := by omega
          simp [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectAfterSparseRank,
            packedReviewerSelectRemaining]
          omega
  | sparseRelative invocation base slot =>
      simp [packedReviewerSelectConsumeReply, packedReviewerSelectRemaining]
  | denseFirstWord invocation n index basePosition baseOccurrence =>
      have hnext :=
        packedReviewerSelectAfterDenseFirstWord_remaining_le_twentySix
          invocation n index basePosition baseOccurrence reply
      simpa [packedReviewerSelectConsumeReply,
        packedReviewerSelectRemaining] using (show
          packedReviewerSelectRemaining
                (packedReviewerSelectAfterDenseFirstWord invocation n index
                  basePosition baseOccurrence reply) + 1 <= 27 by omega)
  | denseBeforeRank invocation n index basePosition baseOccurrence word rank =>
      have hrankRequest :
          packedReviewerRankNextRequest rank = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hrank :=
        packedReviewerRankRemaining_consume_le rank reply request hrankRequest
      cases hresult : packedReviewerRankResult
          (packedReviewerRankConsumeReply rank reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using
            Nat.add_le_add_right hrank 18
      | some beforeFirst =>
          have hdone :=
            packedReviewerRankResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerRankRemaining rank := by omega
          have hnext :=
            packedReviewerSelectAfterDenseBeforeRank_remaining_le_eighteen
              invocation n index basePosition baseOccurrence word beforeFirst
          simp only [packedReviewerSelectConsumeReply, hresult]
          change packedReviewerSelectRemaining
                (packedReviewerSelectAfterDenseBeforeRank invocation n index
                  basePosition baseOccurrence word beforeFirst) + 1 <=
              packedReviewerRankRemaining rank + 18
          omega
  | denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      have hrankRequest :
          packedReviewerRankNextRequest rank = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hrank :=
        packedReviewerRankRemaining_consume_le rank reply request hrankRequest
      cases hresult : packedReviewerRankResult
          (packedReviewerRankConsumeReply rank reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using
            Nat.add_le_add_right hrank 10
      | some uptoFirst =>
          have hdone :=
            packedReviewerRankResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerRankRemaining rank := by omega
          have hnext :=
            packedReviewerSelectAfterDenseUptoRank_remaining_le_ten invocation
              n index basePosition baseOccurrence beforeFirst word uptoFirst
          simp only [packedReviewerSelectConsumeReply, hresult]
          change packedReviewerSelectRemaining
                (packedReviewerSelectAfterDenseUptoRank invocation n index
                  basePosition baseOccurrence beforeFirst word uptoFirst) + 1 <=
              packedReviewerRankRemaining rank + 10
          omega
  | denseFirstSelect invocation n baseWord select =>
      have hselectRequest :
          packedReviewerWordSelectNextRequest select = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hselect :=
        packedReviewerWordSelectRemaining_consume_le select reply request
          hselectRequest
      cases hresult : packedReviewerWordSelectResult
          (packedReviewerWordSelectConsumeReply select reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using hselect
      | some value =>
          have hdone :=
            packedReviewerWordSelectResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerWordSelectRemaining select := by
            omega
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using hpositive
  | denseSecondWord invocation n index basePosition baseOccurrence beforeFirst
      uptoFirst =>
      have hnext :=
        packedReviewerSelectAfterDenseSecondWord_remaining_le_nine invocation n
          index basePosition baseOccurrence beforeFirst uptoFirst reply
      simpa [packedReviewerSelectConsumeReply,
        packedReviewerSelectRemaining] using (show
          packedReviewerSelectRemaining
                (packedReviewerSelectAfterDenseSecondWord invocation n index
                  basePosition baseOccurrence beforeFirst uptoFirst reply) +
              1 <= 10 by omega)
  | denseSecondSelect invocation n baseWord select =>
      have hselectRequest :
          packedReviewerWordSelectNextRequest select = some request := by
        simpa [packedReviewerSelectNextRequest] using hrequest
      have hselect :=
        packedReviewerWordSelectRemaining_consume_le select reply request
          hselectRequest
      cases hresult : packedReviewerWordSelectResult
          (packedReviewerWordSelectConsumeReply select reply) with
      | none =>
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using hselect
      | some value =>
          have hdone :=
            packedReviewerWordSelectResult_some_remaining_eq_zero hresult
          have hpositive : 1 <= packedReviewerWordSelectRemaining select := by
            omega
          simpa [packedReviewerSelectConsumeReply, hresult,
            packedReviewerSelectRemaining] using hpositive
  | done value =>
      simp [packedReviewerSelectNextRequest] at hrequest

/--
The operational join invariant for one canonical whole-query prefix.  Scalar
closure and request-operand closure deliberately live in the same phase
witness, but remain separate fields: neither is inferred from the other.  The
fuel is the literal structural remainder of the represented state, so a
consume step can transfer the request field with
`PackedReviewerRequestsFitFrom.step` while the constructor-specific proof
transfers `scalar_fields`.

The `size_eq` field prevents an arbitrary nested controller from being
reinterpreted at the ambient shape size.  This is the missing phase equality
that a generic state-machine preservation statement would not provide.
-/
private structure PackedReviewerWholeOperationalFits
    (shape : CartesianShape) (state : PackedReviewerWholeState) : Prop where
  size_eq :
    match state with
    | .leftSelect n _ _ _
    | .rightSelect n _ _ _ _
    | .lcaClose n _ _ _ _ _
    | .finalRank n _ _ _ _ => n = shape.size
    | .done _ => True
  scalar_fields :
    forall value, value ∈ packedReviewerWholeStateNatFields state ->
      PackedReviewerNatFits shape.size value
  storage_fits : PackedReviewerWholeStorageFits shape.size state
  continuation_shape : PackedReviewerWholeContinuationShapeSafe state
  remaining_le : packedReviewerWholeRemaining state <= 210
  requests_fit :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
      (packedReviewerWholeRemaining state) state

/--
Generic one-step transfer for the coupled witness.  Constructor-specific work
is exposed as the three premises that genuinely require it: exact size phase,
strict structural-budget descent, and scalar closure under the canonical
reply.  Request-prefix transfer itself is the imported exact one-step
inversion, so no trace provenance is reconstructed after erasure.
-/
private theorem PackedReviewerWholeOperationalFits.consume
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    {request : PackedReviewerLogicalRequest}
    (hfit : PackedReviewerWholeOperationalFits shape state)
    (hrequest : packedReviewerWholeNextRequest state = some request)
    (hsize :
      match packedReviewerWholeConsumeReply state
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index) with
      | .leftSelect n _ _ _
      | .rightSelect n _ _ _ _
      | .lcaClose n _ _ _ _ _
      | .finalRank n _ _ _ _ => n = shape.size
      | .done _ => True)
    (hremaining :
      packedReviewerWholeRemaining
            (packedReviewerWholeConsumeReply state
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) +
          1 <= packedReviewerWholeRemaining state)
    (hscalar :
      forall value,
        value ∈ packedReviewerWholeStateNatFields
            (packedReviewerWholeConsumeReply state
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) ->
          PackedReviewerNatFits shape.size value) :
    PackedReviewerWholeOperationalFits shape
      (packedReviewerWholeConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  let store := concreteBPNativeSuccinctRMQGlobalReadStore shape
  let next := packedReviewerWholeConsumeReply state
    (store.readWord? request.segment request.index)
  have hprefix :
      PackedReviewerRequestsFitFrom shape.size store
        packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
        (packedReviewerWholeRemaining next + 1) state := by
    apply hfit.requests_fit.mono
    simpa [store, next] using hremaining
  have hstep := PackedReviewerRequestsFitFrom.step shape.size store
    packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
    (packedReviewerWholeRemaining next) state request hprefix hrequest
  exact
    { size_eq := by simpa [store, next] using hsize
      scalar_fields := by simpa [store, next] using hscalar
      storage_fits := by
        apply packedReviewerWholeConsumeReply_storage_fits shape state
          (store.readWord? request.segment request.index) request hrequest
          hfit.storage_fits
        intro word hword
        exact packedReviewerGlobalReadStore_word_fits shape request word hword
      continuation_shape := by
        exact packedReviewerWholeConsumeReply_shape_safe state
          (store.readWord? request.segment request.index)
          hfit.continuation_shape
      remaining_le := by
        have hdecrease :
            packedReviewerWholeRemaining next + 1 <=
              packedReviewerWholeRemaining state := by
          simpa [store, next] using hremaining
        have hold := hfit.remaining_le
        have hbound : packedReviewerWholeRemaining next <= 210 := by omega
        simpa [store, next] using hbound
      requests_fit := by simpa [next] using hstep.2 }

private theorem PackedReviewerWholeOperationalFits.core_fits
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    (hfit : PackedReviewerWholeOperationalFits shape state) :
    PackedReviewerWholeStateCoreFits shape.size state := by
  exact
    { scalar_fields := hfit.scalar_fields
      word_fields := hfit.storage_fits.word_fields
      wide_fields := hfit.storage_fits.wide_fields
      continuation_depth := hfit.continuation_shape.depth_le_three
      control_fields := hfit.storage_fits.control_fields }

/-! ## Exact physical controller phases -/

/--
The canonical physical phase invariant records an exact unfinished cell-plan
suffix.  Its `rest_eq` field pins the next address to the head of that suffix;
there is therefore no appeal to a trace after request provenance has been
erased.  Whole-query probes additionally retain the coupled scalar/request
invariant of the logical state that owns the plan.
-/
private inductive PackedReviewerCanonicalControllerInvariant
    (shape : CartesianShape) (left right : Nat) :
    PackedReviewerControllerState -> Prop where
  | header
      (hvalid : left < right /\ right <= shape.size) :
      PackedReviewerCanonicalControllerInvariant shape left right
        (.header shape.size left right)
  | preludeProbe
      (hvalid : left < right /\ right <= shape.size)
      (canonicalReplies : PackedReviewerCanonicalPreludeReplies shape)
      (prelude : PackedReviewerSparsePreludeState)
      (hprelude :
        PackedReviewerCanonicalPreludeState shape canonicalReplies prelude)
      (request : PackedReviewerSparsePreludeRequest) (word : List Bool)
      (hrequest :
        packedReviewerSparsePreludeNextRequest prelude = some request)
      (hread :
        packedReviewerSparsePreludeRequestRead shape.size (longCount shape)
            (packedReviewerMemory shape) request = some word)
      (nextOrdinal : Nat) (repliesRev : List (List Bool))
      (probePrefix :
        PackedReviewerProbePrefix (packedReviewerMemory shape)
          (packedReviewerCurrentPreludePlan shape.size (longCount shape)
            prelude) nextOrdinal repliesRev)
      (address : Nat) (tail : List Nat)
      (rest_eq : probePrefix.rest = address :: tail) :
      PackedReviewerCanonicalControllerInvariant shape left right
        (.preludeProbe shape.size left right (longCount shape) prelude
          nextOrdinal repliesRev)
  | wholeProbe
      (hvalid : left < right /\ right <= shape.size)
      (logicalStepsAfterReply : Nat)
      (hsteps : logicalStepsAfterReply <= 210)
      (whole : PackedReviewerWholeState)
      (hwhole : PackedReviewerWholeOperationalFits shape whole)
      (request : PackedReviewerLogicalRequest)
      (hrequest : packedReviewerWholeNextRequest whole = some request)
      (nextOrdinal : Nat) (repliesRev : List (List Bool))
      (probePrefix :
        PackedReviewerProbePrefix (packedReviewerMemory shape)
          (packedReviewerLogicalPlan shape.size (longCount shape)
            (packedReviewerSparseCount shape) request)
          nextOrdinal repliesRev)
      (address : Nat) (tail : List Nat)
      (rest_eq : probePrefix.rest = address :: tail) :
      PackedReviewerCanonicalControllerInvariant shape left right
        (.wholeProbe shape.size left right (longCount shape)
          (packedReviewerSparseCount shape) logicalStepsAfterReply whole
          nextOrdinal repliesRev)
  | done
      (value : Option Nat)
      (hvalue :
        forall index, value = some index ->
          PackedReviewerNatFits shape.size index) :
      PackedReviewerCanonicalControllerInvariant shape left right (.done value)
  | failed :
      PackedReviewerCanonicalControllerInvariant shape left right .failed

private theorem PackedReviewerCanonicalControllerInvariant.core_fits
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerControllerState}
    (hstate :
      PackedReviewerCanonicalControllerInvariant shape left right state) :
    PackedReviewerControllerStateCoreFits shape.size state := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  cases hstate with
  | header hvalid =>
      have hendpoints :=
        packedReviewerValidEndpoints_lt_two_pow_cellWidth shape.size left right
          hvalid
      exact packedReviewerHeader_core_fits hn hendpoints.1 hendpoints.2
  | preludeProbe hvalid canonicalReplies prelude hprelude request word
      hrequest hread nextOrdinal repliesRev probePrefix address tail rest_eq =>
      have hendpoints :=
        packedReviewerValidEndpoints_lt_two_pow_cellWidth shape.size left right
          hvalid
      have hplanEq := packedReviewerCurrentPreludePlan_eq_requestPlan_of_read
        shape.size (longCount shape) (packedReviewerMemory shape) prelude
        request word hrequest hread
      have hplanLength :
          (packedReviewerCurrentPreludePlan shape.size (longCount shape)
            prelude).length <= 2 := by
        rw [hplanEq]
        exact packedReviewerSparsePreludeRequestPlan_length_le_two
          shape.size (longCount shape) request
      have hnext : nextOrdinal < 2 := by
        have hdecomp := probePrefix.plan_eq
        have hnextEq := probePrefix.next_eq
        rw [rest_eq] at hdecomp
        have hlength := congrArg List.length hdecomp
        simp at hlength
        omega
      exact packedReviewerPreludeProbe_core_fits hn hendpoints.1
        hendpoints.2 (longCount_lt_two_pow_reviewerWidth shape) hnext
        probePrefix.replies_length probePrefix.replies_word_fits
          hprelude.core_fits
  | wholeProbe hvalid logicalStepsAfterReply hsteps whole hwhole request
      hrequest nextOrdinal repliesRev probePrefix address tail rest_eq =>
      have hendpoints :=
        packedReviewerValidEndpoints_lt_two_pow_cellWidth shape.size left right
          hvalid
      have hplanLength :
          (packedReviewerLogicalPlan shape.size (longCount shape)
            (packedReviewerSparseCount shape) request).length <= 2 :=
        packedReviewerLogicalPlan_length_le_two _ _ _ _
      have hnext : nextOrdinal < 2 := by
        have hdecomp := probePrefix.plan_eq
        have hnextEq := probePrefix.next_eq
        rw [rest_eq] at hdecomp
        have hlength := congrArg List.length hdecomp
        simp at hlength
        omega
      exact packedReviewerWholeProbe_core_fits hn hendpoints.1 hendpoints.2
        (longCount_lt_two_pow_reviewerWidth shape)
        (packedReviewerSparseCount_lt_two_pow shape) hsteps hwhole.remaining_le
        hnext probePrefix.replies_length probePrefix.replies_word_fits
          hwhole.core_fits
  | done value hvalue =>
      exact packedReviewerDone_core_fits hvalue
  | failed =>
      exact packedReviewerFailed_core_fits shape.size

private theorem packedReviewerCanonicalController_start_invariant
    (shape : CartesianShape) (left right : Nat) :
    PackedReviewerCanonicalControllerInvariant shape left right
      (packedReviewerController shape.size left right) := by
  by_cases hvalid : left < right /\ right <= shape.size
  · simpa [packedReviewerController, hvalid] using
      (PackedReviewerCanonicalControllerInvariant.header
        (shape := shape) (left := left) (right := right) hvalid)
  · simpa [packedReviewerController, hvalid] using
      (PackedReviewerCanonicalControllerInvariant.done
        (shape := shape) (left := left) (right := right) none
        (by simp))

/-- Valid endpoint geometry makes the canonical whole start's budget literal. -/
private theorem packedReviewerWholeStart_remaining_eq_two_ten
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right ∧ right <= shape.size) :
    packedReviewerWholeRemaining
        (packedReviewerWholeStart shape.size left right) = 210 := by
  have hleft : left < shape.size := by omega
  simp [packedReviewerWholeRemaining, packedReviewerWholeStart,
    packedReviewerSelectStart, packedReviewerSelectRemaining,
    packedReviewerEntryRemaining, hleft]

/--
Once the constructor-exhaustive producer supplies the canonical start witness,
the public 210-step logical operand claim is a direct checked consumer of its
request-prefix field.
-/
private theorem
    packedReviewerDriveLogical_210_request_operands_fit_of_start_operational_fits
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right ∧ right <= shape.size)
    (hfit : PackedReviewerWholeOperationalFits shape
      (packedReviewerWholeStart shape.size left right))
    {event : PackedReviewerLogicalEvent}
    (hmem : event ∈
      (packedReviewerDriveLogical
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
        (packedReviewerWholeStart shape.size left right)).trace) :
    PackedReviewerLogicalRequestOperandsFit shape.size event.request := by
  apply packedReviewerDriveLogical_trace_request_operands_fit_of_fitFrom
    shape.size (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
    (packedReviewerWholeStart shape.size left right)
  · simpa [packedReviewerWholeStart_remaining_eq_two_ten shape left right
      hvalid] using hfit.requests_fit
  · exact hmem

private theorem packedReviewerCanonicalLogicalReachable_storage_fits
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerWholeState}
    (hstate :
      PackedReviewerCanonicalLogicalReachable shape left right state) :
    PackedReviewerWholeStorageFits shape.size state := by
  induction hstate with
  | start =>
      exact packedReviewerWholeStart_storage_fits shape.size left right
  | @step state request hreachable hrequest ih =>
      apply packedReviewerWholeConsumeReply_storage_fits shape state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index) request hrequest ih
      intro word hword
      exact packedReviewerGlobalReadStore_word_fits shape request word hword

private theorem packedReviewerCanonicalLogicalReachable_shape_safe
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerWholeState}
    (hstate :
      PackedReviewerCanonicalLogicalReachable shape left right state) :
    PackedReviewerWholeContinuationShapeSafe state := by
  induction hstate with
  | start =>
      exact packedReviewerWholeStart_shape_safe shape.size left right
  | @step state request hreachable hrequest ih =>
      exact packedReviewerWholeConsumeReply_shape_safe state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index) ih

private theorem packedReviewerCanonicalLogicalReachable_depth_le_three
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerWholeState}
    (hstate :
      PackedReviewerCanonicalLogicalReachable shape left right state) :
    packedReviewerWholeStateContinuationDepth state <= 3 :=
  PackedReviewerWholeContinuationShapeSafe.depth_le_three
    (packedReviewerCanonicalLogicalReachable_shape_safe hstate)

/--
The exact public facts advertised for one canonically reachable controller
prefix.  The reachability field pins the state to transitions against the
canonical reviewer memory; the remaining fields pin every literal component
of the fixed state envelope independently of the record declaration upstream.
-/
structure PackedReviewerReachableStateCertificate
    (shape : CartesianShape) (left right : Nat)
    (state : PackedReviewerControllerState) : Prop where
  reachable : PackedReviewerCanonicalReachable shape left right state
  state_machine_fits :
    PackedReviewerControllerStateMachineFits shape.size state
  phase_tag :
    PackedReviewerNatFits shape.size
      (packedReviewerControllerStatePhaseCode state)
  nested_control_tags :
    forall code, code ∈ packedReviewerControllerNestedTagCodes state ->
      PackedReviewerNatFits shape.size code
  scalar_register_count :
    (packedReviewerControllerStateNatFields state).length <= 512
  scalar_fields :
    forall value, value ∈ packedReviewerControllerStateNatFields state ->
      PackedReviewerNatFits shape.size value
  word_buffer :
    PackedReviewerBufferFits shape.size 212
      (packedReviewerControllerStateWordFields state)
  wide_buffer_count :
    (packedReviewerControllerStateWideFields state).length <= 1
  wide_fields :
    forall bits, bits ∈ packedReviewerControllerStateWideFields state ->
      bits.length <= 4 * packedReviewerCellWidth shape.size
  continuation_depth :
    packedReviewerControllerStateContinuationDepth state <= 3
  control_fields : packedReviewerControllerStateControlBounds state

/--
An independent proposition used by checked consumers to pin every mandatory
reachable-state certificate field at its exact object arguments.
-/
def PackedReviewerReachableStateRequiredFacts
    (shape : CartesianShape) (left right : Nat)
    (state : PackedReviewerControllerState) : Prop :=
  PackedReviewerCanonicalReachable shape left right state ∧
    PackedReviewerControllerStateMachineFits shape.size state ∧
      PackedReviewerNatFits shape.size
          (packedReviewerControllerStatePhaseCode state) ∧
        (forall code, code ∈ packedReviewerControllerNestedTagCodes state ->
          PackedReviewerNatFits shape.size code) ∧
          (packedReviewerControllerStateNatFields state).length <= 512 ∧
            (forall value,
              value ∈ packedReviewerControllerStateNatFields state ->
                PackedReviewerNatFits shape.size value) ∧
              PackedReviewerBufferFits shape.size 212
                  (packedReviewerControllerStateWordFields state) ∧
                (packedReviewerControllerStateWideFields state).length <= 1 ∧
                  (forall bits,
                    bits ∈ packedReviewerControllerStateWideFields state ->
                      bits.length <=
                        4 * packedReviewerCellWidth shape.size) ∧
                    packedReviewerControllerStateContinuationDepth state <= 3 ∧
                      packedReviewerControllerStateControlBounds state

/-- Every mandatory field is a checked projection, rather than uninspected passage. -/
theorem packedReviewerReachableStateCertificate_requiredFacts
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerControllerState}
    (certificate :
      PackedReviewerReachableStateCertificate shape left right state) :
    PackedReviewerReachableStateRequiredFacts shape left right state := by
  exact ⟨certificate.reachable, certificate.state_machine_fits,
    certificate.phase_tag, certificate.nested_control_tags,
    certificate.scalar_register_count, certificate.scalar_fields,
    certificate.word_buffer,
    certificate.wide_buffer_count, certificate.wide_fields,
    certificate.continuation_depth, certificate.control_fields⟩

/-! ## Stable public run certificate -/

/--
The stable public bundle for the actual reviewer-memory run.  These are the
same twenty-six facts exposed before request-operand closure moved downstream;
in particular, every proposition names the canonical payload, memory, store,
trace, and public reference result directly.
-/
structure PackedReviewerPublicRunCertificate
    (xs : List Int) (left right : Nat) : Prop where
  terminal_eq :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).terminal =
        some (SuccinctClassic.queryTraceResult xs left right).value
  failed_false :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).failed = false
  state_eq :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).state =
        .done (SuccinctClassic.queryTraceResult xs left right).value
  grouping :
    PackedReviewerRunGrouping (SuccinctClassic.cartesianShape xs) left right
  invalid_no_requests :
    let shape := SuccinctClassic.cartesianShape xs
    ¬ (left < right ∧ right <= shape.size) ->
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace = []
  input_size_width :
    let shape := SuccinctClassic.cartesianShape xs
    shape.size < 2 ^ packedReviewerCellWidth shape.size
  valid_endpoints_width :
    let shape := SuccinctClassic.cartesianShape xs
    left < right ∧ right <= shape.size ->
      PackedReviewerNatFits shape.size left ∧
        PackedReviewerNatFits shape.size right
  header_values_width :
    let shape := SuccinctClassic.cartesianShape xs
    longCount shape < 2 ^ packedReviewerCellWidth shape.size ∧
      packedReviewerSparseCount shape <
        2 ^ packedReviewerCellWidth shape.size
  memory_words_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall cell, cell ∈ packedReviewerMemory shape ->
      PackedReviewerWordFits shape.size cell ∧
        SuccinctSpace.bitsToNatLE cell <
          2 ^ packedReviewerCellWidth shape.size
  prelude_decode_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall state request cells word,
      packedReviewerSparsePreludeNextRequest state = some request ->
        packedReviewerDecodePreludeReplies shape.size (longCount shape)
            state cells = some word ->
          PackedReviewerWordFits shape.size word
  logical_decode_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall request cells word,
      packedReviewerLogicalDecode shape.size (longCount shape)
          (packedReviewerSparseCount shape) request cells = some word ->
        PackedReviewerWordFits shape.size word
  logical_request_operands_width :
    let shape := SuccinctClassic.cartesianShape xs
    left < right -> right <= shape.size ->
      forall event,
        event ∈
            (packedReviewerDriveLogical
              (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
              (packedReviewerWholeStart shape.size left right)).trace ->
          PackedReviewerLogicalRequestOperandsFit shape.size event.request
  logical_control_tags_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall request, PackedReviewerLogicalControlCodesFit shape.size request
  physical_control_tags_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall origin, PackedReviewerPhysicalControlCodesFit shape.size origin
  controller_phase_tag_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall state,
      PackedReviewerNatFits shape.size
        (packedReviewerControllerStatePhaseCode state)
  memory_only :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.reply = (packedReviewerMemory shape)[event.request.address]?
  reply_success :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        exists cell, event.reply = some cell
  allocated :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address <
          packedReviewerCellCount shape.size (longCount shape)
            (packedReviewerSparseCount shape)
  address_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        event.request.address < 2 ^ packedReviewerCellWidth shape.size
  physical_request_operands_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace ->
        PackedReviewerPhysicalRequestOperandsFit shape.size event.request
  reply_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event cell,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          cell.length = packedReviewerCellWidth shape.size
  reply_value_width :
    let shape := SuccinctClassic.cartesianShape xs
    forall event cell,
      event ∈ (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
          shape.size left right).trace ->
        event.reply = some cell ->
          SuccinctSpace.bitsToNatLE cell <
            2 ^ packedReviewerCellWidth shape.size
  dead_address_width :
    let shape := SuccinctClassic.cartesianShape xs
    (packedInteriorOffsets shape.size).deadAddress <
      2 ^ packedReviewerCellWidth shape.size
  word_width_logarithmic :
    let shape := SuccinctClassic.cartesianShape xs
    packedReviewerCellWidth shape.size <=
      20 * (Nat.log2 (shape.size + 2) + 1)
  trace_cap :
    let shape := SuccinctClassic.cartesianShape xs
    (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
      shape.size left right).trace.length <= 427
  result_width :
    forall index,
      (SuccinctClassic.queryTraceResult xs left right).value = some index ->
        index <
          2 ^ packedReviewerCellWidth
            (SuccinctClassic.cartesianShape xs).size

/-! ## Invariant-driven request-width transport -/

/--
Any state invariant preserved by canonical-store consumption whose states only
emit fitting requests transports to the fuel-indexed request-width prefix at
every fuel.  No budget-descent obligation appears anywhere: the fuel induction
is driven by the invariant alone, so protocols whose structural measures are
not monotone for forged parameters are still covered on their canonical orbit.
-/
private theorem PackedReviewerRequestsFitFrom.of_invariant
    {State : Type} (n : Nat) (store : WordRAM.ReadStore)
    (nextRequest : State -> Option PackedReviewerLogicalRequest)
    (consumeReply : State -> Option (List Bool) -> State)
    (P : State -> Prop)
    (hfit :
      forall state request,
        P state -> nextRequest state = some request ->
          PackedReviewerLogicalRequestOperandsFit n request)
    (hstep :
      forall state request,
        P state -> nextRequest state = some request ->
          P (consumeReply state
            (store.readWord? request.segment request.index)))
    (fuel : Nat) (state : State) (hstate : P state) :
    PackedReviewerRequestsFitFrom n store nextRequest consumeReply fuel
      state := by
  induction fuel generalizing state with
  | zero => trivial
  | succ fuel ih =>
      cases hrequest : nextRequest state with
      | none => simp [PackedReviewerRequestsFitFrom, hrequest]
      | some request =>
          simp only [PackedReviewerRequestsFitFrom, hrequest]
          exact ⟨hfit state request hstate hrequest,
            ih (consumeReply state
              (store.readWord? request.segment request.index))
              (hstep state request hstate hrequest)⟩

/-! ## Canonical rank and word-select orbits

The select tower pins in-flight nested components to the exact orbit of their
canonical start, exactly as the interior module does for segment 20.  The
orbit witness is what later connects a completed rank to its accepted
reference value, which the relative-directory transitions need.
-/

private def packedReviewerRankCanonicalStep
    (shape : CartesianShape) (state : PackedReviewerRankState) :
    PackedReviewerRankState :=
  packedReviewerComponentCanonicalStep packedReviewerRankNextRequest
    packedReviewerRankConsumeReply
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) state

private def packedReviewerRankCanonicalRun
    (shape : CartesianShape) : Nat -> PackedReviewerRankState ->
      PackedReviewerRankState :=
  packedReviewerComponentCanonicalRun packedReviewerRankNextRequest
    packedReviewerRankConsumeReply
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)

private def packedReviewerWordSelectCanonicalStep
    (shape : CartesianShape) (state : PackedReviewerWordSelectState) :
    PackedReviewerWordSelectState :=
  match packedReviewerWordSelectNextRequest state with
  | none => state
  | some request =>
      packedReviewerWordSelectConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)

private def packedReviewerWordSelectCanonicalRun
    (shape : CartesianShape) : Nat -> PackedReviewerWordSelectState ->
      PackedReviewerWordSelectState
  | 0, state => state
  | fuel + 1, state =>
      packedReviewerWordSelectCanonicalStep shape
        (packedReviewerWordSelectCanonicalRun shape fuel state)

/-! ## Canonical select tower -/

/--
Constructor-exhaustive canonical invariant for the close-select machine.
Every arm carries the ambient-size phase equality, the operand width of its
stored invocation, the validity of the public select index, the canonical
carriers of its decoded directory entries, and — for in-flight nested
components — both the scalar envelope and the exact canonical orbit witness
from that component's canonical start.
-/
private def PackedReviewerSelectCanonicalScalarFits
    (shape : CartesianShape) : PackedReviewerSelectState -> Prop
  | .superEntry invocation n index entry =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        PackedReviewerCanonicalEntryState shape invocation .super
          (GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size)) entry
  | .localEntry invocation n index localSlot super entry =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        PackedReviewerCanonicalSuperGeometry shape index super ∧
        GenericSelect.relativeSplitSelectEntryIsMarked super = false ∧
        localSlot =
          GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super ∧
        PackedReviewerCanonicalEntryState shape invocation .local localSlot
          entry
  | .longRank invocation n index super rank =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        PackedReviewerCanonicalSuperGeometry shape index super ∧
        GenericSelect.relativeSplitSelectEntryIsMarked super = true ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape
          (packedReviewerRankQueryPos .selectLong shape.size
            (GenericSelect.selectSuperSlot index
              (packedSelectSuperStride shape.size))) rank ∧
        (exists fuel,
          rank =
            packedReviewerRankCanonicalRun shape fuel
              (.superSample invocation .selectLong shape.size
                (GenericSelect.selectSuperSlot index
                  (packedSelectSuperStride shape.size))))
  | .longRelative invocation base slot =>
      (forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand) ∧
        PackedReviewerNatFits shape.size base ∧
        base <= 2 * shape.size + 1 ∧
        PackedReviewerNatFits shape.size slot ∧
        (forall word,
          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 12
              slot = some word ->
            base + SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1)
  | .sparseRank invocation n index localSlot super loc rank =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        PackedReviewerCanonicalLocalGeometry shape index super loc ∧
        localSlot =
          GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super ∧
        GenericSelect.relativeSplitSelectEntryIsMarked loc = true ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape
          (packedReviewerRankQueryPos .selectSparse shape.size localSlot)
          rank ∧
        (exists fuel,
          rank =
            packedReviewerRankCanonicalRun shape fuel
              (.superSample invocation .selectSparse shape.size localSlot))
  | .sparseRelative invocation base slot =>
      (forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand) ∧
        PackedReviewerNatFits shape.size base ∧
        base <= 2 * shape.size + 1 ∧
        PackedReviewerNatFits shape.size slot ∧
        (forall word,
          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16
              slot = some word ->
            base + SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1)
  | .denseFirstWord invocation n index basePosition baseOccurrence =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        basePosition <= 2 * shape.size + 1 ∧
        baseOccurrence <= index
  | .denseBeforeRank invocation n index basePosition baseOccurrence word
      rank =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        basePosition <= 2 * shape.size + 1 ∧
        baseOccurrence <= index ∧
        PackedReviewerWordFits shape.size word ∧
        word.length <= packedBpCodeWordWidth shape.size ∧
        basePosition / packedSelectWordSize shape.size *
            packedSelectWordSize shape.size + word.length <=
          2 * shape.size ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape word.length rank ∧
        packedReviewerRankRemaining rank <= 8
  | .denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        basePosition <= 2 * shape.size + 1 ∧
        baseOccurrence <= index ∧
        beforeFirst <= word.length ∧
        PackedReviewerWordFits shape.size word ∧
        word.length <= packedBpCodeWordWidth shape.size ∧
        basePosition / packedSelectWordSize shape.size *
            packedSelectWordSize shape.size + word.length <=
          2 * shape.size ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape word.length rank ∧
        packedReviewerRankRemaining rank <= 8
  | .denseFirstSelect invocation n baseWord select =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        baseWord * packedSelectWordSize shape.size <=
          2 * shape.size + 1 + packedSelectWordSize shape.size ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerWordSelectNextRequest
          packedReviewerWordSelectConsumeReply
          (packedReviewerWordSelectRemaining select) select ∧
        (exists word,
          PackedReviewerWordFits shape.size word ∧
            word.length <= packedBpCodeWordWidth shape.size ∧
            baseWord * packedSelectWordSize shape.size + word.length <=
              2 * shape.size ∧
            PackedReviewerWordSelectCanonicalScalarFits shape word.length
              select) ∧
        packedReviewerWordSelectRemaining select <= 9
  | .denseSecondWord invocation n index basePosition baseOccurrence
      beforeFirst uptoFirst =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        index < shape.size ∧
        basePosition <= 2 * shape.size + 1 ∧
        baseOccurrence <= index ∧
        beforeFirst <= packedBpCodeWordWidth shape.size ∧
        uptoFirst <= packedBpCodeWordWidth shape.size
  | .denseSecondSelect invocation n baseWord select =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        baseWord * packedSelectWordSize shape.size <=
          2 * shape.size + 1 + packedSelectWordSize shape.size ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerWordSelectNextRequest
          packedReviewerWordSelectConsumeReply
          (packedReviewerWordSelectRemaining select) select ∧
        (exists word,
          PackedReviewerWordFits shape.size word ∧
            word.length <= packedBpCodeWordWidth shape.size ∧
            baseWord * packedSelectWordSize shape.size + word.length <=
              2 * shape.size ∧
            PackedReviewerWordSelectCanonicalScalarFits shape word.length
              select) ∧
        packedReviewerWordSelectRemaining select <= 9
  | .done value =>
      forall close, value = some close ->
        PackedReviewerNatFits shape.size close ∧ close <= 2 * shape.size + 1

/-- The canonical select start satisfies the tower invariant. -/
private theorem packedReviewerSelectStart_canonicalScalarFits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (hinvocation :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectStart invocation shape.size index) := by
  unfold packedReviewerSelectStart
  simp only [hindex, if_true]
  exact ⟨rfl, hinvocation, hindex, .baseOccurrence⟩

/-- Every stored select scalar fits the modeled word on the canonical tower. -/
private theorem PackedReviewerSelectCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectCanonicalScalarFits shape state) :
    forall value, value ∈ packedReviewerSelectStateNatFields state ->
      PackedReviewerNatFits shape.size value := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  cases state with
  | superEntry invocation n index entry =>
      obtain ⟨rfl, hinv, hindex, hentry⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hslot :
          PackedReviewerNatFits shape.size
            (GenericSelect.selectSuperSlot index
              (packedSelectSuperStride shape.size)) := by
        have hle : GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size) <= index :=
          Nat.div_le_self _ _
        omega
      have hentryFields := hentry.scalar_fields hinv hslot
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | hentryMem
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hentryFields value hentryMem
  | localEntry invocation n index localSlot super entry =>
      obtain ⟨rfl, hinv, hindex, hsuperGeo, hshort, hslotEq, hentry⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hvalid : index < GenericSelect.occurrenceCount shape.bpCode false := by
        rw [packedSelectOccurrenceCount_eq_size]; exact hindex
      have hfacts := GenericSelect.localSlot_facts shape.bpCode false index
        super (by
          simpa [packedSelectSuperStride, CartesianShape.bpCode_length] using
            hsuperGeo.get_eq)
        hvalid hshort
      have hslotFits : PackedReviewerNatFits shape.size localSlot := by
        rw [hslotEq]
        have hbound := packedReviewerLocalSlots_lt_two_pow shape
        have hlt := hfacts.1
        rw [localSlotCount_eq_packed] at hlt
        have hlen := CartesianShape.bpCode_length shape
        simp only [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
          packedSelectLocalStride, hlen] at hlt ⊢
        omega
      have hsuperFields := hsuperGeo.entry_scalar_fields
      have hentryFields := hentry.scalar_fields hinv hslotFits
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | hsuperMem | hentryMem
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hslotFits
      · exact hsuperFields value hsuperMem
      · exact hentryFields value hentryMem
  | longRank invocation n index super rank =>
      obtain ⟨rfl, hinv, hindex, hsuperGeo, hlong, hrankFit, hrank, horbit⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hrankFields := hrank.scalar_fields
      have hsuperFields := hsuperGeo.entry_scalar_fields
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | hsuperMem | hrankMem
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hsuperFields value hsuperMem
      · exact hrankFields value hrankMem
  | longRelative invocation base slot =>
      obtain ⟨hinv, hbase, hbaseLe, hslot, _⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl
      · exact hinvFields value hinvMem
      · exact hbase
      · exact hslot
  | sparseRank invocation n index localSlot super loc rank =>
      obtain ⟨rfl, hinv, hindex, hlocalGeo, hslotEq, hmarked, hrankFit, hrank,
        horbit⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hslotFits : PackedReviewerNatFits shape.size localSlot := by
        rw [hslotEq]
        exact hlocalGeo.localSlot_fits
      have hsuperFields := hlocalGeo.super_geometry.entry_scalar_fields
      have hlocFields := hlocalGeo.entry_scalar_fields
      have hrankFields := hrank.scalar_fields
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | hsuperMem | hlocMem | hrankMem
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hslotFits
      · exact hsuperFields value hsuperMem
      · exact hlocFields value hlocMem
      · exact hrankFields value hrankMem
  | sparseRelative invocation base slot =>
      obtain ⟨hinv, hbase, hbaseLe, hslot, _⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl
      · exact hinvFields value hinvMem
      · exact hbase
      · exact hslot
  | denseFirstWord invocation n index basePosition baseOccurrence =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hbaseFits : PackedReviewerNatFits shape.size basePosition :=
        packedReviewerNatFits_of_le_two_mul_add_one shape.size basePosition
          hbase
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hbaseFits
      · omega
  | denseBeforeRank invocation n index basePosition baseOccurrence word rank =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hword, hwordLen, -, hrankFit, hrank, hbudget⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hbaseFits : PackedReviewerNatFits shape.size basePosition :=
        packedReviewerNatFits_of_le_two_mul_add_one shape.size basePosition
          hbase
      have hrankFields := hrank.scalar_fields
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | hrankMem
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hbaseFits
      · omega
      · exact hrankFields value hrankMem
  | denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hbefore, hword, hwordLen, -,
        hrankFit, hrank, hbudget⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hbaseFits : PackedReviewerNatFits shape.size basePosition :=
        packedReviewerNatFits_of_le_two_mul_add_one shape.size basePosition
          hbase
      have hbeforeFits : PackedReviewerNatFits shape.size beforeFirst := by
        have hlength : word.length <= packedReviewerCellWidth shape.size := hword
        have hwidth := Nat.lt_two_pow_self (n := packedReviewerCellWidth shape.size)
        omega
      have hrankFields := hrank.scalar_fields
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | rfl | hrankMem
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hbaseFits
      · omega
      · exact hbeforeFits
      · exact hrankFields value hrankMem
  | denseFirstSelect invocation n baseWord select =>
      obtain ⟨rfl, hinv, hbase, hselectFit, ⟨word, hword, hwordLen, -, hselect⟩,
        hremaining⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hwordSize : 0 < packedSelectWordSize shape.size := by
        simpa [packedSelectWordSize] using
          GenericSelect.wordBits_pos (2 * shape.size)
      have hbaseFits : PackedReviewerNatFits shape.size baseWord := by
        have hle : baseWord <= baseWord * packedSelectWordSize shape.size :=
          Nat.le_mul_of_pos_right baseWord hwordSize
        have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
        have htwoMul := packedTwoMul_le_reviewerBound shape.size
        have hwsSlack := packedRankWordSize_two_le_aux shape.size
        have hauxSlack := packedRankAux_le_reviewerBound shape.size
        have hwsEq :
            packedRankWordSize shape.size =
              packedSelectWordSize shape.size := rfl
        simp only [PackedReviewerNatFits]
        omega
      have hselectFields := hselect.scalar_fields
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | hselectMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact hbaseFits
      · exact hselectFields value hselectMem
  | denseSecondWord invocation n index basePosition baseOccurrence beforeFirst
      uptoFirst =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hbefore, hupto⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hbaseFits : PackedReviewerNatFits shape.size basePosition :=
        packedReviewerNatFits_of_le_two_mul_add_one shape.size basePosition
          hbase
      have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
      have htwoMul := packedTwoMul_le_reviewerBound shape.size
      have hwsSlack := packedRankWordSize_two_le_aux shape.size
      have hauxSlack := packedRankAux_le_reviewerBound shape.size
      have hwEq :
          packedBpCodeWordWidth shape.size = packedRankWordSize shape.size :=
        rfl
      have huptoFits : PackedReviewerNatFits shape.size uptoFirst := by
        simp only [PackedReviewerNatFits]
        omega
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hinvFields value hinvMem
      · exact hn
      · omega
      · exact hbaseFits
      · omega
      · omega
      · exact huptoFits
  | denseSecondSelect invocation n baseWord select =>
      obtain ⟨rfl, hinv, hbase, hselectFit, ⟨word, hword, hwordLen, -, hselect⟩,
        hremaining⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hwordSize : 0 < packedSelectWordSize shape.size := by
        simpa [packedSelectWordSize] using
          GenericSelect.wordBits_pos (2 * shape.size)
      have hbaseFits : PackedReviewerNatFits shape.size baseWord := by
        have hle : baseWord <= baseWord * packedSelectWordSize shape.size :=
          Nat.le_mul_of_pos_right baseWord hwordSize
        have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
        have htwoMul := packedTwoMul_le_reviewerBound shape.size
        have hwsSlack := packedRankWordSize_two_le_aux shape.size
        have hauxSlack := packedRankAux_le_reviewerBound shape.size
        have hwsEq :
            packedRankWordSize shape.size =
              packedSelectWordSize shape.size := rfl
        simp only [PackedReviewerNatFits]
        omega
      have hselectFields := hselect.scalar_fields
      intro value hmem
      simp [packedReviewerSelectStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | hselectMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact hbaseFits
      · exact hselectFields value hselectMem
  | done value =>
      intro fieldValue hmem
      cases value with
      | none =>
          simp [packedReviewerSelectStateNatFields,
            packedReviewerOptionNatFields] at hmem
      | some close =>
          simp only [packedReviewerSelectStateNatFields,
            packedReviewerOptionNatFields, List.mem_singleton] at hmem
          subst fieldValue
          exact (hstate close rfl).1

/-! ## Pending-request positivity for the nested components -/

private theorem packedReviewerEntryNextRequest_remaining_pos
    {state : PackedReviewerEntryState}
    {request : PackedReviewerLogicalRequest}
    (h : packedReviewerEntryNextRequest state = some request) :
    0 < packedReviewerEntryRemaining state := by
  cases state <;>
    simp_all [packedReviewerEntryNextRequest, packedReviewerEntryRemaining]

private theorem packedReviewerRankNextRequest_remaining_pos
    {state : PackedReviewerRankState}
    {request : PackedReviewerLogicalRequest}
    (h : packedReviewerRankNextRequest state = some request) :
    0 < packedReviewerRankRemaining state := by
  cases state with
  | fold invocation kind n word effectiveLimit j remaining acc base =>
      cases remaining <;>
        simp_all [packedReviewerRankNextRequest,
          packedReviewerRankRemaining]
  | done value =>
      simp [packedReviewerRankNextRequest] at h
  | _ =>
      simp_all [packedReviewerRankNextRequest, packedReviewerRankRemaining]

private theorem packedReviewerWordSelectNextRequest_remaining_pos
    {state : PackedReviewerWordSelectState}
    {request : PackedReviewerLogicalRequest}
    (h : packedReviewerWordSelectNextRequest state = some request) :
    0 < packedReviewerWordSelectRemaining state := by
  cases state <;>
    simp_all [packedReviewerWordSelectNextRequest,
      packedReviewerWordSelectRemaining]

/-- Extract the pending request's width from a remaining-fuel witness. -/
private theorem packedReviewerRequestsFitFrom_head_operands_fit
    {State : Type} {n : Nat} {store : WordRAM.ReadStore}
    {nextRequest : State -> Option PackedReviewerLogicalRequest}
    {consumeReply : State -> Option (List Bool) -> State}
    {remaining : Nat} {state : State}
    {request : PackedReviewerLogicalRequest}
    (hfit :
      PackedReviewerRequestsFitFrom n store nextRequest consumeReply
        remaining state)
    (hpos : 0 < remaining)
    (hrequest : nextRequest state = some request) :
    PackedReviewerLogicalRequestOperandsFit n request := by
  obtain ⟨fuel, rfl⟩ : exists fuel, remaining = fuel + 1 :=
    ⟨remaining - 1, by omega⟩
  exact (PackedReviewerRequestsFitFrom.step n store nextRequest consumeReply
    fuel state request hfit hrequest).1

/-- Every request the canonical select tower emits has fitting operands. -/
private theorem PackedReviewerSelectCanonicalScalarFits.nextRequest_operands_fit
    {shape : CartesianShape} {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectCanonicalScalarFits shape state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerSelectNextRequest state = some request) :
    PackedReviewerLogicalRequestOperandsFit shape.size request := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  cases state with
  | superEntry invocation n index entry =>
      obtain ⟨rfl, hinv, hindex, hentry⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      have hslot :
          PackedReviewerNatFits shape.size
            (GenericSelect.selectSuperSlot index
              (packedSelectSuperStride shape.size)) := by
        have hle : GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size) <= index :=
          Nat.div_le_self _ _
        omega
      exact packedReviewerRequestsFitFrom_head_operands_fit
        (hentry.requests_fit hinv hslot)
        (packedReviewerEntryNextRequest_remaining_pos hrequest) hrequest
  | localEntry invocation n index localSlot super entry =>
      obtain ⟨rfl, hinv, hindex, hsuperGeo, hshort, hslotEq, hentry⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      have hvalid : index < GenericSelect.occurrenceCount shape.bpCode false := by
        rw [packedSelectOccurrenceCount_eq_size]; exact hindex
      have hfacts := GenericSelect.localSlot_facts shape.bpCode false index
        super (by
          simpa [packedSelectSuperStride, CartesianShape.bpCode_length] using
            hsuperGeo.get_eq)
        hvalid hshort
      have hslotFits : PackedReviewerNatFits shape.size localSlot := by
        rw [hslotEq]
        have hbound := packedReviewerLocalSlots_lt_two_pow shape
        have hlt := hfacts.1
        rw [localSlotCount_eq_packed] at hlt
        have hlen := CartesianShape.bpCode_length shape
        simp only [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
          packedSelectLocalStride, hlen] at hlt ⊢
        omega
      exact packedReviewerRequestsFitFrom_head_operands_fit
        (hentry.requests_fit hinv hslotFits)
        (packedReviewerEntryNextRequest_remaining_pos hrequest) hrequest
  | longRank invocation n index super rank =>
      obtain ⟨rfl, hinv, hindex, hsuperGeo, hlong, hrankFit, hrank,
        horbit⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | longRelative invocation base slot =>
      obtain ⟨hinv, hbase, hbaseLe, hslot, _⟩ := hstate
      simp only [packedReviewerSelectNextRequest, Option.some.injEq]
        at hrequest
      subst request
      apply packedReviewerLogicalRequestOperandsFit_mk
      · exact hinv
      · intro operand hmem
        simp [packedReviewerReadSiteOperands] at hmem
      · exact packedReviewerSegment_le_twentyTwo_fits shape.size 12
          (by omega)
      · exact hslot
  | sparseRank invocation n index localSlot super loc rank =>
      obtain ⟨rfl, hinv, hindex, hlocalGeo, hslotEq, hmarked, hrankFit,
        hrank, horbit⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | sparseRelative invocation base slot =>
      obtain ⟨hinv, hbase, hbaseLe, hslot, _⟩ := hstate
      simp only [packedReviewerSelectNextRequest, Option.some.injEq]
        at hrequest
      subst request
      apply packedReviewerLogicalRequestOperandsFit_mk
      · exact hinv
      · intro operand hmem
        simp [packedReviewerReadSiteOperands] at hmem
      · exact packedReviewerSegment_le_twentyTwo_fits shape.size 16
          (by omega)
      · exact hslot
  | denseFirstWord invocation n index basePosition baseOccurrence =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc⟩ := hstate
      simp only [packedReviewerSelectNextRequest, Option.some.injEq]
        at hrequest
      subst request
      have hslotFits :
          PackedReviewerNatFits shape.size
            (basePosition / packedSelectWordSize shape.size) := by
        have hle : basePosition / packedSelectWordSize shape.size <=
            basePosition := Nat.div_le_self _ _
        have hbound := packedReviewerTwoMul_add_three_le_cellBound shape.size
        have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
        omega
      apply packedReviewerLogicalRequestOperandsFit_mk
      · exact hinv
      · intro operand hmem
        simp only [packedReviewerReadSiteOperands,
          List.mem_singleton] at hmem
        subst operand
        exact hslotFits
      · exact packedReviewerSegment_le_twentyTwo_fits shape.size 0 (by omega)
      · exact hslotFits
  | denseBeforeRank invocation n index basePosition baseOccurrence word rank =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hword, hwordLen, -, hrankFit,
        hrank, hbudget⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hbefore, hword, hwordLen, -,
        hrankFit, hrank, hbudget⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | denseFirstSelect invocation n baseWord select =>
      obtain ⟨rfl, hinv, hbase, hselectFit, ⟨word, hword, hwordLen, -, hselect⟩,
        hremaining⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hselectFit
        (packedReviewerWordSelectNextRequest_remaining_pos hrequest) hrequest
  | denseSecondWord invocation n index basePosition baseOccurrence beforeFirst
      uptoFirst =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hbefore, hupto⟩ := hstate
      simp only [packedReviewerSelectNextRequest, Option.some.injEq]
        at hrequest
      subst request
      have hslotFits :
          PackedReviewerNatFits shape.size
            (basePosition / packedSelectWordSize shape.size + 1) := by
        have hle : basePosition / packedSelectWordSize shape.size <=
            basePosition := Nat.div_le_self _ _
        have hbound := packedReviewerTwoMul_add_three_le_cellBound shape.size
        have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
        omega
      apply packedReviewerLogicalRequestOperandsFit_mk
      · exact hinv
      · intro operand hmem
        simp only [packedReviewerReadSiteOperands,
          List.mem_singleton] at hmem
        subst operand
        exact hslotFits
      · exact packedReviewerSegment_le_twentyTwo_fits shape.size 0 (by omega)
      · exact hslotFits
  | denseSecondSelect invocation n baseWord select =>
      obtain ⟨rfl, hinv, hbase, hselectFit, ⟨word, hword, hwordLen, -, hselect⟩,
        hremaining⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hselectFit
        (packedReviewerWordSelectNextRequest_remaining_pos hrequest) hrequest
  | done value =>
      simp [packedReviewerSelectNextRequest] at hrequest

/-- A canonically bounded rank component never exceeds its eleven-read start. -/
private theorem PackedReviewerRankCanonicalScalarFits.remaining_le_eleven
    {shape : CartesianShape} {resultBound : Nat}
    {state : PackedReviewerRankState}
    (hstate : PackedReviewerRankCanonicalScalarFits shape resultBound state) :
    packedReviewerRankRemaining state <= 11 := by
  cases state with
  | fold invocation kind n word effectiveLimit j remaining acc base =>
      obtain ⟨-, -, -, -, hj, -⟩ := hstate
      simp only [packedReviewerRankRemaining]
      omega
  | done value => simp [packedReviewerRankRemaining]
  | superSample invocation kind n pos => simp [packedReviewerRankRemaining]
  | blockSample invocation kind n pos superSample =>
      simp [packedReviewerRankRemaining]
  | word invocation kind n pos superSample blockSample =>
      simp [packedReviewerRankRemaining]

/-- The canonical select tower stays inside its thirty-five-read budget. -/
private theorem PackedReviewerSelectCanonicalScalarFits.remaining_le_thirtyFive
    {shape : CartesianShape} {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectCanonicalScalarFits shape state) :
    packedReviewerSelectRemaining state <= 35 := by
  cases state with
  | superEntry invocation n index entry =>
      cases entry <;>
        simp [packedReviewerSelectRemaining, packedReviewerEntryRemaining]
  | localEntry invocation n index localSlot super entry =>
      cases entry <;>
        simp [packedReviewerSelectRemaining, packedReviewerEntryRemaining]
  | longRank invocation n index super rank =>
      obtain ⟨-, -, -, -, -, -, hrank, -⟩ := hstate
      have hbound := hrank.remaining_le_eleven
      simp only [packedReviewerSelectRemaining]
      omega
  | longRelative invocation base slot =>
      simp [packedReviewerSelectRemaining]
  | sparseRank invocation n index localSlot super loc rank =>
      obtain ⟨-, -, -, -, -, -, -, hrank, -⟩ := hstate
      have hbound := hrank.remaining_le_eleven
      simp only [packedReviewerSelectRemaining]
      omega
  | sparseRelative invocation base slot =>
      simp [packedReviewerSelectRemaining]
  | denseFirstWord invocation n index basePosition baseOccurrence =>
      simp [packedReviewerSelectRemaining]
  | denseBeforeRank invocation n index basePosition baseOccurrence word rank =>
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hbudget⟩ := hstate
      simp only [packedReviewerSelectRemaining]
      omega
  | denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbudget⟩ := hstate
      simp only [packedReviewerSelectRemaining]
      omega
  | denseFirstSelect invocation n baseWord select =>
      obtain ⟨-, -, -, -, -, hremaining⟩ := hstate
      simp only [packedReviewerSelectRemaining]
      omega
  | denseSecondWord invocation n index basePosition baseOccurrence beforeFirst
      uptoFirst =>
      simp [packedReviewerSelectRemaining]
  | denseSecondSelect invocation n baseWord select =>
      obtain ⟨-, -, -, -, -, hremaining⟩ := hstate
      simp only [packedReviewerSelectRemaining]
      omega
  | done value => simp [packedReviewerSelectRemaining]

/-! ## The long-flag rank reference value over the canonical store -/

/-- The canonical store serves segment 21 from the shared fringe table. -/
private theorem packedReviewerGlobalReadStore_fringeChunk
    (shape : CartesianShape) (address : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21 address =
      (SuccinctClose.bpFringeChunkTable
        (SuccinctClose.bpFringeChunkBits
          shape.bpCode.length)).store.words[address]? := by
  rw [← packedExecutedStore_is_reviewerStore shape 21 address]
  change
    (if (21 : Nat) < 20 then
        (concreteBPNativeSuccinctRMQFlatPayloadReadStore shape).readWord?
          21 address
      else if (21 : Nat) = 20 then
        (SuccinctClose.canonicalRelativeRmmInteriorComponentStore
          shape).store.words[address]?
      else if (21 : Nat) = concreteBPNativeFringeChunkTraceSegment then
        (SuccinctClose.bpFringeChunkTable
          (SuccinctClose.bpFringeChunkBits
            shape.bpCode.length)).store.words[address]?
      else if (21 : Nat) = concreteBPNativeSelectChunkTraceSegment then
        (SuccinctClose.bpChunkSelectTable
          (SuccinctClose.bpFringeChunkBits shape.bpCode.length)
            false).store.words[address]?
      else none) = _
  simp [concreteBPNativeFringeChunkTraceSegment]

/-- The long-flag rank reference over the canonical store is the flag rank. -/
private theorem packedReviewerLongFlagRankReference_value_eq
    (shape : CartesianShape) (pos : Nat) :
    (packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1
      pos).value =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.longSuperFlagBits shape.bpCode false) pos := by
  have hbits :
      (GenericSelect.longSuperFlagBits shape.bpCode false).length =
        packedSuperSlots shape.size :=
    packedSelectLongFlagBitsLength_eq shape
  have hwordSize :
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagRankData.wordSize =
        packedLongFlagWordSize shape.size :=
    packedSelectLongFlagRankWordSize_eq shape
  have hbps :
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagRankData.blocksPerSuper = 1 :=
    packedSelectLongFlagRankBlocksPerSuper_eq shape
  have hsuper :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 9
            address =
          ((GenericSelect.sparseExceptionSelectData
            shape.bpCode false).longFlagRankData.superSampleWords
              true)[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_legacy shape (by omega)
      (source :=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLongFlagRankSuperTrue)
      rfl]
    rfl
  have hblock :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 10
            address =
          ((GenericSelect.sparseExceptionSelectData
            shape.bpCode false).longFlagRankData.blockSampleWords
              true)[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_legacy shape (by omega)
      (source :=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLongFlagRankBlockTrue)
      rfl]
    rfl
  have hchunk :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21
            address =
          (SuccinctClose.bpFringeChunkTable
            (packedFringeChunkBits shape.size)).store.words[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_fringeChunk shape address]
    rw [show SuccinctClose.bpFringeChunkBits shape.bpCode.length =
      packedFringeChunkBits shape.size from by
        unfold packedFringeChunkBits
        rw [CartesianShape.bpCode_length]]
  have hword :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 11
            address =
          (GenericSelect.sparseExceptionSelectData
            shape.bpCode
            false).longFlagRankData.bitWords.store.words[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_legacy shape (by omega)
      (source :=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLongFlagBits)
      rfl]
    rfl
  have hconvert :=
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode
        false).longFlagRankData.bpChunkedRankTraceResultWithStore_toCosted_of_agree
      hsuper hblock hword hchunk pos
  have hbitsField :
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagBits.length =
        packedSuperSlots shape.size :=
    packedSelectLongFlagBitsLength_eq shape
  have hchain :
      (packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagBits.length
        ((GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagRankData.wordSize)
        ((GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagRankData.blocksPerSuper)
        pos).value =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.longSuperFlagBits shape.bpCode false) pos := by
    rw [← packedRankRead_eq
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).longFlagRankData
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 9 10 11 21
      (packedFringeChunkBits shape.size) true pos]
    have hvalueToCosted :
        ((GenericSelect.sparseExceptionSelectData
          shape.bpCode
          false).longFlagRankData.bpChunkedRankTraceResultWithStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 9 10 11 21
            (packedFringeChunkBits shape.size) true pos).value =
          ((GenericSelect.sparseExceptionSelectData
            shape.bpCode
            false).longFlagRankData.bpChunkedRankTraceResultWithStore
              (concreteBPNativeSuccinctRMQGlobalReadStore shape) 9 10 11 21
              (packedFringeChunkBits shape.size) true
              pos).toCosted.value := rfl
    rw [hvalueToCosted, hconvert]
    have hc : 0 < packedFringeChunkBits shape.size := by
      unfold packedFringeChunkBits
      exact SuccinctClose.bpFringeChunkBits_pos _
    have hword8 :
        (GenericSelect.sparseExceptionSelectData
            shape.bpCode false).longFlagRankData.wordSize <=
          8 * packedFringeChunkBits shape.size := by
      have hinstance :=
        concreteBPNativeSelectCloseLongFlagRank_wordSize_le_8_chunk shape
      rw [show SuccinctClose.bpFringeChunkBits shape.bpCode.length =
        packedFringeChunkBits shape.size from by
          unfold packedFringeChunkBits
          rw [CartesianShape.bpCode_length]] at hinstance
      exact hinstance
    rw [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankCosted_value_eq
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).longFlagRankData hc hword8 true pos]
    exact
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankCosted_exact
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).longFlagRankData true pos
  rw [hbitsField, hwordSize, hbps] at hchain
  exact hchain

/-- The sparse-flag rank reference over the canonical store is the flag rank. -/
private theorem packedReviewerSparseFlagRankReference_value_eq
    (shape : CartesianShape) (localSlot : Nat) :
    (packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1
      localSlot).value =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false) localSlot := by
  have hbits :
      (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length =
        packedSparseSlots shape.size :=
    sparseFlagBits_length_eq_packed shape
  have hwordSize :
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.rankData.wordSize =
        packedSparseWordSize shape.size :=
    packedSelectSparseRankWordSize_eq shape
  have hbps :
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.rankData.blocksPerSuper = 1 :=
    packedSelectSparseRankBlocksPerSuper_eq shape
  have hsuper :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 13
            address =
          ((GenericSelect.sparseExceptionSelectData
            shape.bpCode false).sparseDirectory.rankData.superSampleWords
              true)[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_legacy shape (by omega)
      (source :=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRankSuperTrue)
      rfl]
    rfl
  have hblock :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 14
            address =
          ((GenericSelect.sparseExceptionSelectData
            shape.bpCode false).sparseDirectory.rankData.blockSampleWords
              true)[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_legacy shape (by omega)
      (source :=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRankBlockTrue)
      rfl]
    rfl
  have hchunk :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 21
            address =
          (SuccinctClose.bpFringeChunkTable
            (packedFringeChunkBits shape.size)).store.words[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_fringeChunk shape address]
    rw [show SuccinctClose.bpFringeChunkBits shape.bpCode.length =
      packedFringeChunkBits shape.size from by
        unfold packedFringeChunkBits
        rw [CartesianShape.bpCode_length]]
  have hword :
      forall address,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 15
            address =
          (GenericSelect.sparseExceptionSelectData
            shape.bpCode
            false).sparseDirectory.rankData.bitWords.store.words[address]? := by
    intro address
    rw [packedReviewerGlobalReadStore_legacy shape (by omega)
      (source :=
        ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseFlagBits)
      rfl]
    rfl
  have hconvert :=
    (GenericSelect.sparseExceptionSelectData
        shape.bpCode
        false).sparseDirectory.rankData.bpChunkedRankTraceResultWithStore_toCosted_of_agree
      hsuper hblock hword hchunk localSlot
  have hbitsField :
      (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.flagBits.length =
        packedSparseSlots shape.size :=
    packedSelectSparseFlagBitsLength_eq shape
  have hchain :
      (packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.flagBits.length
        ((GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.rankData.wordSize)
        ((GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.rankData.blocksPerSuper)
        localSlot).value =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false) localSlot := by
    rw [← packedRankRead_eq
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).sparseDirectory.rankData
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 13 14 15 21
      (packedFringeChunkBits shape.size) true localSlot]
    have hvalueToCosted :
        ((GenericSelect.sparseExceptionSelectData
          shape.bpCode
          false).sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 13 14 15 21
            (packedFringeChunkBits shape.size) true localSlot).value =
          ((GenericSelect.sparseExceptionSelectData
            shape.bpCode
            false).sparseDirectory.rankData.bpChunkedRankTraceResultWithStore
              (concreteBPNativeSuccinctRMQGlobalReadStore shape) 13 14 15 21
              (packedFringeChunkBits shape.size) true
              localSlot).toCosted.value := rfl
    rw [hvalueToCosted, hconvert]
    have hc : 0 < packedFringeChunkBits shape.size := by
      unfold packedFringeChunkBits
      exact SuccinctClose.bpFringeChunkBits_pos _
    have hword8 :
        (GenericSelect.sparseExceptionSelectData
            shape.bpCode false).sparseDirectory.rankData.wordSize <=
          8 * packedFringeChunkBits shape.size := by
      have hinstance :=
        concreteBPNativeSelectCloseSparseRank_wordSize_le_8_chunk shape
      rw [show SuccinctClose.bpFringeChunkBits shape.bpCode.length =
        packedFringeChunkBits shape.size from by
          unfold packedFringeChunkBits
          rw [CartesianShape.bpCode_length]] at hinstance
      exact hinstance
    rw [SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankCosted_value_eq
      (GenericSelect.sparseExceptionSelectData
        shape.bpCode false).sparseDirectory.rankData hc hword8 true localSlot]
    exact
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankCosted_exact
        (GenericSelect.sparseExceptionSelectData
          shape.bpCode false).sparseDirectory.rankData true localSlot
  rw [hbitsField, hwordSize, hbps] at hchain
  exact hchain

private theorem PackedReviewerSelectCanonicalScalarFits.result_fits
    {shape : CartesianShape} {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectCanonicalScalarFits shape state)
    {close : Nat}
    (hresult : packedReviewerSelectResult state = some (some close)) :
    PackedReviewerNatFits shape.size close ∧
      close <= 2 * shape.size + 1 := by
  cases state <;> simp [packedReviewerSelectResult] at hresult
  case done value =>
    subst hresult
    exact hstate close rfl

/-- Any successful segment-12 read at the canonical long compact slot decodes
to the relative exception offset, so the reassembled select position stays
inside the parenthesis string. -/
private theorem packedReviewerLongRelative_read_content_le
    (shape : CartesianShape) (index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hindex : index < shape.size)
    (hsuperGeo : PackedReviewerCanonicalSuperGeometry shape index super)
    (hlong : GenericSelect.relativeSplitSelectEntryIsMarked super = true) :
    forall word,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 12
          (GenericSelect.relativeSplitSelectLongCompactSlot
            (RMQ.Succinct.rankPrefix true
              (GenericSelect.longSuperFlagBits shape.bpCode false)
              (GenericSelect.selectSuperSlot index
                (packedSelectSuperStride shape.size)))
            (index - super.baseOccurrence)
            (packedSelectSuperStride shape.size)) = some word ->
        GenericSelect.relativeSplitSelectEntryBasePosition
            (packedSelectWordSize shape.size) super +
          SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1 := by
  intro word hread
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hvalid : index < GenericSelect.occurrenceCount shape.bpCode false := by
    rw [packedSelectOccurrenceCount_eq_size]
    exact hindex
  have hsuper' :
      (GenericSelect.superEntries shape.bpCode false)[
        GenericSelect.selectSuperSlot index
          (GenericSelect.superStride shape.bpCode.length)]? = some super := by
    simpa [packedSelectSuperStride, CartesianShape.bpCode_length] using
      hsuperGeo.get_eq
  have hexact :=
    GenericSelect.longExplicit_exact shape.bpCode false index super hsuper'
      hvalid hlong
  have hwords :
      forall i,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 12 i =
          (GenericSelect.longSuperRelativeTable shape.bpCode
            false).store.words[i]? :=
    fun i =>
      packedReviewerGlobalReadStore_legacy shape (by omega)
        (source :=
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectLongRelative)
        rfl i
  have hstore :
      (GenericSelect.longSuperRelativeTable shape.bpCode false).store.words[
        GenericSelect.relativeSplitSelectLongCompactSlot
          (RMQ.Succinct.rankPrefix true
            (GenericSelect.longSuperFlagBits shape.bpCode false)
            (GenericSelect.selectSuperSlot index
              (GenericSelect.superStride shape.bpCode.length)))
          (index - super.baseOccurrence)
          (GenericSelect.superStride shape.bpCode.length)]? = some word := by
    rw [← hwords]
    simpa [packedSelectSuperStride, CartesianShape.bpCode_length] using hread
  have hcodec :=
    (GenericSelect.longSuperRelativeTable shape.bpCode false).read_exact
      (GenericSelect.relativeSplitSelectLongCompactSlot
        (RMQ.Succinct.rankPrefix true
          (GenericSelect.longSuperFlagBits shape.bpCode false)
          (GenericSelect.selectSuperSlot index
            (GenericSelect.superStride shape.bpCode.length)))
        (index - super.baseOccurrence)
        (GenericSelect.superStride shape.bpCode.length))
  rw [hstore] at hcodec
  simp only [Option.map_some] at hcodec
  rw [← hcodec] at hexact
  simp only [Option.map_some] at hexact
  have hpos := RMQ.Succinct.select_bounds hexact.symm
  have hbase :
      GenericSelect.relativeSplitSelectEntryBasePosition
          (GenericSelect.wordBits shape.bpCode.length) super =
        GenericSelect.relativeSplitSelectEntryBasePosition
          (packedSelectWordSize shape.size) super := by
    simp [packedSelectWordSize, CartesianShape.bpCode_length]
  rw [hbase] at hpos
  omega

/-- Any successful segment-16 read at the canonical sparse compact slot decodes
to the relative exception offset, so the reassembled select position stays
inside the parenthesis string. -/
private theorem packedReviewerSparseRelative_read_content_le
    (shape : CartesianShape) (index : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hindex : index < shape.size)
    (hlocalGeo : PackedReviewerCanonicalLocalGeometry shape index super loc)
    (hmarked : GenericSelect.relativeSplitSelectEntryIsMarked loc = true) :
    forall word,
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16
          (GenericSelect.relativeSplitSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
              (GenericSelect.relativeSplitSelectLocalSlot index
                (packedSelectSuperStride shape.size)
                (packedSelectLocalSlotsPerSuper shape.size)
                (packedSelectLocalStride shape.size) super))
            (index -
              GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
            (packedSelectLocalStride shape.size)) = some word ->
        GenericSelect.relativeSplitSelectLocalBasePosition
            (packedSelectWordSize shape.size) super loc +
          SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1 := by
  intro word hread
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hvalid : index < GenericSelect.occurrenceCount shape.bpCode false := by
    rw [packedSelectOccurrenceCount_eq_size]
    exact hindex
  have hsuper' :
      (GenericSelect.superEntries shape.bpCode false)[
        GenericSelect.selectSuperSlot index
          (GenericSelect.superStride shape.bpCode.length)]? = some super := by
    simpa [packedSelectSuperStride, CartesianShape.bpCode_length] using
      hlocalGeo.super_geometry.get_eq
  obtain ⟨hslot, heff, hlive, hsameSuper, hbaseLe, hendStride⟩ :=
    GenericSelect.localSlot_facts shape.bpCode false index super hsuper'
      hvalid hlocalGeo.super_short
  have hlocalAtSlot :
      (GenericSelect.localEntries shape.bpCode false)[
        GenericSelect.relativeSplitSelectLocalSlot index
          (GenericSelect.superStride shape.bpCode.length)
          (GenericSelect.localSlotsPerSuper shape.bpCode.length)
          (GenericSelect.localStride shape.bpCode.length) super]? =
        some loc := by
    simpa [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
      packedSelectLocalStride, CartesianShape.bpCode_length] using
      hlocalGeo.get_eq
  have hbuiltLocal :=
    GenericSelect.localEntries_get? shape.bpCode false
      (globalLocalSlot :=
        GenericSelect.relativeSplitSelectLocalSlot index
          (GenericSelect.superStride shape.bpCode.length)
          (GenericSelect.localSlotsPerSuper shape.bpCode.length)
          (GenericSelect.localStride shape.bpCode.length) super) hslot
  rw [hbuiltLocal] at hlocalAtSlot
  have hlocEq :
      loc =
        GenericSelect.localEntry shape.bpCode false
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride shape.bpCode.length)
            (GenericSelect.localSlotsPerSuper shape.bpCode.length)
            (GenericSelect.localStride shape.bpCode.length) super) :=
    (Option.some.inj hlocalAtSlot).symm
  have hflag :
      GenericSelect.localIsSparseException shape.bpCode false
        (GenericSelect.relativeSplitSelectLocalSlot index
          (GenericSelect.superStride shape.bpCode.length)
          (GenericSelect.localSlotsPerSuper shape.bpCode.length)
          (GenericSelect.localStride shape.bpCode.length) super) = true := by
    have hmark :=
      GenericSelect.localEntry_marked_eq_flag shape.bpCode false
        (GenericSelect.relativeSplitSelectLocalSlot index
          (GenericSelect.superStride shape.bpCode.length)
          (GenericSelect.localSlotsPerSuper shape.bpCode.length)
          (GenericSelect.localStride shape.bpCode.length) super)
    rw [← hlocEq] at hmark
    rw [hmark] at hmarked
    have hpair :
        GenericSelect.compactLocalEntryIsLive shape.bpCode false
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super) = true ∧
          GenericSelect.localIsSparseException shape.bpCode false
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super) =
            true := by
      simpa using hmarked
    exact hpair.2
  have hlocalOcc :
      index -
          GenericSelect.localBaseOccurrence shape.bpCode.length
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super) <
        GenericSelect.localStride shape.bpCode.length := by
    omega
  have hqEq :
      GenericSelect.localBaseOccurrence shape.bpCode.length
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride shape.bpCode.length)
            (GenericSelect.localSlotsPerSuper shape.bpCode.length)
            (GenericSelect.localStride shape.bpCode.length) super) +
        (index -
          GenericSelect.localBaseOccurrence shape.bpCode.length
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super)) =
        index := by
    omega
  have hbaseLeSuper :
      GenericSelect.selectSuperSlot index
          (GenericSelect.superStride shape.bpCode.length) *
        GenericSelect.superStride shape.bpCode.length <= index := by
    have hmul :=
      Nat.div_mul_le_self index
        (GenericSelect.superStride shape.bpCode.length)
    simpa [GenericSelect.selectSuperSlot] using hmul
  have hqLtBaseStride :
      index <
        GenericSelect.selectSuperSlot index
            (GenericSelect.superStride shape.bpCode.length) *
          GenericSelect.superStride shape.bpCode.length +
          GenericSelect.superStride shape.bpCode.length := by
    have hstride := GenericSelect.superStride_pos shape.bpCode.length
    have hlt := Nat.lt_div_mul_add hstride (a := index)
    simpa [GenericSelect.selectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      index <
        GenericSelect.superEndOccurrence shape.bpCode false
          (GenericSelect.selectSuperSlot index
            (GenericSelect.superStride shape.bpCode.length)) := by
    unfold GenericSelect.superEndOccurrence GenericSelect.superBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hvalid⟩
  have hend :
      GenericSelect.localBaseOccurrence shape.bpCode.length
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride shape.bpCode.length)
            (GenericSelect.localSlotsPerSuper shape.bpCode.length)
            (GenericSelect.localStride shape.bpCode.length) super) +
        (index -
          GenericSelect.localBaseOccurrence shape.bpCode.length
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super)) <
        GenericSelect.superEndOccurrence shape.bpCode false
          (GenericSelect.localSuperSlot shape.bpCode.length
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super)) := by
    rw [hqEq, hsameSuper]
    exact hqLtSuperEnd
  rcases GenericSelect.select_exists_of_lt_occurrenceCount shape.bpCode false
      hvalid with ⟨pos, hselect⟩
  have hselectLocal :
      RMQ.Succinct.select false shape.bpCode
          (GenericSelect.localBaseOccurrence shape.bpCode.length
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super) +
            (index -
              GenericSelect.localBaseOccurrence shape.bpCode.length
                (GenericSelect.relativeSplitSelectLocalSlot index
                  (GenericSelect.superStride shape.bpCode.length)
                  (GenericSelect.localSlotsPerSuper shape.bpCode.length)
                  (GenericSelect.localStride shape.bpCode.length) super))) =
        some pos := by
    simpa [hqEq] using hselect
  have hlookup :=
    GenericSelect.sparseExceptionRelativeEntries_lookup_exact shape.bpCode
      false hslot hflag hlocalOcc hend hselectLocal
  have hwords :
      forall i,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16 i =
          (GenericSelect.sparseExceptionRelativeTable shape.bpCode
            false).store.words[i]? :=
    fun i =>
      packedReviewerGlobalReadStore_legacy shape (by omega)
        (source :=
          ConcreteBPNativeSuccinctRMQFlatPayloadSource.selectSparseRelative)
        rfl i
  have hbaseOcc :
      GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc =
        GenericSelect.localBaseOccurrence shape.bpCode.length
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride shape.bpCode.length)
            (GenericSelect.localSlotsPerSuper shape.bpCode.length)
            (GenericSelect.localStride shape.bpCode.length) super) := by
    have hb := hlocalGeo.baseOccurrence_eq
    simpa [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
      packedSelectLocalStride, CartesianShape.bpCode_length] using hb
  have hstore :
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode
        false).store.words[
          RMQ.Succinct.rankPrefix true
            (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super) *
            GenericSelect.localStride shape.bpCode.length +
          (index -
            GenericSelect.localBaseOccurrence shape.bpCode.length
              (GenericSelect.relativeSplitSelectLocalSlot index
                (GenericSelect.superStride shape.bpCode.length)
                (GenericSelect.localSlotsPerSuper shape.bpCode.length)
                (GenericSelect.localStride shape.bpCode.length) super))]? =
        some word := by
    rw [← hwords]
    simpa [GenericSelect.relativeSplitSelectSparseCompactSlot,
      packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
      packedSelectLocalStride, CartesianShape.bpCode_length, hbaseOcc]
      using hread
  have hcodec :=
    (GenericSelect.sparseExceptionRelativeTable shape.bpCode
      false).read_exact
      (RMQ.Succinct.rankPrefix true
          (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride shape.bpCode.length)
            (GenericSelect.localSlotsPerSuper shape.bpCode.length)
            (GenericSelect.localStride shape.bpCode.length) super) *
          GenericSelect.localStride shape.bpCode.length +
        (index -
          GenericSelect.localBaseOccurrence shape.bpCode.length
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super)))
  rw [hstore] at hcodec
  simp only [Option.map_some] at hcodec
  rw [hlookup] at hcodec
  have hentry :
      SuccinctSpace.bitsToNatLE word =
        pos -
          GenericSelect.position shape.bpCode false
            (GenericSelect.localBaseOccurrence shape.bpCode.length
              (GenericSelect.relativeSplitSelectLocalSlot index
                (GenericSelect.superStride shape.bpCode.length)
                (GenericSelect.localSlotsPerSuper shape.bpCode.length)
                (GenericSelect.localStride shape.bpCode.length) super)) :=
    Option.some.inj hcodec
  have hposLt := RMQ.Succinct.select_bounds hselect
  have hposition :=
    GenericSelect.position_le_length shape.bpCode false
      (GenericSelect.localBaseOccurrence shape.bpCode.length
        (GenericSelect.relativeSplitSelectLocalSlot index
          (GenericSelect.superStride shape.bpCode.length)
          (GenericSelect.localSlotsPerSuper shape.bpCode.length)
          (GenericSelect.localStride shape.bpCode.length) super))
  have hbasePos :
      GenericSelect.relativeSplitSelectLocalBasePosition
          (packedSelectWordSize shape.size) super loc =
        GenericSelect.position shape.bpCode false
          (GenericSelect.localBaseOccurrence shape.bpCode.length
            (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride shape.bpCode.length)
              (GenericSelect.localSlotsPerSuper shape.bpCode.length)
              (GenericSelect.localStride shape.bpCode.length) super)) := by
    have hb := hlocalGeo.basePosition_eq
    simpa [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
      packedSelectLocalStride, CartesianShape.bpCode_length] using hb
  rw [hbasePos, hentry]
  omega

/-- A completed long-flag rank orbit is exactly the marked-super prefix rank. -/
private theorem packedReviewerSelectLongRank_orbit_value_eq
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat) (rank : PackedReviewerRankState) {exceptionRank : Nat}
    (horbit :
      exists fuel,
        rank =
          packedReviewerRankCanonicalRun shape fuel
            (.superSample invocation .selectLong shape.size
              (GenericSelect.selectSuperSlot index
                (packedSelectSuperStride shape.size))))
    (hresult : packedReviewerRankResult rank = some exceptionRank) :
    exceptionRank =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.longSuperFlagBits shape.bpCode false)
        (GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size)) := by
  obtain ⟨fuel, rfl⟩ := horbit
  have hvalue :=
    packedReviewerRankCanonicalRun_result_eq shape invocation .selectLong
      (GenericSelect.selectSuperSlot index (packedSelectSuperStride shape.size))
      fuel hresult
  exact hvalue.trans
    (packedReviewerLongFlagRankReference_value_eq shape
      (GenericSelect.selectSuperSlot index
        (packedSelectSuperStride shape.size)))

/-- A completed sparse rank orbit is exactly the sparse-exception prefix rank. -/
private theorem packedReviewerSelectSparseRank_orbit_value_eq
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (localSlot : Nat) (rank : PackedReviewerRankState) {exceptionRank : Nat}
    (hslot : localSlot < packedSparseSlots shape.size)
    (horbit :
      exists fuel,
        rank =
          packedReviewerRankCanonicalRun shape fuel
            (.superSample invocation .selectSparse shape.size localSlot))
    (hresult : packedReviewerRankResult rank = some exceptionRank) :
    exceptionRank =
      RMQ.Succinct.rankPrefix true
        (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
        localSlot := by
  obtain ⟨fuel, rfl⟩ := horbit
  have hvalue :=
    packedReviewerRankCanonicalRun_result_eq shape invocation .selectSparse
      localSlot fuel hresult
  have heffective :=
    hvalue.trans
      (packedReviewerSparseFlagRankReference_value_eq shape localSlot)
  rw [heffective]
  have hcount :
      GenericSelect.sparseExceptionEffectiveLocalSlotCount shape.bpCode
        false = packedSparseSlots shape.size := by
    rw [← GenericSelect.sparseExceptionEffectiveFlagBits_length,
      sparseFlagBits_length_eq_packed]
  exact
    GenericSelect.sparseExceptionEffectiveFlagBits_prefix_eq shape.bpCode
      false (by omega)

/-! ## Select tower consume transitions, one arm at a time -/

/-- Entering the long-flag rank phase from a marked super directory entry. -/
private theorem packedReviewerSelectAfterSuper_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (super? : Option GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hget :
      super? =
        (GenericSelect.superEntries shape.bpCode false)[
          GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size)]?) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterSuper invocation shape.size index super?) := by
  cases super? with
  | none =>
      intro close hclose
      simp [packedReviewerSelectAfterSuper] at hclose
  | some super =>
      have hgeometry : PackedReviewerCanonicalSuperGeometry shape index super :=
        ⟨hindex, hget.symm⟩
      unfold packedReviewerSelectAfterSuper
      by_cases hmarked :
          GenericSelect.relativeSplitSelectEntryIsMarked super = true
      · simp only [hmarked, if_true]
        refine ⟨rfl, hinv, hindex, hgeometry, hmarked, ?_, ?_, ⟨0, rfl⟩⟩
        · have hwitness :=
            packedReviewerRankStart_requests_fit shape invocation .selectLong
              (GenericSelect.selectSuperSlot index
                (packedSelectSuperStride shape.size)) hinv
          simpa [packedReviewerRankRemaining] using hwitness
        · exact packedReviewerRankStart_canonicalScalarFits shape invocation
            .selectLong
            (GenericSelect.selectSuperSlot index
              (packedSelectSuperStride shape.size)) hinv
            (by
              have hle : GenericSelect.selectSuperSlot index
                  (packedSelectSuperStride shape.size) <= index :=
                Nat.div_le_self _ _
              have hn :=
                packedReviewerInputSize_lt_two_pow_cellWidth shape.size
              omega)
      · have hshort :
            GenericSelect.relativeSplitSelectEntryIsMarked super = false := by
          simpa using hmarked
        simp only [hmarked, if_false]
        exact ⟨rfl, hinv, hindex, hgeometry, hshort, rfl, .baseOccurrence⟩

/-- One canonical reply preserves the super-entry arm of the select tower. -/
private theorem packedReviewerSelectConsume_superEntry_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat) (entry : PackedReviewerEntryState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hentry :
      PackedReviewerCanonicalEntryState shape invocation .super
        (GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size)) entry)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerEntryNextRequest entry = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.superEntry invocation shape.size index entry)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hentry' := hentry.consume hrequest
  simp only [packedReviewerSelectConsumeReply]
  cases hresult :
      packedReviewerEntryResult
        (packedReviewerEntryConsumeReply entry
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none => exact ⟨rfl, hinv, hindex, hentry'⟩
  | some super? =>
      have hget := hentry'.result_eq hresult
      exact packedReviewerSelectAfterSuper_fits shape invocation index super?
        hinv hindex hget

/-- Entering the sparse rank or dense word phase from a local entry. -/
private theorem packedReviewerSelectAfterLocal_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (loc? : Option GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hsuperGeo : PackedReviewerCanonicalSuperGeometry shape index super)
    (hshort : GenericSelect.relativeSplitSelectEntryIsMarked super = false)
    (hget :
      loc? =
        (GenericSelect.localEntries shape.bpCode false)[
          GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super]?) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterLocal invocation shape.size index
        (GenericSelect.relativeSplitSelectLocalSlot index
          (packedSelectSuperStride shape.size)
          (packedSelectLocalSlotsPerSuper shape.size)
          (packedSelectLocalStride shape.size) super)
        super loc?) := by
  cases loc? with
  | none =>
      intro close hclose
      simp [packedReviewerSelectAfterLocal] at hclose
  | some loc =>
      have hgeometry :
          PackedReviewerCanonicalLocalGeometry shape index super loc :=
        ⟨hsuperGeo, hshort, hget.symm⟩
      unfold packedReviewerSelectAfterLocal
      by_cases hmarked :
          GenericSelect.relativeSplitSelectEntryIsMarked loc = true
      · simp only [hmarked, if_true]
        refine ⟨rfl, hinv, hindex, hgeometry, rfl, hmarked, ?_, ?_, ⟨0, rfl⟩⟩
        · have hwitness :=
            packedReviewerRankStart_requests_fit shape invocation .selectSparse
              (GenericSelect.relativeSplitSelectLocalSlot index
                (packedSelectSuperStride shape.size)
                (packedSelectLocalSlotsPerSuper shape.size)
                (packedSelectLocalStride shape.size) super) hinv
          simpa [packedReviewerRankRemaining] using hwitness
        · exact packedReviewerRankStart_canonicalScalarFits shape invocation
            .selectSparse
            (GenericSelect.relativeSplitSelectLocalSlot index
              (packedSelectSuperStride shape.size)
              (packedSelectLocalSlotsPerSuper shape.size)
              (packedSelectLocalStride shape.size) super) hinv
            hgeometry.localSlot_fits
      · have hlocShort :
            GenericSelect.relativeSplitSelectEntryIsMarked loc = false := by
          simpa using hmarked
        simp only [hmarked, if_false]
        have hbaseFits := hgeometry.base_fields_fit
        refine ⟨rfl, hinv, hindex, ?_, ?_⟩
        · rw [hgeometry.basePosition_eq]
          have hposition :=
            GenericSelect.position_le_length shape.bpCode false
              (GenericSelect.localBaseOccurrence shape.bpCode.length
                (GenericSelect.relativeSplitSelectLocalSlot index
                  (packedSelectSuperStride shape.size)
                  (packedSelectLocalSlotsPerSuper shape.size)
                  (packedSelectLocalStride shape.size) super))
          have hlength : shape.bpCode.length <= 2 * shape.size + 1 := by
            simp [CartesianShape.bpCode_length]
          omega
        · rw [hgeometry.baseOccurrence_eq]
          exact hgeometry.facts.2.2.2.2

/-- One canonical reply preserves the local-entry arm of the select tower. -/
private theorem packedReviewerSelectConsume_localEntry_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (entry : PackedReviewerEntryState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hsuperGeo : PackedReviewerCanonicalSuperGeometry shape index super)
    (hshort : GenericSelect.relativeSplitSelectEntryIsMarked super = false)
    (hentry :
      PackedReviewerCanonicalEntryState shape invocation .local
        (GenericSelect.relativeSplitSelectLocalSlot index
          (packedSelectSuperStride shape.size)
          (packedSelectLocalSlotsPerSuper shape.size)
          (packedSelectLocalStride shape.size) super) entry)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerEntryNextRequest entry = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.localEntry invocation shape.size index
          (GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super)
          super entry)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hentry' := hentry.consume hrequest
  simp only [packedReviewerSelectConsumeReply]
  cases hresult :
      packedReviewerEntryResult
        (packedReviewerEntryConsumeReply entry
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none => exact ⟨rfl, hinv, hindex, hsuperGeo, hshort, rfl, hentry'⟩
  | some loc? =>
      have hget := hentry'.result_eq hresult
      exact packedReviewerSelectAfterLocal_fits shape invocation index super
        loc? hinv hindex hsuperGeo hshort hget

/-- Entering the long-relative directory after the flag rank completes. -/
private theorem packedReviewerSelectAfterLongRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (exceptionRank : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hsuperGeo : PackedReviewerCanonicalSuperGeometry shape index super)
    (hrank :
      exceptionRank <=
        packedReviewerRankQueryPos .selectLong shape.size
          (GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size)))
    (hcontent :
      forall word,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 12
            (GenericSelect.relativeSplitSelectLongCompactSlot exceptionRank
              (index - super.baseOccurrence)
              (packedSelectSuperStride shape.size)) = some word ->
          GenericSelect.relativeSplitSelectEntryBasePosition
              (packedSelectWordSize shape.size) super +
            SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterLongRank invocation shape.size index super
        exceptionRank) := by
  unfold packedReviewerSelectAfterLongRank
  have hbase := hsuperGeo.basePosition_fits
  have hbaseLe :
      GenericSelect.relativeSplitSelectEntryBasePosition
          (packedSelectWordSize shape.size) super <=
        2 * shape.size + 1 := by
    rw [hsuperGeo.basePosition_eq]
    have hposition :=
      GenericSelect.position_le_length shape.bpCode false super.baseOccurrence
    have hlength : shape.bpCode.length <= 2 * shape.size + 1 := by
      simp [CartesianShape.bpCode_length]
    omega
  refine ⟨hinv, hbase, hbaseLe, ?_, hcontent⟩
  have hpos :
      packedReviewerRankQueryPos .selectLong shape.size
          (GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size)) <=
        GenericSelect.selectSuperSlot index
          (packedSelectSuperStride shape.size) :=
    Nat.min_le_left _ _
  have hmul :
      exceptionRank * packedSelectSuperStride shape.size <= index := by
    have hslotMul :
        GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size) *
          packedSelectSuperStride shape.size <= index := by
      unfold GenericSelect.selectSuperSlot
      exact Nat.div_mul_le_self _ _
    have hrankMul :
        exceptionRank * packedSelectSuperStride shape.size <=
          GenericSelect.selectSuperSlot index
              (packedSelectSuperStride shape.size) *
            packedSelectSuperStride shape.size :=
      Nat.mul_le_mul_right _ (Nat.le_trans hrank hpos)
    omega
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  have htwoMul := packedTwoMul_le_reviewerBound shape.size
  unfold GenericSelect.relativeSplitSelectLongCompactSlot
  simp only [PackedReviewerNatFits]
  omega

/-- One canonical reply preserves the long-rank arm of the select tower. -/
private theorem packedReviewerSelectConsume_longRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (rank : PackedReviewerRankState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hsuperGeo : PackedReviewerCanonicalSuperGeometry shape index super)
    (hlong : GenericSelect.relativeSplitSelectEntryIsMarked super = true)
    (hrankFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining rank) rank)
    (hrank :
      PackedReviewerRankCanonicalScalarFits shape
        (packedReviewerRankQueryPos .selectLong shape.size
          (GenericSelect.selectSuperSlot index
            (packedSelectSuperStride shape.size))) rank)
    (horbit :
      exists fuel,
        rank =
          packedReviewerRankCanonicalRun shape fuel
            (.superSample invocation .selectLong shape.size
              (GenericSelect.selectSuperSlot index
                (packedSelectSuperStride shape.size))))
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerRankNextRequest rank = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.longRank invocation shape.size index super rank)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hrank' := hrank.consume hrequest
  have hpos := packedReviewerRankNextRequest_remaining_pos hrequest
  have hdescent :=
    packedReviewerRankRemaining_consume_le rank
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining
          (packedReviewerRankConsumeReply rank
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index)))
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) := by
    obtain ⟨fuel, hfuel⟩ : exists fuel,
        packedReviewerRankRemaining rank = fuel + 1 :=
      ⟨packedReviewerRankRemaining rank - 1, by omega⟩
    rw [hfuel] at hrankFit
    have hstep := (PackedReviewerRequestsFitFrom.step shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply fuel rank
      request hrankFit hrequest).2
    exact PackedReviewerRequestsFitFrom.mono shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply hstep
      (by omega)
  have horbit' :
      exists fuel,
        packedReviewerRankConsumeReply rank
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index) =
          packedReviewerRankCanonicalRun shape fuel
            (.superSample invocation .selectLong shape.size
              (GenericSelect.selectSuperSlot index
                (packedSelectSuperStride shape.size))) := by
    obtain ⟨fuel, hfuel⟩ := horbit
    refine ⟨fuel + 1, ?_⟩
    have hrun :
        packedReviewerRankCanonicalRun shape (fuel + 1)
            (.superSample invocation .selectLong shape.size
              (GenericSelect.selectSuperSlot index
                (packedSelectSuperStride shape.size))) =
          packedReviewerRankCanonicalStep shape
            (packedReviewerRankCanonicalRun shape fuel
              (.superSample invocation .selectLong shape.size
                (GenericSelect.selectSuperSlot index
                  (packedSelectSuperStride shape.size)))) := rfl
    rw [hrun, ← hfuel]
    simp [packedReviewerRankCanonicalStep,
      packedReviewerComponentCanonicalStep, hrequest]
  simp only [packedReviewerSelectConsumeReply]
  cases hresult :
      packedReviewerRankResult
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hindex, hsuperGeo, hlong, hfit', hrank', horbit'⟩
  | some exceptionRank =>
      have hvalue := hrank'.result_fits hresult
      have her :=
        packedReviewerSelectLongRank_orbit_value_eq shape invocation index _
          horbit' hresult
      have hcontent :=
        packedReviewerLongRelative_read_content_le shape index super hindex
          hsuperGeo hlong
      rw [← her] at hcontent
      exact packedReviewerSelectAfterLongRank_fits shape invocation index
        super exceptionRank hinv hindex hsuperGeo hvalue.2 hcontent

/--
The completed sparse exception rank addresses a fitting compact slot.  The
clamped query position keeps the rank at or below the sparse flag slot, the
mixed-radix base-occurrence identity absorbs the slot-times-stride product
into the query index plus a superblock cross-term of at most `index / ws`,
and the sparse directory's literal 512-bit allowance covers every small size.
-/
private theorem packedReviewerSparseCompactSlot_fits
    (shape : CartesianShape) (index exceptionRank : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (hindex : index < shape.size)
    (hlocalGeo : PackedReviewerCanonicalLocalGeometry shape index super loc)
    (hrank :
      exceptionRank <=
        packedReviewerRankQueryPos .selectSparse shape.size
          (GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super)) :
    PackedReviewerNatFits shape.size
      (GenericSelect.relativeSplitSelectSparseCompactSlot exceptionRank
        (index -
          GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
        (packedSelectLocalStride shape.size)) := by
  have hvalid : index < GenericSelect.occurrenceCount shape.bpCode false := by
    rw [packedSelectOccurrenceCount_eq_size]; exact hindex
  have hfacts := GenericSelect.localSlot_facts shape.bpCode false index
    super (by
      simpa [packedSelectSuperStride, CartesianShape.bpCode_length] using
        hlocalGeo.super_geometry.get_eq)
    hvalid hlocalGeo.super_short
  have hbaseOccEq := hlocalGeo.baseOccurrence_eq
  simp only [packedSelectSuperStride, packedSelectLocalSlotsPerSuper,
    packedSelectLocalStride, packedReviewerRankQueryPos] at hrank hbaseOccEq ⊢
  simp only [CartesianShape.bpCode_length] at hfacts hbaseOccEq
  obtain ⟨hcount, heffective, hlive, hsuperEq, hbaseLe, hbaseLt⟩ := hfacts
  have her :
      exceptionRank <=
        GenericSelect.relativeSplitSelectLocalSlot index
          (GenericSelect.superStride (2 * shape.size))
          (GenericSelect.localSlotsPerSuper (2 * shape.size))
          (GenericSelect.localStride (2 * shape.size)) super :=
    Nat.le_trans hrank (Nat.min_le_left _ _)
  -- Local shorthand facts, all spelled at bit length `2 * shape.size`.
  have hdivLe :
      GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super /
          GenericSelect.localSlotsPerSuper (2 * shape.size) *
          GenericSelect.localSlotsPerSuper (2 * shape.size) <=
        GenericSelect.relativeSplitSelectLocalSlot index
          (GenericSelect.superStride (2 * shape.size))
          (GenericSelect.localSlotsPerSuper (2 * shape.size))
          (GenericSelect.localStride (2 * shape.size)) super :=
    Nat.div_mul_le_self _ _
  have hcross :=
    GenericSelect.selectLocalSlotsPerSuper_mul_localStride_le_add
      (GenericSelect.superStride (2 * shape.size))
      (GenericSelect.localStride (2 * shape.size))
  have hspsEq :
      GenericSelect.localSlotsPerSuper (2 * shape.size) =
        GenericSelect.selectLocalSlotsPerSuper
          (GenericSelect.superStride (2 * shape.size))
          (GenericSelect.localStride (2 * shape.size)) := by
    simp [GenericSelect.localSlotsPerSuper]
  have hexpand :
      GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super *
          GenericSelect.localStride (2 * shape.size) =
        GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            (GenericSelect.localSlotsPerSuper (2 * shape.size) *
              GenericSelect.localStride (2 * shape.size)) +
          (GenericSelect.relativeSplitSelectLocalSlot index
                (GenericSelect.superStride (2 * shape.size))
                (GenericSelect.localSlotsPerSuper (2 * shape.size))
                (GenericSelect.localStride (2 * shape.size)) super -
              GenericSelect.relativeSplitSelectLocalSlot index
                  (GenericSelect.superStride (2 * shape.size))
                  (GenericSelect.localSlotsPerSuper (2 * shape.size))
                  (GenericSelect.localStride (2 * shape.size)) super /
                GenericSelect.localSlotsPerSuper (2 * shape.size) *
                GenericSelect.localSlotsPerSuper (2 * shape.size)) *
            GenericSelect.localStride (2 * shape.size) := by
    have hsubmul :
        (GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super -
            GenericSelect.relativeSplitSelectLocalSlot index
                (GenericSelect.superStride (2 * shape.size))
                (GenericSelect.localSlotsPerSuper (2 * shape.size))
                (GenericSelect.localStride (2 * shape.size)) super /
              GenericSelect.localSlotsPerSuper (2 * shape.size) *
              GenericSelect.localSlotsPerSuper (2 * shape.size)) *
            GenericSelect.localStride (2 * shape.size) =
          GenericSelect.relativeSplitSelectLocalSlot index
                (GenericSelect.superStride (2 * shape.size))
                (GenericSelect.localSlotsPerSuper (2 * shape.size))
                (GenericSelect.localStride (2 * shape.size)) super *
              GenericSelect.localStride (2 * shape.size) -
            GenericSelect.relativeSplitSelectLocalSlot index
                  (GenericSelect.superStride (2 * shape.size))
                  (GenericSelect.localSlotsPerSuper (2 * shape.size))
                  (GenericSelect.localStride (2 * shape.size)) super /
                GenericSelect.localSlotsPerSuper (2 * shape.size) *
                GenericSelect.localSlotsPerSuper (2 * shape.size) *
              GenericSelect.localStride (2 * shape.size) :=
      Nat.sub_mul _ _ _
    have hassoc :
        GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.localStride (2 * shape.size) =
          GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            (GenericSelect.localSlotsPerSuper (2 * shape.size) *
              GenericSelect.localStride (2 * shape.size)) :=
      Nat.mul_assoc _ _ _
    have hxle :
        GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.localStride (2 * shape.size) <=
          GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super *
            GenericSelect.localStride (2 * shape.size) :=
      Nat.mul_le_mul_right _ hdivLe
    omega
  have hinSuperEq :
      GenericSelect.localSlotInSuperOfGlobal (2 * shape.size)
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super) =
        GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super -
          GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.localSlotsPerSuper (2 * shape.size) := by
    simp [GenericSelect.localSlotInSuperOfGlobal]
  have hcrossMono :
      GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super /
          GenericSelect.localSlotsPerSuper (2 * shape.size) *
          (GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.localStride (2 * shape.size)) <=
        GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
          (GenericSelect.superStride (2 * shape.size) +
            GenericSelect.localStride (2 * shape.size)) :=
    Nat.mul_le_mul_left _ (by rw [hspsEq]; exact hcross)
  have hsplit :
      GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super /
          GenericSelect.localSlotsPerSuper (2 * shape.size) *
          (GenericSelect.superStride (2 * shape.size) +
            GenericSelect.localStride (2 * shape.size)) =
        GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.superStride (2 * shape.size) +
          GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.localStride (2 * shape.size) :=
    Nat.mul_add _ _ _
  have hbo :
      GenericSelect.localBaseOccurrence (2 * shape.size)
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super) =
        GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.superStride (2 * shape.size) +
          (GenericSelect.relativeSplitSelectLocalSlot index
                (GenericSelect.superStride (2 * shape.size))
                (GenericSelect.localSlotsPerSuper (2 * shape.size))
                (GenericSelect.localStride (2 * shape.size)) super -
              GenericSelect.relativeSplitSelectLocalSlot index
                  (GenericSelect.superStride (2 * shape.size))
                  (GenericSelect.localSlotsPerSuper (2 * shape.size))
                  (GenericSelect.localStride (2 * shape.size)) super /
                GenericSelect.localSlotsPerSuper (2 * shape.size) *
                GenericSelect.localSlotsPerSuper (2 * shape.size)) *
            GenericSelect.localStride (2 * shape.size) := by
    rw [show GenericSelect.localBaseOccurrence (2 * shape.size)
          (GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super) =
        GenericSelect.relativeSplitSelectLocalSlot index
              (GenericSelect.superStride (2 * shape.size))
              (GenericSelect.localSlotsPerSuper (2 * shape.size))
              (GenericSelect.localStride (2 * shape.size)) super /
            GenericSelect.localSlotsPerSuper (2 * shape.size) *
            GenericSelect.superStride (2 * shape.size) +
          GenericSelect.localSlotInSuperOfGlobal (2 * shape.size)
              (GenericSelect.relativeSplitSelectLocalSlot index
                (GenericSelect.superStride (2 * shape.size))
                (GenericSelect.localSlotsPerSuper (2 * shape.size))
                (GenericSelect.localStride (2 * shape.size)) super) *
            GenericSelect.localStride (2 * shape.size) from rfl]
    rw [hinSuperEq]
  -- The superblock cross-term is at most `index / wordBits`.
  have hsuperSlotEq :
      GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super /
          GenericSelect.localSlotsPerSuper (2 * shape.size) =
        GenericSelect.selectSuperSlot index
          (GenericSelect.superStride (2 * shape.size)) := by
    simpa [GenericSelect.localSuperSlot] using hsuperEq
  have hlsLe :
      GenericSelect.localStride (2 * shape.size) <=
        GenericSelect.wordBits (2 * shape.size) := by
    have hdivLe' :
        GenericSelect.wordBits (2 * shape.size) /
            (GenericSelect.ell (2 * shape.size) *
              GenericSelect.ell (2 * shape.size)) <=
          GenericSelect.wordBits (2 * shape.size) := Nat.div_le_self _ _
    have hwsPos : 0 < GenericSelect.wordBits (2 * shape.size) :=
      SuccinctRank.machineWordBits_pos _
    simp only [GenericSelect.localStride]
    omega
  have hcrossLe :
      GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super /
          GenericSelect.localSlotsPerSuper (2 * shape.size) *
          GenericSelect.localStride (2 * shape.size) <=
        index / GenericSelect.wordBits (2 * shape.size) := by
    rw [hsuperSlotEq]
    have hslotDef :
        GenericSelect.selectSuperSlot index
            (GenericSelect.superStride (2 * shape.size)) =
          index /
            (GenericSelect.wordBits (2 * shape.size) *
              GenericSelect.wordBits (2 * shape.size)) := by
      simp [GenericSelect.selectSuperSlot, GenericSelect.superStride]
    have hdd :
        index /
            (GenericSelect.wordBits (2 * shape.size) *
              GenericSelect.wordBits (2 * shape.size)) =
          index / GenericSelect.wordBits (2 * shape.size) /
            GenericSelect.wordBits (2 * shape.size) := by
      rw [Nat.div_div_eq_div_mul]
    rw [hslotDef, hdd]
    have hmono :
        index / GenericSelect.wordBits (2 * shape.size) /
              GenericSelect.wordBits (2 * shape.size) *
            GenericSelect.localStride (2 * shape.size) <=
          index / GenericSelect.wordBits (2 * shape.size) /
              GenericSelect.wordBits (2 * shape.size) *
            GenericSelect.wordBits (2 * shape.size) :=
      Nat.mul_le_mul_left _ hlsLe
    have hlast :
        index / GenericSelect.wordBits (2 * shape.size) /
              GenericSelect.wordBits (2 * shape.size) *
            GenericSelect.wordBits (2 * shape.size) <=
          index / GenericSelect.wordBits (2 * shape.size) :=
      Nat.div_mul_le_self _ _
    omega
  -- Final envelope against the reviewer capacity.
  have hermul :
      exceptionRank * GenericSelect.localStride (2 * shape.size) <=
        GenericSelect.relativeSplitSelectLocalSlot index
            (GenericSelect.superStride (2 * shape.size))
            (GenericSelect.localSlotsPerSuper (2 * shape.size))
            (GenericSelect.localStride (2 * shape.size)) super *
          GenericSelect.localStride (2 * shape.size) :=
    Nat.mul_le_mul_right _ her
  have hir :
      index -
          GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc <=
        GenericSelect.localStride (2 * shape.size) := by
    rw [hbaseOccEq]
    omega
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  have hfiveTwelve := packedReviewerCellBound_ge_five_twelve shape.size
  have htwoMul := packedTwoMul_le_reviewerBound shape.size
  have hwsSlack := packedRankWordSize_two_le_aux shape.size
  have hauxSlack := packedRankAux_le_reviewerBound shape.size
  have hwsEq :
      packedRankWordSize shape.size =
        GenericSelect.wordBits (2 * shape.size) := rfl
  have hdivWsLe :
      index / GenericSelect.wordBits (2 * shape.size) <= index :=
    Nat.div_le_self _ _
  rw [hwsEq] at hwsSlack
  unfold GenericSelect.relativeSplitSelectSparseCompactSlot
  simp only [PackedReviewerNatFits]
  omega

/-- Entering the sparse-relative directory after the sparse rank completes. -/
private theorem packedReviewerSelectAfterSparseRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (exceptionRank : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hlocalGeo : PackedReviewerCanonicalLocalGeometry shape index super loc)
    (hrank :
      exceptionRank <=
        packedReviewerRankQueryPos .selectSparse shape.size
          (GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super))
    (hcontent :
      forall word,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16
            (GenericSelect.relativeSplitSelectSparseCompactSlot exceptionRank
              (index -
                GenericSelect.relativeSplitSelectLocalBaseOccurrence super
                  loc)
              (packedSelectLocalStride shape.size)) = some word ->
          GenericSelect.relativeSplitSelectLocalBasePosition
              (packedSelectWordSize shape.size) super loc +
            SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterSparseRank invocation shape.size index
        (GenericSelect.relativeSplitSelectLocalSlot index
          (packedSelectSuperStride shape.size)
          (packedSelectLocalSlotsPerSuper shape.size)
          (packedSelectLocalStride shape.size) super)
        super loc exceptionRank) := by
  unfold packedReviewerSelectAfterSparseRank
  have hbase := (hlocalGeo.base_fields_fit).2
  have hbaseLe :
      GenericSelect.relativeSplitSelectLocalBasePosition
          (packedSelectWordSize shape.size) super loc <=
        2 * shape.size + 1 := by
    rw [hlocalGeo.basePosition_eq]
    have hposition :=
      GenericSelect.position_le_length shape.bpCode false
        (GenericSelect.localBaseOccurrence shape.bpCode.length
          (GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super))
    have hlength : shape.bpCode.length <= 2 * shape.size + 1 := by
      simp [CartesianShape.bpCode_length]
    omega
  exact ⟨hinv, hbase, hbaseLe,
    packedReviewerSparseCompactSlot_fits shape index exceptionRank super loc
      hindex hlocalGeo hrank, hcontent⟩

/-- One canonical reply preserves the sparse-rank arm of the select tower. -/
private theorem packedReviewerSelectConsume_sparseRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (rank : PackedReviewerRankState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hlocalGeo : PackedReviewerCanonicalLocalGeometry shape index super loc)
    (hmarked : GenericSelect.relativeSplitSelectEntryIsMarked loc = true)
    (hrankFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining rank) rank)
    (hrank :
      PackedReviewerRankCanonicalScalarFits shape
        (packedReviewerRankQueryPos .selectSparse shape.size
          (GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super)) rank)
    (horbit :
      exists fuel,
        rank =
          packedReviewerRankCanonicalRun shape fuel
            (.superSample invocation .selectSparse shape.size
              (GenericSelect.relativeSplitSelectLocalSlot index
                (packedSelectSuperStride shape.size)
                (packedSelectLocalSlotsPerSuper shape.size)
                (packedSelectLocalStride shape.size) super)))
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerRankNextRequest rank = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.sparseRank invocation shape.size index
          (GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super)
          super loc rank)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hrank' := hrank.consume hrequest
  have hpos := packedReviewerRankNextRequest_remaining_pos hrequest
  have hdescent :=
    packedReviewerRankRemaining_consume_le rank
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining
          (packedReviewerRankConsumeReply rank
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index)))
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) := by
    obtain ⟨fuel, hfuel⟩ : exists fuel,
        packedReviewerRankRemaining rank = fuel + 1 :=
      ⟨packedReviewerRankRemaining rank - 1, by omega⟩
    rw [hfuel] at hrankFit
    have hstep := (PackedReviewerRequestsFitFrom.step shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply fuel rank
      request hrankFit hrequest).2
    exact PackedReviewerRequestsFitFrom.mono shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply hstep
      (by omega)
  have horbit' :
      exists fuel,
        packedReviewerRankConsumeReply rank
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index) =
          packedReviewerRankCanonicalRun shape fuel
            (.superSample invocation .selectSparse shape.size
              (GenericSelect.relativeSplitSelectLocalSlot index
                (packedSelectSuperStride shape.size)
                (packedSelectLocalSlotsPerSuper shape.size)
                (packedSelectLocalStride shape.size) super)) := by
    obtain ⟨fuel, hfuel⟩ := horbit
    refine ⟨fuel + 1, ?_⟩
    have hrun :
        packedReviewerRankCanonicalRun shape (fuel + 1)
            (.superSample invocation .selectSparse shape.size
              (GenericSelect.relativeSplitSelectLocalSlot index
                (packedSelectSuperStride shape.size)
                (packedSelectLocalSlotsPerSuper shape.size)
                (packedSelectLocalStride shape.size) super)) =
          packedReviewerRankCanonicalStep shape
            (packedReviewerRankCanonicalRun shape fuel
              (.superSample invocation .selectSparse shape.size
                (GenericSelect.relativeSplitSelectLocalSlot index
                  (packedSelectSuperStride shape.size)
                  (packedSelectLocalSlotsPerSuper shape.size)
                  (packedSelectLocalStride shape.size) super))) := rfl
    rw [hrun, ← hfuel]
    simp [packedReviewerRankCanonicalStep,
      packedReviewerComponentCanonicalStep, hrequest]
  simp only [packedReviewerSelectConsumeReply]
  cases hresult :
      packedReviewerRankResult
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hindex, hlocalGeo, rfl, hmarked, hfit', hrank',
        horbit'⟩
  | some exceptionRank =>
      have hvalue := hrank'.result_fits hresult
      have hcount :
          GenericSelect.sparseExceptionEffectiveLocalSlotCount
              shape.bpCode false =
            packedSparseSlots shape.size := by
        rw [← GenericSelect.sparseExceptionEffectiveFlagBits_length,
          sparseFlagBits_length_eq_packed]
      have hslotCount :
          GenericSelect.relativeSplitSelectLocalSlot index
              (packedSelectSuperStride shape.size)
              (packedSelectLocalSlotsPerSuper shape.size)
              (packedSelectLocalStride shape.size) super <
            packedSparseSlots shape.size := by
        have heff := hlocalGeo.facts.2.1
        rw [hcount] at heff
        exact heff
      have her :=
        packedReviewerSelectSparseRank_orbit_value_eq shape invocation
          (GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride shape.size)
            (packedSelectLocalSlotsPerSuper shape.size)
            (packedSelectLocalStride shape.size) super) _ hslotCount horbit'
          hresult
      have hcontent :=
        packedReviewerSparseRelative_read_content_le shape index super loc
          hindex hlocalGeo hmarked
      rw [← her] at hcontent
      exact packedReviewerSelectAfterSparseRank_fits shape invocation index
        super loc exceptionRank hinv hindex hlocalGeo hvalue.2 hcontent

/-- The reassembled relative-directory reply is a fitting close position. -/
private theorem packedReviewerRelativeDone_fits
    (shape : CartesianShape) (base : Nat) (reply : Option (List Bool))
    (hbound :
      forall word, reply = some word ->
        base + SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1) :
    PackedReviewerSelectCanonicalScalarFits shape
      (.done
        ((packedReviewerDecodeNat reply).map fun offset => base + offset)) := by
  intro close hclose
  cases reply with
  | none => simp [packedReviewerDecodeNat] at hclose
  | some word =>
      simp only [packedReviewerDecodeNat, Option.map_some,
        Option.some.injEq] at hclose
      subst close
      have hbase := hbound word rfl
      exact
        ⟨packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hbase,
          by omega⟩

/-- One canonical reply resolves the long relative directory to done. -/
private theorem packedReviewerSelectConsume_longRelative_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (base slot : Nat)
    (hcontent :
      forall word,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 12
            slot = some word ->
          base + SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1)
    {request : PackedReviewerLogicalRequest}
    (hrequest :
      packedReviewerSelectNextRequest (.longRelative invocation base slot) =
        some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply (.longRelative invocation base slot)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  simp only [packedReviewerSelectNextRequest, Option.some.injEq] at hrequest
  subst request
  simp only [packedReviewerSelectConsumeReply]
  exact packedReviewerRelativeDone_fits shape base _
    (fun word hword => hcontent word hword)

/-- One canonical reply resolves the sparse relative directory to done. -/
private theorem packedReviewerSelectConsume_sparseRelative_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (base slot : Nat)
    (hcontent :
      forall word,
        (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 16
            slot = some word ->
          base + SuccinctSpace.bitsToNatLE word <= 2 * shape.size + 1)
    {request : PackedReviewerLogicalRequest}
    (hrequest :
      packedReviewerSelectNextRequest (.sparseRelative invocation base slot) =
        some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply (.sparseRelative invocation base slot)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  simp only [packedReviewerSelectNextRequest, Option.some.injEq] at hrequest
  subst request
  simp only [packedReviewerSelectConsumeReply]
  exact packedReviewerRelativeDone_fits shape base _
    (fun word hword => hcontent word hword)

/-! ## Dense-phase width helpers -/

private theorem packedReviewerBpCodeWordWidth_le_two_mul_add_one (n : Nat) :
    packedBpCodeWordWidth n <= 2 * n + 1 := by
  unfold packedBpCodeWordWidth SuccinctRank.machineWordBits
  by_cases hzero : 2 * n = 0
  · simp [hzero, Nat.log2]
  · have hpow : 2 ^ Nat.log2 (2 * n) <= 2 * n := Nat.log2_self_le hzero
    have hlt : Nat.log2 (2 * n) < 2 ^ Nat.log2 (2 * n) :=
      Nat.lt_two_pow_self
    omega

private theorem packedReviewerBPWordRead_length_le
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 index =
        some word) :
    word.length <= packedBpCodeWordWidth shape.size := by
  rw [packedReviewerGlobalReadStore_legacy shape (by omega)
    (source := ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode) rfl,
    packedBpCodeWords] at hread
  unfold packedWordSlice at hread
  by_cases hi :
      index <
        packedChunkCount (2 * shape.size) (packedBpCodeWordWidth shape.size)
  · simp only [hi, if_true, Option.some.injEq] at hread
    rw [← hread]
    exact List.length_take_le _ _
  · simp [hi] at hread

/-- A segment-zero read never reaches past the parenthesis string: the word
index times the word size plus the returned length stays within `2n`. -/
private theorem packedReviewerBPWordRead_index_length_le
    (shape : CartesianShape) {index : Nat} {word : List Bool}
    (hread :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 index =
        some word) :
    index * packedSelectWordSize shape.size + word.length <=
      2 * shape.size := by
  rw [packedReviewerGlobalReadStore_legacy shape (by omega)
    (source := ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode) rfl,
    packedBpCodeWords] at hread
  unfold packedWordSlice at hread
  by_cases hi :
      index <
        packedChunkCount (2 * shape.size) (packedBpCodeWordWidth shape.size)
  · simp only [hi, if_true, Option.some.injEq] at hread
    have hlenPayload :
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
            ConcreteBPNativeSuccinctRMQFlatPayloadSource.bpCode).length =
          2 * shape.size := by
      show shape.bpCode.length = 2 * shape.size
      exact CartesianShape.bpCode_length shape
    have hle :
        index <= 2 * shape.size / packedBpCodeWordWidth shape.size := by
      by_cases hmod :
          2 * shape.size % packedBpCodeWordWidth shape.size = 0
      · simp only [packedChunkCount, hmod, if_true] at hi
        omega
      · simp only [packedChunkCount, hmod, if_false] at hi
        omega
    have hmul :
        index * packedBpCodeWordWidth shape.size <=
          2 * shape.size / packedBpCodeWordWidth shape.size *
            packedBpCodeWordWidth shape.size :=
      Nat.mul_le_mul_right _ hle
    have hdivMul :
        2 * shape.size / packedBpCodeWordWidth shape.size *
          packedBpCodeWordWidth shape.size <= 2 * shape.size :=
      Nat.div_mul_le_self _ _
    have hword :
        word.length =
          min (packedBpCodeWordWidth shape.size)
            (2 * shape.size - index * packedBpCodeWordWidth shape.size) := by
      rw [← hread]
      rw [List.length_take, List.length_drop, hlenPayload]
    have hws :
        packedSelectWordSize shape.size = packedBpCodeWordWidth shape.size :=
      rfl
    rw [hws, hword]
    omega
  · simp [hi] at hread

private theorem packedReviewerStartFoldBudget_fits
    (shape : CartesianShape) (word : List Bool) (limit : Nat)
    (hword : word.length <= packedBpCodeWordWidth shape.size) :
    PackedReviewerNatFits shape.size
      (0 +
        SuccinctClose.bpWordChunkCount (packedFringeChunkBits shape.size)
            (SuccinctClose.bpWordRankEffLimit word limit) *
          packedFringeChunkBits shape.size) := by
  have hcount :
      SuccinctClose.bpWordChunkCount (packedFringeChunkBits shape.size)
          (SuccinctClose.bpWordRankEffLimit word limit) <=
        (SuccinctClose.bpWordRankEffLimit word limit - 1) /
            packedFringeChunkBits shape.size + 1 := by
    unfold SuccinctClose.bpWordChunkCount
    exact Nat.min_le_left _ _
  have hdivMul :
      (SuccinctClose.bpWordRankEffLimit word limit - 1) /
            packedFringeChunkBits shape.size *
          packedFringeChunkBits shape.size <=
        SuccinctClose.bpWordRankEffLimit word limit - 1 :=
    Nat.div_mul_le_self _ _
  have hmul :
      SuccinctClose.bpWordChunkCount (packedFringeChunkBits shape.size)
            (SuccinctClose.bpWordRankEffLimit word limit) *
          packedFringeChunkBits shape.size <=
        ((SuccinctClose.bpWordRankEffLimit word limit - 1) /
              packedFringeChunkBits shape.size + 1) *
          packedFringeChunkBits shape.size :=
    Nat.mul_le_mul_right _ hcount
  have hadd :
      ((SuccinctClose.bpWordRankEffLimit word limit - 1) /
            packedFringeChunkBits shape.size + 1) *
          packedFringeChunkBits shape.size =
        (SuccinctClose.bpWordRankEffLimit word limit - 1) /
              packedFringeChunkBits shape.size *
            packedFringeChunkBits shape.size +
          packedFringeChunkBits shape.size := by
    rw [Nat.add_mul, Nat.one_mul]
  have heff : SuccinctClose.bpWordRankEffLimit word limit <= word.length :=
    Nat.min_le_right _ _
  have hchunk :
      packedFringeChunkBits shape.size <=
        packedRankWordSize shape.size := by
    unfold packedFringeChunkBits SuccinctClose.bpFringeChunkBits
    have hdiv : Nat.log2 (2 * shape.size) / 8 <= Nat.log2 (2 * shape.size) :=
      Nat.div_le_self _ _
    have hws : packedRankWordSize shape.size =
        Nat.log2 (2 * shape.size) + 1 := rfl
    omega
  have hbp :
      packedBpCodeWordWidth shape.size = packedRankWordSize shape.size := rfl
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  have htwoMul := packedTwoMul_le_reviewerBound shape.size
  have hwsSlack := packedRankWordSize_two_le_aux shape.size
  have hauxSlack := packedRankAux_le_reviewerBound shape.size
  simp only [PackedReviewerNatFits]
  omega

/-! ## Dense-phase transitions -/

/-- Landing after the second dense rank: an in-word select or the far word. -/
private theorem packedReviewerSelectAfterDenseUptoRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence beforeFirst : Nat) (word : List Bool)
    (uptoFirst : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    (hword : PackedReviewerWordFits shape.size word)
    (hwordLen : word.length <= packedBpCodeWordWidth shape.size)
    (hbefore : beforeFirst <= word.length)
    (hupto : uptoFirst <= word.length)
    (hword2n :
      basePosition / packedSelectWordSize shape.size *
          packedSelectWordSize shape.size + word.length <=
        2 * shape.size) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterDenseUptoRank invocation shape.size index
        basePosition baseOccurrence beforeFirst word uptoFirst) := by
  have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
  have htwoMul := packedTwoMul_le_reviewerBound shape.size
  have hwsSlack := packedRankWordSize_two_le_aux shape.size
  have hauxSlack := packedRankAux_le_reviewerBound shape.size
  have hbp :
      packedBpCodeWordWidth shape.size = packedRankWordSize shape.size := rfl
  have hbpLinear := packedReviewerBpCodeWordWidth_le_two_mul_add_one shape.size
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  have hbaseWordMul :
      basePosition / packedSelectWordSize shape.size *
          packedSelectWordSize shape.size <=
        basePosition := Nat.div_mul_le_self _ _
  simp only [packedReviewerSelectAfterDenseUptoRank]
  by_cases hwithin :
      index - baseOccurrence < uptoFirst - beforeFirst
  · simp only [hwithin, if_true]
    have hoccFits :
        PackedReviewerNatFits shape.size
          (beforeFirst + (index - baseOccurrence)) := by
      simp only [PackedReviewerNatFits]
      omega
    have hselect :=
      packedReviewerWordSelectStart_canonicalScalarFits shape invocation
        false word (beforeFirst + (index - baseOccurrence)) rfl hinv hword
        hoccFits
    let select :=
      packedReviewerWordSelectStart invocation shape.size false word
        (beforeFirst + (index - baseOccurrence))
    cases hresult : packedReviewerWordSelectResult select with
    | none =>
        have hbaseBound :
            basePosition / packedSelectWordSize shape.size *
                packedSelectWordSize shape.size <=
              2 * shape.size + 1 + packedSelectWordSize shape.size := by
          omega
        have hwitness :=
          packedReviewerWordSelectStart_requests_fit shape invocation false
            word (beforeFirst + (index - baseOccurrence)) hinv
        have hnine :=
          packedReviewerWordSelectStart_remaining_le_nine invocation
            shape.size false word (beforeFirst + (index - baseOccurrence))
        simpa [PackedReviewerSelectCanonicalScalarFits, select, hresult] using
          (⟨rfl, hinv, hbaseBound, hwitness,
            ⟨word, hword, hwordLen, hword2n, hselect⟩, hnine⟩ :
            PackedReviewerSelectCanonicalScalarFits shape
              (.denseFirstSelect invocation shape.size
                (basePosition / packedSelectWordSize shape.size)
                (packedReviewerWordSelectStart invocation shape.size false
                  word (beforeFirst + (index - baseOccurrence)))))
    | some localResult =>
        cases localResult with
        | none =>
            have hdone :
                PackedReviewerSelectCanonicalScalarFits shape
                  (.done none) := by
              intro close hclose
              simp at hclose
            simpa [select, hresult] using hdone
        | some offset =>
            have hvalue :=
              hselect.result_fits (by simpa [select] using hresult)
            have hdone :
                PackedReviewerSelectCanonicalScalarFits shape
                  (.done
                    (some
                      (basePosition / packedSelectWordSize shape.size *
                        packedSelectWordSize shape.size + offset))) := by
              intro close hclose
              simp only [Option.some.injEq] at hclose
              subst close
              constructor
              · simp only [PackedReviewerNatFits]
                omega
              · omega
            simpa [select, hresult] using hdone
  · simp only [hwithin, if_false]
    exact ⟨rfl, hinv, hindex, hbase, hocc, by omega, by omega⟩

/-- Landing after the first dense rank: the second fold or its continuation. -/
private theorem packedReviewerSelectAfterDenseBeforeRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence : Nat) (word : List Bool)
    (beforeFirst : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    (hword : PackedReviewerWordFits shape.size word)
    (hwordLen : word.length <= packedBpCodeWordWidth shape.size)
    (hbefore : beforeFirst <= word.length)
    (hword2n :
      basePosition / packedSelectWordSize shape.size *
          packedSelectWordSize shape.size + word.length <=
        2 * shape.size) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterDenseBeforeRank invocation shape.size index
        basePosition baseOccurrence word beforeFirst) := by
  have hfold :=
    packedReviewerRankStartFold_canonicalScalarFits shape word.length
      invocation .close word word.length 0 hinv hword
      (by
        have heff := Nat.min_le_right word.length word.length
        simpa [SuccinctClose.bpWordRankEffLimit] using heff)
      (packedReviewerStartFoldBudget_fits shape word word.length hwordLen)
  simp only [packedReviewerSelectAfterDenseBeforeRank]
  let rank :=
    packedReviewerRankStartFold invocation .close shape.size word
      word.length 0
  cases hresult : packedReviewerRankResult rank with
  | none =>
      have hwitness :=
        packedReviewerRankStartFold_requests_fit shape invocation .close
          word word.length 0 hinv
      have hbound :=
        packedReviewerRankStartFold_remaining_le_eight invocation .close
          shape.size word word.length 0
      have hfit := PackedReviewerRequestsFitFrom.mono shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        hwitness hbound
      simpa [PackedReviewerSelectCanonicalScalarFits, rank, hresult] using
        (⟨rfl, hinv, hindex, hbase, hocc, hbefore, hword, hwordLen, hword2n,
          hfit, hfold, hbound⟩ :
          PackedReviewerSelectCanonicalScalarFits shape
            (.denseUptoRank invocation shape.size index basePosition
              baseOccurrence beforeFirst word
              (packedReviewerRankStartFold invocation .close shape.size word
                word.length 0)))
  | some uptoFirst =>
      have hvalue := hfold.result_fits (by simpa [rank] using hresult)
      simpa [rank, hresult] using
        packedReviewerSelectAfterDenseUptoRank_fits shape invocation index
          basePosition baseOccurrence beforeFirst word uptoFirst hinv hindex
          hbase hocc hword hwordLen hbefore hvalue.2 hword2n

/-- Landing after the first dense BP word arrives from segment zero. -/
private theorem packedReviewerSelectAfterDenseFirstWord_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence : Nat)
    (word? : Option (List Bool))
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    (hword? :
      forall word, word? = some word ->
        PackedReviewerWordFits shape.size word ∧
          word.length <= packedBpCodeWordWidth shape.size ∧
          basePosition / packedSelectWordSize shape.size *
              packedSelectWordSize shape.size + word.length <=
            2 * shape.size) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterDenseFirstWord invocation shape.size index
        basePosition baseOccurrence word?) := by
  cases word? with
  | none =>
      intro close hclose
      simp [packedReviewerSelectAfterDenseFirstWord] at hclose
  | some word =>
      obtain ⟨hword, hwordLen, hword2n⟩ := hword? word rfl
      have hfold :=
        packedReviewerRankStartFold_canonicalScalarFits shape word.length
          invocation .close word
          (basePosition -
            basePosition / packedSelectWordSize shape.size *
              packedSelectWordSize shape.size) 0 hinv hword
          (by
            have heff := Nat.min_le_right
              (basePosition -
                basePosition / packedSelectWordSize shape.size *
                  packedSelectWordSize shape.size) word.length
            simpa [SuccinctClose.bpWordRankEffLimit] using heff)
          (packedReviewerStartFoldBudget_fits shape word _ hwordLen)
      simp only [packedReviewerSelectAfterDenseFirstWord]
      let rank :=
        packedReviewerRankStartFold invocation .close shape.size word
          (basePosition -
            basePosition / packedSelectWordSize shape.size *
              packedSelectWordSize shape.size) 0
      cases hresult : packedReviewerRankResult rank with
      | none =>
          have hwitness :=
            packedReviewerRankStartFold_requests_fit shape invocation .close
              word
              (basePosition -
                basePosition / packedSelectWordSize shape.size *
                  packedSelectWordSize shape.size) 0 hinv
          have hbound :=
            packedReviewerRankStartFold_remaining_le_eight invocation .close
              shape.size word
              (basePosition -
                basePosition / packedSelectWordSize shape.size *
                  packedSelectWordSize shape.size) 0
          have hfit := PackedReviewerRequestsFitFrom.mono shape.size
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            packedReviewerRankNextRequest packedReviewerRankConsumeReply
            hwitness hbound
          simpa [PackedReviewerSelectCanonicalScalarFits, rank, hresult] using
            (⟨rfl, hinv, hindex, hbase, hocc, hword, hwordLen, hword2n, hfit,
              hfold, hbound⟩ :
              PackedReviewerSelectCanonicalScalarFits shape
                (.denseBeforeRank invocation shape.size index basePosition
                  baseOccurrence word
                  (packedReviewerRankStartFold invocation .close shape.size
                    word
                    (basePosition -
                      basePosition / packedSelectWordSize shape.size *
                        packedSelectWordSize shape.size) 0)))
      | some beforeFirst =>
          have hvalue := hfold.result_fits (by simpa [rank] using hresult)
          simpa [rank, hresult] using
            packedReviewerSelectAfterDenseBeforeRank_fits shape invocation
              index basePosition baseOccurrence word beforeFirst hinv hindex
              hbase hocc hword hwordLen hvalue.2 hword2n

/-- Landing after the second dense BP word arrives from segment zero. -/
private theorem packedReviewerSelectAfterDenseSecondWord_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence beforeFirst uptoFirst : Nat)
    (word? : Option (List Bool))
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    (hword? :
      forall word, word? = some word ->
        PackedReviewerWordFits shape.size word ∧
          word.length <= packedBpCodeWordWidth shape.size ∧
          (basePosition / packedSelectWordSize shape.size + 1) *
              packedSelectWordSize shape.size + word.length <=
            2 * shape.size) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectAfterDenseSecondWord invocation shape.size index
        basePosition baseOccurrence beforeFirst uptoFirst word?) := by
  cases word? with
  | none =>
      intro close hclose
      simp [packedReviewerSelectAfterDenseSecondWord] at hclose
  | some word =>
      obtain ⟨hword, hwordLen, hword2n⟩ := hword? word rfl
      have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
      have htwoMul := packedTwoMul_le_reviewerBound shape.size
      have hwsSlack := packedRankWordSize_two_le_aux shape.size
      have hauxSlack := packedRankAux_le_reviewerBound shape.size
      have hbp :
          packedBpCodeWordWidth shape.size = packedRankWordSize shape.size :=
        rfl
      have hbpLinear :=
        packedReviewerBpCodeWordWidth_le_two_mul_add_one shape.size
      have hws :
          packedSelectWordSize shape.size = packedRankWordSize shape.size :=
        rfl
      have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
      have hbaseWordMul :
          basePosition / packedSelectWordSize shape.size *
              packedSelectWordSize shape.size <=
            basePosition := Nat.div_mul_le_self _ _
      have hoccFits :
          PackedReviewerNatFits shape.size
            (index - baseOccurrence - (uptoFirst - beforeFirst)) := by
        simp only [PackedReviewerNatFits]
        omega
      have hselect :=
        packedReviewerWordSelectStart_canonicalScalarFits shape invocation
          false word (index - baseOccurrence - (uptoFirst - beforeFirst)) rfl
          hinv hword hoccFits
      simp only [packedReviewerSelectAfterDenseSecondWord]
      let select :=
        packedReviewerWordSelectStart invocation shape.size false word
          (index - baseOccurrence - (uptoFirst - beforeFirst))
      cases hresult : packedReviewerWordSelectResult select with
      | none =>
          have hbaseBound :
              (basePosition / packedSelectWordSize shape.size + 1) *
                  packedSelectWordSize shape.size <=
                2 * shape.size + 1 + packedSelectWordSize shape.size := by
            rw [Nat.add_mul]
            omega
          have hwitness :=
            packedReviewerWordSelectStart_requests_fit shape invocation
              false word (index - baseOccurrence - (uptoFirst - beforeFirst))
              hinv
          have hnine :=
            packedReviewerWordSelectStart_remaining_le_nine invocation
              shape.size false word
              (index - baseOccurrence - (uptoFirst - beforeFirst))
          simpa [PackedReviewerSelectCanonicalScalarFits, select, hresult] using
            (⟨rfl, hinv, hbaseBound, hwitness,
              ⟨word, hword, hwordLen, hword2n, hselect⟩, hnine⟩ :
              PackedReviewerSelectCanonicalScalarFits shape
                (.denseSecondSelect invocation shape.size
                  (basePosition / packedSelectWordSize shape.size + 1)
                  (packedReviewerWordSelectStart invocation shape.size false
                    word
                    (index - baseOccurrence - (uptoFirst - beforeFirst)))))
      | some localResult =>
          cases localResult with
          | none =>
              have hdone :
                  PackedReviewerSelectCanonicalScalarFits shape
                    (.done none) := by
                intro close hclose
                simp at hclose
              simpa [select, hresult] using hdone
          | some offset =>
              have hvalue :=
                hselect.result_fits (by simpa [select] using hresult)
              have hdone :
                  PackedReviewerSelectCanonicalScalarFits shape
                    (.done
                      (some
                        ((basePosition / packedSelectWordSize shape.size +
                            1) *
                          packedSelectWordSize shape.size + offset))) := by
                intro close hclose
                simp only [Option.some.injEq] at hclose
                subst close
                constructor
                · simp only [PackedReviewerNatFits]
                  omega
                · omega
              simpa [select, hresult] using hdone

/-! ## Dense-phase consume arms -/

/-- One canonical reply preserves the first dense word arm. -/
private theorem packedReviewerSelectConsume_denseFirstWord_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    {request : PackedReviewerLogicalRequest}
    (hrequest :
      packedReviewerSelectNextRequest
          (.denseFirstWord invocation shape.size index basePosition
            baseOccurrence) = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.denseFirstWord invocation shape.size index basePosition
          baseOccurrence)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  simp only [packedReviewerSelectNextRequest, Option.some.injEq] at hrequest
  subst request
  simp only [packedReviewerSelectConsumeReply]
  apply packedReviewerSelectAfterDenseFirstWord_fits shape invocation index
    basePosition baseOccurrence _ hinv hindex hbase hocc
  intro word hread
  refine ⟨?_, packedReviewerBPWordRead_length_le shape hread,
    packedReviewerBPWordRead_index_length_le shape hread⟩
  exact packedReviewerGlobalReadStore_word_fits shape
    { invocation := invocation
      site := .denseBPWord (basePosition / packedSelectWordSize shape.size)
      segment := 0
      index := basePosition / packedSelectWordSize shape.size } word hread

/-- One canonical reply preserves the second dense word arm. -/
private theorem packedReviewerSelectConsume_denseSecondWord_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence beforeFirst uptoFirst : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    {request : PackedReviewerLogicalRequest}
    (hrequest :
      packedReviewerSelectNextRequest
          (.denseSecondWord invocation shape.size index basePosition
            baseOccurrence beforeFirst uptoFirst) = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.denseSecondWord invocation shape.size index basePosition
          baseOccurrence beforeFirst uptoFirst)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  simp only [packedReviewerSelectNextRequest, Option.some.injEq] at hrequest
  subst request
  simp only [packedReviewerSelectConsumeReply]
  apply packedReviewerSelectAfterDenseSecondWord_fits shape invocation index
    basePosition baseOccurrence beforeFirst uptoFirst _ hinv hindex hbase hocc
  intro word hread
  refine ⟨?_, packedReviewerBPWordRead_length_le shape hread,
    packedReviewerBPWordRead_index_length_le shape hread⟩
  exact packedReviewerGlobalReadStore_word_fits shape
    { invocation := invocation
      site :=
        .denseBPWord (basePosition / packedSelectWordSize shape.size + 1)
      segment := 0
      index := basePosition / packedSelectWordSize shape.size + 1 } word hread

/-- One canonical reply preserves the first dense fold arm. -/
private theorem packedReviewerSelectConsume_denseBeforeRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence : Nat) (word : List Bool)
    (rank : PackedReviewerRankState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    (hword : PackedReviewerWordFits shape.size word)
    (hwordLen : word.length <= packedBpCodeWordWidth shape.size)
    (hword2n :
      basePosition / packedSelectWordSize shape.size *
          packedSelectWordSize shape.size + word.length <=
        2 * shape.size)
    (hbudget : packedReviewerRankRemaining rank <= 8)
    (hrankFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining rank) rank)
    (hrank : PackedReviewerRankCanonicalScalarFits shape word.length rank)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerRankNextRequest rank = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.denseBeforeRank invocation shape.size index basePosition
          baseOccurrence word rank)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hrank' := hrank.consume hrequest
  have hpos := packedReviewerRankNextRequest_remaining_pos hrequest
  have hdescent :=
    packedReviewerRankRemaining_consume_le rank
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining
          (packedReviewerRankConsumeReply rank
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index)))
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) := by
    obtain ⟨fuel, hfuel⟩ : exists fuel,
        packedReviewerRankRemaining rank = fuel + 1 :=
      ⟨packedReviewerRankRemaining rank - 1, by omega⟩
    rw [hfuel] at hrankFit
    have hstep := (PackedReviewerRequestsFitFrom.step shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply fuel rank
      request hrankFit hrequest).2
    exact PackedReviewerRequestsFitFrom.mono shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply hstep
      (by omega)
  have hbudget' : packedReviewerRankRemaining
      (packedReviewerRankConsumeReply rank
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) <= 8 := by
    omega
  simp only [packedReviewerSelectConsumeReply]
  cases hresult :
      packedReviewerRankResult
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hindex, hbase, hocc, hword, hwordLen, hword2n, hfit',
        hrank', hbudget'⟩
  | some beforeFirst =>
      have hvalue := hrank'.result_fits hresult
      exact packedReviewerSelectAfterDenseBeforeRank_fits shape invocation
        index basePosition baseOccurrence word beforeFirst hinv hindex hbase
        hocc hword hwordLen hvalue.2 hword2n

/-- One canonical reply preserves the second dense fold arm. -/
private theorem packedReviewerSelectConsume_denseUptoRank_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (index basePosition baseOccurrence beforeFirst : Nat) (word : List Bool)
    (rank : PackedReviewerRankState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hindex : index < shape.size)
    (hbase : basePosition <= 2 * shape.size + 1)
    (hocc : baseOccurrence <= index)
    (hbefore : beforeFirst <= word.length)
    (hword : PackedReviewerWordFits shape.size word)
    (hwordLen : word.length <= packedBpCodeWordWidth shape.size)
    (hword2n :
      basePosition / packedSelectWordSize shape.size *
          packedSelectWordSize shape.size + word.length <=
        2 * shape.size)
    (hbudget : packedReviewerRankRemaining rank <= 8)
    (hrankFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining rank) rank)
    (hrank : PackedReviewerRankCanonicalScalarFits shape word.length rank)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerRankNextRequest rank = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.denseUptoRank invocation shape.size index basePosition
          baseOccurrence beforeFirst word rank)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hrank' := hrank.consume hrequest
  have hpos := packedReviewerRankNextRequest_remaining_pos hrequest
  have hdescent :=
    packedReviewerRankRemaining_consume_le rank
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining
          (packedReviewerRankConsumeReply rank
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index)))
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) := by
    obtain ⟨fuel, hfuel⟩ : exists fuel,
        packedReviewerRankRemaining rank = fuel + 1 :=
      ⟨packedReviewerRankRemaining rank - 1, by omega⟩
    rw [hfuel] at hrankFit
    have hstep := (PackedReviewerRequestsFitFrom.step shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply fuel rank
      request hrankFit hrequest).2
    exact PackedReviewerRequestsFitFrom.mono shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerRankNextRequest packedReviewerRankConsumeReply hstep
      (by omega)
  have hbudget' : packedReviewerRankRemaining
      (packedReviewerRankConsumeReply rank
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) <= 8 := by
    omega
  simp only [packedReviewerSelectConsumeReply]
  cases hresult :
      packedReviewerRankResult
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hindex, hbase, hocc, hbefore, hword, hwordLen,
        hword2n, hfit', hrank', hbudget'⟩
  | some uptoFirst =>
      have hvalue := hrank'.result_fits hresult
      exact packedReviewerSelectAfterDenseUptoRank_fits shape invocation index
        basePosition baseOccurrence beforeFirst word uptoFirst hinv hindex
        hbase hocc hword hwordLen hbefore hvalue.2 hword2n

/-- One canonical reply preserves an in-word select arm. -/
private theorem packedReviewerSelectConsume_denseSelect_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (baseWord : Nat) (select : PackedReviewerWordSelectState)
    (word : List Bool)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hbaseBound :
      baseWord * packedSelectWordSize shape.size <=
        2 * shape.size + 1 + packedSelectWordSize shape.size)
    (hword : PackedReviewerWordFits shape.size word)
    (hwordLen : word.length <= packedBpCodeWordWidth shape.size)
    (hword2n :
      baseWord * packedSelectWordSize shape.size + word.length <=
        2 * shape.size)
    (hselect :
      PackedReviewerWordSelectCanonicalScalarFits shape word.length select)
    (hselectFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerWordSelectNextRequest
        packedReviewerWordSelectConsumeReply
        (packedReviewerWordSelectRemaining select) select)
    (hnine : packedReviewerWordSelectRemaining select <= 9)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerWordSelectNextRequest select = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.denseFirstSelect invocation shape.size baseWord select)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) ∧
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply
        (.denseSecondSelect invocation shape.size baseWord select)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hselect' := hselect.consume hrequest
  have hpos := packedReviewerWordSelectNextRequest_remaining_pos hrequest
  have hdescent :=
    packedReviewerWordSelectRemaining_consume_le select
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerWordSelectNextRequest
        packedReviewerWordSelectConsumeReply
        (packedReviewerWordSelectRemaining
          (packedReviewerWordSelectConsumeReply select
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index)))
        (packedReviewerWordSelectConsumeReply select
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) := by
    obtain ⟨fuel, hfuel⟩ : exists fuel,
        packedReviewerWordSelectRemaining select = fuel + 1 :=
      ⟨packedReviewerWordSelectRemaining select - 1, by omega⟩
    rw [hfuel] at hselectFit
    have hstep := (PackedReviewerRequestsFitFrom.step shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply fuel select request hselectFit
      hrequest).2
    exact PackedReviewerRequestsFitFrom.mono shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerWordSelectNextRequest
      packedReviewerWordSelectConsumeReply hstep (by omega)
  have hnine' : packedReviewerWordSelectRemaining
      (packedReviewerWordSelectConsumeReply select
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) <= 9 := by
    omega
  have hdone :
      forall localResult,
        packedReviewerWordSelectResult
            (packedReviewerWordSelectConsumeReply select
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) = some localResult ->
          PackedReviewerSelectCanonicalScalarFits shape
            (.done
              (localResult.map
                (fun offset =>
                  baseWord * packedSelectWordSize shape.size + offset))) := by
    intro localResult hresult
    cases localResult with
    | none =>
        intro close hclose
        simp at hclose
    | some offset =>
        have hvalue := hselect'.result_fits hresult
        intro close hclose
        simp only [Option.map_some, Option.some.injEq] at hclose
        subst close
        have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
        have htwoMul := packedTwoMul_le_reviewerBound shape.size
        have hwsSlack := packedRankWordSize_two_le_aux shape.size
        have hauxSlack := packedRankAux_le_reviewerBound shape.size
        have hbp :
            packedBpCodeWordWidth shape.size =
              packedRankWordSize shape.size := rfl
        have hws :
            packedSelectWordSize shape.size =
              packedRankWordSize shape.size := rfl
        have hbpLinear :=
          packedReviewerBpCodeWordWidth_le_two_mul_add_one shape.size
        constructor
        · simp only [PackedReviewerNatFits]
          omega
        · omega
  constructor
  · simp only [packedReviewerSelectConsumeReply]
    cases hresult :
        packedReviewerWordSelectResult
          (packedReviewerWordSelectConsumeReply select
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index)) with
    | none =>
        exact ⟨rfl, hinv, hbaseBound, hfit',
          ⟨word, hword, hwordLen, hword2n, hselect'⟩, hnine'⟩
    | some localResult => exact hdone localResult hresult
  · simp only [packedReviewerSelectConsumeReply]
    cases hresult :
        packedReviewerWordSelectResult
          (packedReviewerWordSelectConsumeReply select
            ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
              request.segment request.index)) with
    | none =>
        exact ⟨rfl, hinv, hbaseBound, hfit',
          ⟨word, hword, hwordLen, hword2n, hselect'⟩, hnine'⟩
    | some localResult => exact hdone localResult hresult

/-- One canonical reply preserves the whole select tower invariant. -/
private theorem PackedReviewerSelectCanonicalScalarFits.consume
    {shape : CartesianShape} {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectCanonicalScalarFits shape state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerSelectNextRequest state = some request) :
    PackedReviewerSelectCanonicalScalarFits shape
      (packedReviewerSelectConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases state with
  | superEntry invocation n index entry =>
      obtain ⟨rfl, hinv, hindex, hentry⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerSelectConsume_superEntry_fits shape invocation index
        entry hinv hindex hentry hrequest
  | localEntry invocation n index localSlot super entry =>
      obtain ⟨rfl, hinv, hindex, hsuperGeo, hshort, rfl, hentry⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerSelectConsume_localEntry_fits shape invocation index
        super entry hinv hindex hsuperGeo hshort hentry hrequest
  | longRank invocation n index super rank =>
      obtain ⟨rfl, hinv, hindex, hsuperGeo, hlong, hrankFit, hrank,
        horbit⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerSelectConsume_longRank_fits shape invocation index
        super rank hinv hindex hsuperGeo hlong hrankFit hrank horbit hrequest
  | longRelative invocation base slot =>
      obtain ⟨hinv, hbase, hbaseLe, hslot, hcontent⟩ := hstate
      exact packedReviewerSelectConsume_longRelative_fits shape invocation
        base slot hcontent hrequest
  | sparseRank invocation n index localSlot super loc rank =>
      obtain ⟨rfl, hinv, hindex, hlocalGeo, rfl, hmarked, hrankFit, hrank,
        horbit⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerSelectConsume_sparseRank_fits shape invocation index
        super loc rank hinv hindex hlocalGeo hmarked hrankFit hrank horbit
        hrequest
  | sparseRelative invocation base slot =>
      obtain ⟨hinv, hbase, hbaseLe, hslot, hcontent⟩ := hstate
      exact packedReviewerSelectConsume_sparseRelative_fits shape invocation
        base slot hcontent hrequest
  | denseFirstWord invocation n index basePosition baseOccurrence =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc⟩ := hstate
      exact packedReviewerSelectConsume_denseFirstWord_fits shape invocation
        index basePosition baseOccurrence hinv hindex hbase hocc hrequest
  | denseBeforeRank invocation n index basePosition baseOccurrence word
      rank =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hword, hwordLen, hword2n,
        hrankFit, hrank, hbudget⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerSelectConsume_denseBeforeRank_fits shape invocation
        index basePosition baseOccurrence word rank hinv hindex hbase hocc
        hword hwordLen hword2n hbudget hrankFit hrank hrequest
  | denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
      word rank =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hbefore, hword, hwordLen,
        hword2n, hrankFit, hrank, hbudget⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact packedReviewerSelectConsume_denseUptoRank_fits shape invocation
        index basePosition baseOccurrence beforeFirst word rank hinv hindex
        hbase hocc hbefore hword hwordLen hword2n hbudget hrankFit hrank
        hrequest
  | denseFirstSelect invocation n baseWord select =>
      obtain ⟨rfl, hinv, hbaseBound, hselectFit, ⟨word, hword, hwordLen,
        hword2n, hselect⟩, hnine⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact (packedReviewerSelectConsume_denseSelect_fits shape invocation
        baseWord select word hinv hbaseBound hword hwordLen hword2n hselect
        hselectFit hnine hrequest).1
  | denseSecondWord invocation n index basePosition baseOccurrence
      beforeFirst uptoFirst =>
      obtain ⟨rfl, hinv, hindex, hbase, hocc, hbeforeW, huptoW⟩ := hstate
      exact packedReviewerSelectConsume_denseSecondWord_fits shape invocation
        index basePosition baseOccurrence beforeFirst uptoFirst hinv hindex
        hbase hocc hrequest
  | denseSecondSelect invocation n baseWord select =>
      obtain ⟨rfl, hinv, hbaseBound, hselectFit, ⟨word, hword, hwordLen,
        hword2n, hselect⟩, hnine⟩ := hstate
      simp only [packedReviewerSelectNextRequest] at hrequest
      exact (packedReviewerSelectConsume_denseSelect_fits shape invocation
        baseWord select word hinv hbaseBound hword hwordLen hword2n hselect
        hselectFit hnine hrequest).2
  | done value => simp [packedReviewerSelectNextRequest] at hrequest

/-! ## Close/LCA tower foundations -/

/-- One consumed reply keeps a strictly smaller request-width witness. -/
private theorem packedReviewerRequestsFitFrom_consume_witness
    {State : Type} {n : Nat} {store : WordRAM.ReadStore}
    {nextRequest : State -> Option PackedReviewerLogicalRequest}
    {consumeReply : State -> Option (List Bool) -> State}
    {remaining remaining' : Nat} {state : State}
    {request : PackedReviewerLogicalRequest}
    (hfit : PackedReviewerRequestsFitFrom n store nextRequest consumeReply
      remaining state)
    (hrequest : nextRequest state = some request)
    (hle : remaining' + 1 <= remaining) :
    PackedReviewerRequestsFitFrom n store nextRequest consumeReply remaining'
      (consumeReply state
        (store.readWord? request.segment request.index)) := by
  obtain ⟨fuel, hfuel⟩ : exists fuel, remaining = fuel + 1 :=
    ⟨remaining - 1, by omega⟩
  rw [hfuel] at hfit
  have hstep := (PackedReviewerRequestsFitFrom.step n store nextRequest
    consumeReply fuel state request hfit hrequest).2
  exact PackedReviewerRequestsFitFrom.mono n store nextRequest consumeReply
    hstep (by omega)

private theorem packedReviewerBPWindowNextRequest_remaining_pos
    {state : PackedReviewerBPWindowState}
    {request : PackedReviewerLogicalRequest}
    (h : packedReviewerBPWindowNextRequest state = some request) :
    0 < packedReviewerBPWindowRemaining state := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      have hnext : next < 4 := by
        by_cases hlt : next < 4
        · exact hlt
        · simp [packedReviewerBPWindowNextRequest, hlt] at h
      simp only [packedReviewerBPWindowRemaining]
      omega
  | done bits =>
      simp [packedReviewerBPWindowNextRequest] at h

private theorem packedReviewerBPWindowRemaining_consume_le
    (state : PackedReviewerBPWindowState) (reply : Option (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerBPWindowNextRequest state = some request) :
    packedReviewerBPWindowRemaining
          (packedReviewerBPWindowConsumeReply state reply) + 1 <=
      packedReviewerBPWindowRemaining state := by
  cases state with
  | read invocation n blockSize close next wordsRev =>
      have hnext : next < 4 := by
        by_cases hlt : next < 4
        · exact hlt
        · simp [packedReviewerBPWindowNextRequest, hlt] at hrequest
      by_cases hlast : next + 1 = 4
      · simp only [packedReviewerBPWindowConsumeReply, hlast, if_true,
          packedReviewerBPWindowRemaining]
        omega
      · simp only [packedReviewerBPWindowConsumeReply, hlast, if_false,
          packedReviewerBPWindowRemaining]
        omega
  | done bits =>
      simp [packedReviewerBPWindowNextRequest] at hrequest

private theorem packedReviewerFringeNextRequest_remaining_pos
    {state : PackedReviewerFringeState}
    {request : PackedReviewerLogicalRequest}
    (h : packedReviewerFringeNextRequest state = some request) :
    0 < packedReviewerFringeRemaining state := by
  cases state with
  | chunk invocation n window relLo relHi j remaining foldState =>
      cases remaining with
      | zero => simp [packedReviewerFringeNextRequest] at h
      | succ remaining =>
          simp [packedReviewerFringeRemaining]
  | done result =>
      simp [packedReviewerFringeNextRequest] at h

private theorem packedReviewerFringeRemaining_consume_le
    (state : PackedReviewerFringeState) (reply : Option (List Bool))
    (request : PackedReviewerLogicalRequest)
    (hrequest : packedReviewerFringeNextRequest state = some request) :
    packedReviewerFringeRemaining
          (packedReviewerFringeConsumeReply state reply) + 1 <=
      packedReviewerFringeRemaining state := by
  cases state with
  | chunk invocation n window relLo relHi j remaining foldState =>
      cases remaining with
      | zero => simp [packedReviewerFringeNextRequest] at hrequest
      | succ remaining =>
          by_cases hzero : remaining = 0
          · simp [packedReviewerFringeConsumeReply, hzero,
              packedReviewerFringeRemaining]
          · simp only [packedReviewerFringeConsumeReply, hzero, if_false,
              packedReviewerFringeRemaining]
            omega
  | done result =>
      simp [packedReviewerFringeNextRequest] at hrequest

/-- Segment-zero window reads emit fitting operands for any close within the
augmented parenthesis string; the CP leaf's strict bound is not needed. -/
private theorem packedReviewerLcaBPWindow_read_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (blockSize close next fuel : Nat) (wordsRev : List (List Bool))
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hclose : close <= 2 * shape.size + 1)
    (hfour : next + fuel = 4) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply fuel
      (.read invocation shape.size blockSize close next wordsRev) := by
  induction fuel generalizing next wordsRev with
  | zero => trivial
  | succ fuel ih =>
      have hnext : next < 4 := by omega
      let firstWord :=
        SuccinctClose.blockStartOf blockSize
            (SuccinctClose.blockOfClose blockSize close) /
          packedBpCodeWordWidth shape.size
      have hbase :
          SuccinctClose.blockStartOf blockSize
              (SuccinctClose.blockOfClose blockSize close) <= close :=
        SuccinctClose.blockStartOf_blockOfClose_le
      have hfirst : firstWord <= close :=
        Nat.le_trans (Nat.div_le_self _ _) hbase
      have hindexLe : firstWord + next <= 2 * shape.size + 4 := by omega
      have hindex : PackedReviewerNatFits shape.size (firstWord + next) := by
        have hbound := packedReviewerTwoMul_add_three_le_cellBound shape.size
        have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
        omega
      have hnextFits : PackedReviewerNatFits shape.size next :=
        packedReviewerSegment_le_twentyTwo_fits shape.size next (by omega)
      have hrequest :
          PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .bpWindowWord next
              segment := 0
              index := firstWord + next } := by
        apply packedReviewerLogicalRequestOperandsFit_mk
        · exact hinvocation
        · intro operand hopen
          simp [packedReviewerReadSiteOperands] at hopen
          subst operand
          exact hnextFits
        · exact packedReviewerSegment_le_twentyTwo_fits shape.size 0 (by omega)
        · exact hindex
      simp only [PackedReviewerRequestsFitFrom,
        packedReviewerBPWindowNextRequest, hnext, if_pos]
      change
        PackedReviewerLogicalRequestOperandsFit shape.size
            { invocation := invocation
              site := .bpWindowWord next
              segment := 0
              index := firstWord + next } ∧ _
      refine ⟨hrequest, ?_⟩
      by_cases hlast : next + 1 = 4
      · have hfuel0 : fuel = 0 := by omega
        subst fuel
        trivial
      · have hfour' : next + 1 + fuel = 4 := by omega
        simpa [packedReviewerBPWindowConsumeReply, hlast, firstWord] using
          ih (next + 1)
            (((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                0 (firstWord + next)).getD [] :: wordsRev)
            hfour'

private theorem packedReviewerLcaBPWindowStart_requests_fit
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (blockSize close : Nat)
    (hinvocation :
      forall operand, operand ∈ packedReviewerInvocationOperands invocation ->
        PackedReviewerNatFits shape.size operand)
    (hclose : close <= 2 * shape.size + 1) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply 4
      (packedReviewerBPWindowStart invocation shape.size blockSize close) := by
  simpa [packedReviewerBPWindowStart] using
    packedReviewerLcaBPWindow_read_requests_fit shape invocation blockSize
      close 0 4 [] hinvocation hclose rfl

/-- Thirty-three fringe chunks and a seed inside the parenthesis string stay
below the reviewer cell capacity: the fringe table's own footprint dominates
the chunk budget at every size. -/
private theorem packedReviewerFringeBudget_fits
    (shape : CartesianShape) {seed count : Nat}
    (hseed : seed <= 2 * shape.size + 1) (hcount : count <= 33) :
    PackedReviewerNatFits shape.size
      (seed + count * packedFringeChunkBits shape.size) := by
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hforty := packedReviewerFringeTableOverhead_ge_forty shape.size
  have hoverhead :
      2 * shape.size + SuccinctClose.bpFringeTableOverhead shape.size <=
        packedReviewerCellBound shape.size := by
    unfold packedReviewerCellBound
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    omega
  have hmul :
      count * packedFringeChunkBits shape.size <=
        33 * packedFringeChunkBits shape.size :=
    Nat.mul_le_mul_right _ hcount
  have hchunkBudget :
      33 * packedFringeChunkBits shape.size + 2 <=
        SuccinctClose.bpFringeTableOverhead shape.size := by
    have hc : 0 < packedFringeChunkBits shape.size := by
      unfold packedFringeChunkBits
      exact SuccinctClose.bpFringeChunkBits_pos _
    by_cases hsmall : packedFringeChunkBits shape.size <= 1
    · omega
    · have hEB :
          8 <=
            SuccinctClose.bpFringeChunkEntryBound
              (packedFringeChunkBits shape.size) := by
        show 8 <=
          (2 * packedFringeChunkBits shape.size + 1) *
            ((2 * packedFringeChunkBits shape.size + 2) *
              (packedFringeChunkBits shape.size + 1))
        have hinner :
            4 * 2 <=
              (2 * packedFringeChunkBits shape.size + 2) *
                (packedFringeChunkBits shape.size + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have houter :
            3 *
                ((2 * packedFringeChunkBits shape.size + 2) *
                  (packedFringeChunkBits shape.size + 1)) <=
              (2 * packedFringeChunkBits shape.size + 1) *
                ((2 * packedFringeChunkBits shape.size + 2) *
                  (packedFringeChunkBits shape.size + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hW :
          4 <=
            SuccinctClose.bpFringeChunkEntryWidth
              (packedFringeChunkBits shape.size) := by
        unfold SuccinctClose.bpFringeChunkEntryWidth
        have hlog :
            3 <=
              Nat.log2
                (SuccinctClose.bpFringeChunkEntryBound
                  (packedFringeChunkBits shape.size)) :=
          (Nat.le_log2 (by omega)).mpr (by simpa using hEB)
        omega
      have hcpow :
          packedFringeChunkBits shape.size + 1 <=
            2 ^ packedFringeChunkBits shape.size :=
        Nat.lt_two_pow_self
      have hcube :
          (packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) <=
            SuccinctClose.bpFringeChunkRowCount
              (packedFringeChunkBits shape.size) := by
        show
          (packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) <=
            2 ^ packedFringeChunkBits shape.size *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1))
        exact Nat.mul_le_mul_right _ hcpow
      have hsq :
          3 * (packedFringeChunkBits shape.size + 1) <=
            (packedFringeChunkBits shape.size + 1) *
              (packedFringeChunkBits shape.size + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hnine :
          3 * (3 * (packedFringeChunkBits shape.size + 1)) <=
            3 *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) :=
        Nat.mul_le_mul_left _ hsq
      have hlift :
          3 *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) <=
            (packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have hrowW :
          SuccinctClose.bpFringeChunkRowCount
              (packedFringeChunkBits shape.size) * 4 <=
            SuccinctClose.bpFringeChunkRowCount
                (packedFringeChunkBits shape.size) *
              SuccinctClose.bpFringeChunkEntryWidth
                (packedFringeChunkBits shape.size) :=
        Nat.mul_le_mul_left _ hW
      have hcube4 :
          ((packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1))) * 4 <=
            SuccinctClose.bpFringeChunkRowCount
                (packedFringeChunkBits shape.size) * 4 :=
        Nat.mul_le_mul_right _ hcube
      have hFTO :
          SuccinctClose.bpFringeChunkRowCount
              (packedFringeChunkBits shape.size) *
            SuccinctClose.bpFringeChunkEntryWidth
              (packedFringeChunkBits shape.size) =
            SuccinctClose.bpFringeTableOverhead shape.size := rfl
      omega
  simp only [PackedReviewerNatFits]
  omega

/-- Any close within the augmented parenthesis string lands in a summary
block index at or below the raw block count. -/
private theorem packedReviewerBlockOfClose_le_blockCount
    (n close : Nat) (hclose : close <= 2 * n + 1) :
    SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw n) close <=
      packedSummaryBlockCountRaw n := by
  unfold SuccinctClose.blockOfClose packedSummaryBlockSizeRaw
    packedSummaryBlockCountRaw
  by_cases hbase : packedSummaryBase n = 0
  · simp [hbase]
  · have hmono :
        close / (2 * packedSummaryBase n) <=
          (2 * n + 1) / (2 * packedSummaryBase n) :=
      Nat.div_le_div_right hclose
    have hq := Nat.div_mul_le_self (2 * n + 1) (2 * packedSummaryBase n)
    have hassoc :
        (2 * n + 1) / (2 * packedSummaryBase n) *
            (2 * packedSummaryBase n) =
          2 *
            ((2 * n + 1) / (2 * packedSummaryBase n) *
              packedSummaryBase n) := by
      rw [Nat.mul_left_comm]
    rw [hassoc] at hq
    have hqb :
        (2 * n + 1) / (2 * packedSummaryBase n) * packedSummaryBase n <=
          n := by
      omega
    have hfin :
        (2 * n + 1) / (2 * packedSummaryBase n) <=
          n / packedSummaryBase n :=
      (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hbase)).mpr hqb
    omega

/-- The candidate the fringe fold currently carries. -/
private def packedReviewerFringeCandidateArg :
    PackedReviewerFringeState -> Option (Nat × Nat)
  | .chunk _ _ _ _ _ _ _ foldState => foldState.2
  | .done result => result.2

private theorem packedReviewerFringeResult_candidateArg
    {state : PackedReviewerFringeState} {fold : Nat × Option (Nat × Nat)}
    (hresult : packedReviewerFringeResult state = some fold) :
    packedReviewerFringeCandidateArg state = fold.2 := by
  cases state with
  | chunk invocation n window relLo relHi j remaining foldState =>
      simp [packedReviewerFringeResult] at hresult
  | done result =>
      have heq : result = fold := by
        simpa [packedReviewerFringeResult] using Option.some.inj hresult
      subst fold
      rfl

/-- One decoded chunk step keeps every carried candidate argument inside the
thirty-four chunk window. -/
private theorem packedReviewerLcaFringeArg_step
    (shape : CartesianShape) (relLo relHi j : Nat)
    (foldState : Nat × Option (Nat × Nat)) (value : Option Nat)
    (hj : j <= 32)
    (hold : forall p, foldState.2 = some p ->
      p.2 <= 34 * packedFringeChunkBits shape.size) :
    forall p,
      (SuccinctClose.bpFringeChunkStepDecoded
          (packedFringeChunkBits shape.size) relLo relHi j foldState
          value).2 = some p ->
        p.2 <= 34 * packedFringeChunkBits shape.size := by
  intro p hp
  have hc : 0 < packedFringeChunkBits shape.size := by
    unfold packedFringeChunkBits
    exact SuccinctClose.bpFringeChunkBits_pos _
  have hmod :
      (value.getD 0) % (packedFringeChunkBits shape.size + 1) <=
        packedFringeChunkBits shape.size := by
    have hlt := Nat.mod_lt (value.getD 0)
      (show 0 < packedFringeChunkBits shape.size + 1 by omega)
    omega
  have hjc :
      j * packedFringeChunkBits shape.size <=
        32 * packedFringeChunkBits shape.size :=
    Nat.mul_le_mul_right _ hj
  simp only [SuccinctClose.bpFringeChunkStepDecoded] at hp
  by_cases hoff :
      SuccinctClose.bpFringeChunkStartOff
          (packedFringeChunkBits shape.size) relLo j <
        SuccinctClose.bpFringeChunkEndOff
          (packedFringeChunkBits shape.size) relHi j
  · rw [if_pos hoff] at hp
    cases hfold : foldState.2 with
    | none =>
        rw [hfold] at hp
        simp only [SuccinctClose.bpFringeMergeCand,
          Option.some.injEq] at hp
        rw [← hp]
        show
          j * packedFringeChunkBits shape.size +
              (value.getD 0) % (packedFringeChunkBits shape.size + 1) <=
            34 * packedFringeChunkBits shape.size
        omega
    | some best =>
        rw [hfold] at hp
        have hbest := hold best hfold
        simp only [SuccinctClose.bpFringeMergeCand] at hp
        by_cases hbetter :
            foldState.1 +
                (value.getD 0) / (packedFringeChunkBits shape.size + 1) %
                  (2 * packedFringeChunkBits shape.size + 2) -
              packedFringeChunkBits shape.size < best.1
        · rw [if_pos hbetter] at hp
          have hpe := Option.some.inj hp
          rw [← hpe]
          show
            j * packedFringeChunkBits shape.size +
                (value.getD 0) % (packedFringeChunkBits shape.size + 1) <=
              34 * packedFringeChunkBits shape.size
          omega
        · rw [if_neg hbetter] at hp
          have hpe := Option.some.inj hp
          rw [← hpe]
          exact hbest
  · rw [if_neg hoff] at hp
    cases hfold : foldState.2 with
    | none =>
        rw [hfold] at hp
        simp [SuccinctClose.bpFringeMergeCand] at hp
    | some best =>
        rw [hfold] at hp
        have hbest := hold best hfold
        simp only [SuccinctClose.bpFringeMergeCand,
          Option.some.injEq] at hp
        rw [← hp]
        exact hbest

/-- Consuming one canonical fringe reply keeps the candidate argument inside
the thirty-four chunk window. -/
private theorem packedReviewerLcaFringeArg_consume
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (window : List Bool) (relLo relHi j remaining : Nat)
    (foldState : Nat × Option (Nat × Nat)) (reply : Option (List Bool))
    (hj : j <= 32)
    (hold : forall p, foldState.2 = some p ->
      p.2 <= 34 * packedFringeChunkBits shape.size) :
    forall p,
      packedReviewerFringeCandidateArg
          (packedReviewerFringeConsumeReply
            (.chunk invocation shape.size window relLo relHi j (remaining + 1)
              foldState) reply) = some p ->
        p.2 <= 34 * packedFringeChunkBits shape.size := by
  intro p hp
  apply packedReviewerLcaFringeArg_step shape relLo relHi j foldState
    (packedReviewerDecodeNat reply) hj hold p
  by_cases hzero : remaining = 0
  · simpa [packedReviewerFringeConsumeReply, hzero,
      packedReviewerFringeCandidateArg] using hp
  · simpa [packedReviewerFringeConsumeReply, hzero,
      packedReviewerFringeCandidateArg] using hp

/-- A globalized fringe argument fits: the base is inside the parenthesis
string and the argument inside the chunk window the table already stores. -/
private theorem packedReviewerLcaGlobalArg_fits
    (shape : CartesianShape) (base arg : Nat)
    (hbase : base <= 2 * shape.size + 1)
    (harg : arg <= 34 * packedFringeChunkBits shape.size) :
    PackedReviewerNatFits shape.size (base + arg) := by
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hforty := packedReviewerFringeTableOverhead_ge_forty shape.size
  have hoverhead :
      2 * shape.size + SuccinctClose.bpFringeTableOverhead shape.size <=
        packedReviewerCellBound shape.size := by
    unfold packedReviewerCellBound
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    omega
  have hchunkBudget :
      34 * packedFringeChunkBits shape.size + 3 <=
        SuccinctClose.bpFringeTableOverhead shape.size := by
    have hc : 0 < packedFringeChunkBits shape.size := by
      unfold packedFringeChunkBits
      exact SuccinctClose.bpFringeChunkBits_pos _
    by_cases hsmall : packedFringeChunkBits shape.size <= 1
    · omega
    · have hEB :
          8 <=
            SuccinctClose.bpFringeChunkEntryBound
              (packedFringeChunkBits shape.size) := by
        show 8 <=
          (2 * packedFringeChunkBits shape.size + 1) *
            ((2 * packedFringeChunkBits shape.size + 2) *
              (packedFringeChunkBits shape.size + 1))
        have hinner :
            4 * 2 <=
              (2 * packedFringeChunkBits shape.size + 2) *
                (packedFringeChunkBits shape.size + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have houter :
            3 *
                ((2 * packedFringeChunkBits shape.size + 2) *
                  (packedFringeChunkBits shape.size + 1)) <=
              (2 * packedFringeChunkBits shape.size + 1) *
                ((2 * packedFringeChunkBits shape.size + 2) *
                  (packedFringeChunkBits shape.size + 1)) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      have hW :
          4 <=
            SuccinctClose.bpFringeChunkEntryWidth
              (packedFringeChunkBits shape.size) := by
        unfold SuccinctClose.bpFringeChunkEntryWidth
        have hlog :
            3 <=
              Nat.log2
                (SuccinctClose.bpFringeChunkEntryBound
                  (packedFringeChunkBits shape.size)) :=
          (Nat.le_log2 (by omega)).mpr (by simpa using hEB)
        omega
      have hcpow :
          packedFringeChunkBits shape.size + 1 <=
            2 ^ packedFringeChunkBits shape.size :=
        Nat.lt_two_pow_self
      have hcube :
          (packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) <=
            SuccinctClose.bpFringeChunkRowCount
              (packedFringeChunkBits shape.size) := by
        show
          (packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) <=
            2 ^ packedFringeChunkBits shape.size *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1))
        exact Nat.mul_le_mul_right _ hcpow
      have hsq :
          3 * (packedFringeChunkBits shape.size + 1) <=
            (packedFringeChunkBits shape.size + 1) *
              (packedFringeChunkBits shape.size + 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have hnine :
          3 * (3 * (packedFringeChunkBits shape.size + 1)) <=
            3 *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) :=
        Nat.mul_le_mul_left _ hsq
      have hlift :
          3 *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) <=
            (packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      have hrowW :
          SuccinctClose.bpFringeChunkRowCount
              (packedFringeChunkBits shape.size) * 4 <=
            SuccinctClose.bpFringeChunkRowCount
                (packedFringeChunkBits shape.size) *
              SuccinctClose.bpFringeChunkEntryWidth
                (packedFringeChunkBits shape.size) :=
        Nat.mul_le_mul_left _ hW
      have hcube4 :
          ((packedFringeChunkBits shape.size + 1) *
              ((packedFringeChunkBits shape.size + 1) *
                (packedFringeChunkBits shape.size + 1))) * 4 <=
            SuccinctClose.bpFringeChunkRowCount
                (packedFringeChunkBits shape.size) * 4 :=
        Nat.mul_le_mul_right _ hcube
      have hFTO :
          SuccinctClose.bpFringeChunkRowCount
              (packedFringeChunkBits shape.size) *
            SuccinctClose.bpFringeChunkEntryWidth
              (packedFringeChunkBits shape.size) =
            SuccinctClose.bpFringeTableOverhead shape.size := rfl
      omega
  simp only [PackedReviewerNatFits]
  omega

/-- The summary block never outgrows two rank words. -/
private theorem packedReviewerBlockSizeRaw_le_two_ws (n : Nat) :
    packedSummaryBlockSizeRaw n <= 2 * packedRankWordSize n := by
  unfold packedSummaryBlockSizeRaw packedSummaryBase
  have hws : packedRankWordSize n = Nat.log2 (2 * n) + 1 := rfl
  have hmono :
      SuccinctRank.machineWordBits n <=
        SuccinctRank.machineWordBits (2 * n) :=
    SuccinctRank.machineWordBits_mono_le (by omega)
  unfold SuccinctRank.machineWordBits at hmono
  omega

/-- The base of the local BP window never passes its close. -/
private theorem packedReviewerLcaWindowBase_le (n blockSize close : Nat) :
    packedLocalBPWindowBase n blockSize close <= close := by
  unfold packedLocalBPWindowBase
  have hstart :
      SuccinctClose.blockStartOf blockSize
          (SuccinctClose.blockOfClose blockSize close) <= close :=
    SuccinctClose.blockStartOf_blockOfClose_le
  exact Nat.le_trans (Nat.div_mul_le_self _ _) hstart

/-- Canonical scalar invariant for the close/LCA tower. -/
private def PackedReviewerLcaCanonicalScalarFits
    (shape : CartesianShape) : PackedReviewerLcaState -> Prop
  | .sameSeed invocation n leftClose rightClose rank =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape
          (packedReviewerRankQueryPos .close shape.size
            (packedLocalBPWindowBase shape.size
              (packedSummaryBlockSizeRaw shape.size) leftClose)) rank
  | .sameWindow invocation n leftClose rightClose seed window =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        seed <= 2 * shape.size + 1 ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply
          (packedReviewerBPWindowRemaining window) window ∧
        PackedReviewerBPWindowCanonicalScalarFits shape window
  | .sameFringe invocation n leftClose rightClose seed base start fringe =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        seed <= 2 * shape.size + 1 ∧
        base <= 2 * shape.size + 1 ∧
        start <= 2 * shape.size + 2 ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerFringeNextRequest packedReviewerFringeConsumeReply
          (packedReviewerFringeRemaining fringe) fringe ∧
        (exists resultBound,
          PackedReviewerFringeCanonicalScalarFits shape resultBound fringe) ∧
        (forall p, packedReviewerFringeCandidateArg fringe = some p ->
          p.2 <= 34 * packedFringeChunkBits shape.size)
  | .leftSeed invocation n leftClose rightClose rank =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape
          (packedReviewerRankQueryPos .close shape.size
            (packedLocalBPWindowBase shape.size
              (packedSummaryBlockSizeRaw shape.size) leftClose)) rank
  | .leftWindow invocation n leftClose rightClose seed window =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        seed <= 2 * shape.size + 1 ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply
          (packedReviewerBPWindowRemaining window) window ∧
        PackedReviewerBPWindowCanonicalScalarFits shape window
  | .leftFringe invocation n leftClose rightClose seed base start fringe =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        seed <= 2 * shape.size + 1 ∧
        base <= 2 * shape.size + 1 ∧
        start <= 2 * shape.size + 2 ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerFringeNextRequest packedReviewerFringeConsumeReply
          (packedReviewerFringeRemaining fringe) fringe ∧
        (exists resultBound,
          PackedReviewerFringeCanonicalScalarFits shape resultBound fringe) ∧
        (forall p, packedReviewerFringeCandidateArg fringe = some p ->
          p.2 <= 34 * packedFringeChunkBits shape.size)
  | .middle invocation n leftClose rightClose left interior =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        PackedReviewerCandidateScalarFits shape left ∧
        PackedReviewerInteriorCanonicalScalarFits shape invocation
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              leftClose + 1)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              rightClose -
            SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              leftClose - 1) interior
  | .rightSeed invocation n leftClose rightClose left middle rank =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        PackedReviewerCandidateScalarFits shape left ∧
        PackedReviewerCandidateScalarFits shape middle ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape
          (packedReviewerRankQueryPos .close shape.size
            (packedLocalBPWindowBase shape.size
              (packedSummaryBlockSizeRaw shape.size) rightClose)) rank
  | .rightWindow invocation n leftClose rightClose seed left middle window =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        seed <= 2 * shape.size + 1 ∧
        PackedReviewerCandidateScalarFits shape left ∧
        PackedReviewerCandidateScalarFits shape middle ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply
          (packedReviewerBPWindowRemaining window) window ∧
        PackedReviewerBPWindowCanonicalScalarFits shape window
  | .rightFringe invocation n leftClose rightClose seed base start left middle
        fringe =>
      n = shape.size ∧
        (forall operand,
          operand ∈ packedReviewerInvocationOperands invocation ->
            PackedReviewerNatFits shape.size operand) ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        seed <= 2 * shape.size + 1 ∧
        base <= 2 * shape.size + 1 ∧
        start <= 2 * shape.size + 2 ∧
        PackedReviewerCandidateScalarFits shape left ∧
        PackedReviewerCandidateScalarFits shape middle ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerFringeNextRequest packedReviewerFringeConsumeReply
          (packedReviewerFringeRemaining fringe) fringe ∧
        (exists resultBound,
          PackedReviewerFringeCanonicalScalarFits shape resultBound fringe) ∧
        (forall p, packedReviewerFringeCandidateArg fringe = some p ->
          p.2 <= 34 * packedFringeChunkBits shape.size)
  | .done value =>
      forall answer, value = some answer ->
        PackedReviewerNatFits shape.size answer ∧
          PackedReviewerNatFits shape.size (answer + 1)

/-- A fitting candidate closes to a fitting done value with `+1` slack. -/
private theorem packedReviewerLcaCandidateClose_fits
    (shape : CartesianShape) {candidate : PackedReviewerCandidate}
    (hcandidate : PackedReviewerCandidateScalarFits shape candidate) :
    PackedReviewerLcaCanonicalScalarFits shape
      (.done (SuccinctClose.bpCandidateClose? candidate)) := by
  intro answer hanswer
  cases candidate with
  | none => simp [SuccinctClose.bpCandidateClose?] at hanswer
  | some candidate =>
      rcases candidate with ⟨value, index⟩
      simp only [SuccinctClose.bpCandidateClose?, Option.map_some,
        Option.some.injEq] at hanswer
      subst answer
      have hindex := hcandidate.2
      have hforty := packedReviewerCellBound_ge_forty shape.size
      have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
      constructor
      · simp only [PackedReviewerNatFits] at hindex ⊢
        omega
      · simp only [PackedReviewerNatFits] at hindex ⊢
        omega

/-- The globalized fringe fold candidate has fitting components. -/
private theorem packedReviewerLcaFringeCandidateGlobal_fits
    (shape : CartesianShape) (base seed start resultBound : Nat)
    (result : Nat × Option (Nat × Nat))
    (hbase : base <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hstart : start <= 2 * shape.size + 2)
    (hresult : PackedReviewerFringeResultScalarFits shape resultBound result)
    (harg :
      forall p, result.2 = some p ->
        p.2 <= 34 * packedFringeChunkBits shape.size) :
    PackedReviewerCandidateScalarFits shape
      (SuccinctClose.bpFringeCandGlobal base seed start result.2) := by
  rcases result with ⟨acc, candidate⟩
  rcases hresult with ⟨hboundFits, hacc, hwithin⟩
  cases candidate with
  | none =>
      simp only [SuccinctClose.bpFringeCandGlobal]
      refine ⟨packedReviewerNatFits_of_le_two_mul_add_one shape.size seed
        hseed, ?_⟩
      have hbound := packedReviewerTwoMul_add_three_le_cellBound shape.size
      have hcapacity := packedReviewerCellBound_lt_two_pow_width shape.size
      simp only [PackedReviewerNatFits]
      omega
  | some p =>
      obtain ⟨hp1, hp2⟩ := hwithin
      have hargBound := harg p rfl
      simp only [SuccinctClose.bpFringeCandGlobal]
      exact ⟨Nat.lt_of_le_of_lt hp1 hboundFits,
        packedReviewerLcaGlobalArg_fits shape base p.2 hbase hargBound⟩

/-- Entering the right-block seed once both endpoint candidates are ready. -/
private theorem packedReviewerLcaStartRightSeed_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (left middle : PackedReviewerCandidate)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hleftCand : PackedReviewerCandidateScalarFits shape left)
    (hmiddleCand : PackedReviewerCandidateScalarFits shape middle) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartRightSeed invocation shape.size leftClose
        rightClose left middle) := by
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) rightClose
  have hbaseFits :
      PackedReviewerNatFits shape.size
        (packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) rightClose) :=
    packedReviewerNatFits_of_le_two_mul_add_one shape.size _ (by omega)
  have hwitness :=
    packedReviewerRankStart_requests_fit shape invocation .close
      (packedLocalBPWindowBase shape.size
        (packedSummaryBlockSizeRaw shape.size) rightClose) hinv
  have hrank :=
    packedReviewerRankStart_canonicalScalarFits shape invocation .close
      (packedLocalBPWindowBase shape.size
        (packedSummaryBlockSizeRaw shape.size) rightClose) hinv hbaseFits
  unfold packedReviewerLcaStartRightSeed
  exact ⟨rfl, hinv, hleft, hright, hleftCand, hmiddleCand,
    by simpa [packedReviewerLcaRankStart, packedReviewerRankRemaining]
      using hwitness,
    by simpa [packedReviewerLcaRankStart] using hrank⟩

/-- Entering the same-block or cross-block window after the seed rank. -/
private theorem packedReviewerLcaStartSameWindow_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose rankFalse : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartSameWindow invocation shape.size leftClose
        rightClose rankFalse) := by
  have hws2 := packedRankWordSize_two_le_aux shape.size
  have haux := packedRankAux_le_reviewerBound shape.size
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hbs := packedReviewerBlockSizeRaw_le_two_ws shape.size
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) leftClose
  have hseed :
      packedReviewerLcaSeed shape.size (packedSummaryBlockSizeRaw shape.size)
          leftClose rankFalse <= 2 * shape.size + 1 := by
    unfold packedReviewerLcaSeed SuccinctClose.localBPSeedFromRankFalse
    omega
  have hblockFits :
      PackedReviewerNatFits shape.size
        (packedSummaryBlockSizeRaw shape.size) := by
    simp only [PackedReviewerNatFits]
    omega
  have hcloseFits : PackedReviewerNatFits shape.size leftClose :=
    packedReviewerNatFits_of_le_two_mul_add_one shape.size leftClose hleft
  have hwitness :=
    packedReviewerLcaBPWindowStart_requests_fit shape invocation
      (packedSummaryBlockSizeRaw shape.size) leftClose hinv hleft
  have hwindow :=
    packedReviewerBPWindowStart_canonicalScalarFits shape invocation
      (packedSummaryBlockSizeRaw shape.size) leftClose hinv hblockFits
      hcloseFits
  unfold packedReviewerLcaStartSameWindow
  exact ⟨rfl, hinv, hleft, hright, hseed,
    by simpa [packedReviewerBPWindowStart,
      packedReviewerBPWindowRemaining] using hwitness,
    hwindow⟩

/-- Entering the cross-block left window after the seed rank. -/
private theorem packedReviewerLcaStartLeftWindow_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose rankFalse : Nat)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartLeftWindow invocation shape.size leftClose
        rightClose rankFalse) := by
  have hws2 := packedRankWordSize_two_le_aux shape.size
  have haux := packedRankAux_le_reviewerBound shape.size
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hbs := packedReviewerBlockSizeRaw_le_two_ws shape.size
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) leftClose
  have hseed :
      packedReviewerLcaSeed shape.size (packedSummaryBlockSizeRaw shape.size)
          leftClose rankFalse <= 2 * shape.size + 1 := by
    unfold packedReviewerLcaSeed SuccinctClose.localBPSeedFromRankFalse
    omega
  have hblockFits :
      PackedReviewerNatFits shape.size
        (packedSummaryBlockSizeRaw shape.size) := by
    simp only [PackedReviewerNatFits]
    omega
  have hcloseFits : PackedReviewerNatFits shape.size leftClose :=
    packedReviewerNatFits_of_le_two_mul_add_one shape.size leftClose hleft
  have hwitness :=
    packedReviewerLcaBPWindowStart_requests_fit shape invocation
      (packedSummaryBlockSizeRaw shape.size) leftClose hinv hleft
  have hwindow :=
    packedReviewerBPWindowStart_canonicalScalarFits shape invocation
      (packedSummaryBlockSizeRaw shape.size) leftClose hinv hblockFits
      hcloseFits
  unfold packedReviewerLcaStartLeftWindow
  exact ⟨rfl, hinv, hleft, hright, hseed,
    by simpa [packedReviewerBPWindowStart,
      packedReviewerBPWindowRemaining] using hwitness,
    hwindow⟩

/-- Entering the right window with both candidates in hand. -/
private theorem packedReviewerLcaStartRightWindow_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose rankFalse : Nat)
    (left middle : PackedReviewerCandidate)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hleftCand : PackedReviewerCandidateScalarFits shape left)
    (hmiddleCand : PackedReviewerCandidateScalarFits shape middle) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartRightWindow invocation shape.size leftClose
        rightClose rankFalse left middle) := by
  have hws2 := packedRankWordSize_two_le_aux shape.size
  have haux := packedRankAux_le_reviewerBound shape.size
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hbs := packedReviewerBlockSizeRaw_le_two_ws shape.size
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) rightClose
  have hseed :
      packedReviewerLcaSeed shape.size (packedSummaryBlockSizeRaw shape.size)
          rightClose rankFalse <= 2 * shape.size + 1 := by
    unfold packedReviewerLcaSeed SuccinctClose.localBPSeedFromRankFalse
    omega
  have hblockFits :
      PackedReviewerNatFits shape.size
        (packedSummaryBlockSizeRaw shape.size) := by
    simp only [PackedReviewerNatFits]
    omega
  have hcloseFits : PackedReviewerNatFits shape.size rightClose :=
    packedReviewerNatFits_of_le_two_mul_add_one shape.size rightClose hright
  have hwitness :=
    packedReviewerLcaBPWindowStart_requests_fit shape invocation
      (packedSummaryBlockSizeRaw shape.size) rightClose hinv hright
  have hwindow :=
    packedReviewerBPWindowStart_canonicalScalarFits shape invocation
      (packedSummaryBlockSizeRaw shape.size) rightClose hinv hblockFits
      hcloseFits
  unfold packedReviewerLcaStartRightWindow
  exact ⟨rfl, hinv, hleft, hright, hseed, hleftCand, hmiddleCand,
    by simpa [packedReviewerBPWindowStart,
      packedReviewerBPWindowRemaining] using hwitness,
    hwindow⟩

/-- The fringe start carries no candidate, so its argument clause is vacuous. -/
private theorem packedReviewerLcaFringeStartArg_vacuous
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (window : List Bool) (seed relLo relHi count : Nat) :
    forall p,
      packedReviewerFringeCandidateArg
          (packedReviewerFringeStart invocation shape.size window seed relLo
            relHi count) = some p ->
        p.2 <= 34 * packedFringeChunkBits shape.size := by
  intro p hp
  by_cases hcount0 : count = 0 <;>
    simp [packedReviewerFringeStart, hcount0,
      packedReviewerFringeCandidateArg] at hp

/-- Entering the same-block fringe fold after the window assembles. -/
private theorem packedReviewerLcaStartSameFringe_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (window : List Bool)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartSameFringe invocation shape.size leftClose
        rightClose seed window) := by
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hthree := packedReviewerTwoMul_add_three_le_cellBound shape.size
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) leftClose
  have hbase :
      packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) leftClose <=
        2 * shape.size + 1 := by
    omega
  have hstart : leftClose + 1 <= 2 * shape.size + 2 := by omega
  have hrelLo :
      PackedReviewerNatFits shape.size
        (leftClose + 1 -
          packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) leftClose) := by
    simp only [PackedReviewerNatFits]
    omega
  have hrelHi :
      PackedReviewerNatFits shape.size
        (leftClose + 1 + (rightClose - leftClose + 1) - 1 -
          packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) leftClose) := by
    simp only [PackedReviewerNatFits]
    omega
  have hcount :
      Nat.min
          ((leftClose + 1 + (rightClose - leftClose + 1) - 1 -
              packedLocalBPWindowBase shape.size
                (packedSummaryBlockSizeRaw shape.size) leftClose) /
              packedFringeChunkBits shape.size + 1) 33 <= 33 :=
    Nat.min_le_right _ _
  have hbudget := packedReviewerFringeBudget_fits shape hseed hcount
  have hfits :=
    packedReviewerFringeStart_canonicalScalarFits shape invocation window
      seed _ _ _ hinv hrelLo hrelHi hcount hbudget
  have hwitness :=
    packedReviewerFringeStart_requests_fit shape invocation window seed
      (leftClose + 1 -
        packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) leftClose)
      (leftClose + 1 + (rightClose - leftClose + 1) - 1 -
        packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) leftClose)
      (Nat.min
        ((leftClose + 1 + (rightClose - leftClose + 1) - 1 -
            packedLocalBPWindowBase shape.size
              (packedSummaryBlockSizeRaw shape.size) leftClose) /
            packedFringeChunkBits shape.size + 1) 33) hinv
  unfold packedReviewerLcaStartSameFringe
  exact ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hwitness,
    ⟨_, hfits⟩,
    packedReviewerLcaFringeStartArg_vacuous shape invocation window seed _ _ _⟩

/-- Entering the cross-block left fringe fold after the window assembles. -/
private theorem packedReviewerLcaStartLeftFringe_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (window : List Bool)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartLeftFringe invocation shape.size leftClose
        rightClose seed window) := by
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hthree := packedReviewerTwoMul_add_three_le_cellBound shape.size
  have hws2 := packedRankWordSize_two_le_aux shape.size
  have haux := packedRankAux_le_reviewerBound shape.size
  have hbs := packedReviewerBlockSizeRaw_le_two_ws shape.size
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) leftClose
  have hblockStartLe :
      SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            leftClose) <= leftClose :=
    SuccinctClose.blockStartOf_blockOfClose_le
  have hbase :
      packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) leftClose <=
        2 * shape.size + 1 := by
    omega
  have hstart : leftClose + 1 <= 2 * shape.size + 2 := by omega
  have hrelLo :
      PackedReviewerNatFits shape.size
        (leftClose + 1 -
          packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) leftClose) := by
    simp only [PackedReviewerNatFits]
    omega
  have hrelHi :
      PackedReviewerNatFits shape.size
        (leftClose + 1 +
            (SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
                (SuccinctClose.blockOfClose
                  (packedSummaryBlockSizeRaw shape.size) leftClose) +
              packedSummaryBlockSizeRaw shape.size - leftClose) - 1 -
          packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) leftClose) := by
    simp only [PackedReviewerNatFits]
    omega
  have hcount :
      Nat.min
          ((leftClose + 1 +
              (SuccinctClose.blockStartOf
                  (packedSummaryBlockSizeRaw shape.size)
                  (SuccinctClose.blockOfClose
                    (packedSummaryBlockSizeRaw shape.size) leftClose) +
                packedSummaryBlockSizeRaw shape.size - leftClose) - 1 -
              packedLocalBPWindowBase shape.size
                (packedSummaryBlockSizeRaw shape.size) leftClose) /
              packedFringeChunkBits shape.size + 1) 33 <= 33 :=
    Nat.min_le_right _ _
  have hbudget := packedReviewerFringeBudget_fits shape hseed hcount
  have hfits :=
    packedReviewerFringeStart_canonicalScalarFits shape invocation window
      seed _ _ _ hinv hrelLo hrelHi hcount hbudget
  have hwitness :=
    packedReviewerFringeStart_requests_fit shape invocation window seed
      (leftClose + 1 -
        packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) leftClose)
      (leftClose + 1 +
          (SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
              (SuccinctClose.blockOfClose
                (packedSummaryBlockSizeRaw shape.size) leftClose) +
            packedSummaryBlockSizeRaw shape.size - leftClose) - 1 -
        packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) leftClose)
      (Nat.min
        ((leftClose + 1 +
            (SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
                (SuccinctClose.blockOfClose
                  (packedSummaryBlockSizeRaw shape.size) leftClose) +
              packedSummaryBlockSizeRaw shape.size - leftClose) - 1 -
            packedLocalBPWindowBase shape.size
              (packedSummaryBlockSizeRaw shape.size) leftClose) /
            packedFringeChunkBits shape.size + 1) 33) hinv
  unfold packedReviewerLcaStartLeftFringe
  exact ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hwitness,
    ⟨_, hfits⟩,
    packedReviewerLcaFringeStartArg_vacuous shape invocation window seed _ _ _⟩

/-- Entering the right fringe fold with both candidates in hand. -/
private theorem packedReviewerLcaStartRightFringe_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat)
    (left middle : PackedReviewerCandidate) (window : List Bool)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hleftCand : PackedReviewerCandidateScalarFits shape left)
    (hmiddleCand : PackedReviewerCandidateScalarFits shape middle) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartRightFringe invocation shape.size leftClose
        rightClose seed left middle window) := by
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  have hthree := packedReviewerTwoMul_add_three_le_cellBound shape.size
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) rightClose
  have hblockStartLe :
      SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            rightClose) <= rightClose :=
    SuccinctClose.blockStartOf_blockOfClose_le
  have hbase :
      packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) rightClose <=
        2 * shape.size + 1 := by
    omega
  have hstart :
      SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            rightClose) <= 2 * shape.size + 2 := by
    omega
  have hrelLo :
      PackedReviewerNatFits shape.size
        (SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
            (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              rightClose) -
          packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) rightClose) := by
    simp only [PackedReviewerNatFits]
    omega
  have hrelHi :
      PackedReviewerNatFits shape.size
        (SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
            (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              rightClose) +
            (rightClose -
              SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
                (SuccinctClose.blockOfClose
                  (packedSummaryBlockSizeRaw shape.size) rightClose) + 2) -
            1 -
          packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) rightClose) := by
    simp only [PackedReviewerNatFits]
    omega
  have hcount :
      Nat.min
          ((SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
              (SuccinctClose.blockOfClose
                (packedSummaryBlockSizeRaw shape.size) rightClose) +
              (rightClose -
                SuccinctClose.blockStartOf
                  (packedSummaryBlockSizeRaw shape.size)
                  (SuccinctClose.blockOfClose
                    (packedSummaryBlockSizeRaw shape.size) rightClose) + 2) -
              1 -
              packedLocalBPWindowBase shape.size
                (packedSummaryBlockSizeRaw shape.size) rightClose) /
              packedFringeChunkBits shape.size + 1) 33 <= 33 :=
    Nat.min_le_right _ _
  have hbudget := packedReviewerFringeBudget_fits shape hseed hcount
  have hfits :=
    packedReviewerFringeStart_canonicalScalarFits shape invocation window
      seed _ _ _ hinv hrelLo hrelHi hcount hbudget
  have hwitness :=
    packedReviewerFringeStart_requests_fit shape invocation window seed
      (SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            rightClose) -
        packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) rightClose)
      (SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
          (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            rightClose) +
          (rightClose -
            SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
              (SuccinctClose.blockOfClose
                (packedSummaryBlockSizeRaw shape.size) rightClose) + 2) - 1 -
        packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) rightClose)
      (Nat.min
        ((SuccinctClose.blockStartOf (packedSummaryBlockSizeRaw shape.size)
            (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              rightClose) +
            (rightClose -
              SuccinctClose.blockStartOf
                (packedSummaryBlockSizeRaw shape.size)
                (SuccinctClose.blockOfClose
                  (packedSummaryBlockSizeRaw shape.size) rightClose) + 2) -
            1 -
            packedLocalBPWindowBase shape.size
              (packedSummaryBlockSizeRaw shape.size) rightClose) /
            packedFringeChunkBits shape.size + 1) 33) hinv
  unfold packedReviewerLcaStartRightFringe
  exact ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hleftCand,
    hmiddleCand, hwitness, ⟨_, hfits⟩,
    packedReviewerLcaFringeStartArg_vacuous shape invocation window seed _ _ _⟩

/-- Entering (or skipping) the interior middle phase after the left fringe. -/
private theorem packedReviewerLcaStartMiddle_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (left : PackedReviewerCandidate)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hleftCand : PackedReviewerCandidateScalarFits shape left) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStartMiddle invocation shape.size leftClose rightClose
        left) := by
  have hblock :=
    packedReviewerBlockOfClose_le_blockCount shape.size rightClose hright
  simp only [packedReviewerLcaStartMiddle]
  by_cases hspan :
      SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
          leftClose + 1 <
        SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
          rightClose
  · have hrange :
        SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
              leftClose + 1 +
            (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
                rightClose -
              SuccinctClose.blockOfClose
                (packedSummaryBlockSizeRaw shape.size) leftClose - 1) <=
          packedSummaryBlockCountRaw shape.size := by
      omega
    have hinterior :=
      packedReviewerInteriorStart_canonicalScalarFits shape invocation
        (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            leftClose + 1)
        (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            rightClose -
          SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            leftClose - 1) hinv hrange
    rw [if_pos hspan]
    cases hresult :
        packedReviewerInteriorResult
          (packedReviewerInteriorStart invocation shape.size
            (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
                leftClose + 1)
            (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
                rightClose -
              SuccinctClose.blockOfClose
                (packedSummaryBlockSizeRaw shape.size) leftClose - 1)) with
    | some middle =>
        have hmiddle := hinterior.result_fits hresult
        exact packedReviewerLcaStartRightSeed_fits shape invocation leftClose
          rightClose left middle hinv hleft hright hleftCand hmiddle
    | none =>
        exact ⟨rfl, hinv, hleft, hright, hleftCand, hinterior⟩
  · rw [if_neg hspan]
    exact packedReviewerLcaStartRightSeed_fits shape invocation leftClose
      rightClose left none hinv hleft hright hleftCand trivial

/-- The canonical close/LCA start satisfies the tower invariant. -/
private theorem packedReviewerLcaStart_fits
    (shape : CartesianShape) (leftClose rightClose : Nat)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaStart shape.size leftClose rightClose) := by
  have hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands
          { instruction := .lcaClose
            argument := leftClose
            argument2 := rightClose } ->
          PackedReviewerNatFits shape.size operand := by
    intro operand hmem
    simp [packedReviewerInvocationOperands] at hmem
    rcases hmem with rfl | rfl
    · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
    · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
  have hwbLe := packedReviewerLcaWindowBase_le shape.size
    (packedSummaryBlockSizeRaw shape.size) leftClose
  have hbaseFits :
      PackedReviewerNatFits shape.size
        (packedLocalBPWindowBase shape.size
          (packedSummaryBlockSizeRaw shape.size) leftClose) :=
    packedReviewerNatFits_of_le_two_mul_add_one shape.size _ (by omega)
  have hwitness :=
    packedReviewerRankStart_requests_fit shape
      { instruction := .lcaClose
        argument := leftClose
        argument2 := rightClose } .close
      (packedLocalBPWindowBase shape.size
        (packedSummaryBlockSizeRaw shape.size) leftClose) hinv
  have hrank :=
    packedReviewerRankStart_canonicalScalarFits shape
      { instruction := .lcaClose
        argument := leftClose
        argument2 := rightClose } .close
      (packedLocalBPWindowBase shape.size
        (packedSummaryBlockSizeRaw shape.size) leftClose) hinv hbaseFits
  simp only [packedReviewerLcaStart]
  by_cases hsame :
      SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
          leftClose =
        SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
          rightClose
  · rw [if_pos hsame]
    exact ⟨rfl, hinv, hleft, hright,
      by simpa [packedReviewerLcaRankStart, packedReviewerRankRemaining]
        using hwitness,
      by simpa [packedReviewerLcaRankStart] using hrank⟩
  · rw [if_neg hsame]
    exact ⟨rfl, hinv, hleft, hright,
      by simpa [packedReviewerLcaRankStart, packedReviewerRankRemaining]
        using hwitness,
      by simpa [packedReviewerLcaRankStart] using hrank⟩

/-! ## Close/LCA tower consume transitions -/

/-- One canonical reply preserves the same-block seed arm. -/
private theorem packedReviewerLcaConsume_sameSeed_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (rank : PackedReviewerRankState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hrankFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining rank) rank)
    (hrank :
      PackedReviewerRankCanonicalScalarFits shape
        (packedReviewerRankQueryPos .close shape.size
          (packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) leftClose)) rank)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerRankNextRequest rank = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.sameSeed invocation shape.size leftClose rightClose rank)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hrank' := hrank.consume hrequest
  have hdescent :=
    packedReviewerRankRemaining_consume_le rank
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hrankFit hrequest
      (by omega)
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerRankResult
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none => exact ⟨rfl, hinv, hleft, hright, hfit', hrank'⟩
  | some rankFalse =>
      exact packedReviewerLcaStartSameWindow_fits shape invocation leftClose
        rightClose rankFalse hinv hleft hright

/-- One canonical reply preserves the cross-block left seed arm. -/
private theorem packedReviewerLcaConsume_leftSeed_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (rank : PackedReviewerRankState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hrankFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining rank) rank)
    (hrank :
      PackedReviewerRankCanonicalScalarFits shape
        (packedReviewerRankQueryPos .close shape.size
          (packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) leftClose)) rank)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerRankNextRequest rank = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.leftSeed invocation shape.size leftClose rightClose rank)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hrank' := hrank.consume hrequest
  have hdescent :=
    packedReviewerRankRemaining_consume_le rank
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hrankFit hrequest
      (by omega)
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerRankResult
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none => exact ⟨rfl, hinv, hleft, hright, hfit', hrank'⟩
  | some rankFalse =>
      exact packedReviewerLcaStartLeftWindow_fits shape invocation leftClose
        rightClose rankFalse hinv hleft hright

/-- One canonical reply preserves the right seed arm. -/
private theorem packedReviewerLcaConsume_rightSeed_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (left middle : PackedReviewerCandidate)
    (rank : PackedReviewerRankState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hleftCand : PackedReviewerCandidateScalarFits shape left)
    (hmiddleCand : PackedReviewerCandidateScalarFits shape middle)
    (hrankFit :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerRankNextRequest packedReviewerRankConsumeReply
        (packedReviewerRankRemaining rank) rank)
    (hrank :
      PackedReviewerRankCanonicalScalarFits shape
        (packedReviewerRankQueryPos .close shape.size
          (packedLocalBPWindowBase shape.size
            (packedSummaryBlockSizeRaw shape.size) rightClose)) rank)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerRankNextRequest rank = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.rightSeed invocation shape.size leftClose rightClose left middle
          rank)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hrank' := hrank.consume hrequest
  have hdescent :=
    packedReviewerRankRemaining_consume_le rank
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hrankFit hrequest
      (by omega)
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerRankResult
        (packedReviewerRankConsumeReply rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hleft, hright, hleftCand, hmiddleCand, hfit',
        hrank'⟩
  | some rankFalse =>
      exact packedReviewerLcaStartRightWindow_fits shape invocation leftClose
        rightClose rankFalse left middle hinv hleft hright hleftCand
        hmiddleCand

/-- One canonical reply preserves the same-block window arm. -/
private theorem packedReviewerLcaConsume_sameWindow_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (window : PackedReviewerBPWindowState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hwitness :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply
        (packedReviewerBPWindowRemaining window) window)
    (hwindow : PackedReviewerBPWindowCanonicalScalarFits shape window)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerBPWindowNextRequest window = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.sameWindow invocation shape.size leftClose rightClose seed window)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hwindow' := hwindow.consume hrequest
  have hdescent :=
    packedReviewerBPWindowRemaining_consume_le window
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hwitness hrequest
      (by omega)
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerBPWindowResult
        (packedReviewerBPWindowConsumeReply window
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none => exact ⟨rfl, hinv, hleft, hright, hseed, hfit', hwindow'⟩
  | some bits =>
      exact packedReviewerLcaStartSameFringe_fits shape invocation leftClose
        rightClose seed bits hinv hleft hright hseed

/-- One canonical reply preserves the cross-block left window arm. -/
private theorem packedReviewerLcaConsume_leftWindow_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (window : PackedReviewerBPWindowState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hwitness :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply
        (packedReviewerBPWindowRemaining window) window)
    (hwindow : PackedReviewerBPWindowCanonicalScalarFits shape window)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerBPWindowNextRequest window = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.leftWindow invocation shape.size leftClose rightClose seed window)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hwindow' := hwindow.consume hrequest
  have hdescent :=
    packedReviewerBPWindowRemaining_consume_le window
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hwitness hrequest
      (by omega)
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerBPWindowResult
        (packedReviewerBPWindowConsumeReply window
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none => exact ⟨rfl, hinv, hleft, hright, hseed, hfit', hwindow'⟩
  | some bits =>
      exact packedReviewerLcaStartLeftFringe_fits shape invocation leftClose
        rightClose seed bits hinv hleft hright hseed

/-- One canonical reply preserves the right window arm. -/
private theorem packedReviewerLcaConsume_rightWindow_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed : Nat) (left middle : PackedReviewerCandidate)
    (window : PackedReviewerBPWindowState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hleftCand : PackedReviewerCandidateScalarFits shape left)
    (hmiddleCand : PackedReviewerCandidateScalarFits shape middle)
    (hwitness :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerBPWindowNextRequest packedReviewerBPWindowConsumeReply
        (packedReviewerBPWindowRemaining window) window)
    (hwindow : PackedReviewerBPWindowCanonicalScalarFits shape window)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerBPWindowNextRequest window = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.rightWindow invocation shape.size leftClose rightClose seed left
          middle window)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hwindow' := hwindow.consume hrequest
  have hdescent :=
    packedReviewerBPWindowRemaining_consume_le window
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hwitness hrequest
      (by omega)
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerBPWindowResult
        (packedReviewerBPWindowConsumeReply window
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hleft, hright, hseed, hleftCand, hmiddleCand, hfit',
        hwindow'⟩
  | some bits =>
      exact packedReviewerLcaStartRightFringe_fits shape invocation leftClose
        rightClose seed left middle bits hinv hleft hright hseed hleftCand
        hmiddleCand

/-- One canonical reply preserves the same-block fringe arm. -/
private theorem packedReviewerLcaConsume_sameFringe_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed base start : Nat)
    (fringe : PackedReviewerFringeState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hbase : base <= 2 * shape.size + 1)
    (hstart : start <= 2 * shape.size + 2)
    (hwitness :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerFringeNextRequest packedReviewerFringeConsumeReply
        (packedReviewerFringeRemaining fringe) fringe)
    (hcanonical :
      exists resultBound,
        PackedReviewerFringeCanonicalScalarFits shape resultBound fringe)
    (harg :
      forall p, packedReviewerFringeCandidateArg fringe = some p ->
        p.2 <= 34 * packedFringeChunkBits shape.size)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerFringeNextRequest fringe = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.sameFringe invocation shape.size leftClose rightClose seed base
          start fringe)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  obtain ⟨resultBound, hfringe⟩ := hcanonical
  have hfringe' := hfringe.consume hrequest
  have hdescent :=
    packedReviewerFringeRemaining_consume_le fringe
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hwitness hrequest
      (by omega)
  have harg' :
      forall p,
        packedReviewerFringeCandidateArg
            (packedReviewerFringeConsumeReply fringe
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) = some p ->
          p.2 <= 34 * packedFringeChunkBits shape.size := by
    cases fringe with
    | done result => simp [packedReviewerFringeNextRequest] at hrequest
    | chunk invocation2 n2 window2 relLo relHi j remaining foldState =>
        cases remaining with
        | zero => simp [packedReviewerFringeNextRequest] at hrequest
        | succ remaining =>
            rcases foldState with ⟨acc, candidate⟩
            obtain ⟨rfl, -, -, -, hcounters, -, -, -, -⟩ := hfringe
            exact packedReviewerLcaFringeArg_consume shape invocation2
              window2 relLo relHi j remaining (acc, candidate) _
              (by omega)
              (by
                intro p hp
                exact harg p
                  (by simpa [packedReviewerFringeCandidateArg] using hp))
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerFringeResult
        (packedReviewerFringeConsumeReply fringe
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hfit',
        ⟨resultBound, hfringe'⟩, harg'⟩
  | some fold =>
      have hresultFits := hfringe'.result_fits hresult
      have hfoldArg :
          forall p, fold.2 = some p ->
            p.2 <= 34 * packedFringeChunkBits shape.size := by
        intro p hp
        apply harg'
        rw [packedReviewerFringeResult_candidateArg hresult]
        exact hp
      have hglobal :=
        packedReviewerLcaFringeCandidateGlobal_fits shape base seed start
          resultBound fold hbase hseed hstart hresultFits hfoldArg
      simpa [packedReviewerLcaFinishSameFringe] using
        packedReviewerLcaCandidateClose_fits shape hglobal

/-- One canonical reply preserves the left fringe arm; completion enters the
interior middle dispatch with the globalized left candidate. -/
private theorem packedReviewerLcaConsume_leftFringe_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed base start : Nat)
    (fringe : PackedReviewerFringeState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hbase : base <= 2 * shape.size + 1)
    (hstart : start <= 2 * shape.size + 2)
    (hwitness :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerFringeNextRequest packedReviewerFringeConsumeReply
        (packedReviewerFringeRemaining fringe) fringe)
    (hcanonical :
      exists resultBound,
        PackedReviewerFringeCanonicalScalarFits shape resultBound fringe)
    (harg :
      forall p, packedReviewerFringeCandidateArg fringe = some p ->
        p.2 <= 34 * packedFringeChunkBits shape.size)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerFringeNextRequest fringe = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.leftFringe invocation shape.size leftClose rightClose seed base
          start fringe)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  obtain ⟨resultBound, hfringe⟩ := hcanonical
  have hfringe' := hfringe.consume hrequest
  have hdescent :=
    packedReviewerFringeRemaining_consume_le fringe
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hwitness hrequest
      (by omega)
  have harg' :
      forall p,
        packedReviewerFringeCandidateArg
            (packedReviewerFringeConsumeReply fringe
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) = some p ->
          p.2 <= 34 * packedFringeChunkBits shape.size := by
    cases fringe with
    | done result => simp [packedReviewerFringeNextRequest] at hrequest
    | chunk invocation2 n2 window2 relLo relHi j remaining foldState =>
        cases remaining with
        | zero => simp [packedReviewerFringeNextRequest] at hrequest
        | succ remaining =>
            rcases foldState with ⟨acc, candidate⟩
            obtain ⟨rfl, -, -, -, hcounters, -, -, -, -⟩ := hfringe
            exact packedReviewerLcaFringeArg_consume shape invocation2
              window2 relLo relHi j remaining (acc, candidate) _
              (by omega)
              (by
                intro p hp
                exact harg p
                  (by simpa [packedReviewerFringeCandidateArg] using hp))
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerFringeResult
        (packedReviewerFringeConsumeReply fringe
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hfit',
        ⟨resultBound, hfringe'⟩, harg'⟩
  | some fold =>
      have hresultFits := hfringe'.result_fits hresult
      have hfoldArg :
          forall p, fold.2 = some p ->
            p.2 <= 34 * packedFringeChunkBits shape.size := by
        intro p hp
        apply harg'
        rw [packedReviewerFringeResult_candidateArg hresult]
        exact hp
      have hglobal :=
        packedReviewerLcaFringeCandidateGlobal_fits shape base seed start
          resultBound fold hbase hseed hstart hresultFits hfoldArg
      exact packedReviewerLcaStartMiddle_fits shape invocation leftClose
        rightClose (SuccinctClose.bpFringeCandGlobal base seed start fold.2)
        hinv hleft hright hglobal

/-- One canonical reply preserves the interior middle arm. -/
private theorem packedReviewerLcaConsume_middle_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose : Nat) (left : PackedReviewerCandidate)
    (interior : PackedReviewerInteriorState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hleftCand : PackedReviewerCandidateScalarFits shape left)
    (hinterior :
      PackedReviewerInteriorCanonicalScalarFits shape invocation
        (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            leftClose + 1)
        (SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            rightClose -
          SuccinctClose.blockOfClose (packedSummaryBlockSizeRaw shape.size)
            leftClose - 1) interior)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerInteriorNextRequest interior = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.middle invocation shape.size leftClose rightClose left interior)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  have hinterior' := hinterior.consume hrequest
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerInteriorResult
        (packedReviewerInteriorConsumeReply interior
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none => exact ⟨rfl, hinv, hleft, hright, hleftCand, hinterior'⟩
  | some middle =>
      have hmiddle := hinterior'.result_fits hresult
      exact packedReviewerLcaStartRightSeed_fits shape invocation leftClose
        rightClose left middle hinv hleft hright hleftCand hmiddle

/-- One canonical reply preserves the right fringe arm; completion merges the
three candidates and closes. -/
private theorem packedReviewerLcaConsume_rightFringe_fits
    (shape : CartesianShape) (invocation : PackedReviewerInvocation)
    (leftClose rightClose seed base start : Nat)
    (left middle : PackedReviewerCandidate)
    (fringe : PackedReviewerFringeState)
    (hinv :
      forall operand,
        operand ∈ packedReviewerInvocationOperands invocation ->
          PackedReviewerNatFits shape.size operand)
    (hleft : leftClose <= 2 * shape.size + 1)
    (hright : rightClose <= 2 * shape.size + 1)
    (hseed : seed <= 2 * shape.size + 1)
    (hbase : base <= 2 * shape.size + 1)
    (hstart : start <= 2 * shape.size + 2)
    (hleftCand : PackedReviewerCandidateScalarFits shape left)
    (hmiddleCand : PackedReviewerCandidateScalarFits shape middle)
    (hwitness :
      PackedReviewerRequestsFitFrom shape.size
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        packedReviewerFringeNextRequest packedReviewerFringeConsumeReply
        (packedReviewerFringeRemaining fringe) fringe)
    (hcanonical :
      exists resultBound,
        PackedReviewerFringeCanonicalScalarFits shape resultBound fringe)
    (harg :
      forall p, packedReviewerFringeCandidateArg fringe = some p ->
        p.2 <= 34 * packedFringeChunkBits shape.size)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerFringeNextRequest fringe = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply
        (.rightFringe invocation shape.size leftClose rightClose seed base
          start left middle fringe)
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  obtain ⟨resultBound, hfringe⟩ := hcanonical
  have hfringe' := hfringe.consume hrequest
  have hdescent :=
    packedReviewerFringeRemaining_consume_le fringe
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        request.segment request.index) request hrequest
  have hfit' :=
    packedReviewerRequestsFitFrom_consume_witness hwitness hrequest
      (by omega)
  have harg' :
      forall p,
        packedReviewerFringeCandidateArg
            (packedReviewerFringeConsumeReply fringe
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) = some p ->
          p.2 <= 34 * packedFringeChunkBits shape.size := by
    cases fringe with
    | done result => simp [packedReviewerFringeNextRequest] at hrequest
    | chunk invocation2 n2 window2 relLo relHi j remaining foldState =>
        cases remaining with
        | zero => simp [packedReviewerFringeNextRequest] at hrequest
        | succ remaining =>
            rcases foldState with ⟨acc, candidate⟩
            obtain ⟨rfl, -, -, -, hcounters, -, -, -, -⟩ := hfringe
            exact packedReviewerLcaFringeArg_consume shape invocation2
              window2 relLo relHi j remaining (acc, candidate) _
              (by omega)
              (by
                intro p hp
                exact harg p
                  (by simpa [packedReviewerFringeCandidateArg] using hp))
  simp only [packedReviewerLcaConsumeReply]
  cases hresult :
      packedReviewerFringeResult
        (packedReviewerFringeConsumeReply fringe
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) with
  | none =>
      exact ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hleftCand,
        hmiddleCand, hfit', ⟨resultBound, hfringe'⟩, harg'⟩
  | some fold =>
      have hresultFits := hfringe'.result_fits hresult
      have hfoldArg :
          forall p, fold.2 = some p ->
            p.2 <= 34 * packedFringeChunkBits shape.size := by
        intro p hp
        apply harg'
        rw [packedReviewerFringeResult_candidateArg hresult]
        exact hp
      have hright' :=
        packedReviewerLcaFringeCandidateGlobal_fits shape base seed start
          resultBound fold hbase hseed hstart hresultFits hfoldArg
      exact packedReviewerLcaCandidateClose_fits shape
        (hleftCand.merge3 hmiddleCand hright')

/-- One canonical reply preserves the whole close/LCA tower invariant. -/
private theorem PackedReviewerLcaCanonicalScalarFits.consume
    {shape : CartesianShape} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaCanonicalScalarFits shape state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerLcaNextRequest state = some request) :
    PackedReviewerLcaCanonicalScalarFits shape
      (packedReviewerLcaConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      obtain ⟨rfl, hinv, hleft, hright, hrankFit, hrank⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_sameSeed_fits shape invocation leftClose
        rightClose rank hinv hleft hright hrankFit hrank hrequest
  | sameWindow invocation n leftClose rightClose seed window =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hwitness, hwindow⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_sameWindow_fits shape invocation
        leftClose rightClose seed window hinv hleft hright hseed hwitness
        hwindow hrequest
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hwitness,
        hcanonical, harg⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_sameFringe_fits shape invocation
        leftClose rightClose seed base start fringe hinv hleft hright hseed
        hbase hstart hwitness hcanonical harg hrequest
  | leftSeed invocation n leftClose rightClose rank =>
      obtain ⟨rfl, hinv, hleft, hright, hrankFit, hrank⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_leftSeed_fits shape invocation leftClose
        rightClose rank hinv hleft hright hrankFit hrank hrequest
  | leftWindow invocation n leftClose rightClose seed window =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hwitness, hwindow⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_leftWindow_fits shape invocation
        leftClose rightClose seed window hinv hleft hright hseed hwitness
        hwindow hrequest
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hwitness,
        hcanonical, harg⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_leftFringe_fits shape invocation
        leftClose rightClose seed base start fringe hinv hleft hright hseed
        hbase hstart hwitness hcanonical harg hrequest
  | middle invocation n leftClose rightClose left interior =>
      obtain ⟨rfl, hinv, hleft, hright, hleftCand, hinterior⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_middle_fits shape invocation leftClose
        rightClose left interior hinv hleft hright hleftCand hinterior
        hrequest
  | rightSeed invocation n leftClose rightClose left middle rank =>
      obtain ⟨rfl, hinv, hleft, hright, hleftCand, hmiddleCand, hrankFit,
        hrank⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_rightSeed_fits shape invocation
        leftClose rightClose left middle rank hinv hleft hright hleftCand
        hmiddleCand hrankFit hrank hrequest
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hleftCand, hmiddleCand,
        hwitness, hwindow⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_rightWindow_fits shape invocation
        leftClose rightClose seed left middle window hinv hleft hright hseed
        hleftCand hmiddleCand hwitness hwindow hrequest
  | rightFringe invocation n leftClose rightClose seed base start left
      middle fringe =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hleftCand,
        hmiddleCand, hwitness, hcanonical, harg⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerLcaConsume_rightFringe_fits shape invocation
        leftClose rightClose seed base start left middle fringe hinv hleft
        hright hseed hbase hstart hleftCand hmiddleCand hwitness hcanonical
        harg hrequest
  | done value => simp [packedReviewerLcaNextRequest] at hrequest

/-- Every stored LCA scalar fits the modeled word on the canonical tower. -/
private theorem PackedReviewerLcaCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaCanonicalScalarFits shape state) :
    forall value, value ∈ packedReviewerLcaStateNatFields state ->
      PackedReviewerNatFits shape.size value := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  have hthree := packedReviewerTwoMul_add_three_le_cellBound shape.size
  have hcap := packedReviewerCellBound_lt_two_pow_width shape.size
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      obtain ⟨rfl, hinv, hleft, hright, -, hrank⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hrankFields := hrank.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | hrankMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact hrankFields value hrankMem
  | leftSeed invocation n leftClose rightClose rank =>
      obtain ⟨rfl, hinv, hleft, hright, -, hrank⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hrankFields := hrank.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | hrankMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact hrankFields value hrankMem
  | sameWindow invocation n leftClose rightClose seed window =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, -, hwindow⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hwindowFields := hwindow.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | hwindowMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hseed
      · exact hwindowFields value hwindowMem
  | leftWindow invocation n leftClose rightClose seed window =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, -, hwindow⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hwindowFields := hwindow.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | hwindowMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hseed
      · exact hwindowFields value hwindowMem
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, -,
        ⟨resultBound, hfringe⟩, -⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hfringeFields := hfringe.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | rfl | rfl |
        hfringeMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hseed
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hbase
      · simp only [PackedReviewerNatFits]
        omega
      · exact hfringeFields value hfringeMem
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, -,
        ⟨resultBound, hfringe⟩, -⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hfringeFields := hfringe.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | rfl | rfl |
        hfringeMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hseed
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hbase
      · simp only [PackedReviewerNatFits]
        omega
      · exact hfringeFields value hfringeMem
  | middle invocation n leftClose rightClose left interior =>
      obtain ⟨rfl, hinv, hleft, hright, hleftCand, hinterior⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hleftFields := hleftCand.scalar_fields
      have hinteriorFields := hinterior.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | hleftMem | hinteriorMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact hleftFields value hleftMem
      · exact hinteriorFields value hinteriorMem
  | rightSeed invocation n leftClose rightClose left middle rank =>
      obtain ⟨rfl, hinv, hleft, hright, hleftCand, hmiddleCand, -,
        hrank⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hleftFields := hleftCand.scalar_fields
      have hmiddleFields := hmiddleCand.scalar_fields
      have hrankFields := hrank.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | hleftMem | hmiddleMem |
        hrankMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact hleftFields value hleftMem
      · exact hmiddleFields value hmiddleMem
      · exact hrankFields value hrankMem
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hleftCand, hmiddleCand, -,
        hwindow⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hleftFields := hleftCand.scalar_fields
      have hmiddleFields := hmiddleCand.scalar_fields
      have hwindowFields := hwindow.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | hleftMem |
        hmiddleMem | hwindowMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hseed
      · exact hleftFields value hleftMem
      · exact hmiddleFields value hmiddleMem
      · exact hwindowFields value hwindowMem
  | rightFringe invocation n leftClose rightClose seed base start left
      middle fringe =>
      obtain ⟨rfl, hinv, hleft, hright, hseed, hbase, hstart, hleftCand,
        hmiddleCand, -, ⟨resultBound, hfringe⟩, -⟩ := hstate
      have hinvFields :
          forall value,
            value ∈ packedReviewerInvocationNatFields invocation ->
              PackedReviewerNatFits shape.size value := by
        simpa [packedReviewerInvocationNatFields,
          packedReviewerInvocationOperands] using hinv
      have hleftFields := hleftCand.scalar_fields
      have hmiddleFields := hmiddleCand.scalar_fields
      have hfringeFields := hfringe.scalar_fields
      intro value hmem
      simp [packedReviewerLcaStateNatFields] at hmem
      rcases hmem with hinvMem | rfl | rfl | rfl | rfl | rfl | rfl |
        hleftMem | hmiddleMem | hfringeMem
      · exact hinvFields value hinvMem
      · exact hn
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hleft
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hright
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hseed
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hbase
      · simp only [PackedReviewerNatFits]
        omega
      · exact hleftFields value hleftMem
      · exact hmiddleFields value hmiddleMem
      · exact hfringeFields value hfringeMem
  | done value =>
      intro fieldValue hmem
      cases value with
      | none =>
          simp [packedReviewerLcaStateNatFields,
            packedReviewerOptionNatFields] at hmem
      | some answer =>
          simp only [packedReviewerLcaStateNatFields,
            packedReviewerOptionNatFields, List.mem_singleton] at hmem
          subst fieldValue
          exact (hstate answer rfl).1

/-- Every request the canonical LCA tower emits has fitting operands. -/
private theorem PackedReviewerLcaCanonicalScalarFits.nextRequest_operands_fit
    {shape : CartesianShape} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaCanonicalScalarFits shape state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerLcaNextRequest state = some request) :
    PackedReviewerLogicalRequestOperandsFit shape.size request := by
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      obtain ⟨rfl, -, -, -, hrankFit, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | leftSeed invocation n leftClose rightClose rank =>
      obtain ⟨rfl, -, -, -, hrankFit, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | rightSeed invocation n leftClose rightClose left middle rank =>
      obtain ⟨rfl, -, -, -, -, -, hrankFit, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | sameWindow invocation n leftClose rightClose seed window =>
      obtain ⟨rfl, -, -, -, -, hwitness, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hwitness
        (packedReviewerBPWindowNextRequest_remaining_pos hrequest) hrequest
  | leftWindow invocation n leftClose rightClose seed window =>
      obtain ⟨rfl, -, -, -, -, hwitness, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hwitness
        (packedReviewerBPWindowNextRequest_remaining_pos hrequest) hrequest
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      obtain ⟨rfl, -, -, -, -, -, -, hwitness, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hwitness
        (packedReviewerBPWindowNextRequest_remaining_pos hrequest) hrequest
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨rfl, -, -, -, -, -, -, hwitness, -, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hwitness
        (packedReviewerFringeNextRequest_remaining_pos hrequest) hrequest
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨rfl, -, -, -, -, -, -, hwitness, -, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hwitness
        (packedReviewerFringeNextRequest_remaining_pos hrequest) hrequest
  | rightFringe invocation n leftClose rightClose seed base start left
      middle fringe =>
      obtain ⟨rfl, -, -, -, -, -, -, -, -, hwitness, -, -⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hwitness
        (packedReviewerFringeNextRequest_remaining_pos hrequest) hrequest
  | middle invocation n leftClose rightClose left interior =>
      obtain ⟨rfl, -, -, -, -, hinterior⟩ := hstate
      simp only [packedReviewerLcaNextRequest] at hrequest
      exact hinterior.nextRequest_operands_fit hrequest
  | done value => simp [packedReviewerLcaNextRequest] at hrequest

/-- The canonical LCA tower stays inside its 129-read budget. -/
private theorem PackedReviewerLcaCanonicalScalarFits.remaining_le_oneTwentyNine
    {shape : CartesianShape} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaCanonicalScalarFits shape state) :
    packedReviewerLcaRemaining state <= 129 := by
  cases state with
  | sameSeed invocation n leftClose rightClose rank =>
      obtain ⟨-, -, -, -, -, hrank⟩ := hstate
      have hbound := hrank.remaining_le_eleven
      simp only [packedReviewerLcaRemaining]
      omega
  | leftSeed invocation n leftClose rightClose rank =>
      obtain ⟨-, -, -, -, -, hrank⟩ := hstate
      have hbound := hrank.remaining_le_eleven
      simp only [packedReviewerLcaRemaining]
      omega
  | rightSeed invocation n leftClose rightClose left middle rank =>
      obtain ⟨-, -, -, -, -, -, -, hrank⟩ := hstate
      have hbound := hrank.remaining_le_eleven
      simp only [packedReviewerLcaRemaining]
      omega
  | sameWindow invocation n leftClose rightClose seed window =>
      have hwin : packedReviewerBPWindowRemaining window <= 4 := by
        cases window with
        | read invocation2 n2 blockSize close next wordsRev =>
            simp only [packedReviewerBPWindowRemaining]
            omega
        | done bits => simp [packedReviewerBPWindowRemaining]
      simp only [packedReviewerLcaRemaining]
      omega
  | leftWindow invocation n leftClose rightClose seed window =>
      have hwin : packedReviewerBPWindowRemaining window <= 4 := by
        cases window with
        | read invocation2 n2 blockSize close next wordsRev =>
            simp only [packedReviewerBPWindowRemaining]
            omega
        | done bits => simp [packedReviewerBPWindowRemaining]
      simp only [packedReviewerLcaRemaining]
      omega
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      have hwin : packedReviewerBPWindowRemaining window <= 4 := by
        cases window with
        | read invocation2 n2 blockSize close next wordsRev =>
            simp only [packedReviewerBPWindowRemaining]
            omega
        | done bits => simp [packedReviewerBPWindowRemaining]
      simp only [packedReviewerLcaRemaining]
      omega
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨-, -, -, -, -, -, -, -, ⟨resultBound, hfringe⟩, -⟩ := hstate
      have hfr : packedReviewerFringeRemaining fringe <= 33 := by
        cases fringe with
        | chunk invocation2 n2 window2 relLo relHi j remaining foldState =>
            rcases foldState with ⟨acc, candidate⟩
            obtain ⟨-, -, -, -, hcounters, -, -, -, -⟩ := hfringe
            simp only [packedReviewerFringeRemaining]
            omega
        | done result => simp [packedReviewerFringeRemaining]
      simp only [packedReviewerLcaRemaining]
      omega
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      obtain ⟨-, -, -, -, -, -, -, -, ⟨resultBound, hfringe⟩, -⟩ := hstate
      have hfr : packedReviewerFringeRemaining fringe <= 33 := by
        cases fringe with
        | chunk invocation2 n2 window2 relLo relHi j remaining foldState =>
            rcases foldState with ⟨acc, candidate⟩
            obtain ⟨-, -, -, -, hcounters, -, -, -, -⟩ := hfringe
            simp only [packedReviewerFringeRemaining]
            omega
        | done result => simp [packedReviewerFringeRemaining]
      simp only [packedReviewerLcaRemaining]
      omega
  | rightFringe invocation n leftClose rightClose seed base start left
      middle fringe =>
      obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨resultBound, hfringe⟩,
        -⟩ := hstate
      have hfr : packedReviewerFringeRemaining fringe <= 33 := by
        cases fringe with
        | chunk invocation2 n2 window2 relLo relHi j remaining foldState =>
            rcases foldState with ⟨acc, candidate⟩
            obtain ⟨-, -, -, -, hcounters, -, -, -, -⟩ := hfringe
            simp only [packedReviewerFringeRemaining]
            omega
        | done result => simp [packedReviewerFringeRemaining]
      simp only [packedReviewerLcaRemaining]
      omega
  | middle invocation n leftClose rightClose left interior =>
      obtain ⟨-, -, -, -, -, hinterior⟩ := hstate
      have hbound := hinterior.remaining_le_forty
      simp only [packedReviewerLcaRemaining]
      omega
  | done value => simp [packedReviewerLcaRemaining]

/-- A successful LCA result is a fitting close with `+1` slack for the final
rank position. -/
private theorem PackedReviewerLcaCanonicalScalarFits.result_fits
    {shape : CartesianShape} {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaCanonicalScalarFits shape state)
    {value : Option Nat}
    (hresult : packedReviewerLcaResult state = some value) :
    forall answer, value = some answer ->
      PackedReviewerNatFits shape.size answer ∧
        PackedReviewerNatFits shape.size (answer + 1) := by
  cases state with
  | done stored =>
      have heq : stored = value := by
        simpa [packedReviewerLcaResult] using Option.some.inj hresult
      subst value
      exact hstate
  | sameSeed invocation n leftClose rightClose rank =>
      simp [packedReviewerLcaResult] at hresult
  | sameWindow invocation n leftClose rightClose seed window =>
      simp [packedReviewerLcaResult] at hresult
  | sameFringe invocation n leftClose rightClose seed base start fringe =>
      simp [packedReviewerLcaResult] at hresult
  | leftSeed invocation n leftClose rightClose rank =>
      simp [packedReviewerLcaResult] at hresult
  | leftWindow invocation n leftClose rightClose seed window =>
      simp [packedReviewerLcaResult] at hresult
  | leftFringe invocation n leftClose rightClose seed base start fringe =>
      simp [packedReviewerLcaResult] at hresult
  | middle invocation n leftClose rightClose left interior =>
      simp [packedReviewerLcaResult] at hresult
  | rightSeed invocation n leftClose rightClose left middle rank =>
      simp [packedReviewerLcaResult] at hresult
  | rightWindow invocation n leftClose rightClose seed left middle window =>
      simp [packedReviewerLcaResult] at hresult
  | rightFringe invocation n leftClose rightClose seed base start left
      middle fringe =>
      simp [packedReviewerLcaResult] at hresult

/-- The select tower invariant supplies request-width prefixes of any fuel. -/
private theorem packedReviewerSelect_requests_fitFrom
    (shape : CartesianShape) {state : PackedReviewerSelectState}
    (hstate : PackedReviewerSelectCanonicalScalarFits shape state)
    (fuel : Nat) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerSelectNextRequest packedReviewerSelectConsumeReply fuel
      state :=
  PackedReviewerRequestsFitFrom.of_invariant shape.size
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    packedReviewerSelectNextRequest packedReviewerSelectConsumeReply
    (PackedReviewerSelectCanonicalScalarFits shape)
    (fun _ _ hstate' hrequest => hstate'.nextRequest_operands_fit hrequest)
    (fun _ _ hstate' hrequest => hstate'.consume hrequest) fuel state hstate

/-- The LCA tower invariant supplies request-width prefixes of any fuel. -/
private theorem packedReviewerLca_requests_fitFrom
    (shape : CartesianShape) {state : PackedReviewerLcaState}
    (hstate : PackedReviewerLcaCanonicalScalarFits shape state)
    (fuel : Nat) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerLcaNextRequest packedReviewerLcaConsumeReply fuel
      state :=
  PackedReviewerRequestsFitFrom.of_invariant shape.size
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    packedReviewerLcaNextRequest packedReviewerLcaConsumeReply
    (PackedReviewerLcaCanonicalScalarFits shape)
    (fun _ _ hstate' hrequest => hstate'.nextRequest_operands_fit hrequest)
    (fun _ _ hstate' hrequest => hstate'.consume hrequest) fuel state hstate

/-! ## Canonical whole tower

The five-arm whole coupling ties the select tower and the close/LCA tower to
the four instruction occurrences of the public whole-query program.  Every
arm carries the ambient-size phase equality and the endpoint validity that
the next fresh component start needs, and hands the in-flight component to
its own canonical invariant.  The done arm carries exactly the width fact
the physical controller's done phase stores.
-/

private def PackedReviewerWholeCanonicalScalarFits
    (shape : CartesianShape) : PackedReviewerWholeState -> Prop
  | .leftSelect n left right select =>
      n = shape.size ∧
        left < right ∧
        right <= shape.size ∧
        PackedReviewerSelectCanonicalScalarFits shape select
  | .rightSelect n left right leftClose select =>
      n = shape.size ∧
        left < right ∧
        right <= shape.size ∧
        (forall value, leftClose = some value ->
          PackedReviewerNatFits shape.size value ∧
            value <= 2 * shape.size + 1) ∧
        PackedReviewerSelectCanonicalScalarFits shape select
  | .lcaClose n left right leftClose rightClose lca =>
      n = shape.size ∧
        left < right ∧
        right <= shape.size ∧
        leftClose <= 2 * shape.size + 1 ∧
        rightClose <= 2 * shape.size + 1 ∧
        PackedReviewerLcaCanonicalScalarFits shape lca
  | .finalRank n left right answerClose rank =>
      n = shape.size ∧
        left < right ∧
        right <= shape.size ∧
        PackedReviewerNatFits shape.size answerClose ∧
        PackedReviewerRequestsFitFrom shape.size
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          packedReviewerRankNextRequest packedReviewerRankConsumeReply
          (packedReviewerRankRemaining rank) rank ∧
        PackedReviewerRankCanonicalScalarFits shape
          (packedReviewerRankQueryPos .close shape.size (answerClose + 1))
          rank
  | .done value =>
      forall index, value = some index ->
        PackedReviewerNatFits shape.size index

/-- The canonical whole start satisfies the tower invariant. -/
private theorem packedReviewerWholeStart_canonicalScalarFits
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right ∧ right <= shape.size) :
    PackedReviewerWholeCanonicalScalarFits shape
      (packedReviewerWholeStart shape.size left right) := by
  unfold packedReviewerWholeStart
  exact ⟨rfl, hvalid.1, hvalid.2,
    packedReviewerSelectStart_canonicalScalarFits shape
      { instruction := .leftSelect, argument := left } left
      (packedReviewerSelectInvocation_operands_fit shape .leftSelect left
        (by omega))
      (by omega)⟩

/-- Completing the left select launches the fresh right select in envelope. -/
private theorem packedReviewerWholeAfterLeftSelect_fits
    (shape : CartesianShape) (left right : Nat) (leftClose : Option Nat)
    (hleftRight : left < right) (hrightLe : right <= shape.size)
    (hleftClose :
      forall value, leftClose = some value ->
        PackedReviewerNatFits shape.size value ∧
          value <= 2 * shape.size + 1) :
    PackedReviewerWholeCanonicalScalarFits shape
      (packedReviewerWholeAfterLeftSelect shape.size left right leftClose) := by
  unfold packedReviewerWholeAfterLeftSelect
  exact ⟨rfl, hleftRight, hrightLe, hleftClose,
    packedReviewerSelectStart_canonicalScalarFits shape
      { instruction := .rightSelect, argument := right - 1 } (right - 1)
      (packedReviewerSelectInvocation_operands_fit shape .rightSelect
        (right - 1) (by omega))
      (by omega)⟩

/-- Two decoded closes launch the LCA machine inside the string envelope. -/
private theorem packedReviewerWholeAfterRightSelect_fits
    (shape : CartesianShape) (left right : Nat)
    (leftClose rightClose : Option Nat)
    (hleftRight : left < right) (hrightLe : right <= shape.size)
    (hleftClose :
      forall value, leftClose = some value ->
        PackedReviewerNatFits shape.size value ∧
          value <= 2 * shape.size + 1)
    (hrightClose :
      forall value, rightClose = some value ->
        PackedReviewerNatFits shape.size value ∧
          value <= 2 * shape.size + 1) :
    PackedReviewerWholeCanonicalScalarFits shape
      (packedReviewerWholeAfterRightSelect shape.size left right leftClose
        rightClose) := by
  cases leftClose with
  | none =>
      intro index hindex
      simp at hindex
  | some leftValue =>
      cases rightClose with
      | none =>
          intro index hindex
          simp at hindex
      | some rightValue =>
          obtain ⟨hlcFits, hlcLe⟩ := hleftClose leftValue rfl
          obtain ⟨hrcFits, hrcLe⟩ := hrightClose rightValue rfl
          simp only [packedReviewerWholeAfterRightSelect]
          exact ⟨rfl, hleftRight, hrightLe, hlcLe, hrcLe,
            packedReviewerLcaStart_fits shape leftValue rightValue hlcLe
              hrcLe⟩

/-- A decoded LCA answer launches the final rank at the next position. -/
private theorem packedReviewerWholeAfterLca_fits
    (shape : CartesianShape) (left right : Nat) (answerClose : Option Nat)
    (hleftRight : left < right) (hrightLe : right <= shape.size)
    (hanswer :
      forall answer, answerClose = some answer ->
        PackedReviewerNatFits shape.size answer ∧
          PackedReviewerNatFits shape.size (answer + 1)) :
    PackedReviewerWholeCanonicalScalarFits shape
      (packedReviewerWholeAfterLca shape.size left right answerClose) := by
  cases answerClose with
  | none =>
      intro index hindex
      simp at hindex
  | some answer =>
      obtain ⟨hanswerFits, hanswerPlusFits⟩ := hanswer answer rfl
      have hinvFit :
          forall operand,
            operand ∈ packedReviewerInvocationOperands
              { instruction := .finalRank, argument := answer + 1 } ->
              PackedReviewerNatFits shape.size operand := by
        apply packedReviewerInvocationOperands_fit
        · exact hanswerPlusFits
        · exact Nat.two_pow_pos _
      simp only [packedReviewerWholeAfterLca]
      refine ⟨rfl, hleftRight, hrightLe, hanswerFits, ?_, ?_⟩
      · have hwitness :=
          packedReviewerRankStart_requests_fit shape
            { instruction := .finalRank, argument := answer + 1 } .close
            (answer + 1) hinvFit
        simpa [packedReviewerRankRemaining] using hwitness
      · exact packedReviewerRankStart_canonicalScalarFits shape
          { instruction := .finalRank, argument := answer + 1 } .close
          (answer + 1) hinvFit hanswerPlusFits

/-- Every stored whole scalar fits the modeled word on the canonical tower. -/
private theorem PackedReviewerWholeCanonicalScalarFits.scalar_fields
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeCanonicalScalarFits shape state) :
    forall value, value ∈ packedReviewerWholeStateNatFields state ->
      PackedReviewerNatFits shape.size value := by
  have hn := packedReviewerInputSize_lt_two_pow_cellWidth shape.size
  cases state with
  | leftSelect n left right select =>
      obtain ⟨rfl, hleftRight, hrightLe, hselect⟩ := hstate
      have hselectFields := hselect.scalar_fields
      intro value hmem
      simp [packedReviewerWholeStateNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | hselectMem
      · exact hn
      · omega
      · omega
      · exact hselectFields value hselectMem
  | rightSelect n left right leftClose select =>
      obtain ⟨rfl, hleftRight, hrightLe, hleftClose, hselect⟩ := hstate
      have hselectFields := hselect.scalar_fields
      intro value hmem
      simp [packedReviewerWholeStateNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | hoptMem | hselectMem
      · exact hn
      · omega
      · omega
      · cases leftClose with
        | none =>
            simp [packedReviewerOptionNatFields] at hoptMem
        | some stored =>
            simp only [packedReviewerOptionNatFields,
              List.mem_singleton] at hoptMem
            subst hoptMem
            exact (hleftClose value rfl).1
      · exact hselectFields value hselectMem
  | lcaClose n left right leftClose rightClose lca =>
      obtain ⟨rfl, hleftRight, hrightLe, hlcLe, hrcLe, hlca⟩ := hstate
      have hlcaFields := hlca.scalar_fields
      intro value hmem
      simp [packedReviewerWholeStateNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | hlcaMem
      · exact hn
      · omega
      · omega
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hlcLe
      · exact packedReviewerNatFits_of_le_two_mul_add_one shape.size _ hrcLe
      · exact hlcaFields value hlcaMem
  | finalRank n left right answerClose rank =>
      obtain ⟨rfl, hleftRight, hrightLe, hanswerFits, hrankFit,
        hrank⟩ := hstate
      have hrankFields := hrank.scalar_fields
      intro value hmem
      simp [packedReviewerWholeStateNatFields] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | hrankMem
      · exact hn
      · omega
      · omega
      · exact hanswerFits
      · exact hrankFields value hrankMem
  | done value =>
      intro fieldValue hmem
      cases value with
      | none =>
          simp [packedReviewerWholeStateNatFields,
            packedReviewerOptionNatFields] at hmem
      | some index =>
          simp only [packedReviewerWholeStateNatFields,
            packedReviewerOptionNatFields, List.mem_singleton] at hmem
          subst fieldValue
          exact hstate index rfl

/-- Every request the canonical whole tower emits has fitting operands. -/
private theorem PackedReviewerWholeCanonicalScalarFits.nextRequest_operands_fit
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeCanonicalScalarFits shape state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerWholeNextRequest state = some request) :
    PackedReviewerLogicalRequestOperandsFit shape.size request := by
  cases state with
  | leftSelect n left right select =>
      obtain ⟨rfl, -, -, hselect⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      exact hselect.nextRequest_operands_fit hrequest
  | rightSelect n left right leftClose select =>
      obtain ⟨rfl, -, -, -, hselect⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      exact hselect.nextRequest_operands_fit hrequest
  | lcaClose n left right leftClose rightClose lca =>
      obtain ⟨rfl, -, -, -, -, hlca⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      exact hlca.nextRequest_operands_fit hrequest
  | finalRank n left right answerClose rank =>
      obtain ⟨rfl, -, -, -, hrankFit, -⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      exact packedReviewerRequestsFitFrom_head_operands_fit hrankFit
        (packedReviewerRankNextRequest_remaining_pos hrequest) hrequest
  | done value =>
      simp [packedReviewerWholeNextRequest] at hrequest

/-- The canonical whole tower stays inside its 210-read budget. -/
private theorem
    PackedReviewerWholeCanonicalScalarFits.remaining_le_twoHundredTen
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeCanonicalScalarFits shape state) :
    packedReviewerWholeRemaining state <= 210 := by
  cases state with
  | leftSelect n left right select =>
      obtain ⟨-, -, -, hselect⟩ := hstate
      have hbound := hselect.remaining_le_thirtyFive
      simp only [packedReviewerWholeRemaining]
      omega
  | rightSelect n left right leftClose select =>
      obtain ⟨-, -, -, -, hselect⟩ := hstate
      have hbound := hselect.remaining_le_thirtyFive
      simp only [packedReviewerWholeRemaining]
      omega
  | lcaClose n left right leftClose rightClose lca =>
      obtain ⟨-, -, -, -, -, hlca⟩ := hstate
      have hbound := hlca.remaining_le_oneTwentyNine
      simp only [packedReviewerWholeRemaining]
      omega
  | finalRank n left right answerClose rank =>
      obtain ⟨-, -, -, -, -, hrank⟩ := hstate
      have hbound := hrank.remaining_le_eleven
      simp only [packedReviewerWholeRemaining]
      omega
  | done value => simp [packedReviewerWholeRemaining]

/-- One canonical reply preserves the whole tower invariant. -/
private theorem PackedReviewerWholeCanonicalScalarFits.consume
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    (hstate : PackedReviewerWholeCanonicalScalarFits shape state)
    {request : PackedReviewerLogicalRequest}
    (hrequest : packedReviewerWholeNextRequest state = some request) :
    PackedReviewerWholeCanonicalScalarFits shape
      (packedReviewerWholeConsumeReply state
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          request.segment request.index)) := by
  cases state with
  | leftSelect n left right select =>
      obtain ⟨rfl, hleftRight, hrightLe, hselect⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      have hselect' := hselect.consume hrequest
      simp only [packedReviewerWholeConsumeReply]
      cases hresult :
          packedReviewerSelectResult
            (packedReviewerSelectConsumeReply select
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) with
      | none => exact ⟨rfl, hleftRight, hrightLe, hselect'⟩
      | some leftClose =>
          refine packedReviewerWholeAfterLeftSelect_fits shape left right
            leftClose hleftRight hrightLe ?_
          intro value hvalue
          subst hvalue
          exact hselect'.result_fits hresult
  | rightSelect n left right leftClose select =>
      obtain ⟨rfl, hleftRight, hrightLe, hleftClose, hselect⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      have hselect' := hselect.consume hrequest
      simp only [packedReviewerWholeConsumeReply]
      cases hresult :
          packedReviewerSelectResult
            (packedReviewerSelectConsumeReply select
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) with
      | none => exact ⟨rfl, hleftRight, hrightLe, hleftClose, hselect'⟩
      | some rightClose =>
          refine packedReviewerWholeAfterRightSelect_fits shape left right
            leftClose rightClose hleftRight hrightLe hleftClose ?_
          intro value hvalue
          subst hvalue
          exact hselect'.result_fits hresult
  | lcaClose n left right leftClose rightClose lca =>
      obtain ⟨rfl, hleftRight, hrightLe, hlcLe, hrcLe, hlca⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      have hlca' := hlca.consume hrequest
      simp only [packedReviewerWholeConsumeReply]
      cases hresult :
          packedReviewerLcaResult
            (packedReviewerLcaConsumeReply lca
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) with
      | none => exact ⟨rfl, hleftRight, hrightLe, hlcLe, hrcLe, hlca'⟩
      | some answerClose =>
          exact packedReviewerWholeAfterLca_fits shape left right answerClose
            hleftRight hrightLe (hlca'.result_fits hresult)
  | finalRank n left right answerClose rank =>
      obtain ⟨rfl, hleftRight, hrightLe, hanswerFits, hrankFit,
        hrank⟩ := hstate
      simp only [packedReviewerWholeNextRequest] at hrequest
      have hrank' := hrank.consume hrequest
      have hdescent :=
        packedReviewerRankRemaining_consume_le rank
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index) request hrequest
      have hfit' :=
        packedReviewerRequestsFitFrom_consume_witness hrankFit hrequest
          (by omega)
      simp only [packedReviewerWholeConsumeReply]
      cases hresult :
          packedReviewerRankResult
            (packedReviewerRankConsumeReply rank
              ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
                request.segment request.index)) with
      | none =>
          exact ⟨rfl, hleftRight, hrightLe, hanswerFits, hfit', hrank'⟩
      | some closeRank =>
          have hvalue := hrank'.result_fits hresult
          intro index hindex
          have heq : closeRank - 1 = index := Option.some.inj hindex
          subst heq
          have hcapacity := hvalue.1
          simp only [PackedReviewerNatFits] at hcapacity ⊢
          omega
  | done value =>
      simp [packedReviewerWholeNextRequest] at hrequest

/-- A completed canonical whole state exposes a fitting result scalar. -/
private theorem PackedReviewerWholeCanonicalScalarFits.result_fits
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    {value : Option Nat}
    (hstate : PackedReviewerWholeCanonicalScalarFits shape state)
    (hresult : packedReviewerWholeResult state = some value) :
    forall index, value = some index ->
      PackedReviewerNatFits shape.size index := by
  cases state with
  | done stored =>
      have heq : stored = value := by
        simpa [packedReviewerWholeResult] using hresult
      subst value
      exact hstate
  | leftSelect n left right select =>
      simp [packedReviewerWholeResult] at hresult
  | rightSelect n left right leftClose select =>
      simp [packedReviewerWholeResult] at hresult
  | lcaClose n left right leftClose rightClose lca =>
      simp [packedReviewerWholeResult] at hresult
  | finalRank n left right answerClose rank =>
      simp [packedReviewerWholeResult] at hresult

/-- The invariant transports to the request-width prefix at any budget. -/
private theorem packedReviewerWholeStart_requests_fit
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right ∧ right <= shape.size) :
    PackedReviewerRequestsFitFrom shape.size
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
      (packedReviewerWholeRemaining
        (packedReviewerWholeStart shape.size left right))
      (packedReviewerWholeStart shape.size left right) :=
  PackedReviewerRequestsFitFrom.of_invariant shape.size
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
    (PackedReviewerWholeCanonicalScalarFits shape)
    (fun _ _ hstate hrequest => hstate.nextRequest_operands_fit hrequest)
    (fun _ _ hstate hrequest => hstate.consume hrequest)
    (packedReviewerWholeRemaining
      (packedReviewerWholeStart shape.size left right))
    (packedReviewerWholeStart shape.size left right)
    (packedReviewerWholeStart_canonicalScalarFits shape left right hvalid)

/-- The constructor-exhaustive producer for the canonical whole start. -/
private theorem packedReviewerWholeStart_operational_fits
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right ∧ right <= shape.size) :
    PackedReviewerWholeOperationalFits shape
      (packedReviewerWholeStart shape.size left right) :=
  { size_eq := by simp [packedReviewerWholeStart]
    scalar_fields :=
      (packedReviewerWholeStart_canonicalScalarFits shape left right
        hvalid).scalar_fields
    storage_fits := packedReviewerWholeStart_storage_fits shape.size left right
    continuation_shape :=
      packedReviewerWholeStart_shape_safe shape.size left right
    remaining_le := by
      have hbudget :=
        packedReviewerWholeStart_remaining_eq_two_ten shape left right hvalid
      omega
    requests_fit := packedReviewerWholeStart_requests_fit shape left right
      hvalid }

/--
A finished whole machine feeds the physical done phase exactly through its
option field list, so the controller's done-value width obligation is a
projection of the coupled scalar invariant — no separate result envelope.
-/
private theorem PackedReviewerWholeOperationalFits.done_value_fits
    {shape : CartesianShape} {value : Option Nat}
    (hfit : PackedReviewerWholeOperationalFits shape (.done value)) :
    forall index, value = some index ->
      PackedReviewerNatFits shape.size index := by
  intro index hindex
  subst hindex
  exact hfit.scalar_fields index
    (by simp [packedReviewerWholeStateNatFields,
      packedReviewerOptionNatFields])

/-- Every retained logical operand of the 210-fuel canonical drive fits. -/
theorem packedReviewerDriveLogical_210_request_operands_fit
    (shape : CartesianShape) (left right : Nat)
    (hleft : left < right) (hright : right <= shape.size) :
    forall event,
      event ∈
          (packedReviewerDriveLogical
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) 210
            (packedReviewerWholeStart shape.size left right)).trace ->
        PackedReviewerLogicalRequestOperandsFit shape.size event.request := by
  intro event hmem
  exact
    packedReviewerDriveLogical_210_request_operands_fit_of_start_operational_fits
      shape left right ⟨hleft, hright⟩
      (packedReviewerWholeStart_operational_fits shape left right
        ⟨hleft, hright⟩)
      hmem
/-! ## Physically reachable controller states

The physical chain threads two facts through every canonical transition: the
committed exact-plan invariant, and — for parked whole-query probes — the
whole-level canonical coupling that regenerates the operational witness after
each logical consume.  The coupling rides beside the committed invariant as a
conjunction, so no committed declaration is modified.  Successor operational
witnesses are built field-wise from the coupling; the descent-carrying
`PackedReviewerWholeOperationalFits.consume` is deliberately unused.
-/

/-- The whole-query canonical coupling retained beside a parked physical probe. -/
private def packedReviewerControllerWholeCoupling
    (shape : CartesianShape) : PackedReviewerControllerState -> Prop
  | .wholeProbe _ _ _ _ _ _ whole _ _ =>
      PackedReviewerWholeCanonicalScalarFits shape whole
  | _ => True

/--
The committed exact physical invariant together with the whole coupling.  The
first component is exactly the frozen `PackedReviewerCanonicalControllerInvariant`;
the second is `True` outside parked whole-query probes.
-/
private def PackedReviewerCanonicalControllerCoupledInvariant
    (shape : CartesianShape) (left right : Nat)
    (state : PackedReviewerControllerState) : Prop :=
  PackedReviewerCanonicalControllerInvariant shape left right state /\
    packedReviewerControllerWholeCoupling shape state

/--
Field-wise successor construction for the coupled whole witness.  Scalars and
the phase equality come from the advanced coupling, storage and continuation
shape from the reply-generic preservation lemmas, the budget literal from the
coupling's arm bounds, and the request prefix is regenerated at the successor's
own structural budget by the descent-free invariant transport.
-/
private theorem packedReviewerWholeCanonicalConsume_operational_fits
    {shape : CartesianShape} {state : PackedReviewerWholeState}
    {request : PackedReviewerLogicalRequest}
    (hfit : PackedReviewerWholeOperationalFits shape state)
    (hcanonical : PackedReviewerWholeCanonicalScalarFits shape state)
    (hrequest : packedReviewerWholeNextRequest state = some request) :
    PackedReviewerWholeOperationalFits shape
        (packedReviewerWholeConsumeReply state
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) /\
      PackedReviewerWholeCanonicalScalarFits shape
        (packedReviewerWholeConsumeReply state
          ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
            request.segment request.index)) := by
  have hcanonical' :=
    PackedReviewerWholeCanonicalScalarFits.consume hcanonical hrequest
  refine
    ⟨{ size_eq := by
         revert hcanonical'
         generalize packedReviewerWholeConsumeReply state
           ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
             request.segment request.index) = next
         intro hcanonical'
         cases next with
         | leftSelect n left right select => exact hcanonical'.1
         | rightSelect n left right leftClose select => exact hcanonical'.1
         | lcaClose n left right leftClose rightClose lca =>
             exact hcanonical'.1
         | finalRank n left right answerClose rank => exact hcanonical'.1
         | done value => trivial
       scalar_fields :=
         PackedReviewerWholeCanonicalScalarFits.scalar_fields hcanonical'
       storage_fits := ?_
       continuation_shape :=
         packedReviewerWholeConsumeReply_shape_safe state
           ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
             request.segment request.index)
           hfit.continuation_shape
       remaining_le :=
         PackedReviewerWholeCanonicalScalarFits.remaining_le_twoHundredTen
           hcanonical'
       requests_fit :=
         PackedReviewerRequestsFitFrom.of_invariant shape.size
           (concreteBPNativeSuccinctRMQGlobalReadStore shape)
           packedReviewerWholeNextRequest packedReviewerWholeConsumeReply
           (PackedReviewerWholeCanonicalScalarFits shape)
           (fun st req hst hreq =>
             PackedReviewerWholeCanonicalScalarFits.nextRequest_operands_fit
               hst hreq)
           (fun st req hst hreq =>
             PackedReviewerWholeCanonicalScalarFits.consume hst hreq)
           _ _ hcanonical' },
     hcanonical'⟩
  apply packedReviewerWholeConsumeReply_storage_fits shape state
    ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      request.segment request.index) request hrequest hfit.storage_fits
  intro word hword
  exact packedReviewerGlobalReadStore_word_fits shape request word hword

/-- A terminal whole value is one of its own retained scalar fields. -/
private theorem packedReviewerWholeDone_coupledInvariant
    {shape : CartesianShape} {left right : Nat} {value : Option Nat}
    (hwhole : PackedReviewerWholeOperationalFits shape (.done value)) :
    PackedReviewerCanonicalControllerCoupledInvariant shape left right
      (.done value) := by
  refine ⟨PackedReviewerCanonicalControllerInvariant.done value ?_, trivial⟩
  intro index hindex
  subst hindex
  exact hwhole.scalar_fields index (by
    simp [packedReviewerWholeStateNatFields, packedReviewerOptionNatFields])

/-- Whole normalization lands inside the coupled invariant. -/
private theorem packedReviewerNormalizeWhole_invariant
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right /\ right <= shape.size) :
    forall fuel, fuel <= 210 ->
      forall whole : PackedReviewerWholeState,
        PackedReviewerWholeOperationalFits shape whole ->
        PackedReviewerWholeCanonicalScalarFits shape whole ->
        PackedReviewerCanonicalControllerCoupledInvariant shape left right
          (packedReviewerNormalizeWhole fuel shape.size left right
            (longCount shape) (packedReviewerSparseCount shape) whole) := by
  intro fuel
  induction fuel with
  | zero =>
      intro hfuel whole hwhole hcanonical
      cases hresult : packedReviewerWholeResult whole with
      | some value =>
          cases whole with
          | done doneValue =>
              simp only [packedReviewerNormalizeWhole,
                packedReviewerWholeResult]
              exact packedReviewerWholeDone_coupledInvariant hwhole
          | leftSelect n stateLeft stateRight select =>
              simp [packedReviewerWholeResult] at hresult
          | rightSelect n stateLeft stateRight leftClose select =>
              simp [packedReviewerWholeResult] at hresult
          | lcaClose n stateLeft stateRight leftClose rightClose lca =>
              simp [packedReviewerWholeResult] at hresult
          | finalRank n stateLeft stateRight answerClose rank =>
              simp [packedReviewerWholeResult] at hresult
      | none =>
          simp only [packedReviewerNormalizeWhole, hresult]
          exact ⟨PackedReviewerCanonicalControllerInvariant.failed, trivial⟩
  | succ fuel ih =>
      intro hfuel whole hwhole hcanonical
      cases hresult : packedReviewerWholeResult whole with
      | some value =>
          cases whole with
          | done doneValue =>
              simp only [packedReviewerNormalizeWhole,
                packedReviewerWholeResult]
              exact packedReviewerWholeDone_coupledInvariant hwhole
          | leftSelect n stateLeft stateRight select =>
              simp [packedReviewerWholeResult] at hresult
          | rightSelect n stateLeft stateRight leftClose select =>
              simp [packedReviewerWholeResult] at hresult
          | lcaClose n stateLeft stateRight leftClose rightClose lca =>
              simp [packedReviewerWholeResult] at hresult
          | finalRank n stateLeft stateRight answerClose rank =>
              simp [packedReviewerWholeResult] at hresult
      | none =>
          cases hrequest : packedReviewerWholeNextRequest whole with
          | none =>
              simp only [packedReviewerNormalizeWhole, hresult, hrequest]
              exact ⟨PackedReviewerCanonicalControllerInvariant.failed,
                trivial⟩
          | some request =>
              cases hplan :
                  packedReviewerLogicalPlan shape.size (longCount shape)
                    (packedReviewerSparseCount shape) request with
              | nil =>
                  have hfetch :
                      packedFetch (packedReviewerMemory shape)
                          (packedReviewerLogicalPlan shape.size
                            (longCount shape)
                            (packedReviewerSparseCount shape) request) =
                        some [] := by
                    rw [hplan]
                    simp [packedFetch]
                  have hdecode :=
                    packedReviewerLogicalDecode_eq_globalReadStore_of_fetch
                      shape request [] hfetch
                  have hstep :=
                    packedReviewerWholeCanonicalConsume_operational_fits
                      hwhole hcanonical hrequest
                  simp only [packedReviewerNormalizeWhole, hresult, hrequest,
                    hplan]
                  rw [hdecode]
                  exact ih (by omega) _ hstep.1 hstep.2
              | cons address tail =>
                  simp only [packedReviewerNormalizeWhole, hresult, hrequest,
                    hplan]
                  refine
                    ⟨PackedReviewerCanonicalControllerInvariant.wholeProbe
                      hvalid fuel (by omega) whole hwhole request hrequest
                      0 []
                      (packedReviewerProbePrefix_zero
                        (packedReviewerMemory shape)
                        (packedReviewerLogicalPlan shape.size
                          (longCount shape)
                          (packedReviewerSparseCount shape) request))
                      address tail hplan, ?_⟩
                  show PackedReviewerWholeCanonicalScalarFits shape whole
                  exact hcanonical

/-- K1 prelude normalization lands inside the coupled invariant. -/
private theorem packedReviewerNormalizePrelude_invariant
    (shape : CartesianShape) (left right : Nat)
    (hvalid : left < right /\ right <= shape.size)
    (replies : PackedReviewerCanonicalPreludeReplies shape) :
    forall fuel (prelude : PackedReviewerSparsePreludeState),
      PackedReviewerCanonicalPreludeState shape replies prelude ->
      PackedReviewerCanonicalControllerCoupledInvariant shape left right
        (packedReviewerNormalizePrelude fuel shape.size left right
          (longCount shape) prelude) := by
  intro fuel
  induction fuel with
  | zero =>
      intro prelude hprelude
      cases hresult : packedReviewerSparsePreludeResult prelude with
      | some sparseCount =>
          have hsparse := hprelude.result_eq hresult
          simp only [packedReviewerNormalizePrelude, hresult, hsparse]
          exact packedReviewerNormalizeWhole_invariant shape left right hvalid
            210 (by omega) (packedReviewerWholeStart shape.size left right)
            (packedReviewerWholeStart_operational_fits shape left right hvalid)
            (packedReviewerWholeStart_canonicalScalarFits shape left right
              hvalid)
      | none =>
          simp only [packedReviewerNormalizePrelude, hresult]
          exact ⟨PackedReviewerCanonicalControllerInvariant.failed, trivial⟩
  | succ fuel ih =>
      intro prelude hprelude
      cases hresult : packedReviewerSparsePreludeResult prelude with
      | some sparseCount =>
          have hsparse := hprelude.result_eq hresult
          simp only [packedReviewerNormalizePrelude, hresult, hsparse]
          exact packedReviewerNormalizeWhole_invariant shape left right hvalid
            210 (by omega) (packedReviewerWholeStart shape.size left right)
            (packedReviewerWholeStart_operational_fits shape left right hvalid)
            (packedReviewerWholeStart_canonicalScalarFits shape left right
              hvalid)
      | none =>
          cases hpreludeRequest :
              packedReviewerSparsePreludeNextRequest prelude with
          | none =>
              cases hprelude with
              | awaitSuper =>
                  simp [packedReviewerSparsePreludeNextRequest]
                    at hpreludeRequest
              | awaitBlock =>
                  simp [packedReviewerSparsePreludeNextRequest]
                    at hpreludeRequest
              | awaitFlag =>
                  simp [packedReviewerSparsePreludeNextRequest]
                    at hpreludeRequest
              | done =>
                  simp [packedReviewerSparsePreludeResult] at hresult
          | some preludeRequest =>
              obtain ⟨word, hread⟩ :=
                hprelude.request_read hpreludeRequest
              have hplanEq :=
                packedReviewerCurrentPreludePlan_eq_requestPlan_of_read
                  shape.size (longCount shape) (packedReviewerMemory shape)
                  prelude preludeRequest word hpreludeRequest hread
              cases hplan :
                  packedReviewerCurrentPreludePlan shape.size
                    (longCount shape) prelude with
              | nil =>
                  have hfetch :
                      packedFetch (packedReviewerMemory shape)
                          (packedReviewerSparsePreludeRequestPlan shape.size
                            (longCount shape) preludeRequest) = some [] := by
                    rw [← hplanEq, hplan]
                    simp [packedFetch]
                  have hdecode :=
                    packedReviewerDecodePreludeReplies_eq_of_request_read
                      shape.size (longCount shape)
                      (packedReviewerMemory shape) prelude preludeRequest []
                      word hpreludeRequest hfetch hread
                  simp only [packedReviewerNormalizePrelude, hresult, hplan,
                    hdecode]
                  exact ih _ (hprelude.consume hpreludeRequest hread)
              | cons address tail =>
                  simp only [packedReviewerNormalizePrelude, hresult, hplan]
                  exact
                    ⟨PackedReviewerCanonicalControllerInvariant.preludeProbe
                      hvalid replies prelude hprelude preludeRequest word
                      hpreludeRequest hread 0 []
                      (packedReviewerProbePrefix_zero
                        (packedReviewerMemory shape)
                        (packedReviewerCurrentPreludePlan shape.size
                          (longCount shape) prelude))
                      address tail hplan, trivial⟩

/--
One actual canonical-memory reply preserves the coupled invariant.  Header
decodes the exact header cell; parked probes either advance their exact plan
prefix or complete it, hand the completed fetch to the exact logical decode,
and re-enter the corresponding normalization.
-/
private theorem PackedReviewerCanonicalControllerCoupledInvariant.consume
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerControllerState}
    (hstate :
      PackedReviewerCanonicalControllerCoupledInvariant shape left right
        state)
    {request : PackedReviewerPhysicalRequest}
    (hrequest : packedReviewerNextRequest state = some request) :
    PackedReviewerCanonicalControllerCoupledInvariant shape left right
      (packedReviewerConsumeReply state
        ((packedReviewerMemory shape)[request.address]?)) := by
  obtain ⟨hinvariant, hcoupling⟩ := hstate
  cases hinvariant with
  | header hvalid =>
      have hrequestEq :
          request =
            { origin := .header, address := 0, ordinal := 0,
              cellCount := 1 } := by
        simpa [packedReviewerNextRequest] using hrequest.symm
      have haddress : request.address = 0 := by rw [hrequestEq]
      obtain ⟨replies⟩ := packedReviewerCanonicalPreludeReplies_exists shape
      rw [haddress, packedReviewerMemory_header_cell shape]
      simp only [packedReviewerConsumeReply, packedReviewerHeaderBits_decode]
      exact packedReviewerNormalizePrelude_invariant shape left right hvalid
        replies _ _ (packedReviewerCanonicalPreludeState_start shape replies)
  | preludeProbe hvalid replies prelude hprelude preludeRequest word
      hpreludeRequest hread nextOrdinal repliesRev probePrefix address tail
      rest_eq =>
      obtain ⟨allCells, hfull⟩ :=
        packedReviewerCurrentPreludePlan_fetch_of_read shape.size
          (longCount shape) (packedReviewerMemory shape) prelude
          preludeRequest word hpreludeRequest hread
      obtain ⟨cell, hcell, nextPrefix, hnextRest⟩ :=
        probePrefix.advance_head allCells hfull address tail rest_eq
      have hget :
          (packedReviewerCurrentPreludePlan shape.size (longCount shape)
            prelude)[nextOrdinal]? = some address := by
        have hplanDecomp := probePrefix.plan_eq
        have hnextEq := probePrefix.next_eq
        simpa [hplanDecomp, hnextEq, rest_eq]
      have hrequestEq :
          request =
            { origin := .sparsePrelude preludeRequest, address := address,
              ordinal := nextOrdinal,
              cellCount :=
                (packedReviewerCurrentPreludePlan shape.size (longCount shape)
                  prelude).length } := by
        simpa [packedReviewerNextRequest, hpreludeRequest, hget] using
          hrequest.symm
      have haddress : request.address = address := by rw [hrequestEq]
      have hreply : (packedReviewerMemory shape)[address]? = some cell := by
        simpa [packedProbeCell] using hcell
      have hlen :
          (packedReviewerCurrentPreludePlan shape.size (longCount shape)
              prelude).length = nextOrdinal + 1 + tail.length := by
        have hplanDecomp := probePrefix.plan_eq
        have hnextEq := probePrefix.next_eq
        rw [rest_eq] at hplanDecomp
        have hlength := congrArg List.length hplanDecomp
        simp at hlength
        omega
      rw [haddress, hreply]
      simp only [packedReviewerConsumeReply]
      by_cases hmid :
          nextOrdinal + 1 <
            (packedReviewerCurrentPreludePlan shape.size (longCount shape)
              prelude).length
      · rw [if_pos hmid]
        cases tail with
        | nil =>
            exfalso
            simp at hlen
            omega
        | cons nextAddress nextTail =>
            exact
              ⟨PackedReviewerCanonicalControllerInvariant.preludeProbe hvalid
                replies prelude hprelude preludeRequest word hpreludeRequest
                hread (nextOrdinal + 1) (cell :: repliesRev) nextPrefix
                nextAddress nextTail hnextRest, trivial⟩
      · rw [if_neg hmid]
        have htail : tail = [] := by
          cases tail with
          | nil => rfl
          | cons headAddress restAddresses =>
              exfalso
              apply hmid
              simp at hlen
              omega
        subst htail
        have hfetchFull := nextPrefix.fetch_eq_of_rest_nil hnextRest
        have hfetchRequest :
            packedFetch (packedReviewerMemory shape)
                (packedReviewerSparsePreludeRequestPlan shape.size
                  (longCount shape) preludeRequest) =
              some ((cell :: repliesRev).reverse) := by
          rw [← packedReviewerCurrentPreludePlan_eq_requestPlan_of_read
            shape.size (longCount shape) (packedReviewerMemory shape) prelude
            preludeRequest word hpreludeRequest hread]
          exact hfetchFull
        have hdecode :=
          packedReviewerDecodePreludeReplies_eq_of_request_read shape.size
            (longCount shape) (packedReviewerMemory shape) prelude
            preludeRequest ((cell :: repliesRev).reverse) word
            hpreludeRequest hfetchRequest hread
        simp only [hdecode]
        exact packedReviewerNormalizePrelude_invariant shape left right
          hvalid replies _ _ (hprelude.consume hpreludeRequest hread)
  | wholeProbe hvalid logicalStepsAfterReply hsteps whole hwhole
      logicalRequest hlogicalRequest nextOrdinal repliesRev probePrefix
      address tail rest_eq =>
      have hcanonical : PackedReviewerWholeCanonicalScalarFits shape whole :=
        hcoupling
      obtain ⟨allCells, hfull⟩ :=
        packedReviewerLogicalPlan_fetch shape logicalRequest
      obtain ⟨cell, hcell, nextPrefix, hnextRest⟩ :=
        probePrefix.advance_head allCells hfull address tail rest_eq
      have hget :
          (packedReviewerLogicalPlan shape.size (longCount shape)
            (packedReviewerSparseCount shape)
            logicalRequest)[nextOrdinal]? = some address := by
        have hplanDecomp := probePrefix.plan_eq
        have hnextEq := probePrefix.next_eq
        simpa [hplanDecomp, hnextEq, rest_eq]
      have hrequestEq :
          request =
            { origin := .wholeQuery logicalRequest, address := address,
              ordinal := nextOrdinal,
              cellCount :=
                (packedReviewerLogicalPlan shape.size (longCount shape)
                  (packedReviewerSparseCount shape)
                  logicalRequest).length } := by
        simpa [packedReviewerNextRequest, hlogicalRequest, hget] using
          hrequest.symm
      have haddress : request.address = address := by rw [hrequestEq]
      have hreply : (packedReviewerMemory shape)[address]? = some cell := by
        simpa [packedProbeCell] using hcell
      have hlen :
          (packedReviewerLogicalPlan shape.size (longCount shape)
              (packedReviewerSparseCount shape) logicalRequest).length =
            nextOrdinal + 1 + tail.length := by
        have hplanDecomp := probePrefix.plan_eq
        have hnextEq := probePrefix.next_eq
        rw [rest_eq] at hplanDecomp
        have hlength := congrArg List.length hplanDecomp
        simp at hlength
        omega
      rw [haddress, hreply]
      simp only [packedReviewerConsumeReply, hlogicalRequest]
      by_cases hmid :
          nextOrdinal + 1 <
            (packedReviewerLogicalPlan shape.size (longCount shape)
              (packedReviewerSparseCount shape) logicalRequest).length
      · rw [if_pos hmid]
        cases tail with
        | nil =>
            exfalso
            simp at hlen
            omega
        | cons nextAddress nextTail =>
            refine
              ⟨PackedReviewerCanonicalControllerInvariant.wholeProbe hvalid
                logicalStepsAfterReply hsteps whole hwhole logicalRequest
                hlogicalRequest (nextOrdinal + 1) (cell :: repliesRev)
                nextPrefix nextAddress nextTail hnextRest, ?_⟩
            show PackedReviewerWholeCanonicalScalarFits shape whole
            exact hcanonical
      · rw [if_neg hmid]
        have htail : tail = [] := by
          cases tail with
          | nil => rfl
          | cons headAddress restAddresses =>
              exfalso
              apply hmid
              simp at hlen
              omega
        subst htail
        have hfetchFull := nextPrefix.fetch_eq_of_rest_nil hnextRest
        have hdecode :=
          packedReviewerLogicalDecode_eq_globalReadStore_of_fetch shape
            logicalRequest ((cell :: repliesRev).reverse) hfetchFull
        have hstep :=
          packedReviewerWholeCanonicalConsume_operational_fits hwhole
            hcanonical hlogicalRequest
        rw [hdecode]
        exact packedReviewerNormalizeWhole_invariant shape left right hvalid
          logicalStepsAfterReply hsteps _ hstep.1 hstep.2
  | done value hvalue =>
      simp [packedReviewerNextRequest] at hrequest
  | failed =>
      simp [packedReviewerNextRequest] at hrequest

/-- Strengthened reachability motive: coupled invariant along every prefix. -/
private theorem packedReviewerCanonicalReachable_invariant
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerControllerState}
    (hstate : PackedReviewerCanonicalReachable shape left right state) :
    PackedReviewerCanonicalControllerCoupledInvariant shape left right
      state := by
  induction hstate with
  | start =>
      refine
        ⟨packedReviewerCanonicalController_start_invariant shape left right,
          ?_⟩
      by_cases hvalid : left < right /\ right <= shape.size <;>
        simp [packedReviewerController, hvalid,
          packedReviewerControllerWholeCoupling]
  | @step state request hreachable hrequestStep ih =>
      exact PackedReviewerCanonicalControllerCoupledInvariant.consume ih
        hrequestStep

/--
Every canonically reachable actual controller prefix satisfies the fixed
state-machine envelope.
-/
theorem packedReviewerCanonicalReachable_state_machine_fits
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerControllerState}
    (hstate : PackedReviewerCanonicalReachable shape left right state) :
    PackedReviewerControllerStateMachineFits shape.size state :=
  packedReviewerControllerStateMachineFits_of_core
    (packedReviewerCanonicalReachable_invariant hstate).1.core_fits

/--
The reachable-state certificate from an actual canonical-memory reachability
witness.
-/
theorem packedReviewerReachableStateCertificate_of_reachable
    {shape : CartesianShape} {left right : Nat}
    {state : PackedReviewerControllerState}
    (hstate : PackedReviewerCanonicalReachable shape left right state) :
    PackedReviewerReachableStateCertificate shape left right state := by
  have hfits := packedReviewerCanonicalReachable_state_machine_fits hstate
  exact
    { reachable := hstate
      state_machine_fits := hfits
      phase_tag := hfits.phase_tag
      nested_control_tags :=
        packedReviewerControllerNestedTagCodes_fits shape.size state
      scalar_register_count := hfits.scalar_register_count
      scalar_fields := hfits.scalar_fields
      word_buffer := hfits.word_buffer
      wide_buffer_count := hfits.wide_buffer_count
      wide_fields := hfits.wide_fields
      continuation_depth := hfits.continuation_depth
      control_fields := hfits.control_fields }
/-! ## Physical request-operand closure and the public run certificate -/

/-- Every expected-trace physical request retains only fitting operands. -/
private theorem packedReviewerExpectedPhysicalTrace_request_operands_fit
    (shape : CartesianShape) (left right : Nat)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈ packedReviewerExpectedPhysicalTrace shape left right) :
    PackedReviewerPhysicalRequestOperandsFit shape.size event.request := by
  by_cases hvalid : left < right ∧ right <= shape.size
  · rw [packedReviewerExpectedPhysicalTrace, if_pos hvalid] at hmem
    rcases List.mem_append.mp hmem with hprefix | hlogical
    · rcases List.mem_append.mp hprefix with hheader | hprelude
      · refine packedReviewerPhysicalEvents_request_operands_fit shape.size
          (packedReviewerMemory shape) .header [0] ?_ ?_ ?_ hheader
        · intro operand hoperand
          simp only [packedReviewerPhysicalOriginOperands] at hoperand
          exact False.elim (List.not_mem_nil hoperand)
        · intro address haddress
          simp only [List.mem_singleton] at haddress
          have hsize :=
            packedReviewerInputSize_lt_two_pow_cellWidth shape.size
          omega
        · decide
      · unfold packedReviewerSparsePreludePhysicalTrace at hprelude
        rw [List.mem_flatMap] at hprelude
        rcases hprelude with ⟨request, hrequest, hevent⟩
        refine packedReviewerPhysicalEvents_request_operands_fit shape.size
          (packedReviewerMemory shape) (.sparsePrelude request)
          (packedReviewerSparsePreludeRequestPlan shape.size (longCount shape)
            request) ?_ ?_ ?_ hevent
        · intro operand hoperand
          simp only [packedReviewerPhysicalOriginOperands] at hoperand
          exact False.elim (List.not_mem_nil hoperand)
        · intro address haddress
          have hcell : address <
              packedReviewerCellCount shape.size (longCount shape)
                (packedReviewerSparseCount shape) := by
            apply packedReviewerSparsePreludeProbePlan_address_lt_cellCount
              shape
            exact List.mem_flatMap.mpr ⟨request, hrequest, haddress⟩
          exact Nat.lt_trans hcell
            (packedReviewerSparsePreludeCellCount_lt_two_pow_reviewerWidth
              shape)
        · exact packedReviewerSparsePreludeRequestPlan_length_le_two
            shape.size (longCount shape) request
    · unfold packedReviewerLogicalTracePhysicalTrace at hlogical
      rw [List.mem_flatMap] at hlogical
      rcases hlogical with ⟨logicalEvent, hlogicalMem, hevent⟩
      have hfit := packedReviewerDriveLogical_210_request_operands_fit shape
        left right hvalid.1 hvalid.2 logicalEvent hlogicalMem
      refine packedReviewerPhysicalEvents_request_operands_fit shape.size
        (packedReviewerMemory shape) (.wholeQuery logicalEvent.request)
        (packedReviewerLogicalPlan shape.size (longCount shape)
          (packedReviewerSparseCount shape) logicalEvent.request)
        ?_ ?_ ?_ hevent
      · intro operand hoperand
        simp only [packedReviewerPhysicalOriginOperands] at hoperand
        exact hfit.operands_fit operand hoperand
      · intro address haddress
        exact packedReviewerLogicalPlan_address_lt_two_pow shape
          logicalEvent.request haddress
      · exact packedReviewerLogicalPlan_length_le_two shape.size
          (longCount shape) (packedReviewerSparseCount shape)
          logicalEvent.request
  · simp [packedReviewerExpectedPhysicalTrace, hvalid] at hmem

/-- Every attempted request of a grouped canonical run has fitting operands. -/
theorem PackedReviewerRunGrouping.request_operands_fit
    {shape : CartesianShape} {left right : Nat}
    (grouping : PackedReviewerRunGrouping shape left right)
    {event : PackedReviewerPhysicalEvent}
    (hmem : event ∈
      (packedReviewerRunAgainstMemory (packedReviewerMemory shape)
        shape.size left right).trace) :
    PackedReviewerPhysicalRequestOperandsFit shape.size event.request := by
  rw [grouping.trace_eq] at hmem
  exact packedReviewerExpectedPhysicalTrace_request_operands_fit shape
    left right hmem

/--
Every field of the stable twenty-six-fact public bundle is a checked
projection of an independent run theorem; the two request-operand fields are
the canonical-start closure and its grouped physical transport.
-/
theorem packedReviewerRunAgainstMemory_public_certificate
    (xs : List Int) (left right : Nat) :
    PackedReviewerPublicRunCertificate xs left right := by
  have houtcome := packedReviewerRunAgainstMemory_public_outcome xs left right
  dsimp only at houtcome
  obtain ⟨hterminal, hfailed, hstate, hgrouping⟩ := houtcome
  exact
    { terminal_eq := hterminal
      failed_false := hfailed
      state_eq := hstate
      grouping := hgrouping
      invalid_no_requests :=
        packedReviewerRunAgainstMemory_invalid_trace_eq_nil
          (SuccinctClassic.cartesianShape xs) left right
      input_size_width :=
        packedReviewerInputSize_lt_two_pow_cellWidth
          (SuccinctClassic.cartesianShape xs).size
      valid_endpoints_width :=
        packedReviewerValidEndpoints_lt_two_pow_cellWidth
          (SuccinctClassic.cartesianShape xs).size left right
      header_values_width :=
        ⟨longCount_lt_two_pow_reviewerWidth
            (SuccinctClassic.cartesianShape xs),
          packedReviewerSparseCount_lt_two_pow
            (SuccinctClassic.cartesianShape xs)⟩
      memory_words_width := fun _cell hcell =>
        packedReviewerMemory_word_and_value_fit
          (SuccinctClassic.cartesianShape xs) hcell
      prelude_decode_width :=
        packedReviewerDecodePreludeReplies_word_fits
          (SuccinctClassic.cartesianShape xs).size
          (longCount (SuccinctClassic.cartesianShape xs))
      logical_decode_width :=
        packedReviewerLogicalDecode_word_fits
          (SuccinctClassic.cartesianShape xs).size
          (longCount (SuccinctClassic.cartesianShape xs))
          (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs))
      logical_request_operands_width :=
        packedReviewerDriveLogical_210_request_operands_fit
          (SuccinctClassic.cartesianShape xs) left right
      logical_control_tags_width :=
        packedReviewerLogicalControlCodes_fit
          (SuccinctClassic.cartesianShape xs).size
      physical_control_tags_width :=
        packedReviewerPhysicalControlCodes_fit
          (SuccinctClassic.cartesianShape xs).size
      controller_phase_tag_width :=
        packedReviewerControllerStatePhaseCode_fits
          (SuccinctClassic.cartesianShape xs).size
      memory_only :=
        packedReviewerRunAgainstMemory_memory_only
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right
      reply_success := fun _event hmem => hgrouping.reply_some hmem
      allocated := fun _event hmem => hgrouping.address_lt_cellCount hmem
      address_width := fun _event hmem => hgrouping.address_lt_two_pow hmem
      physical_request_operands_width := fun _event hmem =>
        hgrouping.request_operands_fit hmem
      reply_width := fun _event _cell hmem hreply =>
        packedReviewerRunAgainstMemory_reply_width
          (SuccinctClassic.cartesianShape xs) left right hmem hreply
      reply_value_width := fun _event _cell hmem hreply =>
        packedReviewerRunAgainstMemory_reply_value_width
          (SuccinctClassic.cartesianShape xs) left right hmem hreply
      dead_address_width :=
        packedReviewerInteriorDeadAddress_lt_two_pow
          (SuccinctClassic.cartesianShape xs)
      word_width_logarithmic :=
        packedReviewerCellWidth_le_log
          (SuccinctClassic.cartesianShape xs).size
      trace_cap :=
        packedReviewerRunAgainstMemory_trace_length_le_427
          (packedReviewerMemory (SuccinctClassic.cartesianShape xs))
          (SuccinctClassic.cartesianShape xs).size left right
      result_width :=
        packedReviewerPublicResult_lt_two_pow xs left right }
end PackedCellProbe
end SuccinctFinal
end RMQ
