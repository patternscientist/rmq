import RMQ.Core.BPCloseNavigation
import RMQ.Core.SuccinctSpace.BPAccess

/-!
Public facade for the balanced-parentheses close-navigation spoke.

The construction modules keep the detailed `SuccinctClose` names. This module
provides shorter downstream names for compact BP close/LCA navigation over
Cartesian-shape balanced-parentheses encodings. This is not yet a full tree
navigation API; it is the reusable close/LCA navigation layer consumed by the
succinct RMQ capstone.
-/

namespace RMQ.BPNavigation

/-- Rank/select access for a balanced-parentheses bitvector. -/
abbrev BalancedParensAccess :=
  RMQ.SuccinctSpace.BalancedParensAccess

/-- Family-level balanced-parentheses rank/select access surface. -/
abbrev BalancedParensAccessFamily :=
  RMQ.SuccinctSpace.BalancedParensAccessFamily

/-- Package a Cartesian shape's BP code as certified balanced parentheses. -/
abbrev bpParensOfShape :=
  RMQ.SuccinctSpace.bpParensOfShape

/--
Costed close-position lookup for the node at an inorder index, implemented as
false-select over the Cartesian-shape balanced-parentheses code.
-/
def closeOfInorderCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) : Costed (Option Nat) :=
  access.selectCosted false idx

theorem closeOfInorderCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) :
    (closeOfInorderCosted access idx).cost <= queryCost := by
  exact
    RMQ.SuccinctSpace.BalancedParensAccess.selectCosted_cost_le
      access false idx

theorem closeOfInorderCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) :
    (closeOfInorderCosted access idx).erase =
      RMQ.SuccinctSpace.bpCloseOfInorder? shape idx := by
  calc
    (closeOfInorderCosted access idx).erase =
        RMQ.Succinct.select false shape.bpCode idx := by
          exact
            RMQ.SuccinctSpace.BalancedParensAccess.selectCosted_erase
              access false idx
    _ = RMQ.SuccinctSpace.bpCloseOfInorder? shape idx := by
          exact
            RMQ.SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?
              shape idx

/--
Costed inorder-index recovery from a closing parenthesis position. This is the
false-rank at `close + 1`, shifted from one-based to zero-based indexing.
-/
def inorderOfCloseCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (close : Nat) : Costed Nat :=
  Costed.map (fun rankFalse => rankFalse - 1)
    (access.rankCosted false (close + 1))

theorem inorderOfCloseCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (close : Nat) :
    (inorderOfCloseCosted access close).cost <= queryCost := by
  exact
    RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_cost_le
      access false (close + 1)

theorem inorderOfCloseCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (close : Nat) :
    (inorderOfCloseCosted access close).erase =
      RMQ.Succinct.rankPrefix false shape.bpCode (close + 1) - 1 := by
  unfold inorderOfCloseCosted
  rw [Costed.erase_map]
  exact congrArg (fun rankFalse => rankFalse - 1)
    (RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_erase
      access false (close + 1))

theorem inorderOfCloseCosted_erase_of_bpCloseOfInorder?
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    {idx close : Nat}
    (hclose :
      RMQ.SuccinctSpace.bpCloseOfInorder? shape idx = some close) :
    (inorderOfCloseCosted access close).erase = idx := by
  rw [inorderOfCloseCosted_erase]
  rw [RMQ.SuccinctSpace.bpCloseOfInorder?_rankFalse_succ shape hclose]
  omega

/--
One theorem packaging the public close/rank bridge for Cartesian-shape BP
navigation. It exposes the two charged legs needed by downstream BP tree
navigation: inorder-to-close by select, and close-to-inorder by rank.
-/
theorem shapeAccessCloseRankProfile
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost) :
    (forall idx,
      (closeOfInorderCosted access idx).cost <= queryCost /\
        (closeOfInorderCosted access idx).erase =
          RMQ.SuccinctSpace.bpCloseOfInorder? shape idx) /\
      (forall close,
        (inorderOfCloseCosted access close).cost <= queryCost /\
          (inorderOfCloseCosted access close).erase =
            RMQ.Succinct.rankPrefix false shape.bpCode (close + 1) - 1) /\
      (forall {idx close : Nat},
        RMQ.SuccinctSpace.bpCloseOfInorder? shape idx = some close ->
          (inorderOfCloseCosted access close).erase = idx) := by
  constructor
  · intro idx
    exact ⟨closeOfInorderCosted_cost_le access idx,
      closeOfInorderCosted_erase access idx⟩
  · constructor
    · intro close
      exact ⟨inorderOfCloseCosted_cost_le access close,
        inorderOfCloseCosted_erase access close⟩
    · intro idx close hclose
      exact inorderOfCloseCosted_erase_of_bpCloseOfInorder? access hclose

/-- Compact BP close/LCA directory shape for one Cartesian shape. -/
abbrev CompactCloseDirectory :=
  RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-- Auxiliary-overhead budget for the compact BP close/LCA directory. -/
abbrev compactCloseOverhead :=
  RMQ.SuccinctClose.compactBPCloseOverhead

/-- Uniform modeled query cost for unseeded compact BP close/LCA queries. -/
abbrev compactCloseQueryCost :=
  RMQ.SuccinctClose.concreteCompactBPCloseQueryCost

/--
Uniform modeled query cost when endpoint-local BP decoding receives rank-close
seeds from a supplied rank/select layer.
-/
abbrev compactCloseQueryCostWithRankSeed :=
  RMQ.SuccinctClose.concreteCompactBPCloseQueryCostWithRankSeed

/-- Concrete compact BP close/LCA directory for one Cartesian shape. -/
abbrev compactCloseDirectory :=
  RMQ.SuccinctClose.concreteCompactBPCloseLCADirectory

/--
Public profile for the concrete compact BP close/LCA directory: `o(n)`
auxiliary payload, constant modeled query cost, exact answer-close semantics,
and machine-word-bounded payload reads.
-/
abbrev compactCloseDirectoryProfile :=
  RMQ.SuccinctClose.concreteCompactBPCloseLCADirectory_profile

/-- Large-regime version of `compactCloseDirectoryProfile`. -/
abbrev compactCloseDirectoryProfileOfSizeGe :=
  RMQ.SuccinctClose.concreteCompactBPCloseLCADirectory_profile_of_size_ge

/-- Generic payload-live BP close-navigation family shape. -/
abbrev MacroMicroCloseNavigationFamily :=
  RMQ.SuccinctClose.PayloadLiveMacroMicroBPCloseNavigationFamily

/--
Generic `2*n + o(n)`, constant-query profile for payload-live BP close
navigation families.
-/
abbrev macroMicroTwoNPlusOBuiltQueryProfile
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (family :
      MacroMicroCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) :=
  RMQ.SuccinctClose.PayloadLiveMacroMicroBPCloseNavigationFamily.two_n_plus_o_built_query_profile
    family

end RMQ.BPNavigation
