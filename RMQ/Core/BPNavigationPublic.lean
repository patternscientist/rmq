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
Costed balanced-parentheses prefix excess at `pos`, routed through the public
rank/select BP access layer.
-/
def excessAtCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (pos : Nat) : Costed Nat :=
  access.excessCosted pos

theorem excessAtCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (pos : Nat) :
    (excessAtCosted access pos).cost <= 2 * queryCost := by
  exact
    RMQ.SuccinctSpace.BalancedParensAccess.excessCosted_cost_le
      access pos

theorem excessAtCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (pos : Nat) :
    (excessAtCosted access pos).erase =
      RMQ.Succinct.rankPrefix true shape.bpCode pos -
        RMQ.Succinct.rankPrefix false shape.bpCode pos := by
  exact
    RMQ.SuccinctSpace.BalancedParensAccess.excessCosted_erase
      access pos

theorem closeRank_le_openRank_of_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    {pos : Nat} (hpos : pos <= shape.bpCode.length) :
    (access.rankCosted false pos).erase <=
      (access.rankCosted true pos).erase := by
  exact
    RMQ.SuccinctSpace.BalancedParensAccess.close_rank_le_open_rank
      access hpos

/--
Semantic close-rank/open-rank invariant for Cartesian-shape BP prefixes. This
is the erased `rankPrefix` form of `closeRank_le_openRank_of_le`.
-/
theorem closeRankPrefix_le_openRankPrefix_of_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    {pos : Nat} (hpos : pos <= shape.bpCode.length) :
    RMQ.Succinct.rankPrefix false shape.bpCode pos <=
      RMQ.Succinct.rankPrefix true shape.bpCode pos := by
  have h := closeRank_le_openRank_of_le access hpos
  rw [RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_erase access false pos,
    RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_erase access true pos] at h
  simpa [RMQ.SuccinctSpace.bpParensOfShape_bits] using h

/--
Costed lookup of a node's closing parenthesis together with the prefix excess
immediately after that close. This is the first public composition of the
inorder-to-close select leg with the rank-backed excess leg.
-/
def closeExcessOfInorderCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (closeOfInorderCosted access idx) fun
    | none => Costed.pure none
    | some close =>
        Costed.map (fun excess => some (close, excess))
          (excessAtCosted access (close + 1))

theorem closeExcessOfInorderCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) :
    (closeExcessOfInorderCosted access idx).cost <= 3 * queryCost := by
  unfold closeExcessOfInorderCosted
  rw [Costed.cost_bind]
  cases hclose : (closeOfInorderCosted access idx).value with
  | none =>
      simp
      have hselect := closeOfInorderCosted_cost_le access idx
      omega
  | some close =>
      simp
      have hselect := closeOfInorderCosted_cost_le access idx
      have hexcess := excessAtCosted_cost_le access (close + 1)
      omega

theorem closeExcessOfInorderCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) :
    (closeExcessOfInorderCosted access idx).erase =
      Option.map
        (fun close =>
          (close,
            RMQ.Succinct.rankPrefix true shape.bpCode (close + 1) -
              RMQ.Succinct.rankPrefix false shape.bpCode (close + 1)))
        (RMQ.SuccinctSpace.bpCloseOfInorder? shape idx) := by
  unfold closeExcessOfInorderCosted
  rw [Costed.erase_bind]
  rw [closeOfInorderCosted_erase access idx]
  cases hclose : RMQ.SuccinctSpace.bpCloseOfInorder? shape idx with
  | none =>
      simp
  | some close =>
      simp [excessAtCosted_erase]

theorem closeExcessOfInorderCosted_erase_of_bpCloseOfInorder?
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    {idx close : Nat}
    (hclose :
      RMQ.SuccinctSpace.bpCloseOfInorder? shape idx = some close) :
    (closeExcessOfInorderCosted access idx).erase =
      some
        (close,
          RMQ.Succinct.rankPrefix true shape.bpCode (close + 1) -
            RMQ.Succinct.rankPrefix false shape.bpCode (close + 1)) := by
  rw [closeExcessOfInorderCosted_erase]
  simp [hclose]

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

/--
Stronger public bridge profile adding rank-backed prefix excess and the
composed inorder-to-close-plus-excess query.
-/
theorem shapeAccessCloseRankExcessProfile
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
      (forall pos,
        (excessAtCosted access pos).cost <= 2 * queryCost /\
          (excessAtCosted access pos).erase =
            RMQ.Succinct.rankPrefix true shape.bpCode pos -
              RMQ.Succinct.rankPrefix false shape.bpCode pos) /\
      (forall idx,
        (closeExcessOfInorderCosted access idx).cost <=
            3 * queryCost /\
          (closeExcessOfInorderCosted access idx).erase =
            Option.map
              (fun close =>
                (close,
                  RMQ.Succinct.rankPrefix true shape.bpCode (close + 1) -
                    RMQ.Succinct.rankPrefix false shape.bpCode (close + 1)))
              (RMQ.SuccinctSpace.bpCloseOfInorder? shape idx)) /\
      (forall {idx close : Nat},
        RMQ.SuccinctSpace.bpCloseOfInorder? shape idx = some close ->
          (closeExcessOfInorderCosted access idx).erase =
            some
              (close,
                RMQ.Succinct.rankPrefix true shape.bpCode (close + 1) -
                  RMQ.Succinct.rankPrefix false shape.bpCode (close + 1))) /\
      (forall {pos : Nat},
        pos <= shape.bpCode.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) := by
  constructor
  · intro idx
    exact ⟨closeOfInorderCosted_cost_le access idx,
      closeOfInorderCosted_erase access idx⟩
  · constructor
    · intro close
      exact ⟨inorderOfCloseCosted_cost_le access close,
        inorderOfCloseCosted_erase access close⟩
    · constructor
      · intro pos
        exact ⟨excessAtCosted_cost_le access pos,
          excessAtCosted_erase access pos⟩
      · constructor
        · intro idx
          exact ⟨closeExcessOfInorderCosted_cost_le access idx,
            closeExcessOfInorderCosted_erase access idx⟩
        · constructor
          · intro idx close hclose
            exact
              closeExcessOfInorderCosted_erase_of_bpCloseOfInorder?
                access hclose
          · intro pos hpos
            exact closeRank_le_openRank_of_le access hpos

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
