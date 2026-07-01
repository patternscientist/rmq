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

/-- Public reference prefix excess for a Cartesian-shape BP code. -/
def bpPrefixExcess
    (shape : RMQ.Cartesian.CartesianShape)
    (pos : Nat) : Nat :=
  RMQ.Succinct.rankPrefix true shape.bpCode pos -
    RMQ.Succinct.rankPrefix false shape.bpCode pos

/--
Reference matching-open search for a closing parenthesis.

The search is deliberately phrased only in terms of public BP rank/excess
semantics. It scans left from `fuel`, looking for the nearest prefix position
whose excess equals `target`; for a genuine closing parenthesis, that position
is its matching open.
-/
def matchingOpenSearchRef
    (shape : RMQ.Cartesian.CartesianShape)
    (target : Nat) : Nat -> Option Nat
  | 0 =>
      if bpPrefixExcess shape 0 = target then
        some 0
      else
        none
  | pos + 1 =>
      if bpPrefixExcess shape (pos + 1) = target then
        some (pos + 1)
      else
        matchingOpenSearchRef shape target pos

/-- Charged public matching-open search using only excess queries. -/
def matchingOpenSearchCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (target : Nat) : Nat -> Costed (Option Nat)
  | 0 =>
      Costed.bind (excessAtCosted access 0) fun excess =>
        Costed.pure (if excess = target then some 0 else none)
  | pos + 1 =>
      Costed.bind (excessAtCosted access (pos + 1)) fun excess =>
        if excess = target then
          Costed.pure (some (pos + 1))
        else
          matchingOpenSearchCosted access target pos

theorem matchingOpenSearchCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (target fuel : Nat) :
    (matchingOpenSearchCosted access target fuel).cost <=
      (fuel + 1) * (2 * queryCost) := by
  induction fuel with
  | zero =>
      by_cases htarget : (excessAtCosted access 0).value = target
      · simp [matchingOpenSearchCosted, Costed.bind, htarget]
        have hexcess := excessAtCosted_cost_le access 0
        omega
      · simp [matchingOpenSearchCosted, Costed.bind, htarget]
        have hexcess := excessAtCosted_cost_le access 0
        omega
  | succ fuel ih =>
      by_cases htarget :
          (excessAtCosted access (fuel + 1)).value = target
      · simp [matchingOpenSearchCosted, Costed.bind, htarget]
        have hexcess := excessAtCosted_cost_le access (fuel + 1)
        have hsucc :
            (fuel + 1 + 1) * (2 * queryCost) =
              (fuel + 1) * (2 * queryCost) + 2 * queryCost := by
          simpa [Nat.succ_eq_add_one] using
            (Nat.succ_mul (fuel + 1) (2 * queryCost))
        calc
          (excessAtCosted access (fuel + 1)).cost <=
              2 * queryCost := hexcess
          _ <= (fuel + 1 + 1) * (2 * queryCost) := by
            rw [hsucc]
            omega
      · simp [matchingOpenSearchCosted, Costed.bind, htarget]
        have hexcess := excessAtCosted_cost_le access (fuel + 1)
        have hsucc :
            (fuel + 1 + 1) * (2 * queryCost) =
              (fuel + 1) * (2 * queryCost) + 2 * queryCost := by
          simpa [Nat.succ_eq_add_one] using
            (Nat.succ_mul (fuel + 1) (2 * queryCost))
        calc
          (excessAtCosted access (fuel + 1)).cost +
              (matchingOpenSearchCosted access target fuel).cost <=
              2 * queryCost + (fuel + 1) * (2 * queryCost) := by
            exact Nat.add_le_add hexcess ih
          _ <= (fuel + 1 + 1) * (2 * queryCost) := by
            rw [hsucc]
            omega

theorem matchingOpenSearchCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (target fuel : Nat) :
    (matchingOpenSearchCosted access target fuel).erase =
      matchingOpenSearchRef shape target fuel := by
  induction fuel with
  | zero =>
      have hexcess :
          (excessAtCosted access 0).value =
            bpPrefixExcess shape 0 := by
        simpa [Costed.erase, bpPrefixExcess] using
          excessAtCosted_erase access 0
      by_cases htarget : bpPrefixExcess shape 0 = target
      · have hvalue : (excessAtCosted access 0).value = target := by
          rw [hexcess, htarget]
        simp [matchingOpenSearchCosted, matchingOpenSearchRef,
          Costed.bind, Costed.pure, Costed.erase, htarget, hvalue]
      · have hvalue : ¬(excessAtCosted access 0).value = target := by
          intro hvalue
          exact htarget (by rw [← hexcess, hvalue])
        simp [matchingOpenSearchCosted, matchingOpenSearchRef,
          Costed.bind, Costed.pure, Costed.erase, htarget, hvalue]
  | succ fuel ih =>
      have hexcess :
          (excessAtCosted access (fuel + 1)).value =
            bpPrefixExcess shape (fuel + 1) := by
        simpa [Costed.erase, bpPrefixExcess] using
          excessAtCosted_erase access (fuel + 1)
      by_cases htarget : bpPrefixExcess shape (fuel + 1) = target
      · have hvalue :
            (excessAtCosted access (fuel + 1)).value = target := by
          rw [hexcess, htarget]
        simp [matchingOpenSearchCosted, matchingOpenSearchRef,
          Costed.bind, Costed.pure, Costed.erase, htarget, hvalue]
      · have hvalue :
            ¬(excessAtCosted access (fuel + 1)).value = target := by
          intro hvalue
          exact htarget (by rw [← hexcess, hvalue])
        simp [matchingOpenSearchCosted, matchingOpenSearchRef,
          Costed.bind, Costed.erase, htarget, hvalue]
        simpa [Costed.erase] using ih

theorem matchingOpenSearchRef_some_nearest
    {shape : RMQ.Cartesian.CartesianShape}
    {target fuel openPos : Nat}
    (hopen :
      matchingOpenSearchRef shape target fuel = some openPos) :
    openPos <= fuel /\
      bpPrefixExcess shape openPos = target /\
      forall {pos : Nat},
        openPos < pos ->
          pos <= fuel ->
            Not (bpPrefixExcess shape pos = target) := by
  induction fuel generalizing openPos with
  | zero =>
      by_cases htarget : bpPrefixExcess shape 0 = target
      · simp [matchingOpenSearchRef, htarget] at hopen
        subst openPos
        constructor
        · omega
        constructor
        · exact htarget
        · intro pos hgt hle
          omega
      · simp [matchingOpenSearchRef, htarget] at hopen
  | succ fuel ih =>
      by_cases htarget : bpPrefixExcess shape (fuel + 1) = target
      · simp [matchingOpenSearchRef, htarget] at hopen
        subst openPos
        constructor
        · omega
        constructor
        · exact htarget
        · intro pos hgt hle
          omega
      · simp [matchingOpenSearchRef, htarget] at hopen
        rcases ih hopen with ⟨hleOpen, htargetOpen, hnearest⟩
        constructor
        · omega
        constructor
        · exact htargetOpen
        · intro pos hgt hle
          by_cases hpos : pos = fuel + 1
          · subst pos
            exact htarget
          · have hposLe : pos <= fuel := by
              omega
            exact hnearest hgt hposLe

/-- Reference matching open for a closing position, derived from public excess. -/
def matchingOpenOfClose?
    (shape : RMQ.Cartesian.CartesianShape)
    (close : Nat) : Option Nat :=
  let target :=
    RMQ.Succinct.rankPrefix true shape.bpCode (close + 1) -
      RMQ.Succinct.rankPrefix false shape.bpCode (close + 1)
  matchingOpenSearchRef shape target close

theorem matchingOpenOfClose?_nearest_equal_excess_of_bpCloseOfInorder?
    {shape : RMQ.Cartesian.CartesianShape}
    {idx close openPos : Nat}
    (_hclose :
      RMQ.SuccinctSpace.bpCloseOfInorder? shape idx = some close)
    (hopen : matchingOpenOfClose? shape close = some openPos) :
    openPos <= close /\
      bpPrefixExcess shape openPos = bpPrefixExcess shape (close + 1) /\
      forall {pos : Nat},
        openPos < pos ->
          pos <= close ->
            Not
              (bpPrefixExcess shape pos =
                bpPrefixExcess shape (close + 1)) := by
  unfold matchingOpenOfClose? at hopen
  simpa [bpPrefixExcess] using
    matchingOpenSearchRef_some_nearest (shape := shape) (hopen := hopen)

/--
Reference subtree interval for an inorder node.

The result is a half-open interval of inorder indices. The left endpoint is
the number of closes before the matching open, and the right endpoint is the
rank-close just after the node close.
-/
def subtreeIntervalOfInorder?
    (shape : RMQ.Cartesian.CartesianShape)
    (idx : Nat) : Option (Prod Nat Nat) :=
  match RMQ.SuccinctSpace.bpCloseOfInorder? shape idx with
  | none => none
  | some close =>
      match matchingOpenOfClose? shape close with
      | none => none
      | some openPos =>
          some
            (RMQ.Succinct.rankPrefix false shape.bpCode openPos,
              RMQ.Succinct.rankPrefix false shape.bpCode (close + 1))

/--
A coarse public cost budget for subtree-interval navigation.

This is a model-level budget in charged rank/excess operations, not a claim
about Lean evaluator runtime or stored payload bits.
-/
def subtreeIntervalQueryCost
    (shape : RMQ.Cartesian.CartesianShape)
    (queryCost : Nat) : Nat :=
  queryCost + 2 * queryCost +
    (shape.bpCode.length + 1) * (2 * queryCost) + 2 * queryCost

/--
Costed public subtree interval for an inorder node.

It obtains the close by charged select, searches for the matching open by
charged excess queries, and then returns the half-open inorder interval by two
charged close-rank queries.
-/
def subtreeIntervalOfInorderCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) : Costed (Option (Prod Nat Nat)) :=
  Costed.bind (closeOfInorderCosted access idx) fun close? =>
    match close? with
    | none => Costed.pure none
    | some close =>
        Costed.bind (excessAtCosted access (close + 1)) fun target =>
          Costed.bind (matchingOpenSearchCosted access target close) fun open? =>
            match open? with
            | none => Costed.pure none
            | some openPos =>
                Costed.bind (access.rankCosted false openPos) fun lo =>
                  Costed.map (fun hi => some (lo, hi))
                    (access.rankCosted false (close + 1))

theorem subtreeIntervalOfInorderCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) :
    (subtreeIntervalOfInorderCosted access idx).cost <=
      subtreeIntervalQueryCost shape queryCost := by
  unfold subtreeIntervalOfInorderCosted
  have hcloseCost := closeOfInorderCosted_cost_le access idx
  cases hcloseVal : (closeOfInorderCosted access idx).value with
  | none =>
      simp [Costed.bind, Costed.pure, hcloseVal,
        subtreeIntervalQueryCost]
      omega
  | some close =>
      have hcloseSem :
          RMQ.SuccinctSpace.bpCloseOfInorder? shape idx = some close := by
        have h := (closeOfInorderCosted_erase access idx).symm
        simpa [Costed.erase, hcloseVal] using h
      have hcloseBound :=
        RMQ.SuccinctSpace.bpCloseOfInorder?_bounds shape hcloseSem
      have hsearchMono :
          (close + 1) * (2 * queryCost) <=
            (shape.bpCode.length + 1) * (2 * queryCost) := by
        exact Nat.mul_le_mul_right _ (by omega)
      let target := (excessAtCosted access (close + 1)).value
      have htargetCost := excessAtCosted_cost_le access (close + 1)
      have hsearchCost :=
        matchingOpenSearchCosted_cost_le access target close
      have hsearchCostLen :
          (matchingOpenSearchCosted access target close).cost <=
            (shape.bpCode.length + 1) * (2 * queryCost) :=
        Nat.le_trans hsearchCost hsearchMono
      cases hopenVal :
          (matchingOpenSearchCosted access target close).value with
      | none =>
          simp [Costed.bind, Costed.pure, hcloseVal, hopenVal,
            subtreeIntervalQueryCost, target] at *
          omega
      | some openPos =>
          have hloCost :=
            RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_cost_le
              access false openPos
          have hhiCost :=
            RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_cost_le
              access false (close + 1)
          simp [Costed.bind, Costed.map, Costed.pure, hcloseVal, hopenVal,
            subtreeIntervalQueryCost, target] at *
          omega

theorem subtreeIntervalOfInorderCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (idx : Nat) :
    (subtreeIntervalOfInorderCosted access idx).erase =
      subtreeIntervalOfInorder? shape idx := by
  unfold subtreeIntervalOfInorderCosted subtreeIntervalOfInorder?
  rw [Costed.erase_bind]
  rw [closeOfInorderCosted_erase access idx]
  cases hclose : RMQ.SuccinctSpace.bpCloseOfInorder? shape idx with
  | none =>
      simp
  | some close =>
      simp only
      rw [Costed.erase_bind]
      rw [excessAtCosted_erase access (close + 1)]
      unfold matchingOpenOfClose?
      rw [Costed.erase_bind]
      rw [matchingOpenSearchCosted_erase access
        (RMQ.Succinct.rankPrefix true shape.bpCode (close + 1) -
          RMQ.Succinct.rankPrefix false shape.bpCode (close + 1)) close]
      cases hopen :
          matchingOpenSearchRef shape
            (RMQ.Succinct.rankPrefix true shape.bpCode (close + 1) -
              RMQ.Succinct.rankPrefix false shape.bpCode (close + 1))
            close with
      | none =>
          simp
      | some openPos =>
          simp only
          rw [Costed.erase_bind]
          rw [RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_erase
            access false openPos]
          rw [Costed.erase_map]
          rw [RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_erase
            access false (close + 1)]
          simp [RMQ.SuccinctSpace.bpParensOfShape_bits]

theorem shapeAccessSubtreeIntervalProfile
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost) :
    forall idx,
      (subtreeIntervalOfInorderCosted access idx).cost <=
          subtreeIntervalQueryCost shape queryCost /\
        (subtreeIntervalOfInorderCosted access idx).erase =
          subtreeIntervalOfInorder? shape idx := by
  intro idx
  exact ⟨subtreeIntervalOfInorderCosted_cost_le access idx,
    subtreeIntervalOfInorderCosted_erase access idx⟩

/--
Public matching-open component for fast BP tree navigation.

`payloadBits` is only the component's payload accounting field. The exactness
field is proof-only, and `queryCost` is the model-level charge for one
matching-open query.
-/
structure BalancedParensMatchingOpenAccess
    (shape : RMQ.Cartesian.CartesianShape)
    (overhead queryCost : Nat) where
  payloadBits : Nat
  payloadBits_le_overhead : payloadBits <= overhead
  matchingOpenCosted : Nat -> Costed (Option Nat)
  matchingOpen_cost_le :
    forall close, (matchingOpenCosted close).cost <= queryCost
  matchingOpen_erase_of_lt :
    forall {close}, close < shape.bpCode.length ->
      (matchingOpenCosted close).erase =
      matchingOpenOfClose? shape close

/--
Fast public subtree interval for an inorder node, assuming a constant-query
matching-open component.
-/
def subtreeIntervalOfInorderFastCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost openOverhead openQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (openAccess :
      BalancedParensMatchingOpenAccess shape openOverhead openQueryCost)
    (idx : Nat) : Costed (Option (Prod Nat Nat)) :=
  Costed.bind (closeOfInorderCosted access idx) fun close? =>
    match close? with
    | none => Costed.pure none
    | some close =>
        Costed.bind (openAccess.matchingOpenCosted close) fun open? =>
          match open? with
          | none => Costed.pure none
          | some openPos =>
              Costed.bind (access.rankCosted false openPos) fun lo =>
                Costed.map (fun hi => some (lo, hi))
                  (access.rankCosted false (close + 1))

theorem subtreeIntervalOfInorderFastCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost openOverhead openQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (openAccess :
      BalancedParensMatchingOpenAccess shape openOverhead openQueryCost)
    (idx : Nat) :
    (subtreeIntervalOfInorderFastCosted access openAccess idx).cost <=
      queryCost + openQueryCost + 2 * queryCost := by
  unfold subtreeIntervalOfInorderFastCosted
  have hcloseCost := closeOfInorderCosted_cost_le access idx
  cases hcloseVal : (closeOfInorderCosted access idx).value with
  | none =>
      simp [Costed.bind, Costed.pure, hcloseVal]
      omega
  | some close =>
      have hopenCost := openAccess.matchingOpen_cost_le close
      cases hopenVal : (openAccess.matchingOpenCosted close).value with
      | none =>
          simp [Costed.bind, hcloseVal, hopenVal]
          omega
      | some openPos =>
          have hloCost :=
            RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_cost_le
              access false openPos
          have hhiCost :=
            RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_cost_le
              access false (close + 1)
          simp [Costed.bind, Costed.map, Costed.pure, hcloseVal, hopenVal]
          omega

theorem subtreeIntervalOfInorderFastCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost openOverhead openQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (openAccess :
      BalancedParensMatchingOpenAccess shape openOverhead openQueryCost)
    (idx : Nat) :
    (subtreeIntervalOfInorderFastCosted access openAccess idx).erase =
      subtreeIntervalOfInorder? shape idx := by
  unfold subtreeIntervalOfInorderFastCosted subtreeIntervalOfInorder?
  rw [Costed.erase_bind]
  rw [closeOfInorderCosted_erase access idx]
  cases hclose : RMQ.SuccinctSpace.bpCloseOfInorder? shape idx with
  | none =>
      simp
  | some close =>
      simp only
      have hcloseBound :=
        RMQ.SuccinctSpace.bpCloseOfInorder?_bounds shape hclose
      rw [Costed.erase_bind]
      rw [openAccess.matchingOpen_erase_of_lt hcloseBound]
      cases hopen : matchingOpenOfClose? shape close with
      | none =>
          simp
      | some openPos =>
          simp only
          rw [Costed.erase_bind]
          rw [RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_erase
            access false openPos]
          rw [Costed.erase_map]
          rw [RMQ.SuccinctSpace.BalancedParensAccess.rankCosted_erase
            access false (close + 1)]
          simp [RMQ.SuccinctSpace.bpParensOfShape_bits]

theorem shapeAccessFastSubtreeIntervalProfile
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost openOverhead openQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (openAccess :
      BalancedParensMatchingOpenAccess shape openOverhead openQueryCost) :
    forall idx,
      (subtreeIntervalOfInorderFastCosted access openAccess idx).cost <=
          queryCost + openQueryCost + 2 * queryCost /\
        (subtreeIntervalOfInorderFastCosted access openAccess idx).erase =
          subtreeIntervalOfInorder? shape idx := by
  intro idx
  exact ⟨subtreeIntervalOfInorderFastCosted_cost_le access openAccess idx,
    subtreeIntervalOfInorderFastCosted_erase access openAccess idx⟩

/-- Reference enclose query for an opening parenthesis position. -/
def encloseOpenOfOpen?
    (shape : RMQ.Cartesian.CartesianShape)
    (openPos : Nat) : Option Nat :=
  if bpPrefixExcess shape openPos = 0 then
    none
  else
    matchingOpenSearchRef shape (bpPrefixExcess shape openPos - 1)
      (openPos - 1)

/-- Reference enclose query for the node at an inorder index. -/
def encloseOpenOfInorder?
    (shape : RMQ.Cartesian.CartesianShape)
    (idx : Nat) : Option Nat :=
  match RMQ.SuccinctSpace.bpCloseOfInorder? shape idx with
  | none => none
  | some close =>
      match matchingOpenOfClose? shape close with
      | none => none
      | some openPos => encloseOpenOfOpen? shape openPos

/--
Public tree-navigation component for fast BP navigation.

This packages matching-open and enclose-open queries together. `payloadBits`
accounts for modeled stored payload, the exactness fields are proof-only, and
`queryCost` is the model charge for either tree-navigation query.
-/
structure BalancedParensTreeNavigationAccess
    (shape : RMQ.Cartesian.CartesianShape)
    (overhead queryCost : Nat) where
  payloadBits : Nat
  payloadBits_le_overhead : payloadBits <= overhead
  matchingOpenCosted : Nat -> Costed (Option Nat)
  encloseOpenCosted : Nat -> Costed (Option Nat)
  matchingOpen_cost_le :
    forall close, (matchingOpenCosted close).cost <= queryCost
  encloseOpen_cost_le :
    forall openPos, (encloseOpenCosted openPos).cost <= queryCost
  matchingOpen_erase_of_lt :
    forall {close}, close < shape.bpCode.length ->
      (matchingOpenCosted close).erase =
        matchingOpenOfClose? shape close
  encloseOpen_erase_of_lt :
    forall {openPos}, openPos < shape.bpCode.length ->
      (encloseOpenCosted openPos).erase =
        encloseOpenOfOpen? shape openPos

def BalancedParensTreeNavigationAccess.toMatchingOpenAccess
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (treeAccess :
      BalancedParensTreeNavigationAccess shape overhead queryCost) :
    BalancedParensMatchingOpenAccess shape overhead queryCost where
  payloadBits := treeAccess.payloadBits
  payloadBits_le_overhead := treeAccess.payloadBits_le_overhead
  matchingOpenCosted := treeAccess.matchingOpenCosted
  matchingOpen_cost_le := treeAccess.matchingOpen_cost_le
  matchingOpen_erase_of_lt := treeAccess.matchingOpen_erase_of_lt

/-- Fast public enclose query for the node at an inorder index. -/
def encloseOpenOfInorderFastCosted
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost treeOverhead treeQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (treeAccess :
      BalancedParensTreeNavigationAccess shape treeOverhead treeQueryCost)
    (idx : Nat) : Costed (Option Nat) :=
  Costed.bind (closeOfInorderCosted access idx) fun close? =>
    match close? with
    | none => Costed.pure none
    | some close =>
        Costed.bind (treeAccess.matchingOpenCosted close) fun open? =>
          match open? with
          | none => Costed.pure none
          | some openPos => treeAccess.encloseOpenCosted openPos

theorem encloseOpenOfInorderFastCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost treeOverhead treeQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (treeAccess :
      BalancedParensTreeNavigationAccess shape treeOverhead treeQueryCost)
    (idx : Nat) :
    (encloseOpenOfInorderFastCosted access treeAccess idx).cost <=
      queryCost + treeQueryCost + treeQueryCost := by
  unfold encloseOpenOfInorderFastCosted
  have hcloseCost := closeOfInorderCosted_cost_le access idx
  cases hcloseVal : (closeOfInorderCosted access idx).value with
  | none =>
      simp [Costed.bind, Costed.pure, hcloseVal]
      omega
  | some close =>
      have hopenCost := treeAccess.matchingOpen_cost_le close
      cases hopenVal : (treeAccess.matchingOpenCosted close).value with
      | none =>
          simp [Costed.bind, hcloseVal, hopenVal]
          omega
      | some openPos =>
          have hencloseCost := treeAccess.encloseOpen_cost_le openPos
          simp [Costed.bind, hcloseVal, hopenVal]
          omega

theorem encloseOpenOfInorderFastCosted_erase
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost treeOverhead treeQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (treeAccess :
      BalancedParensTreeNavigationAccess shape treeOverhead treeQueryCost)
    (idx : Nat) :
    (encloseOpenOfInorderFastCosted access treeAccess idx).erase =
      encloseOpenOfInorder? shape idx := by
  unfold encloseOpenOfInorderFastCosted encloseOpenOfInorder?
  rw [Costed.erase_bind]
  rw [closeOfInorderCosted_erase access idx]
  cases hclose : RMQ.SuccinctSpace.bpCloseOfInorder? shape idx with
  | none =>
      simp
  | some close =>
      have hcloseBound :=
        RMQ.SuccinctSpace.bpCloseOfInorder?_bounds shape hclose
      simp only
      rw [Costed.erase_bind]
      rw [treeAccess.matchingOpen_erase_of_lt hcloseBound]
      cases hopen : matchingOpenOfClose? shape close with
      | none =>
          simp
      | some openPos =>
          have hopenNearest :=
            matchingOpenOfClose?_nearest_equal_excess_of_bpCloseOfInorder?
              hclose hopen
          have hopenBound : openPos < shape.bpCode.length := by
            omega
          simp only
          rw [treeAccess.encloseOpen_erase_of_lt hopenBound]

theorem shapeAccessEncloseOpenProfile
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost treeOverhead treeQueryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost)
    (treeAccess :
      BalancedParensTreeNavigationAccess shape treeOverhead treeQueryCost) :
    forall idx,
      (encloseOpenOfInorderFastCosted access treeAccess idx).cost <=
          queryCost + treeQueryCost + treeQueryCost /\
        (encloseOpenOfInorderFastCosted access treeAccess idx).erase =
          encloseOpenOfInorder? shape idx := by
  intro idx
  exact ⟨encloseOpenOfInorderFastCosted_cost_le access treeAccess idx,
    encloseOpenOfInorderFastCosted_erase access treeAccess idx⟩

/-- Lookup an optional value from a dense optional table. -/
def optionTableLookup (table : List (Option Nat)) (idx : Nat) : Option Nat :=
  match table[idx]? with
  | none => none
  | some value => value

theorem optionTableLookup_map_range_of_lt
    (f : Nat -> Option Nat) {len idx : Nat}
    (hidx : idx < len) :
    optionTableLookup ((List.range len).map f) idx = f idx := by
  unfold optionTableLookup
  simp [List.getElem?_map, List.getElem?_range hidx]

/-- Dense concrete matching-open/enclose table for one BP shape. -/
structure ConcreteMatchingOpenEncloseDirectory
    (shape : RMQ.Cartesian.CartesianShape) where
  matchingOpenTable : List (Option Nat)
  encloseOpenTable : List (Option Nat)
  matchingOpenTable_eq :
    matchingOpenTable =
      (List.range shape.bpCode.length).map
        (fun close => matchingOpenOfClose? shape close)
  encloseOpenTable_eq :
    encloseOpenTable =
      (List.range shape.bpCode.length).map
        (fun openPos => encloseOpenOfOpen? shape openPos)

/-- Dense payload budget for the concrete matching-open/enclose table. -/
def concreteMatchingOpenEncloseOverhead
    (shape : RMQ.Cartesian.CartesianShape) : Nat :=
  2 * shape.bpCode.length

/-- Modeled query cost for one dense matching-open/enclose table read. -/
def concreteMatchingOpenEncloseQueryCost : Nat := 1

def concreteMatchingOpenEncloseDirectory
    (shape : RMQ.Cartesian.CartesianShape) :
    ConcreteMatchingOpenEncloseDirectory shape where
  matchingOpenTable :=
    (List.range shape.bpCode.length).map
      (fun close => matchingOpenOfClose? shape close)
  encloseOpenTable :=
    (List.range shape.bpCode.length).map
      (fun openPos => encloseOpenOfOpen? shape openPos)
  matchingOpenTable_eq := rfl
  encloseOpenTable_eq := rfl

namespace ConcreteMatchingOpenEncloseDirectory

def payloadBits
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape) : Nat :=
  directory.matchingOpenTable.length + directory.encloseOpenTable.length

theorem payloadBits_le_overhead
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape) :
    directory.payloadBits <= concreteMatchingOpenEncloseOverhead shape := by
  unfold payloadBits concreteMatchingOpenEncloseOverhead
  rw [directory.matchingOpenTable_eq, directory.encloseOpenTable_eq]
  simp
  omega

def matchingOpenCosted
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape)
    (close : Nat) : Costed (Option Nat) :=
  Costed.tickValue concreteMatchingOpenEncloseQueryCost
    (optionTableLookup directory.matchingOpenTable close)

def encloseOpenCosted
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape)
    (openPos : Nat) : Costed (Option Nat) :=
  Costed.tickValue concreteMatchingOpenEncloseQueryCost
    (optionTableLookup directory.encloseOpenTable openPos)

theorem matchingOpenCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape)
    (close : Nat) :
    (directory.matchingOpenCosted close).cost <=
      concreteMatchingOpenEncloseQueryCost := by
  simp [matchingOpenCosted]

theorem encloseOpenCosted_cost_le
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape)
    (openPos : Nat) :
    (directory.encloseOpenCosted openPos).cost <=
      concreteMatchingOpenEncloseQueryCost := by
  simp [encloseOpenCosted]

theorem matchingOpenCosted_erase_of_lt
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape)
    {close : Nat}
    (hclose : close < shape.bpCode.length) :
    (directory.matchingOpenCosted close).erase =
      matchingOpenOfClose? shape close := by
  unfold matchingOpenCosted
  simp [Costed.erase]
  rw [directory.matchingOpenTable_eq]
  exact optionTableLookup_map_range_of_lt
    (fun close => matchingOpenOfClose? shape close) hclose

theorem encloseOpenCosted_erase_of_lt
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape)
    {openPos : Nat}
    (hopen : openPos < shape.bpCode.length) :
    (directory.encloseOpenCosted openPos).erase =
      encloseOpenOfOpen? shape openPos := by
  unfold encloseOpenCosted
  simp [Costed.erase]
  rw [directory.encloseOpenTable_eq]
  exact optionTableLookup_map_range_of_lt
    (fun openPos => encloseOpenOfOpen? shape openPos) hopen

def treeNavigationAccess
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape) :
    BalancedParensTreeNavigationAccess shape
      (concreteMatchingOpenEncloseOverhead shape)
      concreteMatchingOpenEncloseQueryCost where
  payloadBits := directory.payloadBits
  payloadBits_le_overhead := directory.payloadBits_le_overhead
  matchingOpenCosted := directory.matchingOpenCosted
  encloseOpenCosted := directory.encloseOpenCosted
  matchingOpen_cost_le := directory.matchingOpenCosted_cost_le
  encloseOpen_cost_le := directory.encloseOpenCosted_cost_le
  matchingOpen_erase_of_lt := directory.matchingOpenCosted_erase_of_lt
  encloseOpen_erase_of_lt := directory.encloseOpenCosted_erase_of_lt

theorem profile
    {shape : RMQ.Cartesian.CartesianShape}
    (directory : ConcreteMatchingOpenEncloseDirectory shape) :
    directory.payloadBits <= concreteMatchingOpenEncloseOverhead shape /\
      (forall close,
        (directory.matchingOpenCosted close).cost <=
          concreteMatchingOpenEncloseQueryCost) /\
      (forall openPos,
        (directory.encloseOpenCosted openPos).cost <=
          concreteMatchingOpenEncloseQueryCost) /\
      (forall {close : Nat},
        close < shape.bpCode.length ->
          (directory.matchingOpenCosted close).erase =
            matchingOpenOfClose? shape close) /\
      (forall {openPos : Nat},
        openPos < shape.bpCode.length ->
          (directory.encloseOpenCosted openPos).erase =
            encloseOpenOfOpen? shape openPos) := by
  exact ⟨directory.payloadBits_le_overhead,
    directory.matchingOpenCosted_cost_le,
    directory.encloseOpenCosted_cost_le,
    by intro close hclose
       exact directory.matchingOpenCosted_erase_of_lt hclose,
    by intro openPos hopen
       exact directory.encloseOpenCosted_erase_of_lt hopen⟩

end ConcreteMatchingOpenEncloseDirectory

def concreteMatchingOpenAccess
    (shape : RMQ.Cartesian.CartesianShape) :
    BalancedParensMatchingOpenAccess shape
      (concreteMatchingOpenEncloseOverhead shape)
      concreteMatchingOpenEncloseQueryCost :=
  BalancedParensTreeNavigationAccess.toMatchingOpenAccess
    (ConcreteMatchingOpenEncloseDirectory.treeNavigationAccess
      (concreteMatchingOpenEncloseDirectory shape))

theorem concreteShapeAccessFastSubtreeIntervalProfile
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost) :
    forall idx,
      (subtreeIntervalOfInorderFastCosted access
          (concreteMatchingOpenAccess shape) idx).cost <=
          queryCost + concreteMatchingOpenEncloseQueryCost + 2 * queryCost /\
        (subtreeIntervalOfInorderFastCosted access
          (concreteMatchingOpenAccess shape) idx).erase =
          subtreeIntervalOfInorder? shape idx := by
  exact
    shapeAccessFastSubtreeIntervalProfile access
      (concreteMatchingOpenAccess shape)

theorem concreteShapeAccessEncloseOpenProfile
    {shape : RMQ.Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (access :
      BalancedParensAccess (bpParensOfShape shape) overhead queryCost) :
    forall idx,
      (encloseOpenOfInorderFastCosted access
          (concreteMatchingOpenEncloseDirectory shape).treeNavigationAccess
          idx).cost <=
          queryCost + concreteMatchingOpenEncloseQueryCost +
            concreteMatchingOpenEncloseQueryCost /\
        (encloseOpenOfInorderFastCosted access
          (concreteMatchingOpenEncloseDirectory shape).treeNavigationAccess
          idx).erase =
          encloseOpenOfInorder? shape idx := by
  exact
    shapeAccessEncloseOpenProfile access
      (concreteMatchingOpenEncloseDirectory shape).treeNavigationAccess

/--
The current compact close/LCA component returns close positions, not matching
opens. On the one-node Cartesian shape, singleton LCA-close semantics return
the node close, while matching-open semantics return the opening prefix
position. This blocks reusing the existing close/LCA query as the fast
matching-open component.
-/
theorem singletonLcaCloseSemantics_not_matchingOpen_counterexample :
    exists (shape : RMQ.Cartesian.CartesianShape) (idx close : Nat),
      RMQ.SuccinctSpace.bpCloseOfInorder? shape idx = some close /\
        RMQ.SuccinctSpace.bpCloseOfInorder? shape
            (RMQ.scanWindow shape.representative idx 1) =
          some close /\
        Not (matchingOpenOfClose? shape close = some close) := by
  refine ⟨RMQ.Cartesian.CartesianShape.node
      RMQ.Cartesian.CartesianShape.empty
      RMQ.Cartesian.CartesianShape.empty, 0, 1, ?_, ?_, ?_⟩
  · simp [RMQ.SuccinctSpace.bpCloseOfInorder?,
      RMQ.Cartesian.CartesianShape.size,
      RMQ.Cartesian.CartesianShape.bpCode]
  · simp [RMQ.SuccinctSpace.bpCloseOfInorder?, RMQ.scanWindow,
      RMQ.Cartesian.CartesianShape.size,
      RMQ.Cartesian.CartesianShape.bpCode]
  · simp [matchingOpenOfClose?, matchingOpenSearchRef, bpPrefixExcess,
      RMQ.Cartesian.CartesianShape.bpCode, RMQ.Succinct.rankPrefix]

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
