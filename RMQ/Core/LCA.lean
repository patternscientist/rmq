import RMQ.Core.Backend

/-!
# LCA-facing Euler traces

This module starts the correctness-first bridge from RMQ to LCA. It introduces
a small rose-tree model, proves the Euler-depth plus/minus-one invariant for generated
depth traces, and packages the RMQ-backed "minimum-depth tour node between two
first occurrences" reduction.
-/

namespace RMQ

/-- A tiny proof-friendly rooted tree with natural-number node labels. -/
inductive RoseTree where
  | node (label : Nat) (children : List RoseTree)
deriving Repr

namespace RoseTree

mutual
  /--
  Euler-tour depth moves for a tree. A child descent contributes `+1`, and the
  corresponding return to the parent contributes `-1`.
  -/
  def eulerMoves : RoseTree -> List Int
    | node _ children => eulerMovesForest children

  /-- Euler-tour depth moves for a forest of children. -/
  def eulerMovesForest : List RoseTree -> List Int
    | [] => []
    | child :: rest => 1 :: (eulerMoves child ++ (-1) :: eulerMovesForest rest)
end

end RoseTree

/-- A depth move is one Euler step up or down. -/
def UnitDepthMove (move : Int) : Prop :=
  move = 1 \/ move = -1

/-- Every move in a list is an Euler unit step. -/
def UnitDepthMoves : List Int -> Prop
  | [] => True
  | move :: rest => UnitDepthMove move /\ UnitDepthMoves rest

theorem unitDepthMoves_append {xs ys : List Int} :
    UnitDepthMoves (xs ++ ys) <-> UnitDepthMoves xs /\ UnitDepthMoves ys := by
  induction xs with
  | nil =>
      simp [UnitDepthMoves]
  | cons move rest ih =>
      simp [UnitDepthMoves, ih, and_assoc]

mutual
  theorem roseTree_eulerMoves_unit (tree : RoseTree) :
      UnitDepthMoves tree.eulerMoves := by
    cases tree with
    | node _ children =>
        simpa [RoseTree.eulerMoves] using roseTree_eulerMovesForest_unit children

  theorem roseTree_eulerMovesForest_unit (forest : List RoseTree) :
      UnitDepthMoves (RoseTree.eulerMovesForest forest) := by
    cases forest with
    | nil =>
        simp [RoseTree.eulerMovesForest, UnitDepthMoves]
    | cons child rest =>
        have hchild : UnitDepthMoves child.eulerMoves :=
          roseTree_eulerMoves_unit child
        have hrest : UnitDepthMoves (RoseTree.eulerMovesForest rest) :=
          roseTree_eulerMovesForest_unit rest
        simp [RoseTree.eulerMovesForest, UnitDepthMoves, unitDepthMoves_append,
          hchild, hrest, UnitDepthMove]
end

/--
Depths obtained by starting at `start` and applying a list of Euler depth moves.
The result always includes the starting depth.
-/
def depthsFromMoves (start : Int) : List Int -> List Int
  | [] => [start]
  | move :: rest => start :: depthsFromMoves (start + move) rest

/-- Adjacent depth values differ by exactly one. -/
def AdjacentDepthsDifferByOne : List Int -> Prop
  | [] => True
  | [_] => True
  | a :: b :: rest =>
      (b = a + 1 \/ a = b + 1) /\ AdjacentDepthsDifferByOne (b :: rest)

theorem unitDepthMove_step (depth move : Int)
    (hmove : UnitDepthMove move) :
    (depth + move = depth + 1 \/ depth = depth + move + 1) := by
  rcases hmove with hmove | hmove
  · left
    omega
  · right
    omega

theorem depthsFromMoves_adjacent
    (start : Int) {moves : List Int}
    (hmoves : UnitDepthMoves moves) :
    AdjacentDepthsDifferByOne (depthsFromMoves start moves) := by
  induction moves generalizing start with
  | nil =>
      simp [depthsFromMoves, AdjacentDepthsDifferByOne]
  | cons move rest ih =>
      rcases hmoves with ⟨hmove, hrest⟩
      cases rest with
      | nil =>
          simp [depthsFromMoves, AdjacentDepthsDifferByOne]
          rcases hmove with hmove | hmove
          · exact Or.inl hmove
          · right
            omega
      | cons next tail =>
          exact ⟨unitDepthMove_step start move hmove,
            ih (start + move) hrest⟩

/-- Euler-tour depths for a tree rooted at `startDepth`. -/
def RoseTree.eulerDepthsAt (startDepth : Int) (tree : RoseTree) : List Int :=
  depthsFromMoves startDepth tree.eulerMoves

/-- Public Euler-tour depths, rooted at depth zero. -/
def RoseTree.eulerDepths (tree : RoseTree) : List Int :=
  tree.eulerDepthsAt 0

theorem RoseTree.eulerDepthsAt_adjacent
    (tree : RoseTree) (startDepth : Int) :
    AdjacentDepthsDifferByOne (tree.eulerDepthsAt startDepth) := by
  exact depthsFromMoves_adjacent startDepth (roseTree_eulerMoves_unit tree)

theorem RoseTree.eulerDepths_adjacent (tree : RoseTree) :
    AdjacentDepthsDifferByOne tree.eulerDepths := by
  exact tree.eulerDepthsAt_adjacent 0

/-- Find the first index containing `target`. -/
def firstIndexOf? {α : Type u} [DecidableEq α] (target : α) : List α -> Option Nat
  | [] => none
  | x :: xs =>
      if x = target then
        some 0
      else
        match firstIndexOf? target xs with
        | none => none
        | some idx => some (idx + 1)

theorem firstIndexOf?_lt_length
    {α : Type u} [DecidableEq α] {target : α} :
    forall {xs : List α} {idx : Nat},
      firstIndexOf? target xs = some idx -> idx < xs.length
  | [], _, h => by
      simp [firstIndexOf?] at h
  | x :: xs, idx, h => by
      unfold firstIndexOf? at h
      by_cases hx : x = target
      · simp [hx] at h
        cases h
        simp
      · simp [hx] at h
        cases htail : firstIndexOf? target xs with
        | none =>
            simp [htail] at h
        | some tailIdx =>
            simp [htail] at h
            have htail_lt :
                tailIdx < xs.length :=
              firstIndexOf?_lt_length (target := target) htail
            cases h
            simp
            omega

/--
An Euler trace pairs tour nodes with tour depths. The plus/minus-one invariant is kept as
data so later LCA proofs can consume traces independently of the tree generator.
-/
structure EulerTrace where
  nodes : List Nat
  depths : List Int
  length_eq : nodes.length = depths.length
  adjacent_depths : AdjacentDepthsDifferByOne depths

namespace EulerTrace

/-- First occurrence of a node label in the Euler tour. -/
def firstOccurrence? (trace : EulerTrace) (node : Nat) : Option Nat :=
  firstIndexOf? node trace.nodes

/-- Closed-over-positions, half-open-as-a-list-window interval between two tour positions. -/
def occurrenceWindow (i j : Nat) : Nat × Nat :=
  (Nat.min i j, Nat.max i j + 1)

theorem occurrenceWindow_valid
    (trace : EulerTrace) {u v i j : Nat}
    (hu : trace.firstOccurrence? u = some i)
    (hv : trace.firstOccurrence? v = some j) :
    ValidRange trace.depths (occurrenceWindow i j).1 (occurrenceWindow i j).2 := by
  have hi_nodes : i < trace.nodes.length :=
    firstIndexOf?_lt_length (target := u) hu
  have hj_nodes : j < trace.nodes.length :=
    firstIndexOf?_lt_length (target := v) hv
  have hi_depths : i < trace.depths.length := by
    simpa [trace.length_eq] using hi_nodes
  have hj_depths : j < trace.depths.length := by
    simpa [trace.length_eq] using hj_nodes
  have hmax_depths : Nat.max i j < trace.depths.length :=
    Nat.max_lt.2 ⟨hi_depths, hj_depths⟩
  have hmin_le_max : Nat.min i j <= Nat.max i j :=
    Nat.le_trans (Nat.min_le_left i j) (Nat.le_max_left i j)
  unfold occurrenceWindow
  constructor
  · omega
  · omega

/-- Query an RMQ backend over a tour-depth window and return the tour node there. -/
def minDepthNodeInWindow
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) : Option Nat :=
  match RMQBackend.queryBuilt backend left right with
  | none => none
  | some idx => trace.nodes[idx]?

theorem minDepthNodeInWindow_valid_exact
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    {left right : Nat}
    (hValid : ValidRange trace.depths left right) :
    exists idx node,
      minDepthNodeInWindow trace backend left right = some node /\
        trace.nodes[idx]? = some node /\
        LeftmostArgMin trace.depths left right idx := by
  let len := right - left
  have hlen : 0 < len := by
    unfold len
    omega
  have hbound : left + len <= trace.depths.length := by
    unfold len
    omega
  have hright : left + len = right := by
    unfold len
    omega
  have harg_scan := scanWindow_leftmost trace.depths left len hlen hbound
  let idx := scanWindow trace.depths left len
  have harg : LeftmostArgMin trace.depths left right idx := by
    simpa [idx, hright] using harg_scan
  have hquery :
      RMQBackend.queryBuilt backend left right = some idx :=
    backend.complete harg
  have hidx_depths : idx < trace.depths.length := by
    exact Nat.lt_of_lt_of_le harg.2.2.2.1 hValid.2
  have hidx_nodes : idx < trace.nodes.length := by
    rw [trace.length_eq]
    exact hidx_depths
  let node := trace.nodes[idx]'hidx_nodes
  have hnode : trace.nodes[idx]? = some node := by
    simp [node, hidx_nodes]
  refine ⟨idx, node, ?_, hnode, harg⟩
  unfold minDepthNodeInWindow
  rw [hquery]
  exact hnode

/--
The RMQ-backed LCA candidate: look up both first occurrences, query the minimum
depth over the inclusive tour-position span, and map the returned RMQ index back
to its tour node.
-/
def lcaCandidate
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) : Option Nat :=
  match trace.firstOccurrence? u, trace.firstOccurrence? v with
  | some i, some j =>
      let window := occurrenceWindow i j
      minDepthNodeInWindow trace backend window.1 window.2
  | _, _ => none

theorem lcaCandidate_valid_exact
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    {u v i j : Nat}
    (hu : trace.firstOccurrence? u = some i)
    (hv : trace.firstOccurrence? v = some j) :
    exists idx node,
      lcaCandidate trace backend u v = some node /\
        trace.nodes[idx]? = some node /\
        LeftmostArgMin trace.depths
          (occurrenceWindow i j).1 (occurrenceWindow i j).2 idx := by
  have hValid := trace.occurrenceWindow_valid hu hv
  rcases minDepthNodeInWindow_valid_exact trace backend hValid with
    ⟨idx, node, hres, hnode, harg⟩
  refine ⟨idx, node, ?_, hnode, harg⟩
  unfold lcaCandidate
  rw [hu, hv]
  exact hres

end EulerTrace

end RMQ
