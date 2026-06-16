import RMQ.Core.Cartesian

/-!
# Cartesian shapes and RMQ behavior

This module starts the shape layer behind Cartesian-tree RMQ equivalence and
Fischer-Heun-style block signatures.

The `RoseTree` used for LCA proofs deliberately omits empty children. That is
ergonomic for paths, but it forgets whether a single child was originally a left
or right Cartesian child. `CartesianShape` keeps explicit empty children, so it
is the right object for shape signatures and counting arguments.
-/

namespace RMQ

namespace Cartesian

/-- Binary Cartesian-tree shape with explicit empty children. -/
inductive CartesianShape where
  | empty
  | node (left right : CartesianShape)
deriving DecidableEq, Repr

namespace CartesianShape

/-- Number of real nodes in a Cartesian shape. -/
def size : CartesianShape -> Nat
  | empty => 0
  | node left right => left.size + 1 + right.size

/-- Root offset, measured by the size of the explicit left child. -/
def rootOffset? : CartesianShape -> Option Nat
  | empty => none
  | node left _right => some left.size

end CartesianShape

/--
The explicit binary shape of the Cartesian tree over `[left, left + len)`.

Unlike `treeRange`, this keeps empty left/right children, so one-child nodes
retain their orientation.
-/
def shapeRange (xs : List Int) (left len : Nat) : CartesianShape :=
  match len with
  | 0 => CartesianShape.empty
  | len' + 1 =>
      let width := len' + 1
      let root := scanWindow xs left width
      let leftLen := root - left
      let rightStart := root + 1
      let rightLen := left + width - rightStart
      CartesianShape.node
        (shapeRange xs left leftLen)
        (shapeRange xs rightStart rightLen)
termination_by len
decreasing_by
  · have hbounds := scanWindow_bounds xs left (len' + 1) (by omega)
    omega
  · have hbounds := scanWindow_bounds xs left (len' + 1) (by omega)
    omega

/-- The explicit Cartesian shape over a whole list. -/
def shape (xs : List Int) : CartesianShape :=
  shapeRange xs 0 xs.length

theorem shapeRange_size
    (xs : List Int) (left len : Nat) :
    (shapeRange xs left len).size = len := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left, (shapeRange xs left len).size = len)
      len
      (fun len ih left => by
        cases len with
        | zero =>
            simp [shapeRange, CartesianShape.size]
        | succ len' =>
            let width := len' + 1
            let root := scanWindow xs left width
            let leftLen := root - left
            let rightStart := root + 1
            let rightLen := left + width - rightStart
            have hbounds : left <= root /\ root < left + width :=
              scanWindow_bounds xs left width (by omega)
            have hleftLen_lt : leftLen < len' + 1 := by
              unfold leftLen
              omega
            have hrightLen_lt : rightLen < len' + 1 := by
              unfold rightLen rightStart
              omega
            have hleftSize :
                (shapeRange xs left leftLen).size = leftLen :=
              ih leftLen hleftLen_lt left
            have hrightSize :
                (shapeRange xs rightStart rightLen).size = rightLen :=
              ih rightLen hrightLen_lt rightStart
            simp [shapeRange, CartesianShape.size]
            rw [hleftSize, hrightSize]
            omega)
      left

theorem shape_size (xs : List Int) :
    (shape xs).size = xs.length := by
  simp [shape, shapeRange_size]

theorem rootOffset?_shapeRange
    (xs : List Int) (left len : Nat) (hlen : 0 < len) :
    (shapeRange xs left len).rootOffset? =
      some (scanWindow xs left len - left) := by
  cases len with
  | zero =>
      omega
  | succ len' =>
      simp [shapeRange, CartesianShape.rootOffset?, shapeRange_size]

/--
Two arrays have the same RMQ behavior when every corresponding nonempty
half-open window has the same leftmost-minimum index.
-/
def SameRMQBehavior (xs ys : List Int) : Prop :=
  xs.length = ys.length /\
    forall {left len : Nat},
      0 < len ->
        left + len <= xs.length ->
          scanWindow xs left len = scanWindow ys left len

theorem shapeRange_eq_of_sameRMQBehavior
    {xs ys : List Int} (hbehavior : SameRMQBehavior xs ys)
    {left len : Nat} (hbound : left + len <= xs.length) :
    shapeRange xs left len = shapeRange ys left len := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left,
          left + len <= xs.length ->
            shapeRange xs left len = shapeRange ys left len)
      len
      (fun len ih left hbound => by
        cases len with
        | zero =>
            simp [shapeRange]
        | succ len' =>
            let width := len' + 1
            let root := scanWindow xs left width
            let leftLen := root - left
            let rightStart := root + 1
            let rightLen := left + width - rightStart
            have hroot :
                scanWindow xs left width = scanWindow ys left width :=
              hbehavior.2 (by omega) hbound
            have hbounds : left <= root /\ root < left + width :=
              scanWindow_bounds xs left width (by omega)
            have hleftLen_lt : leftLen < len' + 1 := by
              unfold leftLen
              omega
            have hrightLen_lt : rightLen < len' + 1 := by
              unfold rightLen rightStart
              omega
            have hleftBound : left + leftLen <= xs.length := by
              unfold leftLen
              omega
            have hrightBound : rightStart + rightLen <= xs.length := by
              unfold rightStart rightLen
              omega
            have hleftShape :
                shapeRange xs left leftLen =
                  shapeRange ys left leftLen :=
              ih leftLen hleftLen_lt left hleftBound
            have hrightShape :
                shapeRange xs rightStart rightLen =
                  shapeRange ys rightStart rightLen :=
              ih rightLen hrightLen_lt rightStart hrightBound
            have hleftShape' :
                shapeRange xs left
                    (scanWindow ys left (len' + 1) - left) =
                  shapeRange ys left
                    (scanWindow ys left (len' + 1) - left) := by
              simpa [width, root, leftLen, hroot] using hleftShape
            have hrightShape' :
                shapeRange xs (scanWindow ys left (len' + 1) + 1)
                    (left + (len' + 1) -
                      (scanWindow ys left (len' + 1) + 1)) =
                  shapeRange ys (scanWindow ys left (len' + 1) + 1)
                    (left + (len' + 1) -
                      (scanWindow ys left (len' + 1) + 1)) := by
              simpa [width, root, rightStart, rightLen, hroot] using
                hrightShape
            simp [shapeRange]
            rw [hroot]
            constructor
            · exact hleftShape'
            · exact hrightShape')
      left hbound

theorem shape_eq_of_sameRMQBehavior
    {xs ys : List Int} (hbehavior : SameRMQBehavior xs ys) :
    shape xs = shape ys := by
  unfold shape
  rw [← hbehavior.1]
  exact shapeRange_eq_of_sameRMQBehavior
    (left := 0) (len := xs.length) hbehavior (by simp)

theorem scanWindow_eq_of_shapeRange_eq
    {xs ys : List Int} {left len : Nat}
    (hlen : 0 < len)
    (hshape : shapeRange xs left len = shapeRange ys left len) :
    scanWindow xs left len = scanWindow ys left len := by
  have hoffset := congrArg CartesianShape.rootOffset? hshape
  rw [rootOffset?_shapeRange xs left len hlen,
    rootOffset?_shapeRange ys left len hlen] at hoffset
  injection hoffset with hsub
  have hxbounds := scanWindow_bounds xs left len hlen
  have hybounds := scanWindow_bounds ys left len hlen
  omega

theorem sameRMQBehavior_of_shapeRange_eq
    {xs ys : List Int}
    (hlength : xs.length = ys.length)
    (hshape :
      forall {left len : Nat},
        left + len <= xs.length ->
          shapeRange xs left len = shapeRange ys left len) :
    SameRMQBehavior xs ys := by
  refine ⟨hlength, ?_⟩
  intro left len hlen hbound
  exact scanWindow_eq_of_shapeRange_eq hlen (hshape hbound)

/--
Range-shape equivalence is exactly RMQ-behavior equivalence when stated over
all syntactic subranges.
-/
theorem sameRMQBehavior_iff_shapeRange_eq
    (xs ys : List Int) :
    SameRMQBehavior xs ys ↔
      xs.length = ys.length /\
        forall {left len : Nat},
          left + len <= xs.length ->
            shapeRange xs left len = shapeRange ys left len := by
  constructor
  · intro hbehavior
    exact ⟨hbehavior.1, fun hbound =>
      shapeRange_eq_of_sameRMQBehavior hbehavior hbound⟩
  · intro h
    exact sameRMQBehavior_of_shapeRange_eq h.1 h.2

/-- Proof-side universe of binary Cartesian shapes of a fixed size. -/
inductive ShapeOfSize : Nat -> CartesianShape -> Prop where
  | empty : ShapeOfSize 0 CartesianShape.empty
  | node {leftSize rightSize : Nat} {left right : CartesianShape} :
      ShapeOfSize leftSize left ->
        ShapeOfSize rightSize right ->
          ShapeOfSize (leftSize + 1 + rightSize)
            (CartesianShape.node left right)

theorem ShapeOfSize.size_eq
    {n : Nat} {shape : CartesianShape}
    (hshape : ShapeOfSize n shape) :
    shape.size = n := by
  induction hshape with
  | empty =>
      simp [CartesianShape.size]
  | node hleft hright ihleft ihright =>
      simp [CartesianShape.size, ihleft, ihright]

/--
Computable universe of binary Cartesian shapes of a fixed size. Its length is
the Catalan number for that size, witnessed below by `shapeCount_succ`.
-/
def shapesOfSize (n : Nat) : List CartesianShape :=
  match n with
  | 0 => [CartesianShape.empty]
  | n' + 1 =>
      (List.finRange (n' + 1)).flatMap fun split =>
        let leftSize := split.val
        let rightSize := n' - split.val
        (shapesOfSize leftSize).flatMap fun leftShape =>
          (shapesOfSize rightSize).map fun rightShape =>
            CartesianShape.node leftShape rightShape
termination_by n
decreasing_by
  · have hlt := split.isLt
    omega
  · exact split.isLt

/-- The finite shape count; this is the Catalan-count sequence for shapes. -/
def shapeCount (n : Nat) : Nat :=
  (shapesOfSize n).length

private theorem sum_map_const_nat {α : Type} (xs : List α) (n : Nat) :
    ((xs.map fun _ => n).sum) = xs.length * n := by
  simp [List.map_const']

@[simp] theorem shapeCount_zero : shapeCount 0 = 1 := by
  simp [shapeCount, shapesOfSize]

theorem shapeCount_succ (n : Nat) :
    shapeCount (n + 1) =
      ((List.finRange (n + 1)).map fun split =>
        shapeCount split.val * shapeCount (n - split.val)).sum := by
  simp [shapeCount, shapesOfSize, List.length_flatMap, sum_map_const_nat]

theorem mem_shapesOfSize_shapeOfSize
    {n : Nat} {shape : CartesianShape}
    (hmem : shape ∈ shapesOfSize n) :
    ShapeOfSize n shape := by
  exact
    Nat.strongRecOn
      (motive := fun n =>
        forall {shape : CartesianShape},
          shape ∈ shapesOfSize n -> ShapeOfSize n shape)
      n
      (fun n ih shape hmem => by
        cases n with
        | zero =>
            simp [shapesOfSize] at hmem
            subst shape
            exact ShapeOfSize.empty
        | succ n' =>
            simp [shapesOfSize] at hmem
            rcases hmem with ⟨split, _hsplit_mem, leftShape, hleft_mem,
              rightShape, hright_mem, hshape⟩
            subst shape
            have hleftSize :
                ShapeOfSize split.val leftShape :=
              ih split.val split.isLt hleft_mem
            have hright_lt : n' - split.val < n' + 1 := by
              have hle : split.val <= n' :=
                Nat.lt_succ_iff.mp split.isLt
              omega
            have hrightSize :
                ShapeOfSize (n' - split.val) rightShape :=
              ih (n' - split.val) hright_lt hright_mem
            have hnode :
                ShapeOfSize (split.val + 1 + (n' - split.val))
                  (CartesianShape.node leftShape rightShape) :=
              ShapeOfSize.node hleftSize hrightSize
            have hsize : split.val + 1 + (n' - split.val) = n' + 1 := by
              have hle : split.val <= n' :=
                Nat.lt_succ_iff.mp split.isLt
              omega
            simpa [hsize] using hnode)
      hmem

theorem shapeOfSize_mem_shapesOfSize
    {n : Nat} {shape : CartesianShape}
    (hshape : ShapeOfSize n shape) :
    shape ∈ shapesOfSize n := by
  induction hshape with
  | empty =>
      simp [shapesOfSize]
  | node hleft hright ihleft ihright =>
      rename_i leftSize rightSize left right
      let split : Fin (leftSize + rightSize + 1) :=
        ⟨leftSize, by omega⟩
      have hrightSize :
          leftSize + rightSize - split.val = rightSize := by
        simp [split]
      have hmem :
          CartesianShape.node left right ∈
            shapesOfSize (leftSize + rightSize + 1) := by
        simp [shapesOfSize]
        refine ⟨split, ?_, ?_, ?_⟩
        · rw [List.finRange]
          exact (List.mem_ofFn).2 ⟨split, rfl⟩
        · simpa [split] using ihleft
        · simpa [hrightSize] using ihright
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem

theorem mem_shapesOfSize_iff_shapeOfSize
    {n : Nat} {shape : CartesianShape} :
    shape ∈ shapesOfSize n ↔ ShapeOfSize n shape := by
  constructor
  · exact mem_shapesOfSize_shapeOfSize
  · exact shapeOfSize_mem_shapesOfSize

theorem shapeRange_shapeOfSize
    (xs : List Int) (left len : Nat) :
    ShapeOfSize len (shapeRange xs left len) := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left, ShapeOfSize len (shapeRange xs left len))
      len
      (fun len ih left => by
        cases len with
        | zero =>
            simp [shapeRange]
            exact ShapeOfSize.empty
        | succ len' =>
            let width := len' + 1
            let root := scanWindow xs left width
            let leftLen := root - left
            let rightStart := root + 1
            let rightLen := left + width - rightStart
            have hbounds : left <= root /\ root < left + width :=
              scanWindow_bounds xs left width (by omega)
            have hleftLen_lt : leftLen < len' + 1 := by
              unfold leftLen
              omega
            have hrightLen_lt : rightLen < len' + 1 := by
              unfold rightLen rightStart
              omega
            have hleftShape :
                ShapeOfSize leftLen (shapeRange xs left leftLen) :=
              ih leftLen hleftLen_lt left
            have hrightShape :
                ShapeOfSize rightLen (shapeRange xs rightStart rightLen) :=
              ih rightLen hrightLen_lt rightStart
            have hnode :
                ShapeOfSize (leftLen + 1 + rightLen)
                  (CartesianShape.node
                    (shapeRange xs left leftLen)
                    (shapeRange xs rightStart rightLen)) :=
              ShapeOfSize.node hleftShape hrightShape
            have hsize : leftLen + 1 + rightLen = len' + 1 := by
              unfold leftLen rightLen rightStart
              omega
            have hnode' :
                ShapeOfSize (leftLen + 1 + rightLen)
                  (CartesianShape.node
                    (shapeRange xs left
                      (scanWindow xs left (len' + 1) - left))
                    (shapeRange xs
                      (scanWindow xs left (len' + 1) + 1)
                      (left + (len' + 1) -
                        (scanWindow xs left (len' + 1) + 1)))) := by
              simpa [width, root, leftLen, rightStart, rightLen] using hnode
            have htarget :
                ShapeOfSize (leftLen + 1 + rightLen)
                  (shapeRange xs left (len' + 1)) := by
              simpa [shapeRange] using hnode'
            simpa [hsize] using htarget)
      left

theorem shape_shapeOfSize (xs : List Int) :
    ShapeOfSize xs.length (shape xs) := by
  unfold shape
  exact shapeRange_shapeOfSize xs 0 xs.length

/--
Block signatures are explicit Cartesian shapes. This is the bridge from the
RMQ-characterization theorem above to the Catalan-count/microtable
argument.
-/
def blockSignature (xs : List Int) (start len : Nat) : CartesianShape :=
  shapeRange xs start len

theorem blockSignature_shapeOfSize
    (xs : List Int) (start len : Nat) :
    ShapeOfSize len (blockSignature xs start len) := by
  unfold blockSignature
  exact shapeRange_shapeOfSize xs start len

example : shape [5, 2, 7, 1, 3] =
    CartesianShape.node
      (CartesianShape.node
        (CartesianShape.node CartesianShape.empty CartesianShape.empty)
        (CartesianShape.node CartesianShape.empty CartesianShape.empty))
      (CartesianShape.node CartesianShape.empty CartesianShape.empty) := by
  native_decide

example : blockSignature [4, 1, 1, 2] 0 4 =
    CartesianShape.node
      (CartesianShape.node CartesianShape.empty CartesianShape.empty)
      (CartesianShape.node
        CartesianShape.empty
        (CartesianShape.node CartesianShape.empty CartesianShape.empty)) := by
  native_decide

example : (List.map shapeCount [0, 1, 2, 3, 4]) = [1, 1, 2, 5, 14] := by
  native_decide

end Cartesian

end RMQ
