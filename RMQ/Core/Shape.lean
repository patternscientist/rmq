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

private theorem fin_succ_inj {n : Nat} {i j : Fin n}
    (h : Fin.succ i = Fin.succ j) : i = j := by
  apply Fin.ext
  injection h with hval
  omega

private theorem nodup_ofFn {α : Type} {n : Nat} (f : Fin n -> α)
    (hinj : forall i j : Fin n, f i = f j -> i = j) :
    (List.ofFn f).Nodup := by
  induction n with
  | zero =>
      rw [List.ofFn_zero]
      simp
  | succ n ih =>
      rw [List.ofFn_succ]
      rw [List.nodup_cons]
      constructor
      · intro hx
        rw [List.mem_ofFn] at hx
        rcases hx with ⟨i, hi⟩
        have hfin :
            (0 : Fin (n + 1)) = Fin.succ i := by
          exact hinj 0 (Fin.succ i) hi.symm
        exact Fin.succ_ne_zero i hfin.symm
      · exact ih (fun i => f (Fin.succ i)) (by
          intro i j h
          exact fin_succ_inj (hinj (Fin.succ i) (Fin.succ j) h))

private theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  rw [List.finRange]
  exact nodup_ofFn (fun i : Fin n => i) (by
    intro i j h
    exact h)

private def boolLists : Nat -> List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolLists n).flatMap fun bits =>
      [false :: bits, true :: bits]

private theorem boolLists_length (n : Nat) :
    (boolLists n).length = 2 ^ n := by
  induction n with
  | zero =>
      simp [boolLists]
  | succ n ih =>
      simp [boolLists, List.length_flatMap, sum_map_const_nat]
      rw [ih, Nat.pow_succ]

private theorem mem_boolLists_of_length
    {bits : List Bool} {n : Nat} (hlen : bits.length = n) :
    bits ∈ boolLists n := by
  induction n generalizing bits with
  | zero =>
      cases bits with
      | nil =>
          simp [boolLists]
      | cons _ _ =>
          simp at hlen
  | succ n ih =>
      cases bits with
      | nil =>
          simp at hlen
      | cons b bits =>
          have htail : bits.length = n := by
            simp at hlen
            exact hlen
          have hmem := ih htail
          cases b <;> simp [boolLists, hmem]

namespace CartesianShape

/--
Full preorder code with explicit empty markers. A shape with `n` real nodes has
code length `2*n + 1`; nonempty codes start with `true`, so their tail lives in
the `2*n`-bit universe used by `shapeCount_le_four_pow`.
-/
def fullCode : CartesianShape -> List Bool
  | empty => [false]
  | node left right => true :: (left.fullCode ++ right.fullCode)

theorem fullCode_length (shape : CartesianShape) :
    shape.fullCode.length = 2 * shape.size + 1 := by
  induction shape with
  | empty =>
      simp [fullCode, size]
  | node left right ihleft ihright =>
      simp [fullCode, size, ihleft, ihright]
      omega

end CartesianShape

private def decodeFullCodeFuel :
    Nat -> List Bool -> Option (CartesianShape × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some (CartesianShape.empty, rest)
  | fuel + 1, true :: rest =>
      match decodeFullCodeFuel fuel rest with
      | none => none
      | some (left, rest') =>
          match decodeFullCodeFuel fuel rest' with
          | none => none
          | some (right, rest'') =>
              some (CartesianShape.node left right, rest'')

private theorem decodeFullCodeFuel_fullCode_append
    (shape : CartesianShape) (suffix : List Bool) {fuel : Nat}
    (hfuel : shape.fullCode.length <= fuel) :
    decodeFullCodeFuel fuel (shape.fullCode ++ suffix) =
      some (shape, suffix) := by
  induction shape generalizing fuel suffix with
  | empty =>
      cases fuel with
      | zero =>
          simp [CartesianShape.fullCode] at hfuel
      | succ _ =>
          simp [CartesianShape.fullCode, decodeFullCodeFuel]
  | node left right ihleft ihright =>
      cases fuel with
      | zero =>
          simp [CartesianShape.fullCode] at hfuel
      | succ fuel =>
          have hleftFuel : left.fullCode.length <= fuel := by
            rw [CartesianShape.fullCode_length] at hfuel ⊢
            simp [CartesianShape.size] at hfuel ⊢
            omega
          have hrightFuel : right.fullCode.length <= fuel := by
            rw [CartesianShape.fullCode_length] at hfuel ⊢
            simp [CartesianShape.size] at hfuel ⊢
            omega
          simp [CartesianShape.fullCode, decodeFullCodeFuel,
            ihleft (right.fullCode ++ suffix) hleftFuel,
            ihright suffix hrightFuel]

theorem CartesianShape.fullCode_injective
    {left right : CartesianShape}
    (hcode : left.fullCode = right.fullCode) :
    left = right := by
  have hlen : right.fullCode.length <= left.fullCode.length := by
    rw [hcode]
    exact Nat.le_refl _
  have hleft :=
    decodeFullCodeFuel_fullCode_append left []
      (fuel := left.fullCode.length) (by omega)
  have hright :=
    decodeFullCodeFuel_fullCode_append right []
      (fuel := left.fullCode.length) hlen
  rw [← hcode] at hright
  rw [hleft] at hright
  injection hright with hpair
  exact Prod.ext_iff.mp hpair |>.1

private theorem mem_erase_of_ne_of_mem {α : Type} [BEq α] [LawfulBEq α]
    {a b : α} {xs : List α} (hne : a ≠ b) (hmem : a ∈ xs) :
    a ∈ xs.erase b := by
  induction xs with
  | nil =>
      simp at hmem
  | cons x xs ih =>
      by_cases hxb : x = b
      · subst x
        rw [List.erase_cons_head]
        simp at hmem
        rcases hmem with hmem | hmem
        · exact False.elim (hne hmem)
        · exact hmem
      · have hbeq : ¬(x == b) = true := by
          intro h
          apply hxb
          exact eq_of_beq h
        rw [List.erase_cons_tail hbeq]
        simp at hmem ⊢
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · exact Or.inr (ih hmem)

private theorem length_le_of_nodup_injective_into
    {α β : Type} [BEq β] [LawfulBEq β]
    (xs : List α) (ys : List β) (f : α -> β)
    (hxs : xs.Nodup)
    (hmem : forall x, x ∈ xs -> f x ∈ ys)
    (hinj :
      forall x, x ∈ xs -> forall y, y ∈ xs -> f x = f y -> x = y) :
    xs.length <= ys.length := by
  induction xs generalizing ys with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      have hxmem : f x ∈ ys := hmem x (by simp)
      have htail :
          xs.length <= (ys.erase (f x)).length := by
        apply ih
        · exact hxs.2
        · intro y hy
          have hymem : f y ∈ ys := hmem y (by simp [hy])
          have hne : f y ≠ f x := by
            intro hEq
            have hyx : y = x :=
              hinj y (by simp [hy]) x (by simp) hEq
            exact hxs.1 (by simpa [hyx] using hy)
          exact mem_erase_of_ne_of_mem hne hymem
        · intro y hy z hz hEq
          exact hinj y (by simp [hy]) z (by simp [hz]) hEq
      have herase_len := List.length_erase_of_mem hxmem
      have hys_pos : 0 < ys.length := by
        cases ys with
        | nil =>
            simp at hxmem
        | cons _ _ =>
            simp
      rw [herase_len] at htail
      simp
      omega

private theorem nodup_map_node_left
    (left : CartesianShape) {rights : List CartesianShape}
    (hrights : rights.Nodup) :
    (rights.map fun right => CartesianShape.node left right).Nodup := by
  induction rights with
  | nil =>
      simp
  | cons right rights ih =>
      rw [List.nodup_cons] at hrights
      change
        (CartesianShape.node left right ::
          (rights.map fun right => CartesianShape.node left right)).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨right', hright'_mem, hEq⟩
        injection hEq with _ hright_eq
        exact hrights.1 (by simpa [hright_eq] using hright'_mem)
      · exact ih hrights.2

private theorem mem_nodeProducts
    {shape : CartesianShape} {lefts rights : List CartesianShape}
    (hmem :
      shape ∈ lefts.flatMap
        (fun left => rights.map fun right => CartesianShape.node left right)) :
    ∃ left, left ∈ lefts ∧
      ∃ right, right ∈ rights ∧
        shape = CartesianShape.node left right := by
  rw [List.mem_flatMap] at hmem
  rcases hmem with ⟨left, hleft, hshape⟩
  rw [List.mem_map] at hshape
  rcases hshape with ⟨right, hright, hEq⟩
  exact ⟨left, hleft, right, hright, hEq.symm⟩

private theorem nodup_nodeProducts
    {lefts rights : List CartesianShape}
    (hlefts : lefts.Nodup) (hrights : rights.Nodup) :
    (lefts.flatMap
        (fun left =>
          rights.map fun right =>
            CartesianShape.node left right)).Nodup := by
  induction lefts with
  | nil =>
      simp
  | cons left lefts ih =>
      rw [List.nodup_cons] at hlefts
      simp [List.flatMap]
      rw [List.nodup_append]
      constructor
      · exact nodup_map_node_left left hrights
      constructor
      · exact ih hlefts.2
      · intro a ha b hb hEq
        rw [List.mem_map] at ha
        rcases ha with ⟨right, hright, haEq⟩
        rcases mem_nodeProducts hb with
          ⟨left', hleft', right', _hright', hbEq⟩
        subst a
        subst b
        injection haEq with hleft_eq _hright_eq
        exact hlefts.1 (by simpa [hleft_eq] using hleft')

private theorem nodup_flatMap_of_nodup_disjoint
    {σ α : Type} {splits : List σ} {f : σ -> List α}
    (hsplits : splits.Nodup)
    (hnodup : forall s, s ∈ splits -> (f s).Nodup)
    (hdisjoint :
      forall s, s ∈ splits ->
        forall t, t ∈ splits ->
          s ≠ t ->
            forall a, a ∈ f s ->
              forall b, b ∈ f t -> a ≠ b) :
    (splits.flatMap f).Nodup := by
  induction splits with
  | nil =>
      simp
  | cons s splits ih =>
      rw [List.nodup_cons] at hsplits
      simp [List.flatMap]
      rw [List.nodup_append]
      constructor
      · exact hnodup s (by simp)
      constructor
      · apply ih
        · exact hsplits.2
        · intro t ht
          exact hnodup t (by simp [ht])
        · intro t ht u hu htu a ha b hb
          exact hdisjoint t (by simp [ht]) u (by simp [hu]) htu a ha b hb
      · intro a ha b hb hab
        change b ∈ splits.flatMap f at hb
        rw [List.mem_flatMap] at hb
        rcases hb with ⟨t, ht, hb⟩
        exact hdisjoint s (by simp) t (by simp [ht])
          (by
            intro hst
            subst t
            exact hsplits.1 ht)
          a ha b hb hab

private def splitShapeProducts (n : Nat) (split : Fin (n + 1)) :
    List CartesianShape :=
  let leftSize := split.val
  let rightSize := n - split.val
  (shapesOfSize leftSize).flatMap fun leftShape =>
    (shapesOfSize rightSize).map fun rightShape =>
      CartesianShape.node leftShape rightShape

private theorem mem_splitShapeProducts
    {n : Nat} {split : Fin (n + 1)} {shape : CartesianShape}
    (hmem : shape ∈ splitShapeProducts n split) :
    ∃ leftShape, leftShape ∈ shapesOfSize split.val ∧
      ∃ rightShape, rightShape ∈ shapesOfSize (n - split.val) ∧
        shape = CartesianShape.node leftShape rightShape := by
  unfold splitShapeProducts at hmem
  exact mem_nodeProducts hmem

private theorem splitShapeProducts_nodup
    {n : Nat} {split : Fin (n + 1)}
    (ih : forall m, m < n + 1 -> (shapesOfSize m).Nodup) :
    (splitShapeProducts n split).Nodup := by
  unfold splitShapeProducts
  apply nodup_nodeProducts
  · exact ih split.val split.isLt
  · have hright_lt : n - split.val < n + 1 := by
      omega
    exact ih (n - split.val) hright_lt

theorem shapesOfSize_nodup (n : Nat) :
    (shapesOfSize n).Nodup := by
  exact
    Nat.strongRecOn
      (motive := fun n => (shapesOfSize n).Nodup)
      n
      (fun n ih => by
        cases n with
        | zero =>
            simp [shapesOfSize]
        | succ n =>
            have hnodup :
                ((List.finRange (n + 1)).flatMap
                  (fun split : Fin (n + 1) =>
                    splitShapeProducts n split)).Nodup := by
              apply nodup_flatMap_of_nodup_disjoint
              · exact finRange_nodup (n + 1)
              · intro split _hmem
                exact splitShapeProducts_nodup (n := n) (split := split) ih
              · intro split _hsplit split' _hsplit' hne a ha b hb hab
                rcases mem_splitShapeProducts ha with
                  ⟨left, hleft, right, _hright, haEq⟩
                rcases mem_splitShapeProducts hb with
                  ⟨left', hleft', right', _hright', hbEq⟩
                have hnodes :
                    CartesianShape.node left right =
                      CartesianShape.node left' right' := by
                  rw [← haEq, hab, hbEq]
                injection hnodes with hleft_eq _hright_eq
                subst left'
                have hleftSize := ShapeOfSize.size_eq
                  (mem_shapesOfSize_shapeOfSize hleft)
                have hleftSize' := ShapeOfSize.size_eq
                  (mem_shapesOfSize_shapeOfSize hleft')
                have hval : split.val = split'.val := by
                  omega
                apply hne
                exact Fin.ext hval
            simpa [shapesOfSize, splitShapeProducts] using hnodup)

theorem CartesianShape.fullCode_tail_length_of_shapeOfSize
    {n : Nat} {shape : CartesianShape}
    (hshape : ShapeOfSize n shape) :
    shape.fullCode.tail.length = 2 * n := by
  cases shape with
  | empty =>
      have hsize := ShapeOfSize.size_eq hshape
      simp [CartesianShape.fullCode, CartesianShape.size] at hsize ⊢
      omega
  | node left right =>
      have hsize := ShapeOfSize.size_eq hshape
      simp [CartesianShape.fullCode, CartesianShape.fullCode_length]
      simp [CartesianShape.size] at hsize
      omega

private theorem fullCode_eq_of_tail_eq_of_pos
    {n : Nat} {left right : CartesianShape}
    (hleft : left ∈ shapesOfSize (n + 1))
    (hright : right ∈ shapesOfSize (n + 1))
    (htail : left.fullCode.tail = right.fullCode.tail) :
    left.fullCode = right.fullCode := by
  cases left with
  | empty =>
      have hshape := mem_shapesOfSize_shapeOfSize hleft
      have hsize := ShapeOfSize.size_eq hshape
      simp [CartesianShape.size] at hsize
  | node _ _ =>
      cases right with
      | empty =>
          have hshape := mem_shapesOfSize_shapeOfSize hright
          have hsize := ShapeOfSize.size_eq hshape
          simp [CartesianShape.size] at hsize
      | node _ _ =>
          simp [CartesianShape.fullCode] at htail ⊢
          exact htail

/--
Catalan-count envelope used by the Fischer-Heun microtable bound: the number
of explicit binary Cartesian shapes of size `n` is at most the `2n`-bit
universe.
-/
theorem shapeCount_le_four_pow (n : Nat) :
    shapeCount n <= 4 ^ n := by
  cases n with
  | zero =>
      simp [shapeCount, shapesOfSize]
  | succ n =>
      have hle :
          (shapesOfSize (n + 1)).length <=
            (boolLists (2 * (n + 1))).length := by
        apply length_le_of_nodup_injective_into
        · exact shapesOfSize_nodup (n + 1)
        · intro shape hshapeMem
          apply mem_boolLists_of_length
          exact CartesianShape.fullCode_tail_length_of_shapeOfSize
            (mem_shapesOfSize_shapeOfSize hshapeMem)
        · intro left hleft right hright htail
          apply CartesianShape.fullCode_injective
          exact fullCode_eq_of_tail_eq_of_pos hleft hright htail
      have hpow :
          (boolLists (2 * (n + 1))).length = 4 ^ (n + 1) := by
        rw [boolLists_length, Nat.pow_mul]
      simpa [shapeCount, hpow] using hle

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
