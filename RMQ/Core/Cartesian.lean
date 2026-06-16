import RMQ.Core.Reduction

/-!
# Cartesian-tree certificates for RMQ-to-LCA

This module begins the constructive reverse reduction. It builds a
proof-friendly Cartesian tree over list indices by choosing the root of each
range with the same leftmost-minimum scan used by the RMQ contract.
-/

namespace RMQ

namespace Cartesian

theorem betterIndex_eq_left_or_right
    (xs : List Int) (best i : Nat) :
    betterIndex xs best i = best \/ betterIndex xs best i = i := by
  unfold betterIndex
  cases hbest : xs[best]? with
  | none =>
      cases hi : xs[i]? with
      | none => simp
      | some iVal => simp
  | some bestVal =>
      cases hi : xs[i]? with
      | none => simp
      | some iVal =>
          by_cases hlt : iVal < bestVal
          · simp [hlt]
          · simp [hlt]

theorem scanWindow_bounds
    (xs : List Int) (start len : Nat) (hlen : 0 < len) :
    start <= scanWindow xs start len /\
      scanWindow xs start len < start + len := by
  induction len with
  | zero =>
      omega
  | succ len ih =>
      cases len with
      | zero =>
          simp [scanWindow]
      | succ len =>
          have hprev :
              start <= scanWindow xs start (len + 1) /\
                scanWindow xs start (len + 1) <
                  start + (len + 1) := by
            exact ih (by omega)
          have hchoice :=
            betterIndex_eq_left_or_right xs
              (scanWindow xs start (len + 1))
              (start + len + 1)
          unfold scanWindow
          rcases hchoice with hchoice | hchoice
          · rw [hchoice]
            omega
          · rw [hchoice]
            omega

/-- A child list containing one subtree exactly when the child range is nonempty. -/
def childIf
    (_xs : List Int) (_left len : Nat)
    (build : 0 < len -> RoseTree) : List RoseTree :=
  if h : 0 < len then [build h] else []

/-- Cartesian tree over the syntactic half-open range `[left, left + len)`. -/
def treeRange (xs : List Int) (left len : Nat) : RoseTree :=
  match len with
  | 0 => RoseTree.node left []
  | len' + 1 =>
      let width := len' + 1
      let root := scanWindow xs left width
      let leftLen := root - left
      let rightStart := root + 1
      let rightLen := left + width - rightStart
      RoseTree.node root
        (childIf xs left leftLen
            (fun _ => treeRange xs left leftLen) ++
          childIf xs rightStart rightLen
            (fun _ => treeRange xs rightStart rightLen))
termination_by len
decreasing_by
  · have hbounds := scanWindow_bounds xs left (len' + 1) (by omega)
    omega
  · have hbounds := scanWindow_bounds xs left (len' + 1) (by omega)
    omega

/-- Public Cartesian tree over all indices of `xs`; empty lists use a dummy root. -/
def tree (xs : List Int) : RoseTree :=
  treeRange xs 0 xs.length

/-- The root label of a rose tree. -/
def rootLabel : RoseTree -> Nat
  | RoseTree.node label _ => label

theorem treeRange_root_leftmost
    (xs : List Int) (left len : Nat)
    (hlen : 0 < len) (hbound : left + len <= xs.length) :
    LeftmostArgMin xs left (left + len)
      (rootLabel (treeRange xs left len)) := by
  cases len with
  | zero =>
      omega
  | succ len =>
      simp [treeRange, rootLabel]
      exact scanWindow_leftmost xs left (len + 1) (by omega) hbound

theorem treeRange_pathTo_root
    (xs : List Int) (left len : Nat) :
    (treeRange xs left len).pathTo?
      (rootLabel (treeRange xs left len)) =
        some [rootLabel (treeRange xs left len)] := by
  cases len with
  | zero =>
      simp [treeRange, rootLabel, RoseTree.pathTo?]
  | succ len =>
      simp [treeRange, rootLabel, RoseTree.pathTo?]

theorem treeRange_pathLCA_root_root
    (xs : List Int) (left len : Nat) :
    (treeRange xs left len).pathLCA?
      (rootLabel (treeRange xs left len))
      (rootLabel (treeRange xs left len)) =
        some (rootLabel (treeRange xs left len)) := by
  unfold RoseTree.pathLCA?
  rw [treeRange_pathTo_root xs left len]
  simp [RMQ.pathLCA?, commonPrefix]

theorem leftmostArgMin_restrict_containing
    {xs : List Int} {left right root qleft qright : Nat}
    (harg : LeftmostArgMin xs left right root)
    (hleft : left <= qleft)
    (hright : qright <= right)
    (hqleft_root : qleft <= root)
    (hroot_qright : root < qright) :
    LeftmostArgMin xs qleft qright root := by
  rcases harg with
    ⟨hleft_right, hright_len, hleft_root, hroot_right,
      rootVal, hroot_get, hmin, hleftmost⟩
  refine ⟨by omega, by omega, hqleft_root, hroot_qright,
    rootVal, hroot_get, ?_, ?_⟩
  · intro j w hj_left hj_right hget
    exact hmin j w (by omega) (by omega) hget
  · intro j w hj_left hj_root hget
    exact hleftmost j w (by omega) hj_root hget

theorem treeRange_root_leftmost_of_contains
    (xs : List Int) {left len qleft qright : Nat}
    (hlen : 0 < len) (hbound : left + len <= xs.length)
    (hsub_left : left <= qleft)
    (hsub_right : qright <= left + len)
    (hcontains_left : qleft <= rootLabel (treeRange xs left len))
    (hcontains_right : rootLabel (treeRange xs left len) < qright) :
    LeftmostArgMin xs qleft qright
      (rootLabel (treeRange xs left len)) := by
  exact leftmostArgMin_restrict_containing
    (treeRange_root_leftmost xs left len hlen hbound)
    hsub_left hsub_right hcontains_left hcontains_right

/--
The semantic Cartesian property needed for RMQ-to-LCA: for every exact RMQ
witness on `[left, right)`, the LCA of endpoint labels `left` and `right - 1`
is that witness.
-/
def RangeLCASpec (xs : List Int) (tree : RoseTree) : Prop :=
  forall {left right idx : Nat},
    LeftmostArgMin xs left right idx ->
      tree.pathLCA? left (right - 1) = some idx

/--
Any tree satisfying the endpoint-LCA Cartesian property induces an
`RMQToLCAReduction` with identity labels and decoding.
-/
def reductionOfRangeLCASpec
    (xs : List Int) (tree : RoseTree)
    (hspec : RangeLCASpec xs tree) :
    RMQToLCAReduction xs where
  tree := tree
  leftLabel := fun left => left
  rightLabel := fun right => right - 1
  decode := fun label => some label
  exists_lca := by
    intro left right hValid
    let len := right - left
    have hlen : 0 < len := by
      unfold len
      omega
    have hbound : left + len <= xs.length := by
      unfold len
      omega
    have hright : left + len = right := by
      unfold len
      omega
    have harg :
        LeftmostArgMin xs left right (scanWindow xs left len) := by
      simpa [hright] using scanWindow_leftmost xs left len hlen hbound
    exact ⟨scanWindow xs left len, hspec harg⟩
  sound := by
    intro left right ancestor idx hValid hpath hdecode
    let len := right - left
    have hlen : 0 < len := by
      unfold len
      omega
    have hbound : left + len <= xs.length := by
      unfold len
      omega
    have hright : left + len = right := by
      unfold len
      omega
    have hscan :
        LeftmostArgMin xs left right (scanWindow xs left len) := by
      simpa [hright] using scanWindow_leftmost xs left len hlen hbound
    have hcart :
        tree.pathLCA? left (right - 1) = some (scanWindow xs left len) :=
      hspec hscan
    have hancestor : ancestor = scanWindow xs left len := by
      exact Option.some.inj (by rw [← hpath, hcart])
    have hidx : idx = ancestor := by
      exact (Option.some.inj hdecode).symm
    simpa [hidx, hancestor] using hscan
  complete := by
    intro left right idx harg
    exact ⟨idx, hspec harg, rfl⟩

/-- The remaining constructive theorem for the tree built in this module. -/
def BuiltRangeLCASpec (xs : List Int) : Prop :=
  RangeLCASpec xs (tree xs)

/-- Concrete RMQ-to-LCA reduction from the built Cartesian tree, once certified. -/
def reduction (xs : List Int) (hspec : BuiltRangeLCASpec xs) :
    RMQToLCAReduction xs :=
  reductionOfRangeLCASpec xs (tree xs) hspec

example : rootLabel (tree [5, 2, 7, 1, 3]) = 3 := by
  native_decide

example : (tree [5, 2, 7, 1, 3]).pathLCA? 1 4 = some 3 := by
  native_decide

example : (tree [4, 1, 1, 2]).pathLCA? 1 2 = some 1 := by
  native_decide

end Cartesian

end RMQ
