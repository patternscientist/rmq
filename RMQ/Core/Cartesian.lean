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

/-- Half-open arithmetic membership for a syntactic Cartesian tree range. -/
def InRange (left len target : Nat) : Prop :=
  left <= target /\ target < left + len

/--
Direct arithmetic path to an index in a Cartesian range. This mirrors
`treeRange` but avoids unfolding `RoseTree.pathToForest?` during range-split
proofs.
-/
def indexPath (xs : List Int) (left len target : Nat) : Option (List Nat) :=
  match len with
  | 0 => none
  | len' + 1 =>
      let width := len' + 1
      let root := scanWindow xs left width
      let leftLen := root - left
      let rightStart := root + 1
      let rightLen := left + width - rightStart
      if target = root then
        some [root]
      else if target < root then
        match indexPath xs left leftLen target with
        | some path => some (root :: path)
        | none => none
      else
        match indexPath xs rightStart rightLen target with
        | some path => some (root :: path)
        | none => none
termination_by len
decreasing_by
  · have hbounds := scanWindow_bounds xs left (len' + 1) (by omega)
    omega
  · have hbounds := scanWindow_bounds xs left (len' + 1) (by omega)
    omega

theorem indexPath_root
    (xs : List Int) (left len : Nat) (hlen : 0 < len) :
    indexPath xs left len (rootLabel (treeRange xs left len)) =
      some [rootLabel (treeRange xs left len)] := by
  cases len with
  | zero =>
      omega
  | succ len =>
      simp [indexPath, treeRange, rootLabel]

theorem indexPath_exists_of_inRange
    (xs : List Int) (left len target : Nat)
    (hlen : 0 < len) (hrange : InRange left len target) :
    exists path, indexPath xs left len target = some path := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left target,
          0 < len ->
            InRange left len target ->
              exists path, indexPath xs left len target = some path)
      len
      (fun len ih left target hlen hrange => by
      cases len with
      | zero =>
          omega
      | succ len' =>
          let width := len' + 1
          let root := scanWindow xs left width
          let leftLen := root - left
          let rightStart := root + 1
          let rightLen := left + width - rightStart
          have hbounds : left <= root /\ root < left + width :=
            scanWindow_bounds xs left width (by omega)
          by_cases htarget_root : target = root
          · refine ⟨[root], ?_⟩
            simp [indexPath, width, root, htarget_root]
          · by_cases htarget_left : target < root
            · have hleftRange : InRange left leftLen target := by
                have hleft_end : left + leftLen = root := by
                  unfold leftLen
                  omega
                unfold InRange
                constructor
                · exact hrange.1
                · rw [hleft_end]
                  exact htarget_left
              have hleftLen : 0 < leftLen := by
                have hleft_lt_root : left < root :=
                  Nat.lt_of_le_of_lt hrange.1 htarget_left
                unfold leftLen
                exact Nat.sub_pos_of_lt hleft_lt_root
              have hleftLen_lt : leftLen < len' + 1 := by
                unfold leftLen
                omega
              rcases ih leftLen hleftLen_lt left target hleftLen hleftRange with
                ⟨path, hpath⟩
              refine ⟨root :: path, ?_⟩
              simp [indexPath, width, root, leftLen,
                htarget_root, htarget_left, hpath]
            · have htarget_right : root < target := by omega
              have hrightRange : InRange rightStart rightLen target := by
                have hright_end : rightStart + rightLen = left + width := by
                  unfold rightLen
                  omega
                unfold InRange
                constructor
                · unfold rightStart
                  omega
                · rw [hright_end]
                  exact hrange.2
              have hrightLen : 0 < rightLen := by
                have htarget_end : target < left + width := by
                  unfold InRange at hrange
                  exact hrange.2
                have hright_start_lt_end : rightStart < left + width := by
                  unfold rightStart
                  omega
                unfold rightLen rightStart
                omega
              have hrightLen_lt : rightLen < len' + 1 := by
                unfold rightLen rightStart
                omega
              rcases ih rightLen hrightLen_lt rightStart target
                  hrightLen hrightRange with
                ⟨path, hpath⟩
              refine ⟨root :: path, ?_⟩
              simp [indexPath, width, root, rightStart, rightLen,
                htarget_root, htarget_left, hpath])
      left target hlen hrange

theorem indexPath_none_of_not_inRange
    (xs : List Int) (left len target : Nat)
    (hnot : Not (InRange left len target)) :
    indexPath xs left len target = none := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left target,
          Not (InRange left len target) ->
            indexPath xs left len target = none)
      len
      (fun len ih left target hnot => by
        cases len with
        | zero =>
            simp [indexPath]
        | succ len' =>
            let width := len' + 1
            let root := scanWindow xs left width
            let leftLen := root - left
            let rightStart := root + 1
            let rightLen := left + width - rightStart
            have hbounds : left <= root /\ root < left + width :=
              scanWindow_bounds xs left width (by omega)
            have hroot_in : InRange left (len' + 1) root := by
              unfold InRange
              exact hbounds
            by_cases htarget_root : target = root
            · exact False.elim (hnot (by simpa [htarget_root] using hroot_in))
            · by_cases htarget_left : target < root
              · have hleft_not : Not (InRange left leftLen target) := by
                  intro hleftRange
                  have hleft_end : left + leftLen = root := by
                    unfold leftLen
                    omega
                  have hfull : InRange left (len' + 1) target := by
                    unfold InRange at hleftRange ⊢
                    constructor
                    · exact hleftRange.1
                    · have htarget_root_lt : target < root := by
                        rw [← hleft_end]
                        exact hleftRange.2
                      omega
                  exact hnot hfull
                have hleftLen_lt : leftLen < len' + 1 := by
                  unfold leftLen
                  omega
                have hleft_none :
                    indexPath xs left leftLen target = none :=
                  ih leftLen hleftLen_lt left target hleft_not
                simp [indexPath, width, root, leftLen,
                  htarget_root, htarget_left, hleft_none]
              · have hright_not : Not (InRange rightStart rightLen target) := by
                  intro hrightRange
                  have hright_end :
                      rightStart + rightLen = left + width := by
                    unfold rightLen
                    omega
                  have hfull : InRange left (len' + 1) target := by
                    unfold InRange at hrightRange ⊢
                    constructor
                    · unfold rightStart at hrightRange
                      omega
                    · rw [← hright_end]
                      exact hrightRange.2
                  exact hnot hfull
                have hrightLen_lt : rightLen < len' + 1 := by
                  unfold rightLen rightStart
                  omega
                have hright_none :
                    indexPath xs rightStart rightLen target = none :=
                  ih rightLen hrightLen_lt rightStart target hright_not
                simp [indexPath, width, root, rightStart, rightLen,
                  htarget_root, htarget_left, hright_none])
      left target hnot

theorem indexPath_head_inRange
    (xs : List Int) (left len target : Nat) {path : List Nat}
    (hpath : indexPath xs left len target = some path) :
    forall {head : Nat} {tail : List Nat}, path = head :: tail ->
      InRange left len head := by
  intro head tail hcons
  cases len with
  | zero =>
      simp [indexPath] at hpath
  | succ len' =>
      let width := len' + 1
      let root := scanWindow xs left width
      let leftLen := root - left
      let rightStart := root + 1
      let rightLen := left + width - rightStart
      have hbounds : InRange left (len' + 1) root := by
        unfold InRange
        exact scanWindow_bounds xs left width (by omega)
      by_cases htarget_root : target = root
      · simp [indexPath, width, root, htarget_root] at hpath
        rw [hcons] at hpath
        injection hpath with hhead _htail
        subst head
        exact hbounds
      · by_cases htarget_left : target < root
        · cases hchild : indexPath xs left leftLen target with
          | none =>
              simp [indexPath, width, root, leftLen,
                htarget_root, htarget_left, hchild] at hpath
          | some childPath =>
            simp [indexPath, width, root, leftLen,
              htarget_root, htarget_left, hchild] at hpath
            rw [hcons] at hpath
            injection hpath with hhead _htail
            subst head
            exact hbounds
        · cases hchild : indexPath xs rightStart rightLen target with
          | none =>
              simp [indexPath, width, root, rightStart, rightLen,
                htarget_root, htarget_left, hchild] at hpath
          | some childPath =>
            simp [indexPath, width, root, rightStart, rightLen,
              htarget_root, htarget_left, hchild] at hpath
            rw [hcons] at hpath
            injection hpath with hhead _htail
            subst head
            exact hbounds

theorem commonPrefix_eq_nil_of_head_separated
    {leftPath rightPath : List Nat} {cut : Nat}
    (hleft :
      forall {head : Nat} {tail : List Nat}, leftPath = head :: tail ->
        head < cut)
    (hright :
      forall {head : Nat} {tail : List Nat}, rightPath = head :: tail ->
        cut < head) :
    commonPrefix leftPath rightPath = [] := by
  cases leftPath with
  | nil =>
      simp [commonPrefix]
  | cons leftHead leftTail =>
      cases rightPath with
      | nil =>
          simp [commonPrefix]
      | cons rightHead rightTail =>
          have hne : leftHead ≠ rightHead := by
            intro heq
            have hlt : leftHead < cut := hleft rfl
            have hgt : cut < rightHead := hright rfl
            omega
          simp [commonPrefix, hne]

theorem pathLCA?_root_cons_of_tail_separated
    (root : Nat) (leftPath rightPath : List Nat)
    (hsep : commonPrefix leftPath rightPath = []) :
    RMQ.pathLCA? (root :: leftPath) (root :: rightPath) = some root := by
  simp [RMQ.pathLCA?, commonPrefix, hsep]

theorem pathLCA?_root_cons_of_tail_lca
    {root idx : Nat} {leftPath rightPath : List Nat}
    (htail : RMQ.pathLCA? leftPath rightPath = some idx) :
    RMQ.pathLCA? (root :: leftPath) (root :: rightPath) = some idx := by
  unfold RMQ.pathLCA? at htail ⊢
  cases hprefix : commonPrefix leftPath rightPath with
  | nil =>
      simp [hprefix] at htail
  | cons head tail =>
      simp [commonPrefix, hprefix]
      simpa [hprefix] using htail

theorem pathToForest?_append_none
    (target : Nat) :
    forall (leftForest rightForest : List RoseTree),
      RoseTree.pathToForest? target leftForest = none ->
        RoseTree.pathToForest? target rightForest = none ->
          RoseTree.pathToForest? target (leftForest ++ rightForest) = none
  | [], rightForest, _hleft, hright => by
      simpa [RoseTree.pathToForest?] using hright
  | child :: rest, rightForest, hleft, hright => by
      unfold RoseTree.pathToForest? at hleft ⊢
      cases hchild : child.pathTo? target with
      | none =>
          simp [hchild] at hleft ⊢
          exact pathToForest?_append_none target rest rightForest hleft hright
      | some path =>
          simp [hchild] at hleft

theorem pathToForest?_append_left_some
    {target : Nat} {leftForest rightForest : List RoseTree} {path : List Nat}
    (hleft : RoseTree.pathToForest? target leftForest = some path) :
    RoseTree.pathToForest? target (leftForest ++ rightForest) = some path := by
  induction leftForest with
  | nil =>
      simp [RoseTree.pathToForest?] at hleft
  | cons child rest ih =>
      unfold RoseTree.pathToForest? at hleft ⊢
      cases hchild : child.pathTo? target with
      | none =>
          simp [hchild] at hleft ⊢
          exact ih hleft
      | some childPath =>
          simp [hchild] at hleft ⊢
          exact hleft

theorem pathToForest?_append_right_of_left_none
    {target : Nat} {leftForest rightForest : List RoseTree} {path : List Nat}
    (hleft : RoseTree.pathToForest? target leftForest = none)
    (hright : RoseTree.pathToForest? target rightForest = some path) :
    RoseTree.pathToForest? target (leftForest ++ rightForest) = some path := by
  induction leftForest with
  | nil =>
      simpa [RoseTree.pathToForest?] using hright
  | cons child rest ih =>
      unfold RoseTree.pathToForest? at hleft ⊢
      cases hchild : child.pathTo? target with
      | none =>
          simp [hchild] at hleft ⊢
          exact ih hleft
      | some childPath =>
          simp [hchild] at hleft

theorem treeRange_pathTo?_none_of_not_inRange
    (xs : List Int) (left len target : Nat)
    (hlen : 0 < len)
    (hnot : Not (InRange left len target)) :
    (treeRange xs left len).pathTo? target = none := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left target,
          0 < len ->
            Not (InRange left len target) ->
              (treeRange xs left len).pathTo? target = none)
      len
      (fun len ih left target hlen hnot => by
        cases len with
        | zero =>
            omega
        | succ len' =>
            let width := len' + 1
            let root := scanWindow xs left width
            let leftLen := root - left
            let rightStart := root + 1
            let rightLen := left + width - rightStart
            let leftForest :=
              childIf xs left leftLen
                (fun _ => treeRange xs left leftLen)
            let rightForest :=
              childIf xs rightStart rightLen
                (fun _ => treeRange xs rightStart rightLen)
            have hbounds : left <= root /\ root < left + width :=
              scanWindow_bounds xs left width (by omega)
            have hroot_in : InRange left (len' + 1) root := by
              unfold InRange
              exact hbounds
            have hroot_ne : root ≠ target := by
              intro hrt
              exact hnot (by simpa [hrt] using hroot_in)
            have hleft_none :
                RoseTree.pathToForest? target leftForest = none := by
              by_cases hleft_pos : 0 < leftLen
              · have hleft_not : Not (InRange left leftLen target) := by
                  intro hleftRange
                  have hleft_end : left + leftLen = root := by
                    unfold leftLen
                    omega
                  have hfull : InRange left (len' + 1) target := by
                    unfold InRange at hleftRange ⊢
                    constructor
                    · exact hleftRange.1
                    · rw [hleft_end] at hleftRange
                      omega
                  exact hnot hfull
                have hleftLen_lt : leftLen < len' + 1 := by
                  unfold leftLen
                  omega
                have htree_none :
                    (treeRange xs left leftLen).pathTo? target = none :=
                  ih leftLen hleftLen_lt left target hleft_pos hleft_not
                simp [leftForest, childIf, hleft_pos, RoseTree.pathToForest?,
                  htree_none]
              · simp [leftForest, childIf, hleft_pos, RoseTree.pathToForest?]
            have hright_none :
                RoseTree.pathToForest? target rightForest = none := by
              by_cases hright_pos : 0 < rightLen
              · have hright_not : Not (InRange rightStart rightLen target) := by
                  intro hrightRange
                  have hright_end :
                      rightStart + rightLen = left + width := by
                    unfold rightLen
                    omega
                  have hfull : InRange left (len' + 1) target := by
                    unfold InRange at hrightRange ⊢
                    constructor
                    · unfold rightStart at hrightRange
                      omega
                    · rw [← hright_end]
                      exact hrightRange.2
                  exact hnot hfull
                have hrightLen_lt : rightLen < len' + 1 := by
                  unfold rightLen rightStart
                  omega
                have htree_none :
                    (treeRange xs rightStart rightLen).pathTo? target = none :=
                  ih rightLen hrightLen_lt rightStart target hright_pos hright_not
                simp [rightForest, childIf, hright_pos, RoseTree.pathToForest?,
                  htree_none]
              · simp [rightForest, childIf, hright_pos, RoseTree.pathToForest?]
            have hforest_none :
                RoseTree.pathToForest? target (leftForest ++ rightForest) = none :=
              pathToForest?_append_none target leftForest rightForest
                hleft_none hright_none
            simp [treeRange, RoseTree.pathTo?, width, root, leftLen,
              rightStart, rightLen, leftForest, rightForest, hroot_ne,
              hforest_none])
      left target hlen hnot

theorem treeRange_pathTo?_exists_of_inRange
    (xs : List Int) (left len target : Nat)
    (hlen : 0 < len)
    (hrange : InRange left len target) :
    exists path, (treeRange xs left len).pathTo? target = some path := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left target,
          0 < len ->
            InRange left len target ->
              exists path, (treeRange xs left len).pathTo? target = some path)
      len
      (fun len ih left target hlen hrange => by
        cases len with
        | zero =>
            omega
        | succ len' =>
            let width := len' + 1
            let root := scanWindow xs left width
            let leftLen := root - left
            let rightStart := root + 1
            let rightLen := left + width - rightStart
            let leftForest :=
              childIf xs left leftLen
                (fun _ => treeRange xs left leftLen)
            let rightForest :=
              childIf xs rightStart rightLen
                (fun _ => treeRange xs rightStart rightLen)
            have hbounds : left <= root /\ root < left + width :=
              scanWindow_bounds xs left width (by omega)
            by_cases htarget_root : target = root
            · refine ⟨[root], ?_⟩
              simp [treeRange, RoseTree.pathTo?, width, root, htarget_root]
            · have hroot_ne : root ≠ target := by
                intro hrt
                exact htarget_root hrt.symm
              by_cases htarget_left : target < root
              · have hleftRange : InRange left leftLen target := by
                  have hleft_end : left + leftLen = root := by
                    unfold leftLen
                    omega
                  unfold InRange
                  constructor
                  · exact hrange.1
                  · rw [hleft_end]
                    exact htarget_left
                have hleft_pos : 0 < leftLen := by
                  have hleft_lt_root : left < root :=
                    Nat.lt_of_le_of_lt hrange.1 htarget_left
                  unfold leftLen
                  exact Nat.sub_pos_of_lt hleft_lt_root
                have hleftLen_lt : leftLen < len' + 1 := by
                  unfold leftLen
                  omega
                rcases ih leftLen hleftLen_lt left target
                    hleft_pos hleftRange with
                  ⟨path, hpath⟩
                have hleftForest :
                    RoseTree.pathToForest? target leftForest = some path := by
                  simp [leftForest, childIf, hleft_pos,
                    RoseTree.pathToForest?, hpath]
                have hforest :
                    RoseTree.pathToForest? target
                      (leftForest ++ rightForest) = some path :=
                  pathToForest?_append_left_some hleftForest
                refine ⟨root :: path, ?_⟩
                simp [treeRange, RoseTree.pathTo?, width, root, leftLen,
                  rightStart, rightLen, leftForest, rightForest, hroot_ne,
                  hforest]
              · have htarget_right : root < target := by omega
                have hleftForest_none :
                    RoseTree.pathToForest? target leftForest = none := by
                  by_cases hleft_pos : 0 < leftLen
                  · have hleft_not : Not (InRange left leftLen target) := by
                      intro hleftRange
                      have hleft_end : left + leftLen = root := by
                        unfold leftLen
                        omega
                      unfold InRange at hleftRange
                      rw [hleft_end] at hleftRange
                      omega
                    have htree_none :
                        (treeRange xs left leftLen).pathTo? target = none :=
                      treeRange_pathTo?_none_of_not_inRange
                        xs left leftLen target hleft_pos hleft_not
                    simp [leftForest, childIf, hleft_pos,
                      RoseTree.pathToForest?, htree_none]
                  · simp [leftForest, childIf, hleft_pos,
                      RoseTree.pathToForest?]
                have hrightRange : InRange rightStart rightLen target := by
                  have hright_end :
                      rightStart + rightLen = left + width := by
                    unfold rightLen
                    omega
                  unfold InRange
                  constructor
                  · unfold rightStart
                    omega
                  · rw [hright_end]
                    exact hrange.2
                have hright_pos : 0 < rightLen := by
                  have htarget_end : target < left + width := by
                    unfold InRange at hrange
                    exact hrange.2
                  have hright_start_lt_end : rightStart < left + width := by
                    unfold rightStart
                    omega
                  unfold rightLen rightStart
                  omega
                have hrightLen_lt : rightLen < len' + 1 := by
                  unfold rightLen rightStart
                  omega
                rcases ih rightLen hrightLen_lt rightStart target
                    hright_pos hrightRange with
                  ⟨path, hpath⟩
                have hrightForest :
                    RoseTree.pathToForest? target rightForest = some path := by
                  simp [rightForest, childIf, hright_pos,
                    RoseTree.pathToForest?, hpath]
                have hforest :
                    RoseTree.pathToForest? target
                      (leftForest ++ rightForest) = some path :=
                  pathToForest?_append_right_of_left_none
                    hleftForest_none hrightForest
                refine ⟨root :: path, ?_⟩
                simp [treeRange, RoseTree.pathTo?, width, root, leftLen,
                  rightStart, rightLen, leftForest, rightForest, hroot_ne,
                  hforest])
      left target hlen hrange

theorem treeRange_pathTo?_eq_indexPath
    (xs : List Int) (left len target : Nat)
    (hlen : 0 < len) :
    (treeRange xs left len).pathTo? target =
      indexPath xs left len target := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left target,
          0 < len ->
            (treeRange xs left len).pathTo? target =
              indexPath xs left len target)
      len
      (fun len ih left target hlen => by
        by_cases hrange : InRange left len target
        · cases len with
          | zero =>
              omega
          | succ len' =>
              let width := len' + 1
              let root := scanWindow xs left width
              let leftLen := root - left
              let rightStart := root + 1
              let rightLen := left + width - rightStart
              let leftForest :=
                childIf xs left leftLen
                  (fun _ => treeRange xs left leftLen)
              let rightForest :=
                childIf xs rightStart rightLen
                  (fun _ => treeRange xs rightStart rightLen)
              have hbounds : left <= root /\ root < left + width :=
                scanWindow_bounds xs left width (by omega)
              by_cases htarget_root : target = root
              · simp [treeRange, indexPath, RoseTree.pathTo?, width, root,
                  htarget_root]
              · have hroot_ne : root ≠ target := by
                  intro hrt
                  exact htarget_root hrt.symm
                by_cases htarget_left : target < root
                · have hleftRange : InRange left leftLen target := by
                    have hleft_end : left + leftLen = root := by
                      unfold leftLen
                      omega
                    unfold InRange
                    constructor
                    · exact hrange.1
                    · rw [hleft_end]
                      exact htarget_left
                  have hleft_pos : 0 < leftLen := by
                    have hleft_lt_root : left < root :=
                      Nat.lt_of_le_of_lt hrange.1 htarget_left
                    unfold leftLen
                    exact Nat.sub_pos_of_lt hleft_lt_root
                  have hleftLen_lt : leftLen < len' + 1 := by
                    unfold leftLen
                    omega
                  have hrec :
                      (treeRange xs left leftLen).pathTo? target =
                        indexPath xs left leftLen target :=
                    ih leftLen hleftLen_lt left target hleft_pos
                  rcases indexPath_exists_of_inRange
                      xs left leftLen target hleft_pos hleftRange with
                    ⟨path, hpath⟩
                  have htree_path :
                      (treeRange xs left leftLen).pathTo? target =
                        some path := by
                    rw [hrec, hpath]
                  have hleftForest :
                      RoseTree.pathToForest? target leftForest =
                        some path := by
                    simp [leftForest, childIf, hleft_pos,
                      RoseTree.pathToForest?, htree_path]
                  have hforest :
                      RoseTree.pathToForest? target
                        (leftForest ++ rightForest) = some path :=
                    pathToForest?_append_left_some hleftForest
                  simp [treeRange, indexPath, RoseTree.pathTo?, width, root,
                    leftLen, rightStart, rightLen, leftForest, rightForest,
                    hroot_ne, htarget_root, htarget_left, hpath, hforest]
                · have htarget_right : root < target := by omega
                  have hleftForest_none :
                      RoseTree.pathToForest? target leftForest = none := by
                    by_cases hleft_pos : 0 < leftLen
                    · have hleft_not : Not (InRange left leftLen target) := by
                        intro hleftRange
                        have hleft_end : left + leftLen = root := by
                          unfold leftLen
                          omega
                        unfold InRange at hleftRange
                        rw [hleft_end] at hleftRange
                        omega
                      have htree_none :
                          (treeRange xs left leftLen).pathTo? target = none :=
                        treeRange_pathTo?_none_of_not_inRange
                          xs left leftLen target hleft_pos hleft_not
                      simp [leftForest, childIf, hleft_pos,
                        RoseTree.pathToForest?, htree_none]
                    · simp [leftForest, childIf, hleft_pos,
                        RoseTree.pathToForest?]
                  have hrightRange : InRange rightStart rightLen target := by
                    have hright_end :
                        rightStart + rightLen = left + width := by
                      unfold rightLen
                      omega
                    unfold InRange
                    constructor
                    · unfold rightStart
                      omega
                    · rw [hright_end]
                      exact hrange.2
                  have hright_pos : 0 < rightLen := by
                    have htarget_end : target < left + width := by
                      unfold InRange at hrange
                      exact hrange.2
                    have hright_start_lt_end : rightStart < left + width := by
                      unfold rightStart
                      omega
                    unfold rightLen rightStart
                    omega
                  have hrightLen_lt : rightLen < len' + 1 := by
                    unfold rightLen rightStart
                    omega
                  have hrec :
                      (treeRange xs rightStart rightLen).pathTo? target =
                        indexPath xs rightStart rightLen target :=
                    ih rightLen hrightLen_lt rightStart target hright_pos
                  rcases indexPath_exists_of_inRange
                      xs rightStart rightLen target hright_pos hrightRange with
                    ⟨path, hpath⟩
                  have htree_path :
                      (treeRange xs rightStart rightLen).pathTo? target =
                        some path := by
                    rw [hrec, hpath]
                  have hrightForest :
                      RoseTree.pathToForest? target rightForest =
                        some path := by
                    simp [rightForest, childIf, hright_pos,
                      RoseTree.pathToForest?, htree_path]
                  have hforest :
                      RoseTree.pathToForest? target
                        (leftForest ++ rightForest) = some path :=
                    pathToForest?_append_right_of_left_none
                      hleftForest_none hrightForest
                  simp [treeRange, indexPath, RoseTree.pathTo?, width, root,
                    leftLen, rightStart, rightLen, leftForest, rightForest,
                    hroot_ne, htarget_root, htarget_left, hpath, hforest]
        · have htree_none :
            (treeRange xs left len).pathTo? target = none :=
            treeRange_pathTo?_none_of_not_inRange xs left len target
              hlen hrange
          have hindex_none : indexPath xs left len target = none :=
            indexPath_none_of_not_inRange xs left len target hrange
          rw [htree_none, hindex_none])
      left target hlen

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

theorem treeRange_pathLCA_root_of_contains
    (xs : List Int) {left len qleft qright : Nat}
    (hlen : 0 < len)
    (hsub_left : left <= qleft)
    (hsub_right : qright <= left + len)
    (hcontains_left : qleft <= rootLabel (treeRange xs left len))
    (hcontains_right : rootLabel (treeRange xs left len) < qright) :
    (treeRange xs left len).pathLCA? qleft (qright - 1) =
      some (rootLabel (treeRange xs left len)) := by
  cases len with
  | zero =>
      omega
  | succ len' =>
      let width := len' + 1
      let root := scanWindow xs left width
      let leftLen := root - left
      let rightStart := root + 1
      let rightLen := left + width - rightStart
      have hbounds : left <= root /\ root < left + width :=
        scanWindow_bounds xs left width (by omega)
      have hcontains_left' : qleft <= root := by
        simpa [treeRange, rootLabel, width, root] using hcontains_left
      have hcontains_right' : root < qright := by
        simpa [treeRange, rootLabel, width, root] using hcontains_right
      have hqleftRange : InRange left (len' + 1) qleft := by
        unfold InRange
        constructor
        · exact hsub_left
        · omega
      have hrightTargetRange : InRange left (len' + 1) (qright - 1) := by
        unfold InRange
        constructor
        · omega
        · omega
      have hleftTop :
          exists leftTail,
            indexPath xs left (len' + 1) qleft =
              some (root :: leftTail) /\
            (forall {head : Nat} {tail : List Nat},
              leftTail = head :: tail -> head < root) := by
        by_cases hqleft_root : qleft = root
        · refine ⟨[], ?_, ?_⟩
          · simp [indexPath, width, root, hqleft_root]
          · intro head tail hcons
            cases hcons
        · have hqleft_lt_root : qleft < root := by omega
          have hleftRange : InRange left leftLen qleft := by
            have hleft_end : left + leftLen = root := by
              unfold leftLen
              omega
            unfold InRange
            constructor
            · exact hqleftRange.1
            · rw [hleft_end]
              exact hqleft_lt_root
          have hleft_pos : 0 < leftLen := by
            have hleft_lt_root : left < root :=
              Nat.lt_of_le_of_lt hqleftRange.1 hqleft_lt_root
            unfold leftLen
            exact Nat.sub_pos_of_lt hleft_lt_root
          rcases indexPath_exists_of_inRange
              xs left leftLen qleft hleft_pos hleftRange with
            ⟨leftTail, htail⟩
          refine ⟨leftTail, ?_, ?_⟩
          · simp [indexPath, width, root, leftLen, hqleft_root,
              hqleft_lt_root, htail]
          · intro head tail hcons
            have hheadRange : InRange left leftLen head :=
              indexPath_head_inRange xs left leftLen qleft htail hcons
            have hleft_end : left + leftLen = root := by
              unfold leftLen
              omega
            unfold InRange at hheadRange
            omega
      have hrightTop :
          exists rightTail,
            indexPath xs left (len' + 1) (qright - 1) =
              some (root :: rightTail) /\
            (forall {head : Nat} {tail : List Nat},
              rightTail = head :: tail -> root < head) := by
        by_cases hright_root : qright - 1 = root
        · refine ⟨[], ?_, ?_⟩
          · simp [indexPath, width, root, hright_root]
          · intro head tail hcons
            cases hcons
        · have hroot_lt_right : root < qright - 1 := by omega
          have hnot_left : ¬ qright - 1 < root := by omega
          have hrightRange : InRange rightStart rightLen (qright - 1) := by
            have hright_end :
                rightStart + rightLen = left + width := by
              unfold rightLen
              omega
            unfold InRange
            constructor
            · unfold rightStart
              omega
            · rw [hright_end]
              omega
          have hright_pos : 0 < rightLen := by
            unfold rightLen rightStart
            omega
          rcases indexPath_exists_of_inRange
              xs rightStart rightLen (qright - 1) hright_pos
              hrightRange with
            ⟨rightTail, htail⟩
          refine ⟨rightTail, ?_, ?_⟩
          · simp [indexPath, width, root, rightStart, rightLen,
              hright_root, hnot_left, htail]
          · intro head tail hcons
            have hheadRange : InRange rightStart rightLen head :=
              indexPath_head_inRange xs rightStart rightLen
                (qright - 1) htail hcons
            unfold InRange at hheadRange
            unfold rightStart at hheadRange
            omega
      rcases hleftTop with ⟨leftTail, hleftPath, hleftSep⟩
      rcases hrightTop with ⟨rightTail, hrightPath, hrightSep⟩
      have hsep : commonPrefix leftTail rightTail = [] :=
        commonPrefix_eq_nil_of_head_separated hleftSep hrightSep
      have hresult :
          (treeRange xs left (len' + 1)).pathLCA?
              qleft (qright - 1) = some root := by
        unfold RoseTree.pathLCA?
        rw [treeRange_pathTo?_eq_indexPath
          xs left (len' + 1) qleft (by omega)]
        rw [treeRange_pathTo?_eq_indexPath
          xs left (len' + 1) (qright - 1) (by omega)]
        rw [hleftPath, hrightPath]
        exact pathLCA?_root_cons_of_tail_separated
          root leftTail rightTail hsep
      simpa [treeRange, rootLabel, width, root] using hresult

theorem treeRange_pathLCA_left_lift
    (xs : List Int) {left len qleft qright idx : Nat}
    (hlen : 0 < len)
    (hleft_pos : 0 < rootLabel (treeRange xs left len) - left)
    (hqleft_lt_root : qleft < rootLabel (treeRange xs left len))
    (hright_lt_root : qright - 1 < rootLabel (treeRange xs left len))
    (hchild :
      (treeRange xs left (rootLabel (treeRange xs left len) - left)).pathLCA?
        qleft (qright - 1) = some idx) :
    (treeRange xs left len).pathLCA? qleft (qright - 1) = some idx := by
  cases len with
  | zero =>
      omega
  | succ len' =>
      let width := len' + 1
      let root := scanWindow xs left width
      let leftLen := root - left
      have hleft_pos' : 0 < leftLen := by
        simpa [treeRange, rootLabel, width, root, leftLen] using hleft_pos
      have hqleft_lt_root' : qleft < root := by
        simpa [treeRange, rootLabel, width, root] using hqleft_lt_root
      have hright_lt_root' : qright - 1 < root := by
        simpa [treeRange, rootLabel, width, root] using hright_lt_root
      have hchild' :
          (treeRange xs left leftLen).pathLCA?
            qleft (qright - 1) = some idx := by
        simpa [treeRange, rootLabel, width, root, leftLen] using hchild
      unfold RoseTree.pathLCA? at hchild' ⊢
      rw [treeRange_pathTo?_eq_indexPath
        xs left leftLen qleft hleft_pos'] at hchild'
      rw [treeRange_pathTo?_eq_indexPath
        xs left leftLen (qright - 1) hleft_pos'] at hchild'
      rw [treeRange_pathTo?_eq_indexPath
        xs left (len' + 1) qleft (by omega)]
      rw [treeRange_pathTo?_eq_indexPath
        xs left (len' + 1) (qright - 1) (by omega)]
      cases hleftPath : indexPath xs left leftLen qleft with
      | none =>
          simp [hleftPath] at hchild'
      | some leftPath =>
          cases hrightPath :
              indexPath xs left leftLen (qright - 1) with
          | none =>
              simp [hleftPath, hrightPath] at hchild'
          | some rightPath =>
              simp [hleftPath, hrightPath] at hchild'
              have hqleft_ne : ¬ qleft = root := by omega
              have hright_ne : ¬ qright - 1 = root := by omega
              simp [indexPath, width, root, leftLen, hqleft_ne,
                hqleft_lt_root', hright_ne, hright_lt_root',
                hleftPath, hrightPath]
              exact pathLCA?_root_cons_of_tail_lca hchild'

theorem treeRange_pathLCA_right_lift
    (xs : List Int) {left len qleft qright idx : Nat}
    (hlen : 0 < len)
    (hright_pos :
      0 < left + len - (rootLabel (treeRange xs left len) + 1))
    (hroot_lt_qleft : rootLabel (treeRange xs left len) < qleft)
    (hroot_lt_right : rootLabel (treeRange xs left len) < qright - 1)
    (hchild :
      (treeRange xs (rootLabel (treeRange xs left len) + 1)
          (left + len - (rootLabel (treeRange xs left len) + 1))).pathLCA?
        qleft (qright - 1) = some idx) :
    (treeRange xs left len).pathLCA? qleft (qright - 1) = some idx := by
  cases len with
  | zero =>
      omega
  | succ len' =>
      let width := len' + 1
      let root := scanWindow xs left width
      let leftLen := root - left
      let rightStart := root + 1
      let rightLen := left + width - rightStart
      have hright_pos' : 0 < rightLen := by
        simpa [treeRange, rootLabel, width, root, rightStart, rightLen]
          using hright_pos
      have hroot_lt_qleft' : root < qleft := by
        simpa [treeRange, rootLabel, width, root] using hroot_lt_qleft
      have hroot_lt_right' : root < qright - 1 := by
        simpa [treeRange, rootLabel, width, root] using hroot_lt_right
      have hchild' :
          (treeRange xs rightStart rightLen).pathLCA?
            qleft (qright - 1) = some idx := by
        simpa [treeRange, rootLabel, width, root, rightStart, rightLen]
          using hchild
      unfold RoseTree.pathLCA? at hchild' ⊢
      rw [treeRange_pathTo?_eq_indexPath
        xs rightStart rightLen qleft hright_pos'] at hchild'
      rw [treeRange_pathTo?_eq_indexPath
        xs rightStart rightLen (qright - 1) hright_pos'] at hchild'
      rw [treeRange_pathTo?_eq_indexPath
        xs left (len' + 1) qleft (by omega)]
      rw [treeRange_pathTo?_eq_indexPath
        xs left (len' + 1) (qright - 1) (by omega)]
      cases hleftPath : indexPath xs rightStart rightLen qleft with
      | none =>
          simp [hleftPath] at hchild'
      | some leftPath =>
          cases hrightPath :
              indexPath xs rightStart rightLen (qright - 1) with
          | none =>
              simp [hleftPath, hrightPath] at hchild'
          | some rightPath =>
              simp [hleftPath, hrightPath] at hchild'
              have hqleft_ne : ¬ qleft = root := by omega
              have hqleft_not_left : ¬ qleft < root := by omega
              have hright_ne : ¬ qright - 1 = root := by omega
              have hright_not_left : ¬ qright - 1 < root := by omega
              simp [indexPath, width, root, rightStart, rightLen,
                hqleft_ne, hqleft_not_left, hright_ne, hright_not_left,
                hleftPath, hrightPath]
              exact pathLCA?_root_cons_of_tail_lca hchild'

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

theorem treeRange_rangeLCASpec
    (xs : List Int) (left len : Nat)
    (hlen : 0 < len) (hbound : left + len <= xs.length) :
    forall {qleft qright idx : Nat},
      left <= qleft ->
        qright <= left + len ->
          LeftmostArgMin xs qleft qright idx ->
            (treeRange xs left len).pathLCA? qleft (qright - 1) =
              some idx := by
  exact
    Nat.strongRecOn
      (motive := fun len =>
        forall left,
          0 < len ->
            left + len <= xs.length ->
              forall {qleft qright idx : Nat},
                left <= qleft ->
                  qright <= left + len ->
                    LeftmostArgMin xs qleft qright idx ->
                      (treeRange xs left len).pathLCA?
                        qleft (qright - 1) = some idx)
      len
      (fun len ih left hlen hbound qleft qright idx
          hsub_left hsub_right harg => by
        cases len with
        | zero =>
            omega
        | succ len' =>
            let width := len' + 1
            let root := scanWindow xs left width
            let leftLen := root - left
            let rightStart := root + 1
            let rightLen := left + width - rightStart
            have hbounds : left <= root /\ root < left + width :=
              scanWindow_bounds xs left width (by omega)
            by_cases hqleft_le_root : qleft <= root
            · by_cases hroot_lt_qright : root < qright
              · have hcontains_left :
                    qleft <= rootLabel (treeRange xs left (len' + 1)) := by
                  simpa [treeRange, rootLabel, width, root] using
                    hqleft_le_root
                have hcontains_right :
                    rootLabel (treeRange xs left (len' + 1)) < qright := by
                  simpa [treeRange, rootLabel, width, root] using
                    hroot_lt_qright
                have hrootArg :
                    LeftmostArgMin xs qleft qright
                      (rootLabel (treeRange xs left (len' + 1))) :=
                  treeRange_root_leftmost_of_contains xs (by omega)
                    hbound hsub_left hsub_right hcontains_left
                    hcontains_right
                have hidx :
                    rootLabel (treeRange xs left (len' + 1)) = idx :=
                  leftmostArgMin_unique xs qleft qright
                    (rootLabel (treeRange xs left (len' + 1))) idx
                    hrootArg harg
                have hlca :
                    (treeRange xs left (len' + 1)).pathLCA?
                        qleft (qright - 1) =
                      some (rootLabel (treeRange xs left (len' + 1))) :=
                  treeRange_pathLCA_root_of_contains xs (by omega)
                    hsub_left hsub_right hcontains_left hcontains_right
                simpa [hidx] using hlca
              · have hqright_le_root : qright <= root := by omega
                have hqleft_lt_root : qleft < root := by
                  have hqleft_lt_qright : qleft < qright := harg.1
                  omega
                have hright_target_lt_root : qright - 1 < root := by
                  have hqleft_lt_qright : qleft < qright := harg.1
                  omega
                have hleft_end : left + leftLen = root := by
                  unfold leftLen
                  omega
                have hleft_pos : 0 < leftLen := by
                  have hleft_lt_root : left < root := by
                    have hqleft_lt_qright : qleft < qright := harg.1
                    omega
                  unfold leftLen
                  exact Nat.sub_pos_of_lt hleft_lt_root
                have hleftLen_lt : leftLen < len' + 1 := by
                  unfold leftLen
                  omega
                have hleft_bound : left + leftLen <= xs.length := by
                  omega
                have hchild_sub_right : qright <= left + leftLen := by
                  rw [hleft_end]
                  exact hqright_le_root
                have hchild :
                    (treeRange xs left leftLen).pathLCA?
                        qleft (qright - 1) = some idx :=
                  ih leftLen hleftLen_lt left hleft_pos hleft_bound
                    hsub_left hchild_sub_right harg
                exact treeRange_pathLCA_left_lift xs (by omega)
                  (by
                    simpa [treeRange, rootLabel, width, root, leftLen]
                      using hleft_pos)
                  (by
                    simpa [treeRange, rootLabel, width, root] using
                      hqleft_lt_root)
                  (by
                    simpa [treeRange, rootLabel, width, root] using
                      hright_target_lt_root)
                  (by
                    simpa [treeRange, rootLabel, width, root, leftLen]
                      using hchild)
            · have hroot_lt_qleft : root < qleft := by omega
              have hroot_lt_right_target : root < qright - 1 := by
                have hqleft_lt_qright : qleft < qright := harg.1
                omega
              have hright_end :
                  rightStart + rightLen = left + width := by
                unfold rightLen
                omega
              have hright_pos : 0 < rightLen := by
                unfold rightLen rightStart
                omega
              have hrightLen_lt : rightLen < len' + 1 := by
                unfold rightLen rightStart
                omega
              have hright_bound :
                  rightStart + rightLen <= xs.length := by
                rw [hright_end]
                exact hbound
              have hchild_sub_left : rightStart <= qleft := by
                unfold rightStart
                omega
              have hchild_sub_right : qright <= rightStart + rightLen := by
                rw [hright_end]
                exact hsub_right
              have hchild :
                  (treeRange xs rightStart rightLen).pathLCA?
                      qleft (qright - 1) = some idx :=
                ih rightLen hrightLen_lt rightStart hright_pos
                  hright_bound hchild_sub_left hchild_sub_right harg
              exact treeRange_pathLCA_right_lift xs (by omega)
                (by
                  simpa [treeRange, rootLabel, width, root, rightStart,
                    rightLen] using hright_pos)
                (by
                  simpa [treeRange, rootLabel, width, root] using
                    hroot_lt_qleft)
                (by
                  simpa [treeRange, rootLabel, width, root] using
                    hroot_lt_right_target)
                (by
                  simpa [treeRange, rootLabel, width, root, rightStart,
                    rightLen] using hchild))
      left hlen hbound

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

/-- Top-level endpoint-LCA certificate proposition for the built Cartesian tree. -/
def BuiltRangeLCASpec (xs : List Int) : Prop :=
  RangeLCASpec xs (tree xs)

/-- Endpoint LCAs in the built Cartesian tree are exactly RMQ witnesses. -/
theorem builtRangeLCASpec (xs : List Int) : BuiltRangeLCASpec xs := by
  unfold BuiltRangeLCASpec RangeLCASpec tree
  intro left right idx harg
  have hlen : 0 < xs.length := by
    have hleft_right : left < right := harg.1
    have hright_len : right <= xs.length := harg.2.1
    omega
  exact treeRange_rangeLCASpec xs 0 xs.length hlen (by omega)
    (by omega) (by
      have hright_len : right <= xs.length := harg.2.1
      omega) harg

/-- Concrete RMQ-to-LCA reduction from the built Cartesian tree, once certified. -/
def reduction (xs : List Int) (hspec : BuiltRangeLCASpec xs) :
    RMQToLCAReduction xs :=
  reductionOfRangeLCASpec xs (tree xs) hspec

/-- Concrete certified RMQ-to-LCA reduction from the built Cartesian tree. -/
def certifiedReduction (xs : List Int) : RMQToLCAReduction xs :=
  reduction xs (builtRangeLCASpec xs)

example : rootLabel (tree [5, 2, 7, 1, 3]) = 3 := by
  native_decide

example : (tree [5, 2, 7, 1, 3]).pathLCA? 1 4 = some 3 := by
  native_decide

example : (tree [4, 1, 1, 2]).pathLCA? 1 2 = some 1 := by
  native_decide

end Cartesian

end RMQ
