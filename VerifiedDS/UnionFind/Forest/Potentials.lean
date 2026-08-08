import VerifiedDS.UnionFind.Forest.BackendOps

namespace VerifiedDS

open RMQ

namespace UnionFind

namespace Forest

namespace ParentForest

namespace NoCompressionRankedMassBackendState

def fullCompressionFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  (backend.fullCompressFindTrace x).length

def rankGapFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some root => backend.state.rank root - backend.state.rank x + 1

def logRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some _root => Nat.log2 backend.state.forest.size + 1

/--
Coarse rank bucket used by the first Tarjan-facing accounting checkpoint.

Bucket `b` contains ranks whose successor has binary logarithm `b`; equivalently
the bucket widths grow geometrically. This is not the inverse-Ackermann level
function yet, but it is the first explicit rank-bucket interface above the
plain log-rank bound.
-/
def rankBucket (rank : Nat) : Nat :=
  Nat.log2 (rank + 1)

def rankBucketWidth (bucket : Nat) : Nat :=
  2 ^ (bucket + 1)

def rankBucketFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some root => rankBucketWidth (rankBucket (backend.state.rank root))

def unionByRankCredit
    (_backend : NoCompressionRankedMassBackendState) (_x _y : Nat) : Nat :=
  1

def rankSizePotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.state.forest.size

def rankBucketPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.state.forest.size * (Nat.log2 backend.state.forest.size + 1)

def nodeRootParentRankSlack
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 0
  | some parent => backend.state.rank root - backend.state.rank parent

def traceRootParentRankSlack
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentRankSlack root x +
        backend.traceRootParentRankSlack root xs

def nodeFindRootParentRankSlack
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root => backend.nodeRootParentRankSlack root x

def rankSlackPotentialOver
    (backend : NoCompressionRankedMassBackendState) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeFindRootParentRankSlack x +
        backend.rankSlackPotentialOver xs

def rankSlackPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.rankSlackPotentialOver (List.range backend.state.forest.size)

def rankSlackFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some _root => 2

def rankSlackUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  rankSlackPotential ((backend.unionCosted x y).erase) -
    rankSlackPotential backend + 1

def rankSlackSizeUnionCredit
    (backend : NoCompressionRankedMassBackendState) (_x _y : Nat) : Nat :=
  rankBucketPotential backend + 1

theorem log2_mono {a b : Nat} (h : a <= b) :
    Nat.log2 a <= Nat.log2 b := by
  by_cases ha : a = 0
  · subst a
    simp [Nat.log2_zero]
  · have hb : b ≠ 0 := by
      intro hb
      subst b
      exact ha (Nat.eq_zero_of_le_zero h)
    exact
      (Nat.le_log2 hb).2
        (Nat.le_trans (Nat.log2_self_le ha) h)

/--
Iterated logarithmic rank schedule.

`tarjanLevelIter 0 rank` is the raw rank. Each successor phase applies
`log2 (_ + 1)`. The concrete checkpoint below uses phase `2`, which is still
far from the inverse-Ackermann schedule but is a reusable multilevel interface:
future phases can increase the fuel without changing the node/trace potential
shape.
-/
def tarjanLevelIter : Nat -> Nat -> Nat
  | 0, rank => rank
  | phase + 1, rank => Nat.log2 (tarjanLevelIter phase rank + 1)

theorem tarjanLevelIter_mono (phase : Nat) {a b : Nat} (h : a <= b) :
    tarjanLevelIter phase a <= tarjanLevelIter phase b := by
  induction phase generalizing a b with
  | zero =>
      simpa [tarjanLevelIter] using h
  | succ phase ih =>
      have hinner : tarjanLevelIter phase a <= tarjanLevelIter phase b :=
        ih h
      have hsucc :
          tarjanLevelIter phase a + 1 <=
            tarjanLevelIter phase b + 1 := Nat.succ_le_succ hinner
      simpa [tarjanLevelIter] using log2_mono hsucc

def tarjanRankLevel (rank : Nat) : Nat :=
  tarjanLevelIter 2 rank

theorem tarjanRankLevel_mono {a b : Nat} (h : a <= b) :
    tarjanRankLevel a <= tarjanRankLevel b := by
  simpa [tarjanRankLevel] using tarjanLevelIter_mono 2 h

def nodeRootParentTarjanLevelGap
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  match backend.state.forest.parent? x with
  | none => 0
  | some parent =>
      tarjanRankLevel (backend.state.rank root) -
        tarjanRankLevel (backend.state.rank parent)

def nodeRootParentTarjanResidualSlack
    (backend : NoCompressionRankedMassBackendState)
    (root x : Nat) : Nat :=
  backend.nodeRootParentRankSlack root x -
    backend.nodeRootParentTarjanLevelGap root x

def traceRootParentTarjanLevelGap
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentTarjanLevelGap root x +
        backend.traceRootParentTarjanLevelGap root xs

def traceRootParentTarjanResidualSlack
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeRootParentTarjanResidualSlack root x +
        backend.traceRootParentTarjanResidualSlack root xs

def nodeFindRootTarjanLevelGap
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root => backend.nodeRootParentTarjanLevelGap root x

def nodeFindRootTarjanResidualSlack
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => 0
  | some root => backend.nodeRootParentTarjanResidualSlack root x

def tarjanLevelPotentialOver
    (backend : NoCompressionRankedMassBackendState) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeFindRootTarjanLevelGap x +
        backend.tarjanLevelPotentialOver xs

def tarjanLevelPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.tarjanLevelPotentialOver (List.range backend.state.forest.size)

def tarjanResidualPotentialOver
    (backend : NoCompressionRankedMassBackendState) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      backend.nodeFindRootTarjanResidualSlack x +
        backend.tarjanResidualPotentialOver xs

def tarjanResidualPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.tarjanResidualPotentialOver (List.range backend.state.forest.size)

def tarjanLevelIndexPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  tarjanLevelPotential backend + tarjanResidualPotential backend

def tarjanLevelPotentialBound
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  backend.state.forest.size *
    (tarjanRankLevel (Nat.log2 backend.state.forest.size) + 1)

def tarjanLevelFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some root =>
      backend.traceRootParentTarjanResidualSlack root
        (backend.fullCompressFindTrace x) + 2

def tarjanLevelUnionCredit
    (backend : NoCompressionRankedMassBackendState) (_x _y : Nat) : Nat :=
  tarjanLevelPotentialBound backend + 1

def tarjanLevelRootRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some root => backend.state.rank root + 1

def tarjanLevelDeltaUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  tarjanLevelPotential ((backend.unionCosted x y).erase) -
    tarjanLevelPotential backend + 1

def tarjanRankPhaseCountFuel : Nat -> Nat -> Nat
  | 0, _rank => 0
  | fuel + 1, rank =>
      if rank <= 1 then
        0
      else
        1 + tarjanRankPhaseCountFuel fuel (Nat.log2 (rank + 1))

def tarjanRankPhaseCount (rank : Nat) : Nat :=
  tarjanRankPhaseCountFuel (rank + 1) rank

def tarjanPhaseCountBound
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  tarjanRankPhaseCount (Nat.log2 backend.state.forest.size)

def tarjanPhaseCountPotential
    (backend : NoCompressionRankedMassBackendState) : Nat :=
  rankSlackPotential backend + tarjanLevelPotential backend

def tarjanPhaseCountFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some _root => backend.tarjanPhaseCountBound + 2

def tarjanPhaseCountDeltaUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  tarjanPhaseCountPotential ((backend.unionCosted x y).erase) -
    tarjanPhaseCountPotential backend + 1

def tarjanLevelIndexFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) : Nat :=
  match backend.state.forest.findRoot? x with
  | none => backend.state.forest.maxSearchFuel + 1
  | some _root => backend.tarjanPhaseCountBound + 2

def tarjanLevelIndexDeltaUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) : Nat :=
  tarjanLevelIndexPotential ((backend.unionCosted x y).erase) -
    tarjanLevelIndexPotential backend + 1

theorem nodeRootParentRankSlack_le_tarjanLevelGap_add_residual
    (backend : NoCompressionRankedMassBackendState) (root x : Nat) :
    backend.nodeRootParentRankSlack root x <=
      backend.nodeRootParentTarjanLevelGap root x +
        backend.nodeRootParentTarjanResidualSlack root x := by
  unfold nodeRootParentTarjanResidualSlack
  by_cases hle :
      backend.nodeRootParentTarjanLevelGap root x <=
        backend.nodeRootParentRankSlack root x
  · have hcancel :
        backend.nodeRootParentTarjanLevelGap root x +
            (backend.nodeRootParentRankSlack root x -
              backend.nodeRootParentTarjanLevelGap root x) =
          backend.nodeRootParentRankSlack root x := by
        exact Nat.add_sub_of_le hle
    omega
  · omega

theorem traceRootParentRankSlack_le_tarjanLevelGap_add_residual
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall trace : List Nat,
      backend.traceRootParentRankSlack root trace <=
        backend.traceRootParentTarjanLevelGap root trace +
          backend.traceRootParentTarjanResidualSlack root trace
  | [] => by
      simp [traceRootParentRankSlack, traceRootParentTarjanLevelGap,
        traceRootParentTarjanResidualSlack]
  | x :: xs => by
      have hx :=
        backend.nodeRootParentRankSlack_le_tarjanLevelGap_add_residual
          root x
      have htail :=
        traceRootParentRankSlack_le_tarjanLevelGap_add_residual
          backend root xs
      simp [traceRootParentRankSlack, traceRootParentTarjanLevelGap,
        traceRootParentTarjanResidualSlack]
      omega

theorem tarjanLevelPotentialOver_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat),
      (forall x, x ∈ xs ->
        left.nodeFindRootTarjanLevelGap x <=
          right.nodeFindRootTarjanLevelGap x) ->
      left.tarjanLevelPotentialOver xs <= right.tarjanLevelPotentialOver xs
  | [], _hle => by
      simp [tarjanLevelPotentialOver]
  | x :: xs, hle => by
      have hx :
          left.nodeFindRootTarjanLevelGap x <=
            right.nodeFindRootTarjanLevelGap x :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            left.nodeFindRootTarjanLevelGap y <=
              right.nodeFindRootTarjanLevelGap y := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        tarjanLevelPotentialOver_le_of_forall_mem left right xs hxs
      simp [tarjanLevelPotentialOver]
      omega

theorem tarjanLevelPotentialOver_le_length_mul
    (backend : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat) (bound : Nat),
      (forall x, x ∈ xs ->
        backend.nodeFindRootTarjanLevelGap x <= bound) ->
      backend.tarjanLevelPotentialOver xs <= xs.length * bound
  | [], bound, _hle => by
      simp [tarjanLevelPotentialOver]
  | x :: xs, bound, hle => by
      have hx :
          backend.nodeFindRootTarjanLevelGap x <= bound :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            backend.nodeFindRootTarjanLevelGap y <= bound := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        tarjanLevelPotentialOver_le_length_mul backend xs bound hxs
      have hmul :
          (xs.length + 1) * bound = xs.length * bound + bound := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_mul xs.length bound
      simp [tarjanLevelPotentialOver]
      calc
        backend.nodeFindRootTarjanLevelGap x +
            backend.tarjanLevelPotentialOver xs
            <= bound + xs.length * bound := Nat.add_le_add hx htail
        _ = xs.length * bound + bound := Nat.add_comm _ _
        _ = (xs.length + 1) * bound := hmul.symm

theorem tarjanLevelPotentialOver_add_single_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat) {x d : Nat},
      xs.Nodup ->
      x ∈ xs ->
      left.nodeFindRootTarjanLevelGap x + d <=
        right.nodeFindRootTarjanLevelGap x ->
      (forall y, y ∈ xs -> y ≠ x ->
        left.nodeFindRootTarjanLevelGap y <=
          right.nodeFindRootTarjanLevelGap y) ->
      left.tarjanLevelPotentialOver xs + d <=
        right.tarjanLevelPotentialOver xs
  | [], x, d, _hnodup, hmem, _hdrop, _hle => by
      simp at hmem
  | y :: ys, x, d, hnodup, hmem, hdrop, hle => by
      have hnodupCons := hnodup
      simp at hnodupCons
      rcases hnodupCons with ⟨hyNotMem, hnodupTail⟩
      by_cases hyx : y = x
      · subst x
        have htailLe :
            left.tarjanLevelPotentialOver ys <=
              right.tarjanLevelPotentialOver ys := by
          apply tarjanLevelPotentialOver_le_of_forall_mem
          intro z hz
          have hzy : z ≠ y := by
            intro hzx
            exact hyNotMem (by simpa [hzx] using hz)
          exact hle z (by simp [hz]) hzy
        simp [tarjanLevelPotentialOver]
        omega
      · have hxTail : x ∈ ys := by
          have hcases : x = y ∨ x ∈ ys := by
            simpa using hmem
          cases hcases with
          | inl hxy =>
              exact False.elim (hyx hxy.symm)
          | inr htail =>
              exact htail
        have hhead :
            left.nodeFindRootTarjanLevelGap y <=
              right.nodeFindRootTarjanLevelGap y :=
          hle y (by simp) hyx
        have htail :
            left.tarjanLevelPotentialOver ys + d <=
              right.tarjanLevelPotentialOver ys :=
          tarjanLevelPotentialOver_add_single_le_of_forall_mem
            left right ys hnodupTail hxTail hdrop (by
              intro z hz hzx
              exact hle z (by simp [hz]) hzx)
        simp [tarjanLevelPotentialOver]
        omega

theorem tarjanResidualPotentialOver_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat),
      (forall x, x ∈ xs ->
        left.nodeFindRootTarjanResidualSlack x <=
          right.nodeFindRootTarjanResidualSlack x) ->
      left.tarjanResidualPotentialOver xs <=
        right.tarjanResidualPotentialOver xs
  | [], _hle => by
      simp [tarjanResidualPotentialOver]
  | x :: xs, hle => by
      have hx :
          left.nodeFindRootTarjanResidualSlack x <=
            right.nodeFindRootTarjanResidualSlack x :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            left.nodeFindRootTarjanResidualSlack y <=
              right.nodeFindRootTarjanResidualSlack y := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        tarjanResidualPotentialOver_le_of_forall_mem left right xs hxs
      simp [tarjanResidualPotentialOver]
      omega

theorem tarjanResidualPotentialOver_add_single_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat) {x d : Nat},
      xs.Nodup ->
      x ∈ xs ->
      left.nodeFindRootTarjanResidualSlack x + d <=
        right.nodeFindRootTarjanResidualSlack x ->
      (forall y, y ∈ xs -> y ≠ x ->
        left.nodeFindRootTarjanResidualSlack y <=
          right.nodeFindRootTarjanResidualSlack y) ->
      left.tarjanResidualPotentialOver xs + d <=
        right.tarjanResidualPotentialOver xs
  | [], _x, _d, _hnodup, hmem, _hdrop, _hle => by
      simp at hmem
  | y :: ys, x, d, hnodup, hmem, hdrop, hle => by
      have hnodupCons := hnodup
      simp at hnodupCons
      rcases hnodupCons with ⟨hyNotMem, hnodupTail⟩
      by_cases hyx : y = x
      · subst x
        have htailLe :
            left.tarjanResidualPotentialOver ys <=
              right.tarjanResidualPotentialOver ys := by
          apply tarjanResidualPotentialOver_le_of_forall_mem
          intro z hz
          have hzy : z ≠ y := by
            intro hzx
            exact hyNotMem (by simpa [hzx] using hz)
          exact hle z (by simp [hz]) hzy
        simp [tarjanResidualPotentialOver]
        omega
      · have hxTail : x ∈ ys := by
          have hcases : x = y ∨ x ∈ ys := by
            simpa using hmem
          cases hcases with
          | inl hxy =>
              exact False.elim (hyx hxy.symm)
          | inr htail =>
              exact htail
        have hhead :
            left.nodeFindRootTarjanResidualSlack y <=
              right.nodeFindRootTarjanResidualSlack y :=
          hle y (by simp) hyx
        have htail :
            left.tarjanResidualPotentialOver ys + d <=
              right.tarjanResidualPotentialOver ys :=
          tarjanResidualPotentialOver_add_single_le_of_forall_mem
            left right ys hnodupTail hxTail hdrop (by
              intro z hz hzx
              exact hle z (by simp [hz]) hzx)
        simp [tarjanResidualPotentialOver]
        omega

theorem nodeFindRootTarjanLevelGap_add_residual_eq_rankSlack_of_gap_le
    (backend : NoCompressionRankedMassBackendState) (x : Nat)
    (hle :
      backend.nodeFindRootTarjanLevelGap x <=
        backend.nodeFindRootParentRankSlack x) :
    backend.nodeFindRootTarjanLevelGap x +
        backend.nodeFindRootTarjanResidualSlack x =
      backend.nodeFindRootParentRankSlack x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [nodeFindRootTarjanLevelGap, nodeFindRootTarjanResidualSlack,
        nodeFindRootParentRankSlack, hfind]
  | some root =>
      have hleRoot :
          backend.nodeRootParentTarjanLevelGap root x <=
            backend.nodeRootParentRankSlack root x := by
        simpa [nodeFindRootTarjanLevelGap, nodeFindRootParentRankSlack,
          hfind] using hle
      simpa [nodeFindRootTarjanLevelGap, nodeFindRootTarjanResidualSlack,
        nodeFindRootParentRankSlack, nodeRootParentTarjanResidualSlack,
        hfind] using
        Nat.add_sub_of_le hleRoot

theorem tarjanLevelResidualPotentialOver_eq_rankSlackPotentialOver_of_forall_gap_le
    (backend : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat),
      (forall x, x ∈ xs ->
        backend.nodeFindRootTarjanLevelGap x <=
          backend.nodeFindRootParentRankSlack x) ->
      backend.tarjanLevelPotentialOver xs +
          backend.tarjanResidualPotentialOver xs =
        backend.rankSlackPotentialOver xs
  | [], _hle => by
      simp [tarjanLevelPotentialOver, tarjanResidualPotentialOver,
        rankSlackPotentialOver]
  | x :: xs, hle => by
      have hx :
          backend.nodeFindRootTarjanLevelGap x <=
            backend.nodeFindRootParentRankSlack x :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            backend.nodeFindRootTarjanLevelGap y <=
              backend.nodeFindRootParentRankSlack y := by
        intro y hy
        exact hle y (by simp [hy])
      have hhead :=
        backend.nodeFindRootTarjanLevelGap_add_residual_eq_rankSlack_of_gap_le
          x hx
      have htail :=
        tarjanLevelResidualPotentialOver_eq_rankSlackPotentialOver_of_forall_gap_le
          backend xs hxs
      simp [tarjanLevelPotentialOver, tarjanResidualPotentialOver,
        rankSlackPotentialOver]
      omega

theorem tarjanLevelIndexPotential_eq_rankSlackPotential_of_forall_gap_le
    (backend : NoCompressionRankedMassBackendState)
    (hle :
      forall x, x ∈ List.range backend.state.forest.size ->
        backend.nodeFindRootTarjanLevelGap x <=
          backend.nodeFindRootParentRankSlack x) :
    tarjanLevelIndexPotential backend = rankSlackPotential backend := by
  unfold tarjanLevelIndexPotential tarjanLevelPotential
    tarjanResidualPotential rankSlackPotential
  exact
    backend.tarjanLevelResidualPotentialOver_eq_rankSlackPotentialOver_of_forall_gap_le
      (List.range backend.state.forest.size) hle

/--
Sum an arbitrary node index over a finite node list.

This is the abstract form of the tempting "make the residual smaller by
choosing a better local index" design.  The collapse theorem below explains
why the additive complement of such an index is not enough by itself.
-/
def subtractiveIndexPotentialOver (index : Nat -> Nat) : List Nat -> Nat
  | [] => 0
  | x :: xs => index x + subtractiveIndexPotentialOver index xs

/--
Residual complement of an arbitrary node index under the existing rank-slack
counter.
-/
def subtractiveResidualPotentialOver
    (backend : NoCompressionRankedMassBackendState)
    (index : Nat -> Nat) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      (backend.nodeFindRootParentRankSlack x - index x) +
        backend.subtractiveResidualPotentialOver index xs

def subtractiveResidualIndexPotential
    (backend : NoCompressionRankedMassBackendState)
    (index : Nat -> Nat) : Nat :=
  subtractiveIndexPotentialOver index (List.range backend.state.forest.size) +
    backend.subtractiveResidualPotentialOver index
      (List.range backend.state.forest.size)

theorem subtractiveResidualIndexPotentialOver_eq_rankSlackPotentialOver_of_forall_index_le
    (backend : NoCompressionRankedMassBackendState)
    (index : Nat -> Nat) :
    forall (xs : List Nat),
      (forall x, x ∈ xs -> index x <= backend.nodeFindRootParentRankSlack x) ->
      subtractiveIndexPotentialOver index xs +
          backend.subtractiveResidualPotentialOver index xs =
        backend.rankSlackPotentialOver xs
  | [], _hle => by
      simp [subtractiveIndexPotentialOver, subtractiveResidualPotentialOver,
        rankSlackPotentialOver]
  | x :: xs, hle => by
      have hx :
          index x <= backend.nodeFindRootParentRankSlack x :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            index y <= backend.nodeFindRootParentRankSlack y := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        subtractiveResidualIndexPotentialOver_eq_rankSlackPotentialOver_of_forall_index_le
          backend index xs hxs
      simp [subtractiveIndexPotentialOver, subtractiveResidualPotentialOver,
        rankSlackPotentialOver]
      omega

/--
Formal obstruction for additive residual-counter refinements.

Any design that chooses a node-local index bounded by rank slack and then adds
that index to its complement `rankSlack - index` is extensionally the existing
`rankSlackPotential`.  A true Tarjan residual counter therefore cannot be just
another additive split of the same local rank-slack units; it must count
events/indices with additional sequence or bucket structure.
-/
theorem subtractiveResidualIndexPotential_collapse_obstruction
    (backend : NoCompressionRankedMassBackendState)
    (index : Nat -> Nat)
    (hle :
      forall x, x ∈ List.range backend.state.forest.size ->
        index x <= backend.nodeFindRootParentRankSlack x) :
    backend.subtractiveResidualIndexPotential index =
      rankSlackPotential backend := by
  unfold subtractiveResidualIndexPotential rankSlackPotential
  exact
    backend.subtractiveResidualIndexPotentialOver_eq_rankSlackPotentialOver_of_forall_index_le
      index (List.range backend.state.forest.size) hle

end NoCompressionRankedMassBackendState

end ParentForest

end Forest

end UnionFind

end VerifiedDS
