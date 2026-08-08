import VerifiedDS.UnionFind.Forest.Potentials

namespace VerifiedDS

open RMQ

namespace UnionFind

namespace Forest

namespace ParentForest

namespace NoCompressionRankedMassBackendState

theorem compressFindCosted_nodeFindRootTarjanLevelGap_eq_zero_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootTarjanLevelGap x =
      0 := by
  have hfindEq :
      ((backend.compressFindCosted x).erase.1).state.forest.findRoot? x =
        some root := by
    rw [backend.compressFindCosted_findRoot?_eq x x]
    exact hfind
  have hparent :
      ((backend.compressFindCosted x).erase.1).state.forest.parent? x =
        some root :=
    backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
  simp [nodeFindRootTarjanLevelGap, nodeRootParentTarjanLevelGap,
    hfindEq, hparent]

theorem compressFindCosted_nodeFindRootTarjanLevelGap_le_of_ne
    (backend : NoCompressionRankedMassBackendState)
    {x y : Nat}
    (hne : y ≠ x) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootTarjanLevelGap y <=
      backend.nodeFindRootTarjanLevelGap y := by
  cases hyfind : backend.state.forest.findRoot? y with
  | none =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            none := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      simp [nodeFindRootTarjanLevelGap, hfindEq, hyfind]
  | some yroot =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            some yroot := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      have hrankEq :
          ((backend.compressFindCosted x).erase.1).state.rank =
            backend.state.rank :=
        backend.compressFindCosted_rank_eq x
      cases hparent : backend.state.forest.parent? y with
      | none =>
          have hyvalid :
              backend.state.forest.valid y :=
            backend.state.forest.valid_of_findRoot?_eq_some hyfind
          rcases backend.state.forest.exists_parent?_of_valid hyvalid with
            ⟨parent, hparentSome⟩
          rw [hparent] at hparentSome
          cases hparentSome
      | some parent =>
          have hparentNew :
              ((backend.compressFindCosted x).erase.1).state.forest.parent? y =
                some parent :=
            backend.compressFindCosted_parent?_eq_old_of_ne hne hparent
          have hparentRankLe :
              backend.state.rank parent <= backend.state.rank yroot := by
            by_cases hparentY : parent = y
            · subst hparentY
              exact backend.rank_le_root_rank_of_findRoot? hyfind
            · have hparentFind :
                  backend.state.forest.findRoot? parent = some yroot :=
                backend.findRoot?_parent_eq_of_parent?_ne
                  hparent hparentY hyfind
              exact backend.rank_le_root_rank_of_findRoot? hparentFind
          have hparentLevelLe :
              tarjanRankLevel (backend.state.rank parent) <=
                tarjanRankLevel (backend.state.rank yroot) :=
            tarjanRankLevel_mono hparentRankLe
          simp [nodeFindRootTarjanLevelGap, nodeRootParentTarjanLevelGap,
            hfindEq, hyfind, hparent, hparentNew]
          rw [hrankEq]
          omega

theorem tarjanLevelPotential_compressFindCosted_add_nodeRootParentGap_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    tarjanLevelPotential ((backend.compressFindCosted x).erase.1) +
        backend.nodeRootParentTarjanLevelGap root x <=
      tarjanLevelPotential backend := by
  let final := (backend.compressFindCosted x).erase.1
  unfold tarjanLevelPotential
  have hsize : final.state.forest.size = backend.state.forest.size := by
    simpa [final] using backend.compressFindCosted_forest_size_eq x
  rw [hsize]
  apply tarjanLevelPotentialOver_add_single_le_of_forall_mem
  · exact List.nodup_range
  · exact List.mem_range.mpr
      (backend.state.forest.valid_of_findRoot?_eq_some hfind)
  · change final.nodeFindRootTarjanLevelGap x +
        backend.nodeRootParentTarjanLevelGap root x <=
        backend.nodeFindRootTarjanLevelGap x
    have hzero :
        final.nodeFindRootTarjanLevelGap x = 0 := by
      simpa [final] using
        backend.compressFindCosted_nodeFindRootTarjanLevelGap_eq_zero_of_findRoot?
          hfind
    rw [hzero]
    simp [nodeFindRootTarjanLevelGap, hfind]
  · intro y _hymem hyx
    change final.nodeFindRootTarjanLevelGap y <=
      backend.nodeFindRootTarjanLevelGap y
    simpa [final] using
      backend.compressFindCosted_nodeFindRootTarjanLevelGap_le_of_ne hyx

theorem compressFindCosted_nodeFindRootTarjanResidualSlack_eq_zero_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootTarjanResidualSlack x =
      0 := by
  have hfindEq :
      ((backend.compressFindCosted x).erase.1).state.forest.findRoot? x =
        some root := by
    rw [backend.compressFindCosted_findRoot?_eq x x]
    exact hfind
  have hparent :
      ((backend.compressFindCosted x).erase.1).state.forest.parent? x =
        some root :=
    backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
  simp [nodeFindRootTarjanResidualSlack,
    nodeRootParentTarjanResidualSlack, nodeRootParentRankSlack,
    nodeRootParentTarjanLevelGap, hfindEq, hparent]

theorem compressFindCosted_nodeFindRootTarjanResidualSlack_le_of_ne
    (backend : NoCompressionRankedMassBackendState)
    {x y : Nat}
    (hne : y ≠ x) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootTarjanResidualSlack y <=
      backend.nodeFindRootTarjanResidualSlack y := by
  cases hyfind : backend.state.forest.findRoot? y with
  | none =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            none := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      simp [nodeFindRootTarjanResidualSlack, hfindEq, hyfind]
  | some yroot =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            some yroot := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      have hrankEq :
          ((backend.compressFindCosted x).erase.1).state.rank =
            backend.state.rank :=
        backend.compressFindCosted_rank_eq x
      cases hparent : backend.state.forest.parent? y with
      | none =>
          have hyvalid :
              backend.state.forest.valid y :=
            backend.state.forest.valid_of_findRoot?_eq_some hyfind
          rcases backend.state.forest.exists_parent?_of_valid hyvalid with
            ⟨parent, hparentSome⟩
          rw [hparent] at hparentSome
          cases hparentSome
      | some parent =>
          have hparentNew :
              ((backend.compressFindCosted x).erase.1).state.forest.parent? y =
                some parent :=
            backend.compressFindCosted_parent?_eq_old_of_ne hne hparent
          simp [nodeFindRootTarjanResidualSlack,
            nodeRootParentTarjanResidualSlack, nodeRootParentRankSlack,
            nodeRootParentTarjanLevelGap, hfindEq, hyfind, hparent,
            hparentNew]
          rw [hrankEq]
          have hsplit :=
            backend.nodeRootParentRankSlack_le_tarjanLevelGap_add_residual
              yroot y
          simp [nodeRootParentRankSlack, nodeRootParentTarjanLevelGap,
            nodeRootParentTarjanResidualSlack, hparent] at hsplit
          omega

theorem tarjanResidualPotential_compressFindCosted_add_nodeRootParentResidualSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    tarjanResidualPotential ((backend.compressFindCosted x).erase.1) +
        backend.nodeRootParentTarjanResidualSlack root x <=
      tarjanResidualPotential backend := by
  let final := (backend.compressFindCosted x).erase.1
  unfold tarjanResidualPotential
  have hsize : final.state.forest.size = backend.state.forest.size := by
    simpa [final] using backend.compressFindCosted_forest_size_eq x
  rw [hsize]
  apply tarjanResidualPotentialOver_add_single_le_of_forall_mem
  · exact List.nodup_range
  · exact List.mem_range.mpr
      (backend.state.forest.valid_of_findRoot?_eq_some hfind)
  · change final.nodeFindRootTarjanResidualSlack x +
        backend.nodeRootParentTarjanResidualSlack root x <=
        backend.nodeFindRootTarjanResidualSlack x
    have hzero :
        final.nodeFindRootTarjanResidualSlack x = 0 := by
      simpa [final] using
        backend.compressFindCosted_nodeFindRootTarjanResidualSlack_eq_zero_of_findRoot?
          hfind
    rw [hzero]
    simp [nodeFindRootTarjanResidualSlack, hfind]
  · intro y _hymem hyx
    change final.nodeFindRootTarjanResidualSlack y <=
      backend.nodeFindRootTarjanResidualSlack y
    simpa [final] using
      backend.compressFindCosted_nodeFindRootTarjanResidualSlack_le_of_ne hyx

theorem compressPathFindFuelCosted_nodeRootParentTarjanLevelGap_eq_old_of_not_mem_trace
    (backend : NoCompressionRankedMassBackendState)
    (fuel : Nat) {x y parent root : Nat}
    (hnot : y ∉ backend.compressPathFindFuelTrace fuel x)
    (hparent : backend.state.forest.parent? y = some parent) :
    ((backend.compressPathFindFuelCosted fuel x).erase.1).nodeRootParentTarjanLevelGap
      root y =
      backend.nodeRootParentTarjanLevelGap root y := by
  have hparentNew :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.parent?
        y =
        some parent :=
    backend.compressPathFindFuelCosted_parent?_eq_old_of_not_mem_trace
      fuel hnot hparent
  have hrankEq :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.rank =
        backend.state.rank :=
    backend.compressPathFindFuelCosted_rank_eq fuel x
  simp [nodeRootParentTarjanLevelGap, hparentNew, hparent]
  rw [hrankEq]

theorem rankSlackPotentialOver_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat),
      (forall x, x ∈ xs ->
        left.nodeFindRootParentRankSlack x <=
          right.nodeFindRootParentRankSlack x) ->
      left.rankSlackPotentialOver xs <= right.rankSlackPotentialOver xs
  | [], _hle => by
      simp [rankSlackPotentialOver]
  | x :: xs, hle => by
      have hx :
          left.nodeFindRootParentRankSlack x <=
            right.nodeFindRootParentRankSlack x :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            left.nodeFindRootParentRankSlack y <=
              right.nodeFindRootParentRankSlack y := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        rankSlackPotentialOver_le_of_forall_mem left right xs hxs
      simp [rankSlackPotentialOver]
      omega

theorem rankSlackPotentialOver_le_length_mul
    (backend : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat) (bound : Nat),
      (forall x, x ∈ xs ->
        backend.nodeFindRootParentRankSlack x <= bound) ->
      backend.rankSlackPotentialOver xs <= xs.length * bound
  | [], bound, _hle => by
      simp [rankSlackPotentialOver]
  | x :: xs, bound, hle => by
      have hx :
          backend.nodeFindRootParentRankSlack x <= bound :=
        hle x (by simp)
      have hxs :
          forall y, y ∈ xs ->
            backend.nodeFindRootParentRankSlack y <= bound := by
        intro y hy
        exact hle y (by simp [hy])
      have htail :=
        rankSlackPotentialOver_le_length_mul backend xs bound hxs
      have hmul :
          (xs.length + 1) * bound = xs.length * bound + bound := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_mul xs.length bound
      simp [rankSlackPotentialOver]
      calc
        backend.nodeFindRootParentRankSlack x +
            backend.rankSlackPotentialOver xs
            <= bound + xs.length * bound := Nat.add_le_add hx htail
        _ = xs.length * bound + bound := Nat.add_comm _ _
        _ = (xs.length + 1) * bound := hmul.symm

theorem rankSlackPotentialOver_add_single_le_of_forall_mem
    (left right : NoCompressionRankedMassBackendState) :
    forall (xs : List Nat) {x d : Nat},
      xs.Nodup ->
      x ∈ xs ->
      left.nodeFindRootParentRankSlack x + d <=
        right.nodeFindRootParentRankSlack x ->
      (forall y, y ∈ xs -> y ≠ x ->
        left.nodeFindRootParentRankSlack y <=
          right.nodeFindRootParentRankSlack y) ->
      left.rankSlackPotentialOver xs + d <= right.rankSlackPotentialOver xs
  | [], x, d, _hnodup, hmem, _hdrop, _hle => by
      simp at hmem
  | y :: ys, x, d, hnodup, hmem, hdrop, hle => by
      have hnodupCons := hnodup
      simp at hnodupCons
      rcases hnodupCons with ⟨hyNotMem, hnodupTail⟩
      by_cases hyx : y = x
      · subst x
        have htailLe :
            left.rankSlackPotentialOver ys <=
              right.rankSlackPotentialOver ys := by
          apply rankSlackPotentialOver_le_of_forall_mem
          intro z hz
          have hzy : z ≠ y := by
            intro hzx
            exact hyNotMem (by simpa [hzx] using hz)
          exact hle z (by simp [hz]) hzy
        simp [rankSlackPotentialOver]
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
            left.nodeFindRootParentRankSlack y <=
              right.nodeFindRootParentRankSlack y :=
          hle y (by simp) hyx
        have htail :
            left.rankSlackPotentialOver ys + d <=
              right.rankSlackPotentialOver ys :=
          rankSlackPotentialOver_add_single_le_of_forall_mem
            left right ys hnodupTail hxTail hdrop (by
              intro z hz hzx
              exact hle z (by simp [hz]) hzx)
        simp [rankSlackPotentialOver]
        omega

theorem rankSlackPotential_le_rankBucketPotential
    (backend : NoCompressionRankedMassBackendState) :
    rankSlackPotential backend <= rankBucketPotential backend := by
  unfold rankSlackPotential rankBucketPotential
  have hnode :
      forall x, x ∈ List.range backend.state.forest.size ->
        backend.nodeFindRootParentRankSlack x <=
          Nat.log2 backend.state.forest.size + 1 := by
    intro x _hx
    cases hfind : backend.state.forest.findRoot? x with
    | none =>
        simp [nodeFindRootParentRankSlack, hfind]
    | some root =>
        have hrootRank :
            backend.state.rank root <= Nat.log2 backend.state.forest.size :=
          backend.findRoot?_root_rank_le_log2_size hfind
        cases hparent : backend.state.forest.parent? x with
        | none =>
            simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
              hfind, hparent]
        | some parent =>
            have hsub :
                backend.state.rank root - backend.state.rank parent <=
                  backend.state.rank root := Nat.sub_le _ _
            simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
              hfind, hparent]
            omega
  have hsum :=
    backend.rankSlackPotentialOver_le_length_mul
      (List.range backend.state.forest.size)
      (Nat.log2 backend.state.forest.size + 1) hnode
  simpa using hsum

theorem compressFindCosted_nodeFindRootParentRankSlack_eq_zero_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootParentRankSlack x =
      0 := by
  have hfindEq :
      ((backend.compressFindCosted x).erase.1).state.forest.findRoot? x =
        some root := by
    rw [backend.compressFindCosted_findRoot?_eq x x]
    exact hfind
  have hparent :
      ((backend.compressFindCosted x).erase.1).state.forest.parent? x =
        some root :=
    backend.compressFindCosted_parent?_eq_root_of_findRoot? hfind
  have hrankEq :
      ((backend.compressFindCosted x).erase.1).state.rank =
        backend.state.rank :=
    backend.compressFindCosted_rank_eq x
  simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack, hfindEq,
    hparent]

theorem compressFindCosted_nodeFindRootParentRankSlack_le_of_ne
    (backend : NoCompressionRankedMassBackendState)
    {x y : Nat}
    (hne : y ≠ x) :
    ((backend.compressFindCosted x).erase.1).nodeFindRootParentRankSlack y <=
      backend.nodeFindRootParentRankSlack y := by
  cases hyfind : backend.state.forest.findRoot? y with
  | none =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            none := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      simp [nodeFindRootParentRankSlack, hfindEq, hyfind]
  | some yroot =>
      have hfindEq :
          ((backend.compressFindCosted x).erase.1).state.forest.findRoot? y =
            some yroot := by
        rw [backend.compressFindCosted_findRoot?_eq x y]
        exact hyfind
      have hrankEq :
          ((backend.compressFindCosted x).erase.1).state.rank =
            backend.state.rank :=
        backend.compressFindCosted_rank_eq x
      cases hparent : backend.state.forest.parent? y with
      | none =>
          have hyvalid :
              backend.state.forest.valid y :=
            backend.state.forest.valid_of_findRoot?_eq_some hyfind
          rcases backend.state.forest.exists_parent?_of_valid hyvalid with
            ⟨parent, hparentSome⟩
          rw [hparent] at hparentSome
          cases hparentSome
      | some parent =>
          have hparentNew :
              ((backend.compressFindCosted x).erase.1).state.forest.parent? y =
                some parent :=
            backend.compressFindCosted_parent?_eq_old_of_ne hne hparent
          have hparentRankLe :
              backend.state.rank parent <= backend.state.rank yroot := by
            by_cases hparentY : parent = y
            · subst hparentY
              exact backend.rank_le_root_rank_of_findRoot? hyfind
            · have hparentFind :
                  backend.state.forest.findRoot? parent = some yroot :=
                backend.findRoot?_parent_eq_of_parent?_ne
                  hparent hparentY hyfind
              exact backend.rank_le_root_rank_of_findRoot? hparentFind
          simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
            hfindEq, hyfind, hparent, hparentNew]
          rw [hrankEq]
          omega

theorem rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    rankSlackPotential ((backend.compressFindCosted x).erase.1) +
        backend.nodeRootParentRankSlack root x <=
      rankSlackPotential backend := by
  let final := (backend.compressFindCosted x).erase.1
  unfold rankSlackPotential
  have hsize : final.state.forest.size = backend.state.forest.size := by
    simpa [final] using backend.compressFindCosted_forest_size_eq x
  rw [hsize]
  apply rankSlackPotentialOver_add_single_le_of_forall_mem
  · exact List.nodup_range
  · exact List.mem_range.mpr
      (backend.state.forest.valid_of_findRoot?_eq_some hfind)
  · change final.nodeFindRootParentRankSlack x +
        backend.nodeRootParentRankSlack root x <=
        backend.nodeFindRootParentRankSlack x
    have hzero :
        final.nodeFindRootParentRankSlack x = 0 := by
      simpa [final] using
        backend.compressFindCosted_nodeFindRootParentRankSlack_eq_zero_of_findRoot?
          hfind
    rw [hzero]
    simp [nodeFindRootParentRankSlack, hfind]
  · intro y _hymem hyx
    change final.nodeFindRootParentRankSlack y <=
      backend.nodeFindRootParentRankSlack y
    simpa [final] using
      backend.compressFindCosted_nodeFindRootParentRankSlack_le_of_ne hyx

theorem compressPathFindFuelTrace_rank_le_of_mem_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root y : Nat},
      backend.state.forest.findRoot? x = some root ->
      y ∈ backend.compressPathFindFuelTrace fuel x ->
      backend.state.rank x <= backend.state.rank y
  | 0, x, root, y, _hfind, hmem => by
      have hyx : y = x := by
        simpa [compressPathFindFuelTrace] using hmem
      subst y
      omega
  | fuel + 1, x, root, y, hfind, hmem => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          have hyx : y = x := by
            simpa [compressPathFindFuelTrace, hparent] using hmem
          subst y
          omega
      | some parent =>
          by_cases hsame : parent = x
          · have hyx : y = x := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            subst y
            omega
          · have hmemCases :
                y = x ∨
                  y ∈ backend.compressPathFindFuelTrace fuel parent := by
              simpa [compressPathFindFuelTrace, hparent, hsame] using hmem
            rcases hmemCases with hyx | htailMem
            · subst y
              omega
            · have hparentFind :
                  backend.state.forest.findRoot? parent = some root :=
                backend.findRoot?_parent_eq_of_parent?_ne
                  hparent hsame hfind
              have htailRank :
                  backend.state.rank parent <= backend.state.rank y :=
                compressPathFindFuelTrace_rank_le_of_mem_of_findRoot?
                  backend fuel hparentFind htailMem
              have hparentRank :
                  backend.state.rank x < backend.state.rank parent :=
                backend.inv.toRankInvariant.parent_rank_lt hparent hsame
              omega

theorem not_mem_parent_compressPathFindFuelTrace_of_parent?_ne
    (backend : NoCompressionRankedMassBackendState)
    (fuel : Nat) {x parent root : Nat}
    (hparent : backend.state.forest.parent? x = some parent)
    (hne : parent ≠ x)
    (hparentFind : backend.state.forest.findRoot? parent = some root) :
    x ∉ backend.compressPathFindFuelTrace fuel parent := by
  intro hmem
  have htailRank :
      backend.state.rank parent <= backend.state.rank x :=
    backend.compressPathFindFuelTrace_rank_le_of_mem_of_findRoot?
      fuel hparentFind hmem
  have hparentRank :
      backend.state.rank x < backend.state.rank parent :=
    backend.inv.toRankInvariant.parent_rank_lt hparent hne
  omega

theorem compressPathFindFuelCosted_tarjanLevelPotential_add_traceLevelGap_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      tarjanLevelPotential ((backend.compressPathFindFuelCosted fuel x).erase.1) +
          backend.traceRootParentTarjanLevelGap root
            (backend.compressPathFindFuelTrace fuel x) <=
        tarjanLevelPotential backend
  | 0, x, root, hfind => by
      simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
        traceRootParentTarjanLevelGap] using
        backend.tarjanLevelPotential_compressFindCosted_add_nodeRootParentGap_le_of_findRoot?
          hfind
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
            traceRootParentTarjanLevelGap, hparent] using
            backend.tarjanLevelPotential_compressFindCosted_add_nodeRootParentGap_le_of_findRoot?
              hfind
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentTarjanLevelGap, hparent, hsame] using
              backend.tarjanLevelPotential_compressFindCosted_add_nodeRootParentGap_le_of_findRoot?
                hfind
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne
                hparent hsame hfind
            let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htailDrop :
                tarjanLevelPotential tail +
                    backend.traceRootParentTarjanLevelGap root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  tarjanLevelPotential backend := by
              simpa [tail] using
                compressPathFindFuelCosted_tarjanLevelPotential_add_traceLevelGap_le_of_findRoot?
                  backend fuel hparentFind
            have htailFindX :
                tail.state.forest.findRoot? x = some root := by
              rw [show tail.state.forest.findRoot? x =
                    backend.state.forest.findRoot? x by
                simpa [tail] using
                  backend.compressPathFindFuelCosted_findRoot?_eq
                    fuel parent x]
              exact hfind
            have hxNotTail :
                x ∉ backend.compressPathFindFuelTrace fuel parent :=
              backend.not_mem_parent_compressPathFindFuelTrace_of_parent?_ne
                fuel hparent hsame hparentFind
            have hxGap :
                tail.nodeRootParentTarjanLevelGap root x =
                  backend.nodeRootParentTarjanLevelGap root x := by
              simpa [tail] using
                backend.compressPathFindFuelCosted_nodeRootParentTarjanLevelGap_eq_old_of_not_mem_trace
                  fuel hxNotTail hparent
            have hstep :
                tarjanLevelPotential ((tail.compressFindCosted x).erase.1) +
                    tail.nodeRootParentTarjanLevelGap root x <=
                  tarjanLevelPotential tail :=
              tail.tarjanLevelPotential_compressFindCosted_add_nodeRootParentGap_le_of_findRoot?
                htailFindX
            rw [hxGap] at hstep
            have hcombine :
                tarjanLevelPotential ((tail.compressFindCosted x).erase.1) +
                    backend.nodeRootParentTarjanLevelGap root x +
                    backend.traceRootParentTarjanLevelGap root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  tarjanLevelPotential backend := by
              omega
            simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentTarjanLevelGap, hparent, hsame, tail,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcombine

theorem tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) +
        backend.traceRootParentTarjanLevelGap root
          (backend.fullCompressFindTrace x) <=
      tarjanLevelPotential backend := by
  simpa [fullCompressFindCosted, fullCompressFindTrace] using
    backend.compressPathFindFuelCosted_tarjanLevelPotential_add_traceLevelGap_le_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem compressPathFindFuelCosted_nodeRootParentRankSlack_eq_old_of_not_mem_trace
    (backend : NoCompressionRankedMassBackendState)
    (fuel : Nat) {x y parent root : Nat}
    (hnot : y ∉ backend.compressPathFindFuelTrace fuel x)
    (hparent : backend.state.forest.parent? y = some parent) :
    ((backend.compressPathFindFuelCosted fuel x).erase.1).nodeRootParentRankSlack
      root y =
      backend.nodeRootParentRankSlack root y := by
  have hparentNew :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.forest.parent?
        y =
        some parent :=
    backend.compressPathFindFuelCosted_parent?_eq_old_of_not_mem_trace
      fuel hnot hparent
  have hrankEq :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).state.rank =
        backend.state.rank :=
    backend.compressPathFindFuelCosted_rank_eq fuel x
  simp [nodeRootParentRankSlack, hparentNew, hparent]
  rw [hrankEq]

theorem compressPathFindFuelCosted_nodeRootParentTarjanResidualSlack_eq_old_of_not_mem_trace
    (backend : NoCompressionRankedMassBackendState)
    (fuel : Nat) {x y parent root : Nat}
    (hnot : y ∉ backend.compressPathFindFuelTrace fuel x)
    (hparent : backend.state.forest.parent? y = some parent) :
    ((backend.compressPathFindFuelCosted fuel x).erase.1).nodeRootParentTarjanResidualSlack
      root y =
      backend.nodeRootParentTarjanResidualSlack root y := by
  have hslack :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).nodeRootParentRankSlack
        root y =
        backend.nodeRootParentRankSlack root y :=
    backend.compressPathFindFuelCosted_nodeRootParentRankSlack_eq_old_of_not_mem_trace
      fuel hnot hparent
  have hgap :
      ((backend.compressPathFindFuelCosted fuel x).erase.1).nodeRootParentTarjanLevelGap
        root y =
        backend.nodeRootParentTarjanLevelGap root y :=
    backend.compressPathFindFuelCosted_nodeRootParentTarjanLevelGap_eq_old_of_not_mem_trace
      fuel hnot hparent
  unfold nodeRootParentTarjanResidualSlack
  rw [hslack, hgap]

theorem compressPathFindFuelCosted_rankSlackPotential_add_traceRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      rankSlackPotential ((backend.compressPathFindFuelCosted fuel x).erase.1) +
          backend.traceRootParentRankSlack root
            (backend.compressPathFindFuelTrace fuel x) <=
        rankSlackPotential backend
  | 0, x, root, hfind => by
      simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
        traceRootParentRankSlack] using
        backend.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
          hfind
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
            traceRootParentRankSlack, hparent] using
            backend.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
              hfind
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentRankSlack, hparent, hsame] using
              backend.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
                hfind
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne
                hparent hsame hfind
            let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htailDrop :
                rankSlackPotential tail +
                    backend.traceRootParentRankSlack root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  rankSlackPotential backend := by
              simpa [tail] using
                compressPathFindFuelCosted_rankSlackPotential_add_traceRootParentRankSlack_le_of_findRoot?
                  backend fuel hparentFind
            have htailFindX :
                tail.state.forest.findRoot? x = some root := by
              rw [show tail.state.forest.findRoot? x =
                    backend.state.forest.findRoot? x by
                simpa [tail] using
                  backend.compressPathFindFuelCosted_findRoot?_eq
                    fuel parent x]
              exact hfind
            have hxNotTail :
                x ∉ backend.compressPathFindFuelTrace fuel parent :=
              backend.not_mem_parent_compressPathFindFuelTrace_of_parent?_ne
                fuel hparent hsame hparentFind
            have hxSlack :
                tail.nodeRootParentRankSlack root x =
                  backend.nodeRootParentRankSlack root x := by
              simpa [tail] using
                backend.compressPathFindFuelCosted_nodeRootParentRankSlack_eq_old_of_not_mem_trace
                  fuel hxNotTail hparent
            have hstep :
                rankSlackPotential ((tail.compressFindCosted x).erase.1) +
                    tail.nodeRootParentRankSlack root x <=
                  rankSlackPotential tail :=
              tail.rankSlackPotential_compressFindCosted_add_nodeRootParentRankSlack_le_of_findRoot?
                htailFindX
            rw [hxSlack] at hstep
            have hcombine :
                rankSlackPotential ((tail.compressFindCosted x).erase.1) +
                    backend.nodeRootParentRankSlack root x +
                    backend.traceRootParentRankSlack root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  rankSlackPotential backend := by
              omega
            simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentRankSlack, hparent, hsame, tail, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using hcombine

theorem compressPathFindFuelCosted_tarjanResidualPotential_add_traceResidualSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      tarjanResidualPotential ((backend.compressPathFindFuelCosted fuel x).erase.1) +
          backend.traceRootParentTarjanResidualSlack root
            (backend.compressPathFindFuelTrace fuel x) <=
        tarjanResidualPotential backend
  | 0, x, root, hfind => by
      simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
        traceRootParentTarjanResidualSlack] using
        backend.tarjanResidualPotential_compressFindCosted_add_nodeRootParentResidualSlack_le_of_findRoot?
          hfind
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
            traceRootParentTarjanResidualSlack, hparent] using
            backend.tarjanResidualPotential_compressFindCosted_add_nodeRootParentResidualSlack_le_of_findRoot?
              hfind
      | some parent =>
          by_cases hsame : parent = x
          · simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentTarjanResidualSlack, hparent, hsame] using
              backend.tarjanResidualPotential_compressFindCosted_add_nodeRootParentResidualSlack_le_of_findRoot?
                hfind
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne
                hparent hsame hfind
            let tail :=
              (backend.compressPathFindFuelCosted fuel parent).erase.1
            have htailDrop :
                tarjanResidualPotential tail +
                    backend.traceRootParentTarjanResidualSlack root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  tarjanResidualPotential backend := by
              simpa [tail] using
                compressPathFindFuelCosted_tarjanResidualPotential_add_traceResidualSlack_le_of_findRoot?
                  backend fuel hparentFind
            have htailFindX :
                tail.state.forest.findRoot? x = some root := by
              rw [show tail.state.forest.findRoot? x =
                    backend.state.forest.findRoot? x by
                simpa [tail] using
                  backend.compressPathFindFuelCosted_findRoot?_eq
                    fuel parent x]
              exact hfind
            have hxNotTail :
                x ∉ backend.compressPathFindFuelTrace fuel parent :=
              backend.not_mem_parent_compressPathFindFuelTrace_of_parent?_ne
                fuel hparent hsame hparentFind
            have hxResidual :
                tail.nodeRootParentTarjanResidualSlack root x =
                  backend.nodeRootParentTarjanResidualSlack root x := by
              simpa [tail] using
                backend.compressPathFindFuelCosted_nodeRootParentTarjanResidualSlack_eq_old_of_not_mem_trace
                  fuel hxNotTail hparent
            have hstep :
                tarjanResidualPotential ((tail.compressFindCosted x).erase.1) +
                    tail.nodeRootParentTarjanResidualSlack root x <=
                  tarjanResidualPotential tail :=
              tail.tarjanResidualPotential_compressFindCosted_add_nodeRootParentResidualSlack_le_of_findRoot?
                htailFindX
            rw [hxResidual] at hstep
            have hcombine :
                tarjanResidualPotential ((tail.compressFindCosted x).erase.1) +
                    backend.nodeRootParentTarjanResidualSlack root x +
                    backend.traceRootParentTarjanResidualSlack root
                      (backend.compressPathFindFuelTrace fuel parent) <=
                  tarjanResidualPotential backend := by
              omega
            simpa [compressPathFindFuelCosted, compressPathFindFuelTrace,
              traceRootParentTarjanResidualSlack, hparent, hsame, tail,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcombine

theorem rankSlackPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) +
        backend.traceRootParentRankSlack root (backend.fullCompressFindTrace x) <=
      rankSlackPotential backend := by
  simpa [fullCompressFindCosted, fullCompressFindTrace] using
    backend.compressPathFindFuelCosted_rankSlackPotential_add_traceRootParentRankSlack_le_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem tarjanResidualPotential_fullCompressFindCosted_add_traceResidualSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    tarjanResidualPotential ((backend.fullCompressFindCosted x).erase.1) +
        backend.traceRootParentTarjanResidualSlack root
          (backend.fullCompressFindTrace x) <=
      tarjanResidualPotential backend := by
  simpa [fullCompressFindCosted, fullCompressFindTrace] using
    backend.compressPathFindFuelCosted_tarjanResidualPotential_add_traceResidualSlack_le_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem fullCompressFindCosted_eq_self_of_findRoot?_none
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat}
    (hfind : backend.state.forest.findRoot? x = none) :
    (backend.fullCompressFindCosted x).erase.1 = backend := by
  have hinvalid :
      ¬ backend.state.forest.valid x :=
    backend.state.forest.invalid_of_findRoot?_eq_none
      backend.inv.toInvariant hfind
  have hparent : backend.state.forest.parent? x = none := by
    cases hparent : backend.state.forest.parent? x with
    | none => rfl
    | some parent =>
        have hx : backend.state.forest.valid x :=
          backend.state.forest.valid_of_parent?_eq_some hparent
        exact False.elim (hinvalid hx)
  cases hfuel : backend.state.forest.maxSearchFuel with
  | zero =>
      unfold fullCompressFindCosted
      rw [hfuel]
      simp [compressPathFindFuelCosted,
        compressFindCosted, backend.compressFindResult_none x hfind]
  | succ fuel =>
      unfold fullCompressFindCosted
      rw [hfuel]
      simp [compressPathFindFuelCosted, hparent,
        compressFindCosted, backend.compressFindResult_none x hfind]

theorem rankSlackPotential_fullCompressFindCosted_eq_of_findRoot?_none
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat}
    (hfind : backend.state.forest.findRoot? x = none) :
    rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) =
      rankSlackPotential backend := by
  rw [backend.fullCompressFindCosted_eq_self_of_findRoot?_none hfind]

theorem tarjanResidualPotential_fullCompressFindCosted_eq_of_findRoot?_none
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat}
    (hfind : backend.state.forest.findRoot? x = none) :
    tarjanResidualPotential ((backend.fullCompressFindCosted x).erase.1) =
      tarjanResidualPotential backend := by
  rw [backend.fullCompressFindCosted_eq_self_of_findRoot?_none hfind]

theorem rank_succ_le_rankBucketWidth (rank : Nat) :
    rank + 1 <= rankBucketWidth (rankBucket rank) := by
  have hlt : rank + 1 < 2 ^ (Nat.log2 (rank + 1) + 1) :=
    Nat.lt_log2_self (n := rank + 1)
  exact Nat.le_of_lt (by
    simpa [rankBucket, rankBucketWidth] using hlt)

theorem fullCompressFindCosted_cost_le_rankGapFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.rankGapFindCredit x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hcost := backend.fullCompressFindCosted_cost_le x
      simpa [rankGapFindCredit, hfind] using hcost
  | some root =>
      have hcostEq := backend.fullCompressFindCosted_cost_eq_trace_length x
      have htrace :=
        backend.fullCompressFindTrace_length_le_rank_gap_of_findRoot? hfind
      rw [hcostEq]
      simpa [rankGapFindCredit, hfind] using htrace

theorem rankGapFindCredit_le_tarjanLevelRootRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    backend.rankGapFindCredit x <=
      backend.tarjanLevelRootRankFindCredit x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [rankGapFindCredit, tarjanLevelRootRankFindCredit, hfind]
  | some root =>
      simp [rankGapFindCredit, tarjanLevelRootRankFindCredit, hfind]

theorem fullCompressFindCosted_cost_le_tarjanLevelRootRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.tarjanLevelRootRankFindCredit x :=
  Nat.le_trans
    (backend.fullCompressFindCosted_cost_le_rankGapFindCredit x)
    (backend.rankGapFindCredit_le_tarjanLevelRootRankFindCredit x)

theorem rankGapFindCredit_le_logRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    backend.rankGapFindCredit x <= backend.logRankFindCredit x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [rankGapFindCredit, logRankFindCredit, hfind]
  | some root =>
      have hroot :=
        backend.findRoot?_root_rank_le_log2_size hfind
      have hsub :
          backend.state.rank root - backend.state.rank x <=
            backend.state.rank root := Nat.sub_le _ _
      simp [rankGapFindCredit, logRankFindCredit, hfind]
      omega

theorem fullCompressFindCosted_cost_le_logRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.logRankFindCredit x := by
  exact Nat.le_trans
    (backend.fullCompressFindCosted_cost_le_rankGapFindCredit x)
    (backend.rankGapFindCredit_le_logRankFindCredit x)

theorem rankGapFindCredit_le_rankBucketFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    backend.rankGapFindCredit x <= backend.rankBucketFindCredit x := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      simp [rankGapFindCredit, rankBucketFindCredit, hfind]
  | some root =>
      have hbucket :=
        rank_succ_le_rankBucketWidth (backend.state.rank root)
      have hsub :
          backend.state.rank root - backend.state.rank x <=
            backend.state.rank root := Nat.sub_le _ _
      simp [rankGapFindCredit, rankBucketFindCredit, hfind]
      omega

theorem fullCompressFindTrace_length_le_rankBucketWidth_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindTrace x).length <=
      rankBucketWidth (rankBucket (backend.state.rank root)) := by
  have hgap :=
    backend.fullCompressFindTrace_length_le_rank_gap_of_findRoot? hfind
  have hbucket :=
    rank_succ_le_rankBucketWidth (backend.state.rank root)
  have hsub :
      backend.state.rank root - backend.state.rank x <=
        backend.state.rank root := Nat.sub_le _ _
  omega

theorem compressPathFindFuelTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
    (backend : NoCompressionRankedMassBackendState) :
    forall (fuel : Nat) {x root : Nat},
      backend.state.forest.findRoot? x = some root ->
      (backend.compressPathFindFuelTrace fuel x).length <=
        backend.traceRootParentRankSlack root
          (backend.compressPathFindFuelTrace fuel x) + 2
  | 0, x, root, _hfind => by
      simp [compressPathFindFuelTrace, traceRootParentRankSlack]
  | fuel + 1, x, root, hfind => by
      cases hparent : backend.state.forest.parent? x with
      | none =>
          simp [compressPathFindFuelTrace, traceRootParentRankSlack, hparent]
      | some parent =>
          by_cases hsame : parent = x
          · simp [compressPathFindFuelTrace, traceRootParentRankSlack,
              nodeRootParentRankSlack, hparent, hsame]
          · have hparentFind :
                backend.state.forest.findRoot? parent = some root :=
              backend.findRoot?_parent_eq_of_parent?_ne hparent hsame hfind
            by_cases hparentRoot : parent = root
            · have hroot :
                  backend.state.forest.IsRoot root :=
                backend.state.forest.findRoot?_some_root
                  backend.inv.toInvariant hfind
              have htail :
                  backend.compressPathFindFuelTrace fuel root = [root] :=
                backend.compressPathFindFuelTrace_eq_singleton_of_root
                  fuel hroot
              have hrootNeX : root ≠ x := by
                intro hrootX
                exact hsame (hparentRoot.trans hrootX)
              simp [compressPathFindFuelTrace, traceRootParentRankSlack,
                nodeRootParentRankSlack, hparent, hparentRoot, htail,
                hrootNeX]
            · have htail :=
                compressPathFindFuelTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
                  backend fuel hparentFind
              have hparentRank :
                  backend.state.rank parent < backend.state.rank root :=
                backend.state.forest.findRoot?_rank_lt_of_ne
                  backend.state.rank backend.inv.toRankInvariant
                  hparentFind hparentRoot
              have hslack :
                  1 <= backend.nodeRootParentRankSlack root x := by
                simp [nodeRootParentRankSlack, hparent]
                omega
              simp [compressPathFindFuelTrace, traceRootParentRankSlack,
                hparent, hsame]
              omega

theorem fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindTrace x).length <=
      backend.traceRootParentRankSlack root
        (backend.fullCompressFindTrace x) + 2 := by
  simpa [fullCompressFindTrace] using
    backend.compressPathFindFuelTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
      backend.state.forest.maxSearchFuel hfind

theorem fullCompressFindCosted_nodeRootParentRankSlack_eq_zero_of_trace_mem
    (backend : NoCompressionRankedMassBackendState)
    {x root y : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hmem : y ∈ backend.fullCompressFindTrace x) :
    ((backend.fullCompressFindCosted x).erase.1).nodeRootParentRankSlack
      root y = 0 := by
  have hparent :=
    backend.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
      hfind hmem
  simp [nodeRootParentRankSlack, hparent]

theorem traceRootParentRankSlack_eq_zero_of_forall
    (backend : NoCompressionRankedMassBackendState) (root : Nat) :
    forall (trace : List Nat),
      (forall y, y ∈ trace -> backend.nodeRootParentRankSlack root y = 0) ->
        backend.traceRootParentRankSlack root trace = 0
  | [], _h => by
      simp [traceRootParentRankSlack]
  | y :: ys, h => by
      have hy : backend.nodeRootParentRankSlack root y = 0 := by
        exact h y (by simp)
      have hys :
          forall z, z ∈ ys ->
            backend.nodeRootParentRankSlack root z = 0 := by
        intro z hz
        exact h z (by simp [hz])
      have htail :=
        traceRootParentRankSlack_eq_zero_of_forall backend root ys hys
      simp [traceRootParentRankSlack, hy, htail]

theorem fullCompressFindCosted_traceRootParentRankSlack_eq_zero_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
      root (backend.fullCompressFindTrace x) = 0 := by
  apply traceRootParentRankSlack_eq_zero_of_forall
  intro y hmem
  exact
    backend.fullCompressFindCosted_nodeRootParentRankSlack_eq_zero_of_trace_mem
      hfind hmem

theorem fullCompressFindCosted_cost_add_traceRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindCosted x).cost +
        ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
          root (backend.fullCompressFindTrace x) <=
      2 + backend.traceRootParentRankSlack root
        (backend.fullCompressFindTrace x) := by
  have hcost := backend.fullCompressFindCosted_cost_eq_trace_length x
  have hlen :=
    backend.fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
      hfind
  have hzero :=
    backend.fullCompressFindCosted_traceRootParentRankSlack_eq_zero_of_findRoot?
      hfind
  rw [hcost, hzero]
  omega

theorem fullCompressFindCosted_cost_add_rankSlackPotential_le_two_add_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      2 + rankSlackPotential backend := by
  have hlocal :=
    backend.fullCompressFindCosted_cost_add_traceRootParentRankSlack_le_of_findRoot?
      hfind
  have hdrop :=
    backend.rankSlackPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?
      hfind
  omega

theorem fullCompressFindCosted_cost_add_rankSlackPotential_le_rankSlackFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankSlackFindCredit x + rankSlackPotential backend := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hcost := backend.fullCompressFindCosted_cost_le x
      have hpot :=
        backend.rankSlackPotential_fullCompressFindCosted_eq_of_findRoot?_none
          hfind
      simp [rankSlackFindCredit, hfind]
      rw [hpot]
      omega
  | some root =>
      have hbound :=
        backend.fullCompressFindCosted_cost_add_rankSlackPotential_le_two_add_of_findRoot?
          hfind
      simpa [rankSlackFindCredit, hfind] using hbound

theorem fullCompressFindCosted_nodeFindRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root y : Nat}
    (hfind : backend.state.forest.findRoot? x = some root)
    (hy : backend.state.forest.valid y) :
    ((backend.fullCompressFindCosted x).erase.1).nodeFindRootParentRankSlack
      y <= backend.nodeFindRootParentRankSlack y := by
  let final := (backend.fullCompressFindCosted x).erase.1
  have hfindEq :
      final.state.forest.findRoot? y =
      backend.state.forest.findRoot? y := by
    simpa [final] using backend.fullCompressFindCosted_findRoot?_eq x y
  have hrankEq : final.state.rank = backend.state.rank := by
    simpa [final] using backend.fullCompressFindCosted_rank_eq x
  change final.nodeFindRootParentRankSlack y <=
    backend.nodeFindRootParentRankSlack y
  by_cases hmem : y ∈ backend.fullCompressFindTrace x
  · have hyFind :
        backend.state.forest.findRoot? y = some root :=
      backend.fullCompressFindTrace_mem_findRoot?_eq_of_findRoot?
        hfind hmem
    have hzero :
        final.nodeRootParentRankSlack root y = 0 := by
      simpa [final] using
        backend.fullCompressFindCosted_nodeRootParentRankSlack_eq_zero_of_trace_mem
          hfind hmem
    simp [nodeFindRootParentRankSlack, hfindEq, hyFind, hzero]
  · rcases backend.state.forest.exists_parent?_of_valid hy with
      ⟨parent, hparent⟩
    have hparentFinal :
        final.state.forest.parent? y = some parent := by
      simpa [final] using
        backend.fullCompressFindCosted_parent?_eq_old_of_not_mem_trace
          hmem hparent
    cases hyFind : backend.state.forest.findRoot? y with
    | none =>
        simp [nodeFindRootParentRankSlack, hfindEq, hyFind]
    | some yroot =>
        have hparentRankLe :
            backend.state.rank parent <= backend.state.rank yroot := by
          by_cases hparentY : parent = y
          · subst hparentY
            exact backend.rank_le_root_rank_of_findRoot? hyFind
          · have hparentFind :
                backend.state.forest.findRoot? parent = some yroot :=
              backend.findRoot?_parent_eq_of_parent?_ne
                hparent hparentY hyFind
            exact backend.rank_le_root_rank_of_findRoot? hparentFind
        simp [nodeFindRootParentRankSlack, nodeRootParentRankSlack,
          hfindEq, hyFind, hparent, hparentFinal]
        rw [hrankEq]
        omega

theorem rankSlackPotential_fullCompressFindCosted_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      rankSlackPotential backend := by
  let final := (backend.fullCompressFindCosted x).erase.1
  unfold rankSlackPotential
  have hsize : final.state.forest.size = backend.state.forest.size := by
    simpa [final] using backend.fullCompressFindCosted_forest_size_eq x
  rw [hsize]
  apply rankSlackPotentialOver_le_of_forall_mem
  intro y hyMem
  have hy : backend.state.forest.valid y := by
    exact List.mem_range.mp hyMem
  simpa [final] using
    backend.fullCompressFindCosted_nodeFindRootParentRankSlack_le_of_findRoot?
      hfind hy

theorem fullCompressionRankSlackCheckpoint_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      ((backend.fullCompressFindCosted x).erase.1).state.rank =
        backend.state.rank) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        (backend.fullCompressFindTrace x).length <=
          backend.traceRootParentRankSlack root
            (backend.fullCompressFindTrace x) + 2) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
          root (backend.fullCompressFindTrace x) = 0) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        (backend.fullCompressFindCosted x).cost +
            ((backend.fullCompressFindCosted x).erase.1).traceRootParentRankSlack
              root (backend.fullCompressFindTrace x) <=
          2 + backend.traceRootParentRankSlack root
            (backend.fullCompressFindTrace x)) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root : Nat},
        backend.state.forest.findRoot? x = some root ->
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
          rankSlackPotential backend) := by
  constructor
  · intro backend x
    exact backend.fullCompressFindCosted_rank_eq x
  · constructor
    · intro backend x root hfind
      exact
        backend.fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
          hfind
    · constructor
      · intro backend x root hfind
        exact
          backend.fullCompressFindCosted_traceRootParentRankSlack_eq_zero_of_findRoot?
            hfind
      · constructor
        · intro backend x root hfind
          exact
            backend.fullCompressFindCosted_cost_add_traceRootParentRankSlack_le_of_findRoot?
              hfind
        · intro backend x root hfind
          exact
            backend.rankSlackPotential_fullCompressFindCosted_le_of_findRoot?
              hfind

theorem fullCompressFindCosted_cost_le_rankBucketFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost <=
      backend.rankBucketFindCredit x := by
  exact Nat.le_trans
    (backend.fullCompressFindCosted_cost_le_rankGapFindCredit x)
    (backend.rankGapFindCredit_le_rankBucketFindCredit x)

theorem rankSizePotential_fullCompressFindCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    rankSizePotential ((backend.fullCompressFindCosted x).erase.1) =
      rankSizePotential backend := by
  simpa [rankSizePotential] using
    backend.fullCompressFindCosted_forest_size_eq x

theorem rankSizePotential_unionCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    rankSizePotential ((backend.unionCosted x y).erase) =
      rankSizePotential backend := by
  simp [rankSizePotential, unionCosted, unionResult,
    NoCompressionRankedMassForest.unionCosted]

theorem rankBucketPotential_fullCompressFindCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    rankBucketPotential ((backend.fullCompressFindCosted x).erase.1) =
      rankBucketPotential backend := by
  unfold rankBucketPotential
  rw [backend.fullCompressFindCosted_forest_size_eq x]

theorem rankBucketPotential_unionCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    rankBucketPotential ((backend.unionCosted x y).erase) =
      rankBucketPotential backend := by
  simp [rankBucketPotential, unionCosted, unionResult,
    NoCompressionRankedMassForest.unionCosted]

theorem tarjanLevelPotential_le_bound
    (backend : NoCompressionRankedMassBackendState) :
    tarjanLevelPotential backend <= tarjanLevelPotentialBound backend := by
  unfold tarjanLevelPotential tarjanLevelPotentialBound
  have hnode :
      forall x, x ∈ List.range backend.state.forest.size ->
        backend.nodeFindRootTarjanLevelGap x <=
          tarjanRankLevel (Nat.log2 backend.state.forest.size) + 1 := by
    intro x _hx
    cases hfind : backend.state.forest.findRoot? x with
    | none =>
        simp [nodeFindRootTarjanLevelGap, hfind]
    | some root =>
        have hrootRank :
            backend.state.rank root <= Nat.log2 backend.state.forest.size :=
          backend.findRoot?_root_rank_le_log2_size hfind
        have hrootLevel :
            tarjanRankLevel (backend.state.rank root) <=
              tarjanRankLevel (Nat.log2 backend.state.forest.size) :=
          tarjanRankLevel_mono hrootRank
        cases hparent : backend.state.forest.parent? x with
        | none =>
            simp [nodeFindRootTarjanLevelGap, nodeRootParentTarjanLevelGap,
              hfind, hparent]
        | some parent =>
            have hgap :
                tarjanRankLevel (backend.state.rank root) -
                    tarjanRankLevel (backend.state.rank parent) <=
                  tarjanRankLevel (backend.state.rank root) := Nat.sub_le _ _
            simp [nodeFindRootTarjanLevelGap, nodeRootParentTarjanLevelGap,
              hfind, hparent]
            omega
  have hsum :=
    backend.tarjanLevelPotentialOver_le_length_mul
      (List.range backend.state.forest.size)
      (tarjanRankLevel (Nat.log2 backend.state.forest.size) + 1) hnode
  simpa using hsum

theorem tarjanLevelPotentialBound_unionCosted_eq
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    tarjanLevelPotentialBound ((backend.unionCosted x y).erase) =
      tarjanLevelPotentialBound backend := by
  simp [tarjanLevelPotentialBound, unionCosted, unionResult,
    NoCompressionRankedMassForest.unionCosted]

theorem tarjanLevelPotential_unionCosted_le_bound
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    tarjanLevelPotential ((backend.unionCosted x y).erase) <=
      tarjanLevelPotentialBound backend := by
  have hle :=
    tarjanLevelPotential_le_bound ((backend.unionCosted x y).erase)
  have hbound := backend.tarjanLevelPotentialBound_unionCosted_eq x y
  rwa [hbound] at hle

theorem rankSlackPotential_unionCosted_le_rankBucketPotential
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    rankSlackPotential ((backend.unionCosted x y).erase) <=
      rankBucketPotential backend := by
  have hle :=
    rankSlackPotential_le_rankBucketPotential ((backend.unionCosted x y).erase)
  have hbucket := backend.rankBucketPotential_unionCosted_eq x y
  rwa [hbucket] at hle

theorem unionCosted_cost_add_rankSlackPotential_le_rankSlackSizeUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost +
        rankSlackPotential ((backend.unionCosted x y).erase) <=
      backend.rankSlackSizeUnionCredit x y + rankSlackPotential backend := by
  have hcost : (backend.unionCosted x y).cost = 1 := by
    rfl
  have hpot := backend.rankSlackPotential_unionCosted_le_rankBucketPotential x y
  rw [hcost]
  unfold rankSlackSizeUnionCredit
  omega

theorem tarjanLevelPotential_fullCompressFindCosted_eq_of_findRoot?_none
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat}
    (hfind : backend.state.forest.findRoot? x = none) :
    tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) =
      tarjanLevelPotential backend := by
  rw [backend.fullCompressFindCosted_eq_self_of_findRoot?_none hfind]

theorem fullCompressFindCosted_cost_add_tarjanLevelPotential_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindCosted x).cost +
        tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.traceRootParentTarjanResidualSlack root
          (backend.fullCompressFindTrace x) + 2 +
        tarjanLevelPotential backend := by
  have hcostEq := backend.fullCompressFindCosted_cost_eq_trace_length x
  have hlen :=
    backend.fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
      hfind
  have hsplit :=
    backend.traceRootParentRankSlack_le_tarjanLevelGap_add_residual
      root (backend.fullCompressFindTrace x)
  have hdrop :=
    backend.tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?
      hfind
  rw [hcostEq]
  omega

theorem fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost +
        tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanLevelFindCredit x + tarjanLevelPotential backend := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hcost := backend.fullCompressFindCosted_cost_le x
      have hpot :=
        backend.tarjanLevelPotential_fullCompressFindCosted_eq_of_findRoot?_none
          hfind
      simp [tarjanLevelFindCredit, hfind]
      rw [hpot]
      omega
  | some root =>
      have hbound :=
        backend.fullCompressFindCosted_cost_add_tarjanLevelPotential_le_of_findRoot?
          hfind
      simpa [tarjanLevelFindCredit, hfind, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hbound

theorem unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost +
        tarjanLevelPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanLevelUnionCredit x y + tarjanLevelPotential backend := by
  have hcost : (backend.unionCosted x y).cost = 1 := by
    rfl
  have hpot := backend.tarjanLevelPotential_unionCosted_le_bound x y
  rw [hcost]
  unfold tarjanLevelUnionCredit
  omega

theorem tarjanLevelPotential_fullCompressFindCosted_le
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) <=
      tarjanLevelPotential backend := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hpot :=
        backend.tarjanLevelPotential_fullCompressFindCosted_eq_of_findRoot?_none
          hfind
      omega
  | some root =>
      have hdrop :=
        backend.tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?
          hfind
      omega

theorem fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelRootRankFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost +
        tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanLevelRootRankFindCredit x + tarjanLevelPotential backend := by
  have hcost :=
    backend.fullCompressFindCosted_cost_le_tarjanLevelRootRankFindCredit x
  have hpot := backend.tarjanLevelPotential_fullCompressFindCosted_le x
  omega

theorem unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelDeltaUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost +
        tarjanLevelPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanLevelDeltaUnionCredit x y +
        tarjanLevelPotential backend := by
  have hcost : (backend.unionCosted x y).cost = 1 := by
    rfl
  let before := tarjanLevelPotential backend
  let after := tarjanLevelPotential ((backend.unionCosted x y).erase)
  change (backend.unionCosted x y).cost + after <=
    backend.tarjanLevelDeltaUnionCredit x y + before
  rw [hcost]
  unfold tarjanLevelDeltaUnionCredit
  change 1 + after <= (after - before + 1) + before
  by_cases hle : before <= after
  · have hcancel : after - before + before = after :=
      Nat.sub_add_cancel hle
    omega
  · have hle' : after <= before := by
      omega
    have hzero : after - before = 0 :=
      Nat.sub_eq_zero_of_le hle'
    omega

theorem tarjanLevelDeltaUnionCredit_le_tarjanLevelUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    backend.tarjanLevelDeltaUnionCredit x y <=
      backend.tarjanLevelUnionCredit x y := by
  have hpot := backend.tarjanLevelPotential_unionCosted_le_bound x y
  unfold tarjanLevelDeltaUnionCredit tarjanLevelUnionCredit
  omega

theorem fullCompressFindCosted_cost_add_tarjanPhaseCountPotential_le_tarjanPhaseCountFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost +
        tarjanPhaseCountPotential
          ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanPhaseCountFindCredit x +
        tarjanPhaseCountPotential backend := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hcost := backend.fullCompressFindCosted_cost_le x
      have hrank :=
        backend.rankSlackPotential_fullCompressFindCosted_eq_of_findRoot?_none
          hfind
      have hlevel :=
        backend.tarjanLevelPotential_fullCompressFindCosted_eq_of_findRoot?_none
          hfind
      simp [tarjanPhaseCountFindCredit, hfind, tarjanPhaseCountPotential]
      rw [hrank, hlevel]
      omega
  | some root =>
      have hrank :
          (backend.fullCompressFindCosted x).cost +
              rankSlackPotential
                ((backend.fullCompressFindCosted x).erase.1) <=
            2 + rankSlackPotential backend := by
        have h :=
          backend.fullCompressFindCosted_cost_add_rankSlackPotential_le_rankSlackFindCredit
            x
        simpa [rankSlackFindCredit, hfind] using h
      have hlevel := backend.tarjanLevelPotential_fullCompressFindCosted_le x
      simp [tarjanPhaseCountFindCredit, hfind, tarjanPhaseCountPotential]
      omega

theorem unionCosted_cost_add_tarjanPhaseCountPotential_le_tarjanPhaseCountDeltaUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost +
        tarjanPhaseCountPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanPhaseCountDeltaUnionCredit x y +
        tarjanPhaseCountPotential backend := by
  have hcost : (backend.unionCosted x y).cost = 1 := by
    rfl
  let before := tarjanPhaseCountPotential backend
  let after := tarjanPhaseCountPotential ((backend.unionCosted x y).erase)
  change (backend.unionCosted x y).cost + after <=
    backend.tarjanPhaseCountDeltaUnionCredit x y + before
  rw [hcost]
  unfold tarjanPhaseCountDeltaUnionCredit
  change 1 + after <= (after - before + 1) + before
  by_cases hle : before <= after
  · have hcancel : after - before + before = after :=
      Nat.sub_add_cancel hle
    omega
  · have hle' : after <= before := by
      omega
    have hzero : after - before = 0 :=
      Nat.sub_eq_zero_of_le hle'
    omega

theorem tarjanLevelIndexPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    tarjanLevelIndexPotential ((backend.fullCompressFindCosted x).erase.1) +
        backend.traceRootParentRankSlack root (backend.fullCompressFindTrace x) <=
      tarjanLevelIndexPotential backend := by
  have hlevel :=
    backend.tarjanLevelPotential_fullCompressFindCosted_add_traceLevelGap_le_of_findRoot?
      hfind
  have hresidual :=
    backend.tarjanResidualPotential_fullCompressFindCosted_add_traceResidualSlack_le_of_findRoot?
      hfind
  have hsplit :=
    backend.traceRootParentRankSlack_le_tarjanLevelGap_add_residual
      root (backend.fullCompressFindTrace x)
  unfold tarjanLevelIndexPotential
  omega

theorem fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_two_add_of_findRoot?
    (backend : NoCompressionRankedMassBackendState)
    {x root : Nat}
    (hfind : backend.state.forest.findRoot? x = some root) :
    (backend.fullCompressFindCosted x).cost +
        tarjanLevelIndexPotential ((backend.fullCompressFindCosted x).erase.1) <=
      2 + tarjanLevelIndexPotential backend := by
  have hcostEq := backend.fullCompressFindCosted_cost_eq_trace_length x
  have hlen :=
    backend.fullCompressFindTrace_length_le_traceRootParentRankSlack_add_two_of_findRoot?
      hfind
  have hdrop :=
    backend.tarjanLevelIndexPotential_fullCompressFindCosted_add_traceRootParentRankSlack_le_of_findRoot?
      hfind
  rw [hcostEq]
  omega

theorem tarjanLevelIndexPotential_fullCompressFindCosted_eq_of_findRoot?_none
    (backend : NoCompressionRankedMassBackendState)
    {x : Nat}
    (hfind : backend.state.forest.findRoot? x = none) :
    tarjanLevelIndexPotential ((backend.fullCompressFindCosted x).erase.1) =
      tarjanLevelIndexPotential backend := by
  unfold tarjanLevelIndexPotential
  rw [backend.tarjanLevelPotential_fullCompressFindCosted_eq_of_findRoot?_none hfind,
    backend.tarjanResidualPotential_fullCompressFindCosted_eq_of_findRoot?_none hfind]

theorem fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexFindCredit
    (backend : NoCompressionRankedMassBackendState) (x : Nat) :
    (backend.fullCompressFindCosted x).cost +
        tarjanLevelIndexPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanLevelIndexFindCredit x +
        tarjanLevelIndexPotential backend := by
  cases hfind : backend.state.forest.findRoot? x with
  | none =>
      have hcost := backend.fullCompressFindCosted_cost_le x
      have hpot :=
        backend.tarjanLevelIndexPotential_fullCompressFindCosted_eq_of_findRoot?_none
          hfind
      simp [tarjanLevelIndexFindCredit, hfind]
      rw [hpot]
      omega
  | some root =>
      have hbound :=
        backend.fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_two_add_of_findRoot?
          hfind
      simp [tarjanLevelIndexFindCredit, hfind]
      omega

theorem unionCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexDeltaUnionCredit
    (backend : NoCompressionRankedMassBackendState) (x y : Nat) :
    (backend.unionCosted x y).cost +
        tarjanLevelIndexPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanLevelIndexDeltaUnionCredit x y +
        tarjanLevelIndexPotential backend := by
  have hcost : (backend.unionCosted x y).cost = 1 := by
    rfl
  let before := tarjanLevelIndexPotential backend
  let after := tarjanLevelIndexPotential ((backend.unionCosted x y).erase)
  change (backend.unionCosted x y).cost + after <=
    backend.tarjanLevelIndexDeltaUnionCredit x y + before
  rw [hcost]
  unfold tarjanLevelIndexDeltaUnionCredit
  change 1 + after <= (after - before + 1) + before
  by_cases hle : before <= after
  · have hcancel : after - before + before = after :=
      Nat.sub_add_cancel hle
    omega
  · have hle' : after <= before := by
      omega
    have hzero : after - before = 0 :=
      Nat.sub_eq_zero_of_le hle'
    omega

end NoCompressionRankedMassBackendState

end ParentForest

end Forest

end UnionFind

end VerifiedDS
