import RMQ.Core.UnionFind.Forest.PotentialProofs

namespace RMQ

namespace UnionFind

namespace Forest

namespace ParentForest

namespace NoCompressionRankedMassBackendState

/--
Potential-method scaffold for the current representation backend.

The potential is intentionally zero and the compressed-find credit is the
actual executable trace length.  This is not Tarjan's amortized bound; it is the
checked boundary a future nonzero potential can strengthen.
-/
def fullCompressionRepresentationAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      representationZeroPotential
      fullCompressionFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
      representationZeroPotential fullCompressionFindCredit
    simp [fullCompressionRepresentationBackend,
      fullCompressFindCosted_cost_eq_trace_length]
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
      representationZeroPotential unionByRankCredit
    simp [fullCompressionRepresentationBackend, unionCosted]

theorem fullCompressionRepresentationAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRepresentationAmortizedBackend.findCosted backend x)
        (representationZeroPotential backend)
        (representationZeroPotential
          ((fullCompressionRepresentationAmortizedBackend.findCosted backend x).erase.1))
        (fullCompressionFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRepresentationAmortizedBackend.unionCosted backend x y)
          (representationZeroPotential backend)
          (representationZeroPotential
            (fullCompressionRepresentationAmortizedBackend.unionCosted
              backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionRepresentationAmortizedBackend.find_amortized
  · exact fullCompressionRepresentationAmortizedBackend.union_amortized

/--
First nonzero-potential checkpoint for full compression.

The potential is the current finite forest size, and the find credit is the
rank gap from the queried node to its returned root (falling back to the fuel
bound for invalid nodes).  The potential is coarse and does not yet encode
Tarjan's rank buckets, but the find credit is no longer the executed trace
length: it is discharged by the rank-gap trace theorem.
-/
def fullCompressionRankGapAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSizePotential
      rankGapFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    have hcost := backend.fullCompressFindCosted_cost_le_rankGapFindCredit x
    have hpot := backend.rankSizePotential_fullCompressFindCosted_eq x
    change (backend.fullCompressFindCosted x).cost +
        rankSizePotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankGapFindCredit x + rankSizePotential backend
    rw [hpot]
    omega
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    have hpot := backend.rankSizePotential_unionCosted_eq x y
    change (backend.unionCosted x y).cost +
        rankSizePotential ((backend.unionCosted x y).erase) <=
      backend.unionByRankCredit x y + rankSizePotential backend
    rw [hpot]
    simp [unionByRankCredit]

theorem fullCompressionRankGapAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankGapAmortizedBackend.findCosted backend x)
        (rankSizePotential backend)
        (rankSizePotential
          ((fullCompressionRankGapAmortizedBackend.findCosted backend x).erase.1))
        (rankGapFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankGapAmortizedBackend.unionCosted backend x y)
          (rankSizePotential backend)
          (rankSizePotential
            (fullCompressionRankGapAmortizedBackend.unionCosted backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionRankGapAmortizedBackend.find_amortized
  · exact fullCompressionRankGapAmortizedBackend.union_amortized

/--
Log-rank credit checkpoint for full compression.

For successful finds, the credit is now bounded by `log2 forest.size + 1`
instead of the returned root's concrete rank gap. Invalid queries retain the
same fuel fallback as the rank-gap credit.
-/
def fullCompressionLogRankAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSizePotential
      logRankFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    have hcost := backend.fullCompressFindCosted_cost_le_logRankFindCredit x
    have hpot := backend.rankSizePotential_fullCompressFindCosted_eq x
    change (backend.fullCompressFindCosted x).cost +
        rankSizePotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.logRankFindCredit x + rankSizePotential backend
    rw [hpot]
    omega
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    have hpot := backend.rankSizePotential_unionCosted_eq x y
    change (backend.unionCosted x y).cost +
        rankSizePotential ((backend.unionCosted x y).erase) <=
      backend.unionByRankCredit x y + rankSizePotential backend
    rw [hpot]
    simp [unionByRankCredit]

theorem fullCompressionLogRankAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionLogRankAmortizedBackend.findCosted backend x)
        (rankSizePotential backend)
        (rankSizePotential
          ((fullCompressionLogRankAmortizedBackend.findCosted backend x).erase.1))
        (logRankFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionLogRankAmortizedBackend.unionCosted backend x y)
          (rankSizePotential backend)
          (rankSizePotential
            (fullCompressionLogRankAmortizedBackend.unionCosted backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionLogRankAmortizedBackend.find_amortized
  · exact fullCompressionLogRankAmortizedBackend.union_amortized

/--
First explicit rank-bucket amortized checkpoint for full compression.

The successful-find credit is the geometric width of the returned root's rank
bucket. This is coarser than the log-rank checkpoint and still not Tarjan's
inverse-Ackermann analysis, but it exposes the bucket schedule and proves that
bucket width can pay the existing rank-gap trace bound.
-/
def fullCompressionRankBucketAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankBucketPotential
      rankBucketFindCredit
      unionByRankCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    have hcost := backend.fullCompressFindCosted_cost_le_rankBucketFindCredit x
    have hpot := backend.rankBucketPotential_fullCompressFindCosted_eq x
    change (backend.fullCompressFindCosted x).cost +
        rankBucketPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankBucketFindCredit x + rankBucketPotential backend
    rw [hpot]
    omega
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    have hpot := backend.rankBucketPotential_unionCosted_eq x y
    change (backend.unionCosted x y).cost +
        rankBucketPotential ((backend.unionCosted x y).erase) <=
      backend.unionByRankCredit x y + rankBucketPotential backend
    rw [hpot]
    simp [unionByRankCredit]

theorem fullCompressionRankBucketAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankBucketAmortizedBackend.findCosted backend x)
        (rankBucketPotential backend)
        (rankBucketPotential
          ((fullCompressionRankBucketAmortizedBackend.findCosted backend x).erase.1))
        (rankBucketFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankBucketAmortizedBackend.unionCosted backend x y)
          (rankBucketPotential backend)
          (rankBucketPotential
            (fullCompressionRankBucketAmortizedBackend.unionCosted backend x y).erase)
          (unionByRankCredit backend x y)) := by
  constructor
  · exact fullCompressionRankBucketAmortizedBackend.find_amortized
  · exact fullCompressionRankBucketAmortizedBackend.union_amortized

/--
Rank-slack potential checkpoint for full compression.

Successful finds are paid with constant credit `2`: the aggregate
`rankSlackPotential` drops by enough to cover the trace-root parent slack, and
the local trace theorem converts that slack into the actual trace cost. Invalid
queries retain the fuel fallback. Union uses an explicit potential-delta credit
because this checkpoint is about compression paying for find, not yet about a
Tarjan-tight union/find combined schedule.
-/
def fullCompressionRankSlackAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSlackPotential
      rankSlackFindCredit
      rankSlackUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankSlackFindCredit x + rankSlackPotential backend
    exact backend.fullCompressFindCosted_cost_add_rankSlackPotential_le_rankSlackFindCredit x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    let before := rankSlackPotential backend
    let after := rankSlackPotential ((backend.unionCosted x y).erase)
    change (backend.unionCosted x y).cost + after <=
      backend.rankSlackUnionCredit x y + before
    have hcost : (backend.unionCosted x y).cost = 1 := by
      rfl
    rw [hcost]
    unfold rankSlackUnionCredit
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

theorem fullCompressionRankSlackAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankSlackAmortizedBackend.findCosted backend x)
        (rankSlackPotential backend)
        (rankSlackPotential
          ((fullCompressionRankSlackAmortizedBackend.findCosted backend x).erase.1))
        (rankSlackFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankSlackAmortizedBackend.unionCosted backend x y)
          (rankSlackPotential backend)
          (rankSlackPotential
            (fullCompressionRankSlackAmortizedBackend.unionCosted backend x y).erase)
          (rankSlackUnionCredit backend x y)) := by
  constructor
  · exact fullCompressionRankSlackAmortizedBackend.find_amortized
  · exact fullCompressionRankSlackAmortizedBackend.union_amortized

/--
Rank-slack checkpoint with a non-delta union credit.

This keeps the constant successful-find credit from
`fullCompressionRankSlackAmortizedBackend`, but replaces the union credit
`potential_after - potential_before + 1` with the explicit size-log bound
`rankBucketPotential backend + 1`.  The bound is intentionally coarse; its job
is to remove the answer-shaped delta credit before the later Tarjan potential is
designed.
-/
def fullCompressionRankSlackSizeUnionAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      rankSlackPotential
      rankSlackFindCredit
      rankSlackSizeUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        rankSlackPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.rankSlackFindCredit x + rankSlackPotential backend
    exact
      backend.fullCompressFindCosted_cost_add_rankSlackPotential_le_rankSlackFindCredit x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.unionCosted x y).cost +
        rankSlackPotential ((backend.unionCosted x y).erase) <=
      backend.rankSlackSizeUnionCredit x y + rankSlackPotential backend
    exact
      backend.unionCosted_cost_add_rankSlackPotential_le_rankSlackSizeUnionCredit
        x y

theorem fullCompressionRankSlackSizeUnionAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionRankSlackSizeUnionAmortizedBackend.findCosted backend x)
        (rankSlackPotential backend)
        (rankSlackPotential
          ((fullCompressionRankSlackSizeUnionAmortizedBackend.findCosted
            backend x).erase.1))
        (rankSlackFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionRankSlackSizeUnionAmortizedBackend.unionCosted
            backend x y)
          (rankSlackPotential backend)
          (rankSlackPotential
            (fullCompressionRankSlackSizeUnionAmortizedBackend.unionCosted
              backend x y).erase)
          (rankSlackSizeUnionCredit backend x y)) := by
  constructor
  · exact fullCompressionRankSlackSizeUnionAmortizedBackend.find_amortized
  · exact fullCompressionRankSlackSizeUnionAmortizedBackend.union_amortized

/--
First multilevel Tarjan-style amortized checkpoint.

The potential sums only the cross-level part of each node's parent-to-root rank
gap, where levels are produced by the executable `tarjanLevelIter` schedule.
Successful finds charge the residual rank slack that remains within the current
level, plus constant `2`; the aggregate level potential pays the cross-level
part of the compression trace. Union uses the level-specific global bound
`tarjanLevelPotentialBound`, not the previous full rank-slack bound.

This is still not the inverse-Ackermann theorem. It is the first backend-shaped
interface where the accounting separates level jumps from within-level debt,
which is the reusable boundary a later Tarjan analysis can refine by increasing
the phase schedule and shrinking the residual credit.
-/
def fullCompressionTarjanLevelAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      tarjanLevelPotential
      tarjanLevelFindCredit
      tarjanLevelUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanLevelFindCredit x + tarjanLevelPotential backend
    exact
      backend.fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelFindCredit
        x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.unionCosted x y).cost +
        tarjanLevelPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanLevelUnionCredit x y + tarjanLevelPotential backend
    exact
      backend.unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelUnionCredit
        x y

theorem fullCompressionTarjanLevelAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionTarjanLevelAmortizedBackend.findCosted backend x)
        (tarjanLevelPotential backend)
        (tarjanLevelPotential
          ((fullCompressionTarjanLevelAmortizedBackend.findCosted
            backend x).erase.1))
        (tarjanLevelFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionTarjanLevelAmortizedBackend.unionCosted backend x y)
          (tarjanLevelPotential backend)
          (tarjanLevelPotential
            (fullCompressionTarjanLevelAmortizedBackend.unionCosted
              backend x y).erase)
          (tarjanLevelUnionCredit backend x y)) := by
  constructor
  · exact fullCompressionTarjanLevelAmortizedBackend.find_amortized
  · exact fullCompressionTarjanLevelAmortizedBackend.union_amortized

/--
Trace-free Tarjan-level clean-credit checkpoint.

This keeps the multilevel `tarjanLevelPotential`, but replaces the successful
find credit from `tarjanLevelFindCredit` with the returned root's rank plus one
and replaces the whole-forest union credit with the local potential delta plus
one.  The find credit is therefore independent of `fullCompressFindTrace`, and
the union credit is no larger than `tarjanLevelUnionCredit`.

This is cleaner accounting around the current Tarjan-level scaffold, not the
inverse-Ackermann theorem: the successful-find credit is still a rank-count
bound, not an alpha-style phase count.
-/
def fullCompressionTarjanLevelCleanCreditAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      tarjanLevelPotential
      tarjanLevelRootRankFindCredit
      tarjanLevelDeltaUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        tarjanLevelPotential ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanLevelRootRankFindCredit x +
        tarjanLevelPotential backend
    exact
      backend.fullCompressFindCosted_cost_add_tarjanLevelPotential_le_tarjanLevelRootRankFindCredit
        x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.unionCosted x y).cost +
        tarjanLevelPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanLevelDeltaUnionCredit x y +
        tarjanLevelPotential backend
    exact
      backend.unionCosted_cost_add_tarjanLevelPotential_le_tarjanLevelDeltaUnionCredit
        x y

theorem fullCompressionTarjanLevelCleanCreditAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionTarjanLevelCleanCreditAmortizedBackend.findCosted
          backend x)
        (tarjanLevelPotential backend)
        (tarjanLevelPotential
          ((fullCompressionTarjanLevelCleanCreditAmortizedBackend.findCosted
            backend x).erase.1))
        (tarjanLevelRootRankFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionTarjanLevelCleanCreditAmortizedBackend.unionCosted
            backend x y)
          (tarjanLevelPotential backend)
          (tarjanLevelPotential
            (fullCompressionTarjanLevelCleanCreditAmortizedBackend.unionCosted
              backend x y).erase)
          (tarjanLevelDeltaUnionCredit backend x y)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        backend.tarjanLevelDeltaUnionCredit x y <=
          backend.tarjanLevelUnionCredit x y) := by
  constructor
  · exact fullCompressionTarjanLevelCleanCreditAmortizedBackend.find_amortized
  · constructor
    · exact
        fullCompressionTarjanLevelCleanCreditAmortizedBackend.union_amortized
    · intro backend x y
      exact backend.tarjanLevelDeltaUnionCredit_le_tarjanLevelUnionCredit x y

/--
Phase-count Tarjan-level checkpoint with residual slack absorbed into potential.

The potential is the sum of the aggregate rank-slack potential and the
Tarjan-level cross-gap potential.  This absorbs the residual slack that the
first Tarjan-level profile exposed in `tarjanLevelFindCredit`, so successful
finds are charged only the global iterated-log phase count
`tarjanPhaseCountBound backend + 2`.

This is an alpha-shaped interface checkpoint, not the inverse-Ackermann theorem:
the phase count is still derived from a fixed iterated-log collapse of
`log2 forest.size`, and the potential still includes the full rank-slack layer.
-/
def fullCompressionTarjanPhaseCountAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      tarjanPhaseCountPotential
      tarjanPhaseCountFindCredit
      tarjanPhaseCountDeltaUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        tarjanPhaseCountPotential
          ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanPhaseCountFindCredit x +
        tarjanPhaseCountPotential backend
    exact
      backend.fullCompressFindCosted_cost_add_tarjanPhaseCountPotential_le_tarjanPhaseCountFindCredit
        x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.unionCosted x y).cost +
        tarjanPhaseCountPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanPhaseCountDeltaUnionCredit x y +
        tarjanPhaseCountPotential backend
    exact
      backend.unionCosted_cost_add_tarjanPhaseCountPotential_le_tarjanPhaseCountDeltaUnionCredit
        x y

theorem fullCompressionTarjanPhaseCountAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionTarjanPhaseCountAmortizedBackend.findCosted
          backend x)
        (tarjanPhaseCountPotential backend)
        (tarjanPhaseCountPotential
          ((fullCompressionTarjanPhaseCountAmortizedBackend.findCosted
            backend x).erase.1))
        (tarjanPhaseCountFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionTarjanPhaseCountAmortizedBackend.unionCosted
            backend x y)
          (tarjanPhaseCountPotential backend)
          (tarjanPhaseCountPotential
            (fullCompressionTarjanPhaseCountAmortizedBackend.unionCosted
              backend x y).erase)
          (tarjanPhaseCountDeltaUnionCredit backend x y)) := by
  constructor
  · exact fullCompressionTarjanPhaseCountAmortizedBackend.find_amortized
  · exact fullCompressionTarjanPhaseCountAmortizedBackend.union_amortized

/--
Level-index Tarjan checkpoint with the rank slack split made explicit.

The previous phase-count profile hid the full `rankSlackPotential` inside
`tarjanPhaseCountPotential`.  This profile uses the aggregate cross-level
potential plus an explicit residual-index potential instead. Successful finds
retain the phase-count-shaped credit `tarjanPhaseCountBound + 2`, while the
proof shows that the level gap and residual index together drop enough to pay
the trace-root parent rank slack.

This is still below the full inverse-Ackermann theorem: the residual index is
raw within-level rank slack rather than a recursively bucketed Ackermann index.
It is the backend boundary the next step must shrink.
-/
def fullCompressionTarjanLevelIndexAmortizedBackend :
    RepresentationAmortizedBackend NoCompressionRankedMassBackendState
      tarjanLevelIndexPotential
      tarjanLevelIndexFindCredit
      tarjanLevelIndexDeltaUnionCredit where
  toRepresentationBackend := fullCompressionRepresentationBackend
  find_amortized := by
    intro backend x
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.fullCompressFindCosted x).cost +
        tarjanLevelIndexPotential
          ((backend.fullCompressFindCosted x).erase.1) <=
      backend.tarjanLevelIndexFindCredit x +
        tarjanLevelIndexPotential backend
    exact
      backend.fullCompressFindCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexFindCredit
        x
  union_amortized := by
    intro backend x y
    unfold Amortized.CostedBound Amortized.Bound
    change (backend.unionCosted x y).cost +
        tarjanLevelIndexPotential ((backend.unionCosted x y).erase) <=
      backend.tarjanLevelIndexDeltaUnionCredit x y +
        tarjanLevelIndexPotential backend
    exact
      backend.unionCosted_cost_add_tarjanLevelIndexPotential_le_tarjanLevelIndexDeltaUnionCredit
        x y

theorem fullCompressionTarjanLevelIndexAmortizedBackend_profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      Amortized.CostedBound
        (fullCompressionTarjanLevelIndexAmortizedBackend.findCosted
          backend x)
        (tarjanLevelIndexPotential backend)
        (tarjanLevelIndexPotential
          ((fullCompressionTarjanLevelIndexAmortizedBackend.findCosted
            backend x).erase.1))
        (tarjanLevelIndexFindCredit backend x)) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        Amortized.CostedBound
          (fullCompressionTarjanLevelIndexAmortizedBackend.unionCosted
            backend x y)
          (tarjanLevelIndexPotential backend)
          (tarjanLevelIndexPotential
            (fullCompressionTarjanLevelIndexAmortizedBackend.unionCosted
              backend x y).erase)
          (tarjanLevelIndexDeltaUnionCredit backend x y)) := by
  constructor
  · exact fullCompressionTarjanLevelIndexAmortizedBackend.find_amortized
  · exact fullCompressionTarjanLevelIndexAmortizedBackend.union_amortized

theorem profile :
    (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
      (backend.findCosted x).cost = 1 /\
        (backend.findCosted x).erase.2 =
          backend.abstractState.find? x /\
        State.SamePartition
          (abstractState (backend.findCosted x).erase.1)
          backend.abstractState) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
        (backend.compressFindCosted x).cost = 1 /\
          (backend.compressFindCosted x).erase.2 =
            backend.abstractState.find? x /\
          State.SamePartition
            (abstractState (backend.compressFindCosted x).erase.1)
            backend.abstractState) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x : Nat),
        (backend.fullCompressFindCosted x).cost <=
            backend.state.forest.maxSearchFuel + 1 /\
          (backend.fullCompressFindCosted x).erase.2 =
            backend.abstractState.find? x /\
          (forall i,
            ((backend.fullCompressFindCosted x).erase.1).state.forest.findRoot?
              i =
            backend.state.forest.findRoot? i) /\
          State.SamePartition
            (abstractState (backend.fullCompressFindCosted x).erase.1)
            backend.abstractState) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        {x root y : Nat},
        backend.state.forest.findRoot? x = some root ->
        y ∈ backend.fullCompressFindTrace x ->
        ((backend.fullCompressFindCosted x).erase.1).state.forest.parent? y =
          some root) /\
      (forall (backend : NoCompressionRankedMassBackendState) (x y : Nat),
        (backend.unionCosted x y).cost = 1 /\
          State.SamePartition
            (abstractState (backend.unionCosted x y).erase)
            (backend.abstractState.unionSpec x y)) /\
      (forall (backend : NoCompressionRankedMassBackendState)
        (ops : List (Nat × Nat)),
        (backend.unionManyCosted ops).cost = ops.length /\
          State.SamePartition
            (abstractState (backend.unionManyCosted ops).erase)
            (backend.abstractState.unionSpecMany ops)) := by
  constructor
  · intro backend x
    exact findCosted_refinement_profile backend x
  · constructor
    · intro backend x
      exact compressFindCosted_refinement_profile backend x
    · constructor
      · intro backend x
        exact fullCompressFindCosted_refinement_profile backend x
      · constructor
        · intro backend x root y hfind hmem
          exact backend.fullCompressFindCosted_trace_parent?_eq_root_of_findRoot?
            hfind hmem
        · constructor
          · intro backend x y
            exact unionCosted_refinement_profile backend x y
          · intro backend ops
            exact unionManyCosted_refinement_profile backend ops

end NoCompressionRankedMassBackendState

end ParentForest

end Forest

end UnionFind

end RMQ
