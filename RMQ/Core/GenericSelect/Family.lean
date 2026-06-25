import RMQ.Core.GenericSelect.Source
import RMQ.Core.RankSelectSpec

/-!
# Generic select Jacobson/Clark family layer

This module combines the generic sparse-exception select source with the
Jacobson rank directory and exposes the public plain-bitvector rank/select
family profile.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRankProposal

/--
Uniform modeled query bound for the public Jacobson/Clark bitvector adapter.

Rank comes from the concrete Jacobson two-level directory (`<= 4` ticks), while
select comes from the sparse/dense Clark source (`<= sparseDenseSelectQueryCost`).
-/
def jacobsonClarkRankSelectQueryCost : Nat :=
  Nat.max 4 sparseDenseSelectQueryCost

/--
Auxiliary payload budget for a plain bitvector rank/select family using
Jacobson rank plus independent Clark select sources for `false` and `true`.

The stored `n` input bits are counted by `RankSelectSpec`; this function counts
only the auxiliary rank/select directories.
-/
def jacobsonClarkRankSelectOverhead (n : Nat) : Nat :=
  SuccinctRankProposal.jacobsonRankOverhead n +
    canonicalSparseExceptionSelectOverhead n +
      canonicalSparseExceptionSelectOverhead n

theorem jacobsonClarkRankSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear jacobsonClarkRankSelectOverhead := by
  simpa [jacobsonClarkRankSelectOverhead] using
    (SuccinctRankProposal.jacobsonRankOverhead_littleO.add
      canonicalSparseExceptionSelectOverhead_littleO).add
        canonicalSparseExceptionSelectOverhead_littleO

/--
Concrete auxiliary payload prefix read by the public adapter: Jacobson rank
metadata followed by the two Clark sparse/dense select payloads.
-/
def jacobsonClarkRankSelectAuxPayload (bits : List Bool) : List Bool :=
  (SuccinctRankProposal.jacobsonRankData bits).auxPayload ++
    (sparseExceptionSelectSource bits false).payload ++
      (sparseExceptionSelectSource bits true).payload

theorem jacobsonClarkRankSelectAuxPayload_length_le
    (bits : List Bool) :
    (jacobsonClarkRankSelectAuxPayload bits).length <=
      jacobsonClarkRankSelectOverhead bits.length := by
  have hrankEq :
      (SuccinctRankProposal.jacobsonRankData bits).auxPayload.length =
        SuccinctRankProposal.jacobsonRankOverhead bits.length := by
    have hprofile := SuccinctRankProposal.jacobsonRankData_profile bits
    simpa [SuccinctRankProposal.jacobsonRankOverhead,
      SuccinctRankProposal.twoLevelRankOverhead] using hprofile.1
  have hfalse :
      (sparseExceptionSelectSource bits false).payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length := by
    have h :=
      (sparseExceptionSelectSource bits false).payload_length_le
    simpa [sparseExceptionSelectSource,
      SparseExceptionSelectData.toChargedSelectPositionSource] using h
  have htrue :
      (sparseExceptionSelectSource bits true).payload.length <=
        canonicalSparseExceptionSelectOverhead bits.length := by
    have h :=
      (sparseExceptionSelectSource bits true).payload_length_le
    simpa [sparseExceptionSelectSource,
      SparseExceptionSelectData.toChargedSelectPositionSource] using h
  simp [jacobsonClarkRankSelectAuxPayload,
    jacobsonClarkRankSelectOverhead, List.length_append]
  omega

/--
Published auxiliary payload padded to the clean `o(n)` overhead expression.
The padding is inert: queries below call the concrete rank/select components,
not a semantic oracle over the padded bits.
-/
def jacobsonClarkRankSelectPaddedAuxPayload
    (bits : List Bool) : List Bool :=
  let payload := jacobsonClarkRankSelectAuxPayload bits
  payload ++
    List.replicate
      (jacobsonClarkRankSelectOverhead bits.length - payload.length) false

@[simp] theorem jacobsonClarkRankSelectPaddedAuxPayload_length
    (bits : List Bool) :
    (jacobsonClarkRankSelectPaddedAuxPayload bits).length =
      jacobsonClarkRankSelectOverhead bits.length := by
  have hle := jacobsonClarkRankSelectAuxPayload_length_le bits
  simp [jacobsonClarkRankSelectPaddedAuxPayload]
  omega

/--
Rank/select directory that combines the concrete Jacobson rank builder with
two concrete generic Clark select sources, one per bit value.
-/
def jacobsonClarkRankSelectDirectory (bits : List Bool) :
    SuccinctSpace.RankSelectDirectory bits
      (jacobsonClarkRankSelectOverhead bits.length)
      jacobsonClarkRankSelectQueryCost where
  Aux := Unit
  buildAux := ()
  encodeAux := fun _ => jacobsonClarkRankSelectPaddedAuxPayload bits
  rankCosted := fun _ target pos =>
    (SuccinctRankProposal.jacobsonRankData bits).rankCosted target pos
  selectCosted := fun _ target occurrence =>
    match target with
    | false =>
        (sparseExceptionSelectSource bits false).selectPositionCosted
          occurrence
    | true =>
        (sparseExceptionSelectSource bits true).selectPositionCosted
          occurrence
  aux_length_eq := by
    exact jacobsonClarkRankSelectPaddedAuxPayload_length bits
  rank_cost_le := by
    intro target pos
    exact Nat.le_trans
      ((SuccinctRankProposal.jacobsonRankData bits).rankCosted_cost_le
        target pos)
      (by
        unfold jacobsonClarkRankSelectQueryCost
        exact Nat.le_max_left 4 sparseDenseSelectQueryCost)
  select_cost_le := by
    intro target occurrence
    cases target
    · let source := sparseExceptionSelectSource bits false
      exact Nat.le_trans
        (source.selectPositionCosted_cost_le occurrence)
        (by
          unfold jacobsonClarkRankSelectQueryCost
          exact Nat.le_max_right 4 sparseDenseSelectQueryCost)
    · let source := sparseExceptionSelectSource bits true
      exact Nat.le_trans
        (source.selectPositionCosted_cost_le occurrence)
        (by
          unfold jacobsonClarkRankSelectQueryCost
          exact Nat.le_max_right 4 sparseDenseSelectQueryCost)
  rank_exact := by
    intro target pos
    exact (SuccinctRankProposal.jacobsonRankData bits).rankCosted_exact
      target pos
  select_exact := by
    intro target occurrence
    cases target
    · exact
        (sparseExceptionSelectSource bits false).selectPositionCosted_exact
          occurrence
    · exact
        (sparseExceptionSelectSource bits true).selectPositionCosted_exact
          occurrence

theorem jacobsonClarkRankSelectDirectory_profile
    (bits : List Bool) :
    let directory := jacobsonClarkRankSelectDirectory bits
    directory.auxPayload.length =
        jacobsonClarkRankSelectOverhead bits.length /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.rankQueryCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact
          ⟨(jacobsonClarkRankSelectDirectory bits).auxPayload_length,
      by
        intro target pos
        let directory := jacobsonClarkRankSelectDirectory bits
        exact
          ⟨directory.rankQueryCosted_cost_le target pos,
            directory.rankQueryCosted_erase target pos⟩,
      by
        intro target occurrence
        let directory := jacobsonClarkRankSelectDirectory bits
        exact
          ⟨directory.selectQueryCosted_cost_le target occurrence,
            directory.selectQueryCosted_erase target occurrence⟩⟩

/--
Full public bitvector rank/select/access directory: stored input bits provide
`access`, Jacobson provides `rank`, and the generic Clark sources provide
`select false` and `select true`.
-/
def jacobsonClarkBitVectorRankSelectDirectory (bits : List Bool) :
    RankSelectSpec.BitVectorRankSelectDirectory bits
      (jacobsonClarkRankSelectOverhead bits.length)
      jacobsonClarkRankSelectQueryCost :=
  RankSelectSpec.BitVectorRankSelectDirectory.ofRankSelectDirectoryWithStoredBits
    (jacobsonClarkRankSelectDirectory bits)
    (by
      unfold jacobsonClarkRankSelectQueryCost
      exact Nat.le_trans (by omega : 1 <= 4)
        (Nat.le_max_left 4 sparseDenseSelectQueryCost))

theorem jacobsonClarkBitVectorRankSelectDirectory_profile
    (bits : List Bool) :
    let directory := jacobsonClarkBitVectorRankSelectDirectory bits
    directory.payload.length =
        bits.length + jacobsonClarkRankSelectOverhead bits.length /\
      (forall i,
        (directory.accessQueryCosted i).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.rankQueryCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact (jacobsonClarkBitVectorRankSelectDirectory bits).profile

theorem sparseExceptionSelectSource_rankSelectSpec_adapter_profile
    (bits : List Bool) :
    let directory := jacobsonClarkBitVectorRankSelectDirectory bits
    directory.payload.length =
        bits.length + jacobsonClarkRankSelectOverhead bits.length /\
      (forall i,
        (directory.accessQueryCosted i).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.rankQueryCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            jacobsonClarkRankSelectQueryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact jacobsonClarkBitVectorRankSelectDirectory_profile bits

/-- Public plain-bitvector family: `n + o(n)` payload and constant-time queries. -/
def jacobsonClarkRankSelectFamily :
    RankSelectSpec.BitVectorRankSelectFamily
      jacobsonClarkRankSelectOverhead
      jacobsonClarkRankSelectQueryCost where
  directory := jacobsonClarkBitVectorRankSelectDirectory
  overhead_littleO := jacobsonClarkRankSelectOverhead_littleO

theorem jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile :
    SuccinctSpace.LittleOLinear jacobsonClarkRankSelectOverhead /\
      forall bits : List Bool,
        let directory := jacobsonClarkRankSelectFamily.directory bits
        (directory.payload.length =
          bits.length + jacobsonClarkRankSelectOverhead bits.length) /\
          (forall i,
            (directory.accessQueryCosted i).cost <=
                jacobsonClarkRankSelectQueryCost /\
              (directory.accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            (directory.rankQueryCosted target pos).cost <=
                jacobsonClarkRankSelectQueryCost /\
              (directory.rankQueryCosted target pos).erase =
                RMQ.Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectQueryCosted target occurrence).cost <=
                jacobsonClarkRankSelectQueryCost /\
              (directory.selectQueryCosted target occurrence).erase =
                RMQ.Succinct.select target bits occurrence) := by
  exact
    jacobsonClarkRankSelectFamily.n_plus_o_constant_query_profile

end RMQ.GenericSelect
