import RMQ.Core.RankSelectPublic.Profiles

namespace RMQ.RankSelect

/-- Decoded fixed-weight entries have the requested length and true-count. -/
abbrev fixedWeightDecodeMemLengthTrueCount
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :=
  RMQ.RankSelectSpec.fixedWeightDecode?_mem_length_trueCount hdec

/-- Public compressed/FID family theorem shape. -/
theorem compressedFixedWeightConstantQueryProfile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family :
      CompressedFamily overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            ((family.directory bits).accessQueryCosted i).cost <=
                queryCost /\
              ((family.directory bits).accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              ((family.directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((family.directory bits).selectQueryCosted
                target occurrence).cost <= queryCost /\
              ((family.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily.fixed_weight_constant_query_profile
    family

/--
Public adapter theorem: a fixed-weight auxiliary family converted to the
generic compressed/FID family satisfies the generic fixed-weight
constant-query profile.
-/
theorem fixedWeightCompressedAuxiliaryToCompressedFamilyProfile
    {overhead : Nat -> Nat} {wordSize queryCost : Nat}
    (family :
      FixedWeightCompressedAuxiliaryFamily overhead wordSize queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).accessQueryCosted i).cost <=
                queryCost /\
              (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).selectQueryCosted
                target occurrence).cost <=
                queryCost /\
              (((fixedWeightCompressedAuxiliaryToCompressedFamily family).directory bits).selectQueryCosted
                  target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.FixedWeightCompressedAuxiliaryFamily.toCompressedFamily_fixed_weight_constant_query_profile
      family

/-! ### Concrete fixed-weight compressed/FID capstone -/

/-- Public alias for the concrete compressed/FID auxiliary overhead. -/
abbrev compressedFIDFixedWeightOverhead :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcretePackedClarkOverhead

/-- Public alias for the concrete compressed/FID modeled query cost. -/
abbrev compressedFIDFixedWeightQueryCost :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcretePackedClarkQueryCost

/-- Public alias for the concrete compressed/FID payload. -/
abbrev compressedFIDFixedWeightPayload :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcretePackedClarkPayload

theorem compressedFIDFixedWeightOverheadLittleO :
    SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcretePackedClarkOverhead_littleO

/--
Concrete fixed-weight compressed/FID profile.

For each bitvector `bits`, this profile stores the fixed-weight primary payload
plus `o(n)` auxiliary bits and supports exact access, rank, and select with one
uniform modeled constant query bound.  The cost model is the repository's
payload-backed word-RAM/indexed-read model, not Lean list runtime.
-/
theorem compressedFIDFixedWeightConstantQueryProfile
    (bits : List Bool) :
    (compressedFIDFixedWeightPayload bits).length <=
        fixedWeightPayloadBudget bits +
          compressedFIDFixedWeightOverhead bits.length /\
      SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
      (forall i,
        (RMQ.RankSelectSpec.subLogAccessCosted bits i).cost <=
            compressedFIDFixedWeightQueryCost /\
          (RMQ.RankSelectSpec.subLogAccessCosted bits i).erase = bits[i]?) /\
      (forall target pos,
        (RMQ.RankSelectSpec.subLogRankCosted bits target pos).cost <=
            compressedFIDFixedWeightQueryCost /\
          (RMQ.RankSelectSpec.subLogRankCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      forall target occurrence,
        (RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
          bits target occurrence).cost <=
            compressedFIDFixedWeightQueryCost /\
          (RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
            bits target occurrence).erase =
            Succinct.select target bits occurrence := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcretePackedClarkProfile bits

/--
Concrete compressed/FID directory for one fixed-weight bitvector instance.

The payload is the sub-log packed-Clark construction.  The fields expose the
actual charged access/rank/select queries; proofs and modeled cost bounds stay
in the theorem fields and are not counted as payload bits.
-/
def compressedFIDFixedWeightDirectory
    (bits : List Bool) :
    CompressedDirectory bits
      (compressedFIDFixedWeightOverhead bits.length)
      compressedFIDFixedWeightQueryCost where
  payload := compressedFIDFixedWeightPayload bits
  payload_length_le :=
    (compressedFIDFixedWeightConstantQueryProfile bits).1
  accessCosted := RMQ.RankSelectSpec.subLogAccessCosted bits
  rankCosted := RMQ.RankSelectSpec.subLogRankCosted bits
  selectCosted :=
    RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted bits
  access_cost_le := by
    intro i
    exact
      ((compressedFIDFixedWeightConstantQueryProfile bits).2.2.1 i).1
  rank_cost_le := by
    intro target pos
    exact
      ((compressedFIDFixedWeightConstantQueryProfile bits).2.2.2.1
        target pos).1
  select_cost_le := by
    intro target occurrence
    exact
      ((compressedFIDFixedWeightConstantQueryProfile bits).2.2.2.2
        target occurrence).1
  access_exact := by
    intro i
    exact
      ((compressedFIDFixedWeightConstantQueryProfile bits).2.2.1 i).2
  rank_exact := by
    intro target pos
    exact
      ((compressedFIDFixedWeightConstantQueryProfile bits).2.2.2.1
        target pos).2
  select_exact := by
    intro target occurrence
    exact
      ((compressedFIDFixedWeightConstantQueryProfile bits).2.2.2.2
        target occurrence).2

/--
Concrete fixed-weight compressed/FID family.

This is the reusable family object behind the pointwise packed-Clark theorem:
for every stored bitvector it supplies the same construction, the same
modeled query-cost bound, and an `o(n)` auxiliary-overhead function.
-/
def compressedFIDFixedWeightFamily :
    CompressedFamily
      compressedFIDFixedWeightOverhead
      compressedFIDFixedWeightQueryCost where
  directory := compressedFIDFixedWeightDirectory
  overhead_littleO := compressedFIDFixedWeightOverheadLittleO

/--
Reusable compressed/FID family theorem for the concrete fixed-weight
packed-Clark construction.

The statement is the public family shape: a `LittleOLinear` overhead function
and, for every bitvector, a payload bounded by
`fixedWeightPayloadBudget bits + o(n)` with exact constant-modeled access,
rank, and select.  It is still a payload-backed word-RAM/indexed-read model
statement, not a Lean-runtime claim.
-/
theorem compressedFIDFixedWeightFamilyProfile :
    SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
      forall bits : List Bool,
        ((compressedFIDFixedWeightFamily.directory bits).payload.length <=
          fixedWeightPayloadBudget bits +
            compressedFIDFixedWeightOverhead bits.length) /\
          (forall i,
            ((compressedFIDFixedWeightFamily.directory bits).accessQueryCosted
                i).cost <= compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightFamily.directory bits).accessQueryCosted
                i).erase = bits[i]?) /\
          (forall target pos,
            ((compressedFIDFixedWeightFamily.directory bits).rankQueryCosted
                target pos).cost <= compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightFamily.directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((compressedFIDFixedWeightFamily.directory bits).selectQueryCosted
                target occurrence).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightFamily.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact compressedFixedWeightConstantQueryProfile compressedFIDFixedWeightFamily

/-- Auxiliary-overhead budget for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkOverhead :=
  RMQ.GenericSelect.jacobsonClarkRankSelectOverhead

/-- Uniform modeled query cost for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkQueryCost :=
  RMQ.GenericSelect.jacobsonClarkRankSelectQueryCost

/-- Concrete Jacobson/Clark directory for one stored bitvector. -/
abbrev jacobsonClarkDirectory :=
  RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory

/-- Concrete Jacobson/Clark rank/select family. -/
abbrev jacobsonClarkFamily :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily

/--
Public `n + o(n)`, constant-query theorem for the concrete Jacobson/Clark
rank/select family.
-/
abbrev jacobsonClarkNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile

/--
Public word-bounded profile for the concrete Jacobson/Clark rank/select
family, exposing the machine-word read bounds carried by the concrete
components.
-/
abbrev jacobsonClarkWordBoundedNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_word_bounded_n_plus_o_constant_query_profile

end RMQ.RankSelect
