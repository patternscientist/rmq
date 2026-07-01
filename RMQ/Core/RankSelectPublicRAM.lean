import RMQ.Core.RankSelectPublic
import RMQ.Core.RankSelectCompressedSubLogRAM

/-!
# Public Word-RAM replay surface for compressed/FID rank/select

This module is the public facade corresponding to
`RankSelectCompressedSubLogRAM`: it packages the interpreted access, rank, and
select queries into the same compressed/FID family theorem shape as
`RankSelectPublic`.
-/

namespace RMQ

namespace RankSelect

/-- Interpreted access query for the concrete fixed-weight compressed/FID family. -/
abbrev compressedFIDFixedWeightAccessInterpretedCosted
    (bits : List Bool) (i : Nat) : Costed (Option Bool) :=
  RMQ.RankSelectSpec.subLogAccessInterpretedCosted bits i

/-- Interpreted rank query for the concrete fixed-weight compressed/FID family. -/
abbrev compressedFIDFixedWeightRankInterpretedCosted
    (bits : List Bool) (target : Bool) (pos : Nat) : Costed Nat :=
  RMQ.RankSelectSpec.subLogRankInterpretedCosted bits target pos

/-- Interpreted select query for the concrete fixed-weight compressed/FID family. -/
abbrev compressedFIDFixedWeightSelectInterpretedCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    Costed (Option Nat) :=
  RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteInterpretedCosted
    bits target occurrence

theorem compressedFIDFixedWeightAccessInterpretedCosted_refines_accessCosted
    (bits : List Bool) (i : Nat) :
    compressedFIDFixedWeightAccessInterpretedCosted bits i =
      RMQ.RankSelectSpec.subLogAccessCosted bits i := by
  exact
    RMQ.RankSelectSpec.subLogAccessInterpretedCosted_refines_subLogAccessCosted
      bits i

theorem compressedFIDFixedWeightRankInterpretedCosted_refines_rankCosted
    (bits : List Bool) (target : Bool) (pos : Nat) :
    compressedFIDFixedWeightRankInterpretedCosted bits target pos =
      RMQ.RankSelectSpec.subLogRankCosted bits target pos := by
  exact
    RMQ.RankSelectSpec.subLogRankInterpretedCosted_refines_subLogRankCosted
      bits target pos

theorem compressedFIDFixedWeightSelectInterpretedCosted_refines_selectCosted
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    compressedFIDFixedWeightSelectInterpretedCosted bits target occurrence =
      RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteCosted
        bits target occurrence := by
  exact
    RMQ.RankSelectSpec.subLogSelectFromPackedClarkRouteInterpretedCosted_refines
      bits target occurrence

/--
Pointwise interpreted compressed/FID profile.

The payload bound and asymptotic overhead are identical to the existing
compressed/FID profile; the query clauses use the interpreted replay functions.
-/
theorem compressedFIDFixedWeightInterpretedConstantQueryProfile
    (bits : List Bool) :
    (compressedFIDFixedWeightPayload bits).length <=
        fixedWeightPayloadBudget bits +
          compressedFIDFixedWeightOverhead bits.length /\
      SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
      (forall i,
        (compressedFIDFixedWeightAccessInterpretedCosted bits i).cost <=
            compressedFIDFixedWeightQueryCost /\
          (compressedFIDFixedWeightAccessInterpretedCosted bits i).erase =
            bits[i]?) /\
      (forall target pos,
        (compressedFIDFixedWeightRankInterpretedCosted
          bits target pos).cost <= compressedFIDFixedWeightQueryCost /\
          (compressedFIDFixedWeightRankInterpretedCosted
            bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      forall target occurrence,
        (compressedFIDFixedWeightSelectInterpretedCosted
          bits target occurrence).cost <=
            compressedFIDFixedWeightQueryCost /\
          (compressedFIDFixedWeightSelectInterpretedCosted
            bits target occurrence).erase =
            Succinct.select target bits occurrence := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcretePackedClarkInterpretedProfile
      bits

/-- Concrete compressed/FID directory whose access/rank/select queries are interpreted replays. -/
def compressedFIDFixedWeightInterpretedDirectory
    (bits : List Bool) :
    CompressedDirectory bits
      (compressedFIDFixedWeightOverhead bits.length)
      compressedFIDFixedWeightQueryCost where
  payload := compressedFIDFixedWeightPayload bits
  payload_length_le :=
    (compressedFIDFixedWeightInterpretedConstantQueryProfile bits).1
  accessCosted := compressedFIDFixedWeightAccessInterpretedCosted bits
  rankCosted := compressedFIDFixedWeightRankInterpretedCosted bits
  selectCosted := compressedFIDFixedWeightSelectInterpretedCosted bits
  access_cost_le := by
    intro i
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.1 i).1
  rank_cost_le := by
    intro target pos
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.1 target pos).1
  select_cost_le := by
    intro target occurrence
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.2 target occurrence).1
  access_exact := by
    intro i
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.1 i).2
  rank_exact := by
    intro target pos
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.1 target pos).2
  select_exact := by
    intro target occurrence
    exact
      ((compressedFIDFixedWeightInterpretedConstantQueryProfile
        bits).2.2.2.2 target occurrence).2

/-- Concrete fixed-weight compressed/FID family with interpreted query replays. -/
def compressedFIDFixedWeightInterpretedFamily :
    CompressedFamily
      compressedFIDFixedWeightOverhead
      compressedFIDFixedWeightQueryCost where
  directory := compressedFIDFixedWeightInterpretedDirectory
  overhead_littleO := compressedFIDFixedWeightOverheadLittleO

/-- Family theorem for the interpreted compressed/FID rank/select replay. -/
theorem compressedFIDFixedWeightInterpretedFamilyProfile :
    SuccinctSpace.LittleOLinear compressedFIDFixedWeightOverhead /\
      forall bits : List Bool,
        ((compressedFIDFixedWeightInterpretedFamily.directory bits).payload.length <=
          fixedWeightPayloadBudget bits +
            compressedFIDFixedWeightOverhead bits.length) /\
          (forall i,
            ((compressedFIDFixedWeightInterpretedFamily.directory bits).accessQueryCosted
                i).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).accessQueryCosted
                i).erase = bits[i]?) /\
          (forall target pos,
            ((compressedFIDFixedWeightInterpretedFamily.directory bits).rankQueryCosted
                target pos).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((compressedFIDFixedWeightInterpretedFamily.directory bits).selectQueryCosted
                target occurrence).cost <=
                compressedFIDFixedWeightQueryCost /\
              ((compressedFIDFixedWeightInterpretedFamily.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily.fixed_weight_constant_query_profile
      compressedFIDFixedWeightInterpretedFamily

end RankSelect

end RMQ
