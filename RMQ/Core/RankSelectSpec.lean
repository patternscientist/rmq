import RMQ.Core.SuccinctSpace

/-!
# Standalone rank/select bitvector specification

This module extracts the public rank/select/access theorem shape from the
RMQ-shaped succinct layer.  It deliberately reuses the existing exact
`Succinct.rankPrefix`/`Succinct.select` semantics and
`SuccinctSpace.RankSelectDirectory` costed query interface, while accounting for
the stored bitvector bits separately from auxiliary directory bits.
-/

namespace RMQ

namespace RankSelectSpec

open SuccinctSpace

/--
Payload-accounted bitvector rank/select directory.

The stored bitvector contributes `bits.length` payload bits.  The wrapped
`SuccinctSpace.RankSelectDirectory` contributes the auxiliary payload and the
rank/select query path.  The additional access query is modeled explicitly so
the public surface covers the usual bitvector operations: access, rank, and
select.
-/
structure BitVectorRankSelectDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  rankSelect : SuccinctSpace.RankSelectDirectory bits overhead queryCost
  accessCosted : Nat -> Costed (Option Bool)
  access_cost_le : forall i, (accessCosted i).cost <= queryCost
  access_exact : forall i, (accessCosted i).erase = bits[i]?

namespace BitVectorRankSelectDirectory

/-- Counted payload: the stored bits followed by the rank/select auxiliary bits. -/
def payload
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost) :
    List Bool :=
  bits ++ directory.rankSelect.auxPayload

@[simp] theorem payload_length
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost) :
    directory.payload.length = bits.length + overhead := by
  simp [payload]

/-- Exact access query through the modeled directory. -/
def accessQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (i : Nat) : Costed (Option Bool) :=
  directory.accessCosted i

theorem accessQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (i : Nat) :
    (directory.accessQueryCosted i).cost <= queryCost :=
  directory.access_cost_le i

theorem accessQueryCosted_erase
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (i : Nat) :
    (directory.accessQueryCosted i).erase = bits[i]? :=
  directory.access_exact i

/-- Exact rank query through the modeled directory. -/
def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankSelect.rankQueryCosted target pos

theorem rankQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).cost <= queryCost :=
  directory.rankSelect.rankQueryCosted_cost_le target pos

theorem rankQueryCosted_erase
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).erase =
      Succinct.rankPrefix target bits pos :=
  directory.rankSelect.rankQueryCosted_erase target pos

/-- Exact select query through the modeled directory. -/
def selectQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  directory.rankSelect.selectQueryCosted target occurrence

theorem selectQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (directory.selectQueryCosted target occurrence).cost <= queryCost :=
  directory.rankSelect.selectQueryCosted_cost_le target occurrence

theorem selectQueryCosted_erase
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (directory.selectQueryCosted target occurrence).erase =
      Succinct.select target bits occurrence :=
  directory.rankSelect.selectQueryCosted_erase target occurrence

theorem profile
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : BitVectorRankSelectDirectory bits overhead queryCost) :
    directory.payload.length = bits.length + overhead /\
      (forall i,
        (directory.accessQueryCosted i).cost <= queryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= queryCost /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <= queryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact directory.payload_length
  · constructor
    · intro i
      exact ⟨directory.accessQueryCosted_cost_le i,
        directory.accessQueryCosted_erase i⟩
    · constructor
      · intro target pos
        exact ⟨directory.rankQueryCosted_cost_le target pos,
          directory.rankQueryCosted_erase target pos⟩
      · intro target occurrence
        exact ⟨directory.selectQueryCosted_cost_le target occurrence,
          directory.selectQueryCosted_erase target occurrence⟩

/--
Add the standard stored-bit access query to an existing rank/select directory.
The premise records that one modeled indexed bit access fits in the shared
query-cost budget.
-/
def ofRankSelectDirectoryWithStoredBits
    {bits : List Bool} {overhead queryCost : Nat}
    (rankSelect : SuccinctSpace.RankSelectDirectory bits overhead queryCost)
    (haccess : 1 <= queryCost) :
    BitVectorRankSelectDirectory bits overhead queryCost where
  rankSelect := rankSelect
  accessCosted := fun i => Costed.tickValue 1 bits[i]?
  access_cost_le := by
    intro i
    simpa using haccess
  access_exact := by
    intro i
    rfl

theorem ofRankSelectDirectoryWithStoredBits_profile
    {bits : List Bool} {overhead queryCost : Nat}
    (rankSelect : SuccinctSpace.RankSelectDirectory bits overhead queryCost)
    (haccess : 1 <= queryCost) :
    let directory := ofRankSelectDirectoryWithStoredBits rankSelect haccess
    directory.payload.length = bits.length + overhead /\
      (forall i,
        (directory.accessQueryCosted i).cost <= queryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= queryCost /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <= queryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  exact (ofRankSelectDirectoryWithStoredBits rankSelect haccess).profile

/-- Payload-live stored-word rank/select data, exposed as a full bitvector API. -/
def ofPayloadLiveRankSelectData
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : SuccinctSpace.PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData :
      SuccinctSpace.PayloadLiveStoredWordSelectData bits selectOverhead) :
    BitVectorRankSelectDirectory bits (rankOverhead + selectOverhead) 3 :=
  ofRankSelectDirectoryWithStoredBits
    (SuccinctSpace.RankSelectDirectory.ofPayloadLiveRankSelectData
      rankData selectData)
    (by omega)

theorem ofPayloadLiveRankSelectData_profile
    {bits : List Bool} {rankOverhead selectOverhead : Nat}
    (rankData : SuccinctSpace.PayloadLiveStoredWordRankData bits rankOverhead)
    (selectData :
      SuccinctSpace.PayloadLiveStoredWordSelectData bits selectOverhead) :
    let directory := ofPayloadLiveRankSelectData rankData selectData
    directory.payload.length = bits.length + (rankOverhead + selectOverhead) /\
      (forall i,
        (directory.accessQueryCosted i).cost <= 3 /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= 3 /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <= 3 /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  exact (ofPayloadLiveRankSelectData rankData selectData).profile

end BitVectorRankSelectDirectory

/--
Family-level plain-bitvector theorem surface.

For every bitvector, the family stores the bits plus `overhead bits.length`
auxiliary bits and answers access/rank/select in at most `queryCost` modeled
steps.  The headline plain rank/select goal is an instance with
`LittleOLinear overhead`.
-/
structure BitVectorRankSelectFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall bits : List Bool,
      BitVectorRankSelectDirectory bits (overhead bits.length) queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace BitVectorRankSelectFamily

theorem n_plus_o_constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : BitVectorRankSelectFamily overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).payload.length =
          bits.length + overhead bits.length) /\
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
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact (family.directory bits).profile

end BitVectorRankSelectFamily

end RankSelectSpec

end RMQ
