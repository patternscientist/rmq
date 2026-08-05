import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerLogicalProtocol

/-!
# First-order close-select protocol

The accepted close-select leaf is defunctionalized here into request/reply
states.  All branch decisions are made from `n`, the public select index, and
logical words returned by preceding requests.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

/-- Request/reply state for one invocation of `packedSelectCloseLeaf`. -/
inductive PackedReviewerSelectState where
  | superEntry
      (invocation : PackedReviewerInvocation) (n index : Nat)
      (entry : PackedReviewerEntryState)
  | localEntry
      (invocation : PackedReviewerInvocation) (n index localSlot : Nat)
      (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
      (entry : PackedReviewerEntryState)
  | longRank
      (invocation : PackedReviewerInvocation) (n index : Nat)
      (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
      (rank : PackedReviewerRankState)
  | longRelative
      (invocation : PackedReviewerInvocation) (base slot : Nat)
  | sparseRank
      (invocation : PackedReviewerInvocation) (n index localSlot : Nat)
      (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
      (rank : PackedReviewerRankState)
  | sparseRelative
      (invocation : PackedReviewerInvocation) (base slot : Nat)
  | denseFirstWord
      (invocation : PackedReviewerInvocation) (n index : Nat)
      (basePosition baseOccurrence : Nat)
  | denseBeforeRank
      (invocation : PackedReviewerInvocation) (n index : Nat)
      (basePosition baseOccurrence : Nat) (word : List Bool)
      (rank : PackedReviewerRankState)
  | denseUptoRank
      (invocation : PackedReviewerInvocation) (n index : Nat)
      (basePosition baseOccurrence beforeFirst : Nat) (word : List Bool)
      (rank : PackedReviewerRankState)
  | denseFirstSelect
      (invocation : PackedReviewerInvocation) (n baseWord : Nat)
      (select : PackedReviewerWordSelectState)
  | denseSecondWord
      (invocation : PackedReviewerInvocation) (n index : Nat)
      (basePosition baseOccurrence beforeFirst uptoFirst : Nat)
  | denseSecondSelect
      (invocation : PackedReviewerInvocation) (n baseWord : Nat)
      (select : PackedReviewerWordSelectState)
  | done (value : Option Nat)

def packedReviewerSelectStart
    (invocation : PackedReviewerInvocation) (n index : Nat) :
    PackedReviewerSelectState :=
  if index < n then
    let slot := GenericSelect.selectSuperSlot index (packedSelectSuperStride n)
    .superEntry invocation n index
      (.baseOccurrence invocation .super slot)
  else
    .done none

def packedReviewerSelectNextRequest :
    PackedReviewerSelectState -> Option PackedReviewerLogicalRequest
  | .superEntry _ _ _ entry => packedReviewerEntryNextRequest entry
  | .localEntry _ _ _ _ _ entry => packedReviewerEntryNextRequest entry
  | .longRank _ _ _ _ rank => packedReviewerRankNextRequest rank
  | .longRelative invocation _ slot =>
      some
        { invocation := invocation
          site := .relativeOffset
          segment := 12
          index := slot }
  | .sparseRank _ _ _ _ _ _ rank => packedReviewerRankNextRequest rank
  | .sparseRelative invocation _ slot =>
      some
        { invocation := invocation
          site := .relativeOffset
          segment := 16
          index := slot }
  | .denseFirstWord invocation n _ basePosition _ =>
      let slot := basePosition / packedSelectWordSize n
      some
        { invocation := invocation
          site := .denseBPWord slot
          segment := 0
          index := slot }
  | .denseBeforeRank _ _ _ _ _ _ rank =>
      packedReviewerRankNextRequest rank
  | .denseUptoRank _ _ _ _ _ _ _ rank =>
      packedReviewerRankNextRequest rank
  | .denseFirstSelect _ _ _ select =>
      packedReviewerWordSelectNextRequest select
  | .denseSecondWord invocation n _ basePosition _ _ _ =>
      let slot := basePosition / packedSelectWordSize n + 1
      some
        { invocation := invocation
          site := .denseBPWord slot
          segment := 0
          index := slot }
  | .denseSecondSelect _ _ _ select =>
      packedReviewerWordSelectNextRequest select
  | .done _ => none

def packedReviewerSelectAfterSuper
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (super? : Option GenericSelect.SparseDenseSelectDenseLocalEntry) :
    PackedReviewerSelectState :=
  match super? with
  | none => .done none
  | some super =>
      if GenericSelect.relativeSplitSelectEntryIsMarked super then
        let pos := GenericSelect.selectSuperSlot index (packedSelectSuperStride n)
        .longRank invocation n index super
          (.superSample invocation .selectLong n pos)
      else
        let localSlot :=
          GenericSelect.relativeSplitSelectLocalSlot index
            (packedSelectSuperStride n) (packedSelectLocalSlotsPerSuper n)
            (packedSelectLocalStride n) super
        .localEntry invocation n index localSlot super
          (.baseOccurrence invocation .local localSlot)

def packedReviewerSelectAfterLocal
    (invocation : PackedReviewerInvocation) (n index localSlot : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (loc? : Option GenericSelect.SparseDenseSelectDenseLocalEntry) :
    PackedReviewerSelectState :=
  match loc? with
  | none => .done none
  | some loc =>
      if GenericSelect.relativeSplitSelectEntryIsMarked loc then
        .sparseRank invocation n index localSlot super loc
          (.superSample invocation .selectSparse n localSlot)
      else
        let basePosition :=
          GenericSelect.relativeSplitSelectLocalBasePosition
            (packedSelectWordSize n) super loc
        let baseOccurrence :=
          GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc
        .denseFirstWord invocation n index basePosition baseOccurrence

def packedReviewerSelectAfterLongRank
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (super : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (exceptionRank : Nat) : PackedReviewerSelectState :=
  let base :=
    GenericSelect.relativeSplitSelectEntryBasePosition
      (packedSelectWordSize n) super
  let slot :=
    GenericSelect.relativeSplitSelectLongCompactSlot exceptionRank
      (index - super.baseOccurrence) (packedSelectSuperStride n)
  .longRelative invocation base slot

def packedReviewerSelectAfterSparseRank
    (invocation : PackedReviewerInvocation) (n index localSlot : Nat)
    (super loc : GenericSelect.SparseDenseSelectDenseLocalEntry)
    (exceptionRank : Nat) : PackedReviewerSelectState :=
  let base :=
    GenericSelect.relativeSplitSelectLocalBasePosition
      (packedSelectWordSize n) super loc
  let slot :=
    GenericSelect.relativeSplitSelectSparseCompactSlot exceptionRank
      (index - GenericSelect.relativeSplitSelectLocalBaseOccurrence super loc)
      (packedSelectLocalStride n)
  .sparseRelative invocation base slot

def packedReviewerSelectAfterDenseUptoRank
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence beforeFirst : Nat) (word : List Bool)
    (uptoFirst : Nat) : PackedReviewerSelectState :=
  let localOccurrence := index - baseOccurrence
  let baseWord := basePosition / packedSelectWordSize n
  if localOccurrence < uptoFirst - beforeFirst then
    let select :=
      packedReviewerWordSelectStart invocation n false word
        (beforeFirst + localOccurrence)
    match packedReviewerWordSelectResult select with
    | some local? =>
        .done
          (local?.map
            (fun offset => baseWord * packedSelectWordSize n + offset))
    | none => .denseFirstSelect invocation n baseWord select
  else
    .denseSecondWord invocation n index basePosition baseOccurrence
      beforeFirst uptoFirst

def packedReviewerSelectAfterDenseBeforeRank
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence : Nat) (word : List Bool)
    (beforeFirst : Nat) : PackedReviewerSelectState :=
  let rank :=
    packedReviewerRankStartFold invocation .close n word word.length 0
  match packedReviewerRankResult rank with
  | some uptoFirst =>
      packedReviewerSelectAfterDenseUptoRank invocation n index basePosition
        baseOccurrence beforeFirst word uptoFirst
  | none =>
      .denseUptoRank invocation n index basePosition baseOccurrence
        beforeFirst word rank

def packedReviewerSelectAfterDenseFirstWord
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence : Nat) (word? : Option (List Bool)) :
    PackedReviewerSelectState :=
  match word? with
  | none => .done none
  | some word =>
      let wordSize := packedSelectWordSize n
      let beforeLimit := basePosition - basePosition / wordSize * wordSize
      let rank :=
        packedReviewerRankStartFold invocation .close n word beforeLimit 0
      match packedReviewerRankResult rank with
      | some beforeFirst =>
          packedReviewerSelectAfterDenseBeforeRank invocation n index
            basePosition baseOccurrence word beforeFirst
      | none =>
          .denseBeforeRank invocation n index basePosition baseOccurrence word
            rank

def packedReviewerSelectAfterDenseSecondWord
    (invocation : PackedReviewerInvocation) (n index : Nat)
    (basePosition baseOccurrence beforeFirst uptoFirst : Nat)
    (word? : Option (List Bool)) : PackedReviewerSelectState :=
  match word? with
  | none => .done none
  | some word =>
      let baseWord := basePosition / packedSelectWordSize n + 1
      let select :=
        packedReviewerWordSelectStart invocation n false word
          (index - baseOccurrence - (uptoFirst - beforeFirst))
      match packedReviewerWordSelectResult select with
      | some local? =>
          .done
            (local?.map
              (fun offset => baseWord * packedSelectWordSize n + offset))
      | none => .denseSecondSelect invocation n baseWord select

def packedReviewerSelectConsumeReply
    (state : PackedReviewerSelectState) (reply : Option (List Bool)) :
    PackedReviewerSelectState :=
  match state with
  | .superEntry invocation n index entry =>
      let entry' := packedReviewerEntryConsumeReply entry reply
      match packedReviewerEntryResult entry' with
      | some super? => packedReviewerSelectAfterSuper invocation n index super?
      | none => .superEntry invocation n index entry'
  | .localEntry invocation n index localSlot super entry =>
      let entry' := packedReviewerEntryConsumeReply entry reply
      match packedReviewerEntryResult entry' with
      | some loc? =>
          packedReviewerSelectAfterLocal invocation n index localSlot super loc?
      | none => .localEntry invocation n index localSlot super entry'
  | .longRank invocation n index super rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some exceptionRank =>
          packedReviewerSelectAfterLongRank invocation n index super
            exceptionRank
      | none => .longRank invocation n index super rank'
  | .longRelative _ base _ =>
      .done ((packedReviewerDecodeNat reply).map (fun offset => base + offset))
  | .sparseRank invocation n index localSlot super loc rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some exceptionRank =>
          packedReviewerSelectAfterSparseRank invocation n index localSlot
            super loc exceptionRank
      | none =>
          .sparseRank invocation n index localSlot super loc rank'
  | .sparseRelative _ base _ =>
      .done ((packedReviewerDecodeNat reply).map (fun offset => base + offset))
  | .denseFirstWord invocation n index basePosition baseOccurrence =>
      packedReviewerSelectAfterDenseFirstWord invocation n index basePosition
        baseOccurrence reply
  | .denseBeforeRank invocation n index basePosition baseOccurrence word rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some beforeFirst =>
          packedReviewerSelectAfterDenseBeforeRank invocation n index
            basePosition baseOccurrence word beforeFirst
      | none =>
          .denseBeforeRank invocation n index basePosition baseOccurrence word
            rank'
  | .denseUptoRank invocation n index basePosition baseOccurrence beforeFirst
        word rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some uptoFirst =>
          packedReviewerSelectAfterDenseUptoRank invocation n index
            basePosition baseOccurrence beforeFirst word uptoFirst
      | none =>
          .denseUptoRank invocation n index basePosition baseOccurrence
            beforeFirst word rank'
  | .denseFirstSelect invocation n baseWord select =>
      let select' := packedReviewerWordSelectConsumeReply select reply
      match packedReviewerWordSelectResult select' with
      | some local? =>
          .done (local?.map (fun offset => baseWord * packedSelectWordSize n + offset))
      | none => .denseFirstSelect invocation n baseWord select'
  | .denseSecondWord invocation n index basePosition baseOccurrence beforeFirst
        uptoFirst =>
      packedReviewerSelectAfterDenseSecondWord invocation n index basePosition
        baseOccurrence beforeFirst uptoFirst reply
  | .denseSecondSelect invocation n baseWord select =>
      let select' := packedReviewerWordSelectConsumeReply select reply
      match packedReviewerWordSelectResult select' with
      | some local? =>
          .done (local?.map (fun offset => baseWord * packedSelectWordSize n + offset))
      | none => .denseSecondSelect invocation n baseWord select'
  | .done value => .done value

def packedReviewerSelectResult : PackedReviewerSelectState -> Option (Option Nat)
  | .done value => some value
  | _ => none

/--
Exact structural worst-case budget for the remaining logical reads of one
select invocation.  The initial state is bounded by `35`.
-/
def packedReviewerSelectRemaining : PackedReviewerSelectState -> Nat
  | .superEntry _ _ _ entry => packedReviewerEntryRemaining entry + 31
  | .localEntry _ _ _ _ _ entry => packedReviewerEntryRemaining entry + 27
  | .longRank _ _ _ _ rank => packedReviewerRankRemaining rank + 1
  | .longRelative _ _ _ => 1
  | .sparseRank _ _ _ _ _ _ rank => packedReviewerRankRemaining rank + 1
  | .sparseRelative _ _ _ => 1
  | .denseFirstWord _ _ _ _ _ => 27
  | .denseBeforeRank _ _ _ _ _ _ rank =>
      packedReviewerRankRemaining rank + 18
  | .denseUptoRank _ _ _ _ _ _ _ rank =>
      packedReviewerRankRemaining rank + 10
  | .denseFirstSelect _ _ _ select =>
      packedReviewerWordSelectRemaining select
  | .denseSecondWord _ _ _ _ _ _ _ => 10
  | .denseSecondSelect _ _ _ select =>
      packedReviewerWordSelectRemaining select
  | .done _ => 0

end PackedCellProbe
end SuccinctFinal
end RMQ
