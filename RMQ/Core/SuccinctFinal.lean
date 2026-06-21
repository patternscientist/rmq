import RMQ.Core.SuccinctSelectProposal
import RMQ.Core.SuccinctCloseProposal

namespace RMQ
namespace SuccinctFinal

open SuccinctSpace

def concreteBPNativeSuccinctRMQOverhead
    (rankSelectOverhead : Nat -> Nat) (n : Nat) : Nat :=
  rankSelectOverhead (2 * n) +
    SuccinctCloseProposal.compactBPCloseOverhead n

def concreteBPNativeSuccinctRMQQueryCost
    (rankSelectCost : Nat) : Nat :=
  3 * rankSelectCost +
    SuccinctCloseProposal.concreteCompactBPCloseQueryCost

def concreteBPNativeRankSelectDirectory
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.RankSelectDirectory
      shape.bpCode (family.overhead shape.bpCode.length) rankSelectCost :=
  family.directory shape.bpCode

def concreteBPNativeCloseDirectory
    (shape : Cartesian.CartesianShape) :
    SuccinctCloseProposal.ConcreteCompactBPCloseLCADirectory shape :=
  SuccinctCloseProposal.concreteCompactBPCloseLCADirectory shape

def concreteBPNativeSuccinctRMQAuxPayload
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) :
    List Bool :=
  let rankSelectDirectory :=
    concreteBPNativeRankSelectDirectory family shape
  let closeDirectory := concreteBPNativeCloseDirectory shape
  rankSelectDirectory.auxPayload ++
    closeDirectory.payload ++
      List.replicate
        (SuccinctCloseProposal.compactBPCloseOverhead shape.size -
          closeDirectory.payload.length)
        false

def concreteBPNativeSuccinctRMQPayload
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) :
    List Bool :=
  shape.bpCode ++ concreteBPNativeSuccinctRMQAuxPayload family shape

def concreteBPNativeSelectCloseCosted
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : Costed (Option Nat) :=
  (concreteBPNativeRankSelectDirectory family shape).selectQueryCosted
    false idx

def concreteBPNativeRankCloseCosted
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : Costed Nat :=
  (concreteBPNativeRankSelectDirectory family shape).rankQueryCosted
    false pos

def concreteBPNativeLCACloseCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseCosted
    leftClose rightClose

def concreteBPNativeSuccinctRMQQueryCosted
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (concreteBPNativeSelectCloseCosted family shape left)
    fun leftClose? =>
      Costed.bind
        (concreteBPNativeSelectCloseCosted family shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (concreteBPNativeLCACloseCosted shape leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (concreteBPNativeRankCloseCosted
                          family shape (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none

theorem concreteBPNativeSuccinctRMQOverhead_littleO
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost) :
    SuccinctSpace.LittleOLinear
      (concreteBPNativeSuccinctRMQOverhead family.overhead) := by
  exact
    (family.overhead_littleO.comp_two_mul_arg).add
      SuccinctCloseProposal.compactBPCloseOverhead_littleO

theorem concreteBPNativeSelectCloseCosted_cost_le
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseCosted family shape idx).cost <=
      rankSelectCost := by
  exact
    (concreteBPNativeRankSelectDirectory family shape).selectQueryCosted_cost_le
      false idx

theorem concreteBPNativeRankCloseCosted_cost_le
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseCosted family shape pos).cost <=
      rankSelectCost := by
  exact
    (concreteBPNativeRankSelectDirectory family shape).rankQueryCosted_cost_le
      false pos

theorem concreteBPNativeLCACloseCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseCosted shape leftClose rightClose).cost <=
      SuccinctCloseProposal.concreteCompactBPCloseQueryCost := by
  have hprofile :=
    SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile shape
  simpa [concreteBPNativeLCACloseCosted, concreteBPNativeCloseDirectory]
    using hprofile.2.2.1 leftClose rightClose

theorem concreteBPNativeSelectCloseCosted_exact
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseCosted family shape idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  calc
    (concreteBPNativeSelectCloseCosted family shape idx).erase =
        Succinct.select false shape.bpCode idx := by
      exact
        SuccinctSpace.RankSelectDirectory.selectQueryCosted_erase
          (concreteBPNativeRankSelectDirectory family shape) false idx
    _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
      exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem concreteBPNativeRankCloseCosted_exact
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseCosted family shape pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact
    SuccinctSpace.RankSelectDirectory.rankQueryCosted_erase
      (concreteBPNativeRankSelectDirectory family shape) false pos

theorem concreteBPNativeLCACloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : SuccinctSpace.bpCloseOfInorder? shape left = some leftClose)
    (hright :
      SuccinctSpace.bpCloseOfInorder? shape (left + len - 1) =
        some rightClose)
    (hanswer :
      SuccinctSpace.bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (concreteBPNativeLCACloseCosted shape leftClose rightClose).erase =
      some answerClose := by
  have hprofile :=
    SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile shape
  simpa [concreteBPNativeLCACloseCosted, concreteBPNativeCloseDirectory]
    using hprofile.2.2.2.1 hlen hbound hleft hright hanswer

theorem concreteBPNativeSuccinctRMQAuxPayload_length
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost n : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (concreteBPNativeSuccinctRMQAuxPayload family shape).length =
      concreteBPNativeSuccinctRMQOverhead family.overhead n := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have hrank :
      ((concreteBPNativeRankSelectDirectory family shape).auxPayload).length =
        family.overhead (2 * n) := by
    simp [concreteBPNativeRankSelectDirectory, hbp]
  have hcloseLe :
      (concreteBPNativeCloseDirectory shape).payload.length <=
        SuccinctCloseProposal.compactBPCloseOverhead n := by
    have hprofile :=
      SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile shape
    simpa [concreteBPNativeCloseDirectory,
      Cartesian.ShapeOfSize.size_eq hshapeSize] using hprofile.1
  simp [concreteBPNativeSuccinctRMQAuxPayload,
    concreteBPNativeSuccinctRMQOverhead,
    Cartesian.ShapeOfSize.size_eq hshapeSize, hrank]
  omega

theorem concreteBPNativeSuccinctRMQPayload_length
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost n : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (concreteBPNativeSuccinctRMQPayload family shape).length =
      2 * n + concreteBPNativeSuccinctRMQOverhead family.overhead n := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have haux :=
    concreteBPNativeSuccinctRMQAuxPayload_length family hshape
  simp [concreteBPNativeSuccinctRMQPayload, hbp, haux]

theorem concreteBPNativeSuccinctRMQQueryCosted_cost_le
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryCosted family shape left right).cost <=
      concreteBPNativeSuccinctRMQQueryCost rankSelectCost := by
  unfold concreteBPNativeSuccinctRMQQueryCosted
  have hleft :=
    concreteBPNativeSelectCloseCosted_cost_le family shape left
  have hright :=
    concreteBPNativeSelectCloseCosted_cost_le
      family shape (right - 1)
  cases hleftValue :
      (concreteBPNativeSelectCloseCosted family shape left).value with
  | none =>
      simp [Costed.bind, concreteBPNativeSuccinctRMQQueryCost,
        hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          (concreteBPNativeSelectCloseCosted
            family shape (right - 1)).value with
      | none =>
          simp [Costed.bind, concreteBPNativeSuccinctRMQQueryCost,
            hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            concreteBPNativeLCACloseCosted_cost_le
              shape leftClose rightClose
          cases hlcaValue :
              (concreteBPNativeLCACloseCosted
                shape leftClose rightClose).value with
          | none =>
              simp [Costed.bind, concreteBPNativeSuccinctRMQQueryCost,
                hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                concreteBPNativeRankCloseCosted_cost_le
                  family shape (answerClose + 1)
              simp [Costed.bind, Costed.map,
                concreteBPNativeSuccinctRMQQueryCost, hleftValue,
                hrightValue, hlcaValue]
              omega

theorem concreteBPNativeSuccinctRMQQueryCosted_exact
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost n : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQQueryCosted
      family shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hboundShape : left + len <= shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hbound
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  have hscanLt :
      scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (concreteBPNativeSelectCloseCosted
          family shape left).value = some leftClose := by
    have h :=
      concreteBPNativeSelectCloseCosted_exact family shape left
    simpa [Costed.erase, hleftClose] using h
  have hselectRight :
      (concreteBPNativeSelectCloseCosted
          family shape (left + len - 1)).value =
        some rightClose := by
    have h :=
      concreteBPNativeSelectCloseCosted_exact
        family shape (left + len - 1)
    simpa [Costed.erase, hrightClose] using h
  have hlca :
      (concreteBPNativeLCACloseCosted
          shape leftClose rightClose).value =
        some answerClose := by
    have h :=
      concreteBPNativeLCACloseCosted_exact
        (shape := shape) hlen hboundShape hleftClose hrightClose
        hanswerClose
    simpa [Costed.erase] using h
  have hrank :
      (concreteBPNativeRankCloseCosted
          family shape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact :=
      concreteBPNativeRankCloseCosted_exact
        family shape (answerClose + 1)
    have hrankRecover :=
      SuccinctSpace.bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (concreteBPNativeRankCloseCosted
          family shape (answerClose + 1)).value =
          Succinct.rankPrefix false shape.bpCode
            (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact
      _ = scanWindow shape.representative left len + 1 :=
        hrankRecover
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold concreteBPNativeSuccinctRMQQueryCosted
  simp [Costed.erase, Costed.bind, Costed.map, Costed.pure,
    hselectLeft, hselectRight, hlca, hrank, hrankSub]

theorem concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost) :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead family.overhead) /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload family shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead family.overhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            family shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost rankSelectCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryCosted
                    family shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  constructor
  · exact concreteBPNativeSuccinctRMQOverhead_littleO family
  intro n
  constructor
  · have hbase :=
      EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
    omega
  constructor
  · intro shape hshape
    exact concreteBPNativeSuccinctRMQPayload_length family hshape
  constructor
  · intro shape left right
    exact concreteBPNativeSuccinctRMQQueryCosted_cost_le
      family shape left right
  · intro shape hshape left len hlen hbound
    exact concreteBPNativeSuccinctRMQQueryCosted_exact
      family hshape hlen hbound

end SuccinctFinal
end RMQ
