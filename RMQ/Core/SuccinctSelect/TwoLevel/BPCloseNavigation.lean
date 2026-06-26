import RMQ.Core.SuccinctSelect.TwoLevel.RankSelectAdapters

/-!
# Two-level BP close-navigation wrappers

Split implementation layer for two-level select and rank/select helpers.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal
open SuccinctSpace

/-!
## Two-level BP close-navigation target

This is the stateful BP/RMQ composition using the two-level rank/select
components above plus the existing payload-live BP LCA-close table.
-/

def twoLevelBPCloseNavigationOverhead
    (rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat)
    (n : Nat) : Nat :=
  twoLevelRankSelectOverhead
      rankSuper rankBlock selectSuper selectBlock n +
    lca n

theorem twoLevelBPCloseNavigationOverhead_littleO
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    (hrankSuper : SuccinctSpace.LittleOLinear rankSuper)
    (hrankBlock : SuccinctSpace.LittleOLinear rankBlock)
    (hselectSuper : SuccinctSpace.LittleOLinear selectSuper)
    (hselectBlock : SuccinctSpace.LittleOLinear selectBlock)
    (hlca : SuccinctSpace.LittleOLinear lca) :
    SuccinctSpace.LittleOLinear
      (twoLevelBPCloseNavigationOverhead
        rankSuper rankBlock selectSuper selectBlock lca) := by
  unfold twoLevelBPCloseNavigationOverhead
  exact
    (twoLevelRankSelectOverhead_littleO
      hrankSuper hrankBlock hselectSuper hselectBlock).add hlca

structure TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
    (n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat) where
  rankData :
    (shape : Cartesian.CartesianShape) ->
      SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
        shape.bpCode rankSuper rankBlock queryCost
  selectData :
    (shape : Cartesian.CartesianShape) ->
      TwoLevelPayloadLiveStoredWordSelectData
        shape.bpCode selectSuper selectBlock queryCost
  lcaDirectory : SuccinctSpace.PayloadLiveBPCloseLCADirectory n lcaOverhead

namespace TwoLevelPayloadLiveBPCloseRMQNavigationDirectory

def overhead
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (_directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost) : Nat :=
  (rankSuper + rankBlock) + (selectSuper + selectBlock) + lcaOverhead

def encodeAux
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) : List Bool :=
  (directory.rankData shape).auxPayload ++
    (directory.selectData shape).auxPayload ++
      directory.lcaDirectory.encodeAux
        (directory.lcaDirectory.buildAux shape)

def payload
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) : List Bool :=
  shape.bpCode ++ directory.encodeAux shape

def selectCloseCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    RMQ.Costed (Option Nat) :=
  (directory.selectData shape).selectCosted false idx

def lcaCloseCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    RMQ.Costed (Option Nat) :=
  directory.lcaDirectory.lcaCloseCosted
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

def rankCloseCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    RMQ.Costed Nat :=
  (directory.rankData shape).rankCosted false pos

def queryBuiltCosted
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    RMQ.Costed (Option Nat) :=
  RMQ.Costed.bind (directory.selectCloseCosted shape left)
    fun leftClose? =>
      RMQ.Costed.bind
        (directory.selectCloseCosted shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              RMQ.Costed.bind
                (directory.lcaCloseCosted shape leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      RMQ.Costed.map
                        (fun closeRank => some (closeRank - 1))
                        (directory.rankCloseCosted shape (answerClose + 1))
                  | none => RMQ.Costed.pure none
          | _, _ => RMQ.Costed.pure none

theorem encodeAux_length
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.encodeAux shape).length =
      (rankSuper + rankBlock) + (selectSuper + selectBlock) +
        lcaOverhead := by
  have hrank :
      (directory.rankData shape).auxPayload.length =
        rankSuper + rankBlock :=
    (directory.rankData shape).auxPayload_length
  have hselect :
      (directory.selectData shape).auxPayload.length =
        selectSuper + selectBlock :=
    (directory.selectData shape).auxPayload_length
  have hlca :
      (directory.lcaDirectory.encodeAux
          (directory.lcaDirectory.buildAux shape)).length =
        lcaOverhead :=
    directory.lcaDirectory.aux_length_eq (shape := shape) hshape
  simp [encodeAux, hrank, hselect, hlca]
  omega

theorem payload_length
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.payload shape).length =
      2 * n +
        ((rankSuper + rankBlock) + (selectSuper + selectBlock) +
          lcaOverhead) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp : shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have haux := directory.encodeAux_length hshape
  simp [payload, hbp, haux]

theorem selectCloseCosted_cost_le
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).cost <= queryCost := by
  exact (directory.selectData shape).selectCosted_cost_le false idx

theorem lcaCloseCosted_cost_le_one
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted shape leftClose rightClose).cost <= 1 := by
  exact directory.lcaDirectory.lcaCloseCosted_cost_le_one
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

theorem rankCloseCosted_cost_le
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).cost <= queryCost := by
  exact (directory.rankData shape).rankCosted_cost_le false pos

theorem queryBuiltCosted_cost_le
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (directory.queryBuiltCosted shape left right).cost <=
      3 * queryCost + 1 := by
  unfold queryBuiltCosted selectCloseCosted lcaCloseCosted rankCloseCosted
  have hleft := (directory.selectData shape).selectCosted_cost_le false left
  have hright :=
    (directory.selectData shape).selectCosted_cost_le false (right - 1)
  cases hleftValue :
      ((directory.selectData shape).selectCosted false left).value with
  | none =>
      simp [RMQ.Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          ((directory.selectData shape).selectCosted false (right - 1)).value with
      | none =>
          simp [RMQ.Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            directory.lcaDirectory.lcaCloseCosted_cost_le_one
              (directory.lcaDirectory.buildAux shape) leftClose rightClose
          cases hlcaValue :
              (directory.lcaDirectory.lcaCloseCosted
                (directory.lcaDirectory.buildAux shape)
                leftClose rightClose).value with
          | none =>
              simp [RMQ.Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                (directory.rankData shape).rankCosted_cost_le
                  false (answerClose + 1)
              simp [RMQ.Costed.bind, RMQ.Costed.map, hleftValue,
                hrightValue, hlcaValue]
              omega

theorem selectCloseCosted_exact
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  calc
    (directory.selectCloseCosted shape idx).erase =
        RMQ.Succinct.select false shape.bpCode idx := by
      exact (directory.selectData shape).selectCosted_exact false idx
    _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
      exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem rankCloseCosted_exact
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).erase =
      RMQ.Succinct.rankPrefix false shape.bpCode pos := by
  exact (directory.rankData shape).rankCosted_exact false pos

theorem queryBuiltCosted_exact
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryBuiltCosted shape left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
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
      (directory.selectCloseCosted shape left).value = some leftClose := by
    have h := directory.selectCloseCosted_exact shape left
    simpa [RMQ.Costed.erase, hleftClose] using h
  have hselectRight :
      (directory.selectCloseCosted shape (left + len - 1)).value =
        some rightClose := by
    have h := directory.selectCloseCosted_exact shape (left + len - 1)
    simpa [RMQ.Costed.erase, hrightClose] using h
  have hlca :
      (directory.lcaCloseCosted shape leftClose rightClose).value =
        some answerClose := by
    have h :=
      directory.lcaDirectory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose
    simpa [RMQ.Costed.erase, lcaCloseCosted, hanswerClose] using h
  have hrank :
      (directory.rankCloseCosted shape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact :=
      directory.rankCloseCosted_exact shape (answerClose + 1)
    have hrankRecover :=
      SuccinctSpace.bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (directory.rankCloseCosted shape (answerClose + 1)).value =
          RMQ.Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [RMQ.Costed.erase] using hrankExact
      _ = scanWindow shape.representative left len + 1 := hrankRecover
  have hselectLeftRaw :
      ((directory.selectData shape).selectCosted false left).value =
        some leftClose := by
    simpa [selectCloseCosted] using hselectLeft
  have hselectRightRaw :
      ((directory.selectData shape).selectCosted false (left + len - 1)).value =
        some rightClose := by
    simpa [selectCloseCosted] using hselectRight
  have hlcaRaw :
      (directory.lcaDirectory.lcaCloseCosted
          (directory.lcaDirectory.buildAux shape)
          leftClose rightClose).value =
        some answerClose := by
    simpa [lcaCloseCosted] using hlca
  have hrankRaw :
      ((directory.rankData shape).rankCosted false (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    simpa [rankCloseCosted] using hrank
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold queryBuiltCosted
  simp [selectCloseCosted, lcaCloseCosted, rankCloseCosted,
    RMQ.Costed.erase, RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
    hselectLeftRaw, hselectRightRaw, hlcaRaw, hrankRaw, hrankSub]

theorem profile
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.payload shape).length =
          2 * n + directory.overhead) /\
      (forall shape left right,
        (directory.queryBuiltCosted shape left right).cost <=
          3 * queryCost + 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (directory.queryBuiltCosted shape left (left + len)).erase =
                  some (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    simpa [overhead] using directory.payload_length hshape
  · constructor
    · intro shape left right
      exact directory.queryBuiltCosted_cost_le shape left right
    · intro shape hshape left len hlen hbound
      exact directory.queryBuiltCosted_exact hshape hlen hbound

end TwoLevelPayloadLiveBPCloseRMQNavigationDirectory

structure TwoLevelPayloadLiveBPCloseRMQNavigationFamily
    (rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat)
    (queryCost : Nat) where
  directory :
    forall n : Nat,
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory n
        (rankSuper n) (rankBlock n) (selectSuper n) (selectBlock n)
        (lca n) queryCost
  rankSuper_littleO : SuccinctSpace.LittleOLinear rankSuper
  rankBlock_littleO : SuccinctSpace.LittleOLinear rankBlock
  selectSuper_littleO : SuccinctSpace.LittleOLinear selectSuper
  selectBlock_littleO : SuccinctSpace.LittleOLinear selectBlock
  lca_littleO : SuccinctSpace.LittleOLinear lca

namespace TwoLevelPayloadLiveBPCloseRMQNavigationFamily

def overhead
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      TwoLevelPayloadLiveBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    Nat -> Nat :=
  twoLevelBPCloseNavigationOverhead
    rankSuper rankBlock selectSuper selectBlock lca

theorem overhead_littleO
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact
    twoLevelBPCloseNavigationOverhead_littleO
      family.rankSuper_littleO family.rankBlock_littleO
      family.selectSuper_littleO family.selectBlock_littleO
      family.lca_littleO

theorem two_n_plus_o_built_query_profile
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            3 * queryCost + 1) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · have hbase :=
        EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
      simp [overhead, twoLevelBPCloseNavigationOverhead,
        twoLevelRankSelectOverhead,
        SuccinctRankProposal.twoLevelRankOverhead,
        twoLevelSelectOverhead]
      omega
    · constructor
      · intro shape hshape
        simpa [overhead, twoLevelBPCloseNavigationOverhead,
          twoLevelRankSelectOverhead,
          SuccinctRankProposal.twoLevelRankOverhead,
          twoLevelSelectOverhead,
          TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.overhead]
          using (family.directory n).payload_length hshape
      · constructor
        · intro shape left right
          exact (family.directory n).queryBuiltCosted_cost_le shape left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryBuiltCosted_exact
            hshape hlen hbound

end TwoLevelPayloadLiveBPCloseRMQNavigationFamily

structure TwoLevelEncodedBPCloseRMQNavigationView
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    (directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost) where
  selectCloseEncoded : List Bool -> Nat -> RMQ.Costed (Option Nat)
  lcaCloseEncoded : List Bool -> Nat -> Nat -> RMQ.Costed (Option Nat)
  rankCloseEncoded : List Bool -> Nat -> RMQ.Costed Nat
  select_cost_le :
    forall payload idx, (selectCloseEncoded payload idx).cost <= queryCost
  lca_cost_le :
    forall payload leftClose rightClose,
      (lcaCloseEncoded payload leftClose rightClose).cost <= 1
  rank_cost_le :
    forall payload pos, (rankCloseEncoded payload pos).cost <= queryCost
  select_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall idx,
          selectCloseEncoded (directory.payload shape) idx =
            directory.selectCloseCosted shape idx
  lca_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall leftClose rightClose,
          lcaCloseEncoded (directory.payload shape)
              leftClose rightClose =
            directory.lcaCloseCosted shape leftClose rightClose
  rank_agrees_on_built_payload :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall pos,
          rankCloseEncoded (directory.payload shape) pos =
            directory.rankCloseCosted shape pos

namespace TwoLevelEncodedBPCloseRMQNavigationView

def toBPCloseRMQNavigationDirectory
    {n rankSuper rankBlock selectSuper selectBlock lcaOverhead queryCost :
      Nat}
    {directory :
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory
        n rankSuper rankBlock selectSuper selectBlock lcaOverhead
        queryCost}
    (view : TwoLevelEncodedBPCloseRMQNavigationView directory) :
    SuccinctSpace.BPCloseRMQNavigationDirectory n
      ((rankSuper + rankBlock) + (selectSuper + selectBlock) +
        lcaOverhead)
      queryCost 1 queryCost where
  Aux := Cartesian.CartesianShape
  buildAux shape := shape
  encodeAux shape := directory.encodeAux shape
  selectCloseCosted := view.selectCloseEncoded
  lcaCloseCosted := view.lcaCloseEncoded
  rankCloseCosted := view.rankCloseEncoded
  aux_length_eq := by
    intro shape hshape
    exact directory.encodeAux_length hshape
  select_cost_le := by
    intro payload idx
    exact view.select_cost_le payload idx
  lca_cost_le := by
    intro payload leftClose rightClose
    exact view.lca_cost_le payload leftClose rightClose
  rank_cost_le := by
    intro payload pos
    exact view.rank_cost_le payload pos
  select_close_exact := by
    intro shape hshape idx hidx
    have hagree := view.select_agrees_on_built_payload hshape idx
    calc
      (view.selectCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape) idx).erase =
          (directory.selectCloseCosted shape idx).erase := by
            simpa [TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg RMQ.Costed.erase hagree
      _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
            exact directory.selectCloseCosted_exact shape idx
  lca_close_exact := by
    intro shape hshape left len leftClose rightClose
      hlen hbound hleftClose hrightClose
    have hagree :=
      view.lca_agrees_on_built_payload hshape leftClose rightClose
    calc
      (view.lcaCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape)
          leftClose rightClose).erase =
          (directory.lcaCloseCosted shape leftClose rightClose).erase := by
            simpa [TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg RMQ.Costed.erase hagree
      _ = SuccinctSpace.bpCloseOfInorder? shape
            (scanWindow shape.representative left len) := by
            exact directory.lcaDirectory.lcaCloseCosted_exact
              hshape hlen hbound hleftClose hrightClose
  rank_close_exact := by
    intro shape hshape idx close hclose
    have hagree := view.rank_agrees_on_built_payload hshape (close + 1)
    calc
      (view.rankCloseEncoded
          (shape.bpCode ++ directory.encodeAux shape)
          (close + 1)).erase =
          (directory.rankCloseCosted shape (close + 1)).erase := by
            simpa [TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg RMQ.Costed.erase hagree
      _ = RMQ.Succinct.rankPrefix false shape.bpCode (close + 1) := by
            exact directory.rankCloseCosted_exact shape (close + 1)

end TwoLevelEncodedBPCloseRMQNavigationView

structure TwoLevelEncodedBPCloseRMQNavigationFamily
    (rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat)
    (queryCost : Nat) where
  directory :
    forall n : Nat,
      TwoLevelPayloadLiveBPCloseRMQNavigationDirectory n
        (rankSuper n) (rankBlock n) (selectSuper n) (selectBlock n)
        (lca n) queryCost
  view :
    forall n : Nat,
      TwoLevelEncodedBPCloseRMQNavigationView (directory n)
  rankSuper_littleO : SuccinctSpace.LittleOLinear rankSuper
  rankBlock_littleO : SuccinctSpace.LittleOLinear rankBlock
  selectSuper_littleO : SuccinctSpace.LittleOLinear selectSuper
  selectBlock_littleO : SuccinctSpace.LittleOLinear selectBlock
  lca_littleO : SuccinctSpace.LittleOLinear lca

namespace TwoLevelEncodedBPCloseRMQNavigationFamily

def overhead
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    Nat -> Nat :=
  twoLevelBPCloseNavigationOverhead
    rankSuper rankBlock selectSuper selectBlock lca

def toBPCloseRMQNavigationFamily
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.BPCloseRMQNavigationFamily
      family.overhead queryCost 1 queryCost where
  directory n := (family.view n).toBPCloseRMQNavigationDirectory
  overhead_littleO :=
    twoLevelBPCloseNavigationOverhead_littleO
      family.rankSuper_littleO family.rankBlock_littleO
      family.selectSuper_littleO family.selectBlock_littleO
      family.lca_littleO

theorem overhead_littleO
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact family.toBPCloseRMQNavigationFamily.overhead_littleO

def Profile
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) : Prop :=
  SuccinctSpace.LittleOLinear family.overhead /\
    forall n : Nat,
      EncodingLowerBound.logSlackLower n <= 2 * n + family.overhead n /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          ((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadOf shape =
            shape.bpCode ++
              ((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).encodeAux
                (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).buildAux shape)) /\
          (((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadView).payloadBitCount
            ((((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).stateEncoding).buildState shape) =
              2 * n + family.overhead n)) /\
      (forall
        (state : ((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).State)
        left right,
        (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).queryStateCosted
          state left right).cost <=
            2 * queryCost + 1 + queryCost) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).queryStateCosted
                  (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).buildState shape)
                  left (left + len)).erase =
                    some (scanWindow shape.representative left len))

theorem two_n_plus_o_encoded_query_profile
    {rankSuper rankBlock selectSuper selectBlock lca : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelEncodedBPCloseRMQNavigationFamily
        rankSuper rankBlock selectSuper selectBlock lca queryCost) :
    family.Profile := by
  exact
    SuccinctSpace.BPCloseRMQNavigationFamily.two_n_plus_o_close_navigation_profile
      family.toBPCloseRMQNavigationFamily

end TwoLevelEncodedBPCloseRMQNavigationFamily

end SuccinctSelectProposal
end RMQ

