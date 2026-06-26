import RMQ.Core.SuccinctSpace.BPCloseLCA

namespace RMQ

namespace SuccinctSpace

/--
BP close-navigation RMQ directory.

This is the BP/LCA query skeleton: select the close parenthesis for the two
endpoint inorder nodes, compute the close parenthesis of their BP-LCA, then use
rank over closing parentheses to recover the inorder/RMQ index.  The primitive
navigation operation is abstract, but the endpoint/rank plumbing is proved
once here.
-/
structure BPCloseRMQNavigationDirectory
    (n overhead selectCost lcaCost rankCost : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  selectCloseCosted : List Bool -> Nat -> Costed (Option Nat)
  lcaCloseCosted : List Bool -> Nat -> Nat -> Costed (Option Nat)
  rankCloseCosted : List Bool -> Nat -> Costed Nat
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  select_cost_le :
    forall payload occurrence,
      (selectCloseCosted payload occurrence).cost <= selectCost
  lca_cost_le :
    forall payload leftClose rightClose,
      (lcaCloseCosted payload leftClose rightClose).cost <= lcaCost
  rank_cost_le :
    forall payload pos,
      (rankCloseCosted payload pos).cost <= rankCost
  select_close_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {idx : Nat},
          idx < n ->
            (selectCloseCosted
              (shape.bpCode ++ encodeAux (buildAux shape))
              idx).erase =
                bpCloseOfInorder? shape idx
  lca_close_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len leftClose rightClose : Nat},
          0 < len ->
            left + len <= n ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  (lcaCloseCosted
                    (shape.bpCode ++ encodeAux (buildAux shape))
                    leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)
  rank_close_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {idx close : Nat},
          bpCloseOfInorder? shape idx = some close ->
            (rankCloseCosted
              (shape.bpCode ++ encodeAux (buildAux shape))
              (close + 1)).erase =
                Succinct.rankPrefix false shape.bpCode (close + 1)

namespace BPCloseRMQNavigationDirectory

def queryEncodedCosted
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost)
    (payload : List Bool) (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (directory.selectCloseCosted payload left) fun leftClose? =>
    Costed.bind (directory.selectCloseCosted payload (right - 1))
      fun rightClose? =>
        match leftClose?, rightClose? with
        | some leftClose, some rightClose =>
            Costed.bind
              (directory.lcaCloseCosted payload leftClose rightClose)
              fun answerClose? =>
                match answerClose? with
                | some answerClose =>
                    Costed.map (fun closeRank => some (closeRank - 1))
                      (directory.rankCloseCosted payload (answerClose + 1))
                | none => Costed.pure none
        | _, _ => Costed.pure none

theorem queryEncodedCosted_cost_le
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost)
    (payload : List Bool) (left right : Nat) :
    (directory.queryEncodedCosted payload left right).cost <=
      2 * selectCost + lcaCost + rankCost := by
  unfold queryEncodedCosted
  have hleft := directory.select_cost_le payload left
  have hright := directory.select_cost_le payload (right - 1)
  cases hleftValue : (directory.selectCloseCosted payload left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          (directory.selectCloseCosted payload (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            directory.lca_cost_le payload leftClose rightClose
          cases hlcaValue :
              (directory.lcaCloseCosted payload leftClose rightClose).value with
          | none =>
              simp [Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                directory.rank_cost_le payload (answerClose + 1)
              simp [Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
              omega

theorem queryEncodedCosted_exact
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryEncodedCosted
      (shape.bpCode ++ directory.encodeAux (directory.buildAux shape))
      left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hreprLen : shape.representative.length = n := by
    rw [Cartesian.CartesianShape.representative_length,
      Cartesian.ShapeOfSize.size_eq hshapeSize]
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len (by omega)
  have hscanLt : scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases bpCloseOfInorder?_some_of_lt shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :=
    directory.select_close_exact hshape (idx := left) hleftLt
  have hselectRight :=
    directory.select_close_exact hshape
      (idx := left + len - 1) hrightLt
  have hlca :=
    directory.lca_close_exact hshape hlen hbound
      hleftClose hrightClose
  have hrank :=
    directory.rank_close_exact hshape hanswerClose
  have hrankRecover :=
    bpCloseOfInorder?_rankFalse_succ shape hanswerClose
  unfold queryEncodedCosted
  simp [Costed.erase_bind, Costed.erase_map, hselectLeft, hleftClose,
    hselectRight, hrightClose, hlca, hanswerClose, hrank, hrankRecover]

def toBPBroadwordRMQDirectory
    {n overhead selectCost lcaCost rankCost : Nat}
    (directory :
      BPCloseRMQNavigationDirectory
        n overhead selectCost lcaCost rankCost) :
    BPBroadwordRMQDirectory n overhead
      (2 * selectCost + lcaCost + rankCost) where
  Aux := directory.Aux
  buildAux := directory.buildAux
  encodeAux := directory.encodeAux
  queryEncodedCosted := directory.queryEncodedCosted
  aux_length_eq := by
    intro shape hshape
    exact directory.aux_length_eq hshape
  query_cost_le := by
    intro payload left right
    exact directory.queryEncodedCosted_cost_le payload left right
  query_exact := by
    intro shape hshape left len hlen hbound
    exact directory.queryEncodedCosted_exact hshape hlen hbound

end BPCloseRMQNavigationDirectory

/-- Family form of the BP close-navigation RMQ adapter. -/
structure BPCloseRMQNavigationFamily
    (overhead : Nat -> Nat) (selectCost lcaCost rankCost : Nat) where
  directory :
    forall n : Nat,
      BPCloseRMQNavigationDirectory
        n (overhead n) selectCost lcaCost rankCost
  overhead_littleO : LittleOLinear overhead

namespace BPCloseRMQNavigationFamily

theorem two_n_plus_o_close_navigation_profile
    {overhead : Nat -> Nat} {selectCost lcaCost rankCost : Nat}
    (family :
      BPCloseRMQNavigationFamily
        overhead selectCost lcaCost rankCost) :
    LittleOLinear overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <= 2 * n + overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((((family.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadOf shape =
              shape.bpCode ++
                ((family.directory n).toBPBroadwordRMQDirectory).encodeAux
                  (((family.directory n).toBPBroadwordRMQDirectory).buildAux shape)) /\
            (((((family.directory n).toBPBroadwordRMQDirectory).stateEncoding).payloadView).payloadBitCount
              ((((family.directory n).toBPBroadwordRMQDirectory).stateEncoding).buildState shape) =
                2 * n + overhead n)) /\
        (forall
          (state : ((family.directory n).toBPBroadwordRMQDirectory).State)
          left right,
          (((family.directory n).toBPBroadwordRMQDirectory).queryStateCosted
            state left right).cost <=
              2 * selectCost + lcaCost + rankCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (((family.directory n).toBPBroadwordRMQDirectory).queryStateCosted
                    (((family.directory n).toBPBroadwordRMQDirectory).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · exact
        BPBroadwordRMQDirectory.payloadSpaceBounds_lower_le_upper
          ((family.directory n).toBPBroadwordRMQDirectory)
    · constructor
      · intro shape hshape
        exact
          ⟨BPBroadwordRMQDirectory.payloadOf_eq
              ((family.directory n).toBPBroadwordRMQDirectory) shape,
            BPBroadwordRMQDirectory.payloadBitCount_eq
              ((family.directory n).toBPBroadwordRMQDirectory) hshape⟩
      · constructor
        · intro state left right
          exact
            BPBroadwordRMQDirectory.queryStateCosted_cost_le
              ((family.directory n).toBPBroadwordRMQDirectory)
              state left right
        · intro shape hshape left len hlen hbound
          exact
            BPBroadwordRMQDirectory.queryStateCosted_exact
              ((family.directory n).toBPBroadwordRMQDirectory)
              hshape hlen hbound

end BPCloseRMQNavigationFamily

/-- Auxiliary budget for the payload-live BP close-navigation construction. -/
def bpCloseNavigationOverhead
    (rank select lca : Nat -> Nat) (n : Nat) : Nat :=
  rank n + select n + lca n

theorem bpCloseNavigationOverhead_littleO
    {rank select lca : Nat -> Nat}
    (hrank : LittleOLinear rank)
    (hselect : LittleOLinear select)
    (hlca : LittleOLinear lca) :
    LittleOLinear (bpCloseNavigationOverhead rank select lca) := by
  unfold bpCloseNavigationOverhead
  exact (hrank.add hselect).add hlca

/--
Payload-live BP close-navigation RMQ directory for built Cartesian shapes.

Unlike the retired one-read RMQ answer-table boundary, this query is an explicit
composition: select the two close parentheses, read the BP LCA-close navigation
entry, and rank that close position back to an inorder index.  The component
stores are tied to counted payload words by their own payload-live profiles.
-/
structure PayloadLiveBPCloseRMQNavigationDirectory
    (n rankOverhead selectOverhead lcaOverhead : Nat) where
  rankData :
    (shape : Cartesian.CartesianShape) ->
      PayloadLiveStoredWordRankData
        shape.bpCode rankOverhead
  selectData :
    (shape : Cartesian.CartesianShape) ->
      PayloadLiveStoredWordSelectData
        shape.bpCode selectOverhead
  lcaDirectory : PayloadLiveBPCloseLCADirectory n lcaOverhead

namespace PayloadLiveBPCloseRMQNavigationDirectory

def overhead
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (_directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead) : Nat :=
  rankOverhead + selectOverhead + lcaOverhead

def encodeAux
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) : List Bool :=
  (directory.rankData shape).auxPayload ++
    (directory.selectData shape).auxPayload ++
      directory.lcaDirectory.encodeAux
        (directory.lcaDirectory.buildAux shape)

def payload
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) : List Bool :=
  shape.bpCode ++ directory.encodeAux shape

def selectCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    Costed (Option Nat) :=
  (directory.selectData shape).selectCosted false idx

def lcaCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  directory.lcaDirectory.lcaCloseCosted
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

def rankCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    Costed Nat :=
  (directory.rankData shape).rankCostedClamped false pos

def queryBuiltCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.selectCloseCosted shape left) fun leftClose? =>
    Costed.bind (directory.selectCloseCosted shape (right - 1))
      fun rightClose? =>
        match leftClose?, rightClose? with
        | some leftClose, some rightClose =>
            Costed.bind
              (directory.lcaCloseCosted shape leftClose rightClose)
              fun answerClose? =>
                match answerClose? with
                | some answerClose =>
                    Costed.map (fun closeRank => some (closeRank - 1))
                      (directory.rankCloseCosted shape (answerClose + 1))
                | none => Costed.pure none
        | _, _ => Costed.pure none

theorem encodeAux_length
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.encodeAux shape).length =
      rankOverhead + selectOverhead + lcaOverhead := by
  have hrank : (directory.rankData shape).auxPayload.length = rankOverhead :=
    (directory.rankData shape).auxPayload_length
  have hselect :
      (directory.selectData shape).auxPayload.length = selectOverhead :=
    (directory.selectData shape).auxPayload_length
  have hlca :
      (directory.lcaDirectory.encodeAux
          (directory.lcaDirectory.buildAux shape)).length =
        lcaOverhead :=
    directory.lcaDirectory.aux_length_eq (shape := shape) hshape
  simp [encodeAux, hrank, hselect, hlca]
  omega

theorem payload_length
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (directory.payload shape).length =
      2 * n + (rankOverhead + selectOverhead + lcaOverhead) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n := by
    exact Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have haux := directory.encodeAux_length hshape
  simp [payload, hbp, haux]

theorem selectCloseCosted_cost_le_three
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).cost <= 3 := by
  exact (directory.selectData shape).selectCosted_cost_le_three false idx

theorem lcaCloseCosted_cost_le_one
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted shape leftClose rightClose).cost <= 1 := by
  exact directory.lcaDirectory.lcaCloseCosted_cost_le_one
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

theorem rankCloseCosted_cost_le_three
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).cost <= 3 := by
  exact (directory.rankData shape).rankCostedClamped_cost_le_three false pos

theorem queryBuiltCosted_cost_le_ten
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (directory.queryBuiltCosted shape left right).cost <= 10 := by
  unfold queryBuiltCosted selectCloseCosted lcaCloseCosted rankCloseCosted
  have hleft :=
    (directory.selectData shape).selectCosted_cost_le_three false left
  have hright :=
    (directory.selectData shape).selectCosted_cost_le_three
      false (right - 1)
  cases hleftValue :
      ((directory.selectData shape).selectCosted false left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          ((directory.selectData shape).selectCosted false (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
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
              simp [Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                (directory.rankData shape).rankCostedClamped_cost_le_three
                  false (answerClose + 1)
              simp [Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
              omega

theorem selectCloseCosted_exact
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (directory.selectCloseCosted shape idx).erase =
      bpCloseOfInorder? shape idx := by
  calc
    (directory.selectCloseCosted shape idx).erase =
        Succinct.select false shape.bpCode idx := by
      exact (directory.selectData shape).selectCosted_exact false idx
    _ = bpCloseOfInorder? shape idx := by
      exact select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem rankCloseCosted_exact
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (directory.rankCloseCosted shape pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact (directory.rankData shape).rankCostedClamped_exact false pos

theorem queryBuiltCosted_exact
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
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
  rcases bpCloseOfInorder?_some_of_lt shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (directory.selectCloseCosted shape left).value =
        some leftClose := by
    have h := directory.selectCloseCosted_exact shape left
    simpa [Costed.erase, hleftClose] using h
  have hselectRight :
      (directory.selectCloseCosted shape (left + len - 1)).value =
        some rightClose := by
    have h := directory.selectCloseCosted_exact shape (left + len - 1)
    simpa [Costed.erase, hrightClose] using h
  have hlca :
      (directory.lcaCloseCosted shape leftClose rightClose).value =
        some answerClose := by
    have h :=
      directory.lcaDirectory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose
    simpa [Costed.erase, lcaCloseCosted, hanswerClose] using h
  have hrank :
      (directory.rankCloseCosted shape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact := directory.rankCloseCosted_exact shape (answerClose + 1)
    have hrankRecover :=
      bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (directory.rankCloseCosted shape (answerClose + 1)).value =
          Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact
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
      ((directory.rankData shape).rankCostedClamped false
          (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    simpa [rankCloseCosted] using hrank
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold queryBuiltCosted
  simp [selectCloseCosted, lcaCloseCosted, rankCloseCosted, Costed.erase,
    Costed.bind, Costed.map, Costed.pure,
    hselectLeftRaw, hselectRightRaw, hlcaRaw, hrankRaw, hrankSub]

theorem profile
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.payload shape).length =
          2 * n + (rankOverhead + selectOverhead + lcaOverhead)) /\
      (forall shape left right,
        (directory.queryBuiltCosted shape left right).cost <= 10) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (directory.queryBuiltCosted shape left (left + len)).erase =
                  some (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.payload_length hshape
  · constructor
    · intro shape left right
      exact directory.queryBuiltCosted_cost_le_ten shape left right
    · intro shape hshape left len hlen hbound
      exact directory.queryBuiltCosted_exact hshape hlen hbound

end PayloadLiveBPCloseRMQNavigationDirectory

/--
Payload-only component view for a payload-live BP close-navigation directory.

The functions in this view are the only operations used by the encoded query.
The agreement fields certify that, on payloads produced by the built directory,
they are extensionally the same as the stateful component queries.  This is the
honest bridge toward `BPBroadwordRMQDirectory`: no payload decoder or shape
reconstruction is hidden in the bridge theorem.
-/
structure EncodedPayloadLiveBPCloseRMQNavigationView
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead) where
  selectCloseEncoded : List Bool -> Nat -> Costed (Option Nat)
  lcaCloseEncoded : List Bool -> Nat -> Nat -> Costed (Option Nat)
  rankCloseEncoded : List Bool -> Nat -> Costed Nat
  select_cost_le :
    forall payload idx, (selectCloseEncoded payload idx).cost <= 3
  lca_cost_le :
    forall payload leftClose rightClose,
      (lcaCloseEncoded payload leftClose rightClose).cost <= 1
  rank_cost_le :
    forall payload pos, (rankCloseEncoded payload pos).cost <= 3
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

namespace EncodedPayloadLiveBPCloseRMQNavigationView

def toBPCloseRMQNavigationDirectory
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    {directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead}
    (view : EncodedPayloadLiveBPCloseRMQNavigationView directory) :
    BPCloseRMQNavigationDirectory n
      (rankOverhead + selectOverhead + lcaOverhead) 3 1 3 where
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
            simpa [PayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg Costed.erase hagree
      _ = bpCloseOfInorder? shape idx := by
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
            simpa [PayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg Costed.erase hagree
      _ = bpCloseOfInorder? shape
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
            simpa [PayloadLiveBPCloseRMQNavigationDirectory.payload]
              using congrArg Costed.erase hagree
      _ = Succinct.rankPrefix false shape.bpCode (close + 1) := by
            exact directory.rankCloseCosted_exact shape (close + 1)

end EncodedPayloadLiveBPCloseRMQNavigationView

/-- Family form of the payload-encoded BP close-navigation query. -/
structure EncodedPayloadLiveBPCloseRMQNavigationFamily
    (rank select lca : Nat -> Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory
        n (rank n) (select n) (lca n)
  view :
    forall n : Nat,
      EncodedPayloadLiveBPCloseRMQNavigationView (directory n)
  rank_littleO : LittleOLinear rank
  select_littleO : LittleOLinear select
  lca_littleO : LittleOLinear lca

namespace EncodedPayloadLiveBPCloseRMQNavigationFamily

def overhead
    {rank select lca : Nat -> Nat}
    (_family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    Nat -> Nat :=
  bpCloseNavigationOverhead rank select lca

def toBPCloseRMQNavigationFamily
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    BPCloseRMQNavigationFamily family.overhead 3 1 3 where
  directory n := (family.view n).toBPCloseRMQNavigationDirectory
  overhead_littleO :=
    bpCloseNavigationOverhead_littleO
      family.rank_littleO family.select_littleO family.lca_littleO

theorem overhead_littleO
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    LittleOLinear family.overhead := by
  exact family.toBPCloseRMQNavigationFamily.overhead_littleO

def Profile
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) : Prop :=
  LittleOLinear family.overhead /\
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
            2 * 3 + 1 + 3) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).queryStateCosted
                  (((family.toBPCloseRMQNavigationFamily.directory n).toBPBroadwordRMQDirectory).buildState shape)
                  left (left + len)).erase =
                    some (scanWindow shape.representative left len))

/--
Payload-encoded `2*n + o(n)` close-navigation profile.

The query operates through encoded payload functions only.  The view fields are
the refinement certificates connecting those payload functions back to the
stateful payload-live directory on payloads produced by `buildState`.
-/
theorem two_n_plus_o_encoded_query_profile
    {rank select lca : Nat -> Nat}
    (family :
      EncodedPayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    family.Profile := by
  exact
    BPCloseRMQNavigationFamily.two_n_plus_o_close_navigation_profile
      family.toBPCloseRMQNavigationFamily

end EncodedPayloadLiveBPCloseRMQNavigationFamily

/--
Sampled-envelope payload-encoded BP close-navigation family.

This combines the two current fronts: payload-only encoded component operations
and the canonical sampled-directory `o(n)` auxiliary budget.
-/
structure SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)
  view :
    forall n : Nat,
      EncodedPayloadLiveBPCloseRMQNavigationView (directory n)

namespace SampledEncodedPayloadLiveBPCloseRMQNavigationFamily

def rankOverhead (rankSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead rankSlots

def selectOverhead (selectSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead selectSlots

def lcaOverhead (lcaSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead lcaSlots

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (_family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  bpCloseNavigationOverhead
    (rankOverhead rankSlots)
    (selectOverhead selectSlots)
    (lcaOverhead lcaSlots)

def toEncodedFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    EncodedPayloadLiveBPCloseRMQNavigationFamily
      (rankOverhead rankSlots)
      (selectOverhead selectSlots)
      (lcaOverhead lcaSlots) where
  directory := family.directory
  view := family.view
  rank_littleO := sampledDirectoryOverhead_littleO rankSlots
  select_littleO := sampledDirectoryOverhead_littleO selectSlots
  lca_littleO := sampledDirectoryOverhead_littleO lcaSlots

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toEncodedFamily.overhead_littleO

theorem two_n_plus_o_sampled_encoded_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    family.toEncodedFamily.Profile := by
  exact family.toEncodedFamily.two_n_plus_o_encoded_query_profile

end SampledEncodedPayloadLiveBPCloseRMQNavigationFamily

/-- Family form of the payload-live BP close-navigation query. -/
structure PayloadLiveBPCloseRMQNavigationFamily
    (rank select lca : Nat -> Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory
        n (rank n) (select n) (lca n)
  rank_littleO : LittleOLinear rank
  select_littleO : LittleOLinear select
  lca_littleO : LittleOLinear lca

namespace PayloadLiveBPCloseRMQNavigationFamily

def overhead
    {rank select lca : Nat -> Nat}
    (_family :
      PayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    Nat -> Nat :=
  bpCloseNavigationOverhead rank select lca

theorem overhead_littleO
    {rank select lca : Nat -> Nat}
    (family :
      PayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    LittleOLinear family.overhead :=
  bpCloseNavigationOverhead_littleO
    family.rank_littleO family.select_littleO family.lca_littleO

theorem two_n_plus_o_built_query_profile
    {rank select lca : Nat -> Nat}
    (family :
      PayloadLiveBPCloseRMQNavigationFamily rank select lca) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            10) /\
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
      simp [overhead, bpCloseNavigationOverhead]
      omega
    · constructor
      · intro shape hshape
        exact (family.directory n).payload_length hshape
      · constructor
        · intro shape left right
          exact (family.directory n).queryBuiltCosted_cost_le_ten
            shape left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryBuiltCosted_exact
            hshape hlen hbound

end PayloadLiveBPCloseRMQNavigationFamily

/--
Payload-live BP close-navigation family with all auxiliary components budgeted
by the canonical sampled-directory envelope.

This is the narrow sampled-budget capstone: it does not construct a rank/select
or LCA-close scheme, but it fixes the target asymptotic budget that concrete
sampled codecs must meet.
-/
structure SampledPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)

namespace SampledPayloadLiveBPCloseRMQNavigationFamily

def rankOverhead (rankSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead rankSlots

def selectOverhead (selectSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead selectSlots

def lcaOverhead (lcaSlots : Nat) : Nat -> Nat :=
  sampledDirectoryOverhead lcaSlots

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (_family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  bpCloseNavigationOverhead
    (rankOverhead rankSlots)
    (selectOverhead selectSlots)
    (lcaOverhead lcaSlots)

def toPayloadLiveBPCloseRMQNavigationFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    PayloadLiveBPCloseRMQNavigationFamily
      (rankOverhead rankSlots)
      (selectOverhead selectSlots)
      (lcaOverhead lcaSlots) where
  directory := family.directory
  rank_littleO := sampledDirectoryOverhead_littleO rankSlots
  select_littleO := sampledDirectoryOverhead_littleO selectSlots
  lca_littleO := sampledDirectoryOverhead_littleO lcaSlots

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toPayloadLiveBPCloseRMQNavigationFamily.overhead_littleO

theorem two_n_plus_o_built_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      SampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  exact
    PayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile
      family.toPayloadLiveBPCloseRMQNavigationFamily

end SampledPayloadLiveBPCloseRMQNavigationFamily

/--
Sampled BP close-navigation family with explicit word-size bounds for the
rank/select payload stores.

This keeps the existing stateful query theorem, but strengthens the
representation discipline needed for a broadword interpretation: the BP payload
stores used by rank and select cannot be a single unbounded word.
-/
structure WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)
  selectWordSize : Nat -> Cartesian.CartesianShape -> Nat
  select_wordSize_pos :
    forall n shape, 0 < selectWordSize n shape
  rank_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).rankData shape).bitWords.words.toList) ->
        word.length <= ((directory n).rankData shape).wordSize
  select_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).selectData shape).bitWords.words.toList) ->
        word.length <= selectWordSize n shape

namespace WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily

def toSampledFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    SampledPayloadLiveBPCloseRMQNavigationFamily
      rankSlots selectSlots lcaSlots where
  directory := family.directory

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  family.toSampledFamily.overhead

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toSampledFamily.overhead_littleO

theorem two_n_plus_o_bounded_built_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltCosted shape left right).cost <=
            10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) /\
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).rankData shape).bitWords.words.toList) ->
            word.length <=
              ((family.directory n).rankData shape).wordSize) /\
        (forall shape, 0 < family.selectWordSize n shape) /\
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).selectData shape).bitWords.words.toList) ->
            word.length <= family.selectWordSize n shape) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    have hprofile :=
      family.toSampledFamily.two_n_plus_o_built_query_profile.2 n
    rcases hprofile with
      ⟨hlower, hpayload, hcost, hexact⟩
    constructor
    · exact hlower
    · constructor
      · exact hpayload
      · constructor
        · exact hcost
        · constructor
          · exact hexact
          · constructor
            · intro shape word hmem
              exact family.rank_word_length_le n shape hmem
            · constructor
              · intro shape
                exact family.select_wordSize_pos n shape
              · intro shape word hmem
                exact family.select_word_length_le n shape hmem

end WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily

/--
Sampled encoded BP close-navigation family with explicit word-size bounds.

This is the strongest abstract upper-bound target currently exposed: queries
run through payload-only encoded functions, auxiliary payloads fit the sampled
`o(n)` envelope, and the rank/select stored payload words are bounded instead
of being modeled as one unbounded aggregate word.
-/
structure WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
    (rankSlots selectSlots lcaSlots : Nat) where
  directory :
    forall n : Nat,
      PayloadLiveBPCloseRMQNavigationDirectory n
        (sampledDirectoryOverhead rankSlots n)
        (sampledDirectoryOverhead selectSlots n)
        (sampledDirectoryOverhead lcaSlots n)
  view :
    forall n : Nat,
      EncodedPayloadLiveBPCloseRMQNavigationView (directory n)
  selectWordSize : Nat -> Cartesian.CartesianShape -> Nat
  select_wordSize_pos :
    forall n shape, 0 < selectWordSize n shape
  rank_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).rankData shape).bitWords.words.toList) ->
        word.length <= ((directory n).rankData shape).wordSize
  select_word_length_le :
    forall n (shape : Cartesian.CartesianShape) {word : List Bool},
      List.Mem word (((directory n).selectData shape).bitWords.words.toList) ->
        word.length <= selectWordSize n shape

namespace WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily

def toSampledEncodedFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    SampledEncodedPayloadLiveBPCloseRMQNavigationFamily
      rankSlots selectSlots lcaSlots where
  directory := family.directory
  view := family.view

def toWordBoundedSampledFamily
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily
      rankSlots selectSlots lcaSlots where
  directory := family.directory
  selectWordSize := family.selectWordSize
  select_wordSize_pos := family.select_wordSize_pos
  rank_word_length_le := family.rank_word_length_le
  select_word_length_le := family.select_word_length_le

def overhead
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) : Nat -> Nat :=
  family.toSampledEncodedFamily.overhead

theorem overhead_littleO
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.overhead := by
  exact family.toSampledEncodedFamily.overhead_littleO

theorem two_n_plus_o_word_bounded_encoded_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    family.toSampledEncodedFamily.toEncodedFamily.Profile /\
      forall n : Nat,
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).rankData shape).bitWords.words.toList) ->
            word.length <=
              ((family.directory n).rankData shape).wordSize) /\
        (forall shape, 0 < family.selectWordSize n shape) /\
        (forall shape {word : List Bool},
          List.Mem word
              (((family.directory n).selectData shape).bitWords.words.toList) ->
            word.length <= family.selectWordSize n shape) := by
  constructor
  · exact family.toSampledEncodedFamily.two_n_plus_o_sampled_encoded_query_profile
  · intro n
    constructor
    · intro shape word hmem
      exact family.rank_word_length_le n shape hmem
    · constructor
      · intro shape
        exact family.select_wordSize_pos n shape
      · intro shape word hmem
        exact family.select_word_length_le n shape hmem

end WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily

/-- A family of certified BP-native broadword RMQ directories. -/
structure BPBroadwordSuccinctRMQFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall n : Nat, BPBroadwordRMQDirectory n (overhead n) queryCost
  overhead_littleO : LittleOLinear overhead

namespace BPBroadwordSuccinctRMQFamily

/--
Research-facing BP-native `2*n + o(n)`, constant-query profile.

The payload equality clause exposes the concrete representation: the counted
`2*n` part is the Cartesian shape's balanced-parentheses code.
-/
theorem two_n_plus_o_constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : BPBroadwordSuccinctRMQFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <= 2 * n + overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (((family.directory n).stateEncoding).payloadOf shape =
              shape.bpCode ++
                (family.directory n).encodeAux
                  ((family.directory n).buildAux shape)) /\
            ((((family.directory n).stateEncoding).payloadView).payloadBitCount
              (((family.directory n).stateEncoding).buildState shape) =
                2 * n + overhead n)) /\
        (forall (state : (family.directory n).State) left right,
          ((family.directory n).queryStateCosted state left right).cost <=
            queryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryStateCosted
                    ((family.directory n).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · exact (family.directory n).payloadSpaceBounds_lower_le_upper
    · constructor
      · intro shape hshape
        exact ⟨(family.directory n).payloadOf_eq shape,
          (family.directory n).payloadBitCount_eq hshape⟩
      · constructor
        · intro state left right
          exact (family.directory n).queryStateCosted_cost_le state left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryStateCosted_exact hshape hlen hbound

end BPBroadwordSuccinctRMQFamily

/--
Componentized version of the broadword family interface.  This is the shape
expected from a concrete BP/rank-select implementation: each auxiliary
component supplies its own `o(n)` proof, while the directory states the exact
sum of their counted bits.
-/
structure ComponentizedBPRMQFamily
    (rank select excess micro : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall n : Nat,
      BroadwordRMQDirectory n
        (bpAuxOverhead rank select excess micro n) queryCost
  rank_littleO : LittleOLinear rank
  select_littleO : LittleOLinear select
  excess_littleO : LittleOLinear excess
  micro_littleO : LittleOLinear micro

namespace ComponentizedBPRMQFamily

def overhead
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (_family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    Nat -> Nat :=
  bpAuxOverhead rank select excess micro

theorem overhead_littleO
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    LittleOLinear family.overhead := by
  exact bpAuxOverhead_littleO
    family.rank_littleO family.select_littleO
    family.excess_littleO family.micro_littleO

def toBroadwordSuccinctRMQFamily
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    BroadwordSuccinctRMQFamily family.overhead queryCost where
  directory := family.directory
  overhead_littleO := family.overhead_littleO

theorem two_n_plus_o_constant_query_profile
    {rank select excess micro : Nat -> Nat} {queryCost : Nat}
    (family : ComponentizedBPRMQFamily rank select excess micro queryCost) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (((((family.toBroadwordSuccinctRMQFamily).directory n).stateEncoding).payloadView).payloadBitCount
              ((((family.toBroadwordSuccinctRMQFamily).directory n).stateEncoding).buildState shape) =
                2 * n + family.overhead n)) /\
        (forall
          (state :
            ((family.toBroadwordSuccinctRMQFamily).directory n).State)
          left right,
          (((family.toBroadwordSuccinctRMQFamily).directory n).queryStateCosted
              state left right).cost <= queryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (((family.toBroadwordSuccinctRMQFamily).directory n).queryStateCosted
                    (((family.toBroadwordSuccinctRMQFamily).directory n).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  exact
    BroadwordSuccinctRMQFamily.two_n_plus_o_constant_query_profile
      family.toBroadwordSuccinctRMQFamily

end ComponentizedBPRMQFamily

end SuccinctSpace

end RMQ
