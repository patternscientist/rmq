import RMQ.Core.SuccinctSpace.BPCloseRMQNavigation
import RMQ.Core.SuccinctSpace.RankSelectRAM
import RMQ.Core.SuccinctSpace.BPCloseLCARAM

/-!
# Word-RAM interpretation for BP close-navigation queries

This module is the first whole-query consumer of the `WordRAM` bridges in the
succinct-space layer.  The query still returns a `Costed` value because the
surrounding theorem surface is cost/profile based, but every rank/select/LCA
leaf it uses is evaluated through the interpreter-backed payload reads from
`RankSelectRAM` and `BPCloseLCARAM`.
-/

namespace RMQ

namespace SuccinctSpace

namespace PayloadLiveBPCloseRMQNavigationDirectory

/-- Interpreted select-close leg for the built payload-live directory. -/
def selectCloseInterpretedCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    Costed (Option Nat) :=
  (directory.selectData shape).selectInterpretedCosted false idx

/-- Interpreted rank-close leg for the built payload-live directory. -/
def rankCloseInterpretedCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    Costed Nat :=
  (((directory.rankData shape).rankProgramClamped false pos).eval
    ((directory.rankData shape).rankWordRAMStore false)).toCosted

/-- Interpreted BP close/LCA table leg for the built payload-live directory. -/
def lcaCloseInterpretedCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  ((directory.lcaDirectory.lcaCloseProgram
      (directory.lcaDirectory.buildAux shape) leftClose rightClose).eval
    (directory.lcaDirectory.lcaCloseWordRAMStore
      (directory.lcaDirectory.buildAux shape))).toCosted

theorem selectCloseInterpretedCosted_refines_selectCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    directory.selectCloseInterpretedCosted shape idx =
      directory.selectCloseCosted shape idx := by
  unfold selectCloseInterpretedCosted selectCloseCosted
  exact (directory.selectData shape).selectInterpretedCosted_refines_selectCosted
    false idx

theorem rankCloseInterpretedCosted_refines_rankCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    directory.rankCloseInterpretedCosted shape pos =
      directory.rankCloseCosted shape pos := by
  unfold rankCloseInterpretedCosted rankCloseCosted
  exact (directory.rankData shape).rankProgramClamped_refines_rankCostedClamped
    false pos

theorem lcaCloseInterpretedCosted_refines_lcaCloseCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    directory.lcaCloseInterpretedCosted shape leftClose rightClose =
      directory.lcaCloseCosted shape leftClose rightClose := by
  unfold lcaCloseInterpretedCosted lcaCloseCosted
  exact directory.lcaDirectory.lcaCloseProgram_refines_lcaCloseCosted
    (directory.lcaDirectory.buildAux shape) leftClose rightClose

/--
Built BP close-navigation query whose component reads are interpreter-backed.

This is intentionally the same option-sequencing shape as `queryBuiltCosted`;
the difference is that the select/rank/LCA leaves are the interpreted versions
above, not the older direct costed leaves.
-/
def queryBuiltInterpretedCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.selectCloseInterpretedCosted shape left)
    fun leftClose? =>
      Costed.bind
        (directory.selectCloseInterpretedCosted shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (directory.lcaCloseInterpretedCosted shape leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (directory.rankCloseInterpretedCosted shape
                          (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none

theorem queryBuiltInterpretedCosted_refines_queryBuiltCosted
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    directory.queryBuiltInterpretedCosted shape left right =
      directory.queryBuiltCosted shape left right := by
  unfold queryBuiltInterpretedCosted queryBuiltCosted
  simp only [
    directory.selectCloseInterpretedCosted_refines_selectCloseCosted,
    directory.lcaCloseInterpretedCosted_refines_lcaCloseCosted,
    directory.rankCloseInterpretedCosted_refines_rankCloseCosted]
  rfl

theorem queryBuiltInterpretedCosted_cost_le_ten
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (directory.queryBuiltInterpretedCosted shape left right).cost <= 10 := by
  rw [directory.queryBuiltInterpretedCosted_refines_queryBuiltCosted
    shape left right]
  exact directory.queryBuiltCosted_cost_le_ten shape left right

theorem queryBuiltInterpretedCosted_exact
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryBuiltInterpretedCosted shape left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  rw [directory.queryBuiltInterpretedCosted_refines_queryBuiltCosted]
  exact directory.queryBuiltCosted_exact hshape hlen hbound

theorem interpreted_profile
    {n rankOverhead selectOverhead lcaOverhead : Nat}
    (directory :
      PayloadLiveBPCloseRMQNavigationDirectory
        n rankOverhead selectOverhead lcaOverhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.payload shape).length =
          2 * n + (rankOverhead + selectOverhead + lcaOverhead)) /\
      (forall shape left right,
        (directory.queryBuiltInterpretedCosted shape left right).cost <= 10) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len : Nat},
            0 < len ->
              left + len <= n ->
                (directory.queryBuiltInterpretedCosted
                  shape left (left + len)).erase =
                  some (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.payload_length hshape
  · constructor
    · intro shape left right
      exact directory.queryBuiltInterpretedCosted_cost_le_ten shape left right
    · intro shape hshape left len hlen hbound
      exact directory.queryBuiltInterpretedCosted_exact hshape hlen hbound

end PayloadLiveBPCloseRMQNavigationDirectory

namespace PayloadLiveBPCloseRMQNavigationFamily

/--
Family-level `2*n + o(n)` profile whose query path uses the interpreted
rank/select/LCA leaves.
-/
theorem two_n_plus_o_interpreted_built_query_profile
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
          ((family.directory n).queryBuiltInterpretedCosted
            shape left right).cost <= 10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltInterpretedCosted
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
          exact (family.directory n).queryBuiltInterpretedCosted_cost_le_ten
            shape left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryBuiltInterpretedCosted_exact
            hshape hlen hbound

end PayloadLiveBPCloseRMQNavigationFamily

namespace SampledPayloadLiveBPCloseRMQNavigationFamily

theorem two_n_plus_o_interpreted_built_query_profile
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
          ((family.directory n).queryBuiltInterpretedCosted
            shape left right).cost <= 10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltInterpretedCosted
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  exact
    PayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_built_query_profile
      family.toPayloadLiveBPCloseRMQNavigationFamily

end SampledPayloadLiveBPCloseRMQNavigationFamily

namespace WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily

theorem two_n_plus_o_interpreted_bounded_built_query_profile
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
          ((family.directory n).queryBuiltInterpretedCosted
            shape left right).cost <= 10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltInterpretedCosted
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
      family.toSampledFamily.two_n_plus_o_interpreted_built_query_profile.2 n
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

namespace WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily

theorem two_n_plus_o_interpreted_word_bounded_query_profile
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :
    LittleOLinear family.toWordBoundedSampledFamily.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.toWordBoundedSampledFamily.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).payload shape).length =
              2 * n + family.toWordBoundedSampledFamily.overhead n) /\
        (forall shape left right,
          ((family.directory n).queryBuiltInterpretedCosted
            shape left right).cost <= 10) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryBuiltInterpretedCosted
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
  exact
    WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_bounded_built_query_profile
      family.toWordBoundedSampledFamily

end WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily

end SuccinctSpace

end RMQ
