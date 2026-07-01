import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectory
import RMQ.Core.SuccinctSpace.RankSelectRAM

/-!
# Word-RAM rank-seed bridge for compact BP close/LCA

This module connects the concrete compact close/LCA directory to the
interpreter-backed stored-word rank leaf.  The existing seeded close wrapper is
kept unchanged; the rank callback it consumes is now built directly from
`PayloadLiveStoredWordRankData.rankProgramClamped` and the corresponding
payload-only Word-RAM store.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace
open RMQ.WordRAM.Register

namespace ConcreteCompactBPCloseLCADirectory

/-- Interpreted false-rank callback for the BP close seed. -/
def interpretedRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : Costed Nat :=
  (((rankData.rankProgramClamped false pos).eval
    (rankData.rankWordRAMStore false)).toCosted)

theorem interpretedRankCloseCosted_refines_rankCostedClamped
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    interpretedRankCloseCosted rankData pos =
      rankData.rankCostedClamped false pos := by
  exact rankData.rankProgramClamped_refines_rankCostedClamped false pos

theorem interpretedRankCloseCosted_cost_le_three
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (interpretedRankCloseCosted rankData pos).cost <= 3 := by
  rw [interpretedRankCloseCosted_refines_rankCostedClamped
    (rankData := rankData) (pos := pos)]
  exact rankData.rankCostedClamped_cost_le_three false pos

theorem interpretedRankCloseCosted_exact
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (interpretedRankCloseCosted rankData pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  rw [interpretedRankCloseCosted_refines_rankCostedClamped
    (rankData := rankData) (pos := pos)]
  exact rankData.rankCostedClamped_exact false pos

/--
Register-interpreted false-rank callback for the BP close seed.

Unlike `interpretedRankCloseCosted`, the queried position is read from a
natural register before the sample and bit-word addresses are computed.
-/
def registerRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) : Costed Nat :=
  (((rankData.rankRegProgram false (NatExpr.reg 0)).eval
    (rankData.rankWordRAMStore false)
    (RegFile.withNat1 pos)).toCosted)

theorem registerRankCloseCosted_refines_interpretedRankCloseCosted
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    registerRankCloseCosted rankData pos =
      interpretedRankCloseCosted rankData pos := by
  unfold registerRankCloseCosted interpretedRankCloseCosted
  exact
    rankData.rankRegProgram_refines_rankProgramClamped false
      (NatExpr.reg 0) (RegFile.withNat1 pos)

theorem registerRankCloseCosted_cost_le_three
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseCosted rankData pos).cost <= 3 := by
  rw [registerRankCloseCosted_refines_interpretedRankCloseCosted
    (rankData := rankData) (pos := pos)]
  exact interpretedRankCloseCosted_cost_le_three
    (rankData := rankData) (pos := pos)

theorem registerRankCloseCosted_exact
    {shape : Cartesian.CartesianShape} {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (pos : Nat) :
    (registerRankCloseCosted rankData pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  rw [registerRankCloseCosted_refines_interpretedRankCloseCosted
    (rankData := rankData) (pos := pos)]
  exact interpretedRankCloseCosted_exact
    (rankData := rankData) (pos := pos)

/-- Compact close/LCA query using the interpreted false-rank seed callback. -/
def lcaCloseCostedWithInterpretedRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  directory.lcaCloseCostedWithRankSeed
    (fun pos => interpretedRankCloseCosted rankData pos)
    leftClose rightClose

theorem lcaCloseCostedWithInterpretedRankSeed_refines_lcaCloseCostedWithRankSeed
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) :
    directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose =
      directory.lcaCloseCostedWithRankSeed
        (fun pos => rankData.rankCostedClamped false pos)
        leftClose rightClose := by
  have hfun :
      (fun pos => interpretedRankCloseCosted rankData pos) =
        (fun pos => rankData.rankCostedClamped false pos) := by
    funext pos
    exact interpretedRankCloseCosted_refines_rankCostedClamped
      (rankData := rankData) (pos := pos)
  simp [lcaCloseCostedWithInterpretedRankSeed, hfun]

theorem lcaCloseCostedWithInterpretedRankSeed_cost_le
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).cost <=
      concreteCompactBPCloseQueryCostWithRankSeed 3 := by
  unfold lcaCloseCostedWithInterpretedRankSeed
  exact
    directory.lcaCloseCostedWithRankSeed_cost_le
      (fun pos => interpretedRankCloseCosted rankData pos)
      leftClose rightClose 3
      (by
        intro pos
        exact interpretedRankCloseCosted_cost_le_three
          (rankData := rankData) (pos := pos))

theorem lcaCloseCostedWithInterpretedRankSeed_exact_of_query
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).erase =
      some answerClose := by
  unfold lcaCloseCostedWithInterpretedRankSeed
  exact
    directory.lcaCloseCostedWithRankSeed_exact_of_query
      (fun pos => interpretedRankCloseCosted rankData pos)
      (by
        intro pos
        exact interpretedRankCloseCosted_exact
          (rankData := rankData) (pos := pos))
      hlen hbound hleft hright hanswer

theorem lcaCloseCostedWithInterpretedRankSeed_profile
    {shape : Cartesian.CartesianShape}
    (directory : ConcreteCompactBPCloseLCADirectory shape)
    {rankOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead) :
    (forall leftClose rightClose,
      (directory.lcaCloseCostedWithInterpretedRankSeed rankData leftClose
        rightClose).cost <=
          concreteCompactBPCloseQueryCostWithRankSeed 3) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCostedWithInterpretedRankSeed rankData
                    leftClose rightClose).erase =
                    some answerClose) := by
  constructor
  next =>
    intro leftClose rightClose
    exact directory.lcaCloseCostedWithInterpretedRankSeed_cost_le
      rankData leftClose rightClose
  next =>
    intro left len leftClose rightClose answerClose hlen hbound hleft hright
      hanswer
    exact directory.lcaCloseCostedWithInterpretedRankSeed_exact_of_query
      rankData hlen hbound hleft hright hanswer

end ConcreteCompactBPCloseLCADirectory

end SuccinctClose
end RMQ
