import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerInteriorProtocol

/-!
# First-order close/LCA protocol

This file composes the rank seed, four-word BP windows, charged fringe folds,
and the defunctionalized segment-20 interior protocol into the exact same-block
and cross-block branches of `packedLcaCloseLeaf`.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

inductive PackedReviewerLcaState where
  | sameSeed
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose : Nat) (rank : PackedReviewerRankState)
  | sameWindow
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose seed : Nat)
      (window : PackedReviewerBPWindowState)
  | sameFringe
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose seed base start : Nat)
      (fringe : PackedReviewerFringeState)
  | leftSeed
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose : Nat) (rank : PackedReviewerRankState)
  | leftWindow
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose seed : Nat)
      (window : PackedReviewerBPWindowState)
  | leftFringe
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose seed base start : Nat)
      (fringe : PackedReviewerFringeState)
  | middle
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose : Nat)
      (left : PackedReviewerCandidate)
      (interior : PackedReviewerInteriorState)
  | rightSeed
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose : Nat)
      (left middle : PackedReviewerCandidate)
      (rank : PackedReviewerRankState)
  | rightWindow
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose seed : Nat)
      (left middle : PackedReviewerCandidate)
      (window : PackedReviewerBPWindowState)
  | rightFringe
      (invocation : PackedReviewerInvocation)
      (n leftClose rightClose seed base start : Nat)
      (left middle : PackedReviewerCandidate)
      (fringe : PackedReviewerFringeState)
  | done (value : Option Nat)

def packedReviewerLcaRankStart
    (invocation : PackedReviewerInvocation) (n pos : Nat) :
    PackedReviewerRankState :=
  .superSample invocation .close n pos

def packedReviewerLcaStart
    (n leftClose rightClose : Nat) : PackedReviewerLcaState :=
  let invocation : PackedReviewerInvocation :=
    { instruction := .lcaClose
      argument := leftClose
      argument2 := rightClose }
  let blockSize := packedSummaryBlockSizeRaw n
  let seedPos := packedLocalBPWindowBase n blockSize leftClose
  if SuccinctClose.blockOfClose blockSize leftClose =
      SuccinctClose.blockOfClose blockSize rightClose then
    .sameSeed invocation n leftClose rightClose
      (packedReviewerLcaRankStart invocation n seedPos)
  else
    .leftSeed invocation n leftClose rightClose
      (packedReviewerLcaRankStart invocation n seedPos)

def packedReviewerLcaNextRequest :
    PackedReviewerLcaState -> Option PackedReviewerLogicalRequest
  | .sameSeed _ _ _ _ rank => packedReviewerRankNextRequest rank
  | .sameWindow _ _ _ _ _ window => packedReviewerBPWindowNextRequest window
  | .sameFringe _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeNextRequest fringe
  | .leftSeed _ _ _ _ rank => packedReviewerRankNextRequest rank
  | .leftWindow _ _ _ _ _ window => packedReviewerBPWindowNextRequest window
  | .leftFringe _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeNextRequest fringe
  | .middle _ _ _ _ _ interior => packedReviewerInteriorNextRequest interior
  | .rightSeed _ _ _ _ _ _ rank => packedReviewerRankNextRequest rank
  | .rightWindow _ _ _ _ _ _ _ window =>
      packedReviewerBPWindowNextRequest window
  | .rightFringe _ _ _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeNextRequest fringe
  | .done _ => none

def packedReviewerLcaSeed
    (n blockSize close rankFalse : Nat) : Nat :=
  SuccinctClose.localBPSeedFromRankFalse
    (packedLocalBPWindowBase n blockSize close) rankFalse

def packedReviewerLcaStartSameWindow
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose rankFalse : Nat) : PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let seed := packedReviewerLcaSeed n blockSize leftClose rankFalse
  .sameWindow invocation n leftClose rightClose seed
    (packedReviewerBPWindowStart invocation n blockSize leftClose)

def packedReviewerLcaStartSameFringe
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose seed : Nat) (window : List Bool) :
    PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let base := packedLocalBPWindowBase n blockSize leftClose
  let start := leftClose + 1
  let relLo := start - base
  let relHi :=
    leftClose + 1 + (rightClose - leftClose + 1) - 1 - base
  let count :=
    Nat.min (relHi / packedFringeChunkBits n + 1) 33
  .sameFringe invocation n leftClose rightClose seed base start
    (packedReviewerFringeStart invocation n window seed relLo relHi count)

def packedReviewerLcaFinishSameFringe
    (base seed start : Nat) (fold : Nat × Option (Nat × Nat)) :
    Option Nat :=
  SuccinctClose.bpCandidateClose?
    (SuccinctClose.bpFringeCandGlobal base seed start fold.2)

def packedReviewerLcaStartLeftWindow
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose rankFalse : Nat) : PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let seed := packedReviewerLcaSeed n blockSize leftClose rankFalse
  .leftWindow invocation n leftClose rightClose seed
    (packedReviewerBPWindowStart invocation n blockSize leftClose)

def packedReviewerLcaStartLeftFringe
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose seed : Nat) (window : List Bool) :
    PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let base := packedLocalBPWindowBase n blockSize leftClose
  let start := leftClose + 1
  let span :=
    SuccinctClose.blockStartOf blockSize
        (SuccinctClose.blockOfClose blockSize leftClose) +
      blockSize - leftClose
  let relLo := start - base
  let relHi := start + span - 1 - base
  let count := Nat.min (relHi / packedFringeChunkBits n + 1) 33
  .leftFringe invocation n leftClose rightClose seed base start
    (packedReviewerFringeStart invocation n window seed relLo relHi count)

def packedReviewerLcaStartRightSeed
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose : Nat)
    (left middle : PackedReviewerCandidate) : PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let seedPos := packedLocalBPWindowBase n blockSize rightClose
  .rightSeed invocation n leftClose rightClose left middle
    (packedReviewerLcaRankStart invocation n seedPos)

def packedReviewerLcaStartMiddle
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose : Nat) (left : PackedReviewerCandidate) :
    PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
  let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
  if leftBlock + 1 < rightBlock then
    let interior :=
      packedReviewerInteriorStart invocation n (leftBlock + 1)
        (rightBlock - leftBlock - 1)
    match packedReviewerInteriorResult interior with
    | some middle =>
        packedReviewerLcaStartRightSeed invocation n leftClose rightClose left
          middle
    | none => .middle invocation n leftClose rightClose left interior
  else
    packedReviewerLcaStartRightSeed invocation n leftClose rightClose left none

def packedReviewerLcaStartRightWindow
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose rankFalse : Nat)
    (left middle : PackedReviewerCandidate) : PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let seed := packedReviewerLcaSeed n blockSize rightClose rankFalse
  .rightWindow invocation n leftClose rightClose seed left middle
    (packedReviewerBPWindowStart invocation n blockSize rightClose)

def packedReviewerLcaStartRightFringe
    (invocation : PackedReviewerInvocation)
    (n leftClose rightClose seed : Nat)
    (left middle : PackedReviewerCandidate) (window : List Bool) :
    PackedReviewerLcaState :=
  let blockSize := packedSummaryBlockSizeRaw n
  let base := packedLocalBPWindowBase n blockSize rightClose
  let start :=
    SuccinctClose.blockStartOf blockSize
      (SuccinctClose.blockOfClose blockSize rightClose)
  let span := rightClose - start + 2
  let relLo := start - base
  let relHi := start + span - 1 - base
  let count := Nat.min (relHi / packedFringeChunkBits n + 1) 33
  .rightFringe invocation n leftClose rightClose seed base start left middle
    (packedReviewerFringeStart invocation n window seed relLo relHi count)

def packedReviewerLcaConsumeReply
    (state : PackedReviewerLcaState) (reply : Option (List Bool)) :
    PackedReviewerLcaState :=
  match state with
  | .sameSeed invocation n leftClose rightClose rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some rankFalse =>
          packedReviewerLcaStartSameWindow invocation n leftClose rightClose
            rankFalse
      | none => .sameSeed invocation n leftClose rightClose rank'
  | .sameWindow invocation n leftClose rightClose seed window =>
      let window' := packedReviewerBPWindowConsumeReply window reply
      match packedReviewerBPWindowResult window' with
      | some bits =>
          packedReviewerLcaStartSameFringe invocation n leftClose rightClose
            seed bits
      | none => .sameWindow invocation n leftClose rightClose seed window'
  | .sameFringe invocation n leftClose rightClose seed base start fringe =>
      let fringe' := packedReviewerFringeConsumeReply fringe reply
      match packedReviewerFringeResult fringe' with
      | some fold =>
          .done (packedReviewerLcaFinishSameFringe base seed start fold)
      | none =>
          .sameFringe invocation n leftClose rightClose seed base start fringe'
  | .leftSeed invocation n leftClose rightClose rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some rankFalse =>
          packedReviewerLcaStartLeftWindow invocation n leftClose rightClose
            rankFalse
      | none => .leftSeed invocation n leftClose rightClose rank'
  | .leftWindow invocation n leftClose rightClose seed window =>
      let window' := packedReviewerBPWindowConsumeReply window reply
      match packedReviewerBPWindowResult window' with
      | some bits =>
          packedReviewerLcaStartLeftFringe invocation n leftClose rightClose
            seed bits
      | none => .leftWindow invocation n leftClose rightClose seed window'
  | .leftFringe invocation n leftClose rightClose seed base start fringe =>
      let fringe' := packedReviewerFringeConsumeReply fringe reply
      match packedReviewerFringeResult fringe' with
      | some fold =>
          let left :=
            SuccinctClose.bpFringeCandGlobal base seed start fold.2
          packedReviewerLcaStartMiddle invocation n leftClose rightClose left
      | none =>
          .leftFringe invocation n leftClose rightClose seed base start fringe'
  | .middle invocation n leftClose rightClose left interior =>
      let interior' := packedReviewerInteriorConsumeReply interior reply
      match packedReviewerInteriorResult interior' with
      | some middle =>
          packedReviewerLcaStartRightSeed invocation n leftClose rightClose left
            middle
      | none => .middle invocation n leftClose rightClose left interior'
  | .rightSeed invocation n leftClose rightClose left middle rank =>
      let rank' := packedReviewerRankConsumeReply rank reply
      match packedReviewerRankResult rank' with
      | some rankFalse =>
          packedReviewerLcaStartRightWindow invocation n leftClose rightClose
            rankFalse left middle
      | none =>
          .rightSeed invocation n leftClose rightClose left middle rank'
  | .rightWindow invocation n leftClose rightClose seed left middle window =>
      let window' := packedReviewerBPWindowConsumeReply window reply
      match packedReviewerBPWindowResult window' with
      | some bits =>
          packedReviewerLcaStartRightFringe invocation n leftClose rightClose
            seed left middle bits
      | none =>
          .rightWindow invocation n leftClose rightClose seed left middle
            window'
  | .rightFringe invocation n leftClose rightClose seed base start left middle
        fringe =>
      let fringe' := packedReviewerFringeConsumeReply fringe reply
      match packedReviewerFringeResult fringe' with
      | some fold =>
          let right :=
            SuccinctClose.bpFringeCandGlobal base seed start fold.2
          .done
            (SuccinctClose.bpCandidateClose?
              (SuccinctClose.bpCandidateMerge3? left middle right))
      | none =>
          .rightFringe invocation n leftClose rightClose seed base start left
            middle fringe'
  | .done value => .done value

def packedReviewerLcaResult : PackedReviewerLcaState -> Option (Option Nat)
  | .done value => some value
  | _ => none

/--
Structural remaining-read budget for close/LCA.  Same-block states are bounded
by `48`; cross-block states by `129`.
-/
def packedReviewerLcaRemaining : PackedReviewerLcaState -> Nat
  | .sameSeed _ _ _ _ rank => packedReviewerRankRemaining rank + 37
  | .sameWindow _ _ _ _ _ window =>
      packedReviewerBPWindowRemaining window + 33
  | .sameFringe _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeRemaining fringe
  | .leftSeed _ _ _ _ rank => packedReviewerRankRemaining rank + 118
  | .leftWindow _ _ _ _ _ window =>
      packedReviewerBPWindowRemaining window + 114
  | .leftFringe _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeRemaining fringe + 81
  | .middle _ _ _ _ _ interior =>
      packedReviewerInteriorRemaining interior + 48
  | .rightSeed _ _ _ _ _ _ rank => packedReviewerRankRemaining rank + 37
  | .rightWindow _ _ _ _ _ _ _ window =>
      packedReviewerBPWindowRemaining window + 33
  | .rightFringe _ _ _ _ _ _ _ _ _ fringe =>
      packedReviewerFringeRemaining fringe
  | .done _ => 0

end PackedCellProbe
end SuccinctFinal
end RMQ
