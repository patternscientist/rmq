import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerLogicalProtocol

/-!
# First-order interior range-min protocol

This is the request/reply form of the table-free computations in
`ReadProgram.lean`.  Continuations are a closed inductive family rather than
Lean functions.  The only reads issued are segment-20 machine words.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

abbrev PackedReviewerCandidate := Option (Nat × Nat)

/-- Defunctionalized continuations for candidate-producing subcomputations. -/
inductive PackedReviewerCandidateContinuation where
  | finish
  | localTwoLeft
      (n macroIdx localStart count encoded : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | localTwoRight
      (left : PackedReviewerCandidate)
      (outer : PackedReviewerCandidateContinuation)
  | globalTwoLeft
      (n macroStart macroSpanCount encoded : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | globalTwoRight
      (left : PackedReviewerCandidate)
      (outer : PackedReviewerCandidateContinuation)
  | adjacentLeft
      (n macroStart rightCount : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | adjacentRight
      (left : PackedReviewerCandidate)
      (outer : PackedReviewerCandidateContinuation)
  | leftMiddleLeft
      (n macroStart middleCount : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | leftMiddleMiddle
      (left : PackedReviewerCandidate)
      (outer : PackedReviewerCandidateContinuation)
  | crossLeft
      (n macroStart middleCount rightCount : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | crossMiddle
      (n macroStart middleCount rightCount : Nat)
      (left : PackedReviewerCandidate)
      (outer : PackedReviewerCandidateContinuation)
  | crossRight
      (left middle : PackedReviewerCandidate)
      (outer : PackedReviewerCandidateContinuation)

/-- Defunctionalized continuations for one decoded interior table cell. -/
inductive PackedReviewerInteriorNatContinuation where
  | summaryBaseline
      (n block : Nat) (outer : PackedReviewerCandidateContinuation)
  | summaryMin
      (n block : Nat) (baseline : Option Nat)
      (outer : PackedReviewerCandidateContinuation)
  | summaryMax
      (n block : Nat) (baseline minRel : Option Nat)
      (outer : PackedReviewerCandidateContinuation)
  | summaryArg
      (n block : Nat) (baseline minRel maxRel : Option Nat)
      (outer : PackedReviewerCandidateContinuation)
  | localOffset
      (n macroIdx localStart level : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | globalBlock
      (n macroStart level : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | localLevel
      (n macroIdx localStart count : Nat)
      (outer : PackedReviewerCandidateContinuation)
  | globalLevel
      (n macroStart macroSpanCount : Nat)
      (outer : PackedReviewerCandidateContinuation)

/-- One active interior cell read or a terminal candidate. -/
inductive PackedReviewerInteriorState where
  | readNat
      (invocation : PackedReviewerInvocation)
      (read : PackedReviewerInteriorNatState)
      (continuation : PackedReviewerInteriorNatContinuation)
  | done (value : PackedReviewerCandidate)

def packedReviewerInteriorReadNat
    (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat)
    (continuation : PackedReviewerInteriorNatContinuation) :
    PackedReviewerInteriorState :=
  .readNat
    invocation
    (packedReviewerInteriorNatStart invocation n entryCount width base index)
    continuation

def packedReviewerInteriorStartMinCandidate
    (invocation : PackedReviewerInvocation) (n block : Nat)
    (outer : PackedReviewerCandidateContinuation) :
    PackedReviewerInteriorState :=
  packedReviewerInteriorReadNat invocation n
    (packedInteriorLayout n).superSampleCount (packedBpCodeWordWidth n)
    (packedInteriorOffsets n).baseline
    (block / (packedInteriorLayout n).blocksPerSuper)
    (.summaryBaseline n block outer)

def packedReviewerInteriorStartLocalSpan
    (invocation : PackedReviewerInvocation)
    (n macroIdx localStart level : Nat)
    (outer : PackedReviewerCandidateContinuation) :
    PackedReviewerInteriorState :=
  packedReviewerInteriorReadNat invocation n
    ((packedInteriorLayout n).macroSampleCount *
      ((packedInteriorLayout n).levelCount *
        (packedInteriorLayout n).macroSize))
    (packedInteriorLayout n).offsetWidth
    (packedInteriorOffsets n).localOffset
    (SuccinctClose.bpLocalSparseCellSlot
      (packedInteriorLayout n).macroSize (packedInteriorLayout n).levelCount
      macroIdx localStart level)
    (.localOffset n macroIdx localStart level outer)

def packedReviewerInteriorStartGlobalSpan
    (invocation : PackedReviewerInvocation)
    (n macroStart level : Nat)
    (outer : PackedReviewerCandidateContinuation) :
    PackedReviewerInteriorState :=
  packedReviewerInteriorReadNat invocation n
    ((packedInteriorLayout n).globalLevelCount *
      (packedInteriorLayout n).macroSampleCount)
    (packedInteriorLayout n).blockAddressWidth
    (packedInteriorOffsets n).globalBlock
    (SuccinctClose.bpGlobalSparseCellSlot
      (packedInteriorLayout n).macroSampleCount macroStart level)
    (.globalBlock n macroStart level outer)

def packedReviewerInteriorStartLocalTwo
    (invocation : PackedReviewerInvocation)
    (n macroIdx localStart count : Nat)
    (outer : PackedReviewerCandidateContinuation) :
    PackedReviewerInteriorState :=
  let domain :=
    SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize
  packedReviewerInteriorReadNat invocation n domain
    (SuccinctClose.bpSparseLevelWidth domain)
    (packedInteriorOffsets n).localLevel count
    (.localLevel n macroIdx localStart count outer)

def packedReviewerInteriorStartGlobalTwo
    (invocation : PackedReviewerInvocation)
    (n macroStart macroSpanCount : Nat)
    (outer : PackedReviewerCandidateContinuation) :
    PackedReviewerInteriorState :=
  let domain :=
    SuccinctClose.bpSparseLevelDomain
      (packedInteriorLayout n).macroSampleCount
  packedReviewerInteriorReadNat invocation n domain
    (SuccinctClose.bpSparseLevelWidth domain)
    (packedInteriorOffsets n).globalLevel macroSpanCount
    (.globalLevel n macroStart macroSpanCount outer)

def packedReviewerInteriorFinishCandidate
    (invocation : PackedReviewerInvocation)
    (value : PackedReviewerCandidate) :
    PackedReviewerCandidateContinuation -> PackedReviewerInteriorState
  | .finish => .done value
  | .localTwoLeft n macroIdx localStart count encoded outer =>
      let domain :=
        SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize
      packedReviewerInteriorStartLocalSpan invocation n macroIdx
        (localStart + count - encoded % domain) (encoded / domain)
        (.localTwoRight value outer)
  | .localTwoRight left outer =>
      packedReviewerInteriorFinishCandidate invocation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .globalTwoLeft n macroStart macroSpanCount encoded outer =>
      let domain :=
        SuccinctClose.bpSparseLevelDomain
          (packedInteriorLayout n).macroSampleCount
      packedReviewerInteriorStartGlobalSpan invocation n
        (macroStart + macroSpanCount - encoded % domain) (encoded / domain)
        (.globalTwoRight value outer)
  | .globalTwoRight left outer =>
      packedReviewerInteriorFinishCandidate invocation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .adjacentLeft n macroStart rightCount outer =>
      packedReviewerInteriorStartLocalTwo invocation n (macroStart + 1) 0
        rightCount (.adjacentRight value outer)
  | .adjacentRight left outer =>
      packedReviewerInteriorFinishCandidate invocation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .leftMiddleLeft n macroStart middleCount outer =>
      packedReviewerInteriorStartGlobalTwo invocation n (macroStart + 1)
        middleCount (.leftMiddleMiddle value outer)
  | .leftMiddleMiddle left outer =>
      packedReviewerInteriorFinishCandidate invocation
        (SuccinctClose.bpCandidateMerge? left value) outer
  | .crossLeft n macroStart middleCount rightCount outer =>
      packedReviewerInteriorStartGlobalTwo invocation n (macroStart + 1)
        middleCount
        (.crossMiddle n macroStart middleCount rightCount value outer)
  | .crossMiddle n macroStart middleCount rightCount left outer =>
      packedReviewerInteriorStartLocalTwo invocation n
        (macroStart + 1 + middleCount) 0 rightCount
        (.crossRight left value outer)
  | .crossRight left middle outer =>
      packedReviewerInteriorFinishCandidate invocation
        (SuccinctClose.bpCandidateMerge3? left middle value) outer
termination_by continuation => continuation

def packedReviewerInteriorFinishNat
    (invocation : PackedReviewerInvocation) (value : Option Nat) :
    PackedReviewerInteriorNatContinuation -> PackedReviewerInteriorState
  | .summaryBaseline n block outer =>
      packedReviewerInteriorReadNat invocation n
        (packedInteriorLayout n).blockCount
        (packedInteriorLayout n).relativeWidth
        (packedInteriorOffsets n).minRel block
        (.summaryMin n block value outer)
  | .summaryMin n block baseline outer =>
      packedReviewerInteriorReadNat invocation n
        (packedInteriorLayout n).blockCount
        (packedInteriorLayout n).relativeWidth
        (packedInteriorOffsets n).maxRel block
        (.summaryMax n block baseline value outer)
  | .summaryMax n block baseline minRel outer =>
      packedReviewerInteriorReadNat invocation n
        (packedInteriorLayout n).blockCount
        (packedInteriorLayout n).relativeWidth
        (packedInteriorOffsets n).argOffset block
        (.summaryArg n block baseline minRel value outer)
  | .summaryArg n block baseline minRel maxRel outer =>
      let summary : Option (Nat × Nat × Nat × Nat) :=
        match baseline, minRel, maxRel, value with
        | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
        | _, _, _, _ => none
      packedReviewerInteriorFinishCandidate invocation
        (summary.map
          (SuccinctClose.bpRelativeSummaryMinCandidate
            (packedInteriorLayout n).blockSize
            (packedInteriorLayout n).blocksPerSuper block)) outer
  | .localOffset n macroIdx _ _ outer =>
      match value with
      | some offset =>
          packedReviewerInteriorStartMinCandidate invocation n
            (macroIdx * (packedInteriorLayout n).macroSize + offset) outer
      | none => packedReviewerInteriorFinishCandidate invocation none outer
  | .globalBlock n _ _ outer =>
      match value with
      | some block =>
          packedReviewerInteriorStartMinCandidate invocation n block outer
      | none => packedReviewerInteriorFinishCandidate invocation none outer
  | .localLevel n macroIdx localStart count outer =>
      match value with
      | none => packedReviewerInteriorFinishCandidate invocation none outer
      | some encoded =>
          let domain :=
            SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize
          packedReviewerInteriorStartLocalSpan invocation n macroIdx localStart
            (encoded / domain)
            (.localTwoLeft n macroIdx localStart count encoded outer)
  | .globalLevel n macroStart macroSpanCount outer =>
      match value with
      | none => packedReviewerInteriorFinishCandidate invocation none outer
      | some encoded =>
          let domain :=
            SuccinctClose.bpSparseLevelDomain
              (packedInteriorLayout n).macroSampleCount
          packedReviewerInteriorStartGlobalSpan invocation n macroStart
            (encoded / domain)
            (.globalTwoLeft n macroStart macroSpanCount encoded outer)

def packedReviewerInteriorStartRaw
    (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) : PackedReviewerInteriorState :=
  let layout := packedInteriorLayout n
  if count = 0 then
    .done none
  else if count <= layout.macroSize - startBlock % layout.macroSize then
    packedReviewerInteriorStartLocalTwo invocation n
      (startBlock / layout.macroSize) (startBlock % layout.macroSize) count
      .finish
  else
    let firstCount := layout.macroSize - startBlock % layout.macroSize
    let rest := count - firstCount
    let middleCount := rest / layout.macroSize
    let rightCount := rest % layout.macroSize
    if middleCount = 0 then
      packedReviewerInteriorStartLocalTwo invocation n
        (startBlock / layout.macroSize) (startBlock % layout.macroSize)
        firstCount
        (.adjacentLeft n (startBlock / layout.macroSize) rightCount .finish)
    else if rightCount = 0 then
      packedReviewerInteriorStartLocalTwo invocation n
        (startBlock / layout.macroSize) (startBlock % layout.macroSize)
        firstCount
        (.leftMiddleLeft n (startBlock / layout.macroSize) middleCount .finish)
    else
      packedReviewerInteriorStartLocalTwo invocation n
        (startBlock / layout.macroSize) (startBlock % layout.macroSize)
        firstCount
        (.crossLeft n (startBlock / layout.macroSize) middleCount rightCount
          .finish)

def packedReviewerCandidateContinuationRemaining :
    PackedReviewerCandidateContinuation -> Nat
  | .finish => 0
  | .localTwoLeft _ _ _ _ _ outer =>
      5 + packedReviewerCandidateContinuationRemaining outer
  | .localTwoRight _ outer =>
      packedReviewerCandidateContinuationRemaining outer
  | .globalTwoLeft _ _ _ _ outer =>
      5 + packedReviewerCandidateContinuationRemaining outer
  | .globalTwoRight _ outer =>
      packedReviewerCandidateContinuationRemaining outer
  | .adjacentLeft _ _ _ outer =>
      11 + packedReviewerCandidateContinuationRemaining outer
  | .adjacentRight _ outer =>
      packedReviewerCandidateContinuationRemaining outer
  | .leftMiddleLeft _ _ _ outer =>
      11 + packedReviewerCandidateContinuationRemaining outer
  | .leftMiddleMiddle _ outer =>
      packedReviewerCandidateContinuationRemaining outer
  | .crossLeft _ _ _ _ outer =>
      22 + packedReviewerCandidateContinuationRemaining outer
  | .crossMiddle _ _ _ _ _ outer =>
      11 + packedReviewerCandidateContinuationRemaining outer
  | .crossRight _ _ outer =>
      packedReviewerCandidateContinuationRemaining outer

def packedReviewerInteriorNatContinuationRemaining :
    PackedReviewerInteriorNatContinuation -> Nat
  | .summaryBaseline _ _ outer =>
      3 + packedReviewerCandidateContinuationRemaining outer
  | .summaryMin _ _ _ outer =>
      2 + packedReviewerCandidateContinuationRemaining outer
  | .summaryMax _ _ _ _ outer =>
      1 + packedReviewerCandidateContinuationRemaining outer
  | .summaryArg _ _ _ _ _ outer =>
      packedReviewerCandidateContinuationRemaining outer
  | .localOffset _ _ _ _ outer =>
      4 + packedReviewerCandidateContinuationRemaining outer
  | .globalBlock _ _ _ outer =>
      4 + packedReviewerCandidateContinuationRemaining outer
  | .localLevel _ _ _ _ outer =>
      10 + packedReviewerCandidateContinuationRemaining outer
  | .globalLevel _ _ _ outer =>
      10 + packedReviewerCandidateContinuationRemaining outer

/--
Structural remaining measure used by the protocol.  Adequacy and the fixed
whole-run `<= 33` bound are proved only for canonically reachable invocations;
arbitrary forged state parameters carry no such claim here.
-/
def packedReviewerInteriorRemaining : PackedReviewerInteriorState -> Nat
  | .readNat _ read continuation =>
      packedReviewerInteriorNatRemaining read +
        packedReviewerInteriorNatContinuationRemaining continuation
  | .done _ => 0

/--
Consume proof-free child completions before exposing an interior state.  The
fuel is a structural bound derived from the same continuation measure as the
logical-read budget; normalization performs no memory read.
-/
def packedReviewerInteriorNormalize : Nat -> PackedReviewerInteriorState ->
    PackedReviewerInteriorState
  | 0, state => state
  | _fuel + 1, .done value => .done value
  | fuel + 1, .readNat invocation read continuation =>
      match packedReviewerInteriorNatResult read with
      | none => .readNat invocation read continuation
      | some value =>
          let next := packedReviewerInteriorFinishNat invocation value continuation
          packedReviewerInteriorNormalize fuel next

/-- Public smart constructor: every reachable child is active or fully done. -/
def packedReviewerInteriorStart
    (invocation : PackedReviewerInvocation)
    (n startBlock count : Nat) : PackedReviewerInteriorState :=
  let state := packedReviewerInteriorStartRaw invocation n startBlock count
  packedReviewerInteriorNormalize (packedReviewerInteriorRemaining state + 1)
    state

def packedReviewerInteriorNextRequest :
    PackedReviewerInteriorState -> Option PackedReviewerLogicalRequest
  | .readNat _ read _ => packedReviewerInteriorNatNextRequest read
  | .done _ => none

def packedReviewerInteriorConsumeReply
    (state : PackedReviewerInteriorState) (reply : Option (List Bool)) :
    PackedReviewerInteriorState :=
  match state with
  | .readNat invocation read continuation =>
      let read' := packedReviewerInteriorNatConsumeReply read reply
      match packedReviewerInteriorNatResult read' with
      | some value =>
          let next := packedReviewerInteriorFinishNat invocation value continuation
          packedReviewerInteriorNormalize
            (packedReviewerInteriorRemaining next + 1) next
      | none => .readNat invocation read' continuation
  | .done value => .done value

def packedReviewerInteriorResult :
    PackedReviewerInteriorState -> Option PackedReviewerCandidate
  | .done value => some value
  | _ => none

end PackedCellProbe
end SuccinctFinal
end RMQ
