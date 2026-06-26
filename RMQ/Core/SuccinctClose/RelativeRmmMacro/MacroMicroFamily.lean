import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectory

/-!
# Macro/micro close-navigation families

Split implementation layer for the relative-rmM BP close/LCA macro. Public
declarations live in the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

/--
Guarded macro/micro close directory using a relative-rmM cross-block macro.

This is the positive C2 query surface that avoids dense interior block-pair
payloads.  Same-block queries use the existing payload-live micro codebook;
cross-block queries use the relative-rmM macro component.
-/
structure PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroComponent :
    PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
      relativeOverhead middleQueryCost
  blockSize_pos : 0 < blockSize
  close_block_lt :
    forall {close : Nat},
      close < shape.bpCode.length ->
        blockOfClose blockSize close < blockCount

namespace PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost) : List Bool :=
  directory.micro.payload ++ directory.macroComponent.payload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    directory.micro.lcaCloseCosted leftClose rightClose
  else
    directory.macroComponent.lcaCloseCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead + relativeOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroComponent.payload_length]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      4 + middleQueryCost := by
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    have hmicro := directory.micro.lcaCloseCosted_cost_le_two
      leftClose rightClose
    omega
  · simp [hsame]
    exact directory.macroComponent.lcaCloseCosted_cost_le
      leftClose rightClose

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
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
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hleftBlock :
      blockOfClose blockSize leftClose < blockCount :=
    directory.close_block_lt hleftCloseBound
  have hrightBlock :
      blockOfClose blockSize rightClose < blockCount :=
    directory.close_block_lt hrightCloseBound
  have hbetween :=
    answerClose_between_endpoint_closes
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    rcases directory.micro.classifier.codeAt_exists_of_lt hleftBlock with
      ⟨code, hcodeAt⟩
    have hrightLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          rightClose := by
      simpa [hsame] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose))
    have hrightHi :
        rightClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      simpa [hsame] using
        (close_lt_blockStartOf_blockOfClose_add
          (blockSize := blockSize) (close := rightClose)
          directory.blockSize_pos)
    have hanswerLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          answerClose := by
      exact Nat.le_trans blockStartOf_blockOfClose_le hbetween.1
    have hanswerHi :
        answerClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      exact Nat.lt_of_le_of_lt hbetween.2 hrightHi
    exact
      directory.micro.lcaCloseCosted_exact_of_left_block
        directory.blockSize_pos hcodeAt hlen hbound hleft hright hanswer
        hrightLo hrightHi hanswerLo hanswerHi
  · simp [hsame]
    have hleftRight : leftClose <= rightClose := by
      omega
    have hblockLe :
        blockOfClose blockSize leftClose <=
          blockOfClose blockSize rightClose := by
      unfold blockOfClose
      exact Nat.div_le_div_right hleftRight
    have hcross :
        blockOfClose blockSize leftClose <
          blockOfClose blockSize rightClose := by
      omega
    exact
      directory.macroComponent.lcaCloseCosted_exact_of_query_cross_block
        hlen hbound hleft hright hanswer directory.blockSize_pos
        hleftBlock hrightBlock hcross

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost : Nat}
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead + relativeOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory

def relativeRmmMacroMicroBPCloseLCAOverhead
    (microOverhead relativeOverhead : Nat -> Nat) (n : Nat) : Nat :=
  microOverhead n + relativeOverhead n

theorem relativeRmmMacroMicroBPCloseLCAOverhead_littleO
    {microOverhead relativeOverhead : Nat -> Nat}
    (hmicro : LittleOLinear microOverhead)
    (hrelative : LittleOLinear relativeOverhead) :
    LittleOLinear
      (relativeRmmMacroMicroBPCloseLCAOverhead
        microOverhead relativeOverhead) := by
  unfold relativeRmmMacroMicroBPCloseLCAOverhead
  exact hmicro.add hrelative

theorem relativeRmmMacroMicroBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead relativeOverhead middleQueryCost n : Nat)
    (microBudget relativeBudget : Nat -> Nat)
    (directory :
      PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead relativeOverhead middleQueryCost)
    (hmicroLittle : LittleOLinear microBudget)
    (hrelativeLittle : LittleOLinear relativeBudget)
    (hmicroBudget :
      codeOverhead + codeCount * microTableOverhead <= microBudget n)
    (hrelativeBudget : relativeOverhead <= relativeBudget n) :
    LittleOLinear
        (relativeRmmMacroMicroBPCloseLCAOverhead
          microBudget relativeBudget) /\
      directory.payload.length <=
        relativeRmmMacroMicroBPCloseLCAOverhead
          microBudget relativeBudget n /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose := by
  have hprofile := directory.profile
  constructor
  · exact relativeRmmMacroMicroBPCloseLCAOverhead_littleO
      hmicroLittle hrelativeLittle
  constructor
  · rw [hprofile.1]
    unfold relativeRmmMacroMicroBPCloseLCAOverhead
    omega
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2

/--
Concrete dense fallback instance for the payload-live macro/micro surface.

The micro phase is the charged empty classifier above, and the macro phase is
the dense all-close table.  This construction is exact and constant-cost, but
`denseAllCloseBPCloseLCAOverhead_not_littleO` shows why it is only a blocker
baseline, not the final succinct macro.
-/
def denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize 0 1 0 0 0
      ((shape.bpCode.length * shape.bpCode.length) *
        optionNatWordWidth fieldWidth) 1 where
  micro := emptyPayloadLiveBlockMicroCodebook shape blockSize fieldWidth
  macroPayload :=
    (denseAllCloseBPCloseLCATable shape fieldWidth hwidth).payload
  macroPayload_length_eq := by
    exact
      (denseAllCloseBPCloseLCATable
        shape fieldWidth hwidth).payload_length
  macroCosted :=
    (denseAllCloseBPCloseLCATable shape fieldWidth hwidth).lcaCloseCosted
  macro_cost_le := by
    intro leftClose rightClose
    exact
      (denseAllCloseBPCloseLCATable
        shape fieldWidth hwidth).lcaCloseCosted_cost_le_one
          leftClose rightClose
  split_exact := by
    intro left len leftClose rightClose answerClose
      hlen hbound hleft hright hanswer
    right
    constructor
    · exact
        emptyPayloadLiveBlockMicroCodebook_lcaCloseCosted_erase
          shape blockSize fieldWidth leftClose rightClose
    · exact
        (denseAllCloseBPCloseLCATable_profile
          shape fieldWidth hwidth).2.2 hlen hbound hleft hright hanswer

theorem denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    ((denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
        shape blockSize fieldWidth hwidth).payload.length =
        (shape.bpCode.length * shape.bpCode.length) *
          optionNatWordWidth fieldWidth) /\
      (forall leftClose rightClose,
        ((denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
          shape blockSize fieldWidth hwidth).lcaCloseCosted
            leftClose rightClose).cost <= 3) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  ((denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
                    shape blockSize fieldWidth hwidth).lcaCloseCosted
                      leftClose rightClose).erase =
                    some answerClose := by
  have hprofile :=
    (denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory
      shape blockSize fieldWidth hwidth).profile
  constructor
  · simpa using hprofile.1
  constructor
  · intro leftClose rightClose
    have hcost := hprofile.2.1 leftClose rightClose
    simpa using hcost
  · intro left len leftClose rightClose answerClose
      hlen hbound hleft hright hanswer
    exact hprofile.2.2 hlen hbound hleft hright hanswer

def payloadLiveMacroMicroBPCloseLCAOverhead
    (codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat)
    (n : Nat) : Nat :=
  codeOverhead n + codeCount n * microTableOverhead n + macroOverhead n

theorem payloadLiveMacroMicroBPCloseLCAOverhead_littleO
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    (hcode : LittleOLinear codeOverhead)
    (hcodebook :
      LittleOLinear (fun n => codeCount n * microTableOverhead n))
    (hmacro : LittleOLinear macroOverhead) :
    LittleOLinear
      (payloadLiveMacroMicroBPCloseLCAOverhead
        codeOverhead codeCount microTableOverhead macroOverhead) := by
  unfold payloadLiveMacroMicroBPCloseLCAOverhead
  exact (hcode.add hcodebook).add hmacro

/--
Family-level macro/micro close-LCA interface.

The code classifier overhead, finite codebook overhead, and macro overhead are
separate LittleOLinear obligations.  This avoids proving a final RMQ theorem
from a dense per-block table while still pinning the exact payload read by the
close/LCA primitive.
-/
structure PayloadLiveMacroMicroBPCloseLCAFamily
    (codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat)
    (queryCost : Nat) where
  blockSize : Nat -> Nat
  blockCount : Nat -> Nat
  codeWidth : Nat -> Nat
  macroCost : Nat -> Nat
  directory :
    forall {n : Nat} (shape : Cartesian.CartesianShape),
      List.Mem shape (Cartesian.shapesOfSize n) ->
        PayloadLiveMacroMicroBPCloseLCADirectory shape
          (blockSize n) (blockCount n) (codeCount n) (codeWidth n)
          (codeOverhead n) (microTableOverhead n) (macroOverhead n)
          (macroCost n)
  code_littleO : LittleOLinear codeOverhead
  codebook_littleO :
    LittleOLinear (fun n => codeCount n * microTableOverhead n)
  macro_littleO : LittleOLinear macroOverhead
  macro_cost_le_query : forall n : Nat, 2 + macroCost n <= queryCost

namespace PayloadLiveMacroMicroBPCloseLCAFamily

def overhead
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) : Nat -> Nat :=
  payloadLiveMacroMicroBPCloseLCAOverhead
    codeOverhead codeCount microTableOverhead macroOverhead

theorem overhead_littleO
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) :
    LittleOLinear family.overhead := by
  exact
    payloadLiveMacroMicroBPCloseLCAOverhead_littleO
      family.code_littleO family.codebook_littleO family.macro_littleO

def Profile
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) : Prop :=
  LittleOLinear family.overhead /\
    forall n : Nat,
      forall {shape : Cartesian.CartesianShape},
        (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
          ((family.directory (n := n) shape hshape).payload.length =
              family.overhead n) /\
            (forall leftClose rightClose,
              ((family.directory (n := n) shape hshape).lcaCloseCosted
                    leftClose rightClose).cost <= queryCost) /\
            forall {left len leftClose rightClose answerClose : Nat},
              0 < len ->
                left + len <= shape.size ->
                  bpCloseOfInorder? shape left = some leftClose ->
                    bpCloseOfInorder? shape (left + len - 1) =
                        some rightClose ->
                      bpCloseOfInorder? shape
                          (scanWindow shape.representative left len) =
                        some answerClose ->
                        ((family.directory (n := n) shape hshape).lcaCloseCosted
                              leftClose rightClose).erase =
                          some answerClose

theorem profile
    {codeOverhead codeCount microTableOverhead macroOverhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
        microTableOverhead macroOverhead queryCost) :
    family.Profile := by
  constructor
  · exact family.overhead_littleO
  intro n shape hshape
  let directory := family.directory (n := n) shape hshape
  have hdirProfile := directory.profile
  constructor
  · simpa [directory, overhead,
      payloadLiveMacroMicroBPCloseLCAOverhead] using hdirProfile.1
  constructor
  · intro leftClose rightClose
    have hcost := hdirProfile.2.1 leftClose rightClose
    have hbudget := family.macro_cost_le_query n
    simpa [directory] using Nat.le_trans hcost hbudget
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact hdirProfile.2.2 hlen hbound hleft hright hanswer

end PayloadLiveMacroMicroBPCloseLCAFamily

/--
Overhead for the built-query BP close-navigation join that uses payload-live
rank/select plus the payload-live macro/micro BP close-LCA directory.
-/
def payloadLiveMacroMicroBPCloseNavigationOverhead
    (rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat)
    (n : Nat) : Nat :=
  rankOverhead n + selectOverhead n +
    payloadLiveMacroMicroBPCloseLCAOverhead
      codeOverhead codeCount microTableOverhead macroOverhead n

theorem payloadLiveMacroMicroBPCloseNavigationOverhead_littleO
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    (hrank : LittleOLinear rankOverhead)
    (hselect : LittleOLinear selectOverhead)
    (hlca :
      LittleOLinear
        (payloadLiveMacroMicroBPCloseLCAOverhead
          codeOverhead codeCount microTableOverhead macroOverhead)) :
    LittleOLinear
      (payloadLiveMacroMicroBPCloseNavigationOverhead
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead) := by
  unfold payloadLiveMacroMicroBPCloseNavigationOverhead
  exact (hrank.add hselect).add hlca

/--
Built-query BP close-navigation family using the payload-live macro/micro
close-LCA component.

This is the cost-parametric join layer: select-close and rank-close are the
existing payload-live rank/select reads, while the LCA leg is the
`PayloadLiveMacroMicroBPCloseLCAFamily` with its exposed `lcaQueryCost`.
-/
structure PayloadLiveMacroMicroBPCloseNavigationFamily
    (rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat)
    (lcaQueryCost : Nat) where
  lcaFamily :
    PayloadLiveMacroMicroBPCloseLCAFamily codeOverhead codeCount
      microTableOverhead macroOverhead lcaQueryCost
  rankData :
    forall {n : Nat} (shape : Cartesian.CartesianShape),
      List.Mem shape (Cartesian.shapesOfSize n) ->
        PayloadLiveStoredWordRankData shape.bpCode (rankOverhead n)
  selectData :
    forall {n : Nat} (shape : Cartesian.CartesianShape),
      List.Mem shape (Cartesian.shapesOfSize n) ->
        PayloadLiveStoredWordSelectData shape.bpCode (selectOverhead n)
  rank_littleO : LittleOLinear rankOverhead
  select_littleO : LittleOLinear selectOverhead

namespace PayloadLiveMacroMicroBPCloseNavigationFamily

def overhead
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (_family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) : Nat -> Nat :=
  payloadLiveMacroMicroBPCloseNavigationOverhead
    rankOverhead selectOverhead codeOverhead codeCount
    microTableOverhead macroOverhead

def payload
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) : List Bool :=
  shape.bpCode ++
    (family.rankData shape hshape).auxPayload ++
      (family.selectData shape hshape).auxPayload ++
        (family.lcaFamily.directory (n := n) shape hshape).payload

def selectCloseCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (idx : Nat) : Costed (Option Nat) :=
  (family.selectData shape hshape).selectCosted false idx

def lcaCloseCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (family.lcaFamily.directory (n := n) shape hshape).lcaCloseCosted
    leftClose rightClose

def rankCloseCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (pos : Nat) : Costed Nat :=
  (family.rankData shape hshape).rankCostedClamped false pos

def queryBuiltCosted
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (family.selectCloseCosted shape hshape left) fun leftClose? =>
    Costed.bind
      (family.selectCloseCosted shape hshape (right - 1))
      fun rightClose? =>
        match leftClose?, rightClose? with
        | some leftClose, some rightClose =>
            Costed.bind
              (family.lcaCloseCosted shape hshape leftClose rightClose)
              fun answerClose? =>
                match answerClose? with
                | some answerClose =>
                    Costed.map (fun closeRank => some (closeRank - 1))
                      (family.rankCloseCosted shape hshape (answerClose + 1))
                | none => Costed.pure none
        | _, _ => Costed.pure none

theorem overhead_littleO
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) :
    LittleOLinear family.overhead := by
  exact
    payloadLiveMacroMicroBPCloseNavigationOverhead_littleO
      family.rank_littleO family.select_littleO
      family.lcaFamily.overhead_littleO

theorem payload_length
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (family.payload shape hshape).length =
      2 * n + family.overhead n := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n := by
    exact Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have hrank :
      (family.rankData shape hshape).auxPayload.length =
        rankOverhead n :=
    (family.rankData shape hshape).auxPayload_length
  have hselect :
      (family.selectData shape hshape).auxPayload.length =
        selectOverhead n :=
    (family.selectData shape hshape).auxPayload_length
  have hlca :
      ((family.lcaFamily.directory (n := n) shape hshape).payload.length =
        family.lcaFamily.overhead n) :=
    ((family.lcaFamily.profile).2 n hshape).1
  simp [payload, overhead, PayloadLiveMacroMicroBPCloseLCAFamily.overhead,
    payloadLiveMacroMicroBPCloseNavigationOverhead, hbp, hrank, hselect,
    hlca]
  omega

theorem queryBuiltCosted_cost_le
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (left right : Nat) :
    (family.queryBuiltCosted shape hshape left right).cost <=
      9 + lcaQueryCost := by
  unfold queryBuiltCosted selectCloseCosted lcaCloseCosted rankCloseCosted
  have hleft :=
    (family.selectData shape hshape).selectCosted_cost_le_three false left
  have hright :=
    (family.selectData shape hshape).selectCosted_cost_le_three
      false (right - 1)
  cases hleftValue :
      ((family.selectData shape hshape).selectCosted false left).value with
  | none =>
      simp [Costed.bind, hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          ((family.selectData shape hshape).selectCosted
            false (right - 1)).value with
      | none =>
          simp [Costed.bind, hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            ((family.lcaFamily.profile).2 n hshape).2.1
              leftClose rightClose
          cases hlcaValue :
              ((family.lcaFamily.directory
                (n := n) shape hshape).lcaCloseCosted
                  leftClose rightClose).value with
          | none =>
              simp [Costed.bind, hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                (family.rankData shape hshape).rankCostedClamped_cost_le_three
                  false (answerClose + 1)
              simp [Costed.bind, Costed.map, hleftValue, hrightValue,
                hlcaValue]
              omega

theorem selectCloseCosted_exact
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (idx : Nat) :
    (family.selectCloseCosted shape hshape idx).erase =
      bpCloseOfInorder? shape idx := by
  calc
    (family.selectCloseCosted shape hshape idx).erase =
        Succinct.select false shape.bpCode idx := by
      exact (family.selectData shape hshape).selectCosted_exact false idx
    _ = bpCloseOfInorder? shape idx := by
      exact select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem rankCloseCosted_exact
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    (shape : Cartesian.CartesianShape)
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (pos : Nat) :
    (family.rankCloseCosted shape hshape pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact (family.rankData shape hshape).rankCostedClamped_exact false pos

theorem queryBuiltCosted_exact
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost n : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (family.queryBuiltCosted shape hshape left (left + len)).erase =
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
  rcases bpCloseOfInorder?_some_of_lt shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (family.selectCloseCosted shape hshape left).value =
        some leftClose := by
    have h := family.selectCloseCosted_exact shape hshape left
    simpa [Costed.erase, hleftClose] using h
  have hselectRight :
      (family.selectCloseCosted shape hshape
          (left + len - 1)).value =
        some rightClose := by
    have h :=
      family.selectCloseCosted_exact shape hshape (left + len - 1)
    simpa [Costed.erase, hrightClose] using h
  have hlca :
      (family.lcaCloseCosted shape hshape leftClose rightClose).value =
        some answerClose := by
    have h :=
      ((family.lcaFamily.profile).2 n hshape).2.2
        hlen hboundShape hleftClose hrightClose hanswerClose
    simpa [Costed.erase, lcaCloseCosted, hanswerClose] using h
  have hrank :
      (family.rankCloseCosted shape hshape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact :=
      family.rankCloseCosted_exact shape hshape (answerClose + 1)
    have hrankRecover :=
      bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (family.rankCloseCosted shape hshape (answerClose + 1)).value =
          Succinct.rankPrefix false shape.bpCode (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact
      _ = scanWindow shape.representative left len + 1 := hrankRecover
  have hselectLeftRaw :
      ((family.selectData shape hshape).selectCosted false left).value =
        some leftClose := by
    simpa [selectCloseCosted] using hselectLeft
  have hselectRightRaw :
      ((family.selectData shape hshape).selectCosted
          false (left + len - 1)).value =
        some rightClose := by
    simpa [selectCloseCosted] using hselectRight
  have hlcaRaw :
      ((family.lcaFamily.directory
          (n := n) shape hshape).lcaCloseCosted
          leftClose rightClose).value =
        some answerClose := by
    simpa [lcaCloseCosted] using hlca
  have hrankRaw :
      ((family.rankData shape hshape).rankCostedClamped false
          (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    simpa [rankCloseCosted] using hrank
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold queryBuiltCosted
  simp [selectCloseCosted, lcaCloseCosted, rankCloseCosted, Costed.erase,
    Costed.bind, Costed.map, Costed.pure, hselectLeftRaw,
    hselectRightRaw, hlcaRaw, hrankRaw, hrankSub]

theorem two_n_plus_o_built_query_profile
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (family :
      PayloadLiveMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) :
    LittleOLinear family.overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            (family.payload shape hshape).length =
              2 * n + family.overhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            forall left right,
              (family.queryBuiltCosted shape hshape left right).cost <=
                9 + lcaQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (family.queryBuiltCosted
                    shape hshape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  intro n
  constructor
  · have hbase :=
      EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
    omega
  constructor
  · intro shape hshape
    exact family.payload_length hshape
  constructor
  · intro shape hshape left right
    exact family.queryBuiltCosted_cost_le shape hshape left right
  intro shape hshape left len hlen hbound
  exact family.queryBuiltCosted_exact hshape hlen hbound

end PayloadLiveMacroMicroBPCloseNavigationFamily

end SuccinctClose
end RMQ
