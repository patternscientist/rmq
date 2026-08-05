import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReadProgram

/-!
# First-order logical read protocols for the packed reviewer controller

This file defunctionalizes the repeatedly used read-producing atoms of the
packed whole-query program.  Every active state has exactly one next logical
word request.  Consuming the corresponding reply either produces the next
first-order state or a terminal value.  No state contains a shape, a store, a
program list, a proof, or a continuation function.

The physical reviewer controller lowers these logical requests to one or two
reviewer-memory cell requests.  Keeping this layer separate makes the ordered
logical/physical simulation explicit instead of hiding a supplied store behind
a clean wrapper.
-/

namespace RMQ
namespace SuccinctFinal
namespace PackedCellProbe

open RMQ.Cartesian

/-! ## Provenance carried by every logical request -/

/-- The fixed whole-query instruction occurrence producing a logical read. -/
inductive PackedReviewerInstructionSite where
  | leftSelect
  | rightSelect
  | lcaClose
  | finalRank
deriving Repr, DecidableEq

/-- The read-producing site inside one instruction occurrence. -/
inductive PackedReviewerReadSite where
  | entryBaseOccurrence
  | entryBaseWordIndex
  | entryRankBefore
  | entryFirstOffset
  | rankSuper
  | rankBlock
  | rankWord
  | rankChunk
  | selectChunkRank
  | selectChunkValue
  | relativeOffset
  | denseBPWord (slot : Nat)
  | bpWindowWord (slot : Nat)
  | fringeChunk (slot : Nat)
  | interiorChunk (slot : Nat)
deriving Repr, DecidableEq

/--
Invocation data retained in the ordered trace relation.  `argument` is the
select index, rank position, or left close; `argument2` is the right close for
the LCA instruction and zero otherwise.
-/
structure PackedReviewerInvocation where
  instruction : PackedReviewerInstructionSite
  argument : Nat
  argument2 : Nat := 0
deriving Repr, DecidableEq

/-- One logical word request before its physical reviewer-memory lowering. -/
structure PackedReviewerLogicalRequest where
  invocation : PackedReviewerInvocation
  site : PackedReviewerReadSite
  segment : Nat
  index : Nat
deriving Repr, DecidableEq

/-- Decode one optional logical word exactly as the existing word-read atoms. -/
def packedReviewerDecodeNat (reply : Option (List Bool)) : Option Nat :=
  reply.map SuccinctSpace.bitsToNatLE

/-! ## Four-field select-entry protocol -/

inductive PackedReviewerEntryKind where
  | super
  | local
deriving Repr, DecidableEq

def PackedReviewerEntryKind.segmentBase : PackedReviewerEntryKind -> Nat
  | .super => 1
  | .local => 5

/-- First-order state for the four charged fields of one select entry. -/
inductive PackedReviewerEntryState where
  | baseOccurrence
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerEntryKind) (index : Nat)
  | baseWordIndex
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerEntryKind) (index : Nat)
      (baseOccurrence : Option Nat)
  | rankBefore
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerEntryKind) (index : Nat)
      (baseOccurrence baseWordIndex : Option Nat)
  | firstOffset
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerEntryKind) (index : Nat)
      (baseOccurrence baseWordIndex rankBefore : Option Nat)
  | done (value : Option GenericSelect.SparseDenseSelectDenseLocalEntry)

def packedReviewerEntryNextRequest :
    PackedReviewerEntryState -> Option PackedReviewerLogicalRequest
  | .baseOccurrence invocation kind index =>
      some
        { invocation := invocation
          site := .entryBaseOccurrence
          segment := kind.segmentBase
          index := index }
  | .baseWordIndex invocation kind index _ =>
      some
        { invocation := invocation
          site := .entryBaseWordIndex
          segment := kind.segmentBase + 1
          index := index }
  | .rankBefore invocation kind index _ _ =>
      some
        { invocation := invocation
          site := .entryRankBefore
          segment := kind.segmentBase + 2
          index := index }
  | .firstOffset invocation kind index _ _ _ =>
      some
        { invocation := invocation
          site := .entryFirstOffset
          segment := kind.segmentBase + 3
          index := index }
  | .done _ => none

def packedReviewerEntryConsumeReply
    (state : PackedReviewerEntryState) (reply : Option (List Bool)) :
    PackedReviewerEntryState :=
  match state with
  | .baseOccurrence invocation kind index =>
      .baseWordIndex invocation kind index (packedReviewerDecodeNat reply)
  | .baseWordIndex invocation kind index baseOccurrence =>
      .rankBefore invocation kind index baseOccurrence
        (packedReviewerDecodeNat reply)
  | .rankBefore invocation kind index baseOccurrence baseWordIndex =>
      .firstOffset invocation kind index baseOccurrence baseWordIndex
        (packedReviewerDecodeNat reply)
  | .firstOffset _ _ _ baseOccurrence baseWordIndex rankBefore =>
      .done
        (GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.entryOfFields
          baseOccurrence baseWordIndex rankBefore
          (packedReviewerDecodeNat reply))
  | .done value => .done value

def packedReviewerEntryResult :
    PackedReviewerEntryState ->
      Option (Option GenericSelect.SparseDenseSelectDenseLocalEntry)
  | .done value => some value
  | _ => none

def packedReviewerEntryRemaining : PackedReviewerEntryState -> Nat
  | .baseOccurrence _ _ _ => 4
  | .baseWordIndex _ _ _ _ => 3
  | .rankBefore _ _ _ _ _ => 2
  | .firstOffset _ _ _ _ _ _ => 1
  | .done _ => 0

/-! ## Two-level rank plus charged in-word fold -/

/-- The three fixed rank geometries used by the whole query. -/
inductive PackedReviewerRankKind where
  | selectLong
  | selectSparse
  | close
deriving Repr, DecidableEq

def PackedReviewerRankKind.superSegment : PackedReviewerRankKind -> Nat
  | .selectLong => 9
  | .selectSparse => 13
  | .close => 17

def PackedReviewerRankKind.blockSegment (kind : PackedReviewerRankKind) : Nat :=
  kind.superSegment + 1

def PackedReviewerRankKind.wordSegment (kind : PackedReviewerRankKind) : Nat :=
  kind.superSegment + 2

def PackedReviewerRankKind.target : PackedReviewerRankKind -> Bool
  | .selectLong | .selectSparse => true
  | .close => false

def PackedReviewerRankKind.bitLength
    (kind : PackedReviewerRankKind) (n : Nat) : Nat :=
  match kind with
  | .selectLong => packedSuperSlots n
  | .selectSparse => packedSparseSlots n
  | .close => 2 * n

def PackedReviewerRankKind.wordSize
    (kind : PackedReviewerRankKind) (n : Nat) : Nat :=
  match kind with
  | .selectLong => packedLongFlagWordSize n
  | .selectSparse => packedSparseWordSize n
  | .close => packedBpCodeWordWidth n

def PackedReviewerRankKind.blocksPerSuper
    (kind : PackedReviewerRankKind) (n : Nat) : Nat :=
  match kind with
  | .selectLong | .selectSparse => 1
  | .close => packedBpCodeWordWidth n

/--
First-order state for the exact logical trace of `packedRankRead`.  The fold
stores only a returned logical word and scalar accumulator data.
-/
inductive PackedReviewerRankState where
  | superSample
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerRankKind) (n pos : Nat)
  | blockSample
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerRankKind) (n pos : Nat)
      (superSample : Option Nat)
  | word
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerRankKind) (n pos : Nat)
      (superSample blockSample : Option Nat)
  | fold
      (invocation : PackedReviewerInvocation)
      (kind : PackedReviewerRankKind) (n : Nat)
      (word : List Bool) (effectiveLimit j remaining acc base : Nat)
  | done (value : Nat)

def packedReviewerRankQueryPos
    (kind : PackedReviewerRankKind) (n pos : Nat) : Nat :=
  Nat.min pos (kind.bitLength n)

def packedReviewerRankStartFold
    (invocation : PackedReviewerInvocation)
    (kind : PackedReviewerRankKind) (n : Nat)
    (word : List Bool) (limit base : Nat) :
    PackedReviewerRankState :=
  let effectiveLimit := SuccinctClose.bpWordRankEffLimit word limit
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) effectiveLimit
  if count = 0 then
    .done base
  else
    .fold invocation kind n word effectiveLimit 0 count 0 base

def packedReviewerRankNextRequest :
    PackedReviewerRankState -> Option PackedReviewerLogicalRequest
  | .superSample invocation kind n pos =>
      let q := packedReviewerRankQueryPos kind n pos
      some
        { invocation := invocation
          site := .rankSuper
          segment := kind.superSegment
          index := q / kind.wordSize n / kind.blocksPerSuper n }
  | .blockSample invocation kind n pos _ =>
      let q := packedReviewerRankQueryPos kind n pos
      some
        { invocation := invocation
          site := .rankBlock
          segment := kind.blockSegment
          index := q / kind.wordSize n }
  | .word invocation kind n pos _ _ =>
      let q := packedReviewerRankQueryPos kind n pos
      some
        { invocation := invocation
          site := .rankWord
          segment := kind.wordSegment
          index := q / kind.wordSize n }
  | .fold invocation _ n word effectiveLimit j remaining _ _ =>
      match remaining with
      | 0 => none
      | _ + 1 =>
          let c := packedFringeChunkBits n
          some
            { invocation := invocation
              site := .rankChunk
              segment := 21
              index :=
                SuccinctClose.bpFringeChunkSlot c
                  (SuccinctClose.bpFringeWindowChunkValue c word j)
                  (SuccinctClose.bpWordChunkSliceLen c effectiveLimit j)
                  (SuccinctClose.bpWordChunkSliceLen c effectiveLimit j) }
  | .done _ => none

def packedReviewerRankConsumeReply
    (state : PackedReviewerRankState) (reply : Option (List Bool)) :
    PackedReviewerRankState :=
  match state with
  | .superSample invocation kind n pos =>
      .blockSample invocation kind n pos (packedReviewerDecodeNat reply)
  | .blockSample invocation kind n pos superSample =>
      .word invocation kind n pos superSample (packedReviewerDecodeNat reply)
  | .word invocation kind n pos superSample blockSample =>
      match superSample, blockSample, reply with
      | some superValue, some blockValue, some word =>
          let q := packedReviewerRankQueryPos kind n pos
          let limit := q - q / kind.wordSize n * kind.wordSize n
          packedReviewerRankStartFold invocation kind n word limit
            (superValue + blockValue)
      | _, _, _ => .done 0
  | .fold invocation kind n word effectiveLimit j remaining acc base =>
      match remaining with
      | 0 => .done (base + acc)
      | remaining + 1 =>
          let c := packedFringeChunkBits n
          let acc' :=
            SuccinctClose.bpWordRankStepDecoded c kind.target
              (SuccinctClose.bpWordChunkSliceLen c effectiveLimit j) acc
              (packedReviewerDecodeNat reply)
          if remaining = 0 then
            .done (base + acc')
          else
            .fold invocation kind n word effectiveLimit (j + 1) remaining
              acc' base
  | .done value => .done value

def packedReviewerRankResult : PackedReviewerRankState -> Option Nat
  | .done value => some value
  | _ => none

/-- Worst-case remaining logical reads; every in-word fold has at most eight. -/
def packedReviewerRankRemaining : PackedReviewerRankState -> Nat
  | .superSample _ _ _ _ => 11
  | .blockSample _ _ _ _ _ => 10
  | .word _ _ _ _ _ _ => 9
  | .fold _ _ _ _ _ _ remaining _ _ => remaining
  | .done _ => 0

/-! ## Charged in-word select fold -/

inductive PackedReviewerWordSelectState where
  | rankChunk
      (invocation : PackedReviewerInvocation)
      (n : Nat) (target : Bool) (word : List Bool)
      (j remaining occurrence : Nat)
  | selectChunk
      (invocation : PackedReviewerInvocation)
      (n : Nat) (target : Bool) (word : List Bool)
      (j remaining occurrence : Nat)
  | done (value : Option Nat)

def packedReviewerWordSelectStart
    (invocation : PackedReviewerInvocation)
    (n : Nat) (target : Bool) (word : List Bool) (occurrence : Nat) :
    PackedReviewerWordSelectState :=
  let count :=
    SuccinctClose.bpWordChunkCount (packedFringeChunkBits n) word.length
  if count = 0 then .done none
  else .rankChunk invocation n target word 0 count occurrence

def packedReviewerWordSelectNextRequest :
    PackedReviewerWordSelectState -> Option PackedReviewerLogicalRequest
  | .rankChunk invocation n _ word j remaining _ =>
      match remaining with
      | 0 => none
      | _ + 1 =>
          let c := packedFringeChunkBits n
          some
            { invocation := invocation
              site := .selectChunkRank
              segment := 21
              index :=
                SuccinctClose.bpFringeChunkSlot c
                  (SuccinctClose.bpFringeWindowChunkValue c word j)
                  (SuccinctClose.bpWordChunkSliceLen c word.length j)
                  (SuccinctClose.bpWordChunkSliceLen c word.length j) }
  | .selectChunk invocation n _ word j _ occurrence =>
      let c := packedFringeChunkBits n
      some
        { invocation := invocation
          site := .selectChunkValue
          segment := 22
          index :=
            SuccinctClose.bpChunkSelectSlot c
              (SuccinctClose.bpFringeWindowChunkValue c word j) occurrence }
  | .done _ => none

def packedReviewerWordSelectConsumeReply
    (state : PackedReviewerWordSelectState) (reply : Option (List Bool)) :
    PackedReviewerWordSelectState :=
  match state with
  | .rankChunk invocation n target word j remaining occurrence =>
      let c := packedFringeChunkBits n
      let rank :=
        SuccinctClose.bpChunkRankOfEntry c target
          (SuccinctClose.bpWordChunkSliceLen c word.length j)
          ((packedReviewerDecodeNat reply).getD 0)
      if occurrence < rank then
        .selectChunk invocation n target word j remaining occurrence
      else
        match remaining with
        | 0 => .done none
        | remaining + 1 =>
            if remaining = 0 then .done none
            else
              .rankChunk invocation n target word (j + 1) remaining
                (occurrence - rank)
  | .selectChunk _ n _ _ j _ _ =>
      .done
        (some
          (j * packedFringeChunkBits n +
            (packedReviewerDecodeNat reply).getD 0))
  | .done value => .done value

def packedReviewerWordSelectResult :
    PackedReviewerWordSelectState -> Option (Option Nat)
  | .done value => some value
  | _ => none

/-- One rank-table read per remaining chunk, plus at most one select read. -/
def packedReviewerWordSelectRemaining : PackedReviewerWordSelectState -> Nat
  | .rankChunk _ _ _ _ _ remaining _ => remaining + 1
  | .selectChunk _ _ _ _ _ _ _ => 1
  | .done _ => 0

/-! ## Charged fringe fold -/

inductive PackedReviewerFringeState where
  | chunk
      (invocation : PackedReviewerInvocation)
      (n : Nat) (window : List Bool) (relLo relHi j remaining : Nat)
      (state : Nat × Option (Nat × Nat))
  | done (value : Nat × Option (Nat × Nat))

def packedReviewerFringeStart
    (invocation : PackedReviewerInvocation)
    (n : Nat) (window : List Bool) (seed relLo relHi count : Nat) :
    PackedReviewerFringeState :=
  if count = 0 then .done (seed, none)
  else .chunk invocation n window relLo relHi 0 count (seed, none)

def packedReviewerFringeNextRequest :
    PackedReviewerFringeState -> Option PackedReviewerLogicalRequest
  | .chunk invocation n window relLo relHi j remaining _ =>
      match remaining with
      | 0 => none
      | _ + 1 =>
          let c := packedFringeChunkBits n
          let slot :=
            SuccinctClose.bpFringeChunkSlot c
              (SuccinctClose.bpFringeWindowChunkValue c window j)
              (SuccinctClose.bpFringeChunkStartOff c relLo j)
              (SuccinctClose.bpFringeChunkEndOff c relHi j)
          some
            { invocation := invocation
              site := .fringeChunk slot
              segment := 21
              index := slot }
  | .done _ => none

def packedReviewerFringeConsumeReply
    (state : PackedReviewerFringeState) (reply : Option (List Bool)) :
    PackedReviewerFringeState :=
  match state with
  | .chunk invocation n window relLo relHi j remaining foldState =>
      let c := packedFringeChunkBits n
      let nextState :=
        SuccinctClose.bpFringeChunkStepDecoded c relLo relHi j foldState
          (packedReviewerDecodeNat reply)
      match remaining with
      | 0 => .done nextState
      | remaining + 1 =>
          if remaining = 0 then .done nextState
          else
            .chunk invocation n window relLo relHi (j + 1) remaining nextState
  | .done value => .done value

def packedReviewerFringeResult :
    PackedReviewerFringeState -> Option (Nat × Option (Nat × Nat))
  | .done value => some value
  | _ => none

def packedReviewerFringeRemaining : PackedReviewerFringeState -> Nat
  | .chunk _ _ _ _ _ _ remaining _ => remaining
  | .done _ => 0

/-! ## Four-word local BP window -/

inductive PackedReviewerBPWindowState where
  | read
      (invocation : PackedReviewerInvocation)
      (n blockSize close next : Nat)
      (wordsRev : List (List Bool))
  | done (bits : List Bool)

def packedReviewerBPWindowStart
    (invocation : PackedReviewerInvocation)
    (n blockSize close : Nat) : PackedReviewerBPWindowState :=
  .read invocation n blockSize close 0 []

def packedReviewerBPWindowNextRequest :
    PackedReviewerBPWindowState -> Option PackedReviewerLogicalRequest
  | .read invocation n blockSize close next _ =>
      if next < 4 then
        let firstWord :=
          SuccinctClose.blockStartOf blockSize
              (SuccinctClose.blockOfClose blockSize close) /
            packedBpCodeWordWidth n
        some
          { invocation := invocation
            site := .bpWindowWord next
            segment := 0
            index := firstWord + next }
      else none
  | .done _ => none

def packedReviewerBPWindowConsumeReply
    (state : PackedReviewerBPWindowState) (reply : Option (List Bool)) :
    PackedReviewerBPWindowState :=
  match state with
  | .read invocation n blockSize close next wordsRev =>
      let wordsRev' := reply.getD [] :: wordsRev
      if next + 1 = 4 then
        .done (SuccinctSpace.flattenPayloadWords wordsRev'.reverse)
      else
        .read invocation n blockSize close (next + 1) wordsRev'
  | .done bits => .done bits

def packedReviewerBPWindowResult :
    PackedReviewerBPWindowState -> Option (List Bool)
  | .done bits => some bits
  | _ => none

def packedReviewerBPWindowRemaining : PackedReviewerBPWindowState -> Nat
  | .read _ _ _ _ next _ => 4 - next
  | .done _ => 0

/-! ## Table-free segment-20 read primitive -/

/--
First-order state for `packedInteriorReadNatOf`.  The only list in an active
state is the reverse-ordered list of replies already consumed from segment 20.
-/
inductive PackedReviewerInteriorNatState where
  | read
      (invocation : PackedReviewerInvocation)
      (n start next remaining : Nat)
      (repliesRev : List (Option (List Bool)))
  | done (value : Option Nat)

def packedReviewerInteriorNatStart
    (invocation : PackedReviewerInvocation)
    (n entryCount width base index : Nat) : PackedReviewerInteriorNatState :=
  let wordSize := packedBpCodeWordWidth n
  let count := SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize
  if index < entryCount then
    if count = 0 then
      .done (SuccinctSpace.fixedWidthNatTableMachineDecode [])
    else
      .read invocation n (base + index * count) 0 count []
  else
    .read invocation n (packedInteriorOffsets n).deadAddress 0 1 []

def packedReviewerInteriorNatNextRequest :
    PackedReviewerInteriorNatState -> Option PackedReviewerLogicalRequest
  | .read invocation _ start next remaining _ =>
      match remaining with
      | 0 => none
      | _ + 1 =>
          let slot := start + next
          some
            { invocation := invocation
              site := .interiorChunk slot
              segment := 20
              index := slot }
  | .done _ => none

def packedReviewerInteriorNatConsumeReply
    (state : PackedReviewerInteriorNatState) (reply : Option (List Bool)) :
    PackedReviewerInteriorNatState :=
  match state with
  | .read invocation n start next remaining repliesRev =>
      let repliesRev' := reply :: repliesRev
      match remaining with
      | 0 =>
          .done
            (SuccinctSpace.fixedWidthNatTableMachineDecode repliesRev'.reverse)
      | remaining + 1 =>
          if remaining = 0 then
            .done
              (SuccinctSpace.fixedWidthNatTableMachineDecode
                repliesRev'.reverse)
          else
            .read invocation n start (next + 1) remaining repliesRev'
  | .done value => .done value

def packedReviewerInteriorNatResult :
    PackedReviewerInteriorNatState -> Option (Option Nat)
  | .done value => some value
  | _ => none

def packedReviewerInteriorNatRemaining : PackedReviewerInteriorNatState -> Nat
  | .read _ _ _ _ remaining _ => remaining
  | .done _ => 0

end PackedCellProbe
end SuccinctFinal
end RMQ
