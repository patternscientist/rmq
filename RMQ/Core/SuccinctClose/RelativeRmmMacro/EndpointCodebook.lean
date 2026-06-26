import RMQ.Core.SuccinctClose.RelativeRmmMacro.AbstractMacro

/-!
# Payload-live endpoint-fringe codebook

Split implementation layer for the relative-rmM BP close/LCA macro. Public
declarations stay in the historical RMQ.SuccinctCloseProposal namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

def payloadWordReadOfGet?
    (words : Array (List Bool)) (index : Nat) : List (List Bool) :=
  match words[index]? with
  | some word => [word]
  | none => []

theorem payloadWordReadOfGet?_length_le
    {words : Array (List Bool)} {index limit : Nat}
    (hword :
      forall {word : List Bool},
        words[index]? = some word -> word.length <= limit)
    {word : List Bool}
    (hmem : word ∈ payloadWordReadOfGet? words index) :
    word.length <= limit := by
  unfold payloadWordReadOfGet? at hmem
  cases hget : words[index]? with
  | none =>
      simp [hget] at hmem
  | some stored =>
      simp [hget] at hmem
      rcases hmem with rfl
      exact hword hget

/--
Local endpoint-fringe slot for the left endpoint of a cross-block query.

The slot is block-local: it is keyed only by the endpoint's offset within its
block.  This is the compact replacement for the global dense
`endpointLeftFringeRanges blockSize blockCount` index.
-/
def endpointLeftLocalFringeSlot (_blockSize localClose : Nat) : Nat :=
  localClose

/--
Local endpoint-fringe slot for the right endpoint of a cross-block query.

Right-fringe slots occupy the second half of the per-code local table, after
the left-fringe slots.
-/
def endpointRightLocalFringeSlot (blockSize localClose : Nat) : Nat :=
  blockSize + localClose

/-- Decode one local endpoint-fringe table slot into the represented prefix range. -/
def endpointLocalFringeRangeOfSlot
    (blockSize blockStart slot : Nat) : Nat × Nat :=
  if slot < blockSize then
    (blockStart + slot + 1, blockSize - slot)
  else
    (blockStart, slot - blockSize + 2)

/--
All endpoint-fringe ranges for a single block, stored in a local table:
left-fringe ranges first, then right-fringe ranges.
-/
def endpointLocalFringeRanges
    (blockSize blockStart : Nat) : List (Nat × Nat) :=
  (List.range (2 * blockSize)).map
    (endpointLocalFringeRangeOfSlot blockSize blockStart)

theorem endpointLocalFringeRanges_length
    (blockSize blockStart : Nat) :
    (endpointLocalFringeRanges blockSize blockStart).length =
      2 * blockSize := by
  simp [endpointLocalFringeRanges]

theorem endpointLocalFringeRanges_get?_left
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (endpointLocalFringeRanges blockSize blockStart)[
        endpointLeftLocalFringeSlot blockSize localClose]? =
      some (blockStart + localClose + 1, blockSize - localClose) := by
  have hslot :
      endpointLeftLocalFringeSlot blockSize localClose < 2 * blockSize := by
    simp [endpointLeftLocalFringeSlot]
    omega
  have hslotGet :
      (List.range (2 * blockSize))[
          endpointLeftLocalFringeSlot blockSize localClose]? =
        some (endpointLeftLocalFringeSlot blockSize localClose) := by
    exact List.getElem?_range hslot
  have hmapped :
      ((List.range (2 * blockSize)).map
          (endpointLocalFringeRangeOfSlot blockSize blockStart))[
            endpointLeftLocalFringeSlot blockSize localClose]? =
        some
          (endpointLocalFringeRangeOfSlot blockSize blockStart
            (endpointLeftLocalFringeSlot blockSize localClose)) := by
    simp [List.getElem?_map, hslotGet]
  simpa [endpointLocalFringeRanges, endpointLocalFringeRangeOfSlot,
    endpointLeftLocalFringeSlot, hlocal] using hmapped

theorem endpointLocalFringeRanges_get?_right
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (endpointLocalFringeRanges blockSize blockStart)[
        endpointRightLocalFringeSlot blockSize localClose]? =
      some (blockStart, localClose + 2) := by
  have hslot :
      endpointRightLocalFringeSlot blockSize localClose < 2 * blockSize := by
    simp [endpointRightLocalFringeSlot]
    omega
  have hslotGet :
      (List.range (2 * blockSize))[
          endpointRightLocalFringeSlot blockSize localClose]? =
        some (endpointRightLocalFringeSlot blockSize localClose) := by
    exact List.getElem?_range hslot
  have hnot :
      ¬ endpointRightLocalFringeSlot blockSize localClose < blockSize := by
    simp [endpointRightLocalFringeSlot]
  have hcount :
      endpointRightLocalFringeSlot blockSize localClose - blockSize + 2 =
        localClose + 2 := by
    simp [endpointRightLocalFringeSlot]
  have hmapped :
      ((List.range (2 * blockSize)).map
          (endpointLocalFringeRangeOfSlot blockSize blockStart))[
            endpointRightLocalFringeSlot blockSize localClose]? =
        some
          (endpointLocalFringeRangeOfSlot blockSize blockStart
            (endpointRightLocalFringeSlot blockSize localClose)) := by
    simp [List.getElem?_map, hslotGet]
  simpa [endpointLocalFringeRanges, endpointLocalFringeRangeOfSlot,
    hnot, hcount] using hmapped

theorem endpointLocalFringeMinExcessEntries_get?_left
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointLeftLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeMinExcess shape
          (blockStart + localClose + 1) (blockSize - localClose)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_left hlocal)

theorem endpointLocalFringeArgMinEntries_get?_left
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointLeftLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape
          (blockStart + localClose + 1) (blockSize - localClose)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_left hlocal)

theorem endpointLocalFringeMinExcessEntries_get?_right
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointRightLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeMinExcess shape blockStart (localClose + 2)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_right hlocal)

theorem endpointLocalFringeArgMinEntries_get?_right
    {shape : Cartesian.CartesianShape}
    {blockSize blockStart localClose : Nat}
    (hlocal : localClose < blockSize) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLocalFringeRanges blockSize blockStart))[
          endpointRightLocalFringeSlot blockSize localClose]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape blockStart (localClose + 2)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointLocalFringeRanges_get?_right hlocal)

/--
Payload-live endpoint-fringe codebook.

The query path reads a charged per-block code and then two charged fixed-width
payload words from the finite local endpoint-fringe table for that code.  The
payload is a classifier plus one local left/right-fringe witness table per
code; there is no global dense table over all endpoint positions.
-/
structure PayloadLiveBlockEndpointFringeCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat) where
  classifier :
    BlockCodeTable blockCount codeCount codeWidth codeOverhead
  minEntriesByCode : Nat -> List Nat
  argEntriesByCode : Nat -> List Nat
  minTable :
    (code : Nat) ->
      FixedWidthNatTable (minEntriesByCode code) fieldWidth
  argTable :
    (code : Nat) ->
      FixedWidthNatTable (argEntriesByCode code) fieldWidth
  tablePayload : List Bool
  tablePayload_eq_tables :
    tablePayload =
      (List.range codeCount).flatMap fun code =>
        (minTable code).payload ++ (argTable code).payload
  tablePayload_length_eq :
    tablePayload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (minTable code).payload.length +
          (argTable code).payload.length =
        tableOverhead
  block_fringe_entries :
    forall {block code : Nat},
      classifier.codeAt block = some code ->
        minEntriesByCode code =
            bpPrefixRangeMinExcessEntries shape
              (endpointLocalFringeRanges blockSize
                (blockStartOf blockSize block)) /\
          argEntriesByCode code =
            bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLocalFringeRanges blockSize
                (blockStartOf blockSize block))

namespace PayloadLiveBlockEndpointFringeCodebook

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead) :
    List Bool :=
  fringe.classifier.payload ++ fringe.tablePayload

def leftSlot
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (_fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Nat :=
  endpointLeftLocalFringeSlot blockSize
    (close - blockStartOf blockSize block)

def rightSlot
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (_fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Nat :=
  endpointRightLocalFringeSlot blockSize
    (close - blockStartOf blockSize block)

def witnessCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (slot block : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (fringe.classifier.codeCosted block) fun code? =>
    match code? with
    | none => Costed.pure none
    | some code =>
        if _hcode : code < codeCount then
          Costed.bind ((fringe.minTable code).readCosted slot) fun min? =>
            Costed.map
              (fun arg? =>
                match min?, arg? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
              ((fringe.argTable code).readCosted slot)
        else
          Costed.pure none

def leftFringeCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.witnessCostedAtBlock (fringe.leftSlot block close) block

def rightFringeCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.witnessCostedAtBlock (fringe.rightSlot block close) block

def leftFringeCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.leftFringeCostedAtBlock (blockOfClose blockSize close) close

def rightFringeCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) : Costed (Option (Nat × Nat)) :=
  fringe.rightFringeCostedAtBlock (blockOfClose blockSize close) close

def wordsReadAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (slot block : Nat) : List (List Bool) :=
  payloadWordReadOfGet? fringe.classifier.table.store.words block ++
    match fringe.classifier.codeAt block with
    | none => []
    | some code =>
        if code < codeCount then
          payloadWordReadOfGet? (fringe.minTable code).store.words slot ++
            payloadWordReadOfGet? (fringe.argTable code).store.words slot
        else
          []

def leftWordsReadAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : List (List Bool) :=
  fringe.wordsReadAtBlock (fringe.leftSlot block close) block

def rightWordsReadAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) : List (List Bool) :=
  fringe.wordsReadAtBlock (fringe.rightSlot block close) block

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead) :
    fringe.payload.length =
      codeOverhead + codeCount * tableOverhead := by
  simp [payload, fringe.classifier.payload_length,
    fringe.tablePayload_length_eq]

theorem witnessCostedAtBlock_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (slot block : Nat) :
    (fringe.witnessCostedAtBlock slot block).cost <= 3 := by
  unfold witnessCostedAtBlock
  have hclassifier := fringe.classifier.codeCosted_cost_le_one block
  cases hread : (fringe.classifier.codeCosted block).value with
  | none =>
      simp [Costed.bind, Costed.pure, hread]
      omega
  | some code =>
      by_cases hcode : code < codeCount
      · cases hmin : ((fringe.minTable code).readCosted slot).value with
        | none =>
            simp [Costed.bind, Costed.map, Costed.pure, hread, hcode,
              hmin]
            omega
        | some minExcess =>
            simp [Costed.bind, Costed.map, Costed.pure, hread, hcode,
              hmin]
            omega
      · simp [Costed.bind, Costed.pure, hread, hcode]
        omega

theorem leftFringeCostedAtBlock_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) :
    (fringe.leftFringeCostedAtBlock block close).cost <= 3 := by
  exact fringe.witnessCostedAtBlock_cost_le_three
    (fringe.leftSlot block close) block

theorem rightFringeCostedAtBlock_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (block close : Nat) :
    (fringe.rightFringeCostedAtBlock block close).cost <= 3 := by
  exact fringe.witnessCostedAtBlock_cost_le_three
    (fringe.rightSlot block close) block

theorem leftFringeCosted_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) :
    (fringe.leftFringeCosted close).cost <= 3 := by
  unfold leftFringeCosted
  exact fringe.leftFringeCostedAtBlock_cost_le_three
    (blockOfClose blockSize close) close

theorem rightFringeCosted_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (close : Nat) :
    (fringe.rightFringeCosted close).cost <= 3 := by
  unfold rightFringeCosted
  exact fringe.rightFringeCostedAtBlock_cost_le_three
    (blockOfClose blockSize close) close

theorem leftFringeCostedAtBlock_exact_of_code
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close code : Nat}
    (hcodeAt : fringe.classifier.codeAt block = some code)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.leftFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize block + blockSize - close),
          bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
  let localClose := close - blockStartOf blockSize block
  have hlocal : localClose < blockSize := by
    dsimp [localClose]
    omega
  have hstart :
      blockStartOf blockSize block + localClose + 1 = close + 1 := by
    dsimp [localClose]
    omega
  have hcount :
      blockSize - localClose =
        blockStartOf blockSize block + blockSize - close := by
    dsimp [localClose]
    omega
  have hread :
      (fringe.classifier.codeCosted block).value = some code := by
    simpa [Costed.erase] using
      fringe.classifier.codeCosted_exact_of_codeAt hcodeAt
  have hcodeLt : code < codeCount :=
    fringe.classifier.codeAt_lt hcodeAt
  have hentries := fringe.block_fringe_entries hcodeAt
  have hminEntry :
      (fringe.minEntriesByCode code)[fringe.leftSlot block close]? =
        some
          (bpPrefixRangeMinExcess shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    rw [hentries.1]
    simpa [leftSlot, endpointLeftLocalFringeSlot, localClose, hstart,
      hcount] using
      (endpointLocalFringeMinExcessEntries_get?_left
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hargEntry :
      (fringe.argEntriesByCode code)[fringe.leftSlot block close]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    rw [hentries.2]
    simpa [leftSlot, endpointLeftLocalFringeSlot, localClose, hstart,
      hcount] using
      (endpointLocalFringeArgMinEntries_get?_left
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hminRead :
      ((fringe.minTable code).readCosted
          (fringe.leftSlot block close)).value =
        some
          (bpPrefixRangeMinExcess shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    have h := (fringe.minTable code).readCosted_erase
      (fringe.leftSlot block close)
    simpa [Costed.erase, hminEntry] using h
  have hargRead :
      ((fringe.argTable code).readCosted
          (fringe.leftSlot block close)).value =
        some
          (bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
    have h := (fringe.argTable code).readCosted_erase
      (fringe.leftSlot block close)
    simpa [Costed.erase, hargEntry] using h
  simp [leftFringeCostedAtBlock, witnessCostedAtBlock, Costed.bind,
    Costed.map, Costed.erase, hread, hcodeLt, hminRead, hargRead]

theorem rightFringeCostedAtBlock_exact_of_code
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close code : Nat}
    (hcodeAt : fringe.classifier.codeAt block = some code)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.rightFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize block)
          (close - blockStartOf blockSize block + 2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
  let localClose := close - blockStartOf blockSize block
  have hlocal : localClose < blockSize := by
    dsimp [localClose]
    omega
  have hcount :
      localClose + 2 =
        close - blockStartOf blockSize block + 2 := by
    dsimp [localClose]
  have hread :
      (fringe.classifier.codeCosted block).value = some code := by
    simpa [Costed.erase] using
      fringe.classifier.codeCosted_exact_of_codeAt hcodeAt
  have hcodeLt : code < codeCount :=
    fringe.classifier.codeAt_lt hcodeAt
  have hentries := fringe.block_fringe_entries hcodeAt
  have hminEntry :
      (fringe.minEntriesByCode code)[fringe.rightSlot block close]? =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    rw [hentries.1]
    simpa [rightSlot, endpointRightLocalFringeSlot, localClose, hcount] using
      (endpointLocalFringeMinExcessEntries_get?_right
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hargEntry :
      (fringe.argEntriesByCode code)[fringe.rightSlot block close]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    rw [hentries.2]
    simpa [rightSlot, endpointRightLocalFringeSlot, localClose, hcount] using
      (endpointLocalFringeArgMinEntries_get?_right
        (shape := shape) (blockSize := blockSize)
        (blockStart := blockStartOf blockSize block)
        (localClose := localClose) hlocal)
  have hminRead :
      ((fringe.minTable code).readCosted
          (fringe.rightSlot block close)).value =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    have h := (fringe.minTable code).readCosted_erase
      (fringe.rightSlot block close)
    simpa [Costed.erase, hminEntry] using h
  have hargRead :
      ((fringe.argTable code).readCosted
          (fringe.rightSlot block close)).value =
        some
          (bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
    have h := (fringe.argTable code).readCosted_erase
      (fringe.rightSlot block close)
    simpa [Costed.erase, hargEntry] using h
  simp [rightFringeCostedAtBlock, witnessCostedAtBlock, Costed.bind,
    Costed.map, Costed.erase, hread, hcodeLt, hminRead, hargRead]

theorem leftFringeCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close : Nat}
    (hblock : block < blockCount)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.leftFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize block + blockSize - close),
          bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize block + blockSize - close)) := by
  rcases fringe.classifier.codeAt_exists_of_lt hblock with
    ⟨code, hcodeAt⟩
  exact fringe.leftFringeCostedAtBlock_exact_of_code
    hcodeAt hcloseLo hcloseHi

theorem rightFringeCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    {block close : Nat}
    (hblock : block < blockCount)
    (hcloseLo : blockStartOf blockSize block <= close)
    (hcloseHi : close < blockStartOf blockSize block + blockSize) :
    (fringe.rightFringeCostedAtBlock block close).erase =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize block)
          (close - blockStartOf blockSize block + 2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize block)
            (close - blockStartOf blockSize block + 2)) := by
  rcases fringe.classifier.codeAt_exists_of_lt hblock with
    ⟨code, hcodeAt⟩
  exact fringe.rightFringeCostedAtBlock_exact_of_code
    hcodeAt hcloseLo hcloseHi

theorem leftFringeCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hblockSize : 0 < blockSize)
    {close : Nat}
    (hblock : blockOfClose blockSize close < blockCount) :
    (fringe.leftFringeCosted close).erase =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close),
          bpPrefixRangeArgMinPrefixPos shape (close + 1)
            (blockStartOf blockSize (blockOfClose blockSize close) +
              blockSize - close)) := by
  unfold leftFringeCosted
  exact
    fringe.leftFringeCostedAtBlock_exact hblock
      blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)

theorem rightFringeCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hblockSize : 0 < blockSize)
    {close : Nat}
    (hblock : blockOfClose blockSize close < blockCount) :
    (fringe.rightFringeCosted close).erase =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close -
              blockStartOf blockSize (blockOfClose blockSize close) +
            2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize (blockOfClose blockSize close))
            (close -
                blockStartOf blockSize (blockOfClose blockSize close) +
              2)) := by
  unfold rightFringeCosted
  exact
    fringe.rightFringeCostedAtBlock_exact hblock
      blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)

theorem wordsReadAtBlock_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {slot block : Nat} {word : List Bool}
    (hmem : word ∈ fringe.wordsReadAtBlock slot block) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hclass :
      forall {word : List Bool},
        fringe.classifier.table.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
    intro word hword
    have hlen := fringe.classifier.table.read_word_length_of_some hword
    omega
  unfold wordsReadAtBlock at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hclassMem | htableMem
  · exact payloadWordReadOfGet?_length_le hclass hclassMem
  · cases hcodeAt : fringe.classifier.codeAt block with
    | none =>
        simp [hcodeAt] at htableMem
    | some code =>
        by_cases hcode : code < codeCount
        · have hmin :
            forall {word : List Bool},
              (fringe.minTable code).store.words[slot]? = some word ->
                word.length <=
                  SuccinctRankProposal.machineWordBits
                    shape.bpCode.length := by
            intro word hword
            have hlen := (fringe.minTable code).read_word_length_of_some
              hword
            omega
          have harg :
            forall {word : List Bool},
              (fringe.argTable code).store.words[slot]? = some word ->
                word.length <=
                  SuccinctRankProposal.machineWordBits
                    shape.bpCode.length := by
            intro word hword
            have hlen := (fringe.argTable code).read_word_length_of_some
              hword
            omega
          simp [hcodeAt, hcode, List.mem_append] at htableMem
          rcases htableMem with hminMem | hargMem
          · exact payloadWordReadOfGet?_length_le hmin hminMem
          · exact payloadWordReadOfGet?_length_le harg hargMem
        · simp [hcodeAt, hcode] at htableMem

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    forall {slot block : Nat} {word : List Bool},
      word ∈ fringe.wordsReadAtBlock slot block ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro slot block word hmem
  exact fringe.wordsReadAtBlock_length_le_machine
    hcodeMachine hfieldMachine hmem

theorem leftWordsReadAtBlock_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {block close : Nat} {word : List Bool}
    (hmem : word ∈ fringe.leftWordsReadAtBlock block close) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact fringe.wordsReadAtBlock_length_le_machine
    hcodeMachine hfieldMachine hmem

theorem rightWordsReadAtBlock_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead)
    (hcodeMachine :
      codeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hfieldMachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {block close : Nat} {word : List Bool}
    (hmem : word ∈ fringe.rightWordsReadAtBlock block close) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact fringe.wordsReadAtBlock_length_le_machine
    hcodeMachine hfieldMachine hmem

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      fieldWidth tableOverhead : Nat}
    (fringe :
      PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
        codeCount codeWidth codeOverhead fieldWidth tableOverhead) :
    fringe.payload.length =
        codeOverhead + codeCount * tableOverhead /\
      (forall close,
        (fringe.leftFringeCosted close).cost <= 3 /\
          (fringe.rightFringeCosted close).cost <= 3) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.leftFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape (close + 1)
                  (blockStartOf blockSize
                      (blockOfClose blockSize close) +
                    blockSize - close),
                  bpPrefixRangeArgMinPrefixPos shape (close + 1)
                    (blockStartOf blockSize
                        (blockOfClose blockSize close) +
                      blockSize - close))) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.rightFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape
                  (blockStartOf blockSize
                    (blockOfClose blockSize close))
                  (close -
                      blockStartOf blockSize
                        (blockOfClose blockSize close) +
                    2),
                  bpPrefixRangeArgMinPrefixPos shape
                    (blockStartOf blockSize
                      (blockOfClose blockSize close))
                    (close -
                        blockStartOf blockSize
                          (blockOfClose blockSize close) +
                      2))) := by
  constructor
  · exact fringe.payload_length
  constructor
  · intro close
    exact ⟨fringe.leftFringeCosted_cost_le_three close,
      fringe.rightFringeCosted_cost_le_three close⟩
  constructor
  · intro close hblockSize hblock
    exact fringe.leftFringeCosted_exact hblockSize hblock
  · intro close hblockSize hblock
    exact fringe.rightFringeCosted_exact hblockSize hblock

end PayloadLiveBlockEndpointFringeCodebook

def concreteEndpointFringeMinEntries
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) : List Nat :=
  bpPrefixRangeMinExcessEntries shape
    (endpointLocalFringeRanges blockSize
      (blockStartOf blockSize code))

def concreteEndpointFringeArgEntries
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) : List Nat :=
  bpPrefixRangeArgMinPrefixPosEntries shape
    (endpointLocalFringeRanges blockSize
      (blockStartOf blockSize code))

theorem concreteEndpointFringeMinEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) :
    (concreteEndpointFringeMinEntries shape blockSize code).length =
      2 * blockSize := by
  simp [concreteEndpointFringeMinEntries,
    bpPrefixRangeMinExcessEntries_length,
    endpointLocalFringeRanges_length]

theorem concreteEndpointFringeArgEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize code : Nat) :
    (concreteEndpointFringeArgEntries shape blockSize code).length =
      2 * blockSize := by
  simp [concreteEndpointFringeArgEntries,
    bpPrefixRangeArgMinPrefixPosEntries_length,
    endpointLocalFringeRanges_length]

def concreteEndpointFringeMinTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    FixedWidthNatTable
      (concreteEndpointFringeMinEntries shape blockSize code)
      fieldWidth :=
  FixedWidthNatTable.ofEntries
    (concreteEndpointFringeMinEntries shape blockSize code)
    fieldWidth
    (by
      intro entry hmem
      exact bpPrefixRangeMinExcessEntries_mem_bound hwidth hmem)

def concreteEndpointFringeArgTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    FixedWidthNatTable
      (concreteEndpointFringeArgEntries shape blockSize code)
      fieldWidth :=
  FixedWidthNatTable.ofEntries
    (concreteEndpointFringeArgEntries shape blockSize code)
    fieldWidth
    (by
      intro entry hmem
      exact bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth hmem)

theorem concreteEndpointFringeMinTable_payload_length
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    (concreteEndpointFringeMinTable
      shape blockSize fieldWidth hwidth code).payload.length =
      (2 * blockSize) * fieldWidth := by
  simpa [concreteEndpointFringeMinTable,
    concreteEndpointFringeMinEntries_length] using
    (FixedWidthNatTable.ofEntries
      (concreteEndpointFringeMinEntries shape blockSize code)
      fieldWidth
      (by
        intro entry hmem
        exact bpPrefixRangeMinExcessEntries_mem_bound hwidth hmem)).payload_length

theorem concreteEndpointFringeArgTable_payload_length
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (code : Nat) :
    (concreteEndpointFringeArgTable
      shape blockSize fieldWidth hwidth code).payload.length =
      (2 * blockSize) * fieldWidth := by
  simpa [concreteEndpointFringeArgTable,
    concreteEndpointFringeArgEntries_length] using
    (FixedWidthNatTable.ofEntries
      (concreteEndpointFringeArgEntries shape blockSize code)
      fieldWidth
      (by
        intro entry hmem
        exact bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth hmem)).payload_length

def concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
    (blockSize fieldWidth : Nat) : Nat :=
  2 * ((2 * blockSize) * fieldWidth)

def concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
    (blockCount blockSize fieldWidth : Nat) : Nat :=
  blockCount * fieldWidth +
    blockCount *
      concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        blockSize fieldWidth

private theorem concreteEndpointFringeTablePayload_length
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    ((List.range codeCount).flatMap fun code =>
        (concreteEndpointFringeMinTable
          shape blockSize fieldWidth hwidth code).payload ++
        (concreteEndpointFringeArgTable
          shape blockSize fieldWidth hwidth code).payload).length =
      codeCount *
        concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
          blockSize fieldWidth := by
  induction codeCount with
  | zero =>
      simp [concretePayloadLiveBlockEndpointFringeCodebookTableOverhead]
  | succ codeCount ih =>
      have hrow :
          (blockSize + blockSize) * fieldWidth +
              (blockSize + blockSize) * fieldWidth =
            concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
              blockSize fieldWidth := by
        have htwo : blockSize + blockSize = 2 * blockSize := by
          omega
        rw [htwo]
        unfold concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        omega
      simp [List.range_succ, ih,
        concreteEndpointFringeMinTable_payload_length,
        concreteEndpointFringeArgTable_payload_length,
        hrow, Nat.succ_mul]

def concretePayloadLiveBlockEndpointFringeCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hblockCountWidth : blockCount <= shape.bpCode.length)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBlockEndpointFringeCodebook shape blockSize blockCount
      blockCount fieldWidth (blockCount * fieldWidth) fieldWidth
      (concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        blockSize fieldWidth) where
  classifier :=
    BlockCodeTable.ofEntries blockCount blockCount fieldWidth
      (blockCount * fieldWidth) (List.range blockCount)
      (by
        intro code hmem
        exact Nat.lt_trans
          (Nat.lt_of_lt_of_le (List.mem_range.mp hmem)
            hblockCountWidth)
          hwidth)
      (by simp)
      (by simp)
      (by
        intro block code hget
        by_cases hblock : block < blockCount
        · simp [List.getElem?_range hblock] at hget
          cases hget
          exact hblock
        · simp [hblock] at hget)
  minEntriesByCode :=
    fun code => concreteEndpointFringeMinEntries shape blockSize code
  argEntriesByCode :=
    fun code => concreteEndpointFringeArgEntries shape blockSize code
  minTable :=
    fun code => concreteEndpointFringeMinTable
      shape blockSize fieldWidth hwidth code
  argTable :=
    fun code => concreteEndpointFringeArgTable
      shape blockSize fieldWidth hwidth code
  tablePayload :=
    (List.range blockCount).flatMap fun code =>
      (concreteEndpointFringeMinTable
        shape blockSize fieldWidth hwidth code).payload ++
      (concreteEndpointFringeArgTable
        shape blockSize fieldWidth hwidth code).payload
  tablePayload_eq_tables := rfl
  tablePayload_length_eq := by
    exact concreteEndpointFringeTablePayload_length
      shape blockSize blockCount fieldWidth hwidth
  table_payload_length_eq := by
    intro code _hcode
    simp [concreteEndpointFringeMinTable_payload_length,
      concreteEndpointFringeArgTable_payload_length,
      concretePayloadLiveBlockEndpointFringeCodebookTableOverhead]
    omega
  block_fringe_entries := by
    intro block code hcodeAt
    have hget : (List.range blockCount)[block]? = some code := by
      simpa [BlockCodeTable.codeAt, BlockCodeTable.ofEntries] using hcodeAt
    by_cases hblock : block < blockCount
    · simp [List.getElem?_range hblock] at hget
      cases hget
      simp [concreteEndpointFringeMinEntries,
        concreteEndpointFringeArgEntries]
    · simp [hblock] at hget

theorem concretePayloadLiveBlockEndpointFringeCodebook_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hblockCountWidth : blockCount <= shape.bpCode.length)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let fringe :=
      concretePayloadLiveBlockEndpointFringeCodebook
        shape blockSize blockCount fieldWidth hblockCountWidth hwidth
    fringe.payload.length =
        concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
          blockCount blockSize fieldWidth /\
      (forall close,
        (fringe.leftFringeCosted close).cost <= 3 /\
          (fringe.rightFringeCosted close).cost <= 3) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.leftFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape (close + 1)
                  (blockStartOf blockSize
                      (blockOfClose blockSize close) +
                    blockSize - close),
                  bpPrefixRangeArgMinPrefixPos shape (close + 1)
                    (blockStartOf blockSize
                        (blockOfClose blockSize close) +
                      blockSize - close))) /\
      (forall {close : Nat},
        0 < blockSize ->
          blockOfClose blockSize close < blockCount ->
            (fringe.rightFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape
                  (blockStartOf blockSize
                    (blockOfClose blockSize close))
                  (close -
                      blockStartOf blockSize
                        (blockOfClose blockSize close) +
                    2),
                  bpPrefixRangeArgMinPrefixPos shape
                    (blockStartOf blockSize
                      (blockOfClose blockSize close))
                    (close -
                        blockStartOf blockSize
                          (blockOfClose blockSize close) +
                      2))) /\
      forall {slot block : Nat} {word : List Bool},
        word ∈ fringe.wordsReadAtBlock slot block ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let fringe :=
    concretePayloadLiveBlockEndpointFringeCodebook
      shape blockSize blockCount fieldWidth hblockCountWidth hwidth
  have hprofile := fringe.profile
  constructor
  · simpa [concretePayloadLiveBlockEndpointFringeCodebookPayloadLength]
      using hprofile.1
  constructor
  · exact hprofile.2.1
  constructor
  · exact hprofile.2.2.1
  constructor
  · exact hprofile.2.2.2
  · intro slot block word hmem
    exact fringe.read_words_length_le_machine hmachine hmachine hmem

def concretePayloadLiveBlockEndpointFringeCodebook_canonical
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBlockEndpointFringeCodebook shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (canonicalBPRelativeSummaryBlockCount shape *
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (concretePayloadLiveBlockEndpointFringeCodebookTableOverhead
        (canonicalBPRelativeSummaryBlockSize shape)
        (SuccinctRankProposal.machineWordBits shape.bpCode.length)) :=
  concretePayloadLiveBlockEndpointFringeCodebook
    shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (canonicalBPRelativeSummaryBlockCount_le_bpCode_length shape)
    (by
      simpa [canonicalBPRelativeSummarySuperWidth] using
        canonicalBPRelativeSummary_superWidth_bound shape)

theorem concretePayloadLiveBlockEndpointFringeCodebook_canonical_profile
    (shape : Cartesian.CartesianShape) :
    let fringe :=
      concretePayloadLiveBlockEndpointFringeCodebook_canonical shape
    fringe.payload.length =
        concretePayloadLiveBlockEndpointFringeCodebookPayloadLength
          (canonicalBPRelativeSummaryBlockCount shape)
          (canonicalBPRelativeSummaryBlockSize shape)
          (SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall close,
        (fringe.leftFringeCosted close).cost <= 3 /\
          (fringe.rightFringeCosted close).cost <= 3) /\
      (forall {close : Nat},
        0 < canonicalBPRelativeSummaryBlockSize shape ->
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <
              canonicalBPRelativeSummaryBlockCount shape ->
            (fringe.leftFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape (close + 1)
                  (blockStartOf
                      (canonicalBPRelativeSummaryBlockSize shape)
                      (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        close) +
                    canonicalBPRelativeSummaryBlockSize shape - close),
                  bpPrefixRangeArgMinPrefixPos shape (close + 1)
                    (blockStartOf
                        (canonicalBPRelativeSummaryBlockSize shape)
                        (blockOfClose
                          (canonicalBPRelativeSummaryBlockSize shape)
                          close) +
                      canonicalBPRelativeSummaryBlockSize shape - close))) /\
      (forall {close : Nat},
        0 < canonicalBPRelativeSummaryBlockSize shape ->
          blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <
              canonicalBPRelativeSummaryBlockCount shape ->
            (fringe.rightFringeCosted close).erase =
              some
                (bpPrefixRangeMinExcess shape
                  (blockStartOf
                    (canonicalBPRelativeSummaryBlockSize shape)
                    (blockOfClose
                      (canonicalBPRelativeSummaryBlockSize shape)
                      close))
                  (close -
                      blockStartOf
                        (canonicalBPRelativeSummaryBlockSize shape)
                        (blockOfClose
                          (canonicalBPRelativeSummaryBlockSize shape)
                          close) +
                    2),
                  bpPrefixRangeArgMinPrefixPos shape
                    (blockStartOf
                      (canonicalBPRelativeSummaryBlockSize shape)
                      (blockOfClose
                        (canonicalBPRelativeSummaryBlockSize shape)
                        close))
                    (close -
                        blockStartOf
                          (canonicalBPRelativeSummaryBlockSize shape)
                          (blockOfClose
                            (canonicalBPRelativeSummaryBlockSize shape)
                            close) +
                      2))) /\
      forall {slot block : Nat} {word : List Bool},
        word ∈ fringe.wordsReadAtBlock slot block ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simpa [concretePayloadLiveBlockEndpointFringeCodebook_canonical] using
    concretePayloadLiveBlockEndpointFringeCodebook_profile
      shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (SuccinctRankProposal.machineWordBits shape.bpCode.length)
      (canonicalBPRelativeSummaryBlockCount_le_bpCode_length shape)
      (by
        simpa [canonicalBPRelativeSummarySuperWidth] using
          canonicalBPRelativeSummary_superWidth_bound shape)
      (Nat.le_refl _)


end SuccinctCloseProposal
end RMQ
