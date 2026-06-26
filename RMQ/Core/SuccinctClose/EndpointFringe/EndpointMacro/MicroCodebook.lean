import RMQ.Core.SuccinctClose.EndpointFringe.EndpointMacro.RangeMacro

/-!
# Endpoint-fringe micro-codebook fallback

Block-code tables, micro-codebook fallback directories, and the guarded
endpoint-fringe macro/micro close-LCA directory. Declarations live in the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace
/--
The right-spine shape of size four is the smallest useful witness that a macro
entry keyed only by the pair of endpoint close blocks cannot be exact.
-/
def blockPairMacroBlockerShape : Cartesian.CartesianShape :=
  Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
    (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
      (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
        (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
          Cartesian.CartesianShape.empty)))

/--
A concrete blocker for the tempting compact macro layout keyed only by
`(blockOfClose leftClose, blockOfClose rightClose)`.

For `blockSize = 3`, the two valid queries `[1, 4)` and `[2, 4)` in the
right-spine shape have endpoint closes in the same pair of close blocks, but
their BP-LCA close answers are different (`3` and `5`).  Therefore a macro
directory whose inter-block entry is only a function of the endpoint block pair
cannot satisfy the close-LCA exactness contract.
-/
theorem blockPairMacroDirectory_not_sufficient
    (blockAnswer : Nat -> Nat -> Option Nat) :
    ¬ (forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= blockPairMacroBlockerShape.size ->
          bpCloseOfInorder? blockPairMacroBlockerShape left = some leftClose ->
            bpCloseOfInorder? blockPairMacroBlockerShape
                (left + len - 1) =
              some rightClose ->
              bpCloseOfInorder? blockPairMacroBlockerShape
                  (scanWindow blockPairMacroBlockerShape.representative
                    left len) =
                some answerClose ->
                blockAnswer (blockOfClose 3 leftClose)
                    (blockOfClose 3 rightClose) =
                  some answerClose) := by
  intro hexact
  have hfirst :
      blockAnswer (blockOfClose 3 3) (blockOfClose 3 7) = some 3 := by
    exact
      hexact (left := 1) (len := 3) (leftClose := 3)
        (rightClose := 7) (answerClose := 3)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hsecond :
      blockAnswer (blockOfClose 3 5) (blockOfClose 3 7) = some 5 := by
    exact
      hexact (left := 2) (len := 2) (leftClose := 5)
        (rightClose := 7) (answerClose := 5)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hfirstKey :
      blockAnswer (blockOfClose 3 5) (blockOfClose 3 7) = some 3 := by
    simpa [blockOfClose] using hfirst
  rw [hsecond] at hfirstKey
  simp at hfirstKey

/--
Endpoint summary key for the tempting "read the endpoint block summaries, then
answer by key" macro shortcut.

This records exactly the information returned by the existing min/max summary
layer for one endpoint block: the block id plus that block's sampled minimum
and maximum BP excess.
-/
def endpointSummaryBlockKey
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    Nat × (Nat × Nat) :=
  let block := blockOfClose blockSize close
  (block,
    (bpBlockMinExcess shape blockSize block,
      bpBlockMaxExcess shape blockSize block))

/--
Reading only the two endpoint block min/max summaries still cannot be a global
macro answer.

On the same four-node right spine as `blockPairMacroDirectory_not_sufficient`,
the queries `[1, 4)` and `[2, 4)` have the same endpoint summary keys at
`blockSize = 3`, because their endpoints fall in the same two BP blocks.  Their
correct close answers are nevertheless different.  A concrete macro therefore
needs position-bearing endpoint/fringe or range-min witnesses; the existing
summary values alone are not enough to determine the answer close.
-/
theorem endpointSummaryBlockMacroDirectory_not_sufficient
    (summaryAnswer :
      (Nat × (Nat × Nat)) -> (Nat × (Nat × Nat)) -> Option Nat) :
    ¬ (forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= blockPairMacroBlockerShape.size ->
          bpCloseOfInorder? blockPairMacroBlockerShape left = some leftClose ->
            bpCloseOfInorder? blockPairMacroBlockerShape
                (left + len - 1) =
              some rightClose ->
              bpCloseOfInorder? blockPairMacroBlockerShape
                  (scanWindow blockPairMacroBlockerShape.representative
                    left len) =
                some answerClose ->
                summaryAnswer
                    (endpointSummaryBlockKey
                      blockPairMacroBlockerShape 3 leftClose)
                    (endpointSummaryBlockKey
                      blockPairMacroBlockerShape 3 rightClose) =
                  some answerClose) := by
  intro hexact
  have hfirst :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 3)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 3 := by
    exact
      hexact (left := 1) (len := 3) (leftClose := 3)
        (rightClose := 7) (answerClose := 3)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hsecond :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 5)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 5 := by
    exact
      hexact (left := 2) (len := 2) (leftClose := 5)
        (rightClose := 7) (answerClose := 5)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hfirstKey :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 5)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 3 := by
    simpa [endpointSummaryBlockKey, blockOfClose] using hfirst
  rw [hsecond] at hfirstKey
  simp at hfirstKey

/--
Payload-live table of per-block close/LCA micro-codes.

The old `BlockMicroCodebook` stores only the finite codebook payload and takes
`codeOfBlock` as proof-side data.  This table is the missing charged classifier:
one fixed-width payload word per block is read to recover the code used for the
local close/LCA table.
-/
structure BlockCodeTable
    (blockCount codeCount codeWidth overhead : Nat) where
  codes : List Nat
  table : FixedWidthNatTable codes codeWidth
  codes_length_eq : codes.length = blockCount
  payload_length_eq : table.payload.length = overhead
  code_lt :
    forall {block code : Nat}, codes[block]? = some code -> code < codeCount

namespace BlockCodeTable

def payload
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) : List Bool :=
  classifier.table.payload

def codeAt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) : Option Nat :=
  classifier.codes[block]?

def codeCosted
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) : Costed (Option Nat) :=
  classifier.table.readCosted block

theorem payload_length
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) :
    classifier.payload.length = overhead := by
  exact classifier.payload_length_eq

theorem codeCosted_cost
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).cost = 1 := by
  simp [codeCosted]

theorem codeCosted_cost_le_one
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).cost <= 1 := by
  simp [classifier.codeCosted_cost block]

theorem codeCosted_erase
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).erase = classifier.codeAt block := by
  simp [codeCosted, codeAt]

theorem codeCosted_exact_of_codeAt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block code : Nat}
    (hcode : classifier.codeAt block = some code) :
    (classifier.codeCosted block).erase = some code := by
  simpa [hcode] using classifier.codeCosted_erase block

theorem codeAt_lt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block code : Nat}
    (hcode : classifier.codeAt block = some code) :
    code < codeCount := by
  exact classifier.code_lt (by simpa [codeAt] using hcode)

private theorem list_get?_exists_of_lt
    {α : Type} (xs : List α) {idx : Nat}
    (hidx : idx < xs.length) :
    exists value, xs[idx]? = some value := by
  induction xs generalizing idx with
  | nil =>
      simp at hidx
  | cons head tail ih =>
      cases idx with
      | zero =>
          exact ⟨head, by simp⟩
      | succ idx =>
          have htail : idx < tail.length := by
            simp at hidx
            exact hidx
          rcases ih htail with ⟨value, hvalue⟩
          exact ⟨value, by simpa using hvalue⟩

theorem codeAt_exists_of_lt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block : Nat}
    (hblock : block < blockCount) :
    exists code, classifier.codeAt block = some code := by
  have hidx : block < classifier.codes.length := by
    rw [classifier.codes_length_eq]
    exact hblock
  simpa [codeAt] using list_get?_exists_of_lt classifier.codes hidx

theorem profile
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) :
    classifier.payload.length = overhead /\
      classifier.codes.length = blockCount /\
      forall block : Nat,
        (classifier.codeCosted block).cost <= 1 /\
          (classifier.codeCosted block).erase =
            classifier.codeAt block /\
          forall {code : Nat},
            classifier.codeAt block = some code -> code < codeCount := by
  constructor
  · exact classifier.payload_length
  constructor
  · exact classifier.codes_length_eq
  intro block
  constructor
  · exact classifier.codeCosted_cost_le_one block
  constructor
  · exact classifier.codeCosted_erase block
  intro code hcode
  exact classifier.codeAt_lt hcode

def ofEntries
    (blockCount codeCount codeWidth overhead : Nat)
    (codes : List Nat)
    (hwidth :
      forall {code : Nat}, List.Mem code codes -> code < 2 ^ codeWidth)
    (hlength : codes.length = blockCount)
    (hoverhead : codes.length * codeWidth = overhead)
    (hcode :
      forall {block code : Nat}, codes[block]? = some code ->
        code < codeCount) :
    BlockCodeTable blockCount codeCount codeWidth overhead where
  codes := codes
  table := FixedWidthNatTable.ofEntries codes codeWidth hwidth
  codes_length_eq := hlength
  payload_length_eq := by
    simpa [hoverhead] using
      (FixedWidthNatTable.ofEntries codes codeWidth hwidth).payload_length
  code_lt := hcode

theorem ofEntries_profile
    (blockCount codeCount codeWidth overhead : Nat)
    (codes : List Nat)
    (hwidth :
      forall {code : Nat}, List.Mem code codes -> code < 2 ^ codeWidth)
    (hlength : codes.length = blockCount)
    (hoverhead : codes.length * codeWidth = overhead)
    (hcode :
      forall {block code : Nat}, codes[block]? = some code ->
        code < codeCount) :
    (ofEntries blockCount codeCount codeWidth overhead codes hwidth
      hlength hoverhead hcode).payload.length = overhead /\
      (ofEntries blockCount codeCount codeWidth overhead codes hwidth
        hlength hoverhead hcode).codes.length = blockCount /\
      forall block : Nat,
        ((ofEntries blockCount codeCount codeWidth overhead codes hwidth
          hlength hoverhead hcode).codeCosted block).cost <= 1 /\
          ((ofEntries blockCount codeCount codeWidth overhead codes hwidth
            hlength hoverhead hcode).codeCosted block).erase =
            (ofEntries blockCount codeCount codeWidth overhead codes hwidth
              hlength hoverhead hcode).codeAt block /\
          forall {code : Nat},
            (ofEntries blockCount codeCount codeWidth overhead codes hwidth
              hlength hoverhead hcode).codeAt block = some code ->
              code < codeCount := by
  exact
    (ofEntries blockCount codeCount codeWidth overhead codes hwidth
      hlength hoverhead hcode).profile

end BlockCodeTable

/--
Reusable micro-codebook for block-local BP close/LCA tables.

The dense table from `BlockLocalBPCloseLCATable.concrete` is no longer charged
once per block here.  Each block carries a small code into a finite codebook,
and the counted micro payload is the concatenation of the table payloads for
those codes.  This is the micro half that a real macro/micro BP navigation
scheme can consume.

This compatibility skeleton still takes `codeOfBlock` as a supplied classifier.
`PayloadLiveBlockMicroCodebook` below is the counted successor that stores and
reads that classifier from payload bits.
-/
structure BlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount tableOverhead : Nat) where
  fieldWidth : Nat
  entriesByCode : Nat -> List (Option Nat)
  table :
    (code : Nat) ->
      FixedWidthOptionNatTable (entriesByCode code) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  codeOfBlock : Nat -> Nat
  codeOfBlock_lt : forall block, codeOfBlock block < codeCount
  payload : List Bool
  payload_eq_tables :
    payload =
      (List.range codeCount).flatMap fun code => (table code).payload
  payload_length_eq : payload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (table code).payload.length = tableOverhead
  block_spec :
    forall block : Nat,
      BlockLocalBPCloseLCASpec shape
        (blockStartOf blockSize block) blockSize
        (entriesByCode (codeOfBlock block)) slotIndex

namespace BlockMicroCodebook

def tableForBlock
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block : Nat) :
    FixedWidthOptionNatTable
      (micro.entriesByCode (micro.codeOfBlock block)) micro.fieldWidth :=
  micro.table (micro.codeOfBlock block)

def lcaCloseCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    ((micro.tableForBlock block).readCosted
      (micro.slotIndex
        (leftClose - blockStartOf blockSize block)
        (rightClose - blockStartOf blockSize block)))

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  micro.lcaCloseCostedAtBlock
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead) :
    micro.payload.length = codeCount * tableOverhead := by
  exact micro.payload_length_eq

theorem lcaCloseCostedAtBlock_cost
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost = 1 := by
  simp [lcaCloseCostedAtBlock, Costed.map_cost]

theorem lcaCloseCostedAtBlock_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost <= 1 := by
  simp [micro.lcaCloseCostedAtBlock_cost block leftClose rightClose]

theorem lcaCloseCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (leftClose rightClose : Nat) :
    (micro.lcaCloseCosted leftClose rightClose).cost <= 1 := by
  unfold lcaCloseCosted
  exact micro.lcaCloseCostedAtBlock_cost_le_one
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem lcaCloseCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    {block left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hleftLo : blockStartOf blockSize block <= leftClose)
    (hleftHi :
      leftClose < blockStartOf blockSize block + blockSize)
    (hrightLo : blockStartOf blockSize block <= rightClose)
    (hrightHi :
      rightClose < blockStartOf blockSize block + blockSize)
    (hanswerLo : blockStartOf blockSize block <= answerClose)
    (hanswerHi :
      answerClose < blockStartOf blockSize block + blockSize) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).erase =
      some answerClose := by
  exact
    blockLocalBPCloseLCA_read_exact
      (micro.tableForBlock block) (micro.block_spec block)
      hlen hbound hleft hright hanswer hleftLo hleftHi
      hrightLo hrightHi hanswerLo hanswerHi

theorem lcaCloseCosted_exact_of_left_block
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (hblockSize : 0 < blockSize)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hrightLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        rightClose)
    (hrightHi :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize)
    (hanswerLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        answerClose)
    (hanswerHi :
      answerClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (micro.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  unfold lcaCloseCosted
  exact
    micro.lcaCloseCostedAtBlock_exact hlen hbound hleft hright hanswer
      blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)
      hrightLo hrightHi hanswerLo hanswerHi

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead) :
    micro.payload.length = codeCount * tableOverhead /\
      (forall leftClose rightClose,
        (micro.lcaCloseCosted leftClose rightClose).cost <= 1) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockStartOf blockSize
                        (blockOfClose blockSize leftClose) <=
                      rightClose ->
                    rightClose <
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize ->
                    blockStartOf blockSize
                        (blockOfClose blockSize leftClose) <=
                      answerClose ->
                    answerClose <
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize ->
                      (micro.lcaCloseCosted
                        leftClose rightClose).erase =
                        some answerClose) := by
  constructor
  · exact micro.payload_length
  constructor
  · intro leftClose rightClose
    exact micro.lcaCloseCosted_cost_le_one leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer hblockSize hrightLo hrightHi hanswerLo hanswerHi
  exact
    micro.lcaCloseCosted_exact_of_left_block hblockSize hlen hbound hleft
      hright hanswer hrightLo hrightHi hanswerLo hanswerHi

end BlockMicroCodebook

/--
Payload-live micro-codebook for BP close/LCA.

The query first performs a counted read from `classifier` to recover the
per-block code, then performs a counted read from the corresponding finite
codebook table.  The charged payload is exactly the classifier payload followed
by the finite codebook payload; no dense per-block close/LCA table is charged.
-/
structure PayloadLiveBlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat) where
  classifier :
    BlockCodeTable blockCount codeCount codeWidth codeOverhead
  fieldWidth : Nat
  entriesByCode : Nat -> List (Option Nat)
  table :
    (code : Nat) ->
      FixedWidthOptionNatTable (entriesByCode code) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  tablePayload : List Bool
  tablePayload_eq_tables :
    tablePayload =
      (List.range codeCount).flatMap fun code => (table code).payload
  tablePayload_length_eq : tablePayload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (table code).payload.length = tableOverhead
  block_spec :
    forall {block code : Nat},
      classifier.codeAt block = some code ->
        BlockLocalBPCloseLCASpec shape
          (blockStartOf blockSize block) blockSize
          (entriesByCode code) slotIndex

namespace PayloadLiveBlockMicroCodebook

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) : List Bool :=
  micro.classifier.payload ++ micro.tablePayload

def lcaCloseCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (block leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (micro.classifier.codeCosted block) fun code? =>
    match code? with
    | none => Costed.pure none
    | some code =>
        if _hcode : code < codeCount then
          Costed.map (fun entry? => entry?.join)
            ((micro.table code).readCosted
              (micro.slotIndex
                (leftClose - blockStartOf blockSize block)
                (rightClose - blockStartOf blockSize block)))
        else
          Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  micro.lcaCloseCostedAtBlock
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) :
    micro.payload.length =
      codeOverhead + codeCount * tableOverhead := by
  simp [payload, micro.classifier.payload_length,
    micro.tablePayload_length_eq]

theorem lcaCloseCostedAtBlock_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost <= 2 := by
  unfold lcaCloseCostedAtBlock
  have hclassifier :=
    micro.classifier.codeCosted_cost_le_one block
  cases hread : (micro.classifier.codeCosted block).value with
  | none =>
      simp [Costed.bind, hread]
      omega
  | some code =>
      by_cases hcode : code < codeCount
      · simp [Costed.bind, hread, hcode, Costed.map_cost]
        omega
      · simp [Costed.bind, hread, hcode, Costed.pure]
        omega

theorem lcaCloseCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (leftClose rightClose : Nat) :
    (micro.lcaCloseCosted leftClose rightClose).cost <= 2 := by
  unfold lcaCloseCosted
  exact micro.lcaCloseCostedAtBlock_cost_le_two
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem lcaCloseCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    {block code left len leftClose rightClose answerClose : Nat}
    (hcodeAt : micro.classifier.codeAt block = some code)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hleftLo : blockStartOf blockSize block <= leftClose)
    (hleftHi :
      leftClose < blockStartOf blockSize block + blockSize)
    (hrightLo : blockStartOf blockSize block <= rightClose)
    (hrightHi :
      rightClose < blockStartOf blockSize block + blockSize)
    (hanswerLo : blockStartOf blockSize block <= answerClose)
    (hanswerHi :
      answerClose < blockStartOf blockSize block + blockSize) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).erase =
      some answerClose := by
  have hread :
      (micro.classifier.codeCosted block).value = some code := by
    simpa [Costed.erase] using
      micro.classifier.codeCosted_exact_of_codeAt hcodeAt
  have hcodeLt : code < codeCount :=
    micro.classifier.codeAt_lt hcodeAt
  have hlocal :
      (Costed.map (fun entry? => entry?.join)
        ((micro.table code).readCosted
          (micro.slotIndex
            (leftClose - blockStartOf blockSize block)
            (rightClose - blockStartOf blockSize block)))).erase =
        some answerClose := by
    exact
      blockLocalBPCloseLCA_read_exact
        (micro.table code) (micro.block_spec hcodeAt)
        hlen hbound hleft hright hanswer hleftLo hleftHi
        hrightLo hrightHi hanswerLo hanswerHi
  simpa [lcaCloseCostedAtBlock, Costed.erase, Costed.bind,
    hread, hcodeLt] using hlocal

theorem lcaCloseCosted_exact_of_left_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (hblockSize : 0 < blockSize)
    {code left len leftClose rightClose answerClose : Nat}
    (hcodeAt :
      micro.classifier.codeAt
          (blockOfClose blockSize leftClose) = some code)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hrightLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        rightClose)
    (hrightHi :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize)
    (hanswerLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        answerClose)
    (hanswerHi :
      answerClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (micro.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  unfold lcaCloseCosted
  exact
    micro.lcaCloseCostedAtBlock_exact hcodeAt hlen hbound hleft hright
      hanswer blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)
      hrightLo hrightHi hanswerLo hanswerHi

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) :
    micro.payload.length =
        codeOverhead + codeCount * tableOverhead /\
      (forall block : Nat,
        (micro.classifier.codeCosted block).cost <= 1 /\
          (micro.classifier.codeCosted block).erase =
            micro.classifier.codeAt block /\
          forall {code : Nat},
            micro.classifier.codeAt block = some code ->
              code < codeCount) /\
      (forall leftClose rightClose,
        (micro.lcaCloseCosted leftClose rightClose).cost <= 2) /\
      (forall {code left len leftClose rightClose answerClose : Nat},
        micro.classifier.codeAt
            (blockOfClose blockSize leftClose) = some code ->
          0 < len ->
            left + len <= shape.size ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  bpCloseOfInorder? shape
                      (scanWindow shape.representative left len) =
                    some answerClose ->
                    0 < blockSize ->
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) <=
                        rightClose ->
                      rightClose <
                        blockStartOf blockSize
                            (blockOfClose blockSize leftClose) +
                          blockSize ->
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) <=
                        answerClose ->
                      answerClose <
                        blockStartOf blockSize
                            (blockOfClose blockSize leftClose) +
                          blockSize ->
                        (micro.lcaCloseCosted
                          leftClose rightClose).erase =
                          some answerClose) := by
  constructor
  · exact micro.payload_length
  constructor
  · intro block
    have hprofile := micro.classifier.profile
    exact hprofile.2.2 block
  constructor
  · intro leftClose rightClose
    exact micro.lcaCloseCosted_cost_le_two leftClose rightClose
  intro code left len leftClose rightClose answerClose hcodeAt hlen hbound
    hleft hright hanswer hblockSize hrightLo hrightHi hanswerLo hanswerHi
  exact
    micro.lcaCloseCosted_exact_of_left_block hblockSize hcodeAt hlen hbound
      hleft hright hanswer hrightLo hrightHi hanswerLo hanswerHi

end PayloadLiveBlockMicroCodebook

/-- Empty fixed-width Nat classifier used by the dense fallback construction. -/
def emptyBlockCodeTable : BlockCodeTable 0 1 0 0 :=
  BlockCodeTable.ofEntries 0 1 0 0 ([] : List Nat)
    (by intro code hmem; cases hmem)
    rfl
    rfl
    (by intro block code hget; cases hget)

/-- Empty optional-Nat table used by the dense fallback construction. -/
def emptyOptionNatTable
    (fieldWidth : Nat) :
    FixedWidthOptionNatTable ([] : List (Option Nat)) fieldWidth :=
  FixedWidthOptionNatTable.ofEntries
    ([] : List (Option Nat)) fieldWidth
    (by intro entry value hmem _hentry; cases hmem)

/--
Payload-live micro phase that always misses.

It still performs the charged classifier read before returning `none`; the
point is to make the dense fallback macro leg below a concrete consumer of the
existing payload-live macro/micro directory surface.
-/
def emptyPayloadLiveBlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat) :
    PayloadLiveBlockMicroCodebook shape blockSize 0 1 0 0 0 where
  classifier := emptyBlockCodeTable
  fieldWidth := fieldWidth
  entriesByCode := fun _ => []
  table := fun _ => emptyOptionNatTable fieldWidth
  slotIndex := densePairSlot blockSize
  tablePayload := []
  tablePayload_eq_tables := by
    simp [emptyOptionNatTable, FixedWidthOptionNatTable.ofEntries,
      FixedWidthOptionNatTable.ofEncodedWords, flattenPayloadWords]
  tablePayload_length_eq := by
    simp
  table_payload_length_eq := by
    intro code _hcode
    simp [emptyOptionNatTable, FixedWidthOptionNatTable.ofEntries,
      FixedWidthOptionNatTable.ofEncodedWords, flattenPayloadWords]
  block_spec := by
    intro block code hcodeAt
    have hnone : (emptyBlockCodeTable.codeAt block) = none := by
      simp [emptyBlockCodeTable, BlockCodeTable.codeAt,
        BlockCodeTable.ofEntries]
    rw [hnone] at hcodeAt
    cases hcodeAt

theorem emptyPayloadLiveBlockMicroCodebook_lcaCloseCosted_erase
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth leftClose rightClose : Nat) :
    ((emptyPayloadLiveBlockMicroCodebook
      shape blockSize fieldWidth).lcaCloseCosted
        leftClose rightClose).erase = none := by
  have hcode :
      (emptyBlockCodeTable.codeCosted
        (blockOfClose blockSize leftClose)).value = none := by
    have h :=
      emptyBlockCodeTable.codeCosted_erase
        (blockOfClose blockSize leftClose)
    simpa [Costed.erase, emptyBlockCodeTable, BlockCodeTable.codeAt,
      BlockCodeTable.ofEntries] using h
  unfold PayloadLiveBlockMicroCodebook.lcaCloseCosted
    PayloadLiveBlockMicroCodebook.lcaCloseCostedAtBlock
  simp [emptyPayloadLiveBlockMicroCodebook, hcode, Costed.bind,
    Costed.pure]

/--
Macro/micro BP close/LCA query skeleton.

The micro codebook gets the first constant-time attempt.  If it misses, the
query falls back to an explicit macro component.  The exactness field matches
this control flow instead of pretending that a real macro/micro navigation
structure is still a single fixed-width table read.
-/
structure MacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount microTableOverhead macroOverhead macroCost : Nat)
    where
  micro :
    BlockMicroCodebook shape blockSize codeCount microTableOverhead
  macroPayload : List Bool
  macroPayload_length_eq : macroPayload.length = macroOverhead
  macroCosted : Nat -> Nat -> Costed (Option Nat)
  macro_cost_le :
    forall leftClose rightClose,
      (macroCosted leftClose rightClose).cost <= macroCost
  split_exact :
    forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
            bpCloseOfInorder? shape (left + len - 1) =
                some rightClose ->
              bpCloseOfInorder? shape
                  (scanWindow shape.representative left len) =
                some answerClose ->
                (micro.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose \/
                  ((micro.lcaCloseCosted leftClose rightClose).erase =
                      none /\
                    (macroCosted leftClose rightClose).erase =
                      some answerClose)

namespace MacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) : List Bool :=
  directory.micro.payload ++ directory.macroPayload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.micro.lcaCloseCosted leftClose rightClose)
    fun local? =>
      match local? with
      | some answerClose => Costed.pure (some answerClose)
      | none => directory.macroCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) :
    directory.payload.length =
      codeCount * microTableOverhead + macroOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroPayload_length_eq]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      1 + macroCost := by
  unfold lcaCloseCosted
  have hmicro :=
    directory.micro.lcaCloseCosted_cost_le_one leftClose rightClose
  cases hlocal :
      (directory.micro.lcaCloseCosted leftClose rightClose).value with
  | none =>
      have hmacro := directory.macro_cost_le leftClose rightClose
      simp [Costed.bind, hlocal]
      omega
  | some answerClose =>
      simp [Costed.bind, Costed.pure, hlocal]
      omega

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
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
  have hsplit :=
    directory.split_exact hlen hbound hleft hright hanswer
  unfold lcaCloseCosted
  cases hsplit with
  | inl hlocalExact =>
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hlocalExact
      simp [Costed.bind, Costed.pure, Costed.erase, hlocalValue]
  | inr hfallback =>
      rcases hfallback with ⟨hlocalNone, hmacroExact⟩
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            none := by
        simpa [Costed.erase] using hlocalNone
      have hmacroValue :
          (directory.macroCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hmacroExact
      simp [Costed.bind, Costed.erase, hlocalValue, hmacroValue]

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) :
    directory.payload.length =
        codeCount * microTableOverhead + macroOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          1 + macroCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end MacroMicroBPCloseLCADirectory

/--
Payload-live macro/micro BP close/LCA directory.

This is the counted successor to `MacroMicroBPCloseLCADirectory`: the micro
phase reads a stored per-block code before reading the codebook table.  The
macro component remains an explicit interface, but its payload length, query
cost, and fallback exactness are all exposed here.
-/
structure PayloadLiveMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroPayload : List Bool
  macroPayload_length_eq : macroPayload.length = macroOverhead
  macroCosted : Nat -> Nat -> Costed (Option Nat)
  macro_cost_le :
    forall leftClose rightClose,
      (macroCosted leftClose rightClose).cost <= macroCost
  split_exact :
    forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
            bpCloseOfInorder? shape (left + len - 1) =
                some rightClose ->
              bpCloseOfInorder? shape
                  (scanWindow shape.representative left len) =
                some answerClose ->
                (micro.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose \/
                  ((micro.lcaCloseCosted leftClose rightClose).erase =
                      none /\
                    (macroCosted leftClose rightClose).erase =
                      some answerClose)

namespace PayloadLiveMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) : List Bool :=
  directory.micro.payload ++ directory.macroPayload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.micro.lcaCloseCosted leftClose rightClose)
    fun local? =>
      match local? with
      | some answerClose => Costed.pure (some answerClose)
      | none => directory.macroCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead + macroOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroPayload_length_eq]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      2 + macroCost := by
  unfold lcaCloseCosted
  have hmicro :=
    directory.micro.lcaCloseCosted_cost_le_two leftClose rightClose
  cases hlocal :
      (directory.micro.lcaCloseCosted leftClose rightClose).value with
  | none =>
      have hmacro := directory.macro_cost_le leftClose rightClose
      simp [Costed.bind, hlocal]
      omega
  | some answerClose =>
      simp [Costed.bind, Costed.pure, hlocal]
      omega

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
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
  have hsplit :=
    directory.split_exact hlen hbound hleft hright hanswer
  unfold lcaCloseCosted
  cases hsplit with
  | inl hlocalExact =>
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hlocalExact
      simp [Costed.bind, Costed.pure, Costed.erase, hlocalValue]
  | inr hfallback =>
      rcases hfallback with ⟨hlocalNone, hmacroExact⟩
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            none := by
        simpa [Costed.erase] using hlocalNone
      have hmacroValue :
          (directory.macroCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hmacroExact
      simp [Costed.bind, Costed.erase, hlocalValue, hmacroValue]

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead + macroOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          2 + macroCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveMacroMicroBPCloseLCADirectory

/--
Guarded payload-live macro/micro BP close/LCA directory.

Unlike the compatibility `PayloadLiveMacroMicroBPCloseLCADirectory`, this query
does not ask the micro table about cross-block endpoints.  Same-block queries
use the charged micro-codebook path; cross-block queries use the charged
endpoint-fringe/range macro path.
-/
structure PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroComponent :
    PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
      fieldWidth leftOverhead interiorOverhead rightOverhead
  blockSize_pos : 0 < blockSize
  close_block_lt :
    forall {close : Nat},
      close < shape.bpCode.length ->
        blockOfClose blockSize close < blockCount

namespace PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) : List Bool :=
  directory.micro.payload ++ directory.macroComponent.payload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
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
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead +
        (leftOverhead + interiorOverhead + rightOverhead) := by
  simp [payload, directory.micro.payload_length,
    directory.macroComponent.payload_length]

theorem lcaCloseCosted_cost_le_six
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <= 6 := by
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    have hmicro :=
      directory.micro.lcaCloseCosted_cost_le_two leftClose rightClose
    omega
  · simp [hsame]
    exact directory.macroComponent.lcaCloseCosted_cost_le_six
      leftClose rightClose

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
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
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead +
          (leftOverhead + interiorOverhead + rightOverhead) /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le_six leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory

def concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount) :
    PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
        fieldWidth))
      (2 * ((interiorBlockPairRanges blockCount).length * fieldWidth))
      (2 * ((endpointRightFringeRanges blockSize blockCount).length *
        fieldWidth)) where
  micro := micro
  macroComponent :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  blockSize_pos := hblockSize
  close_block_lt := hcover

theorem concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount) :
    let directory :=
      concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth hwidth micro hblockSize hcover
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead +
          (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
              fieldWidth) +
            2 * ((interiorBlockPairRanges blockCount).length *
              fieldWidth) +
            2 * ((endpointRightFringeRanges blockSize blockCount).length *
              fieldWidth)) /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  let directory :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  simpa [directory] using directory.profile

theorem guardedEndpointFringeMacroMicroOverhead_littleO
    (microOverhead : Nat -> Nat) (slots : Nat)
    (hmicro : LittleOLinear microOverhead) :
    LittleOLinear
      (fun n => microOverhead n + sampledDirectoryOverhead slots n) := by
  exact LittleOLinear.add hmicro (sampledDirectoryOverhead_littleO slots)

theorem concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth slots n : Nat)
    (microOverhead : Nat -> Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount)
    (hmicroLittle : LittleOLinear microOverhead)
    (hmicroBudget :
      codeOverhead + codeCount * microTableOverhead <= microOverhead n)
    (hmacroBudget :
      2 * ((endpointLeftFringeRanges blockSize blockCount).length *
          fieldWidth) +
        2 * ((interiorBlockPairRanges blockCount).length * fieldWidth) +
        2 * ((endpointRightFringeRanges blockSize blockCount).length *
          fieldWidth) <= sampledDirectoryOverhead slots n) :
    let directory :=
      concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth hwidth micro hblockSize hcover
    LittleOLinear
        (fun n => microOverhead n + sampledDirectoryOverhead slots n) /\
      directory.payload.length <=
        microOverhead n + sampledDirectoryOverhead slots n /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  let directory :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  have hprofile :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  constructor
  · exact guardedEndpointFringeMacroMicroOverhead_littleO
      microOverhead slots hmicroLittle
  constructor
  · rw [hprofile.1]
    omega
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2


end SuccinctClose
end RMQ
