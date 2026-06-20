import RMQ.Core.SuccinctSpace

/-!
# BP close/LCA succinct-navigation proposal

This module keeps the next BP-close step honest.  The existing
`PayloadLiveBPCloseLCADirectory` is a payload-live host interface, but by
itself it can also host a dense all-pairs table.  The block-local predicate
below is the small component theorem a real succinct close/LCA scheme should
feed into that host interface without claiming the global `2*n + o(n)` result
too early.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

/--
Specification for one block-local BP close/LCA table.

The table is keyed by close positions relative to `blockStart`; it is only
responsible for queries whose endpoint closes and answer close all stay inside
the block.  A future macro scheme can combine this with inter-block navigation.
-/
def BlockLocalBPCloseLCASpec
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize : Nat)
    (entries : List (Option Nat))
    (slotIndex : Nat -> Nat -> Nat) : Prop :=
  forall {left len leftClose rightClose answerClose : Nat},
    0 < len ->
      left + len <= shape.size ->
        bpCloseOfInorder? shape left = some leftClose ->
          bpCloseOfInorder? shape (left + len - 1) = some rightClose ->
            bpCloseOfInorder? shape
                (scanWindow shape.representative left len) =
              some answerClose ->
              blockStart <= leftClose ->
                leftClose < blockStart + blockSize ->
                  blockStart <= rightClose ->
                    rightClose < blockStart + blockSize ->
                      blockStart <= answerClose ->
                        answerClose < blockStart + blockSize ->
                          entries[
                              slotIndex (leftClose - blockStart)
                                (rightClose - blockStart)]? =
                            some (some answerClose)

/--
Decode a close parenthesis back to its zero-based inorder index by counting
closing parentheses up to and including that close.

For invalid close positions this is just a total arithmetic decoder.  The
theorem below is the semantic inverse used by the concrete local table.
-/
def closeToInorder
    (shape : Cartesian.CartesianShape) (close : Nat) : Nat :=
  Succinct.rankPrefix false shape.bpCode (close + 1) - 1

theorem closeToInorder_eq_of_bpCloseOfInorder?
    {shape : Cartesian.CartesianShape} {idx close : Nat}
    (hclose : bpCloseOfInorder? shape idx = some close) :
    closeToInorder shape close = idx := by
  unfold closeToInorder
  have hrank := bpCloseOfInorder?_rankFalse_succ shape hclose
  rw [hrank]
  omega

/-- Dense row-major slot for a block-local pair of close positions. -/
def densePairSlot
    (blockSize leftLocal rightLocal : Nat) : Nat :=
  leftLocal * blockSize + rightLocal

theorem densePairSlot_lt
    {blockSize leftLocal rightLocal : Nat}
    (hleft : leftLocal < blockSize)
    (hright : rightLocal < blockSize) :
    densePairSlot blockSize leftLocal rightLocal <
      blockSize * blockSize := by
  unfold densePairSlot
  have hltStep :
      leftLocal * blockSize + rightLocal <
        leftLocal * blockSize + blockSize :=
    Nat.add_lt_add_left hright (leftLocal * blockSize)
  have hstepEq :
      leftLocal * blockSize + blockSize =
        (leftLocal + 1) * blockSize := by
    simpa using (Nat.succ_mul leftLocal blockSize).symm
  have hmul :
      (leftLocal + 1) * blockSize <= blockSize * blockSize :=
    Nat.mul_le_mul_right blockSize (Nat.succ_le_of_lt hleft)
  exact Nat.lt_of_lt_of_le (by simpa [hstepEq] using hltStep) hmul

theorem densePairSlot_div
    {blockSize leftLocal rightLocal : Nat}
    (hright : rightLocal < blockSize) :
    densePairSlot blockSize leftLocal rightLocal / blockSize =
      leftLocal := by
  have hpos : 0 < blockSize := by omega
  unfold densePairSlot
  rw [Nat.mul_comm leftLocal blockSize]
  rw [Nat.mul_add_div hpos]
  rw [Nat.div_eq_of_lt hright]
  omega

theorem densePairSlot_mod
    {blockSize leftLocal rightLocal : Nat}
    (hright : rightLocal < blockSize) :
    densePairSlot blockSize leftLocal rightLocal % blockSize =
      rightLocal := by
  unfold densePairSlot
  rw [Nat.mul_comm leftLocal blockSize]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hright

/--
Concrete local BP close/LCA entry.

The row and column are local close positions inside the block.  Valid close
positions are decoded to inorder indices with `closeToInorder`; valid ordered
pairs store the BP close of the ordinary reference RMQ answer.
-/
def concreteBlockLocalBPCloseLCAEntry?
    (shape : Cartesian.CartesianShape)
    (blockStart leftLocal rightLocal : Nat) : Option Nat :=
  let left := closeToInorder shape (blockStart + leftLocal)
  let right := closeToInorder shape (blockStart + rightLocal)
  if left <= right then
    bpCloseOfInorder? shape
      (scanWindow shape.representative left (right - left + 1))
  else
    none

/-- Dense row-major payload entries for one block-local BP close/LCA table. -/
def concreteBlockLocalBPCloseLCAEntries
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize : Nat) : List (Option Nat) :=
  (List.range (blockSize * blockSize)).map fun slot =>
    concreteBlockLocalBPCloseLCAEntry? shape blockStart
      (slot / blockSize) (slot % blockSize)

theorem concreteBlockLocalBPCloseLCAEntries_length
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize : Nat) :
    (concreteBlockLocalBPCloseLCAEntries
      shape blockStart blockSize).length =
      blockSize * blockSize := by
  simp [concreteBlockLocalBPCloseLCAEntries]

theorem concreteBlockLocalBPCloseLCAEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize fieldWidth : Nat}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    forall {entry : Option Nat} {value : Nat},
      List.Mem entry
          (concreteBlockLocalBPCloseLCAEntries
            shape blockStart blockSize) ->
        entry = some value -> value < 2 ^ fieldWidth := by
  intro entry value hmem hentry
  unfold concreteBlockLocalBPCloseLCAEntries at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, rfl⟩
  dsimp [concreteBlockLocalBPCloseLCAEntry?] at hentry
  by_cases hle :
      closeToInorder shape (blockStart + slot / blockSize) <=
        closeToInorder shape (blockStart + slot % blockSize)
  · simp [hle] at hentry
    exact Nat.lt_trans
      (bpCloseOfInorder?_bounds shape hentry) hwidth
  · simp [hle] at hentry

theorem concreteBlockLocalBPCloseLCAEntries_spec
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize : Nat) :
    BlockLocalBPCloseLCASpec shape blockStart blockSize
      (concreteBlockLocalBPCloseLCAEntries
        shape blockStart blockSize)
      (densePairSlot blockSize) := by
  intro left len leftClose rightClose answerClose
    hlen _hbound hleft hright hanswer hleftLo hleftHi
    hrightLo hrightHi _hanswerLo _hanswerHi
  let leftLocal := leftClose - blockStart
  let rightLocal := rightClose - blockStart
  have hleftLocalLt : leftLocal < blockSize := by
    unfold leftLocal
    omega
  have hrightLocalLt : rightLocal < blockSize := by
    unfold rightLocal
    omega
  have hslotLt :
      densePairSlot blockSize leftLocal rightLocal <
        blockSize * blockSize :=
    densePairSlot_lt hleftLocalLt hrightLocalLt
  have hleftLocalEq : blockStart + leftLocal = leftClose := by
    unfold leftLocal
    omega
  have hrightLocalEq : blockStart + rightLocal = rightClose := by
    unfold rightLocal
    omega
  have hleftDecode :
      closeToInorder shape (blockStart + leftLocal) = left := by
    rw [hleftLocalEq]
    exact closeToInorder_eq_of_bpCloseOfInorder? hleft
  have hrightDecode :
      closeToInorder shape (blockStart + rightLocal) =
        left + len - 1 := by
    rw [hrightLocalEq]
    exact closeToInorder_eq_of_bpCloseOfInorder? hright
  have hordered : left <= left + len - 1 := by omega
  have hlenEq : (left + len - 1) - left + 1 = len := by omega
  have hdiv :
      densePairSlot blockSize leftLocal rightLocal / blockSize =
        leftLocal :=
    densePairSlot_div hrightLocalLt
  have hmod :
      densePairSlot blockSize leftLocal rightLocal % blockSize =
        rightLocal :=
    densePairSlot_mod hrightLocalLt
  have hslotGet :
      (List.range (blockSize * blockSize))[
          densePairSlot blockSize leftLocal rightLocal]? =
        some (densePairSlot blockSize leftLocal rightLocal) := by
    exact List.getElem?_range hslotLt
  change
    (concreteBlockLocalBPCloseLCAEntries shape blockStart blockSize)[
        densePairSlot blockSize leftLocal rightLocal]? =
      some (some answerClose)
  simp [concreteBlockLocalBPCloseLCAEntries, List.getElem?_map, hslotGet,
    concreteBlockLocalBPCloseLCAEntry?, hdiv, hmod, hleftDecode,
    hrightDecode, hordered, hlenEq, hanswer]

/--
Reading a certified block-local close/LCA table returns the certified answer.

This is deliberately a local table theorem, not a global succinct-navigation
claim.  It ties the semantic `BlockLocalBPCloseLCASpec` to the counted
fixed-width optional-Nat table read used by the payload-live BP close/LCA
boundary.
-/
theorem blockLocalBPCloseLCA_read_exact
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize fieldWidth : Nat}
    {entries : List (Option Nat)}
    {slotIndex : Nat -> Nat -> Nat}
    (table : FixedWidthOptionNatTable entries fieldWidth)
    (hspec :
      BlockLocalBPCloseLCASpec shape blockStart blockSize entries slotIndex)
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
    (hleftLo : blockStart <= leftClose)
    (hleftHi : leftClose < blockStart + blockSize)
    (hrightLo : blockStart <= rightClose)
    (hrightHi : rightClose < blockStart + blockSize)
    (hanswerLo : blockStart <= answerClose)
    (hanswerHi : answerClose < blockStart + blockSize) :
    (Costed.map (fun entry? => entry?.join)
      (table.readCosted
        (slotIndex (leftClose - blockStart)
          (rightClose - blockStart)))).erase =
      some answerClose := by
  have hentry :=
    hspec hlen hbound hleft hright hanswer hleftLo hleftHi
      hrightLo hrightHi hanswerLo hanswerHi
  simp [Costed.erase_map, hentry]

/--
Payload-live block-local BP close/LCA table.

This is the local component a genuine succinct navigation directory should
materialize inside one block: the payload is a fixed-width optional-Nat table,
the query performs one counted table read, and exactness is only claimed when
the two endpoint closes and the answer close stay in the block.
-/
structure BlockLocalBPCloseLCATable
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize overhead : Nat) where
  fieldWidth : Nat
  entries : List (Option Nat)
  table : FixedWidthOptionNatTable entries fieldWidth
  slotIndex : Nat -> Nat -> Nat
  payload_length_eq : table.payload.length = overhead
  spec : BlockLocalBPCloseLCASpec
    shape blockStart blockSize entries slotIndex

namespace BlockLocalBPCloseLCATable

def payload
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize overhead : Nat}
    (data :
      BlockLocalBPCloseLCATable shape blockStart blockSize overhead) :
    List Bool :=
  data.table.payload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize overhead : Nat}
    (data :
      BlockLocalBPCloseLCATable shape blockStart blockSize overhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    (data.table.readCosted
      (data.slotIndex (leftClose - blockStart)
        (rightClose - blockStart)))

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize overhead : Nat}
    (data :
      BlockLocalBPCloseLCATable shape blockStart blockSize overhead) :
    data.payload.length = overhead := by
  exact data.payload_length_eq

theorem lcaCloseCosted_cost
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize overhead : Nat}
    (data :
      BlockLocalBPCloseLCATable shape blockStart blockSize overhead)
    (leftClose rightClose : Nat) :
    (data.lcaCloseCosted leftClose rightClose).cost = 1 := by
  simp [lcaCloseCosted, Costed.map_cost]

theorem lcaCloseCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize overhead : Nat}
    (data :
      BlockLocalBPCloseLCATable shape blockStart blockSize overhead)
    (leftClose rightClose : Nat) :
    (data.lcaCloseCosted leftClose rightClose).cost <= 1 := by
  simp [data.lcaCloseCosted_cost leftClose rightClose]

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize overhead : Nat}
    (data :
      BlockLocalBPCloseLCATable shape blockStart blockSize overhead)
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
    (hleftLo : blockStart <= leftClose)
    (hleftHi : leftClose < blockStart + blockSize)
    (hrightLo : blockStart <= rightClose)
    (hrightHi : rightClose < blockStart + blockSize)
    (hanswerLo : blockStart <= answerClose)
    (hanswerHi : answerClose < blockStart + blockSize) :
    (data.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  exact
    blockLocalBPCloseLCA_read_exact data.table data.spec
      hlen hbound hleft hright hanswer hleftLo hleftHi
      hrightLo hrightHi hanswerLo hanswerHi

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockStart blockSize overhead : Nat}
    (data :
      BlockLocalBPCloseLCATable shape blockStart blockSize overhead) :
    data.payload.length = overhead /\
      (forall leftClose rightClose,
        (data.lcaCloseCosted leftClose rightClose).cost <= 1) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  blockStart <= leftClose ->
                    leftClose < blockStart + blockSize ->
                      blockStart <= rightClose ->
                        rightClose < blockStart + blockSize ->
                          blockStart <= answerClose ->
                            answerClose < blockStart + blockSize ->
                              (data.lcaCloseCosted
                                leftClose rightClose).erase =
                                some answerClose := by
  constructor
  · exact data.payload_length
  · constructor
    · intro leftClose rightClose
      exact data.lcaCloseCosted_cost_le_one leftClose rightClose
    · intro left len leftClose rightClose answerClose
        hlen hbound hleft hright hanswer hleftLo hleftHi
        hrightLo hrightHi hanswerLo hanswerHi
      exact data.lcaCloseCosted_exact hlen hbound hleft hright hanswer
        hleftLo hleftHi hrightLo hrightHi hanswerLo hanswerHi

def ofEntries
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize overhead fieldWidth : Nat)
    (entries : List (Option Nat))
    (slotIndex : Nat -> Nat -> Nat)
    (hentryBound :
      forall {entry : Option Nat} {value : Nat},
        List.Mem entry entries -> entry = some value ->
          value < 2 ^ fieldWidth)
    (hlength :
      entries.length * optionNatWordWidth fieldWidth = overhead)
    (hspec :
      BlockLocalBPCloseLCASpec
        shape blockStart blockSize entries slotIndex) :
    BlockLocalBPCloseLCATable shape blockStart blockSize overhead where
  fieldWidth := fieldWidth
  entries := entries
  table := FixedWidthOptionNatTable.ofEntries
    entries fieldWidth hentryBound
  slotIndex := slotIndex
  payload_length_eq := by
    simpa [FixedWidthOptionNatTable.payload_length] using hlength
  spec := hspec

/--
Build the concrete dense block-local BP close/LCA table from the shape's BP
payload.  The only caller obligation is that the fixed field is wide enough to
store any close position in the shape.
-/
def concrete
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    BlockLocalBPCloseLCATable shape blockStart blockSize
      ((blockSize * blockSize) * optionNatWordWidth fieldWidth) :=
  ofEntries shape blockStart blockSize
    ((blockSize * blockSize) * optionNatWordWidth fieldWidth)
    fieldWidth
    (concreteBlockLocalBPCloseLCAEntries shape blockStart blockSize)
    (densePairSlot blockSize)
    (concreteBlockLocalBPCloseLCAEntries_mem_bound hwidth)
    (by
      rw [concreteBlockLocalBPCloseLCAEntries_length])
    (concreteBlockLocalBPCloseLCAEntries_spec shape blockStart blockSize)

theorem ofEntries_profile
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize overhead fieldWidth : Nat)
    (entries : List (Option Nat))
    (slotIndex : Nat -> Nat -> Nat)
    (hentryBound :
      forall {entry : Option Nat} {value : Nat},
        List.Mem entry entries -> entry = some value ->
          value < 2 ^ fieldWidth)
    (hlength :
      entries.length * optionNatWordWidth fieldWidth = overhead)
    (hspec :
      BlockLocalBPCloseLCASpec
        shape blockStart blockSize entries slotIndex) :
    (ofEntries shape blockStart blockSize overhead fieldWidth entries
      slotIndex hentryBound hlength hspec).payload.length = overhead /\
      (forall leftClose rightClose,
        ((ofEntries shape blockStart blockSize overhead fieldWidth entries
          slotIndex hentryBound hlength hspec).lcaCloseCosted
            leftClose rightClose).cost <= 1) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  blockStart <= leftClose ->
                    leftClose < blockStart + blockSize ->
                      blockStart <= rightClose ->
                        rightClose < blockStart + blockSize ->
                          blockStart <= answerClose ->
                            answerClose < blockStart + blockSize ->
                              ((ofEntries shape blockStart blockSize overhead
                                fieldWidth entries slotIndex hentryBound
                                  hlength hspec).lcaCloseCosted
                                    leftClose rightClose).erase =
                                some answerClose := by
  exact
    (ofEntries shape blockStart blockSize overhead fieldWidth entries
      slotIndex hentryBound hlength hspec).profile

theorem concrete_profile
    (shape : Cartesian.CartesianShape)
    (blockStart blockSize fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    ((concrete shape blockStart blockSize fieldWidth hwidth).payload.length =
        (blockSize * blockSize) *
          optionNatWordWidth fieldWidth) /\
      (forall leftClose rightClose,
        ((concrete shape blockStart blockSize fieldWidth hwidth).lcaCloseCosted
          leftClose rightClose).cost <= 1) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  blockStart <= leftClose ->
                    leftClose < blockStart + blockSize ->
                      blockStart <= rightClose ->
                        rightClose < blockStart + blockSize ->
                          blockStart <= answerClose ->
                            answerClose < blockStart + blockSize ->
                              ((concrete shape blockStart blockSize fieldWidth
                                hwidth).lcaCloseCosted
                                  leftClose rightClose).erase =
                                some answerClose := by
  exact
    (concrete shape blockStart blockSize fieldWidth hwidth).profile

end BlockLocalBPCloseLCATable

/-- Block number containing a BP close position. -/
def blockOfClose (blockSize close : Nat) : Nat :=
  close / blockSize

/-- First BP position in a block. -/
def blockStartOf (blockSize block : Nat) : Nat :=
  block * blockSize

theorem blockStartOf_blockOfClose_le
    {blockSize close : Nat} :
    blockStartOf blockSize (blockOfClose blockSize close) <= close := by
  unfold blockStartOf blockOfClose
  have hdiv := Nat.div_add_mod close blockSize
  have hcomm :
      close / blockSize * blockSize =
        blockSize * (close / blockSize) := by
    exact Nat.mul_comm (close / blockSize) blockSize
  omega

theorem close_lt_blockStartOf_blockOfClose_add
    {blockSize close : Nat} (hblockSize : 0 < blockSize) :
    close < blockStartOf blockSize (blockOfClose blockSize close) +
      blockSize := by
  unfold blockStartOf blockOfClose
  have hdiv := Nat.div_add_mod close blockSize
  have hmod := Nat.mod_lt close hblockSize
  have hcomm :
      close / blockSize * blockSize =
        blockSize * (close / blockSize) := by
    exact Nat.mul_comm (close / blockSize) blockSize
  omega

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

end SuccinctCloseProposal
end RMQ
