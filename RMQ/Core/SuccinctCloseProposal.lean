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

end SuccinctCloseProposal
end RMQ
