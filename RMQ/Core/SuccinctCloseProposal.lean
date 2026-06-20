import RMQ.Core.SuccinctRankProposal

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

/--
A fully endpoint-sensitive direct-access BP close/LCA table.

This is a concrete charged macro fallback: it is just the certified block-local
table run with one block covering the whole BP payload.  It is useful as a
baseline because the query is exact and costs one payload-table read, but the
payload is dense in endpoint close positions.
-/
def denseAllCloseBPCloseLCATable
    (shape : Cartesian.CartesianShape)
    (fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    BlockLocalBPCloseLCATable shape 0 shape.bpCode.length
      ((shape.bpCode.length * shape.bpCode.length) *
        optionNatWordWidth fieldWidth) :=
  BlockLocalBPCloseLCATable.concrete shape 0 shape.bpCode.length
    fieldWidth hwidth

theorem denseAllCloseBPCloseLCATable_profile
    (shape : Cartesian.CartesianShape)
    (fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    ((denseAllCloseBPCloseLCATable shape fieldWidth hwidth).payload.length =
        (shape.bpCode.length * shape.bpCode.length) *
          optionNatWordWidth fieldWidth) /\
      (forall leftClose rightClose,
        ((denseAllCloseBPCloseLCATable shape fieldWidth hwidth).lcaCloseCosted
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
                  ((denseAllCloseBPCloseLCATable
                    shape fieldWidth hwidth).lcaCloseCosted
                      leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact
      (denseAllCloseBPCloseLCATable
        shape fieldWidth hwidth).payload_length
  constructor
  · intro leftClose rightClose
    exact
      (denseAllCloseBPCloseLCATable
        shape fieldWidth hwidth).lcaCloseCosted_cost_le_one
          leftClose rightClose
  intro left len leftClose rightClose answerClose
    hlen hbound hleft hright hanswer
  have hleftHi : leftClose < shape.bpCode.length :=
    bpCloseOfInorder?_bounds shape hleft
  have hrightHi : rightClose < shape.bpCode.length :=
    bpCloseOfInorder?_bounds shape hright
  have hanswerHi : answerClose < shape.bpCode.length :=
    bpCloseOfInorder?_bounds shape hanswer
  exact
    (denseAllCloseBPCloseLCATable
      shape fieldWidth hwidth).lcaCloseCosted_exact
        hlen hbound hleft hright hanswer
        (by omega) (by simpa using hleftHi)
        (by omega) (by simpa using hrightHi)
        (by omega) (by simpa using hanswerHi)

/--
The family-level overhead of the dense all-close endpoint table for shapes of
size `n`.  This is deliberately named so the space blocker below can refer to
the concrete direct-access fallback rather than to a vague "quadratic table".
-/
def denseAllCloseBPCloseLCAOverhead
    (fieldWidth : Nat -> Nat) (n : Nat) : Nat :=
  ((2 * n) * (2 * n)) * optionNatWordWidth (fieldWidth n)

theorem denseAllCloseBPCloseLCATable_payload_length_of_shapeOfSize
    {shape : Cartesian.CartesianShape} {n : Nat}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    (fieldWidth : Nat -> Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth n) :
    ((denseAllCloseBPCloseLCATable
      shape (fieldWidth n) hwidth).payload.length =
        denseAllCloseBPCloseLCAOverhead fieldWidth n) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  simpa [denseAllCloseBPCloseLCAOverhead, hbp] using
    (denseAllCloseBPCloseLCATable
      shape (fieldWidth n) hwidth).payload_length

theorem not_littleOLinear_square :
    ¬ LittleOLinear (fun n : Nat => n * n) := by
  intro hsquare
  rcases hsquare 1 (by omega) with ⟨threshold, hthreshold⟩
  let n := Nat.max threshold 2
  have hthreshold_le : threshold <= n := Nat.le_max_left threshold 2
  have htwo_le : 2 <= n := Nat.le_max_right threshold 2
  have hle : n * n <= n := by
    simpa using hthreshold n hthreshold_le
  have hlt : n < n * n := by
    have hone_lt : 1 < n := by omega
    have hpos : 0 < n := by omega
    have hmul : n * 1 < n * n :=
      Nat.mul_lt_mul_of_pos_left hone_lt hpos
    simpa using hmul
  exact (Nat.not_lt_of_ge hle) hlt

theorem denseAllCloseBPCloseLCAOverhead_not_littleO
    (fieldWidth : Nat -> Nat) :
    ¬ LittleOLinear (denseAllCloseBPCloseLCAOverhead fieldWidth) := by
  intro hdense
  have hquad :
      LittleOLinear (fun n : Nat => n * n) := by
    exact hdense.of_le (fun n => by
      unfold denseAllCloseBPCloseLCAOverhead
      have hn_le : n <= 2 * n := by omega
      have hsquare :
          n * n <= (2 * n) * (2 * n) :=
        Nat.mul_le_mul hn_le hn_le
      have hword :
          1 <= optionNatWordWidth (fieldWidth n) := by
        unfold optionNatWordWidth
        omega
      have hdense_ge :
          (2 * n) * (2 * n) <=
            ((2 * n) * (2 * n)) *
              optionNatWordWidth (fieldWidth n) := by
        have hmul :=
          Nat.mul_le_mul_left ((2 * n) * (2 * n)) hword
        simpa using hmul
      exact Nat.le_trans hsquare hdense_ge)
  exact not_littleOLinear_square hquad

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

/-!
## Concrete BP range min/max block summaries

The final BP close/LCA macro needs a charged range-min/max substrate over
block summaries, rather than an all-close endpoint table.  The definitions in
this section build the first concrete payload-live layer for that substrate:
each BP block stores its minimum and maximum prefix excess in fixed-width
payload words, and query lemmas read those payload words back exactly.
-/

/-- BP prefix excess at position `pos`, counted as opens minus closes. -/
def bpExcessAt (shape : Cartesian.CartesianShape) (pos : Nat) : Nat :=
  Succinct.rankPrefix true shape.bpCode pos -
    Succinct.rankPrefix false shape.bpCode pos

theorem bpExcessAt_le_length
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    bpExcessAt shape pos <= shape.bpCode.length := by
  unfold bpExcessAt
  exact Nat.le_trans
    (Nat.sub_le _ _)
    (Succinct.rankPrefix_le_length true shape.bpCode pos)

/--
Balanced-prefix invariant for the `Nat`-subtraction BP excess.

Inside the BP payload bounds, close-rank never exceeds open-rank, so
`bpExcessAt` is the ordinary open-minus-close difference rather than a
saturated subtraction artifact.
-/
theorem bpExcessAt_prefix_nonnegative
    (shape : Cartesian.CartesianShape) {pos : Nat}
    (hpos : pos <= shape.bpCode.length) :
    Succinct.rankPrefix false shape.bpCode pos <=
      Succinct.rankPrefix true shape.bpCode pos := by
  simpa [bpParensOfShape] using
    Succinct.BalancedParens.close_rank_le_open_rank
      (bpParensOfShape shape) (pos := pos) hpos

theorem bpExcessAt_add_close_rank_eq_open_rank_of_le
    (shape : Cartesian.CartesianShape) {pos : Nat}
    (hpos : pos <= shape.bpCode.length) :
    bpExcessAt shape pos +
        Succinct.rankPrefix false shape.bpCode pos =
      Succinct.rankPrefix true shape.bpCode pos := by
  unfold bpExcessAt
  exact Nat.sub_add_cancel (bpExcessAt_prefix_nonnegative shape hpos)

/-- Tail-recursive minimum over a list, seeded by an explicit bound. -/
def natListMinFrom (seed : Nat) : List Nat -> Nat
  | [] => seed
  | value :: rest => natListMinFrom (Nat.min seed value) rest

theorem natListMinFrom_le_seed (seed : Nat) (values : List Nat) :
    natListMinFrom seed values <= seed := by
  induction values generalizing seed with
  | nil =>
      simp [natListMinFrom]
  | cons value rest ih =>
      exact Nat.le_trans
        (ih (Nat.min seed value))
        (Nat.min_le_left seed value)

/-- Maximum over a list, using zero as the empty-list value. -/
def natListMax : List Nat -> Nat
  | [] => 0
  | value :: rest => Nat.max value (natListMax rest)

theorem natListMax_le_of_forall_mem
    {values : List Nat} {bound : Nat}
    (hbound : forall {value : Nat}, List.Mem value values -> value <= bound) :
    natListMax values <= bound := by
  induction values with
  | nil =>
      simp [natListMax]
  | cons value rest ih =>
      have hvalue : value <= bound := hbound List.mem_cons_self
      have hrest : natListMax rest <= bound := by
        exact ih (by
          intro restValue hmem
          exact hbound (List.mem_cons_of_mem value hmem))
      exact Nat.max_le.2 ⟨hvalue, hrest⟩

/-- BP excess samples at the `blockSize + 1` prefix positions of one block. -/
def bpBlockExcessSamples
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) : List Nat :=
  (List.range (blockSize + 1)).map fun offset =>
    bpExcessAt shape (blockStartOf blockSize block + offset)

theorem bpBlockExcessSamples_mem_le_length
    {shape : Cartesian.CartesianShape}
    {blockSize block value : Nat}
    (hmem :
      List.Mem value (bpBlockExcessSamples shape blockSize block)) :
    value <= shape.bpCode.length := by
  unfold bpBlockExcessSamples at hmem
  rcases List.mem_map.mp hmem with ⟨offset, _hoffset, hvalue⟩
  rw [← hvalue]
  exact bpExcessAt_le_length shape
    (blockStartOf blockSize block + offset)

/-- Minimum BP excess sampled inside one block. -/
def bpBlockMinExcess
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) : Nat :=
  natListMinFrom shape.bpCode.length
    (bpBlockExcessSamples shape blockSize block)

/-- Maximum BP excess sampled inside one block. -/
def bpBlockMaxExcess
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) : Nat :=
  natListMax (bpBlockExcessSamples shape blockSize block)

theorem bpBlockMinExcess_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) :
    bpBlockMinExcess shape blockSize block <= shape.bpCode.length := by
  exact natListMinFrom_le_seed shape.bpCode.length
    (bpBlockExcessSamples shape blockSize block)

theorem bpBlockMaxExcess_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) :
    bpBlockMaxExcess shape blockSize block <= shape.bpCode.length := by
  unfold bpBlockMaxExcess
  exact natListMax_le_of_forall_mem
    (by
      intro value hmem
      exact bpBlockExcessSamples_mem_le_length hmem)

/--
Tail-recursive argmin over the sampled BP-prefix positions of a block.

The returned value is a BP prefix position, capped to the payload length, not
only the minimum excess value. This is the position-bearing payload missing from
the earlier min/max-only summaries.
-/
def bpBlockArgMinPrefixPosFrom
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    Nat -> Nat -> Nat
  | 0, best => best
  | steps + 1, best =>
      let sample := Nat.min pos shape.bpCode.length
      let best' :=
        if bpExcessAt shape sample < bpExcessAt shape best then
          sample
        else
          best
      bpBlockArgMinPrefixPosFrom shape (pos + 1) steps best'

theorem bpBlockArgMinPrefixPosFrom_le_length
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat)
    (hbest : best <= shape.bpCode.length) :
    bpBlockArgMinPrefixPosFrom shape pos steps best <=
      shape.bpCode.length := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpBlockArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpBlockArgMinPrefixPosFrom
      by_cases hlt :
          bpExcessAt shape (Nat.min pos shape.bpCode.length) <
            bpExcessAt shape best
      · simp [hlt]
        exact ih (pos + 1) (Nat.min pos shape.bpCode.length)
          (Nat.min_le_right pos shape.bpCode.length)
      · simp [hlt]
        exact ih (pos + 1) best hbest

/-- First sampled prefix position attaining a block-local minimum excess. -/
def bpBlockArgMinPrefixPos
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) : Nat :=
  let start := blockStartOf blockSize block
  bpBlockArgMinPrefixPosFrom shape start (blockSize + 1)
    (Nat.min start shape.bpCode.length)

theorem bpBlockArgMinPrefixPos_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) :
    bpBlockArgMinPrefixPos shape blockSize block <=
      shape.bpCode.length := by
  unfold bpBlockArgMinPrefixPos
  exact bpBlockArgMinPrefixPosFrom_le_length shape
    (blockStartOf blockSize block) (blockSize + 1)
    (Nat.min (blockStartOf blockSize block) shape.bpCode.length)
    (Nat.min_le_right (blockStartOf blockSize block) shape.bpCode.length)

def bpBlockMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockMinExcess shape blockSize block

def bpBlockMaxExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockMaxExcess shape blockSize block

def bpBlockArgMinPrefixPosEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockArgMinPrefixPos shape blockSize block

theorem bpBlockMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    (bpBlockMinExcessEntries shape blockSize blockCount).length =
      blockCount := by
  simp [bpBlockMinExcessEntries]

theorem bpBlockMaxExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    (bpBlockMaxExcessEntries shape blockSize blockCount).length =
      blockCount := by
  simp [bpBlockMaxExcessEntries]

theorem bpBlockArgMinPrefixPosEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    (bpBlockArgMinPrefixPosEntries shape blockSize blockCount).length =
      blockCount := by
  simp [bpBlockArgMinPrefixPosEntries]

theorem bpBlockMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth entry : Nat}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (bpBlockMinExcessEntries shape blockSize blockCount)) :
    entry < 2 ^ fieldWidth := by
  unfold bpBlockMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, _hblock, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpBlockMinExcess_le_length shape blockSize block) hwidth

theorem bpBlockMaxExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth entry : Nat}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (bpBlockMaxExcessEntries shape blockSize blockCount)) :
    entry < 2 ^ fieldWidth := by
  unfold bpBlockMaxExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, _hblock, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpBlockMaxExcess_le_length shape blockSize block) hwidth

theorem bpBlockArgMinPrefixPosEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth entry : Nat}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)) :
    entry < 2 ^ fieldWidth := by
  unfold bpBlockArgMinPrefixPosEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, _hblock, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpBlockArgMinPrefixPos_le_length shape blockSize block) hwidth

/--
Payload-live BP range-min/max summary table.

The min and max summary arrays are concrete fixed-width payload tables.  A
macro directory can read these two charged words before deciding which macro
summary range or endpoint repair to use.
-/
structure PayloadLiveBPRangeMinMaxSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth overhead : Nat) where
  minTable :
    FixedWidthNatTable
      (bpBlockMinExcessEntries shape blockSize blockCount) fieldWidth
  maxTable :
    FixedWidthNatTable
      (bpBlockMaxExcessEntries shape blockSize blockCount) fieldWidth
  payload_length_eq :
    minTable.payload.length + maxTable.payload.length = overhead

namespace PayloadLiveBPRangeMinMaxSummaryTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead) : List Bool :=
  table.minTable.payload ++ table.maxTable.payload

def minExcessCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) : Costed (Option Nat) :=
  table.minTable.readCosted block

def maxExcessCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) : Costed (Option Nat) :=
  table.maxTable.readCosted block

def summaryCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (table.minExcessCosted block) fun min? =>
    Costed.map
      (fun max? =>
        match min?, max? with
        | some minExcess, some maxExcess => some (minExcess, maxExcess)
        | _, _ => none)
      (table.maxExcessCosted block)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem minExcessCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.minExcessCosted block).cost <= 1 := by
  simp [minExcessCosted]

theorem maxExcessCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.maxExcessCosted block).cost <= 1 := by
  simp [maxExcessCosted]

theorem summaryCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.summaryCosted block).cost <= 2 := by
  unfold summaryCosted minExcessCosted maxExcessCosted
  have hmin := table.minTable.readCosted_cost_le_one block
  have hmax := table.maxTable.readCosted_cost_le_one block
  cases hread :
      (table.minTable.readCosted block).value <;>
    simp [Costed.bind, Costed.map, hread]

theorem minExcessCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.minExcessCosted block).erase =
      (bpBlockMinExcessEntries shape blockSize blockCount)[block]? := by
  simp [minExcessCosted]

theorem maxExcessCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.maxExcessCosted block).erase =
      (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? := by
  simp [maxExcessCosted]

theorem summaryCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.summaryCosted block).erase =
      match
        (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
        (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? with
      | some minExcess, some maxExcess => some (minExcess, maxExcess)
      | _, _ => none := by
  unfold summaryCosted
  have hmin :
      (table.minTable.readCosted block).value =
        (bpBlockMinExcessEntries shape blockSize blockCount)[block]? := by
    exact table.minTable.readCosted_erase block
  have hmax :
      (table.maxTable.readCosted block).value =
        (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? := by
    exact table.maxTable.readCosted_erase block
  simp [Costed.bind, Costed.map, Costed.erase, minExcessCosted,
    maxExcessCosted, hmin, hmax]

theorem minExcess_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {block : Nat} {word : List Bool}
    (hword : table.minTable.store.words[block]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := table.minTable.read_word_length_of_some hword
  omega

theorem maxExcess_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {block : Nat} {word : List Bool}
    (hword : table.maxTable.store.words[block]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := table.maxTable.read_word_length_of_some hword
  omega

theorem summary_read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {block : Nat} {word : List Bool},
      table.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  constructor
  · intro block word hword
    exact table.minExcess_read_word_length_le_machine hmachine hword
  · intro block word hword
    exact table.maxExcess_read_word_length_le_machine hmachine hword

theorem payload_length_le_sampled
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead slots n : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hbudget :
      overhead <= sampledDirectoryOverhead slots n) :
    table.payload.length <= sampledDirectoryOverhead slots n := by
  rw [table.payload_length]
  exact hbudget

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
        fieldWidth overhead) :
    table.payload.length = overhead /\
      (forall block,
        (table.minExcessCosted block).cost <= 1 /\
          (table.minExcessCosted block).erase =
            (bpBlockMinExcessEntries shape blockSize blockCount)[block]?) /\
      (forall block,
        (table.maxExcessCosted block).cost <= 1 /\
          (table.maxExcessCosted block).erase =
            (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?) /\
      forall block,
        (table.summaryCosted block).cost <= 2 /\
          (table.summaryCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? with
            | some minExcess, some maxExcess =>
                some (minExcess, maxExcess)
            | _, _ => none := by
  constructor
  · exact table.payload_length
  constructor
  · intro block
    exact ⟨table.minExcessCosted_cost_le_one block,
      table.minExcessCosted_erase block⟩
  constructor
  · intro block
    exact ⟨table.maxExcessCosted_cost_le_one block,
      table.maxExcessCosted_erase block⟩
  intro block
  exact ⟨table.summaryCosted_cost_le_two block,
    table.summaryCosted_erase block⟩

end PayloadLiveBPRangeMinMaxSummaryTable

def concreteBPRangeMinMaxSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
      fieldWidth (2 * (blockCount * fieldWidth)) where
  minTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockMinExcessEntries shape blockSize blockCount)
      fieldWidth
      (by
        intro entry hmem
        exact bpBlockMinExcessEntries_mem_bound hwidth hmem)
  maxTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockMaxExcessEntries shape blockSize blockCount)
      fieldWidth
      (by
        intro entry hmem
        exact bpBlockMaxExcessEntries_mem_bound hwidth hmem)
  payload_length_eq := by
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpBlockMinExcessEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockMinExcessEntries_mem_bound hwidth hmem)).payload.length =
          blockCount * fieldWidth := by
      simpa [bpBlockMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockMinExcessEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockMinExcessEntries_mem_bound hwidth hmem)).payload_length
    have hmax :
        (FixedWidthNatTable.ofEntries
          (bpBlockMaxExcessEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockMaxExcessEntries_mem_bound hwidth hmem)).payload.length =
          blockCount * fieldWidth := by
      simpa [bpBlockMaxExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockMaxExcessEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockMaxExcessEntries_mem_bound hwidth hmem)).payload_length
    omega

theorem concreteBPRangeMinMaxSummaryTable_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let table :=
      concreteBPRangeMinMaxSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    table.payload.length = 2 * (blockCount * fieldWidth) /\
      (forall block,
        (table.minExcessCosted block).cost <= 1 /\
          (table.minExcessCosted block).erase =
            (bpBlockMinExcessEntries shape blockSize blockCount)[block]?) /\
      (forall block,
        (table.maxExcessCosted block).cost <= 1 /\
          (table.maxExcessCosted block).erase =
            (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?) /\
      forall block,
        (table.summaryCosted block).cost <= 2 /\
          (table.summaryCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? with
            | some minExcess, some maxExcess =>
                some (minExcess, maxExcess)
            | _, _ => none := by
  exact
    (concreteBPRangeMinMaxSummaryTable
      shape blockSize blockCount fieldWidth hwidth).profile

theorem concreteBPRangeMinMaxSummaryTable_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * (blockCount * fieldWidth) <= sampledDirectoryOverhead slots n) :
    let table :=
      concreteBPRangeMinMaxSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      table.payload.length <= sampledDirectoryOverhead slots n /\
      (forall block,
        (table.summaryCosted block).cost <= 2 /\
          (table.summaryCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? with
            | some minExcess, some maxExcess =>
                some (minExcess, maxExcess)
            | _, _ => none) := by
  let table :=
    concreteBPRangeMinMaxSummaryTable
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · exact table.payload_length_le_sampled hbudget
  intro block
  exact ⟨table.summaryCosted_cost_le_two block,
    table.summaryCosted_erase block⟩

theorem concreteBPRangeMinMaxSummaryTable_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRangeMinMaxSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    (forall {block : Nat} {word : List Bool},
      table.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPRangeMinMaxSummaryTable.summary_read_words_length_le_machine
      (concreteBPRangeMinMaxSummaryTable
        shape blockSize blockCount fieldWidth hwidth)
      hmachine

/-!
## Position-bearing BP block summaries

The min/max summary table above is not enough to route a close/LCA answer.  The
next concrete payload layer stores the first sampled prefix position attaining a
block-local minimum excess.  This is still not the final answer-close theorem,
but unlike the min/max-only table it carries a charged position witness for the
macro range-min path.
-/

/-- Payload-live min/max summary table plus a charged argmin prefix position. -/
structure PayloadLiveBPRangeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth overhead : Nat) where
  summary :
    PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
      fieldWidth (2 * (blockCount * fieldWidth))
  argTable :
    FixedWidthNatTable
      (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
      fieldWidth
  payload_length_eq :
    summary.payload.length + argTable.payload.length = overhead

namespace PayloadLiveBPRangeMinMaxArgSummaryTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead) : List Bool :=
  table.summary.payload ++ table.argTable.payload

def argMinPrefixPosCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) : Costed (Option Nat) :=
  table.argTable.readCosted block

def summaryArgCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) : Costed (Option (Nat × Nat × Nat)) :=
  Costed.bind (table.summary.summaryCosted block) fun summary? =>
    Costed.map
      (fun arg? =>
        match summary?, arg? with
        | some (minExcess, maxExcess), some argPos =>
            some (minExcess, maxExcess, argPos)
        | _, _ => none)
      (table.argMinPrefixPosCosted block)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem argMinPrefixPosCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.argMinPrefixPosCosted block).cost <= 1 := by
  simp [argMinPrefixPosCosted]

theorem argMinPrefixPosCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.argMinPrefixPosCosted block).erase =
      (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]? := by
  simp [argMinPrefixPosCosted]

theorem summaryArgCosted_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.summaryArgCosted block).cost <= 3 := by
  unfold summaryArgCosted argMinPrefixPosCosted
  have hsummary := table.summary.summaryCosted_cost_le_two block
  have harg := table.argTable.readCosted_cost_le_one block
  cases hread : (table.summary.summaryCosted block).value with
  | none =>
      simp [Costed.bind, Costed.map, hread]
      omega
  | some value =>
      simp [Costed.bind, Costed.map, hread]
      omega

theorem summaryArgCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.summaryArgCosted block).erase =
      match
        (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
        (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
        (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]? with
      | some minExcess, some maxExcess, some argPos =>
          some (minExcess, maxExcess, argPos)
      | _, _, _ => none := by
  unfold summaryArgCosted
  have hsummary :
      (table.summary.summaryCosted block).value =
        match
          (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
          (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? with
        | some minExcess, some maxExcess => some (minExcess, maxExcess)
        | _, _ => none := by
    simpa [Costed.erase] using table.summary.summaryCosted_erase block
  have harg :
      (table.argTable.readCosted block).value =
        (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]? := by
    exact table.argTable.readCosted_erase block
  cases hmin : (bpBlockMinExcessEntries shape blockSize blockCount)[block]?
  <;> cases hmax :
    (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?
  <;> cases hargEntry :
    (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, argMinPrefixPosCosted,
    hsummary, harg, hmin, hmax, hargEntry]

theorem arg_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {block : Nat} {word : List Bool}
    (hword : table.argTable.store.words[block]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := table.argTable.read_word_length_of_some hword
  omega

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {block : Nat} {word : List Bool},
      table.summary.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.summary.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  have hsummary :=
    table.summary.summary_read_words_length_le_machine hmachine
  exact ⟨hsummary.1, hsummary.2,
    by
      intro block word hword
      exact table.arg_read_word_length_le_machine hmachine hword⟩

theorem payload_length_le_sampled
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead slots n : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hbudget :
      overhead <= sampledDirectoryOverhead slots n) :
    table.payload.length <= sampledDirectoryOverhead slots n := by
  rw [table.payload_length]
  exact hbudget

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead) :
    table.payload.length = overhead /\
      (forall block,
        (table.summaryArgCosted block).cost <= 3 /\
          (table.summaryArgCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
            with
            | some minExcess, some maxExcess, some argPos =>
                some (minExcess, maxExcess, argPos)
            | _, _, _ => none) := by
  constructor
  · exact table.payload_length
  intro block
  exact ⟨table.summaryArgCosted_cost_le_three block,
    table.summaryArgCosted_erase block⟩

end PayloadLiveBPRangeMinMaxArgSummaryTable

def concreteBPRangeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
      fieldWidth (3 * (blockCount * fieldWidth)) where
  summary :=
    concreteBPRangeMinMaxSummaryTable
      shape blockSize blockCount fieldWidth hwidth
  argTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
      fieldWidth
      (by
        intro entry hmem
        exact bpBlockArgMinPrefixPosEntries_mem_bound hwidth hmem)
  payload_length_eq := by
    have hsummary :
        (concreteBPRangeMinMaxSummaryTable
          shape blockSize blockCount fieldWidth hwidth).payload.length =
          2 * (blockCount * fieldWidth) := by
      exact
        (concreteBPRangeMinMaxSummaryTable
          shape blockSize blockCount fieldWidth hwidth).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockArgMinPrefixPosEntries_mem_bound hwidth hmem)).payload.length =
          blockCount * fieldWidth := by
      simpa [bpBlockArgMinPrefixPosEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockArgMinPrefixPosEntries_mem_bound hwidth hmem)).payload_length
    omega

theorem concreteBPRangeMinMaxArgSummaryTable_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let table :=
      concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    table.payload.length = 3 * (blockCount * fieldWidth) /\
      forall block,
        (table.summaryArgCosted block).cost <= 3 /\
          (table.summaryArgCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
            with
            | some minExcess, some maxExcess, some argPos =>
                some (minExcess, maxExcess, argPos)
            | _, _, _ => none := by
  exact
    (concreteBPRangeMinMaxArgSummaryTable
      shape blockSize blockCount fieldWidth hwidth).profile

theorem concreteBPRangeMinMaxArgSummaryTable_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      3 * (blockCount * fieldWidth) <= sampledDirectoryOverhead slots n) :
    let table :=
      concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      table.payload.length <= sampledDirectoryOverhead slots n /\
      (forall block,
        (table.summaryArgCosted block).cost <= 3 /\
          (table.summaryArgCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
            with
            | some minExcess, some maxExcess, some argPos =>
                some (minExcess, maxExcess, argPos)
            | _, _, _ => none) := by
  let table :=
    concreteBPRangeMinMaxArgSummaryTable
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · exact table.payload_length_le_sampled hbudget
  intro block
  exact ⟨table.summaryArgCosted_cost_le_three block,
    table.summaryArgCosted_erase block⟩

theorem concreteBPRangeMinMaxArgSummaryTable_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    (forall {block : Nat} {word : List Bool},
      table.summary.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.summary.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPRangeMinMaxArgSummaryTable.read_words_length_le_machine
      (concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth)
      hmachine

/-!
## Position-bearing BP range witnesses

The block summaries above are single-block data.  The next macro ingredient is
an actual range witness: for each stored block range, the payload stores both
the minimum excess value and the prefix position attaining it.  The close
candidate returned by `rangeCloseCosted` is therefore computed from charged
payload reads instead of from proof-only block scans.
-/

def bpBetterArgMinPrefixPos
    (shape : Cartesian.CartesianShape) (left right : Nat) : Nat :=
  if bpExcessAt shape right < bpExcessAt shape left then right else left

theorem bpBetterArgMinPrefixPos_le_length
    (shape : Cartesian.CartesianShape) {left right : Nat}
    (hleft : left <= shape.bpCode.length)
    (hright : right <= shape.bpCode.length) :
    bpBetterArgMinPrefixPos shape left right <= shape.bpCode.length := by
  unfold bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt, hright]
  · simp [hlt, hleft]

def bpRangeArgMinPrefixPosFrom
    (shape : Cartesian.CartesianShape) (blockSize : Nat) :
    Nat -> Nat -> Nat -> Nat
  | _block, 0, best => best
  | block, steps + 1, best =>
      let candidate := bpBlockArgMinPrefixPos shape blockSize block
      let best' := bpBetterArgMinPrefixPos shape best candidate
      bpRangeArgMinPrefixPosFrom shape blockSize (block + 1) steps best'

theorem bpRangeArgMinPrefixPosFrom_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize block steps best : Nat)
    (hbest : best <= shape.bpCode.length) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best <=
      shape.bpCode.length := by
  induction steps generalizing block best with
  | zero =>
      simpa [bpRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      exact ih (block + 1)
        (bpBetterArgMinPrefixPos shape best
          (bpBlockArgMinPrefixPos shape blockSize block))
        (bpBetterArgMinPrefixPos_le_length shape hbest
          (bpBlockArgMinPrefixPos_le_length shape blockSize block))

def bpRangeArgMinPrefixPos
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  match blockCount with
  | 0 => Nat.min (blockStartOf blockSize startBlock) shape.bpCode.length
  | count + 1 =>
      bpRangeArgMinPrefixPosFrom shape blockSize (startBlock + 1) count
        (bpBlockArgMinPrefixPos shape blockSize startBlock)

theorem bpRangeArgMinPrefixPos_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) :
    bpRangeArgMinPrefixPos shape blockSize startBlock blockCount <=
      shape.bpCode.length := by
  unfold bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      exact Nat.min_le_right (blockStartOf blockSize startBlock)
        shape.bpCode.length
  | succ count =>
      exact bpRangeArgMinPrefixPosFrom_le_length shape blockSize
        (startBlock + 1) count
        (bpBlockArgMinPrefixPos shape blockSize startBlock)
        (bpBlockArgMinPrefixPos_le_length shape blockSize startBlock)

def bpRangeMinExcess
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  bpExcessAt shape
    (bpRangeArgMinPrefixPos shape blockSize startBlock blockCount)

theorem bpRangeMinExcess_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) :
    bpRangeMinExcess shape blockSize startBlock blockCount <=
      shape.bpCode.length := by
  exact bpExcessAt_le_length shape
    (bpRangeArgMinPrefixPos shape blockSize startBlock blockCount)

def bpRangeMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range =>
    bpRangeMinExcess shape blockSize range.1 range.2

def bpRangeArgMinPrefixPosEntries
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range =>
    bpRangeArgMinPrefixPos shape blockSize range.1 range.2

theorem bpRangeMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) :
    (bpRangeMinExcessEntries shape blockSize ranges).length =
      ranges.length := by
  simp [bpRangeMinExcessEntries]

theorem bpRangeArgMinPrefixPosEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) :
    (bpRangeArgMinPrefixPosEntries shape blockSize ranges).length =
      ranges.length := by
  simp [bpRangeArgMinPrefixPosEntries]

theorem bpRangeMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (bpRangeMinExcessEntries shape blockSize ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpRangeMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpRangeMinExcess_le_length shape blockSize range.1 range.2) hwidth

theorem bpRangeArgMinPrefixPosEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpRangeArgMinPrefixPosEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpRangeArgMinPrefixPos_le_length shape blockSize range.1 range.2)
    hwidth

/--
Payload-live macro witness table for explicit BP block ranges.

Each range consumes two fixed-width payload reads: one for the minimum excess
value and one for the prefix-position witness attaining that value.
-/
structure PayloadLiveBPRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth overhead : Nat)
    (ranges : List (Nat × Nat)) where
  minTable :
    FixedWidthNatTable
      (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
  argTable :
    FixedWidthNatTable
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
  payload_length_eq :
    minTable.payload.length + argTable.payload.length = overhead

namespace PayloadLiveBPRangeArgMinWitnessTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges) : List Bool :=
  table.minTable.payload ++ table.argTable.payload

def rangeWitnessCosted
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (table.minTable.readCosted rangeIndex) fun min? =>
    Costed.map
      (fun arg? =>
        match min?, arg? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none)
      (table.argTable.readCosted rangeIndex)

def rangeCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) : Costed (Option Nat) :=
  Costed.map
    (fun candidate? => candidate?.map fun candidate => candidate.2 - 1)
    (table.rangeWitnessCosted rangeIndex)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem rangeWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).cost <= 2 := by
  unfold rangeWitnessCosted
  cases hread :
      (table.minTable.readCosted rangeIndex).value with
  | none =>
      simp [Costed.bind, Costed.map, hread]
  | some minExcess =>
      simp [Costed.bind, Costed.map, hread]

theorem rangeCloseCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeCloseCosted rangeIndex).cost <= 2 := by
  simpa [rangeCloseCosted, Costed.map_cost] using
    table.rangeWitnessCosted_cost_le_two rangeIndex

theorem rangeWitnessCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).erase =
      match
        (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? with
      | some minExcess, some prefixPos => some (minExcess, prefixPos)
      | _, _ => none := by
  unfold rangeWitnessCosted
  have hmin :
      (table.minTable.readCosted rangeIndex).value =
        (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]? := by
    exact table.minTable.readCosted_erase rangeIndex
  have harg :
      (table.argTable.readCosted rangeIndex).value =
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? := by
    exact table.argTable.readCosted_erase rangeIndex
  cases hminEntry :
      (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?
  <;> cases hargEntry :
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, hmin, harg,
    hminEntry, hargEntry]

theorem rangeCloseCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeCloseCosted rangeIndex).erase =
      match
        (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? with
      | some _minExcess, some prefixPos => some (prefixPos - 1)
      | _, _ => none := by
  cases hminEntry :
      (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?
  <;> cases hargEntry :
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]?
  <;> simp [rangeCloseCosted, Costed.erase_map,
    table.rangeWitnessCosted_erase, hminEntry, hargEntry]

theorem rangeCloseCosted_exact_of_prefix_pos
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead answerClose rangeIndex : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmin :
      (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]? =
        some (bpExcessAt shape (answerClose + 1)))
    (harg :
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? =
        some (answerClose + 1)) :
    (table.rangeCloseCosted rangeIndex).erase = some answerClose := by
  simp [table.rangeCloseCosted_erase, hmin, harg]

theorem min_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {rangeIndex : Nat} {word : List Bool}
    (hword : table.minTable.store.words[rangeIndex]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := table.minTable.read_word_length_of_some hword
  omega

theorem arg_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {rangeIndex : Nat} {word : List Bool}
    (hword : table.argTable.store.words[rangeIndex]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := table.argTable.read_word_length_of_some hword
  omega

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  constructor
  · intro rangeIndex word hword
    exact table.min_read_word_length_le_machine hmachine hword
  · intro rangeIndex word hword
    exact table.arg_read_word_length_le_machine hmachine hword

theorem payload_length_le_sampled
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead slots n : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hoverhead : overhead <= sampledDirectoryOverhead slots n) :
    table.payload.length <= sampledDirectoryOverhead slots n := by
  rw [table.payload_length]
  exact hoverhead

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges) :
    table.payload.length = overhead /\
      (forall rangeIndex,
        (table.rangeWitnessCosted rangeIndex).cost <= 2 /\
          (table.rangeWitnessCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some minExcess, some prefixPos =>
                some (minExcess, prefixPos)
            | _, _ => none) /\
      (forall rangeIndex,
        (table.rangeCloseCosted rangeIndex).cost <= 2 /\
          (table.rangeCloseCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none) := by
  constructor
  · exact table.payload_length
  constructor
  · intro rangeIndex
    exact ⟨table.rangeWitnessCosted_cost_le_two rangeIndex,
      table.rangeWitnessCosted_erase rangeIndex⟩
  · intro rangeIndex
    exact ⟨table.rangeCloseCosted_cost_le_two rangeIndex,
      table.rangeCloseCosted_erase rangeIndex⟩

end PayloadLiveBPRangeArgMinWitnessTable

def concreteBPRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
      (2 * (ranges.length * fieldWidth)) ranges where
  minTable :=
    FixedWidthNatTable.ofEntries
      (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
      (bpRangeMinExcessEntries_mem_bound hwidth)
  argTable :=
    FixedWidthNatTable.ofEntries
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
      (bpRangeArgMinPrefixPosEntries_mem_bound hwidth)
  payload_length_eq := by
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
          (bpRangeMinExcessEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpRangeMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
          (bpRangeMinExcessEntries_mem_bound hwidth)).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
          (bpRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpRangeArgMinPrefixPosEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
          (bpRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload_length
    omega

theorem concreteBPRangeArgMinWitnessTable_profile
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let table :=
      concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth
    table.payload.length = 2 * (ranges.length * fieldWidth) /\
      (forall rangeIndex,
        (table.rangeWitnessCosted rangeIndex).cost <= 2 /\
          (table.rangeWitnessCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some minExcess, some prefixPos =>
                some (minExcess, prefixPos)
            | _, _ => none) /\
      (forall rangeIndex,
        (table.rangeCloseCosted rangeIndex).cost <= 2 /\
          (table.rangeCloseCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none) := by
  exact
    (concreteBPRangeArgMinWitnessTable
      shape blockSize fieldWidth ranges hwidth).profile

theorem concreteBPRangeArgMinWitnessTable_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth slots n : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hoverhead :
      2 * (ranges.length * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let table :=
      concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      table.payload.length <= sampledDirectoryOverhead slots n /\
      (forall rangeIndex,
        (table.rangeCloseCosted rangeIndex).cost <= 2 /\
          (table.rangeCloseCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none) := by
  let table :=
    concreteBPRangeArgMinWitnessTable
      shape blockSize fieldWidth ranges hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · exact
      PayloadLiveBPRangeArgMinWitnessTable.payload_length_le_sampled
        table hoverhead
  · intro rangeIndex
    exact (concreteBPRangeArgMinWitnessTable_profile
      shape blockSize fieldWidth ranges hwidth).2.2 rangeIndex

theorem concreteBPRangeArgMinWitnessTable_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPRangeArgMinWitnessTable.read_words_length_le_machine
      (concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth) hmachine

/-!
## Block-pair macro close candidate

This component consumes the range-witness table through an
`lcaCloseCosted`-shaped API.  It is intentionally only the macro candidate:
the full C2 close answer still has to combine this interior witness with
endpoint-fringe repair.
-/

def blockPairRangeSlot
    (blockCount leftBlock rightBlock : Nat) : Nat :=
  leftBlock * blockCount + rightBlock

def blockPairRangeOfSlot (blockCount slot : Nat) : Nat × Nat :=
  let leftBlock := slot / blockCount
  let rightBlock := slot % blockCount
  if leftBlock <= rightBlock then
    (leftBlock, rightBlock - leftBlock + 1)
  else
    (leftBlock, 0)

def blockPairRanges (blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockCount)).map
    (blockPairRangeOfSlot blockCount)

theorem blockPairRanges_length (blockCount : Nat) :
    (blockPairRanges blockCount).length =
      blockCount * blockCount := by
  simp [blockPairRanges]

theorem blockPairRangeSlot_lt
    {blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount) :
    blockPairRangeSlot blockCount leftBlock rightBlock <
      blockCount * blockCount := by
  simpa [blockPairRangeSlot, densePairSlot] using
    densePairSlot_lt hleft hright

theorem blockPairRangeSlot_div
    {blockCount leftBlock rightBlock : Nat}
    (hright : rightBlock < blockCount) :
    blockPairRangeSlot blockCount leftBlock rightBlock / blockCount =
      leftBlock := by
  simpa [blockPairRangeSlot, densePairSlot] using
    (densePairSlot_div
      (blockSize := blockCount) (leftLocal := leftBlock)
      (rightLocal := rightBlock) hright)

theorem blockPairRangeSlot_mod
    {blockCount leftBlock rightBlock : Nat}
    (hright : rightBlock < blockCount) :
    blockPairRangeSlot blockCount leftBlock rightBlock % blockCount =
      rightBlock := by
  simpa [blockPairRangeSlot, densePairSlot] using
    (densePairSlot_mod
      (blockSize := blockCount) (leftLocal := leftBlock)
      (rightLocal := rightBlock) hright)

theorem blockPairRanges_get?_of_ordered_bounds
    {blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hordered : leftBlock <= rightBlock) :
    (blockPairRanges blockCount)[
        blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some (leftBlock, rightBlock - leftBlock + 1) := by
  have hslot :
      blockPairRangeSlot blockCount leftBlock rightBlock <
        blockCount * blockCount :=
    blockPairRangeSlot_lt hleft hright
  have hslotGet :
      (List.range (blockCount * blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
        some (blockPairRangeSlot blockCount leftBlock rightBlock) := by
    exact List.getElem?_range hslot
  have hdiv :
      blockPairRangeSlot blockCount leftBlock rightBlock / blockCount =
        leftBlock :=
    blockPairRangeSlot_div hright
  have hmod :
      blockPairRangeSlot blockCount leftBlock rightBlock % blockCount =
        rightBlock :=
    blockPairRangeSlot_mod hright
  simp [blockPairRanges, List.getElem?_map, hslotGet,
    blockPairRangeOfSlot, hdiv, hmod, hordered]

/--
Concrete payload-live macro candidate indexed by the endpoint close blocks.

The payload is a position-bearing range-witness table over the block-pair range
list.  A query reads the block-pair witness and returns its close candidate.
-/
structure PayloadLiveBPBlockPairRangeWitnessMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth overhead : Nat) where
  table :
    PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth overhead
      (blockPairRanges blockCount)

namespace PayloadLiveBPBlockPairRangeWitnessMacro

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead) : List Bool :=
  component.table.payload

def rangeIndex
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (_component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) : Nat :=
  blockPairRangeSlot blockCount
    (blockOfClose blockSize leftClose)
    (blockOfClose blockSize rightClose)

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  component.table.rangeCloseCosted
    (component.rangeIndex leftClose rightClose)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead) :
    component.payload.length = overhead := by
  exact component.table.payload_length

theorem lcaCloseCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <= 2 := by
  exact component.table.rangeCloseCosted_cost_le_two
    (component.rangeIndex leftClose rightClose)

theorem lcaCloseCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      match
        (bpRangeMinExcessEntries shape blockSize
          (blockPairRanges blockCount))[
            component.rangeIndex leftClose rightClose]?,
        (bpRangeArgMinPrefixPosEntries shape blockSize
          (blockPairRanges blockCount))[
            component.rangeIndex leftClose rightClose]? with
      | some _minExcess, some prefixPos => some (prefixPos - 1)
      | _, _ => none := by
  exact component.table.rangeCloseCosted_erase
    (component.rangeIndex leftClose rightClose)

theorem lcaCloseCosted_exact_of_prefix_pos
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead answerClose : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat)
    (hmin :
      (bpRangeMinExcessEntries shape blockSize
        (blockPairRanges blockCount))[
          component.rangeIndex leftClose rightClose]? =
        some (bpExcessAt shape (answerClose + 1)))
    (harg :
      (bpRangeArgMinPrefixPosEntries shape blockSize
        (blockPairRanges blockCount))[
          component.rangeIndex leftClose rightClose]? =
        some (answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  exact component.table.rangeCloseCosted_exact_of_prefix_pos hmin harg

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact component.table.read_words_length_le_machine hmachine

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead) :
    component.payload.length = overhead /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 2 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            match
              (bpRangeMinExcessEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none := by
  constructor
  · exact component.payload_length
  · intro leftClose rightClose
    exact ⟨component.lcaCloseCosted_cost_le_two leftClose rightClose,
      component.lcaCloseCosted_erase leftClose rightClose⟩

end PayloadLiveBPBlockPairRangeWitnessMacro

def concreteBPBlockPairRangeWitnessMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
      fieldWidth
        (2 * ((blockPairRanges blockCount).length * fieldWidth)) where
  table :=
    concreteBPRangeArgMinWitnessTable
      shape blockSize fieldWidth (blockPairRanges blockCount) hwidth

theorem concreteBPBlockPairRangeWitnessMacro_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let component :=
      concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth
    component.payload.length =
        2 * ((blockCount * blockCount) * fieldWidth) /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 2 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            match
              (bpRangeMinExcessEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none := by
  have hprofile :=
    (concreteBPBlockPairRangeWitnessMacro
      shape blockSize blockCount fieldWidth hwidth).profile
  constructor
  · simpa [concreteBPBlockPairRangeWitnessMacro, blockPairRanges_length]
      using hprofile.1
  · exact hprofile.2

theorem concreteBPBlockPairRangeWitnessMacro_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hoverhead :
      2 * ((blockCount * blockCount) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 2 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            match
              (bpRangeMinExcessEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none := by
  let component :=
    concreteBPBlockPairRangeWitnessMacro
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [component.payload_length]
    simpa [blockPairRanges_length] using hoverhead
  · exact (concreteBPBlockPairRangeWitnessMacro_profile
      shape blockSize blockCount fieldWidth hwidth).2

theorem concreteBPBlockPairRangeWitnessMacro_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let component :=
      concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPBlockPairRangeWitnessMacro.read_words_length_le_machine
      (concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth) hmachine

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

end SuccinctCloseProposal
end RMQ
