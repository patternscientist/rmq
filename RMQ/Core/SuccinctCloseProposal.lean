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

theorem bpCloseOfInorder?_le_of_le
    {shape : Cartesian.CartesianShape} {leftIdx rightIdx leftClose rightClose : Nat}
    (hleft : bpCloseOfInorder? shape leftIdx = some leftClose)
    (hright : bpCloseOfInorder? shape rightIdx = some rightClose)
    (hidx : leftIdx <= rightIdx) :
    leftClose <= rightClose := by
  induction shape generalizing leftIdx rightIdx leftClose rightClose with
  | empty =>
      simp [bpCloseOfInorder?] at hleft
  | node left right ihleft ihright =>
      by_cases hleftBranch : leftIdx < left.size
      · cases hleftRec : bpCloseOfInorder? left leftIdx with
        | none =>
            simp [bpCloseOfInorder?, hleftBranch, hleftRec] at hleft
        | some innerLeft =>
            have hinnerLeftBound :
                innerLeft < left.bpCode.length :=
              bpCloseOfInorder?_bounds left hleftRec
            simp [bpCloseOfInorder?, hleftBranch, hleftRec] at hleft
            subst leftClose
            by_cases hrightBranch : rightIdx < left.size
            · cases hrightRec : bpCloseOfInorder? left rightIdx with
              | none =>
                  simp [bpCloseOfInorder?, hrightBranch, hrightRec] at hright
              | some innerRight =>
                  have hrec :
                      innerLeft <= innerRight :=
                    ihleft hleftRec hrightRec hidx
                  simp [bpCloseOfInorder?, hrightBranch, hrightRec] at hright
                  subst rightClose
                  omega
            · by_cases hrightRoot : rightIdx = left.size
              · simp [bpCloseOfInorder?, hrightRoot] at hright
                subst rightClose
                omega
              · cases hrightRec :
                    bpCloseOfInorder? right
                      (rightIdx - left.size - 1) with
                | none =>
                    simp [bpCloseOfInorder?, hrightBranch, hrightRoot,
                      hrightRec] at hright
                | some innerRight =>
                    simp [bpCloseOfInorder?, hrightBranch, hrightRoot,
                      hrightRec] at hright
                    subst rightClose
                    omega
      · by_cases hleftRoot : leftIdx = left.size
        · simp [bpCloseOfInorder?, hleftRoot] at hleft
          subst leftClose
          by_cases hrightBranch : rightIdx < left.size
          · omega
          · by_cases hrightRoot : rightIdx = left.size
            · simp [bpCloseOfInorder?, hrightRoot] at hright
              subst rightClose
              omega
            · cases hrightRec :
                  bpCloseOfInorder? right
                    (rightIdx - left.size - 1) with
              | none =>
                  simp [bpCloseOfInorder?, hrightBranch, hrightRoot,
                    hrightRec] at hright
              | some innerRight =>
                  simp [bpCloseOfInorder?, hrightBranch, hrightRoot,
                    hrightRec] at hright
                  subst rightClose
                  omega
        · cases hleftRec :
              bpCloseOfInorder? right (leftIdx - left.size - 1) with
          | none =>
              simp [bpCloseOfInorder?, hleftBranch, hleftRoot,
                hleftRec] at hleft
          | some innerLeft =>
              simp [bpCloseOfInorder?, hleftBranch, hleftRoot,
                hleftRec] at hleft
              subst leftClose
              by_cases hrightBranch : rightIdx < left.size
              · omega
              · by_cases hrightRoot : rightIdx = left.size
                · omega
                · cases hrightRec :
                      bpCloseOfInorder? right
                        (rightIdx - left.size - 1) with
                  | none =>
                      simp [bpCloseOfInorder?, hrightBranch, hrightRoot,
                        hrightRec] at hright
                  | some innerRight =>
                      have hshift :
                          leftIdx - left.size - 1 <=
                            rightIdx - left.size - 1 := by
                        omega
                      have hrec :
                          innerLeft <= innerRight :=
                        ihright hleftRec hrightRec hshift
                      simp [bpCloseOfInorder?, hrightBranch, hrightRoot,
                        hrightRec] at hright
                      subst rightClose
                      omega

theorem bpCloseOfInorder?_lt_of_lt
    {shape : Cartesian.CartesianShape} {leftIdx rightIdx leftClose rightClose : Nat}
    (hleft : bpCloseOfInorder? shape leftIdx = some leftClose)
    (hright : bpCloseOfInorder? shape rightIdx = some rightClose)
    (hidx : leftIdx < rightIdx) :
    leftClose < rightClose := by
  have hle :
      leftClose <= rightClose :=
    bpCloseOfInorder?_le_of_le hleft hright (Nat.le_of_lt hidx)
  have hne : leftClose ≠ rightClose := by
    intro heq
    have hleftRank := bpCloseOfInorder?_rankFalse_succ shape hleft
    have hrightRank := bpCloseOfInorder?_rankFalse_succ shape hright
    rw [heq] at hleftRank
    rw [hrightRank] at hleftRank
    omega
  omega

theorem endpoint_closes_ordered_of_query_span
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose) :
    leftClose <= rightClose := by
  have hidx : left <= left + len - 1 := by
    omega
  exact bpCloseOfInorder?_le_of_le hleft hright hidx

theorem answerClose_between_endpoint_closes
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    leftClose <= answerClose /\ answerClose <= rightClose := by
  have hscan :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  constructor
  · exact bpCloseOfInorder?_le_of_le hleft hanswer hscan.1
  · have hscanRight :
        scanWindow shape.representative left len <= left + len - 1 := by
      omega
    exact bpCloseOfInorder?_le_of_le hanswer hright hscanRight

theorem answerClose_prefix_between_endpoint_prefixes
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    leftClose + 1 <= answerClose + 1 /\
      answerClose + 1 <= rightClose + 1 := by
  have hbetween :=
    answerClose_between_endpoint_closes
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose) hlen hleft hright hanswer
  omega

theorem endpoint_prefix_range_count_pos
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose) :
    0 < rightClose - leftClose + 1 := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  omega

theorem answerClose_prefix_mem_endpoint_prefix_range
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    leftClose + 1 <= answerClose + 1 /\
      answerClose + 1 < leftClose + 1 + (rightClose - leftClose + 1) := by
  have hbetween :=
    answerClose_prefix_between_endpoint_prefixes
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose) hlen hleft hright hanswer
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

theorem blockStartOf_succ
    (blockSize block : Nat) :
    blockStartOf blockSize block + blockSize =
      blockStartOf blockSize (block + 1) := by
  unfold blockStartOf
  simpa using (Nat.succ_mul block blockSize).symm

theorem blockStartOf_mono
    {blockSize leftBlock rightBlock : Nat}
    (hblock : leftBlock <= rightBlock) :
    blockStartOf blockSize leftBlock <=
      blockStartOf blockSize rightBlock := by
  unfold blockStartOf
  exact Nat.mul_le_mul_right blockSize hblock

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

theorem bpCode_rankTrue_full (shape : Cartesian.CartesianShape) :
    Succinct.rankPrefix true shape.bpCode shape.bpCode.length =
      shape.size := by
  have hfinal :=
    Succinct.BalancedParens.final_rank_eq (bpParensOfShape shape)
  have hfalse := bpCode_rankFalse_full shape
  simpa [bpParensOfShape, hfalse] using hfinal

theorem bpExcessAt_close_succ_add_inorder_succ_eq_open_rank
    {shape : Cartesian.CartesianShape} {idx close : Nat}
    (hclose : bpCloseOfInorder? shape idx = some close) :
    bpExcessAt shape (close + 1) + (idx + 1) =
      Succinct.rankPrefix true shape.bpCode (close + 1) := by
  have hbound : close + 1 <= shape.bpCode.length := by
    have hcloseBound := bpCloseOfInorder?_bounds shape hclose
    omega
  have hrank := bpCloseOfInorder?_rankFalse_succ shape hclose
  calc
    bpExcessAt shape (close + 1) + (idx + 1) =
        bpExcessAt shape (close + 1) +
          Succinct.rankPrefix false shape.bpCode (close + 1) := by
      rw [hrank]
    _ = Succinct.rankPrefix true shape.bpCode (close + 1) := by
      exact bpExcessAt_add_close_rank_eq_open_rank_of_le shape hbound

theorem bpExcessAt_node_left_prefix_succ
    (left right : Cartesian.CartesianShape) {pos : Nat}
    (hpos : pos <= left.bpCode.length) :
    bpExcessAt (Cartesian.CartesianShape.node left right) (pos + 1) =
      bpExcessAt left pos + 1 := by
  have hfalseTail :
      Succinct.rankPrefix false
          (left.bpCode ++ false :: right.bpCode) pos =
        Succinct.rankPrefix false left.bpCode pos :=
    Succinct.rankPrefix_append_of_le false left.bpCode
      (false :: right.bpCode) hpos
  have htrueTail :
      Succinct.rankPrefix true
          (left.bpCode ++ false :: right.bpCode) pos =
        Succinct.rankPrefix true left.bpCode pos :=
    Succinct.rankPrefix_append_of_le true left.bpCode
      (false :: right.bpCode) hpos
  have hnonneg := bpExcessAt_prefix_nonnegative left hpos
  unfold bpExcessAt
  simp [Cartesian.CartesianShape.bpCode, Succinct.rankPrefix,
    hfalseTail, htrueTail]
  omega

theorem bpExcessAt_node_right_prefix_shift
    (left right : Cartesian.CartesianShape) {pos : Nat}
    (hpos : pos <= right.bpCode.length) :
    bpExcessAt (Cartesian.CartesianShape.node left right)
        (left.bpCode.length + 2 + pos) =
      bpExcessAt right pos := by
  have hfalseTail :
      Succinct.rankPrefix false
          (left.bpCode ++ false :: right.bpCode)
          (left.bpCode.length + 1 + pos) =
        Succinct.rankPrefix false left.bpCode left.bpCode.length +
          Succinct.rankPrefix false (false :: right.bpCode) (1 + pos) := by
    have happ :=
      Succinct.rankPrefix_append_of_ge false left.bpCode
        (false :: right.bpCode)
        (limit := left.bpCode.length + 1 + pos) (by omega)
    have hsub :
        left.bpCode.length + 1 + pos - left.bpCode.length = 1 + pos := by
      omega
    rw [hsub] at happ
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using happ
  have htrueTail :
      Succinct.rankPrefix true
          (left.bpCode ++ false :: right.bpCode)
          (left.bpCode.length + 1 + pos) =
        Succinct.rankPrefix true left.bpCode left.bpCode.length +
          Succinct.rankPrefix true (false :: right.bpCode) (1 + pos) := by
    have happ :=
      Succinct.rankPrefix_append_of_ge true left.bpCode
        (false :: right.bpCode)
        (limit := left.bpCode.length + 1 + pos) (by omega)
    have hsub :
        left.bpCode.length + 1 + pos - left.bpCode.length = 1 + pos := by
      omega
    rw [hsub] at happ
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using happ
  have hleftFalse := bpCode_rankFalse_full left
  have hleftTrue := bpCode_rankTrue_full left
  have hrightNonneg := bpExcessAt_prefix_nonnegative right hpos
  have hfalseParent :
      Succinct.rankPrefix false
          (Cartesian.CartesianShape.node left right).bpCode
          (left.bpCode.length + 2 + pos) =
        left.size + 1 +
          Succinct.rankPrefix false right.bpCode pos := by
    calc
      Succinct.rankPrefix false
          (Cartesian.CartesianShape.node left right).bpCode
          (left.bpCode.length + 2 + pos) =
        Succinct.rankPrefix false
          (left.bpCode ++ false :: right.bpCode)
          (left.bpCode.length + 1 + pos) := by
          have hlimit :
              left.bpCode.length + 2 + pos =
                (left.bpCode.length + 1 + pos) + 1 := by
            omega
          rw [hlimit]
          simp [Cartesian.CartesianShape.bpCode, Succinct.rankPrefix]
      _ =
        Succinct.rankPrefix false left.bpCode left.bpCode.length +
          Succinct.rankPrefix false (false :: right.bpCode) (1 + pos) :=
          hfalseTail
      _ =
        left.size + (1 +
          Succinct.rankPrefix false right.bpCode pos) := by
          rw [hleftFalse]
          have hlimit : 1 + pos = pos + 1 := by
            omega
          rw [hlimit]
          simp [Succinct.rankPrefix]
      _ =
        left.size + 1 +
          Succinct.rankPrefix false right.bpCode pos := by
          omega
  have htrueParent :
      Succinct.rankPrefix true
          (Cartesian.CartesianShape.node left right).bpCode
          (left.bpCode.length + 2 + pos) =
        left.size + 1 +
          Succinct.rankPrefix true right.bpCode pos := by
    calc
      Succinct.rankPrefix true
          (Cartesian.CartesianShape.node left right).bpCode
          (left.bpCode.length + 2 + pos) =
        1 +
          Succinct.rankPrefix true
            (left.bpCode ++ false :: right.bpCode)
            (left.bpCode.length + 1 + pos) := by
          have hlimit :
              left.bpCode.length + 2 + pos =
                (left.bpCode.length + 1 + pos) + 1 := by
            omega
          rw [hlimit]
          simp [Cartesian.CartesianShape.bpCode, Succinct.rankPrefix]
      _ =
        1 +
          (Succinct.rankPrefix true left.bpCode left.bpCode.length +
            Succinct.rankPrefix true (false :: right.bpCode) (1 + pos)) := by
          rw [htrueTail]
      _ =
        1 + (left.size +
          Succinct.rankPrefix true right.bpCode pos) := by
          rw [hleftTrue]
          have hlimit : 1 + pos = pos + 1 := by
            omega
          rw [hlimit]
          simp [Succinct.rankPrefix]
      _ =
        left.size + 1 +
          Succinct.rankPrefix true right.bpCode pos := by
          omega
  unfold bpExcessAt
  rw [htrueParent, hfalseParent]
  omega

theorem bpExcessAt_node_root_close_succ
    (left right : Cartesian.CartesianShape) :
    bpExcessAt (Cartesian.CartesianShape.node left right)
      (left.bpCode.length + 2) = 0 := by
  have hfalseTail :
      Succinct.rankPrefix false (left.bpCode ++ false :: right.bpCode)
          (left.bpCode.length + 1) =
        Succinct.rankPrefix false left.bpCode left.bpCode.length + 1 := by
    have hge : left.bpCode.length <= left.bpCode.length + 1 := by
      omega
    have happ :=
      Succinct.rankPrefix_append_of_ge false left.bpCode
        (false :: right.bpCode)
        (limit := left.bpCode.length + 1) hge
    have htail :
        Succinct.rankPrefix false (false :: right.bpCode)
            (left.bpCode.length + 1 - left.bpCode.length) = 1 := by
      have hsub : left.bpCode.length + 1 - left.bpCode.length = 1 := by
        omega
      simp [hsub, Succinct.rankPrefix]
    rw [happ, htail]
  have htrueTail :
      Succinct.rankPrefix true (left.bpCode ++ false :: right.bpCode)
          (left.bpCode.length + 1) =
        Succinct.rankPrefix true left.bpCode left.bpCode.length := by
    have hge : left.bpCode.length <= left.bpCode.length + 1 := by
      omega
    have happ :=
      Succinct.rankPrefix_append_of_ge true left.bpCode
        (false :: right.bpCode)
        (limit := left.bpCode.length + 1) hge
    have htail :
        Succinct.rankPrefix true (false :: right.bpCode)
            (left.bpCode.length + 1 - left.bpCode.length) = 0 := by
      have hsub : left.bpCode.length + 1 - left.bpCode.length = 1 := by
        omega
      simp [hsub, Succinct.rankPrefix]
    rw [happ, htail]
    omega
  have hleftBalanced :
      Succinct.rankPrefix true left.bpCode left.bpCode.length =
        Succinct.rankPrefix false left.bpCode left.bpCode.length := by
    exact Succinct.BalancedParens.final_rank_eq (bpParensOfShape left)
  unfold bpExcessAt
  simp [Cartesian.CartesianShape.bpCode, Succinct.rankPrefix,
    hfalseTail, htrueTail, hleftBalanced]
  omega

theorem bpExcessAt_node_pos_before_root_close_succ_pos
    (left right : Cartesian.CartesianShape)
    {pos : Nat}
    (hpos : 0 < pos)
    (hbefore : pos < left.bpCode.length + 2) :
    0 <
      bpExcessAt (Cartesian.CartesianShape.node left right) pos := by
  cases pos with
  | zero =>
      omega
  | succ p =>
      have hp_le : p <= left.bpCode.length := by
        omega
      have hfalseTail :
          Succinct.rankPrefix false
              (left.bpCode ++ false :: right.bpCode) p =
            Succinct.rankPrefix false left.bpCode p :=
        Succinct.rankPrefix_append_of_le false left.bpCode
          (false :: right.bpCode) hp_le
      have htrueTail :
          Succinct.rankPrefix true
              (left.bpCode ++ false :: right.bpCode) p =
            Succinct.rankPrefix true left.bpCode p :=
        Succinct.rankPrefix_append_of_le true left.bpCode
          (false :: right.bpCode) hp_le
      have hprefix :
          Succinct.rankPrefix false left.bpCode p <=
            Succinct.rankPrefix true left.bpCode p :=
        bpExcessAt_prefix_nonnegative left hp_le
      unfold bpExcessAt
      simp [Cartesian.CartesianShape.bpCode, Succinct.rankPrefix,
        hfalseTail, htrueTail]
      omega

theorem bpExcessAt_node_root_close_succ_le_prefix
    (left right : Cartesian.CartesianShape)
    (pos : Nat) :
    bpExcessAt (Cartesian.CartesianShape.node left right)
        (left.bpCode.length + 2) <=
      bpExcessAt (Cartesian.CartesianShape.node left right) pos := by
  rw [bpExcessAt_node_root_close_succ]
  exact Nat.zero_le _

theorem bpExcessAt_node_root_close_succ_lt_before
    (left right : Cartesian.CartesianShape)
    {pos : Nat}
    (hpos : 0 < pos)
    (hbefore : pos < left.bpCode.length + 2) :
    bpExcessAt (Cartesian.CartesianShape.node left right)
        (left.bpCode.length + 2) <
      bpExcessAt (Cartesian.CartesianShape.node left right) pos := by
  rw [bpExcessAt_node_root_close_succ]
  exact bpExcessAt_node_pos_before_root_close_succ_pos
    left right hpos hbefore

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

/--
A compact asymptotic envelope for the charged BP close/LCA summary payload.

The four terms reserve sampled space for a block-code classifier, universal
small-block tables, relative block summaries, and relative superblock summaries.
There is deliberately no dense endpoint-pair or interior block-pair payload in
this budget.
-/
def compactBPCloseSummaryPayloadOverhead
    (codeSlots microSlots blockSummarySlots superSummarySlots : Nat)
    (n : Nat) : Nat :=
  logLogSampledDirectoryOverhead codeSlots n +
    sampledDirectoryOverhead microSlots n +
      sampledDirectoryOverhead blockSummarySlots n +
        sampledDirectoryOverhead superSummarySlots n

theorem compactBPCloseSummaryPayloadOverhead_littleO
    (codeSlots microSlots blockSummarySlots superSummarySlots : Nat) :
    LittleOLinear
      (compactBPCloseSummaryPayloadOverhead
        codeSlots microSlots blockSummarySlots superSummarySlots) := by
  unfold compactBPCloseSummaryPayloadOverhead
  exact
    (((logLogSampledDirectoryOverhead_littleO codeSlots).add
      (sampledDirectoryOverhead_littleO microSlots)).add
      (sampledDirectoryOverhead_littleO blockSummarySlots)).add
      (sampledDirectoryOverhead_littleO superSummarySlots)

theorem concreteBPRangeMinMaxSummaryTable_compact_summary_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth
      codeSlots microSlots blockSummarySlots superSummarySlots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hbudget :
      2 * (blockCount * fieldWidth) <=
        compactBPCloseSummaryPayloadOverhead
          codeSlots microSlots blockSummarySlots superSummarySlots n) :
    let table :=
      concreteBPRangeMinMaxSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear
      (compactBPCloseSummaryPayloadOverhead
        codeSlots microSlots blockSummarySlots superSummarySlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead
          codeSlots microSlots blockSummarySlots superSummarySlots n /\
      (forall {block : Nat} {word : List Bool},
        table.minTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      forall block,
        (table.summaryCosted block).cost <= 2 /\
          (table.summaryCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? with
            | some minExcess, some maxExcess =>
                some (minExcess, maxExcess)
            | _, _ => none := by
  let table :=
    concreteBPRangeMinMaxSummaryTable
      shape blockSize blockCount fieldWidth hwidth
  have hwords :=
    concreteBPRangeMinMaxSummaryTable_read_words_length_le_machine
      shape blockSize blockCount fieldWidth hwidth hmachine
  constructor
  · exact
      compactBPCloseSummaryPayloadOverhead_littleO
        codeSlots microSlots blockSummarySlots superSummarySlots
  constructor
  · have hlen : table.payload.length = 2 * (blockCount * fieldWidth) :=
      table.payload_length
    exact Nat.le_trans (Nat.le_of_eq hlen) hbudget
  constructor
  · intro block word hget
    exact hwords.1 hget
  constructor
  · intro block word hget
    exact hwords.2 hget
  intro block
  exact ⟨table.summaryCosted_cost_le_two block,
    table.summaryCosted_erase block⟩

/-!
## Relative BP block summaries

The absolute min/max summaries above are intentionally too wide for the final
word-RAM profile: storing a `Theta(log n)` excess value for every block costs
too much.  The relative layer below stores sparse absolute superblock
baselines, then encodes each block's min/max excess as a shifted delta inside
the superblock span.  The block-local argmin is stored as a local offset.
-/

theorem rankPrefix_le_rankPrefix_add_distance
    (target : Bool) (bits : List Bool) {lo hi : Nat}
    (hlohi : lo <= hi) (hhi : hi <= bits.length) :
    Succinct.rankPrefix target bits hi <=
      Succinct.rankPrefix target bits lo + (hi - lo) := by
  have hdrop :=
    Succinct.rankPrefix_drop_eq_sub_of_le
      target bits hlohi hhi
  have htail :=
    Succinct.rankPrefix_le_limit target (bits.drop lo) (hi - lo)
  have hmono := Succinct.rankPrefix_mono_limit target bits hlohi
  omega

theorem bpExcessAt_le_bpExcessAt_add_distance_right
    (shape : Cartesian.CartesianShape) {lo hi : Nat}
    (hlohi : lo <= hi) (hhi : hi <= shape.bpCode.length) :
    bpExcessAt shape hi <= bpExcessAt shape lo + (hi - lo) := by
  unfold bpExcessAt
  have hopen :=
    rankPrefix_le_rankPrefix_add_distance
      true shape.bpCode hlohi hhi
  have hcloseMono :=
    Succinct.rankPrefix_mono_limit false shape.bpCode hlohi
  have hloLen : lo <= shape.bpCode.length := Nat.le_trans hlohi hhi
  have hnonneg := bpExcessAt_prefix_nonnegative shape hloLen
  have hsubMono :
      Succinct.rankPrefix true shape.bpCode hi -
          Succinct.rankPrefix false shape.bpCode hi <=
        Succinct.rankPrefix true shape.bpCode hi -
          Succinct.rankPrefix false shape.bpCode lo :=
    Nat.sub_le_sub_left hcloseMono
      (Succinct.rankPrefix true shape.bpCode hi)
  omega

theorem bpExcessAt_le_bpExcessAt_add_distance_left
    (shape : Cartesian.CartesianShape) {lo hi : Nat}
    (hlohi : lo <= hi) (hhi : hi <= shape.bpCode.length) :
    bpExcessAt shape lo <= bpExcessAt shape hi + (hi - lo) := by
  unfold bpExcessAt
  have hopenMono :=
    Succinct.rankPrefix_mono_limit true shape.bpCode hlohi
  have hclose :=
    rankPrefix_le_rankPrefix_add_distance
      false shape.bpCode hlohi hhi
  have hloLen : lo <= shape.bpCode.length := Nat.le_trans hlohi hhi
  have hhiNonneg := bpExcessAt_prefix_nonnegative shape hhi
  have hsubMono :
      Succinct.rankPrefix true shape.bpCode lo -
          Succinct.rankPrefix false shape.bpCode lo <=
        Succinct.rankPrefix true shape.bpCode hi -
          Succinct.rankPrefix false shape.bpCode lo :=
    Nat.sub_le_sub_right hopenMono
      (Succinct.rankPrefix false shape.bpCode lo)
  omega

def bpSuperblockStartBlock (blocksPerSuper block : Nat) : Nat :=
  (block / blocksPerSuper) * blocksPerSuper

def bpSuperblockSpan (blockSize blocksPerSuper : Nat) : Nat :=
  blocksPerSuper * blockSize

def bpSuperblockStartPos
    (blockSize blocksPerSuper block : Nat) : Nat :=
  blockStartOf blockSize (bpSuperblockStartBlock blocksPerSuper block)

theorem bpSuperblockStartBlock_le
    {blocksPerSuper block : Nat} :
    bpSuperblockStartBlock blocksPerSuper block <= block := by
  unfold bpSuperblockStartBlock
  by_cases hzero : blocksPerSuper = 0
  · simp [hzero]
  · exact Nat.div_mul_le_self block blocksPerSuper

theorem block_lt_bpSuperblockStartBlock_add_blocksPerSuper
    {blocksPerSuper block : Nat} (hblocks : 0 < blocksPerSuper) :
    block < bpSuperblockStartBlock blocksPerSuper block + blocksPerSuper := by
  unfold bpSuperblockStartBlock
  have h := (Nat.div_add_mod block blocksPerSuper).symm
  have hmod := Nat.mod_lt block hblocks
  calc
    block = blocksPerSuper * (block / blocksPerSuper) +
        block % blocksPerSuper := h
    _ = (block / blocksPerSuper) * blocksPerSuper +
        block % blocksPerSuper := by rw [Nat.mul_comm]
    _ < (block / blocksPerSuper) * blocksPerSuper +
        blocksPerSuper := Nat.add_lt_add_left hmod _

theorem blockStart_add_offset_le_blockCount_mul
    {blockSize blockCount block offset : Nat}
    (hblock : block < blockCount) (hoffset : offset <= blockSize) :
    blockStartOf blockSize block + offset <= blockCount * blockSize := by
  unfold blockStartOf
  have hsucc : block + 1 <= blockCount := by omega
  have hmul := Nat.mul_le_mul_right blockSize hsucc
  have hleft :
      block * blockSize + offset <= (block + 1) * blockSize := by
    have hsuccMul :
        (block + 1) * blockSize = block * blockSize + blockSize := by
      rw [Nat.add_mul]
      simp
    rw [hsuccMul]
    exact Nat.add_le_add_left hoffset (block * blockSize)
  exact Nat.le_trans hleft hmul

theorem bpSuperblockStartPos_le_blockStart_add_offset
    {blockSize blocksPerSuper block offset : Nat} :
    bpSuperblockStartPos blockSize blocksPerSuper block <=
      blockStartOf blockSize block + offset := by
  unfold bpSuperblockStartPos blockStartOf
  have hblock := bpSuperblockStartBlock_le
      (blocksPerSuper := blocksPerSuper) (block := block)
  have hmul := Nat.mul_le_mul_right blockSize hblock
  omega

theorem blockStart_add_offset_le_bpSuperblockEnd
    {blockSize blocksPerSuper block offset : Nat}
    (hblocks : 0 < blocksPerSuper) (hoffset : offset <= blockSize) :
    blockStartOf blockSize block + offset <=
      bpSuperblockStartPos blockSize blocksPerSuper block +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpSuperblockStartPos bpSuperblockSpan blockStartOf
  have hblock :
      block + 1 <=
        bpSuperblockStartBlock blocksPerSuper block + blocksPerSuper := by
    have hlt :=
      block_lt_bpSuperblockStartBlock_add_blocksPerSuper
        (block := block) hblocks
    omega
  have hmul := Nat.mul_le_mul_right blockSize hblock
  have hleft :
      block * blockSize + offset <= (block + 1) * blockSize := by
    have hsuccMul :
        (block + 1) * blockSize = block * blockSize + blockSize := by
      rw [Nat.add_mul]
      simp
    rw [hsuccMul]
    exact Nat.add_le_add_left hoffset (block * blockSize)
  have hend :
      (bpSuperblockStartBlock blocksPerSuper block + blocksPerSuper) *
          blockSize =
        bpSuperblockStartBlock blocksPerSuper block * blockSize +
          blocksPerSuper * blockSize := by
    rw [Nat.add_mul]
  exact Nat.le_trans hleft (by simpa [hend] using hmul)

theorem bpBlockSample_excess_le_baseline_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block offset : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hoffset : offset <= blockSize) :
    bpExcessAt shape (blockStartOf blockSize block + offset) <=
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  have hlohi :=
    bpSuperblockStartPos_le_blockStart_add_offset
      (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
      (block := block) (offset := offset)
  have hsampleLeBlockCount :
      blockStartOf blockSize block + offset <= blockCount * blockSize :=
    blockStart_add_offset_le_blockCount_mul hblock hoffset
  have hsampleLen :
      blockStartOf blockSize block + offset <= shape.bpCode.length :=
    Nat.le_trans hsampleLeBlockCount hcover
  have hdist :
      blockStartOf blockSize block + offset -
          bpSuperblockStartPos blockSize blocksPerSuper block <=
        bpSuperblockSpan blockSize blocksPerSuper := by
    have hend :=
      blockStart_add_offset_le_bpSuperblockEnd
        (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
        (block := block) (offset := offset) hblocks hoffset
    omega
  have hvar :=
    bpExcessAt_le_bpExcessAt_add_distance_right
      shape hlohi hsampleLen
  omega

theorem bpBlockSample_baseline_le_excess_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block offset : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hoffset : offset <= blockSize) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) <=
      bpExcessAt shape (blockStartOf blockSize block + offset) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  have hlohi :=
    bpSuperblockStartPos_le_blockStart_add_offset
      (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
      (block := block) (offset := offset)
  have hsampleLeBlockCount :
      blockStartOf blockSize block + offset <= blockCount * blockSize :=
    blockStart_add_offset_le_blockCount_mul hblock hoffset
  have hsampleLen :
      blockStartOf blockSize block + offset <= shape.bpCode.length :=
    Nat.le_trans hsampleLeBlockCount hcover
  have hdist :
      blockStartOf blockSize block + offset -
          bpSuperblockStartPos blockSize blocksPerSuper block <=
        bpSuperblockSpan blockSize blocksPerSuper := by
    have hend :=
      blockStart_add_offset_le_bpSuperblockEnd
        (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
        (block := block) (offset := offset) hblocks hoffset
    omega
  have hvar :=
    bpExcessAt_le_bpExcessAt_add_distance_left
      shape hlohi hsampleLen
  omega

theorem natListMinFrom_le_of_mem
    {seed value : Nat} {values : List Nat}
    (hmem : List.Mem value values) :
    natListMinFrom seed values <= value := by
  induction values generalizing seed with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          exact Nat.le_trans
            (natListMinFrom_le_seed (Nat.min seed value) tail)
            (Nat.min_le_right seed value)
      | tail _ htail =>
          exact ih (seed := Nat.min seed head) htail

theorem le_natListMinFrom_add_of_forall_mem
    {lower seed span : Nat} {values : List Nat}
    (hseed : lower <= seed + span)
    (hmem : forall {value : Nat}, List.Mem value values ->
      lower <= value + span) :
    lower <= natListMinFrom seed values + span := by
  induction values generalizing seed with
  | nil =>
      simpa [natListMinFrom] using hseed
  | cons head tail ih =>
      have hhead : lower <= head + span :=
        hmem List.mem_cons_self
      have htail : forall {value : Nat}, List.Mem value tail ->
          lower <= value + span := by
        intro value hvalue
        exact hmem (List.mem_cons_of_mem head hvalue)
      have hminSeed : lower <= Nat.min seed head + span := by
        by_cases hle : seed <= head
        · simpa [Nat.min_eq_left hle] using hseed
        · have hheadLe : head <= seed := Nat.le_of_not_ge hle
          simpa [Nat.min_eq_right hheadLe] using hhead
      exact ih hminSeed htail

theorem le_natListMax_of_mem
    {value : Nat} {values : List Nat}
    (hmem : List.Mem value values) :
    value <= natListMax values := by
  induction values with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          exact Nat.le_max_left value (natListMax tail)
      | tail _ htail =>
          have htailLe := ih htail
          exact Nat.le_trans htailLe (Nat.le_max_right head (natListMax tail))

theorem bpBlockExcessSamples_offset_mem
    (shape : Cartesian.CartesianShape)
    {blockSize block offset : Nat}
    (hoffset : offset <= blockSize) :
    List.Mem
      (bpExcessAt shape (blockStartOf blockSize block + offset))
      (bpBlockExcessSamples shape blockSize block) := by
  unfold bpBlockExcessSamples
  apply List.mem_map.mpr
  refine ⟨offset, ?_, rfl⟩
  simp [Nat.lt_succ_iff, hoffset]

theorem bpBlockMinExcess_le_baseline_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockMinExcess shape blockSize block <=
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpBlockMinExcess
  have hmem :=
    bpBlockExcessSamples_offset_mem
      shape (blockSize := blockSize) (block := block) (offset := 0)
      (by omega)
  have hle :=
    natListMinFrom_le_of_mem
      (seed := shape.bpCode.length) hmem
  have hsample :=
    bpBlockSample_excess_le_baseline_add_span
      shape hblocks hblock hcover (block := block) (offset := 0)
      (by omega)
  exact Nat.le_trans hle hsample

theorem bpBlockMinExcess_baseline_le_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) <=
      bpBlockMinExcess shape blockSize block +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpBlockMinExcess
  apply le_natListMinFrom_add_of_forall_mem
  · have hbaselineLen :
        bpSuperblockStartPos blockSize blocksPerSuper block <=
          shape.bpCode.length := by
      have hstartLe :
          bpSuperblockStartPos blockSize blocksPerSuper block <=
            blockStartOf blockSize block := by
        simpa using
          bpSuperblockStartPos_le_blockStart_add_offset
            (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
            (block := block) (offset := 0)
      have hblockStartLe :
          blockStartOf blockSize block <= blockCount * blockSize := by
        simpa using
          blockStart_add_offset_le_blockCount_mul
            (blockSize := blockSize) (blockCount := blockCount)
            (block := block) (offset := 0) hblock (by omega)
      exact Nat.le_trans (Nat.le_trans hstartLe hblockStartLe) hcover
    have hbaselineExcess :=
      bpExcessAt_le_length shape
        (bpSuperblockStartPos blockSize blocksPerSuper block)
    omega
  · intro value hmem
    unfold bpBlockExcessSamples at hmem
    rcases List.mem_map.mp hmem with ⟨offset, hoffsetMem, hvalue⟩
    have hoffset : offset <= blockSize := by
      simp at hoffsetMem
      omega
    rw [← hvalue]
    exact
      bpBlockSample_baseline_le_excess_add_span
        shape hblocks hblock hcover (block := block)
        (offset := offset) hoffset

theorem bpBlockMaxExcess_le_baseline_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockMaxExcess shape blockSize block <=
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpBlockMaxExcess
  apply natListMax_le_of_forall_mem
  intro value hmem
  unfold bpBlockExcessSamples at hmem
  rcases List.mem_map.mp hmem with ⟨offset, hoffsetMem, hvalue⟩
  have hoffset : offset <= blockSize := by
    simp at hoffsetMem
    omega
  rw [← hvalue]
  exact
    bpBlockSample_excess_le_baseline_add_span
      shape hblocks hblock hcover (block := block)
      (offset := offset) hoffset

theorem bpBlockMaxExcess_baseline_le_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) <=
      bpBlockMaxExcess shape blockSize block +
        bpSuperblockSpan blockSize blocksPerSuper := by
  have hmem :=
    bpBlockExcessSamples_offset_mem
      shape (blockSize := blockSize) (block := block) (offset := 0)
      (by omega)
  have hsampleLeMax :
      bpExcessAt shape (blockStartOf blockSize block + 0) <=
        bpBlockMaxExcess shape blockSize block := by
    unfold bpBlockMaxExcess
    exact le_natListMax_of_mem hmem
  have hbaselineSample :=
    bpBlockSample_baseline_le_excess_add_span
      shape hblocks hblock hcover (block := block) (offset := 0)
      (by omega)
  omega

def bpRelativeExcessEntry
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper block value : Nat) : Nat :=
  value + bpSuperblockSpan blockSize blocksPerSuper -
    bpExcessAt shape
      (bpSuperblockStartPos blockSize blocksPerSuper block)

theorem bpRelativeExcessEntry_le_two_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper block value : Nat}
    (hupper :
      value <=
        bpExcessAt shape
            (bpSuperblockStartPos blockSize blocksPerSuper block) +
          bpSuperblockSpan blockSize blocksPerSuper)
    (hlower :
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) <=
        value + bpSuperblockSpan blockSize blocksPerSuper) :
    bpRelativeExcessEntry shape blockSize blocksPerSuper block value <=
      2 * bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpRelativeExcessEntry
  omega

def bpBlockRelativeMinExcess
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper block : Nat) : Nat :=
  bpRelativeExcessEntry shape blockSize blocksPerSuper block
    (bpBlockMinExcess shape blockSize block)

def bpBlockRelativeMaxExcess
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper block : Nat) : Nat :=
  bpRelativeExcessEntry shape blockSize blocksPerSuper block
    (bpBlockMaxExcess shape blockSize block)

def bpBlockArgMinLocalOffset
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) : Nat :=
  bpBlockArgMinPrefixPos shape blockSize block -
    blockStartOf blockSize block

theorem bpBlockArgMinPrefixPosFrom_le_start_add
    (shape : Cartesian.CartesianShape)
    {start limit pos steps best : Nat}
    (hbest : best <= start + limit)
    (hpos : pos + steps <= start + limit + 1) :
    bpBlockArgMinPrefixPosFrom shape pos steps best <=
      start + limit := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpBlockArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpBlockArgMinPrefixPosFrom
      have hposLe : pos <= start + limit := by omega
      have hsample :
          Nat.min pos shape.bpCode.length <= start + limit := by
        exact Nat.le_trans (Nat.min_le_left pos shape.bpCode.length) hposLe
      by_cases hlt :
          bpExcessAt shape (Nat.min pos shape.bpCode.length) <
            bpExcessAt shape best
      · simp [hlt]
        apply ih
        · exact hsample
        · omega
      · simp [hlt]
        apply ih
        · exact hbest
        · omega

theorem bpBlockArgMinLocalOffset_le_blockSize
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockArgMinLocalOffset shape blockSize block <= blockSize := by
  unfold bpBlockArgMinLocalOffset
  have hargLen :=
    bpBlockArgMinPrefixPos_le_length shape blockSize block
  have hblockStartLen :
      blockStartOf blockSize block <= shape.bpCode.length := by
    have hblockStartLe :
        blockStartOf blockSize block <= blockCount * blockSize := by
      simpa using
        blockStart_add_offset_le_blockCount_mul
          (blockSize := blockSize) (blockCount := blockCount)
          (block := block) (offset := 0) hblock (by omega)
    exact Nat.le_trans hblockStartLe hcover
  have hargUpper :
      bpBlockArgMinPrefixPos shape blockSize block <=
        blockStartOf blockSize block + blockSize := by
    -- The absolute argmin scans only the block samples.  This arithmetic bound
    -- is the one remaining local-position fact needed by the relative table.
    have hblockEndLen :
        blockStartOf blockSize block + blockSize <=
          shape.bpCode.length := by
      have hblockEndLe :
          blockStartOf blockSize block + blockSize <=
            blockCount * blockSize := by
        exact
          blockStart_add_offset_le_blockCount_mul
            (blockSize := blockSize) (blockCount := blockCount)
            (block := block) (offset := blockSize) hblock (by omega)
      exact Nat.le_trans hblockEndLe hcover
    unfold bpBlockArgMinPrefixPos
    apply bpBlockArgMinPrefixPosFrom_le_start_add
    · exact Nat.le_trans
        (Nat.min_le_left (blockStartOf blockSize block)
          shape.bpCode.length) (by omega)
    · omega
  omega

def bpSuperblockBaselineEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper superCount : Nat) : List Nat :=
  (List.range superCount).map fun super =>
    bpExcessAt shape (blockStartOf blockSize (super * blocksPerSuper))

def bpBlockRelativeMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockRelativeMinExcess shape blockSize blocksPerSuper block

def bpBlockRelativeMaxExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block

def bpBlockArgMinLocalOffsetEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockArgMinLocalOffset shape blockSize block

theorem bpSuperblockBaselineEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper superCount : Nat) :
    (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
      superCount).length = superCount := by
  simp [bpSuperblockBaselineEntries]

theorem bpBlockRelativeMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) :
    (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
      blockCount).length = blockCount := by
  simp [bpBlockRelativeMinExcessEntries]

theorem bpBlockRelativeMaxExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) :
    (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
      blockCount).length = blockCount := by
  simp [bpBlockRelativeMaxExcessEntries]

theorem bpBlockArgMinLocalOffsetEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount).length =
      blockCount := by
  simp [bpBlockArgMinLocalOffsetEntries]

theorem bpSuperblockBaselineEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper superCount superWidth entry : Nat}
    (hwidth : shape.bpCode.length < 2 ^ superWidth)
    (hmem :
      List.Mem entry
        (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
          superCount)) :
    entry < 2 ^ superWidth := by
  unfold bpSuperblockBaselineEntries at hmem
  rcases List.mem_map.mp hmem with ⟨super, _hsuper, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpExcessAt_le_length shape
      (blockStartOf blockSize (super * blocksPerSuper))) hwidth

theorem bpBlockRelativeMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount relativeWidth entry : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hmem :
      List.Mem entry
        (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
          blockCount)) :
    entry < 2 ^ relativeWidth := by
  unfold bpBlockRelativeMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, hblockMem, hentry⟩
  have hblock : block < blockCount := by
    simp at hblockMem
    exact hblockMem
  rw [← hentry]
  apply Nat.lt_of_le_of_lt
  · unfold bpBlockRelativeMinExcess
    apply bpRelativeExcessEntry_le_two_span
    · exact bpBlockMinExcess_le_baseline_add_span
        shape hblocks hblock hcover
    · exact bpBlockMinExcess_baseline_le_add_span
        shape hblocks hblock hcover
  · exact hrelativeWidth

theorem bpBlockRelativeMaxExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount relativeWidth entry : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hmem :
      List.Mem entry
        (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
          blockCount)) :
    entry < 2 ^ relativeWidth := by
  unfold bpBlockRelativeMaxExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, hblockMem, hentry⟩
  have hblock : block < blockCount := by
    simp at hblockMem
    exact hblockMem
  rw [← hentry]
  apply Nat.lt_of_le_of_lt
  · unfold bpBlockRelativeMaxExcess
    apply bpRelativeExcessEntry_le_two_span
    · exact bpBlockMaxExcess_le_baseline_add_span
        shape hblocks hblock hcover
    · exact bpBlockMaxExcess_baseline_le_add_span
        shape hblocks hblock hcover
  · exact hrelativeWidth

theorem bpBlockArgMinLocalOffsetEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount relativeWidth entry : Nat}
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hrelativeWidth : blockSize < 2 ^ relativeWidth)
    (hmem :
      List.Mem entry
        (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)) :
    entry < 2 ^ relativeWidth := by
  unfold bpBlockArgMinLocalOffsetEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, hblockMem, hentry⟩
  have hblock : block < blockCount := by
    simp at hblockMem
    exact hblockMem
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpBlockArgMinLocalOffset_le_blockSize shape hblock hcover)
    hrelativeWidth

def relativeBPCloseSummaryPayloadOverhead
    (superSlots blockSlots : Nat) (n : Nat) : Nat :=
  sampledDirectoryOverhead superSlots n +
    logLogSampledDirectoryOverhead blockSlots n

theorem relativeBPCloseSummaryPayloadOverhead_littleO
    (superSlots blockSlots : Nat) :
    LittleOLinear
      (relativeBPCloseSummaryPayloadOverhead superSlots blockSlots) := by
  unfold relativeBPCloseSummaryPayloadOverhead
  exact
    (sampledDirectoryOverhead_littleO superSlots).add
      (logLogSampledDirectoryOverhead_littleO blockSlots)

theorem relativeBPCloseSummaryPayloadOverhead_le_compact
    (superSlots blockSlots n : Nat) :
    relativeBPCloseSummaryPayloadOverhead superSlots blockSlots n <=
      compactBPCloseSummaryPayloadOverhead blockSlots 0 0 superSlots n := by
  simp [relativeBPCloseSummaryPayloadOverhead,
    compactBPCloseSummaryPayloadOverhead, sampledDirectoryOverhead,
    Nat.add_comm]

structure PayloadLiveBPRelativeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat) where
  baselineTable :
    FixedWidthNatTable
      (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount) superWidth
  minRelTable :
    FixedWidthNatTable
      (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount) relativeWidth
  maxRelTable :
    FixedWidthNatTable
      (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount) relativeWidth
  argOffsetTable :
    FixedWidthNatTable
      (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
      relativeWidth
  payload_length_eq :
    baselineTable.payload.length + minRelTable.payload.length +
      maxRelTable.payload.length + argOffsetTable.payload.length = overhead

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) : List Bool :=
  table.baselineTable.payload ++ table.minRelTable.payload ++
    table.maxRelTable.payload ++ table.argOffsetTable.payload

def summaryCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : Costed (Option (Nat × Nat × Nat × Nat)) :=
  Costed.bind (table.baselineTable.readCosted (block / blocksPerSuper))
    fun baseline? =>
      Costed.bind (table.minRelTable.readCosted block) fun minRel? =>
        Costed.bind (table.maxRelTable.readCosted block) fun maxRel? =>
          Costed.map
            (fun argOffset? =>
              match baseline?, minRel?, maxRel?, argOffset? with
              | some baseline, some minRel, some maxRel, some argOffset =>
                  some (baseline, minRel, maxRel, argOffset)
              | _, _, _, _ => none)
            (table.argOffsetTable.readCosted block)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    table.payload.length = overhead := by
  have h := table.payload_length_eq
  simp only [payload, List.length_append]
  omega

theorem summaryCosted_cost_le_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryCosted block).cost <= 4 := by
  unfold summaryCosted
  cases (table.baselineTable.readCosted (block / blocksPerSuper)).value
  <;> cases (table.minRelTable.readCosted block).value
  <;> cases (table.maxRelTable.readCosted block).value
  <;> simp [Costed.bind, Costed.map]

theorem summaryCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryCosted block).erase =
      match
        (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
          superCount)[block / blocksPerSuper]?,
        (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]?,
        (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]?,
        (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
      with
      | some baseline, some minRel, some maxRel, some argOffset =>
          some (baseline, minRel, maxRel, argOffset)
      | _, _, _, _ => none := by
  unfold summaryCosted
  have hbaseline :
      (table.baselineTable.readCosted (block / blocksPerSuper)).value =
        (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
          superCount)[block / blocksPerSuper]? := by
    exact table.baselineTable.readCosted_erase (block / blocksPerSuper)
  have hmin :
      (table.minRelTable.readCosted block).value =
        (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]? := by
    exact table.minRelTable.readCosted_erase block
  have hmax :
      (table.maxRelTable.readCosted block).value =
        (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]? := by
    exact table.maxRelTable.readCosted_erase block
  have harg :
      (table.argOffsetTable.readCosted block).value =
        (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]? := by
    exact table.argOffsetTable.readCosted_erase block
  cases hbaselineEntry :
      (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount)[block / blocksPerSuper]?
  <;> cases hminEntry :
      (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]?
  <;> cases hmaxEntry :
      (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]?
  <;> cases hargEntry :
      (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, hbaseline, hmin, hmax,
    harg, hbaselineEntry, hminEntry, hmaxEntry, hargEntry]

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {index : Nat} {word : List Bool},
      table.baselineTable.store.words[index]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  constructor
  · intro index word hword
    have hlen := table.baselineTable.read_word_length_of_some hword
    omega
  constructor
  · intro block word hword
    have hlen := table.minRelTable.read_word_length_of_some hword
    omega
  constructor
  · intro block word hword
    have hlen := table.maxRelTable.read_word_length_of_some hword
    omega
  intro block word hword
  have hlen := table.argOffsetTable.read_word_length_of_some hword
  omega

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    table.payload.length = overhead /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  constructor
  · exact table.payload_length
  intro block
  exact ⟨table.summaryCosted_cost_le_four block,
    table.summaryCosted_erase block⟩

end PayloadLiveBPRelativeMinMaxArgSummaryTable

def concreteBPRelativeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth) :
    PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      (superCount * superWidth + 3 * (blockCount * relativeWidth)) where
  baselineTable :=
    FixedWidthNatTable.ofEntries
      (bpSuperblockBaselineEntries shape blockSize blocksPerSuper superCount)
      superWidth
      (by
        intro entry hmem
        exact bpSuperblockBaselineEntries_mem_bound hsuperWidth hmem)
  minRelTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount)
      relativeWidth
      (by
        intro entry hmem
        exact bpBlockRelativeMinExcessEntries_mem_bound
          hblocks hcover hrelativeWidth hmem)
  maxRelTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount)
      relativeWidth
      (by
        intro entry hmem
        exact bpBlockRelativeMaxExcessEntries_mem_bound
          hblocks hcover hrelativeWidth hmem)
  argOffsetTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
      relativeWidth
      (by
        intro entry hmem
        exact bpBlockArgMinLocalOffsetEntries_mem_bound
          hcover hargWidth hmem)
  payload_length_eq := by
    have hbase :
        (FixedWidthNatTable.ofEntries
          (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
            superCount)
          superWidth
          (by
            intro entry hmem
            exact bpSuperblockBaselineEntries_mem_bound
              hsuperWidth hmem)).payload.length =
          superCount * superWidth := by
      simpa [bpSuperblockBaselineEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
            superCount)
          superWidth
          (by
            intro entry hmem
            exact bpSuperblockBaselineEntries_mem_bound
              hsuperWidth hmem)).payload_length
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMinExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload.length =
          blockCount * relativeWidth := by
      simpa [bpBlockRelativeMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMinExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload_length
    have hmax :
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMaxExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload.length =
          blockCount * relativeWidth := by
      simpa [bpBlockRelativeMaxExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMaxExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockArgMinLocalOffsetEntries_mem_bound
              hcover hargWidth hmem)).payload.length =
          blockCount * relativeWidth := by
      simpa [bpBlockArgMinLocalOffsetEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockArgMinLocalOffsetEntries_mem_bound
              hcover hargWidth hmem)).payload_length
    omega

theorem concreteBPRelativeMinMaxArgSummaryTable_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    table.payload.length =
        superCount * superWidth + 3 * (blockCount * relativeWidth) /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  exact
    (concreteBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      hblocks hcover hsuperWidth hrelativeWidth hargWidth).profile

theorem concreteBPRelativeMinMaxArgSummaryTable_relative_payload_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth superSlots blockSlots n : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth)
    (hsuperPayload :
      superCount * superWidth <= sampledDirectoryOverhead superSlots n)
    (hblockPayload :
      3 * (blockCount * relativeWidth) <=
        logLogSampledDirectoryOverhead blockSlots n) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    LittleOLinear
      (relativeBPCloseSummaryPayloadOverhead superSlots blockSlots) /\
      table.payload.length <=
        relativeBPCloseSummaryPayloadOverhead superSlots blockSlots n /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  let table :=
    concreteBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      hblocks hcover hsuperWidth hrelativeWidth hargWidth
  constructor
  · exact relativeBPCloseSummaryPayloadOverhead_littleO
      superSlots blockSlots
  constructor
  · have hlen :
        table.payload.length =
          superCount * superWidth + 3 * (blockCount * relativeWidth) :=
      table.payload_length
    change table.payload.length <=
      relativeBPCloseSummaryPayloadOverhead superSlots blockSlots n
    unfold relativeBPCloseSummaryPayloadOverhead
    omega
  intro block
  exact ⟨table.summaryCosted_cost_le_four block,
    table.summaryCosted_erase block⟩

theorem concreteBPRelativeMinMaxArgSummaryTable_compact_payload_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth superSlots blockSlots n : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth)
    (hsuperPayload :
      superCount * superWidth <= sampledDirectoryOverhead superSlots n)
    (hblockPayload :
      3 * (blockCount * relativeWidth) <=
        logLogSampledDirectoryOverhead blockSlots n) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    LittleOLinear
      (compactBPCloseSummaryPayloadOverhead blockSlots 0 0 superSlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead blockSlots 0 0 superSlots n /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  let table :=
    concreteBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      hblocks hcover hsuperWidth hrelativeWidth hargWidth
  have hrel :=
    concreteBPRelativeMinMaxArgSummaryTable_relative_payload_profile
      shape blockSize blocksPerSuper blockCount superCount superWidth
      relativeWidth superSlots blockSlots n hblocks hcover hsuperWidth
      hrelativeWidth hargWidth hsuperPayload hblockPayload
  constructor
  · exact
      compactBPCloseSummaryPayloadOverhead_littleO
        blockSlots 0 0 superSlots
  constructor
  · exact Nat.le_trans hrel.2.1
      (relativeBPCloseSummaryPayloadOverhead_le_compact
        superSlots blockSlots n)
  · exact hrel.2.2

theorem concreteBPRelativeMinMaxArgSummaryTable_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    (forall {index : Nat} {word : List Bool},
      table.baselineTable.store.words[index]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPRelativeMinMaxArgSummaryTable.read_words_length_le_machine
      (concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth)
      hsuperMachine hrelativeMachine

def canonicalBPRelativeSummaryBase
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.log2 shape.size + 1

def canonicalBPRelativeSummaryBlockSizeRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  2 * canonicalBPRelativeSummaryBase shape

def canonicalBPRelativeSummaryBlocksPerSuperRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  canonicalBPRelativeSummaryBase shape

def canonicalBPRelativeSummaryBlockCountRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  shape.size / canonicalBPRelativeSummaryBase shape

def canonicalBPRelativeSummarySuperCountRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  canonicalBPRelativeSummaryBlockCountRaw shape /
      canonicalBPRelativeSummaryBlocksPerSuperRaw shape + 1

def canonicalBPRelativeSummarySuperWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits shape.bpCode.length

def canonicalBPRelativeSummaryRelativeWidthRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  2 * (Nat.log2 (canonicalBPRelativeSummaryBase shape) + 1) + 3

def canonicalBPRelativeSummarySuperSlots : Nat := 16

def canonicalBPRelativeSummaryBlockSlots : Nat := 64

def canonicalBPRelativeMinMaxArgSummaryTableActive
    (shape : Cartesian.CartesianShape) : Prop :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let blocksPerSuper := canonicalBPRelativeSummaryBlocksPerSuperRaw shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  let superCount := canonicalBPRelativeSummarySuperCountRaw shape
  let superWidth := canonicalBPRelativeSummarySuperWidth shape
  let relativeWidth := canonicalBPRelativeSummaryRelativeWidthRaw shape
  blockCount * blockSize <= shape.bpCode.length /\
    2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth /\
    blockSize < 2 ^ relativeWidth /\
    superCount * superWidth <=
      sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
        shape.size /\
    3 * (blockCount * relativeWidth) <=
      logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
        shape.size /\
    relativeWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length

instance canonicalBPRelativeMinMaxArgSummaryTableActive_decidable
    (shape : Cartesian.CartesianShape) :
    Decidable (canonicalBPRelativeMinMaxArgSummaryTableActive shape) := by
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive
  infer_instance

def canonicalBPRelativeSummaryBlockSize
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryBlockSizeRaw shape
  else
    0

def canonicalBPRelativeSummaryBlocksPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryBlocksPerSuperRaw shape
  else
    1

def canonicalBPRelativeSummaryBlockCount
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryBlockCountRaw shape
  else
    0

def canonicalBPRelativeSummarySuperCount
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummarySuperCountRaw shape
  else
    0

def canonicalBPRelativeSummaryRelativeWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryRelativeWidthRaw shape
  else
    0

private theorem canonicalBPRelativeSummary_active_parts
    {shape : Cartesian.CartesianShape}
    (hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        shape.bpCode.length /\
      2 * bpSuperblockSpan
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummaryBlockSizeRaw shape <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummarySuperCountRaw shape *
          canonicalBPRelativeSummarySuperWidth shape <=
        sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
          shape.size /\
      3 * (canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryRelativeWidthRaw shape) <=
        logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
          shape.size /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simpa [canonicalBPRelativeMinMaxArgSummaryTableActive] using hactive

def canonicalBPRelativeSummaryLargeRegime
    (shape : Cartesian.CartesianShape) : Prop :=
  let base := canonicalBPRelativeSummaryBase shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  base <= blockCount /\
    canonicalBPRelativeSummarySuperWidth shape <= 8 * base /\
    2 * bpSuperblockSpan
        (canonicalBPRelativeSummaryBlockSizeRaw shape)
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
      2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
    canonicalBPRelativeSummaryBlockSizeRaw shape <
      2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
    canonicalBPRelativeSummaryRelativeWidthRaw shape <=
      canonicalBPRelativeSummarySuperWidth shape

private theorem canonicalBPRelativeSummary_large_parts
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeSummaryBase shape <=
        canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummarySuperWidth shape <=
        8 * canonicalBPRelativeSummaryBase shape /\
      2 * bpSuperblockSpan
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummaryBlockSizeRaw shape <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        canonicalBPRelativeSummarySuperWidth shape := by
  simpa [canonicalBPRelativeSummaryLargeRegime] using hlarge

private theorem canonicalBPRelativeSummary_raw_cover
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape *
        canonicalBPRelativeSummaryBlockSizeRaw shape <=
      shape.bpCode.length := by
  rw [Cartesian.CartesianShape.bpCode_length]
  have hdiv :
      (shape.size / canonicalBPRelativeSummaryBase shape) *
          canonicalBPRelativeSummaryBase shape <= shape.size :=
    Nat.div_mul_le_self shape.size (canonicalBPRelativeSummaryBase shape)
  have hmul := Nat.mul_le_mul_left 2 hdiv
  simpa [canonicalBPRelativeSummaryBlockCountRaw,
    canonicalBPRelativeSummaryBlockSizeRaw, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hmul

private theorem canonicalBPRelativeSummary_superPayload_bound_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeSummarySuperCountRaw shape *
        canonicalBPRelativeSummarySuperWidth shape <=
      sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
        shape.size := by
  rcases canonicalBPRelativeSummary_large_parts (shape := shape) hlarge with
    ⟨hbase_le_count, hsuperWidth, _hspan, _harg, _hmachine⟩
  let base := canonicalBPRelativeSummaryBase shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  have hbase_pos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hdiv_pos : 1 <= blockCount / base := by
    exact (Nat.le_div_iff_mul_le hbase_pos).2 (by
      simpa [Nat.mul_comm] using hbase_le_count)
  have hsuperCount_le :
      blockCount / base + 1 <= 2 * (blockCount / base) := by
    omega
  have hright_le :
      (2 * (blockCount / base)) * (8 * base) <= 16 * blockCount := by
    have hdiv :
        (blockCount / base) * base <= blockCount :=
      Nat.div_mul_le_self blockCount base
    have hmul := Nat.mul_le_mul_left 16 hdiv
    calc
      (2 * (blockCount / base)) * (8 * base) =
          16 * ((blockCount / base) * base) := by
        calc
          (2 * (blockCount / base)) * (8 * base) =
              (2 * (blockCount / base)) * (base * 8) := by
            rw [Nat.mul_comm 8 base]
          _ = ((2 * (blockCount / base)) * base) * 8 := by
            rw [← Nat.mul_assoc]
          _ = (2 * ((blockCount / base) * base)) * 8 := by
            rw [Nat.mul_assoc 2 (blockCount / base) base]
          _ = 8 * (2 * ((blockCount / base) * base)) := by
            rw [Nat.mul_comm]
          _ = (8 * 2) * ((blockCount / base) * base) := by
            rw [Nat.mul_assoc]
          _ = 16 * ((blockCount / base) * base) := by
            simp
      _ <= 16 * blockCount := hmul
  have hmul :
      (blockCount / base + 1) *
          canonicalBPRelativeSummarySuperWidth shape <=
        (2 * (blockCount / base)) * (8 * base) :=
    Nat.mul_le_mul hsuperCount_le hsuperWidth
  have hbudget := Nat.le_trans hmul hright_le
  simpa [canonicalBPRelativeSummarySuperCountRaw,
    canonicalBPRelativeSummaryBlockCountRaw, canonicalBPRelativeSummaryBase,
    canonicalBPRelativeSummarySuperSlots, sampledDirectoryOverhead, base,
    blockCount] using hbudget

private theorem canonicalBPRelativeSummary_blockPayload_bound_raw
    (shape : Cartesian.CartesianShape) :
    3 * (canonicalBPRelativeSummaryBlockCountRaw shape *
        canonicalBPRelativeSummaryRelativeWidthRaw shape) <=
      logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
        shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  let logBase := Nat.log2 base + 1
  have hlog_pos : 0 < logBase := by
    simp [logBase]
  have hfactor :
      3 * (2 * logBase + 3) <= 64 * logBase := by
    omega
  have hmul := Nat.mul_le_mul_left blockCount hfactor
  simpa [canonicalBPRelativeSummaryRelativeWidthRaw,
    canonicalBPRelativeSummaryBlockCountRaw, canonicalBPRelativeSummaryBase,
    canonicalBPRelativeSummaryBlockSlots, logLogSampledDirectoryOverhead,
    base, blockCount, logBase, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using hmul

theorem canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeMinMaxArgSummaryTableActive shape := by
  rcases canonicalBPRelativeSummary_large_parts (shape := shape) hlarge with
    ⟨_hbase_le_count, _hsuperWidth, hspan, harg, hmachine⟩
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive
  exact ⟨canonicalBPRelativeSummary_raw_cover shape, hspan, harg,
    canonicalBPRelativeSummary_superPayload_bound_of_large
      (shape := shape) hlarge,
    canonicalBPRelativeSummary_blockPayload_bound_raw shape,
    hmachine⟩

theorem canonicalBPRelativeSummary_blocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < canonicalBPRelativeSummaryBlocksPerSuper shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · simp [canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummaryBlocksPerSuperRaw,
      canonicalBPRelativeSummaryBase, hactive]
  · simp [canonicalBPRelativeSummaryBlocksPerSuper, hactive]

theorem canonicalBPRelativeSummary_cover
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCount shape *
        canonicalBPRelativeSummaryBlockSize shape <=
      shape.bpCode.length := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryBlockSize, hactive] using hparts.1
  · simp [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryBlockSize, hactive]

theorem canonicalBPRelativeSummary_superWidth_bound
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      2 ^ canonicalBPRelativeSummarySuperWidth shape := by
  unfold canonicalBPRelativeSummarySuperWidth
  unfold SuccinctRankProposal.machineWordBits
  exact Nat.lt_log2_self (n := shape.bpCode.length)

theorem canonicalBPRelativeSummary_relativeWidth_bound
    (shape : Cartesian.CartesianShape) :
    2 * bpSuperblockSpan
        (canonicalBPRelativeSummaryBlockSize shape)
        (canonicalBPRelativeSummaryBlocksPerSuper shape) <
      2 ^ canonicalBPRelativeSummaryRelativeWidth shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummaryRelativeWidth, hactive] using hparts.2.1
  · simp [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummaryRelativeWidth, bpSuperblockSpan, hactive]

theorem canonicalBPRelativeSummary_argWidth_bound
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockSize shape <
      2 ^ canonicalBPRelativeSummaryRelativeWidth shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryRelativeWidth, hactive] using hparts.2.2.1
  · simp [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryRelativeWidth, hactive]

theorem canonicalBPRelativeSummary_superPayload_bound
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummarySuperCount shape *
        canonicalBPRelativeSummarySuperWidth shape <=
      sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
        shape.size := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummarySuperCount, hactive] using
      hparts.2.2.2.1
  · simp [canonicalBPRelativeSummarySuperCount, hactive]

theorem canonicalBPRelativeSummary_blockPayload_bound
    (shape : Cartesian.CartesianShape) :
    3 * (canonicalBPRelativeSummaryBlockCount shape *
        canonicalBPRelativeSummaryRelativeWidth shape) <=
      logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
        shape.size := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryRelativeWidth, hactive] using
      hparts.2.2.2.2.1
  · simp [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryRelativeWidth, hactive]

theorem canonicalBPRelativeSummary_superWidth_machine
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummarySuperWidth shape <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact Nat.le_refl _

theorem canonicalBPRelativeSummary_relativeWidth_machine
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryRelativeWidth shape <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryRelativeWidth, hactive] using
      hparts.2.2.2.2.2
  · simp [canonicalBPRelativeSummaryRelativeWidth, hactive]

def concreteBPRelativeMinMaxArgSummaryTable_canonical
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRelativeMinMaxArgSummaryTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlocksPerSuper shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummarySuperCount shape)
      (canonicalBPRelativeSummarySuperWidth shape)
      (canonicalBPRelativeSummaryRelativeWidth shape)
      (canonicalBPRelativeSummarySuperCount shape *
          canonicalBPRelativeSummarySuperWidth shape +
        3 * (canonicalBPRelativeSummaryBlockCount shape *
          canonicalBPRelativeSummaryRelativeWidth shape)) :=
  concreteBPRelativeMinMaxArgSummaryTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlocksPerSuper shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (canonicalBPRelativeSummarySuperCount shape)
    (canonicalBPRelativeSummarySuperWidth shape)
    (canonicalBPRelativeSummaryRelativeWidth shape)
    (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
    (canonicalBPRelativeSummary_cover shape)
    (canonicalBPRelativeSummary_superWidth_bound shape)
    (canonicalBPRelativeSummary_relativeWidth_bound shape)
    (canonicalBPRelativeSummary_argWidth_bound shape)

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile
    (shape : Cartesian.CartesianShape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    LittleOLinear
      (compactBPCloseSummaryPayloadOverhead
        canonicalBPRelativeSummaryBlockSlots 0 0
        canonicalBPRelativeSummarySuperSlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlocksPerSuper shape)
                (canonicalBPRelativeSummarySuperCount shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuper shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlocksPerSuper shape)
                (canonicalBPRelativeSummaryBlockCount shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlocksPerSuper shape)
                (canonicalBPRelativeSummaryBlockCount shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlockCount shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  have hprofile :=
    concreteBPRelativeMinMaxArgSummaryTable_compact_payload_profile
      shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlocksPerSuper shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummarySuperCount shape)
      (canonicalBPRelativeSummarySuperWidth shape)
      (canonicalBPRelativeSummaryRelativeWidth shape)
      canonicalBPRelativeSummarySuperSlots
      canonicalBPRelativeSummaryBlockSlots
      shape.size
      (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
      (canonicalBPRelativeSummary_cover shape)
      (canonicalBPRelativeSummary_superWidth_bound shape)
      (canonicalBPRelativeSummary_relativeWidth_bound shape)
      (canonicalBPRelativeSummary_argWidth_bound shape)
      (canonicalBPRelativeSummary_superPayload_bound shape)
      (canonicalBPRelativeSummary_blockPayload_bound shape)
  have hwords :=
    concreteBPRelativeMinMaxArgSummaryTable_read_words_length_le_machine
      shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlocksPerSuper shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummarySuperCount shape)
      (canonicalBPRelativeSummarySuperWidth shape)
      (canonicalBPRelativeSummaryRelativeWidth shape)
      (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
      (canonicalBPRelativeSummary_cover shape)
      (canonicalBPRelativeSummary_superWidth_bound shape)
      (canonicalBPRelativeSummary_relativeWidth_bound shape)
      (canonicalBPRelativeSummary_argWidth_bound shape)
      (canonicalBPRelativeSummary_superWidth_machine shape)
      (canonicalBPRelativeSummary_relativeWidth_machine shape)
  exact ⟨hprofile.1, hprofile.2.1, hprofile.2.2, hwords.1,
    hwords.2.1, hwords.2.2.1, hwords.2.2.2⟩

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_large
    (shape : Cartesian.CartesianShape)
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    canonicalBPRelativeSummaryBlockSize shape =
        canonicalBPRelativeSummaryBlockSizeRaw shape /\
      canonicalBPRelativeSummaryBlocksPerSuper shape =
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      canonicalBPRelativeSummaryBlockCount shape =
        canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummarySuperCount shape =
        canonicalBPRelativeSummarySuperCountRaw shape /\
      canonicalBPRelativeSummaryRelativeWidth shape =
        canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      LittleOLinear
        (compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummarySuperCountRaw shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuperRaw shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hprofile :=
    concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile
      shape
  exact ⟨by
      simp [canonicalBPRelativeSummaryBlockSize, hactive],
    by
      simp [canonicalBPRelativeSummaryBlocksPerSuper, hactive],
    by
      simp [canonicalBPRelativeSummaryBlockCount, hactive],
    by
      simp [canonicalBPRelativeSummarySuperCount, hactive],
    by
      simp [canonicalBPRelativeSummaryRelativeWidth, hactive],
    by
      simpa [canonicalBPRelativeSummaryBlockSize,
        canonicalBPRelativeSummaryBlocksPerSuper,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummarySuperCount,
        canonicalBPRelativeSummaryRelativeWidth, hactive] using hprofile⟩

theorem canonicalBPRelativeSummaryBlockSizeRaw_pos
    (shape : Cartesian.CartesianShape) :
    0 < canonicalBPRelativeSummaryBlockSizeRaw shape := by
  simp [canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBase]

theorem canonicalBPRelativeSummaryBlocksPerSuperRaw_pos
    (shape : Cartesian.CartesianShape) :
    0 < canonicalBPRelativeSummaryBlocksPerSuperRaw shape := by
  simp [canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryBase]

theorem canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape *
        canonicalBPRelativeSummaryBlockSizeRaw shape <=
      shape.bpCode.length :=
  canonicalBPRelativeSummary_raw_cover shape

theorem canonicalBPRelativeSummaryBlockCountRaw_pos_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    0 < canonicalBPRelativeSummaryBlockCountRaw shape := by
  rcases canonicalBPRelativeSummary_large_parts
      (shape := shape) hlarge with
    ⟨hbase_le_count, _hsuperWidth, _hspan, _harg, _hmachine⟩
  have hbase_pos : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  omega

theorem canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape <= shape.bpCode.length := by
  have hcover :=
    canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
      shape
  have hsize : 1 <= canonicalBPRelativeSummaryBlockSizeRaw shape :=
    Nat.succ_le_of_lt (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
  have hcount_le_mul :
      canonicalBPRelativeSummaryBlockCountRaw shape <=
        canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape := by
    calc
      canonicalBPRelativeSummaryBlockCountRaw shape =
          canonicalBPRelativeSummaryBlockCountRaw shape * 1 := by
        rw [Nat.mul_one]
      _ <=
          canonicalBPRelativeSummaryBlockCountRaw shape *
            canonicalBPRelativeSummaryBlockSizeRaw shape :=
        Nat.mul_le_mul_left
          (canonicalBPRelativeSummaryBlockCountRaw shape) hsize
  exact Nat.le_trans hcount_le_mul hcover

theorem canonicalBPRelativeSummaryRelativeWidthRaw_machine_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeSummaryRelativeWidthRaw shape <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  rcases canonicalBPRelativeSummary_large_parts
      (shape := shape) hlarge with
    ⟨_hbase_le_count, _hsuperWidth, _hspan, _harg, hmachine⟩
  simpa [canonicalBPRelativeSummarySuperWidth] using hmachine

def concreteBPRelativeRmmInteriorNodeSlots : Nat := 64

def concreteBPRelativeRmmInteriorTopSlots : Nat := 16

def concreteBPRelativeRmmInteriorQueryCost : Nat := 8

/--
Canonical compact overhead envelope for the intended relative-rmM interior
navigator.

The first summand is the charged relative min/max/arg block summary table.  The
last two summands reserve fixed many log-log and sampled directory words for
the compact rmM/min-max-tree routing layer.  There is intentionally no dense
`interiorBlockPairRanges` or all-pairs range payload in this budget.
-/
def concreteBPRelativeRmmInteriorOverhead (n : Nat) : Nat :=
  compactBPCloseSummaryPayloadOverhead
      canonicalBPRelativeSummaryBlockSlots 0 0
      canonicalBPRelativeSummarySuperSlots n +
    logLogSampledDirectoryOverhead concreteBPRelativeRmmInteriorNodeSlots n +
      sampledDirectoryOverhead concreteBPRelativeRmmInteriorTopSlots n

theorem concreteBPRelativeRmmInteriorOverhead_littleO :
    LittleOLinear concreteBPRelativeRmmInteriorOverhead := by
  unfold concreteBPRelativeRmmInteriorOverhead
  exact
    ((compactBPCloseSummaryPayloadOverhead_littleO
      canonicalBPRelativeSummaryBlockSlots 0 0
      canonicalBPRelativeSummarySuperSlots).add
      (logLogSampledDirectoryOverhead_littleO
        concreteBPRelativeRmmInteriorNodeSlots)).add
      (sampledDirectoryOverhead_littleO
        concreteBPRelativeRmmInteriorTopSlots)

theorem concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_large
    (shape : Cartesian.CartesianShape)
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    canonicalBPRelativeSummaryBlockSize shape =
        canonicalBPRelativeSummaryBlockSizeRaw shape /\
      canonicalBPRelativeSummaryBlocksPerSuper shape =
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      canonicalBPRelativeSummaryBlockCount shape =
        canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummarySuperCount shape =
        canonicalBPRelativeSummarySuperCountRaw shape /\
      canonicalBPRelativeSummaryRelativeWidth shape =
        canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      canonicalBPRelativeMinMaxArgSummaryTableActive shape /\
      0 < canonicalBPRelativeSummaryBlockSizeRaw shape /\
      0 < canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      0 < canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        shape.bpCode.length /\
      canonicalBPRelativeSummaryBlockCountRaw shape <=
        shape.bpCode.length /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length /\
      table.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummarySuperCountRaw shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuperRaw shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  have hsummary :=
    concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_large
      shape hlarge
  rcases hsummary with
    ⟨hblockSize, hblocksPerSuper, hblockCount, hsuperCount,
      hrelativeWidth, _hsummaryLittleO, hsummaryPayload, hsummaryExact,
      hbaselineRead, hminRead, hmaxRead, hargRead⟩
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hrelativeMachine :=
    canonicalBPRelativeSummaryRelativeWidthRaw_machine_of_large
      (shape := shape) hlarge
  have hpayloadLe :
      compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots shape.size <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    unfold concreteBPRelativeRmmInteriorOverhead
    omega
  exact ⟨hblockSize, hblocksPerSuper, hblockCount, hsuperCount,
    hrelativeWidth, concreteBPRelativeRmmInteriorOverhead_littleO,
    hactive, canonicalBPRelativeSummaryBlockSizeRaw_pos shape,
    canonicalBPRelativeSummaryBlocksPerSuperRaw_pos shape,
    canonicalBPRelativeSummaryBlockCountRaw_pos_of_large
      (shape := shape) hlarge,
    canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
      shape,
    canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length shape,
    hrelativeMachine, Nat.le_trans hsummaryPayload hpayloadLe,
    hsummaryExact, hbaselineRead, hminRead, hmaxRead, hargRead⟩

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

theorem bpExcessAt_bpBetterArgMinPrefixPos_le_left
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    bpExcessAt shape (bpBetterArgMinPrefixPos shape left right) <=
      bpExcessAt shape left := by
  unfold bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt, Nat.le_of_lt hlt]
  · simp [hlt]

theorem bpExcessAt_bpBetterArgMinPrefixPos_le_right
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    bpExcessAt shape (bpBetterArgMinPrefixPos shape left right) <=
      bpExcessAt shape right := by
  unfold bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt]
  · have hle :
        bpExcessAt shape left <= bpExcessAt shape right := by
      exact Nat.le_of_not_gt hlt
    simp [hlt, hle]

theorem bpBetterArgMinPrefixPos_eq_left_of_excess_le
    (shape : Cartesian.CartesianShape) {left right : Nat}
    (hle :
      bpExcessAt shape left <= bpExcessAt shape right) :
    bpBetterArgMinPrefixPos shape left right = left := by
  unfold bpBetterArgMinPrefixPos
  have hnot :
      ¬ bpExcessAt shape right < bpExcessAt shape left := by
    omega
  simp [hnot]

theorem bpBetterArgMinPrefixPos_eq_right_of_excess_lt
    (shape : Cartesian.CartesianShape) {left right : Nat}
    (hlt :
      bpExcessAt shape right < bpExcessAt shape left) :
    bpBetterArgMinPrefixPos shape left right = right := by
  simp [bpBetterArgMinPrefixPos, hlt]

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

theorem bpRangeMinExcessEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {blockSize : Nat}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]? =
      some (bpRangeMinExcess shape blockSize range.1 range.2) := by
  simp [bpRangeMinExcessEntries, List.getElem?_map, hget]

theorem bpRangeArgMinPrefixPosEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {blockSize : Nat}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? =
      some (bpRangeArgMinPrefixPos shape blockSize range.1 range.2) := by
  simp [bpRangeArgMinPrefixPosEntries, List.getElem?_map, hget]

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

/-!
## Charged endpoint-fringe range repair

The block-pair macro above reads a real position-bearing payload entry, but it
ranges over whole endpoint blocks.  A close/LCA answer needs the exact prefix
interval from `leftClose + 1` through `rightClose + 1`.  The next layer stores
charged prefix-range witnesses for endpoint fringes and combines them with the
existing full-block range witness.
-/

def bpPrefixRangeArgMinPrefixPosFrom
    (shape : Cartesian.CartesianShape) :
    Nat -> Nat -> Nat -> Nat
  | _pos, 0, best => best
  | pos, steps + 1, best =>
      let sample := Nat.min pos shape.bpCode.length
      let best' := bpBetterArgMinPrefixPos shape best sample
      bpPrefixRangeArgMinPrefixPosFrom shape (pos + 1) steps best'

theorem bpPrefixRangeArgMinPrefixPosFrom_le_length
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat)
    (hbest : best <= shape.bpCode.length) :
    bpPrefixRangeArgMinPrefixPosFrom shape pos steps best <=
      shape.bpCode.length := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpPrefixRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      exact ih (pos + 1)
        (bpBetterArgMinPrefixPos shape best
          (Nat.min pos shape.bpCode.length))
        (bpBetterArgMinPrefixPos_le_length shape hbest
          (Nat.min_le_right pos shape.bpCode.length))

theorem bpPrefixRangeArgMinPrefixPosFrom_excess_le_best
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat) :
    bpExcessAt shape
        (bpPrefixRangeArgMinPrefixPosFrom shape pos steps best) <=
      bpExcessAt shape best := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      exact Nat.le_trans
        (ih (pos + 1)
          (bpBetterArgMinPrefixPos shape best
            (Nat.min pos shape.bpCode.length)))
        (bpExcessAt_bpBetterArgMinPrefixPos_le_left shape best
          (Nat.min pos shape.bpCode.length))

theorem bpPrefixRangeArgMinPrefixPosFrom_excess_le_pos_add
    (shape : Cartesian.CartesianShape)
    (pos steps best offset : Nat)
    (hoffset : offset < steps) :
    bpExcessAt shape
        (bpPrefixRangeArgMinPrefixPosFrom shape pos steps best) <=
      bpExcessAt shape (Nat.min (pos + offset) shape.bpCode.length) := by
  induction steps generalizing pos best offset with
  | zero =>
      omega
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      by_cases hzero : offset = 0
      · subst offset
        exact Nat.le_trans
          (bpPrefixRangeArgMinPrefixPosFrom_excess_le_best shape
            (pos + 1) steps
            (bpBetterArgMinPrefixPos shape best
              (Nat.min pos shape.bpCode.length)))
          (bpExcessAt_bpBetterArgMinPrefixPos_le_right shape best
            (Nat.min pos shape.bpCode.length))
      · have hoffsetTail : offset - 1 < steps := by
          omega
        have htail :=
          ih (pos + 1)
            (bpBetterArgMinPrefixPos shape best
              (Nat.min pos shape.bpCode.length))
            (offset - 1) hoffsetTail
        have hpos : pos + 1 + (offset - 1) = pos + offset := by
          omega
        simpa [hpos] using htail

theorem bpPrefixRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat)
    (hall :
      forall {offset : Nat},
        offset < steps ->
          bpExcessAt shape best <=
            bpExcessAt shape
              (Nat.min (pos + offset) shape.bpCode.length)) :
    bpPrefixRangeArgMinPrefixPosFrom shape pos steps best = best := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      have hhead :
          bpBetterArgMinPrefixPos shape best
              (Nat.min pos shape.bpCode.length) = best := by
        exact bpBetterArgMinPrefixPos_eq_left_of_excess_le
          shape (hall (offset := 0) (by omega))
      simp [hhead]
      apply ih
      intro offset hoffset
      have htail := hall (offset := offset + 1) (by omega)
      have hpos :
          pos + (offset + 1) = pos + 1 + offset := by
        omega
      simpa [hpos] using htail

theorem bpPrefixRangeArgMinPrefixPosFrom_eq_of_leftmost_min_excess
    (shape : Cartesian.CartesianShape)
    {pos steps best target : Nat}
    (hbest :
      bpExcessAt shape target < bpExcessAt shape best)
    (hlo : pos <= target)
    (hhi : target < pos + steps)
    (hbound : pos + steps <= shape.bpCode.length + 1)
    (hmin :
      forall {sample : Nat},
        pos <= sample ->
          sample < pos + steps ->
            bpExcessAt shape target <= bpExcessAt shape sample)
    (hleft :
      forall {sample : Nat},
        pos <= sample ->
          sample < target ->
            bpExcessAt shape target < bpExcessAt shape sample) :
    bpPrefixRangeArgMinPrefixPosFrom shape pos steps best = target := by
  induction steps generalizing pos best with
  | zero =>
      omega
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      have hposLeLen : pos <= shape.bpCode.length := by
        omega
      have hsample :
          Nat.min pos shape.bpCode.length = pos :=
        Nat.min_eq_left hposLeLen
      by_cases hposEq : pos = target
      · subst target
        have hchoose :
            bpBetterArgMinPrefixPos shape best
                (Nat.min pos shape.bpCode.length) = pos := by
          rw [hsample]
          exact bpBetterArgMinPrefixPos_eq_right_of_excess_lt
            shape hbest
        simp [hchoose]
        exact
          bpPrefixRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape (pos + 1) steps pos (by
              intro offset hoffset
              have hsampleLe :
                  pos + 1 + offset <= shape.bpCode.length := by
                omega
              have hsampleMin :
                  Nat.min (pos + 1 + offset)
                      shape.bpCode.length =
                    pos + 1 + offset :=
                Nat.min_eq_left hsampleLe
              rw [hsampleMin]
              exact hmin (by omega) (by omega))
      · have hposLt : pos < target := by
          omega
        have hsampleGt :
            bpExcessAt shape target <
              bpExcessAt shape
                (Nat.min pos shape.bpCode.length) := by
          rw [hsample]
          exact hleft (by omega) hposLt
        have hnextBest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (Nat.min pos shape.bpCode.length)) := by
          unfold bpBetterArgMinPrefixPos
          by_cases hlt :
              bpExcessAt shape
                  (Nat.min pos shape.bpCode.length) <
                bpExcessAt shape best
          · simp [hlt, hsampleGt]
          · simp [hlt, hbest]
        exact ih hnextBest
          (by omega)
          (by omega)
          (by omega)
          (by
            intro sample hslo hshi
            exact hmin (by omega) (by omega))
          (by
            intro sample hslo hshi
            exact hleft (by omega) hshi)

def bpPrefixRangeArgMinPrefixPos
    (shape : Cartesian.CartesianShape)
    (start count : Nat) : Nat :=
  match count with
  | 0 => Nat.min start shape.bpCode.length
  | steps + 1 =>
      bpPrefixRangeArgMinPrefixPosFrom shape (start + 1) steps
        (Nat.min start shape.bpCode.length)

theorem bpPrefixRangeArgMinPrefixPos_le_length
    (shape : Cartesian.CartesianShape)
    (start count : Nat) :
    bpPrefixRangeArgMinPrefixPos shape start count <=
      shape.bpCode.length := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      exact Nat.min_le_right start shape.bpCode.length
  | succ steps =>
      exact bpPrefixRangeArgMinPrefixPosFrom_le_length shape
        (start + 1) steps (Nat.min start shape.bpCode.length)
        (Nat.min_le_right start shape.bpCode.length)

theorem bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {start count target : Nat}
    (hmem : start <= target /\ target < start + count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        start <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    bpPrefixRangeArgMinPrefixPos shape start count = target := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hstartLeLen : start <= shape.bpCode.length := by
        omega
      have hstartMin :
          Nat.min start shape.bpCode.length = start :=
        Nat.min_eq_left hstartLeLen
      by_cases htargetStart : target = start
      · subst target
        simp [hstartMin]
        exact
          bpPrefixRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape (start + 1) steps start (by
              intro offset hoffset
              have hposLeLen :
                  start + 1 + offset <= shape.bpCode.length := by
                omega
              have hposMin :
                  Nat.min (start + 1 + offset)
                      shape.bpCode.length =
                    start + 1 + offset :=
                Nat.min_eq_left hposLeLen
              rw [hposMin]
              exact hmin (by omega) (by omega))
      · have hstartLt : start < target := by
          omega
        have hbest :
            bpExcessAt shape target < bpExcessAt shape start :=
          hleft (by omega) hstartLt
        simp [hstartMin]
        exact
          bpPrefixRangeArgMinPrefixPosFrom_eq_of_leftmost_min_excess
            shape hbest
            (by omega)
            (by omega)
            (by omega)
            (by
              intro pos hposLo hposHi
              exact hmin (by omega) (by omega))
          (by
            intro pos hposLo hposHi
            exact hleft (by omega) hposHi)

theorem bpPrefixRangeArgMinPrefixPosFrom_mem_range
    (shape : Cartesian.CartesianShape)
    {start pos steps best : Nat}
    (hbest : start <= best /\ best < pos + steps)
    (hpos : start <= pos)
    (hbound : pos + steps <= shape.bpCode.length + 1) :
    start <= bpPrefixRangeArgMinPrefixPosFrom shape pos steps best /\
      bpPrefixRangeArgMinPrefixPosFrom shape pos steps best <
        pos + steps := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpPrefixRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      have hposLeLen : pos <= shape.bpCode.length := by
        omega
      have hsample :
          Nat.min pos shape.bpCode.length = pos :=
        Nat.min_eq_left hposLeLen
      let next :=
        bpBetterArgMinPrefixPos shape best
          (Nat.min pos shape.bpCode.length)
      have hnext :
          start <= next /\ next < pos + 1 + steps := by
        unfold next bpBetterArgMinPrefixPos
        rw [hsample]
        by_cases hlt :
            bpExcessAt shape pos < bpExcessAt shape best
        · simp [hlt]
          omega
        · simp [hlt]
          omega
      have hrec :=
        ih (pos := pos + 1) (best := next)
          hnext (by omega) (by omega)
      simpa [next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hrec

theorem bpPrefixRangeArgMinPrefixPos_mem_range
    {shape : Cartesian.CartesianShape}
    {start count : Nat}
    (hcount : 0 < count)
    (hbound : start + count <= shape.bpCode.length + 1) :
    start <= bpPrefixRangeArgMinPrefixPos shape start count /\
      bpPrefixRangeArgMinPrefixPos shape start count < start + count := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hstartLeLen : start <= shape.bpCode.length := by
        omega
      have hstartMin :
          Nat.min start shape.bpCode.length = start :=
        Nat.min_eq_left hstartLeLen
      simp [hstartMin]
      have hmem :=
        bpPrefixRangeArgMinPrefixPosFrom_mem_range
          shape
          (start := start)
          (pos := start + 1)
          (steps := steps)
          (best := start)
          (by omega) (by omega) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem

theorem bpPrefixRangeArgMinPrefixPos_excess_le_offset
    (shape : Cartesian.CartesianShape)
    (start count offset : Nat)
    (hoffset : offset < count) :
    bpExcessAt shape (bpPrefixRangeArgMinPrefixPos shape start count) <=
      bpExcessAt shape (Nat.min (start + offset) shape.bpCode.length) := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      omega
  | succ steps =>
      cases offset with
      | zero =>
          simpa using
            (bpPrefixRangeArgMinPrefixPosFrom_excess_le_best shape
              (start + 1) steps
              (Nat.min start shape.bpCode.length))
      | succ offset =>
          have hoffsetTail : offset < steps := by
            omega
          have htail :=
            bpPrefixRangeArgMinPrefixPosFrom_excess_le_pos_add shape
              (start + 1) steps (Nat.min start shape.bpCode.length)
              offset hoffsetTail
          have hpos : start + 1 + offset = start + Nat.succ offset := by
            omega
          simpa [hpos] using htail

def bpPrefixRangeMinExcess
    (shape : Cartesian.CartesianShape)
    (start count : Nat) : Nat :=
  bpExcessAt shape (bpPrefixRangeArgMinPrefixPos shape start count)

theorem bpPrefixRangeMinExcess_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {start count target : Nat}
    (hmem : start <= target /\ target < start + count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        start <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    bpPrefixRangeMinExcess shape start count =
      bpExcessAt shape target := by
  unfold bpPrefixRangeMinExcess
  rw [bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
    hmem hbound hmin hleft]

theorem bpPrefixRangeWitness_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {start count target : Nat}
    (hmem : start <= target /\ target < start + count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        start <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    (bpPrefixRangeMinExcess shape start count,
        bpPrefixRangeArgMinPrefixPos shape start count) =
      (bpExcessAt shape target, target) := by
  apply Prod.ext
  · exact
      bpPrefixRangeMinExcess_eq_of_leftmost_min_excess
        hmem hbound hmin hleft
  · exact
      bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
        hmem hbound hmin hleft

theorem bpBlockArgMinPrefixPosFrom_eq_prefixRangeArgMinPrefixPosFrom
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat) :
    bpBlockArgMinPrefixPosFrom shape pos steps best =
      bpPrefixRangeArgMinPrefixPosFrom shape pos steps best := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpBlockArgMinPrefixPosFrom,
        bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpBlockArgMinPrefixPosFrom
      unfold bpPrefixRangeArgMinPrefixPosFrom
      unfold bpBetterArgMinPrefixPos
      by_cases hlt :
          bpExcessAt shape (Nat.min pos shape.bpCode.length) <
            bpExcessAt shape best
      · simp [hlt, ih]
      · simp [hlt, ih]

theorem bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) :
    bpBlockArgMinPrefixPos shape blockSize block =
      bpPrefixRangeArgMinPrefixPos shape
        (blockStartOf blockSize block) (blockSize + 1) := by
  unfold bpBlockArgMinPrefixPos
  unfold bpPrefixRangeArgMinPrefixPos
  have hfirst :
      (if bpExcessAt shape
            (Nat.min (blockStartOf blockSize block)
              shape.bpCode.length) <
          bpExcessAt shape
            (Nat.min (blockStartOf blockSize block)
              shape.bpCode.length)
        then
          Nat.min (blockStartOf blockSize block) shape.bpCode.length
        else
          Nat.min (blockStartOf blockSize block)
            shape.bpCode.length) =
        Nat.min (blockStartOf blockSize block) shape.bpCode.length := by
    simp
  simp [bpBlockArgMinPrefixPosFrom,
    bpBlockArgMinPrefixPosFrom_eq_prefixRangeArgMinPrefixPosFrom]

theorem bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {blockSize block target : Nat}
    (hmem :
      blockStartOf blockSize block <= target /\
        target < blockStartOf blockSize block + (blockSize + 1))
    (hbound :
      blockStartOf blockSize block + (blockSize + 1) <=
        shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        blockStartOf blockSize block <= pos ->
          pos < blockStartOf blockSize block + (blockSize + 1) ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        blockStartOf blockSize block <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    bpBlockArgMinPrefixPos shape blockSize block = target := by
  rw [bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos]
  exact
    bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
      hmem hbound hmin hleft

theorem bpBlockArgMinPrefixPos_mem_range
    {shape : Cartesian.CartesianShape}
    {blockSize block : Nat}
    (hbound :
      blockStartOf blockSize block + (blockSize + 1) <=
        shape.bpCode.length + 1) :
    blockStartOf blockSize block <=
        bpBlockArgMinPrefixPos shape blockSize block /\
      bpBlockArgMinPrefixPos shape blockSize block <
        blockStartOf blockSize block + (blockSize + 1) := by
  rw [bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos]
  exact bpPrefixRangeArgMinPrefixPos_mem_range
    (shape := shape) (start := blockStartOf blockSize block)
    (count := blockSize + 1) (by omega) hbound

def bpRelativeSummaryMinCandidate
    (blockSize blocksPerSuper block : Nat)
    (summary : Nat × Nat × Nat × Nat) : Nat × Nat :=
  let baseline := summary.1
  let minRel := summary.2.1
  let argOffset := summary.2.2.2
  (baseline + minRel - bpSuperblockSpan blockSize blocksPerSuper,
    blockStartOf blockSize block + argOffset)

theorem bpRelativeExcessEntry_decode
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper block value : Nat}
    (hlower :
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) <=
        value + bpSuperblockSpan blockSize blocksPerSuper) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpRelativeExcessEntry shape blockSize blocksPerSuper block value -
      bpSuperblockSpan blockSize blocksPerSuper =
        value := by
  unfold bpRelativeExcessEntry
  omega

theorem bpBlockRelativeMinExcess_decode
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpBlockRelativeMinExcess shape blockSize blocksPerSuper block -
      bpSuperblockSpan blockSize blocksPerSuper =
        bpBlockMinExcess shape blockSize block := by
  exact bpRelativeExcessEntry_decode shape
    (bpBlockMinExcess_baseline_le_add_span
      shape hblocks hblock hcover)

theorem bpBlockArgMinLocalOffset_decode
    {shape : Cartesian.CartesianShape}
    {blockSize block : Nat}
    (hbound :
      blockStartOf blockSize block + (blockSize + 1) <=
        shape.bpCode.length + 1) :
    blockStartOf blockSize block +
        bpBlockArgMinLocalOffset shape blockSize block =
      bpBlockArgMinPrefixPos shape blockSize block := by
  have hmem :=
    bpBlockArgMinPrefixPos_mem_range
      (shape := shape) (blockSize := blockSize) (block := block) hbound
  unfold bpBlockArgMinLocalOffset
  omega

theorem bpBlockArgMinPrefixPos_excess_le_offset
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block offset : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hoffset : offset <= blockSize) :
    bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) <=
      bpExcessAt shape (blockStartOf blockSize block + offset) := by
  have hsampleLe :
      blockStartOf blockSize block + offset <= shape.bpCode.length := by
    have hblockLe :
        blockStartOf blockSize block + offset <= blockCount * blockSize :=
      blockStart_add_offset_le_blockCount_mul
        (blockSize := blockSize) (blockCount := blockCount)
        (block := block) (offset := offset) hblock hoffset
    exact Nat.le_trans hblockLe hcover
  rw [bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos]
  have hle :=
    bpPrefixRangeArgMinPrefixPos_excess_le_offset
      shape (blockStartOf blockSize block) (blockSize + 1) offset
      (by omega)
  simpa [Nat.min_eq_left hsampleLe] using hle

theorem bpBlockMinExcess_eq_excess_argMin
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockMinExcess shape blockSize block =
      bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) := by
  apply Nat.le_antisymm
  · have hbound :
        blockStartOf blockSize block + (blockSize + 1) <=
          shape.bpCode.length + 1 := by
      have hend :
          blockStartOf blockSize block + blockSize <=
            shape.bpCode.length := by
        have hblockEnd :
            blockStartOf blockSize block + blockSize <=
              blockCount * blockSize :=
          blockStart_add_offset_le_blockCount_mul
            (blockSize := blockSize) (blockCount := blockCount)
            (block := block) (offset := blockSize) hblock (by omega)
        exact Nat.le_trans hblockEnd hcover
      omega
    have hmem :=
      bpBlockArgMinPrefixPos_mem_range
        (shape := shape) (blockSize := blockSize) (block := block)
        hbound
    let offset := bpBlockArgMinPrefixPos shape blockSize block -
      blockStartOf blockSize block
    have hoffset : offset <= blockSize := by
      have hstart :
          blockStartOf blockSize block <=
            bpBlockArgMinPrefixPos shape blockSize block := hmem.1
      have hlt :
          bpBlockArgMinPrefixPos shape blockSize block <
            blockStartOf blockSize block + (blockSize + 1) := hmem.2
      omega
    have hsample :
        blockStartOf blockSize block + offset =
          bpBlockArgMinPrefixPos shape blockSize block := by
      have hstart :
          blockStartOf blockSize block <=
            bpBlockArgMinPrefixPos shape blockSize block := hmem.1
      omega
    have hvalueMem :
        List.Mem
          (bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize block))
          (bpBlockExcessSamples shape blockSize block) := by
      have hmemOffset :=
        bpBlockExcessSamples_offset_mem
          shape (blockSize := blockSize) (block := block)
          (offset := offset) hoffset
      simpa [hsample] using hmemOffset
    exact
      natListMinFrom_le_of_mem
        (seed := shape.bpCode.length) hvalueMem
  · unfold bpBlockMinExcess
    have hle :
        bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) <=
          natListMinFrom shape.bpCode.length
            (bpBlockExcessSamples shape blockSize block) + 0 :=
      le_natListMinFrom_add_of_forall_mem
        (span := 0)
        (by
          exact bpExcessAt_le_length shape
            (bpBlockArgMinPrefixPos shape blockSize block))
        (by
          intro value hmem
          unfold bpBlockExcessSamples at hmem
          rcases List.mem_map.mp hmem with ⟨offset, hoffsetMem, hvalue⟩
          have hoffset : offset <= blockSize := by
            simp at hoffsetMem
            omega
          have harg :=
            bpBlockArgMinPrefixPos_excess_le_offset
              shape hblock hcover hoffset
          rw [← hvalue]
          omega)
    omega

theorem bpSuperblockBaselineEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper superCount super : Nat}
    (hsuper : super < superCount) :
    (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount)[super]? =
      some
        (bpExcessAt shape
          (blockStartOf blockSize (super * blocksPerSuper))) := by
  have hget :
      (List.range superCount)[super]? = some super :=
    List.getElem?_range hsuper
  simp [bpSuperblockBaselineEntries, List.getElem?_map, hget]

theorem bpBlockRelativeMinExcessEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]? =
      some
        (bpBlockRelativeMinExcess shape blockSize blocksPerSuper block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockRelativeMinExcessEntries, List.getElem?_map, hget]

theorem bpBlockRelativeMaxExcessEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]? =
      some
        (bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockRelativeMaxExcessEntries, List.getElem?_map, hget]

theorem bpBlockArgMinLocalOffsetEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]? =
      some (bpBlockArgMinLocalOffset shape blockSize block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockArgMinLocalOffsetEntries, List.getElem?_map, hget]

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def minCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.map
    (fun summary? =>
      summary?.map
        (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block))
    (table.summaryCosted block)

theorem minCandidateCosted_cost_le_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.minCandidateCosted block).cost <= 4 := by
  simpa [minCandidateCosted, Costed.map_cost] using
    table.summaryCosted_cost_le_four block

theorem summaryCosted_cost_eq_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryCosted block).cost = 4 := by
  unfold summaryCosted
  cases (table.baselineTable.readCosted (block / blocksPerSuper)).value
  <;> cases (table.minRelTable.readCosted block).value
  <;> cases (table.maxRelTable.readCosted block).value
  <;> simp [Costed.bind, Costed.map]

theorem minCandidateCosted_cost_eq_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.minCandidateCosted block).cost = 4 := by
  simpa [minCandidateCosted, Costed.map_cost] using
    table.summaryCosted_cost_eq_four block

theorem summaryCosted_erase_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblock : block < blockCount)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.summaryCosted block).erase =
      some
        (bpExcessAt shape
            (blockStartOf blockSize
              ((block / blocksPerSuper) * blocksPerSuper)),
          bpBlockRelativeMinExcess shape blockSize blocksPerSuper block,
          bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block,
          bpBlockArgMinLocalOffset shape blockSize block) := by
  rw [table.summaryCosted_erase]
  simp [bpSuperblockBaselineEntries_get?_of_lt hsuper,
    bpBlockRelativeMinExcessEntries_get?_of_lt hblock,
    bpBlockRelativeMaxExcessEntries_get?_of_lt hblock,
    bpBlockArgMinLocalOffsetEntries_get?_of_lt hblock]

theorem minCandidateCosted_erase_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.minCandidateCosted block).erase =
      some
        (bpBlockMinExcess shape blockSize block,
          bpBlockArgMinPrefixPos shape blockSize block) := by
  have hsummary :=
    table.summaryCosted_erase_of_bounds hblock hsuper
  have hmin :=
    bpBlockRelativeMinExcess_decode
      shape hblocks hblock hcover
  have hmin' :
      bpExcessAt shape
          (blockStartOf blockSize
            (block / blocksPerSuper * blocksPerSuper)) +
          bpBlockRelativeMinExcess shape blockSize blocksPerSuper block -
        bpSuperblockSpan blockSize blocksPerSuper =
          bpBlockMinExcess shape blockSize block := by
    simpa [bpSuperblockStartPos, bpSuperblockStartBlock] using hmin
  have hblockEnd :
      blockStartOf blockSize block + blockSize <=
        shape.bpCode.length := by
    have hend :
        blockStartOf blockSize block + blockSize <=
          blockCount * blockSize :=
      blockStart_add_offset_le_blockCount_mul
        (blockSize := blockSize) (blockCount := blockCount)
        (block := block) (offset := blockSize) hblock (by omega)
    exact Nat.le_trans hend hcover
  have harg :=
    bpBlockArgMinLocalOffset_decode
      (shape := shape) (blockSize := blockSize) (block := block)
      (by omega)
  unfold minCandidateCosted
  simp [Costed.erase_map, hsummary, bpRelativeSummaryMinCandidate,
    hmin', harg]

theorem minCandidateCosted_erase_arg_excess_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.minCandidateCosted block).erase =
      some
        (bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block),
          bpBlockArgMinPrefixPos shape blockSize block) := by
  have hread :=
    table.minCandidateCosted_erase_of_bounds
      hblocks hblock hcover hsuper
  have hmin :=
    bpBlockMinExcess_eq_excess_argMin
      shape hblock hcover
  simpa [hmin] using hread

end PayloadLiveBPRelativeMinMaxArgSummaryTable

theorem bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
    (shape : Cartesian.CartesianShape)
    (blockSize block steps best : Nat)
    (hall :
      forall {offset : Nat},
        offset < steps ->
          bpExcessAt shape best <=
            bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize
                (block + offset))) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best = best := by
  induction steps generalizing block best with
  | zero =>
      simp [bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      have hhead :
          bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block) = best := by
        exact bpBetterArgMinPrefixPos_eq_left_of_excess_le
          shape (hall (offset := 0) (by omega))
      simp [hhead]
      apply ih
      intro offset hoffset
      have htail := hall (offset := offset + 1) (by omega)
      have hblock :
          block + (offset + 1) = block + 1 + offset := by
        omega
      simpa [hblock] using htail

theorem bpRangeArgMinPrefixPosFrom_eq_of_leftmost_block_candidate
    (shape : Cartesian.CartesianShape)
    {blockSize block steps best targetBlock target : Nat}
    (hbest :
      bpExcessAt shape target < bpExcessAt shape best)
    (hlo : block <= targetBlock)
    (hhi : targetBlock < block + steps)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        block <= candidateBlock ->
          candidateBlock < block + steps ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        block <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best =
      target := by
  induction steps generalizing block best with
  | zero =>
      omega
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      by_cases hblockEq : block = targetBlock
      · subst targetBlock
        have hchoose :
            bpBetterArgMinPrefixPos shape best
                (bpBlockArgMinPrefixPos shape blockSize block) =
              target := by
          rw [htarget]
          exact bpBetterArgMinPrefixPos_eq_right_of_excess_lt
            shape hbest
        simp [hchoose]
        exact
          bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape blockSize (block + 1) steps target (by
              intro offset hoffset
              exact hmin (by omega) (by omega))
      · have hblockLt : block < targetBlock := by
          omega
        have hcandidateGt :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block) :=
          hleft (by omega) hblockLt
        have hnextBest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
          by_cases hlt :
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize block) <
                bpExcessAt shape best
          · rw [bpBetterArgMinPrefixPos_eq_right_of_excess_lt
              shape hlt]
            exact hcandidateGt
          · have hle :
                bpExcessAt shape best <=
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize block) :=
              Nat.le_of_not_gt hlt
            rw [bpBetterArgMinPrefixPos_eq_left_of_excess_le
              shape hle]
            exact hbest
        exact ih
          (block := block + 1)
          (best :=
            bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block))
          hnextBest
          (by omega)
          (by omega)
          (by
            intro candidateBlock hlo' hhi'
            exact hmin (by omega) (by omega))
          (by
            intro candidateBlock hlo' hlt'
            exact hleft (by omega) hlt')

theorem bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeArgMinPrefixPos shape blockSize startBlock blockCount =
      target := by
  unfold bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      by_cases htargetStart : targetBlock = startBlock
      · subst targetBlock
        rw [htarget]
        exact
          bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape blockSize (startBlock + 1) count target (by
              intro offset hoffset
              exact hmin (by omega) (by omega))
      · have hstartLt : startBlock < targetBlock := by
          omega
        have hbest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock) :=
          hleft (by omega) hstartLt
        exact
          bpRangeArgMinPrefixPosFrom_eq_of_leftmost_block_candidate
            shape hbest
            (by omega)
            (by omega)
            htarget
            (by
              intro candidateBlock hlo hhi
              exact hmin (by omega) (by omega))
            (by
              intro candidateBlock hlo hlt
              exact hleft (by omega) hlt)

theorem bpRangeMinExcess_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeMinExcess shape blockSize startBlock blockCount =
      bpExcessAt shape target := by
  unfold bpRangeMinExcess
  rw [bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
    hblock htarget hmin hleft]

theorem bpRangeWitness_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape target, target) := by
  apply Prod.ext
  · exact
      bpRangeMinExcess_eq_of_leftmost_block_candidate
        hblock htarget hmin hleft
  · exact
      bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
        hblock htarget hmin hleft

theorem bpRangeArgMinPrefixPosFrom_mem_of_best_and_candidates
    (shape : Cartesian.CartesianShape)
    (blockSize block steps best lo hi : Nat)
    (hbest : lo <= best /\ best < hi)
    (hcandidate :
      forall {offset : Nat},
        offset < steps ->
          lo <= bpBlockArgMinPrefixPos shape blockSize (block + offset) /\
            bpBlockArgMinPrefixPos shape blockSize (block + offset) < hi) :
    lo <= bpRangeArgMinPrefixPosFrom shape blockSize block steps best /\
      bpRangeArgMinPrefixPosFrom shape blockSize block steps best < hi := by
  induction steps generalizing block best with
  | zero =>
      simpa [bpRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      let candidate := bpBlockArgMinPrefixPos shape blockSize block
      let next := bpBetterArgMinPrefixPos shape best candidate
      have hcand0 : lo <= candidate /\ candidate < hi := by
        simpa [candidate] using hcandidate (offset := 0) (by omega)
      have hnext : lo <= next /\ next < hi := by
        unfold next bpBetterArgMinPrefixPos
        by_cases hlt : bpExcessAt shape candidate < bpExcessAt shape best
        · simp [hlt, hcand0]
        · simp [hlt, hbest]
      have hrec :=
        ih (block := block + 1) (best := next)
          hnext
          (by
            intro offset hoffset
            have htail := hcandidate (offset := offset + 1) (by omega)
            have hblock :
                block + (offset + 1) = block + 1 + offset := by
              omega
            simpa [hblock] using htail)
      simpa [candidate, next] using hrec

theorem bpRangeArgMinPrefixPos_mem_prefix_range
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount : Nat}
    (hcount : 0 < blockCount)
    (hbound :
      blockStartOf blockSize (startBlock + blockCount) + 1 <=
        shape.bpCode.length + 1) :
    blockStartOf blockSize startBlock <=
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount /\
      bpRangeArgMinPrefixPos shape blockSize startBlock blockCount <
        blockStartOf blockSize (startBlock + blockCount) + 1 := by
  unfold bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      have hstartBlockBound :
          blockStartOf blockSize startBlock + (blockSize + 1) <=
            shape.bpCode.length + 1 := by
        have hlocal :
            blockStartOf blockSize startBlock + (blockSize + 1) <=
              blockStartOf blockSize (startBlock + (count + 1)) + 1 := by
          have hstep :
              blockStartOf blockSize startBlock + (blockSize + 1) =
                blockStartOf blockSize (startBlock + 1) + 1 := by
            rw [← blockStartOf_succ blockSize startBlock]
            omega
          have hmono :
              blockStartOf blockSize (startBlock + 1) <=
                blockStartOf blockSize (startBlock + (count + 1)) :=
            blockStartOf_mono (blockSize := blockSize) (by omega)
          omega
        omega
      have hbestLocal :=
        bpBlockArgMinPrefixPos_mem_range
          (shape := shape) (blockSize := blockSize)
          (block := startBlock) hstartBlockBound
      have hbest :
          blockStartOf blockSize startBlock <=
              bpBlockArgMinPrefixPos shape blockSize startBlock /\
            bpBlockArgMinPrefixPos shape blockSize startBlock <
              blockStartOf blockSize (startBlock + (count + 1)) + 1 := by
        constructor
        · exact hbestLocal.1
        · have hlocal :
              blockStartOf blockSize startBlock + (blockSize + 1) <=
                blockStartOf blockSize (startBlock + (count + 1)) + 1 := by
            have hstep :
                blockStartOf blockSize startBlock + (blockSize + 1) =
                  blockStartOf blockSize (startBlock + 1) + 1 := by
              rw [← blockStartOf_succ blockSize startBlock]
              omega
            have hmono :
                blockStartOf blockSize (startBlock + 1) <=
                  blockStartOf blockSize (startBlock + (count + 1)) :=
              blockStartOf_mono (blockSize := blockSize) (by omega)
            omega
          omega
      exact
        bpRangeArgMinPrefixPosFrom_mem_of_best_and_candidates
          shape blockSize (startBlock + 1) count
          (bpBlockArgMinPrefixPos shape blockSize startBlock)
          (blockStartOf blockSize startBlock)
          (blockStartOf blockSize (startBlock + (count + 1)) + 1)
          hbest
          (by
            intro offset hoffset
            have hcandidateBound :
                blockStartOf blockSize (startBlock + 1 + offset) +
                    (blockSize + 1) <=
                  shape.bpCode.length + 1 := by
              have hlocal :
                  blockStartOf blockSize (startBlock + 1 + offset) +
                      (blockSize + 1) <=
                    blockStartOf blockSize (startBlock + (count + 1)) +
                      1 := by
                have hstep :
                    blockStartOf blockSize (startBlock + 1 + offset) +
                        (blockSize + 1) =
                      blockStartOf blockSize
                          (startBlock + 1 + offset + 1) + 1 := by
                  rw [← blockStartOf_succ
                    blockSize (startBlock + 1 + offset)]
                  omega
                have hmono :
                    blockStartOf blockSize
                        (startBlock + 1 + offset + 1) <=
                      blockStartOf blockSize
                        (startBlock + (count + 1)) :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                omega
              omega
            have hcand :=
              bpBlockArgMinPrefixPos_mem_range
                (shape := shape) (blockSize := blockSize)
                (block := startBlock + 1 + offset)
                hcandidateBound
            constructor
            · have hlo :
                  blockStartOf blockSize startBlock <=
                    blockStartOf blockSize (startBlock + 1 + offset) := by
                exact blockStartOf_mono (blockSize := blockSize) (by omega)
              omega
            · have hhi :
                  blockStartOf blockSize (startBlock + 1 + offset) +
                      (blockSize + 1) <=
                    blockStartOf blockSize (startBlock + (count + 1)) +
                      1 := by
                have hstep :
                    blockStartOf blockSize (startBlock + 1 + offset) +
                        (blockSize + 1) =
                      blockStartOf blockSize
                          (startBlock + 1 + offset + 1) + 1 := by
                  rw [← blockStartOf_succ
                    blockSize (startBlock + 1 + offset)]
                  omega
                have hmono :
                    blockStartOf blockSize
                        (startBlock + 1 + offset + 1) <=
                      blockStartOf blockSize
                        (startBlock + (count + 1)) :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                omega
              omega)

theorem bpPrefixRangeMinExcess_ge_of_all_prefix_ge
    {shape : Cartesian.CartesianShape}
    {start count lower : Nat}
    (hcount : 0 < count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hge :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            lower <= bpExcessAt shape pos) :
    lower <= bpPrefixRangeMinExcess shape start count := by
  have hmem :=
    bpPrefixRangeArgMinPrefixPos_mem_range
      (shape := shape) (start := start) (count := count)
      hcount hbound
  exact hge hmem.1 hmem.2

theorem bpPrefixRangeMinExcess_gt_of_all_prefix_gt
    {shape : Cartesian.CartesianShape}
    {start count lower : Nat}
    (hcount : 0 < count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hgt :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            lower < bpExcessAt shape pos) :
    lower < bpPrefixRangeMinExcess shape start count := by
  have hmem :=
    bpPrefixRangeArgMinPrefixPos_mem_range
      (shape := shape) (start := start) (count := count)
      hcount hbound
  exact hgt hmem.1 hmem.2

theorem bpRangeMinExcess_ge_of_all_prefix_ge
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount lower : Nat}
    (hcount : 0 < blockCount)
    (hbound :
      blockStartOf blockSize (startBlock + blockCount) + 1 <=
        shape.bpCode.length + 1)
    (hge :
      forall {pos : Nat},
        blockStartOf blockSize startBlock <= pos ->
          pos < blockStartOf blockSize (startBlock + blockCount) + 1 ->
            lower <= bpExcessAt shape pos) :
    lower <=
      bpRangeMinExcess shape blockSize startBlock blockCount := by
  have hmem :=
    bpRangeArgMinPrefixPos_mem_prefix_range
      (shape := shape) (blockSize := blockSize)
      (startBlock := startBlock) (blockCount := blockCount)
      hcount hbound
  exact hge hmem.1 hmem.2

theorem bpRangeMinExcess_gt_of_all_prefix_gt
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount lower : Nat}
    (hcount : 0 < blockCount)
    (hbound :
      blockStartOf blockSize (startBlock + blockCount) + 1 <=
        shape.bpCode.length + 1)
    (hgt :
      forall {pos : Nat},
        blockStartOf blockSize startBlock <= pos ->
          pos < blockStartOf blockSize (startBlock + blockCount) + 1 ->
            lower < bpExcessAt shape pos) :
    lower <
      bpRangeMinExcess shape blockSize startBlock blockCount := by
  have hmem :=
    bpRangeArgMinPrefixPos_mem_prefix_range
      (shape := shape) (blockSize := blockSize)
      (startBlock := startBlock) (blockCount := blockCount)
      hcount hbound
  exact hgt hmem.1 hmem.2

theorem bpPrefixRangeMinExcess_le_length
    (shape : Cartesian.CartesianShape)
    (start count : Nat) :
    bpPrefixRangeMinExcess shape start count <= shape.bpCode.length := by
  exact bpExcessAt_le_length shape
    (bpPrefixRangeArgMinPrefixPos shape start count)

theorem bpPrefixRangeMinExcess_le_prefix_of_mem
    {shape : Cartesian.CartesianShape}
    {start count prefixPos : Nat}
    (hmem : start <= prefixPos /\ prefixPos < start + count)
    (hprefix : prefixPos <= shape.bpCode.length) :
    bpPrefixRangeMinExcess shape start count <=
      bpExcessAt shape prefixPos := by
  have hoffset : prefixPos - start < count := by
    omega
  have hmin :=
    bpPrefixRangeArgMinPrefixPos_excess_le_offset shape
      start count (prefixPos - start) hoffset
  have hpos : start + (prefixPos - start) = prefixPos := by
    omega
  simpa [bpPrefixRangeMinExcess, hpos, Nat.min_eq_left hprefix]
    using hmin

theorem bpEndpointPrefixRangeMinExcess_le_answerClose
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    bpPrefixRangeMinExcess shape (leftClose + 1)
        (rightClose - leftClose + 1) <=
      bpExcessAt shape (answerClose + 1) := by
  have hmem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose) hlen hleft hright hanswer
  have hanswerBound := bpCloseOfInorder?_bounds shape hanswer
  have hprefixBound : answerClose + 1 <= shape.bpCode.length := by
    omega
  exact
    bpPrefixRangeMinExcess_le_prefix_of_mem
      (shape := shape)
      (start := leftClose + 1)
      (count := rightClose - leftClose + 1)
      (prefixPos := answerClose + 1)
      hmem hprefixBound

theorem scanWindow_node_representative_spanning_root
    (leftShape rightShape : Cartesian.CartesianShape)
    {start len : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len) :
    scanWindow
        (Cartesian.CartesianShape.node
          leftShape rightShape).representative start len =
      leftShape.size := by
  let xs :=
    (Cartesian.CartesianShape.node
      leftShape rightShape).representative
  let leftValues := Cartesian.addConst 1 leftShape.representative
  let rightValues := Cartesian.addConst 1 rightShape.representative
  have hxs :
      xs = leftValues ++ (0 :: rightValues) := by
    simp [xs, leftValues, rightValues,
      Cartesian.CartesianShape.representative]
  have hleftValuesLen : leftValues.length = leftShape.size := by
    simp [leftValues, Cartesian.addConst_length,
      Cartesian.CartesianShape.representative_length]
  have hrootGet : xs[leftShape.size]? = some 0 := by
    rw [hxs]
    have hidx : leftShape.size = leftValues.length := by
      omega
    simp [hidx]
  have harg :
      LeftmostArgMin xs start (start + len) leftShape.size := by
    refine ⟨by omega, ?_, hrootLo, hrootHi, 0, hrootGet, ?_, ?_⟩
    · simpa [xs, Cartesian.CartesianShape.representative_length] using hbound
    · intro j w _hjLo _hjHi hget
      have hmem : w ∈ xs := List.mem_of_getElem? hget
      have hnonneg :=
        Cartesian.CartesianShape.representative_nonnegative
          (Cartesian.CartesianShape.node leftShape rightShape) w
          (by simpa [xs] using hmem)
      omega
    · intro j w _hjLo hjRoot hget
      have hgetLeft :
          leftValues[j]? = some w := by
        rw [hxs] at hget
        have hjLeftValues : j < leftValues.length := by
          omega
        simpa [List.getElem?_append, hjLeftValues] using hget
      have hpos :=
        Cartesian.CartesianShape.representative_shift_positive
          leftShape w (List.mem_of_getElem? hgetLeft)
      omega
  have hscan :
      LeftmostArgMin xs start (start + len)
        (scanWindow xs start len) := by
    exact scanWindow_leftmost xs start len hlen (by
      simpa [xs, Cartesian.CartesianShape.representative_length] using hbound)
  have huniq :=
    leftmostArgMin_unique xs start (start + len)
      (scanWindow xs start len) leftShape.size hscan harg
  simpa [xs] using huniq

theorem answerClose_eq_root_close_of_spanning_root
    {leftShape rightShape : Cartesian.CartesianShape}
    {start len answerClose : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose) :
    answerClose = leftShape.bpCode.length + 1 := by
  have hscan :=
    scanWindow_node_representative_spanning_root
      leftShape rightShape hlen hbound hrootLo hrootHi
  rw [hscan] at hanswer
  simp [bpCloseOfInorder?] at hanswer
  exact hanswer.symm

theorem answerClose_prefix_leftmost_min_excess_of_spanning_root
    {leftShape rightShape : Cartesian.CartesianShape}
    {start len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (_hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (_hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose) :
    (forall {pos : Nat},
      leftClose + 1 <= pos ->
        pos < rightClose + 2 ->
          bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1) <=
            bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape) pos) /\
      (forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt
                (Cartesian.CartesianShape.node leftShape rightShape)
                (answerClose + 1) <
              bpExcessAt
                (Cartesian.CartesianShape.node leftShape rightShape) pos) := by
  have hanswerEq :=
    answerClose_eq_root_close_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len) (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hanswer
  constructor
  · intro pos _hlo _hhi
    subst answerClose
    exact bpExcessAt_node_root_close_succ_le_prefix
      leftShape rightShape pos
  · intro pos hlo hlt
    subst answerClose
    have hpos : 0 < pos := by
      omega
    exact bpExcessAt_node_root_close_succ_lt_before
      leftShape rightShape hpos hlt

theorem answerClose_prefix_leftmost_min_excess_of_query
    {shape : Cartesian.CartesianShape}
    {start len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : start + len <= shape.size)
    (hleft : bpCloseOfInorder? shape start = some leftClose)
    (hright :
      bpCloseOfInorder? shape (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative start len) =
        some answerClose) :
    (forall {pos : Nat},
      leftClose + 1 <= pos ->
        pos < rightClose + 2 ->
          bpExcessAt shape (answerClose + 1) <=
            bpExcessAt shape pos) /\
      (forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) := by
  induction shape generalizing start len leftClose rightClose answerClose with
  | empty =>
      simp [Cartesian.CartesianShape.size] at hbound
      omega
  | node leftShape rightShape ihLeft ihRight =>
      by_cases hrootLo : start <= leftShape.size
      · by_cases hrootHi : leftShape.size < start + len
        · exact
            answerClose_prefix_leftmost_min_excess_of_spanning_root
              (leftShape := leftShape) (rightShape := rightShape)
              (start := start) (len := len)
              (leftClose := leftClose) (rightClose := rightClose)
              (answerClose := answerClose)
              hlen hbound hrootLo hrootHi hleft hright hanswer
        · have hleftWindow : start + len <= leftShape.size :=
            Nat.le_of_not_gt hrootHi
          have hstartLeft : start < leftShape.size := by
            omega
          have hendLeft : start + len - 1 < leftShape.size := by
            omega
          let leftValues := Cartesian.addConst 1 leftShape.representative
          let rightValues := Cartesian.addConst 1 rightShape.representative
          have hleftValuesBound :
              start + len <= leftValues.length := by
            simp [leftValues, Cartesian.addConst_length,
              Cartesian.CartesianShape.representative_length]
            exact hleftWindow
          have hscanParent :
              scanWindow
                  (Cartesian.CartesianShape.node
                    leftShape rightShape).representative start len =
                scanWindow leftShape.representative start len := by
            have happ :=
              Cartesian.scanWindow_append_left leftValues
                (0 :: rightValues) (left := start) (len := len)
                hleftValuesBound
            calc
              scanWindow
                  (Cartesian.CartesianShape.node
                    leftShape rightShape).representative start len =
                scanWindow (leftValues ++ (0 :: rightValues)) start len := by
                  simp [leftValues, rightValues,
                    Cartesian.CartesianShape.representative]
              _ = scanWindow leftValues start len := happ
              _ = scanWindow leftShape.representative start len := by
                  exact Cartesian.scanWindow_addConst 1
                    leftShape.representative start len
          cases hleftRec :
              bpCloseOfInorder? leftShape start with
          | none =>
              simp [bpCloseOfInorder?, hstartLeft, hleftRec] at hleft
          | some childLeftClose =>
              simp [bpCloseOfInorder?, hstartLeft, hleftRec] at hleft
              subst leftClose
              cases hrightRec :
                  bpCloseOfInorder? leftShape (start + len - 1) with
              | none =>
                  simp [bpCloseOfInorder?, hendLeft, hrightRec] at hright
              | some childRightClose =>
                  simp [bpCloseOfInorder?, hendLeft, hrightRec] at hright
                  subst rightClose
                  have hscanBounds :=
                    Cartesian.scanWindow_bounds leftShape.representative
                      start len hlen
                  have hscanLeft :
                      scanWindow leftShape.representative start len <
                        leftShape.size := by
                    omega
                  cases hanswerRec :
                      bpCloseOfInorder? leftShape
                        (scanWindow leftShape.representative start len) with
                  | none =>
                      simp [bpCloseOfInorder?, hscanParent, hscanLeft,
                        hanswerRec] at hanswer
                  | some childAnswerClose =>
                      simp [bpCloseOfInorder?, hscanParent, hscanLeft,
                        hanswerRec] at hanswer
                      subst answerClose
                      have hchild :=
                        ihLeft hlen hleftWindow hleftRec hrightRec
                          hanswerRec
                      have hanswerBound :
                          childAnswerClose + 1 <= leftShape.bpCode.length := by
                        have hcloseBound :=
                          bpCloseOfInorder?_bounds leftShape hanswerRec
                        omega
                      have hrightBound :
                          childRightClose + 1 <= leftShape.bpCode.length := by
                        have hcloseBound :=
                          bpCloseOfInorder?_bounds leftShape hrightRec
                        omega
                      constructor
                      · intro pos hlo hhi
                        have hchildLo :
                            childLeftClose + 1 <= pos - 1 := by
                          omega
                        have hchildHi :
                            pos - 1 < childRightClose + 2 := by
                          omega
                        have hposBound :
                            pos - 1 <= leftShape.bpCode.length := by
                          omega
                        have hanswerShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := childAnswerClose + 1) hanswerBound
                        have hposShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := pos - 1) hposBound
                        have hposEq : pos = (pos - 1) + 1 := by
                          omega
                        rw [show childAnswerClose + 1 + 1 =
                            (childAnswerClose + 1) + 1 by omega]
                        rw [hanswerShift]
                        rw [hposEq, hposShift]
                        have hcmp := hchild.1 hchildLo hchildHi
                        omega
                      · intro pos hlo hhi
                        have hchildLo :
                            childLeftClose + 1 <= pos - 1 := by
                          omega
                        have hchildHi :
                            pos - 1 < childAnswerClose + 1 := by
                          omega
                        have hposBound :
                            pos - 1 <= leftShape.bpCode.length := by
                          omega
                        have hanswerShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := childAnswerClose + 1) hanswerBound
                        have hposShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := pos - 1) hposBound
                        have hposEq : pos = (pos - 1) + 1 := by
                          omega
                        rw [show childAnswerClose + 1 + 1 =
                            (childAnswerClose + 1) + 1 by omega]
                        rw [hanswerShift]
                        rw [hposEq, hposShift]
                        have hcmp := hchild.2 hchildLo hchildHi
                        omega
      · have hstartRight : leftShape.size < start := Nat.lt_of_not_ge hrootLo
        let localStart := start - leftShape.size - 1
        have hstartEq : start = leftShape.size + 1 + localStart := by
          simp [localStart]
          omega
        have hrightWindow : localStart + len <= rightShape.size := by
          simp [Cartesian.CartesianShape.size] at hbound
          omega
        have hendLocalEq :
            start + len - 1 - leftShape.size - 1 =
              localStart + len - 1 := by
          simp [localStart]
          omega
        let leftValues := Cartesian.addConst 1 leftShape.representative
        let rightValues := Cartesian.addConst 1 rightShape.representative
        let pre := leftValues ++ [0]
        have hpreLen : pre.length = leftShape.size + 1 := by
          simp [pre, leftValues, Cartesian.addConst_length,
            Cartesian.CartesianShape.representative_length]
        have hrightValuesBound :
            localStart + len <= rightValues.length := by
          simp [rightValues, Cartesian.addConst_length,
            Cartesian.CartesianShape.representative_length]
          exact hrightWindow
        have hscanParent :
            scanWindow
                (Cartesian.CartesianShape.node
                  leftShape rightShape).representative start len =
              leftShape.size + 1 +
                scanWindow rightShape.representative localStart len := by
          have happ :=
            Cartesian.scanWindow_append_right pre rightValues
              (left := localStart) (len := len) hrightValuesBound
          calc
            scanWindow
                (Cartesian.CartesianShape.node
                  leftShape rightShape).representative start len =
              scanWindow (pre ++ rightValues) (pre.length + localStart)
                len := by
                have hstartPre : start = pre.length + localStart := by
                  omega
                simp [pre, leftValues, rightValues,
                  Cartesian.CartesianShape.representative, hstartPre,
                  List.append_assoc]
            _ = pre.length + scanWindow rightValues localStart len := happ
            _ = leftShape.size + 1 +
                scanWindow rightShape.representative localStart len := by
                rw [hpreLen]
                rw [Cartesian.scanWindow_addConst]
        have hnotStartLeft : ¬ start < leftShape.size := by
          omega
        have hnotStartRoot : ¬ start = leftShape.size := by
          omega
        cases hleftRec :
            bpCloseOfInorder? rightShape localStart with
        | none =>
            simp [bpCloseOfInorder?, hnotStartLeft, hnotStartRoot,
              localStart, hleftRec] at hleft
        | some childLeftClose =>
            simp [bpCloseOfInorder?, hnotStartLeft, hnotStartRoot,
              localStart, hleftRec] at hleft
            subst leftClose
            have hnotEndLeft : ¬ start + len - 1 < leftShape.size := by
              omega
            have hnotEndRoot : ¬ start + len - 1 = leftShape.size := by
              omega
            cases hrightRec :
                bpCloseOfInorder? rightShape
                  (localStart + len - 1) with
            | none =>
                simp [bpCloseOfInorder?, hnotEndLeft, hnotEndRoot,
                  localStart, hendLocalEq, hrightRec] at hright
            | some childRightClose =>
                simp [bpCloseOfInorder?, hnotEndLeft, hnotEndRoot,
                  localStart, hendLocalEq, hrightRec] at hright
                subst rightClose
                have hscanBounds :=
                  Cartesian.scanWindow_bounds rightShape.representative
                    localStart len hlen
                have hscanRight :
                    scanWindow rightShape.representative localStart len <
                      rightShape.size := by
                  omega
                have hnotAnswerLeft :
                    ¬ scanWindow
                        (Cartesian.CartesianShape.node
                          leftShape rightShape).representative start len <
                      leftShape.size := by
                  rw [hscanParent]
                  omega
                have hnotAnswerRoot :
                    ¬ scanWindow
                        (Cartesian.CartesianShape.node
                          leftShape rightShape).representative start len =
                      leftShape.size := by
                  rw [hscanParent]
                  omega
                have hanswerLocalEq :
                    scanWindow
                          (Cartesian.CartesianShape.node
                            leftShape rightShape).representative start len -
                        leftShape.size - 1 =
                      scanWindow rightShape.representative localStart len := by
                  rw [hscanParent]
                  omega
                cases hanswerRec :
                    bpCloseOfInorder? rightShape
                      (scanWindow rightShape.representative
                        localStart len) with
                | none =>
                    simp [bpCloseOfInorder?, hnotAnswerLeft,
                      hnotAnswerRoot, hanswerLocalEq, hanswerRec] at hanswer
                | some childAnswerClose =>
                    simp [bpCloseOfInorder?, hnotAnswerLeft,
                      hnotAnswerRoot, hanswerLocalEq, hanswerRec] at hanswer
                    subst answerClose
                    have hchild :=
                      ihRight hlen hrightWindow hleftRec hrightRec hanswerRec
                    have hanswerBound :
                        childAnswerClose + 1 <= rightShape.bpCode.length := by
                      have hcloseBound :=
                        bpCloseOfInorder?_bounds rightShape hanswerRec
                      omega
                    have hrightBound :
                        childRightClose + 1 <= rightShape.bpCode.length := by
                      have hcloseBound :=
                        bpCloseOfInorder?_bounds rightShape hrightRec
                      omega
                    constructor
                    · intro pos hlo hhi
                      have hchildLo :
                          childLeftClose + 1 <=
                            pos - (leftShape.bpCode.length + 2) := by
                        omega
                      have hchildHi :
                          pos - (leftShape.bpCode.length + 2) <
                            childRightClose + 2 := by
                        omega
                      have hposBound :
                          pos - (leftShape.bpCode.length + 2) <=
                            rightShape.bpCode.length := by
                        omega
                      have hanswerShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := childAnswerClose + 1) hanswerBound
                      have hposShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := pos - (leftShape.bpCode.length + 2))
                          hposBound
                      have hposEq :
                          pos =
                            leftShape.bpCode.length + 2 +
                              (pos - (leftShape.bpCode.length + 2)) := by
                        omega
                      rw [show leftShape.bpCode.length + 2 +
                          childAnswerClose + 1 =
                        leftShape.bpCode.length + 2 +
                          (childAnswerClose + 1) by omega]
                      rw [hanswerShift]
                      rw [hposEq, hposShift]
                      exact hchild.1 hchildLo hchildHi
                    · intro pos hlo hhi
                      have hchildLo :
                          childLeftClose + 1 <=
                            pos - (leftShape.bpCode.length + 2) := by
                        omega
                      have hchildHi :
                          pos - (leftShape.bpCode.length + 2) <
                            childAnswerClose + 1 := by
                        omega
                      have hposBound :
                          pos - (leftShape.bpCode.length + 2) <=
                            rightShape.bpCode.length := by
                        omega
                      have hanswerShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := childAnswerClose + 1) hanswerBound
                      have hposShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := pos - (leftShape.bpCode.length + 2))
                          hposBound
                      have hposEq :
                          pos =
                            leftShape.bpCode.length + 2 +
                              (pos - (leftShape.bpCode.length + 2)) := by
                        omega
                      rw [show leftShape.bpCode.length + 2 +
                          childAnswerClose + 1 =
                        leftShape.bpCode.length + 2 +
                          (childAnswerClose + 1) by omega]
                      rw [hanswerShift]
                      rw [hposEq, hposShift]
                      exact hchild.2 hchildLo hchildHi

theorem endpointPrefixRangeWitness_eq_answerClose_of_spanning_root
    {leftShape rightShape : Cartesian.CartesianShape}
    {start len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose) :
    (bpPrefixRangeMinExcess
        (Cartesian.CartesianShape.node leftShape rightShape)
        (leftClose + 1) (rightClose - leftClose + 1),
      bpPrefixRangeArgMinPrefixPos
        (Cartesian.CartesianShape.node leftShape rightShape)
        (leftClose + 1) (rightClose - leftClose + 1)) =
      (bpExcessAt
          (Cartesian.CartesianShape.node leftShape rightShape)
          (answerClose + 1),
        answerClose + 1) := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  have hmem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := Cartesian.CartesianShape.node leftShape rightShape)
      (left := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := Cartesian.CartesianShape.node leftShape rightShape)
      (left := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hrightBound :=
    bpCloseOfInorder?_bounds
      (Cartesian.CartesianShape.node leftShape rightShape) hright
  have hrangeBound :
      leftClose + 1 + (rightClose - leftClose + 1) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1 := by
    omega
  exact
    bpPrefixRangeWitness_eq_of_leftmost_min_excess
      hmem hrangeBound
      (by
        intro pos hlo hhi
        exact hsemantic.1 hlo (by omega))
      (by
        intro pos hlo hhi
        exact hsemantic.2 hlo hhi)

def bpPrefixRangeMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range => bpPrefixRangeMinExcess shape range.1 range.2

def bpPrefixRangeArgMinPrefixPosEntries
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range =>
    bpPrefixRangeArgMinPrefixPos shape range.1 range.2

theorem bpPrefixRangeMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) :
    (bpPrefixRangeMinExcessEntries shape ranges).length = ranges.length := by
  simp [bpPrefixRangeMinExcessEntries]

theorem bpPrefixRangeArgMinPrefixPosEntries_length
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) :
    (bpPrefixRangeArgMinPrefixPosEntries shape ranges).length =
      ranges.length := by
  simp [bpPrefixRangeArgMinPrefixPosEntries]

theorem bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]? =
      some (bpPrefixRangeMinExcess shape range.1 range.2) := by
  simp [bpPrefixRangeMinExcessEntries, List.getElem?_map, hget]

theorem bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? =
      some (bpPrefixRangeArgMinPrefixPos shape range.1 range.2) := by
  simp [bpPrefixRangeArgMinPrefixPosEntries, List.getElem?_map, hget]

theorem bpPrefixRangeMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry (bpPrefixRangeMinExcessEntries shape ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpPrefixRangeMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpPrefixRangeMinExcess_le_length shape range.1 range.2) hwidth

theorem bpPrefixRangeArgMinPrefixPosEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry (bpPrefixRangeArgMinPrefixPosEntries shape ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpPrefixRangeArgMinPrefixPosEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpPrefixRangeArgMinPrefixPos_le_length shape range.1 range.2)
    hwidth

structure PayloadLiveBPPrefixRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (fieldWidth overhead : Nat)
    (ranges : List (Nat × Nat)) where
  minTable :
    FixedWidthNatTable
      (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
  argTable :
    FixedWidthNatTable
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
  payload_length_eq :
    minTable.payload.length + argTable.payload.length = overhead

namespace PayloadLiveBPPrefixRangeArgMinWitnessTable

def payload
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) : List Bool :=
  table.minTable.payload ++ table.argTable.payload

def rangeWitnessCosted
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (table.minTable.readCosted rangeIndex) fun min? =>
    Costed.map
      (fun arg? =>
        match min?, arg? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none)
      (table.argTable.readCosted rangeIndex)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem rangeWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).cost <= 2 := by
  unfold rangeWitnessCosted
  cases hread :
      (table.minTable.readCosted rangeIndex).value with
  | none =>
      simp [Costed.bind, Costed.map, hread]
  | some minExcess =>
      simp [Costed.bind, Costed.map, hread]

theorem rangeWitnessCosted_erase
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).erase =
      match
        (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?,
        (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? with
      | some minExcess, some prefixPos => some (minExcess, prefixPos)
      | _, _ => none := by
  unfold rangeWitnessCosted
  have hmin :
      (table.minTable.readCosted rangeIndex).value =
        (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]? := by
    exact table.minTable.readCosted_erase rangeIndex
  have harg :
      (table.argTable.readCosted rangeIndex).value =
        (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? := by
    exact table.argTable.readCosted_erase rangeIndex
  cases hminEntry :
      (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?
  <;> cases hargEntry :
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, hmin, harg,
    hminEntry, hargEntry]

theorem min_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
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
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
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
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
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

theorem profile
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) :
    table.payload.length = overhead /\
      forall rangeIndex,
        (table.rangeWitnessCosted rangeIndex).cost <= 2 /\
          (table.rangeWitnessCosted rangeIndex).erase =
            match
              (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?,
              (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]?
            with
            | some minExcess, some prefixPos =>
                some (minExcess, prefixPos)
            | _, _ => none := by
  constructor
  · exact table.payload_length
  intro rangeIndex
  exact ⟨table.rangeWitnessCosted_cost_le_two rangeIndex,
    table.rangeWitnessCosted_erase rangeIndex⟩

end PayloadLiveBPPrefixRangeArgMinWitnessTable

def concreteBPPrefixRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (2 * (ranges.length * fieldWidth)) ranges where
  minTable :=
    FixedWidthNatTable.ofEntries
      (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
      (bpPrefixRangeMinExcessEntries_mem_bound hwidth)
  argTable :=
    FixedWidthNatTable.ofEntries
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
      (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)
  payload_length_eq := by
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
          (bpPrefixRangeMinExcessEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpPrefixRangeMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
          (bpPrefixRangeMinExcessEntries_mem_bound hwidth)).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
          (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpPrefixRangeArgMinPrefixPosEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
          (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload_length
    omega

def bpCandidateBetter (left right : Nat × Nat) : Nat × Nat :=
  if right.1 < left.1 then right else left

def bpCandidateMerge? :
    Option (Nat × Nat) -> Option (Nat × Nat) -> Option (Nat × Nat)
  | none, candidate => candidate
  | candidate, none => candidate
  | some left, some right => some (bpCandidateBetter left right)

def bpCandidateMerge3?
    (left middle right : Option (Nat × Nat)) : Option (Nat × Nat) :=
  bpCandidateMerge? (bpCandidateMerge? left middle) right

def bpCandidateClose? (candidate? : Option (Nat × Nat)) : Option Nat :=
  candidate?.map fun candidate => candidate.2 - 1

theorem bpCandidateBetter_eq_left_of_fst_le
    {left right : Nat × Nat}
    (hle : left.1 <= right.1) :
    bpCandidateBetter left right = left := by
  unfold bpCandidateBetter
  have hnot : ¬ right.1 < left.1 := by
    omega
  simp [hnot]

theorem bpCandidateBetter_eq_right_of_fst_lt
    {left right : Nat × Nat}
    (hlt : right.1 < left.1) :
    bpCandidateBetter left right = right := by
  simp [bpCandidateBetter, hlt]

theorem bpCandidateMerge?_some_left_of_fst_le
    {left : Nat × Nat} {right? : Option (Nat × Nat)}
    (hright :
      forall {right : Nat × Nat}, right? = some right -> left.1 <= right.1) :
    bpCandidateMerge? (some left) right? = some left := by
  cases right? with
  | none =>
      simp [bpCandidateMerge?]
  | some right =>
      have hle : left.1 <= right.1 := hright rfl
      simp [bpCandidateMerge?, bpCandidateBetter_eq_left_of_fst_le hle]

theorem bpCandidateMerge?_some_right_of_fst_lt
    {left right : Nat × Nat}
    (hlt : right.1 < left.1) :
    bpCandidateMerge? (some left) (some right) = some right := by
  simp [bpCandidateMerge?, bpCandidateBetter_eq_right_of_fst_lt hlt]

theorem bpCandidateMerge3?_eq_some_left_of_fst_le
    {left : Nat × Nat}
    {middle? right? : Option (Nat × Nat)}
    (hmiddle :
      forall {middle : Nat × Nat},
        middle? = some middle -> left.1 <= middle.1)
    (hright :
      forall {right : Nat × Nat},
        right? = some right -> left.1 <= right.1) :
    bpCandidateMerge3? (some left) middle? right? = some left := by
  have hfirst :
      bpCandidateMerge? (some left) middle? = some left :=
    bpCandidateMerge?_some_left_of_fst_le hmiddle
  unfold bpCandidateMerge3?
  rw [hfirst]
  exact bpCandidateMerge?_some_left_of_fst_le hright

theorem bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
    {left middle : Nat × Nat}
    {right? : Option (Nat × Nat)}
    (hmiddleLeft : middle.1 < left.1)
    (hright :
      forall {right : Nat × Nat},
        right? = some right -> middle.1 <= right.1) :
    bpCandidateMerge3? (some left) (some middle) right? =
      some middle := by
  have hfirst :
      bpCandidateMerge? (some left) (some middle) = some middle :=
    bpCandidateMerge?_some_right_of_fst_lt hmiddleLeft
  unfold bpCandidateMerge3?
  rw [hfirst]
  exact bpCandidateMerge?_some_left_of_fst_le hright

theorem bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
    {left right : Nat × Nat}
    {middle? : Option (Nat × Nat)}
    (hrightLeft : right.1 < left.1)
    (hrightMiddle :
      forall {middle : Nat × Nat},
        middle? = some middle -> right.1 < middle.1) :
    bpCandidateMerge3? (some left) middle? (some right) =
      some right := by
  cases middle? with
  | none =>
      unfold bpCandidateMerge3?
      simp [bpCandidateMerge?,
        bpCandidateBetter_eq_right_of_fst_lt hrightLeft]
  | some middle =>
      have hmiddle : right.1 < middle.1 := hrightMiddle rfl
      have hfirst :
          bpCandidateMerge? (some left) (some middle) =
            some (bpCandidateBetter left middle) := by
        simp [bpCandidateMerge?]
      unfold bpCandidateMerge3?
      rw [hfirst]
      by_cases hmiddleLeft : middle.1 < left.1
      · have hbest :
            bpCandidateBetter left middle = middle :=
          bpCandidateBetter_eq_right_of_fst_lt hmiddleLeft
        rw [hbest]
        exact bpCandidateMerge?_some_right_of_fst_lt hmiddle
      · have hle : left.1 <= middle.1 := Nat.le_of_not_gt hmiddleLeft
        have hbest :
            bpCandidateBetter left middle = left :=
          bpCandidateBetter_eq_left_of_fst_le hle
        rw [hbest]
        exact bpCandidateMerge?_some_right_of_fst_lt hrightLeft

theorem bpCandidateMerge?_argmin_pair
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    bpCandidateMerge?
        (some (bpExcessAt shape left, left))
        (some (bpExcessAt shape right, right)) =
      some
        (bpExcessAt shape (bpBetterArgMinPrefixPos shape left right),
          bpBetterArgMinPrefixPos shape left right) := by
  unfold bpCandidateMerge? bpCandidateBetter bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt]
  · simp [hlt]

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def rangeScanFromCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    Nat -> Nat -> Option (Nat × Nat) -> Costed (Option (Nat × Nat))
  | _block, 0, best? => Costed.pure best?
  | block, steps + 1, best? =>
      Costed.bind (table.minCandidateCosted block) fun candidate? =>
        table.rangeScanFromCosted (block + 1) steps
          (bpCandidateMerge? best? candidate?)

def rangeScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  match count with
  | 0 => Costed.pure none
  | steps + 1 =>
      Costed.bind (table.minCandidateCosted startBlock) fun first? =>
        table.rangeScanFromCosted (startBlock + 1) steps first?

theorem rangeScanFromCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block steps : Nat) (best? : Option (Nat × Nat)) :
    (table.rangeScanFromCosted block steps best?).cost <= 4 * steps := by
  induction steps generalizing block best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure]
  | succ steps ih =>
      have hhead := table.minCandidateCosted_cost_le_four block
      have htail :=
        ih (block + 1)
          (bpCandidateMerge? best? (table.minCandidateCosted block).value)
      simp [rangeScanFromCosted, Costed.bind]
      omega

theorem rangeScanFromCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block steps : Nat) (best? : Option (Nat × Nat)) :
    (table.rangeScanFromCosted block steps best?).cost = 4 * steps := by
  induction steps generalizing block best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure]
  | succ steps ih =>
      have htail :=
        ih (block + 1)
          (bpCandidateMerge? best? (table.minCandidateCosted block).value)
      simp [rangeScanFromCosted, Costed.bind,
        table.minCandidateCosted_cost_eq_four block, htail,
        Nat.succ_mul]
      omega

theorem rangeScanCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeScanCosted startBlock count).cost <= 4 * count := by
  unfold rangeScanCosted
  cases count with
  | zero =>
      simp [Costed.pure]
  | succ steps =>
      have hhead := table.minCandidateCosted_cost_le_four startBlock
      have htail :=
        table.rangeScanFromCosted_cost_le (startBlock + 1) steps
          (table.minCandidateCosted startBlock).value
      simp [Costed.bind]
      omega

theorem rangeScanCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeScanCosted startBlock count).cost = 4 * count := by
  unfold rangeScanCosted
  cases count with
  | zero =>
      simp [Costed.pure]
  | succ steps =>
      have htail :=
        table.rangeScanFromCosted_cost_eq (startBlock + 1) steps
          (table.minCandidateCosted startBlock).value
      simp [Costed.bind, table.minCandidateCosted_cost_eq_four startBlock,
        htail, Nat.succ_mul]
      omega

theorem rangeScanCosted_no_uniform_constant
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock : Nat) :
    ¬ exists queryCost : Nat,
      forall count : Nat,
        (table.rangeScanCosted startBlock count).cost <= queryCost := by
  intro hconstant
  rcases hconstant with ⟨queryCost, hqueryCost⟩
  have hbad := hqueryCost (queryCost + 1)
  rw [table.rangeScanCosted_cost_eq] at hbad
  have hgt : queryCost < 4 * (queryCost + 1) := by
    omega
  omega

def interiorScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  table.rangeScanCosted (blockOfClose blockSize leftClose + 1)
    (blockOfClose blockSize rightClose -
      blockOfClose blockSize leftClose - 1)

theorem interiorScanCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (leftClose rightClose : Nat) :
    (table.interiorScanCosted leftClose rightClose).cost =
      4 * (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1) := by
  simp [interiorScanCosted, table.rangeScanCosted_cost_eq]

theorem interiorScanCosted_no_uniform_constant
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblockSize : 0 < blockSize) :
    ¬ exists queryCost : Nat,
      forall leftClose rightClose : Nat,
        (table.interiorScanCosted leftClose rightClose).cost <=
          queryCost := by
  intro hconstant
  rcases hconstant with ⟨queryCost, hqueryCost⟩
  let rightClose := (queryCost + 2) * blockSize
  have hleftBlock : blockOfClose blockSize 0 = 0 := by
    simp [blockOfClose]
  have hrightBlock :
      blockOfClose blockSize rightClose = queryCost + 2 := by
    unfold rightClose blockOfClose
    simpa [Nat.mul_comm] using
      Nat.mul_div_right (queryCost + 2) hblockSize
  have hbad := hqueryCost 0 rightClose
  rw [table.interiorScanCosted_cost_eq] at hbad
  simp [hleftBlock, hrightBlock] at hbad
  have hgt : queryCost < 4 * (queryCost + 1) := by
    omega
  omega

theorem rangeScanFromCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps best : Nat}
    {best? : Option (Nat × Nat)}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hblockRange :
      forall {offset : Nat}, offset < steps ->
        block + offset < blockCount)
    (hsuperRange :
      forall {offset : Nat}, offset < steps ->
        (block + offset) / blocksPerSuper < superCount)
    (hbest :
      best? = some (bpExcessAt shape best, best)) :
    (table.rangeScanFromCosted block steps best?).erase =
      some
        (bpExcessAt shape
          (bpRangeArgMinPrefixPosFrom shape blockSize block steps best),
          bpRangeArgMinPrefixPosFrom shape blockSize block steps best) := by
  induction steps generalizing block best best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure, hbest,
        bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      have hblock : block < blockCount :=
        hblockRange (offset := 0) (by omega)
      have hsuper : block / blocksPerSuper < superCount :=
        hsuperRange (offset := 0) (by omega)
      have hread :=
        table.minCandidateCosted_erase_arg_excess_of_bounds
          hblocks hblock hcover hsuper
      have hvalue :
          (table.minCandidateCosted block).value =
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block),
                bpBlockArgMinPrefixPos shape blockSize block) := by
        simpa [Costed.erase] using hread
      have hmerge :
          bpCandidateMerge? best?
              (table.minCandidateCosted block).value =
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
        rw [hbest, hvalue]
        exact bpCandidateMerge?_argmin_pair shape best
          (bpBlockArgMinPrefixPos shape blockSize block)
      have hmergeValue :
          bpCandidateMerge? best?
              (some
                (bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize block),
                  bpBlockArgMinPrefixPos shape blockSize block)) =
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
        simpa [hvalue] using hmerge
      have htail :=
        ih (block := block + 1)
          (best :=
            bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block))
          (best? :=
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)))
          (by
            intro offset hoffset
            have h :=
              hblockRange (offset := offset + 1) (by omega)
            omega)
          (by
            intro offset hoffset
            have h :=
              hsuperRange (offset := offset + 1) (by omega)
            have hpos :
                block + 1 + offset = block + (offset + 1) := by
              omega
            simpa [hpos] using h)
          rfl
      simpa [rangeScanFromCosted, Costed.bind, Costed.erase, hvalue,
        hmergeValue,
        bpRangeArgMinPrefixPosFrom] using htail

theorem rangeScanCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hcount : 0 < count)
    (hblockRange :
      forall {offset : Nat}, offset < count ->
        startBlock + offset < blockCount)
    (hsuperRange :
      forall {offset : Nat}, offset < count ->
        (startBlock + offset) / blocksPerSuper < superCount) :
    (table.rangeScanCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hblock : startBlock < blockCount :=
        hblockRange (offset := 0) (by omega)
      have hsuper : startBlock / blocksPerSuper < superCount :=
        hsuperRange (offset := 0) (by omega)
      have hread :=
        table.minCandidateCosted_erase_arg_excess_of_bounds
          hblocks hblock hcover hsuper
      have hvalue :
          (table.minCandidateCosted startBlock).value =
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock),
                bpBlockArgMinPrefixPos shape blockSize startBlock) := by
        simpa [Costed.erase] using hread
      have htail :=
        table.rangeScanFromCosted_erase_exact
          (block := startBlock + 1)
          (steps := steps)
          (best := bpBlockArgMinPrefixPos shape blockSize startBlock)
          (best? :=
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock),
                bpBlockArgMinPrefixPos shape blockSize startBlock))
          hblocks hcover
          (by
            intro offset hoffset
            have h :=
              hblockRange (offset := offset + 1) (by omega)
            omega)
          (by
            intro offset hoffset
            have h :=
              hsuperRange (offset := offset + 1) (by omega)
            have hpos :
                startBlock + 1 + offset =
                  startBlock + (offset + 1) := by
              omega
            simpa [hpos] using h)
          rfl
      simpa [rangeScanCosted, Costed.bind, hvalue,
        bpRangeArgMinPrefixPos, bpRangeMinExcess] using htail

end PayloadLiveBPRelativeMinMaxArgSummaryTable

/--
Interior full-block range-minimum directory for the relative-rmM close layer.

This interface is deliberately narrow: a concrete implementation has to expose
one charged `rangeMinCosted` path whose erasure is the leftmost block-minimum
candidate over the requested complete-block range.  The compact C2 target must
instantiate this with a constant `queryCost`; the scan instance below is kept
only as a diagnostic replacement target.
-/
structure PayloadLiveBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount overhead queryCost : Nat) where
  payload : List Bool
  payload_length_eq : payload.length = overhead
  rangeMinCosted : Nat -> Nat -> Costed (Option (Nat × Nat))
  rangeMin_cost_le :
    forall startBlock count,
      (rangeMinCosted startBlock count).cost <= queryCost
  rangeMin_exact :
    forall {startBlock count : Nat},
      0 < count ->
        startBlock + count <= blockCount ->
          (rangeMinCosted startBlock count).erase =
            some
              (bpRangeMinExcess shape blockSize startBlock count,
                bpRangeArgMinPrefixPos shape blockSize startBlock count)

namespace PayloadLiveBPRelativeRmmInteriorDirectory

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead queryCost : Nat}
    (directory :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        overhead queryCost) :
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= queryCost) /\
      forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  exact ⟨directory.payload_length_eq, directory.rangeMin_cost_le,
    directory.rangeMin_exact⟩

end PayloadLiveBPRelativeRmmInteriorDirectory

/--
Proof-only range-min oracle used to document a target-shape obstruction.

This is intentionally *not* a compact C2 construction: it answers by directly
calling the semantic reference functions and charges a constant without reading
payload bits.  The theorem below records why `concreteBPRelativeRmmInteriorDirectory_profile`
cannot be closed merely by exposing the abstract `PayloadLiveBPRelativeRmmInteriorDirectory`
record and invoking its generic `.profile`.
-/
def proofOnlyBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      0 1 where
  payload := []
  payload_length_eq := rfl
  rangeMinCosted := fun startBlock count =>
    { value :=
        if 0 < count ∧ startBlock + count <= blockCount then
          some
            (bpRangeMinExcess shape blockSize startBlock count,
              bpRangeArgMinPrefixPos shape blockSize startBlock count)
        else
          none
      cost := 1 }
  rangeMin_cost_le := by
    intro startBlock count
    simp
  rangeMin_exact := by
    intro startBlock count hcount hbound
    have hcond : 0 < count ∧ startBlock + count <= blockCount :=
      ⟨hcount, hbound⟩
    simp [hcond]

theorem payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    let directory :=
      proofOnlyBPRelativeRmmInteriorDirectory shape blockSize blockCount
    directory.payload.length = 0 /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= 1) /\
      forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  exact
    (proofOnlyBPRelativeRmmInteriorDirectory
      shape blockSize blockCount).profile

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def boundedRangeScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  if startBlock + count <= blockCount then
    table.rangeScanCosted startBlock count
  else
    Costed.pure none

theorem boundedRangeScanCosted_cost_le_blockCount
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.boundedRangeScanCosted startBlock count).cost <=
      4 * blockCount := by
  unfold boundedRangeScanCosted
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound]
    have hcost := table.rangeScanCosted_cost_le startBlock count
    have hcount : count <= blockCount := by omega
    have hmul : 4 * count <= 4 * blockCount :=
      Nat.mul_le_mul_left 4 hcount
    exact Nat.le_trans hcost hmul
  · simp [hbound, Costed.pure]

theorem div_lt_succ_div_of_lt
    {block blocksPerSuper blockCount : Nat}
    (hblock : block < blockCount) :
    block / blocksPerSuper < blockCount / blocksPerSuper + 1 := by
  have hle : block / blocksPerSuper <= blockCount / blocksPerSuper := by
    exact Nat.div_le_div_right (Nat.le_of_lt hblock)
  omega

theorem boundedRangeScanCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount)
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount) :
    (table.boundedRangeScanCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  unfold boundedRangeScanCosted
  simp [hbound]
  exact
    table.rangeScanCosted_erase_exact hblocks hcover hcount
      (by
        intro offset hoffset
        omega)
      (by
        intro offset hoffset
        exact hsuperCount (by omega))

def scanInteriorDirectory
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      overhead (4 * blockCount) where
  payload := table.payload
  payload_length_eq := table.payload_length
  rangeMinCosted := table.boundedRangeScanCosted
  rangeMin_cost_le := table.boundedRangeScanCosted_cost_le_blockCount
  rangeMin_exact := by
    intro startBlock count hcount hbound
    exact table.boundedRangeScanCosted_erase_exact hblocks hcover
      hsuperCount hcount hbound

theorem scanInteriorDirectory_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    let directory :=
      table.scanInteriorDirectory hblocks hcover hsuperCount
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          4 * blockCount) /\
      forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  exact
    (table.scanInteriorDirectory hblocks hcover hsuperCount).profile

end PayloadLiveBPRelativeMinMaxArgSummaryTable

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_interior_scan_not_constant
    (shape : Cartesian.CartesianShape)
    (hblockSize : 0 < canonicalBPRelativeSummaryBlockSize shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    ¬ exists queryCost : Nat,
      forall leftClose rightClose : Nat,
        (table.interiorScanCosted leftClose rightClose).cost <=
          queryCost := by
  exact
    PayloadLiveBPRelativeMinMaxArgSummaryTable.interiorScanCosted_no_uniform_constant
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      hblockSize

def endpointFringeSlot (blockSize close : Nat) : Nat :=
  let block := blockOfClose blockSize close
  block * blockSize + (close - blockStartOf blockSize block)

def endpointLeftFringeRangeOfSlot
    (blockSize slot : Nat) : Nat × Nat :=
  let block := slot / blockSize
  let offset := slot % blockSize
  (blockStartOf blockSize block + offset + 1, blockSize - offset)

def endpointRightFringeRangeOfSlot
    (blockSize slot : Nat) : Nat × Nat :=
  let block := slot / blockSize
  let offset := slot % blockSize
  (blockStartOf blockSize block, offset + 2)

def endpointLeftFringeRanges
    (blockSize blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockSize)).map
    (endpointLeftFringeRangeOfSlot blockSize)

theorem endpointLeftFringeRanges_length
    (blockSize blockCount : Nat) :
    (endpointLeftFringeRanges blockSize blockCount).length =
      blockCount * blockSize := by
  simp [endpointLeftFringeRanges]

theorem endpointFringeSlot_lt
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    endpointFringeSlot blockSize close < blockCount * blockSize := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  unfold endpointFringeSlot
  have hltStep :
      blockOfClose blockSize close * blockSize +
          (close - blockStartOf blockSize (blockOfClose blockSize close)) <
        blockOfClose blockSize close * blockSize + blockSize :=
    Nat.add_lt_add_left hoffset
      (blockOfClose blockSize close * blockSize)
  have hstepEq :
      blockOfClose blockSize close * blockSize + blockSize =
        (blockOfClose blockSize close + 1) * blockSize := by
    simpa using
      (Nat.succ_mul (blockOfClose blockSize close) blockSize).symm
  have hmul :
      (blockOfClose blockSize close + 1) * blockSize <=
        blockCount * blockSize :=
    Nat.mul_le_mul_right blockSize (Nat.succ_le_of_lt hblock)
  exact Nat.lt_of_lt_of_le (by simpa [hstepEq] using hltStep) hmul

theorem endpointFringeSlot_div
    {blockSize close : Nat}
    (hblockSize : 0 < blockSize) :
    endpointFringeSlot blockSize close / blockSize =
      blockOfClose blockSize close := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  simpa [endpointFringeSlot, densePairSlot] using
    (densePairSlot_div
      (blockSize := blockSize)
      (leftLocal := blockOfClose blockSize close)
      (rightLocal :=
        close - blockStartOf blockSize (blockOfClose blockSize close))
      hoffset)

theorem endpointFringeSlot_mod
    {blockSize close : Nat}
    (hblockSize : 0 < blockSize) :
    endpointFringeSlot blockSize close % blockSize =
      close - blockStartOf blockSize (blockOfClose blockSize close) := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  simpa [endpointFringeSlot, densePairSlot] using
    (densePairSlot_mod
      (blockSize := blockSize)
      (leftLocal := blockOfClose blockSize close)
      (rightLocal :=
        close - blockStartOf blockSize (blockOfClose blockSize close))
      hoffset)

def endpointRightFringeRanges
    (blockSize blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockSize)).map
    (endpointRightFringeRangeOfSlot blockSize)

theorem endpointRightFringeRanges_length
    (blockSize blockCount : Nat) :
    (endpointRightFringeRanges blockSize blockCount).length =
      blockCount * blockSize := by
  simp [endpointRightFringeRanges]

theorem endpointLeftFringeRanges_get?_of_close_bounds
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (endpointLeftFringeRanges blockSize blockCount)[
        endpointFringeSlot blockSize close]? =
      some
        (close + 1,
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close) := by
  have hslot :
      endpointFringeSlot blockSize close < blockCount * blockSize :=
    endpointFringeSlot_lt hblockSize hblock
  have hslotGet :
      (List.range (blockCount * blockSize))[
          endpointFringeSlot blockSize close]? =
        some (endpointFringeSlot blockSize close) := by
    exact List.getElem?_range hslot
  have hdiv := endpointFringeSlot_div (blockSize := blockSize)
    (close := close) hblockSize
  have hmod := endpointFringeSlot_mod (blockSize := blockSize)
    (close := close) hblockSize
  have hstart :
      blockStartOf blockSize (blockOfClose blockSize close) <= close :=
    blockStartOf_blockOfClose_le
  have hend :
      close <
        blockStartOf blockSize (blockOfClose blockSize close) +
          blockSize :=
    close_lt_blockStartOf_blockOfClose_add hblockSize
  have hfirst :
      blockStartOf blockSize (blockOfClose blockSize close) +
          (close - blockStartOf blockSize (blockOfClose blockSize close)) +
          1 =
        close + 1 := by
    omega
  have hcount :
      blockSize -
          (close - blockStartOf blockSize (blockOfClose blockSize close)) =
        blockStartOf blockSize (blockOfClose blockSize close) +
          blockSize - close := by
    omega
  simp [endpointLeftFringeRanges, List.getElem?_map, hslotGet,
    endpointLeftFringeRangeOfSlot, hdiv, hmod, hfirst, hcount]

theorem endpointRightFringeRanges_get?_of_close_bounds
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (endpointRightFringeRanges blockSize blockCount)[
        endpointFringeSlot blockSize close]? =
      some
        (blockStartOf blockSize (blockOfClose blockSize close),
          close - blockStartOf blockSize (blockOfClose blockSize close) +
            2) := by
  have hslot :
      endpointFringeSlot blockSize close < blockCount * blockSize :=
    endpointFringeSlot_lt hblockSize hblock
  have hslotGet :
      (List.range (blockCount * blockSize))[
          endpointFringeSlot blockSize close]? =
        some (endpointFringeSlot blockSize close) := by
    exact List.getElem?_range hslot
  have hdiv := endpointFringeSlot_div (blockSize := blockSize)
    (close := close) hblockSize
  have hmod := endpointFringeSlot_mod (blockSize := blockSize)
    (close := close) hblockSize
  simp [endpointRightFringeRanges, List.getElem?_map, hslotGet,
    endpointRightFringeRangeOfSlot, hdiv, hmod]

theorem endpointLeftFringeMinExcessEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointLeftFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointLeftFringeArgMinEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointLeftFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointRightFringeMinExcessEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close - blockStartOf blockSize (blockOfClose blockSize close) +
            2)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointRightFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointRightFringeArgMinEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close - blockStartOf blockSize (blockOfClose blockSize close) +
            2)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointRightFringeRanges_get?_of_close_bounds
        hblockSize hblock)

def interiorBlockPairRangeOfSlot
    (blockCount slot : Nat) : Nat × Nat :=
  let leftBlock := slot / blockCount
  let rightBlock := slot % blockCount
  if leftBlock + 1 < rightBlock then
    (leftBlock + 1, rightBlock - leftBlock - 1)
  else
    (leftBlock + 1, 0)

def interiorBlockPairRanges (blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockCount)).map
    (interiorBlockPairRangeOfSlot blockCount)

theorem interiorBlockPairRanges_length (blockCount : Nat) :
    (interiorBlockPairRanges blockCount).length =
      blockCount * blockCount := by
  simp [interiorBlockPairRanges]

theorem interiorBlockPairRanges_get?_of_gap_bounds
    {blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (interiorBlockPairRanges blockCount)[
        blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some (leftBlock + 1, rightBlock - leftBlock - 1) := by
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
  simp [interiorBlockPairRanges, List.getElem?_map, hslotGet,
    interiorBlockPairRangeOfSlot, hdiv, hmod, hgap]

theorem interiorBlockPairRangeMinExcessEntries_get?_of_gap_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (bpRangeMinExcessEntries shape blockSize
        (interiorBlockPairRanges blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some
        (bpRangeMinExcess shape blockSize
          (leftBlock + 1) (rightBlock - leftBlock - 1)) := by
  exact
    bpRangeMinExcessEntries_get?_of_ranges_get?
      (interiorBlockPairRanges_get?_of_gap_bounds
        hleft hright hgap)

theorem interiorBlockPairRangeArgMinEntries_get?_of_gap_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (bpRangeArgMinPrefixPosEntries shape blockSize
        (interiorBlockPairRanges blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some
        (bpRangeArgMinPrefixPos shape blockSize
          (leftBlock + 1) (rightBlock - leftBlock - 1)) := by
  exact
    bpRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (interiorBlockPairRanges_get?_of_gap_bounds
        hleft hright hgap)

structure PayloadLiveBPEndpointFringeRangeMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat) where
  leftFringe :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth leftOverhead
      (endpointLeftFringeRanges blockSize blockCount)
  interior :
    PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
      interiorOverhead (interiorBlockPairRanges blockCount)
  rightFringe :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth rightOverhead
      (endpointRightFringeRanges blockSize blockCount)

namespace PayloadLiveBPEndpointFringeRangeMacro

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    List Bool :=
  component.leftFringe.payload ++ component.interior.payload ++
    component.rightFringe.payload

def interiorIndex
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (_component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Nat :=
  blockPairRangeSlot blockCount
    (blockOfClose blockSize leftClose)
    (blockOfClose blockSize rightClose)

def interiorWitnessCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  if blockOfClose blockSize leftClose + 1 <
      blockOfClose blockSize rightClose then
    component.interior.rangeWitnessCosted
      (component.interiorIndex leftClose rightClose)
  else
    Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (component.leftFringe.rangeWitnessCosted
      (endpointFringeSlot blockSize leftClose)) fun left? =>
    Costed.bind
      (component.interiorWitnessCosted leftClose rightClose) fun middle? =>
      Costed.map
        (fun right? =>
          bpCandidateClose? (bpCandidateMerge3? left? middle? right?))
        (component.rightFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize rightClose))

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
      leftOverhead + interiorOverhead + rightOverhead := by
  simp [payload, component.leftFringe.payload_length,
    component.interior.payload_length, component.rightFringe.payload_length]
  omega

theorem interiorWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.interiorWitnessCosted leftClose rightClose).cost <= 2 := by
  unfold interiorWitnessCosted
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [hblocks]
    exact component.interior.rangeWitnessCosted_cost_le_two
      (component.interiorIndex leftClose rightClose)
  · simp [hblocks, Costed.pure]

theorem lcaCloseCosted_cost_le_six
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <= 6 := by
  unfold lcaCloseCosted
  have hleft :=
    component.leftFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize leftClose)
  have hmiddle :=
    component.interiorWitnessCosted_cost_le_two leftClose rightClose
  have hright :=
    component.rightFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize rightClose)
  simp [Costed.bind, Costed.map]
  omega

theorem lcaCloseCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      bpCandidateClose?
        (bpCandidateMerge3?
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            match
              (bpRangeMinExcessEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]? with
            | some minExcess, some prefixPos => some (minExcess, prefixPos)
            | _, _ => none
          else
            none)
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)) := by
  have hleft :
      (component.leftFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize leftClose)).value =
        match
          (bpPrefixRangeMinExcessEntries shape
            (endpointLeftFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize leftClose]?,
          (bpPrefixRangeArgMinPrefixPosEntries shape
            (endpointLeftFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize leftClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.leftFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize leftClose)
  have hright :
      (component.rightFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize rightClose)).value =
        match
          (bpPrefixRangeMinExcessEntries shape
            (endpointRightFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize rightClose]?,
          (bpPrefixRangeArgMinPrefixPosEntries shape
            (endpointRightFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize rightClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.rightFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize rightClose)
  have hmiddle :
      (component.interior.rangeWitnessCosted
          (component.interiorIndex leftClose rightClose)).value =
        match
          (bpRangeMinExcessEntries shape blockSize
            (interiorBlockPairRanges blockCount))[
              component.interiorIndex leftClose rightClose]?,
          (bpRangeArgMinPrefixPosEntries shape blockSize
            (interiorBlockPairRanges blockCount))[
              component.interiorIndex leftClose rightClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.interior.rangeWitnessCosted_erase
        (component.interiorIndex leftClose rightClose)
  unfold lcaCloseCosted interiorWitnessCosted
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [Costed.bind, Costed.map, Costed.erase,
      hleft, hmiddle, hright, hblocks]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      hleft, hright, hblocks]

theorem lcaCloseCosted_exact_of_merged_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hmerge :
      bpCandidateMerge3?
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            match
              (bpRangeMinExcessEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]? with
            | some minExcess, some prefixPos => some (minExcess, prefixPos)
            | _, _ => none
          else
            none)
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none) =
        some (bpExcessAt shape (answerClose + 1), answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  simp [component.lcaCloseCosted_erase, hmerge, bpCandidateClose?]

theorem lcaCloseCosted_exact_of_decoded_merged_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hmerge :
      bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose)))
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2))) =
        some (bpExcessAt shape (answerClose + 1), answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
  have hleftMin :
      (bpPrefixRangeMinExcessEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize leftClose]? =
        some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)) :=
    endpointLeftFringeMinExcessEntries_get?_of_close_bounds
      hblockSize hleftBlock
  have hleftArg :
      (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize leftClose]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)) :=
    endpointLeftFringeArgMinEntries_get?_of_close_bounds
      hblockSize hleftBlock
  have hrightMin :
      (bpPrefixRangeMinExcessEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize rightClose]? =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2)) :=
    endpointRightFringeMinExcessEntries_get?_of_close_bounds
      hblockSize hrightBlock
  have hrightArg :
      (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize rightClose]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2)) :=
    endpointRightFringeArgMinEntries_get?_of_close_bounds
      hblockSize hrightBlock
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · have hmiddleMin :
        (bpRangeMinExcessEntries shape blockSize
          (interiorBlockPairRanges blockCount))[
            component.interiorIndex leftClose rightClose]? =
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) := by
      simpa [interiorIndex] using
        (interiorBlockPairRangeMinExcessEntries_get?_of_gap_bounds
          (shape := shape) (blockSize := blockSize)
          (blockCount := blockCount)
          (leftBlock := blockOfClose blockSize leftClose)
          (rightBlock := blockOfClose blockSize rightClose)
          hleftBlock hrightBlock hblocks)
    have hmiddleArg :
        (bpRangeArgMinPrefixPosEntries shape blockSize
          (interiorBlockPairRanges blockCount))[
            component.interiorIndex leftClose rightClose]? =
          some
            (bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) := by
      simpa [interiorIndex] using
        (interiorBlockPairRangeArgMinEntries_get?_of_gap_bounds
          (shape := shape) (blockSize := blockSize)
          (blockCount := blockCount)
          (leftBlock := blockOfClose blockSize leftClose)
          (rightBlock := blockOfClose blockSize rightClose)
          hleftBlock hrightBlock hblocks)
    simpa [hleftMin, hleftArg, hmiddleMin, hmiddleArg,
      hrightMin, hrightArg, hblocks] using hmerge
  · simpa [hleftMin, hleftArg, hrightMin, hrightArg, hblocks]
      using hmerge

theorem lcaCloseCosted_exact_of_left_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hanswerLeft :
      leftClose + 1 <= answerClose + 1 /\
        answerClose + 1 <
          leftClose + 1 +
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        shape.bpCode.length + 1)
    (hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        shape.bpCode.length + 1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
  have hleftPair :
      (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
        bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerLeft hleftBound
        (by
          intro pos hlo hhi
          exact hmin hlo (hleftInside hlo hhi))
        (by
          intro pos hlo hhi
          exact hleftmost hlo hhi)
  have hrightCount :
      0 <
        rightClose -
            blockStartOf blockSize
              (blockOfClose blockSize rightClose) +
          2 := by
    omega
  have hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) := by
    exact
      bpPrefixRangeMinExcess_ge_of_all_prefix_ge
        hrightCount hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hmin hinside.1 hinside.2)
  have hmiddleLe :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) <= middle.1 := by
    intro middle hmiddle
    by_cases hblocks :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
    · simp [hblocks] at hmiddle
      subst middle
      have hcount :
          0 <
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1 := by
        omega
      exact
        bpRangeMinExcess_ge_of_all_prefix_ge
          (shape := shape) (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower := bpExcessAt shape (answerClose + 1))
          hcount
          (by
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            simpa [hend] using hmiddleBound hblocks)
          (by
            intro pos hlo hhi
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            have hinside :=
              hmiddleInside (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hmin hinside.1 hinside.2)
    · simp [hblocks] at hmiddle
  have hmerge :
      bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose)))
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2))) =
        some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
    simpa [hleftPair] using
      bpCandidateMerge3?_eq_some_left_of_fst_le
        (left := (bpExcessAt shape (answerClose + 1), answerClose + 1))
        (middle? :=
          if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none)
        (right? :=
          some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2)))
        (by
          intro middle hmiddle
          exact hmiddleLe middle hmiddle)
        (by
          intro right hright
          cases hright
          exact hrightLe)
  exact hmerge

theorem lcaCloseCosted_exact_of_decoded_right_fringe_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hrightPair :
      (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hleftGt :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) < middle.1) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
  simpa [hrightPair] using
    bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (right := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      hleftGt
      (by
        intro middle hmiddle
        exact hmiddleGt middle hmiddle)

theorem lcaCloseCosted_exact_of_decoded_middle_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose)
    (hmiddlePair :
      (bpRangeMinExcess shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1),
        bpRangeArgMinPrefixPos shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hmiddleLeft :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
  simpa [hblocks, hmiddlePair] using
    bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (middle := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      hmiddleLeft
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem lcaCloseCosted_exact_of_spanning_root_left_fringe
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hanswerLeft :
      leftClose + 1 <= answerClose + 1 /\
        answerClose + 1 <
          leftClose + 1 +
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
            1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_left_fringe_leftmost
      leftClose rightClose hblockSize hleftBlock hrightBlock
      hanswerLeft hleftBound hleftInside
      hrightBound hrightInside hmiddleBound hmiddleInside
      hsemantic.1 hsemantic.2

theorem lcaCloseCosted_exact_of_spanning_root_right_fringe
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hanswerRight :
      blockStartOf blockSize (blockOfClose blockSize rightClose) <=
          answerClose + 1 /\
        answerClose + 1 <
          blockStartOf blockSize (blockOfClose blockSize rightClose) +
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hleftBefore :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < answerClose + 1)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
            1)
    (hmiddleBefore :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < answerClose + 1) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  have hrightPair :
      (bpPrefixRangeMinExcess
          (Cartesian.CartesianShape.node leftShape rightShape)
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos
          (Cartesian.CartesianShape.node leftShape rightShape)
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt
            (Cartesian.CartesianShape.node leftShape rightShape)
            (answerClose + 1),
          answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerRight hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hsemantic.1 hinside.1 hinside.2)
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo (by omega)
          exact hsemantic.2 hinside.1 hhi)
  have hleftCount :
      0 <
        blockStartOf blockSize
            (blockOfClose blockSize leftClose) +
          blockSize - leftClose := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    omega
  have hleftGt :
      bpExcessAt
          (Cartesian.CartesianShape.node leftShape rightShape)
          (answerClose + 1) <
        bpPrefixRangeMinExcess
          (Cartesian.CartesianShape.node leftShape rightShape)
          (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) := by
    exact
      bpPrefixRangeMinExcess_gt_of_all_prefix_gt
        hleftCount hleftBound
        (by
          intro pos hlo hhi
          exact hsemantic.2 hlo (hleftBefore hlo hhi))
  have hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess
                (Cartesian.CartesianShape.node leftShape rightShape)
                blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos
                  (Cartesian.CartesianShape.node leftShape rightShape)
                  blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1) < middle.1 := by
    intro middle hmiddle
    by_cases hblocks :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
    · simp [hblocks] at hmiddle
      subst middle
      have hcount :
          0 <
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1 := by
        omega
      exact
        bpRangeMinExcess_gt_of_all_prefix_gt
          (shape := Cartesian.CartesianShape.node leftShape rightShape)
          (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower :=
            bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1))
          hcount
          (by
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            simpa [hend] using hmiddleBound hblocks)
          (by
            intro pos hlo hhi
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            have hbefore :=
              hmiddleBefore (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hsemantic.2 hbefore.1 hbefore.2)
    · simp [hblocks] at hmiddle
  exact
    component.lcaCloseCosted_exact_of_decoded_right_fringe_candidate
      leftClose rightClose hblockSize hleftBlock hrightBlock
      hrightPair hleftGt hmiddleGt

theorem lcaCloseCosted_exact_of_query_semantics_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  let answerPrefix := answerClose + 1
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hanswerCloseBound := bpCloseOfInorder?_bounds shape hanswer
  have hrightStartLe :
      blockStartOf blockSize rightBlock <= rightClose := by
    simpa [rightBlock] using
      (blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose))
  have hleftNextStart :
      leftClose < blockStartOf blockSize (leftBlock + 1) := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    simpa [leftBlock, blockStartOf_succ] using hend
  have hleftLimitEq :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) =
        blockStartOf blockSize (leftBlock + 1) + 1 := by
    have hstart :
        blockStartOf blockSize leftBlock <= leftClose := by
      simpa [leftBlock] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := leftClose))
    have hsucc :
        blockStartOf blockSize leftBlock + blockSize =
          blockStartOf blockSize (leftBlock + 1) :=
      blockStartOf_succ blockSize leftBlock
    omega
  have hrightLimitEq :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) =
        rightClose + 2 := by
    omega
  have hleftToRightStart :
      blockStartOf blockSize (leftBlock + 1) <=
        blockStartOf blockSize rightBlock := by
    exact blockStartOf_mono (blockSize := blockSize) (by
      simpa [leftBlock, rightBlock] using hcross)
  have hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) <=
        shape.bpCode.length + 1 := by
    rw [hleftLimitEq]
    omega
  have hrightBound :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) <=
        shape.bpCode.length + 1 := by
    rw [hrightLimitEq]
    omega
  have hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1 := by
    intro _hgap
    have hstart :
        blockStartOf blockSize
            (blockOfClose blockSize rightClose) <= rightClose :=
      blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose)
    omega
  have hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2 := by
    intro pos _hlo hhi
    have hhi' :
        pos < blockStartOf blockSize (leftBlock + 1) + 1 := by
      simpa [leftBlock, hleftLimitEq] using hhi
    have hleRight :
        blockStartOf blockSize (leftBlock + 1) + 1 <= rightClose + 1 := by
      omega
    omega
  have hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize rightClose) := by
      have hlt := hleftNextStart
      have hmono :
          blockStartOf blockSize (leftBlock + 1) <=
            blockStartOf blockSize rightBlock :=
        hleftToRightStart
      simpa [rightBlock] using (by omega : leftClose + 1 <=
        blockStartOf blockSize rightBlock)
    constructor
    · exact Nat.le_trans hleftLe hlo
    · simpa [rightBlock, hrightLimitEq] using hhi
  have hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos _hgap hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize leftClose + 1) := by
      simpa [leftBlock] using (by omega :
        leftClose + 1 <= blockStartOf blockSize (leftBlock + 1))
    constructor
    · exact Nat.le_trans hleftLe hlo
    · have hrightLeClose :
          blockStartOf blockSize
              (blockOfClose blockSize rightClose) <= rightClose :=
        blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose)
      omega
  have hanswerMem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hanswerUpper : answerPrefix < rightClose + 2 := by
    simpa [answerPrefix] using (by omega :
      answerClose + 1 < rightClose + 2)
  by_cases hanswerLeft :
      answerPrefix <
        leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)
  · exact
      component.lcaCloseCosted_exact_of_left_fringe_leftmost
        leftClose rightClose hblockSize hleftBlock hrightBlock
        (by
          constructor
          · simpa [answerPrefix] using hanswerMem.1
          · exact hanswerLeft)
        (by simpa [leftBlock] using hleftBound)
        hleftInside
        (by simpa [rightBlock] using hrightBound)
        hrightInside
        hmiddleBound
        hmiddleInside
        hmin hleftmost
  · by_cases hanswerRight :
        blockStartOf blockSize rightBlock + 1 <= answerPrefix
    · have hrightAnswer :
        blockStartOf blockSize (blockOfClose blockSize rightClose) <=
            answerClose + 1 /\
          answerClose + 1 <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        constructor
        · simpa [rightBlock, answerPrefix] using
            (Nat.le_trans (Nat.le_of_lt (by omega :
              blockStartOf blockSize rightBlock <
                blockStartOf blockSize rightBlock + 1)) hanswerRight)
        · simpa [rightBlock, hrightLimitEq, answerPrefix] using hanswerUpper
      have hleftBefore :
          forall {pos : Nat},
            leftClose + 1 <= pos ->
              pos <
                leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) ->
                pos < answerClose + 1 := by
        intro pos _hlo hhi
        have hlimit :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix := by
          omega
        simpa [answerPrefix] using (by omega : pos < answerPrefix)
      have hmiddleBefore :
          forall {pos : Nat},
            blockOfClose blockSize leftClose + 1 <
                blockOfClose blockSize rightClose ->
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose + 1) <= pos ->
                pos <
                  blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                    1 ->
                  leftClose + 1 <= pos /\ pos < answerClose + 1 := by
        intro pos hgap hlo hhi
        have hinside := hmiddleInside (pos := pos) hgap hlo hhi
        constructor
        · exact hinside.1
        · have hhi' : pos < blockStartOf blockSize rightBlock + 1 := by
            simpa [rightBlock] using hhi
          simpa [answerPrefix] using
            (by omega : pos < answerPrefix)
      exact
        component.lcaCloseCosted_exact_of_decoded_right_fringe_candidate
          leftClose rightClose hblockSize hleftBlock hrightBlock
          (by
            exact
              bpPrefixRangeWitness_eq_of_leftmost_min_excess
                hrightAnswer
                (by simpa [rightBlock] using hrightBound)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo hhi
                  exact hmin hinside.1 hinside.2)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo (by omega)
                  exact hleftmost hinside.1 hhi))
          (by
            have hleftCount :
                0 <
                  blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose := by
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := leftClose)
                  hblockSize
              omega
            exact
              bpPrefixRangeMinExcess_gt_of_all_prefix_gt
                hleftCount
                (by simpa [leftBlock] using hleftBound)
                (by
                  intro pos hlo hhi
                  exact hleftmost hlo (hleftBefore hlo hhi)))
          (by
            intro middle hmiddle
            by_cases hgap :
                blockOfClose blockSize leftClose + 1 <
                  blockOfClose blockSize rightClose
            · simp [hgap] at hmiddle
              subst middle
              have hcount :
                  0 <
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1 := by
                omega
              exact
                bpRangeMinExcess_gt_of_all_prefix_gt
                  (shape := shape) (blockSize := blockSize)
                  (startBlock :=
                    blockOfClose blockSize leftClose + 1)
                  (blockCount :=
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1)
                  (lower := bpExcessAt shape (answerClose + 1))
                  hcount
                  (by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    simpa [hend] using hmiddleBound hgap)
                  (by
                    intro pos hlo hhi
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    have hbefore :=
                      hmiddleBefore (pos := pos) hgap hlo
                        (by simpa [hend] using hhi)
                    exact hleftmost hbefore.1 hbefore.2)
            · simp [hgap] at hmiddle)
    · have hmiddleGap :
          blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose := by
        by_cases heq : rightBlock = leftBlock + 1
        · have hlimitEq :
              leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) =
                blockStartOf blockSize rightBlock + 1 := by
            simpa [leftBlock, rightBlock, heq] using hleftLimitEq
          have hlimitLe :
              blockStartOf blockSize rightBlock + 1 <= answerPrefix := by
            simpa [hlimitEq] using (Nat.le_of_not_gt hanswerLeft)
          exact False.elim (hanswerRight hlimitLe)
        · have hcross' : leftBlock < rightBlock := by
            simpa [leftBlock, rightBlock] using hcross
          have hgap' : leftBlock + 1 < rightBlock := by
            omega
          simpa [leftBlock, rightBlock] using hgap'
      have hrangeEndEq :
          blockOfClose blockSize leftClose + 1 +
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1) =
            blockOfClose blockSize rightClose := by
        omega
      let answerBlock := blockOfClose blockSize answerClose
      have hanswerBlockMem :
          blockOfClose blockSize leftClose + 1 <= answerBlock /\
            answerBlock <
              blockOfClose blockSize leftClose + 1 +
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1) := by
        have hnotLeftLe :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix :=
          Nat.le_of_not_gt hanswerLeft
        have hanswerBeforeRight :
            answerPrefix < blockStartOf blockSize rightBlock + 1 :=
          Nat.lt_of_not_ge hanswerRight
        have hanswerCloseGeNext :
            blockStartOf blockSize (leftBlock + 1) <= answerClose := by
          have hlimit :
              blockStartOf blockSize (leftBlock + 1) + 1 <=
                answerPrefix := by
            simpa [leftBlock, hleftLimitEq] using hnotLeftLe
          omega
        have hanswerCloseLtRight :
            answerClose < blockStartOf blockSize rightBlock := by
          omega
        constructor
        · have hanswerBlockGeLeftNext : leftBlock + 1 <= answerBlock := by
            by_cases hge : leftBlock + 1 <= answerBlock
            · exact hge
            · have hltBlock : answerBlock < leftBlock + 1 :=
                Nat.lt_of_not_ge hge
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := answerClose)
                  hblockSize
              have hend' :
                  answerClose <
                    blockStartOf blockSize answerBlock + blockSize := by
                simpa [answerBlock] using hend
              have hsucc :
                  blockStartOf blockSize answerBlock + blockSize =
                    blockStartOf blockSize (answerBlock + 1) :=
                blockStartOf_succ blockSize answerBlock
              have hmono :
                  blockStartOf blockSize (answerBlock + 1) <=
                    blockStartOf blockSize (leftBlock + 1) :=
                blockStartOf_mono (blockSize := blockSize) (by omega)
              have hnext :
                  answerClose < blockStartOf blockSize (leftBlock + 1) := by
                omega
              omega
          simpa [answerBlock, leftBlock] using hanswerBlockGeLeftNext
        · have hanswerBlockLtRight : answerBlock < rightBlock := by
            by_cases hlt : answerBlock < rightBlock
            · exact hlt
            · have hge : rightBlock <= answerBlock := Nat.le_of_not_gt hlt
              have hstartAns :=
                blockStartOf_blockOfClose_le
                  (blockSize := blockSize) (close := answerClose)
              have hstartAns' :
                  blockStartOf blockSize answerBlock <= answerClose := by
                simpa [answerBlock] using hstartAns
              have hmono :
                  blockStartOf blockSize rightBlock <=
                    blockStartOf blockSize answerBlock :=
                blockStartOf_mono (blockSize := blockSize) hge
              omega
          simpa [answerBlock, rightBlock, hrangeEndEq] using
            hanswerBlockLtRight
      have hanswerBlockLtRight : answerBlock < rightBlock := by
        have h := hanswerBlockMem.2
        simpa [answerBlock, rightBlock, hrangeEndEq] using h
      have hanswerBlockTarget :
          bpBlockArgMinPrefixPos shape blockSize answerBlock =
            answerPrefix := by
        have hlocalMem :
            blockStartOf blockSize answerBlock <= answerPrefix /\
              answerPrefix <
                blockStartOf blockSize answerBlock + (blockSize + 1) := by
          have hstart :=
            blockStartOf_blockOfClose_le
              (blockSize := blockSize) (close := answerClose)
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := answerClose)
              hblockSize
          constructor
          · simpa [answerBlock, answerPrefix] using
              (by omega : blockStartOf blockSize
                  (blockOfClose blockSize answerClose) <=
                answerClose + 1)
          · simpa [answerBlock, answerPrefix] using
              (by omega : answerClose + 1 <
                blockStartOf blockSize
                    (blockOfClose blockSize answerClose) +
                  (blockSize + 1))
        have hlocalBound :
            blockStartOf blockSize answerBlock + (blockSize + 1) <=
              shape.bpCode.length + 1 := by
          have hmono :
              blockStartOf blockSize (answerBlock + 1) <=
                blockStartOf blockSize rightBlock :=
            blockStartOf_mono (blockSize := blockSize) (by omega)
          have hsucc :
              blockStartOf blockSize answerBlock + blockSize =
                blockStartOf blockSize (answerBlock + 1) :=
            blockStartOf_succ blockSize answerBlock
          omega
        exact
          bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess
            hlocalMem hlocalBound
            (by
              intro pos hlo hhi
              have hinside :
                  leftClose + 1 <= pos /\ pos < rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize answerBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize answerBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        have h := hanswerBlockMem.1
                        simpa [answerBlock, leftBlock] using h)
                  omega
                have hupper :
                    pos < blockStartOf blockSize rightBlock + 1 := by
                  have hanswerBlockLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  have hmono :
                      blockStartOf blockSize (answerBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize answerBlock + blockSize =
                        blockStartOf blockSize (answerBlock + 1) :=
                    blockStartOf_succ blockSize answerBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hlo
                · have hrightStartLe' :
                    blockStartOf blockSize rightBlock <= rightClose :=
                    hrightStartLe
                  omega
              exact hmin hinside.1 hinside.2)
            (by
              intro pos hlo hhi
              have hstartLower :
                  leftClose + 1 <= blockStartOf blockSize answerBlock := by
                have hleftLeBlock :
                    blockStartOf blockSize (leftBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize)
                    (by
                      have h := hanswerBlockMem.1
                      simpa [answerBlock, leftBlock] using h)
                omega
              exact hleftmost (Nat.le_trans hstartLower hlo) hhi)
      have hmiddlePair :
          (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
            bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) =
            (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
        exact
          bpRangeWitness_eq_of_leftmost_block_candidate
            hanswerBlockMem
            hanswerBlockTarget
            (by
              intro candidateBlock hcLo hcHi
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hend :
                      blockOfClose blockSize leftClose + 1 +
                          (blockOfClose blockSize rightClose -
                            blockOfClose blockSize leftClose - 1) =
                        blockOfClose blockSize rightClose := by
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hinside :
                  leftClose + 1 <=
                      bpBlockArgMinPrefixPos shape blockSize candidateBlock /\
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        simpa [leftBlock] using hcLo)
                  omega
                have hupper :
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      blockStartOf blockSize rightBlock + 1 := by
                  have hcandidateLtRight : candidateBlock < rightBlock := by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    omega
                  have hmono :
                      blockStartOf blockSize (candidateBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize candidateBlock + blockSize =
                        blockStartOf blockSize (candidateBlock + 1) :=
                    blockStartOf_succ blockSize candidateBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hcandMem.1
                · omega
              exact hmin hinside.1 hinside.2)
            (by
              intro candidateBlock hcLo hcLt
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hABLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hlower :
                  leftClose + 1 <=
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by simpa [leftBlock] using hcLo)
                  omega
                exact Nat.le_trans hstartLower hcandMem.1
              have hbefore :
                  bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                    answerPrefix := by
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                have hanswerLower :
                    blockStartOf blockSize answerBlock + 1 <= answerPrefix := by
                  have hstart :=
                    blockStartOf_blockOfClose_le
                      (blockSize := blockSize) (close := answerClose)
                  simpa [answerBlock, answerPrefix] using
                    (by omega : blockStartOf blockSize
                        (blockOfClose blockSize answerClose) + 1 <=
                      answerClose + 1)
                omega
              exact hleftmost hlower (by simpa [answerPrefix] using hbefore))
      have hleftGt :
          bpExcessAt shape (answerClose + 1) <
            bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) := by
        have hleftCount :
            0 <
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose := by
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := leftClose)
              hblockSize
          omega
        exact
          bpPrefixRangeMinExcess_gt_of_all_prefix_gt
            hleftCount
            (by simpa [leftBlock] using hleftBound)
            (by
              intro pos hlo hhi
              have hlimit :
                  leftClose + 1 +
                      (blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize - leftClose) <= answerPrefix :=
                Nat.le_of_not_gt hanswerLeft
              exact hleftmost hlo (by simpa [answerPrefix] using
                (by omega : pos < answerPrefix)))
      have hrightLe :
          bpExcessAt shape (answerClose + 1) <=
            bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        have hrightCount :
            0 <
              rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2 := by
          omega
        exact
          bpPrefixRangeMinExcess_ge_of_all_prefix_ge
            hrightCount
            (by simpa [rightBlock] using hrightBound)
            (by
              intro pos hlo hhi
              have hinside := hrightInside hlo hhi
              exact hmin hinside.1 hinside.2)
      exact
        component.lcaCloseCosted_exact_of_decoded_middle_candidate
          leftClose rightClose hblockSize hleftBlock hrightBlock
          hmiddleGap hmiddlePair hleftGt hrightLe

theorem lcaCloseCosted_exact_of_query_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
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
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock hcross
      hsemantic.1 hsemantic.2

theorem lcaCloseCosted_exact_of_spanning_root_cross_block
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock hcross
      hsemantic.1 hsemantic.2

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  have hleft := component.leftFringe.read_words_length_le_machine hmachine
  have hmid := component.interior.read_words_length_le_machine hmachine
  have hright := component.rightFringe.read_words_length_le_machine hmachine
  exact ⟨hleft.1, hleft.2, hmid.1, hmid.2, hright.1, hright.2⟩

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  constructor
  · exact component.payload_length
  intro leftClose rightClose
  exact ⟨component.lcaCloseCosted_cost_le_six leftClose rightClose,
    component.lcaCloseCosted_erase leftClose rightClose⟩

theorem profile_cross_block_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockOfClose blockSize leftClose < blockCount ->
                      blockOfClose blockSize rightClose < blockCount ->
                        blockOfClose blockSize leftClose <
                            blockOfClose blockSize rightClose ->
                          (component.lcaCloseCosted
                            leftClose rightClose).erase =
                            some answerClose := by
  constructor
  · exact component.payload_length
  constructor
  · intro leftClose rightClose
    exact component.lcaCloseCosted_cost_le_six leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer hblockSize hleftBlock hrightBlock hcross
  exact
    component.lcaCloseCosted_exact_of_query_cross_block
      hlen hbound hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross

end PayloadLiveBPEndpointFringeRangeMacro

theorem bpRelativeRmmCandidateMerge_exact_of_left_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hanswerLeft :
      leftClose + 1 <= answerClose + 1 /\
        answerClose + 1 <
          leftClose + 1 +
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        shape.bpCode.length + 1)
    (hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        shape.bpCode.length + 1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  have hleftPair :
      (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
        bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerLeft hleftBound
        (by
          intro pos hlo hhi
          exact hmin hlo (hleftInside hlo hhi))
        (by
          intro pos hlo hhi
          exact hleftmost hlo hhi)
  have hrightCount :
      0 <
        rightClose -
            blockStartOf blockSize
              (blockOfClose blockSize rightClose) +
          2 := by
    omega
  have hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) := by
    exact
      bpPrefixRangeMinExcess_ge_of_all_prefix_ge
        hrightCount hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hmin hinside.1 hinside.2)
  have hmiddleLe :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) <= middle.1 := by
    intro middle hmiddle
    by_cases hblocks :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
    · simp [hblocks] at hmiddle
      subst middle
      have hcount :
          0 <
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1 := by
        omega
      exact
        bpRangeMinExcess_ge_of_all_prefix_ge
          (shape := shape) (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower := bpExcessAt shape (answerClose + 1))
          hcount
          (by
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            simpa [hend] using hmiddleBound hblocks)
          (by
            intro pos hlo hhi
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            have hinside :=
              hmiddleInside (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hmin hinside.1 hinside.2)
    · simp [hblocks] at hmiddle
  simpa [hleftPair] using
    bpCandidateMerge3?_eq_some_left_of_fst_le
      (left := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      (by
        intro middle hmiddle
        exact hmiddleLe middle hmiddle)
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem bpRelativeRmmCandidateMerge_exact_of_right_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hrightPair :
      (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hleftGt :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) < middle.1) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  simpa [hrightPair] using
    bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (right := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      hleftGt
      (by
        intro middle hmiddle
        exact hmiddleGt middle hmiddle)

theorem bpRelativeRmmCandidateMerge_exact_of_middle_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose)
    (hmiddlePair :
      (bpRangeMinExcess shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1),
        bpRangeArgMinPrefixPos shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hmiddleLeft :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  simpa [hblocks, hmiddlePair] using
    bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (middle := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      hmiddleLeft
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem bpRelativeRmmCandidateMerge_exact_of_query_semantics
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (_hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (_hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  let answerPrefix := answerClose + 1
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hanswerCloseBound := bpCloseOfInorder?_bounds shape hanswer
  have hrightStartLe :
      blockStartOf blockSize rightBlock <= rightClose := by
    simpa [rightBlock] using
      (blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose))
  have hleftNextStart :
      leftClose < blockStartOf blockSize (leftBlock + 1) := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    simpa [leftBlock, blockStartOf_succ] using hend
  have hleftLimitEq :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) =
        blockStartOf blockSize (leftBlock + 1) + 1 := by
    have hstart :
        blockStartOf blockSize leftBlock <= leftClose := by
      simpa [leftBlock] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := leftClose))
    have hsucc :
        blockStartOf blockSize leftBlock + blockSize =
          blockStartOf blockSize (leftBlock + 1) :=
      blockStartOf_succ blockSize leftBlock
    omega
  have hrightLimitEq :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) =
        rightClose + 2 := by
    omega
  have hleftToRightStart :
      blockStartOf blockSize (leftBlock + 1) <=
        blockStartOf blockSize rightBlock := by
    exact blockStartOf_mono (blockSize := blockSize) (by
      simpa [leftBlock, rightBlock] using hcross)
  have hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) <=
        shape.bpCode.length + 1 := by
    rw [hleftLimitEq]
    omega
  have hrightBound :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) <=
        shape.bpCode.length + 1 := by
    rw [hrightLimitEq]
    omega
  have hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1 := by
    intro _hgap
    have hstart :
        blockStartOf blockSize
            (blockOfClose blockSize rightClose) <= rightClose :=
      blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose)
    omega
  have hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2 := by
    intro pos _hlo hhi
    have hhi' :
        pos < blockStartOf blockSize (leftBlock + 1) + 1 := by
      simpa [leftBlock, hleftLimitEq] using hhi
    have hleRight :
        blockStartOf blockSize (leftBlock + 1) + 1 <= rightClose + 1 := by
      omega
    omega
  have hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize rightClose) := by
      have hlt := hleftNextStart
      have hmono :
          blockStartOf blockSize (leftBlock + 1) <=
            blockStartOf blockSize rightBlock :=
        hleftToRightStart
      simpa [rightBlock] using (by omega : leftClose + 1 <=
        blockStartOf blockSize rightBlock)
    constructor
    · exact Nat.le_trans hleftLe hlo
    · simpa [rightBlock, hrightLimitEq] using hhi
  have hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos _hgap hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize leftClose + 1) := by
      simpa [leftBlock] using (by omega :
        leftClose + 1 <= blockStartOf blockSize (leftBlock + 1))
    constructor
    · exact Nat.le_trans hleftLe hlo
    · have hrightLeClose :
          blockStartOf blockSize
              (blockOfClose blockSize rightClose) <= rightClose :=
        blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose)
      omega
  have hanswerMem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hanswerUpper : answerPrefix < rightClose + 2 := by
    simpa [answerPrefix] using (by omega :
      answerClose + 1 < rightClose + 2)
  by_cases hanswerLeft :
      answerPrefix <
        leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)
  · exact
      bpRelativeRmmCandidateMerge_exact_of_left_fringe_leftmost
        leftClose rightClose
        (by
          constructor
          · simpa [answerPrefix] using hanswerMem.1
          · exact hanswerLeft)
        (by simpa [leftBlock] using hleftBound)
        hleftInside
        (by simpa [rightBlock] using hrightBound)
        hrightInside
        hmiddleBound
        hmiddleInside
        hmin hleftmost
  · by_cases hanswerRight :
        blockStartOf blockSize rightBlock + 1 <= answerPrefix
    · have hrightAnswer :
        blockStartOf blockSize (blockOfClose blockSize rightClose) <=
            answerClose + 1 /\
          answerClose + 1 <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        constructor
        · simpa [rightBlock, answerPrefix] using
            (Nat.le_trans (Nat.le_of_lt (by omega :
              blockStartOf blockSize rightBlock <
                blockStartOf blockSize rightBlock + 1)) hanswerRight)
        · simpa [rightBlock, hrightLimitEq, answerPrefix] using hanswerUpper
      have hleftBefore :
          forall {pos : Nat},
            leftClose + 1 <= pos ->
              pos <
                leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) ->
                pos < answerClose + 1 := by
        intro pos _hlo hhi
        have hlimit :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix := by
          omega
        simpa [answerPrefix] using (by omega : pos < answerPrefix)
      have hmiddleBefore :
          forall {pos : Nat},
            blockOfClose blockSize leftClose + 1 <
                blockOfClose blockSize rightClose ->
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose + 1) <= pos ->
                pos <
                  blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                    1 ->
                  leftClose + 1 <= pos /\ pos < answerClose + 1 := by
        intro pos hgap hlo hhi
        have hinside := hmiddleInside (pos := pos) hgap hlo hhi
        constructor
        · exact hinside.1
        · have hhi' : pos < blockStartOf blockSize rightBlock + 1 := by
            simpa [rightBlock] using hhi
          simpa [answerPrefix] using
            (by omega : pos < answerPrefix)
      exact
        bpRelativeRmmCandidateMerge_exact_of_right_fringe_leftmost
          leftClose rightClose
          (by
            exact
              bpPrefixRangeWitness_eq_of_leftmost_min_excess
                hrightAnswer
                (by simpa [rightBlock] using hrightBound)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo hhi
                  exact hmin hinside.1 hinside.2)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo (by omega)
                  exact hleftmost hinside.1 hhi))
          (by
            have hleftCount :
                0 <
                  blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose := by
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := leftClose)
                  hblockSize
              omega
            exact
              bpPrefixRangeMinExcess_gt_of_all_prefix_gt
                hleftCount
                (by simpa [leftBlock] using hleftBound)
                (by
                  intro pos hlo hhi
                  exact hleftmost hlo (hleftBefore hlo hhi)))
          (by
            intro middle hmiddle
            by_cases hgap :
                blockOfClose blockSize leftClose + 1 <
                  blockOfClose blockSize rightClose
            · simp [hgap] at hmiddle
              subst middle
              have hcount :
                  0 <
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1 := by
                omega
              exact
                bpRangeMinExcess_gt_of_all_prefix_gt
                  (shape := shape) (blockSize := blockSize)
                  (startBlock :=
                    blockOfClose blockSize leftClose + 1)
                  (blockCount :=
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1)
                  (lower := bpExcessAt shape (answerClose + 1))
                  hcount
                  (by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    simpa [hend] using hmiddleBound hgap)
                  (by
                    intro pos hlo hhi
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    have hbefore :=
                      hmiddleBefore (pos := pos) hgap hlo
                        (by simpa [hend] using hhi)
                    exact hleftmost hbefore.1 hbefore.2)
            · simp [hgap] at hmiddle)
    · have hmiddleGap :
          blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose := by
        by_cases heq : rightBlock = leftBlock + 1
        · have hlimitEq :
              leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) =
                blockStartOf blockSize rightBlock + 1 := by
            simpa [leftBlock, rightBlock, heq] using hleftLimitEq
          have hlimitLe :
              blockStartOf blockSize rightBlock + 1 <= answerPrefix := by
            simpa [hlimitEq] using (Nat.le_of_not_gt hanswerLeft)
          exact False.elim (hanswerRight hlimitLe)
        · have hcross' : leftBlock < rightBlock := by
            simpa [leftBlock, rightBlock] using hcross
          have hgap' : leftBlock + 1 < rightBlock := by
            omega
          simpa [leftBlock, rightBlock] using hgap'
      have hrangeEndEq :
          blockOfClose blockSize leftClose + 1 +
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1) =
            blockOfClose blockSize rightClose := by
        omega
      let answerBlock := blockOfClose blockSize answerClose
      have hanswerBlockMem :
          blockOfClose blockSize leftClose + 1 <= answerBlock /\
            answerBlock <
              blockOfClose blockSize leftClose + 1 +
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1) := by
        have hnotLeftLe :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix :=
          Nat.le_of_not_gt hanswerLeft
        have hanswerBeforeRight :
            answerPrefix < blockStartOf blockSize rightBlock + 1 :=
          Nat.lt_of_not_ge hanswerRight
        have hanswerCloseGeNext :
            blockStartOf blockSize (leftBlock + 1) <= answerClose := by
          have hlimit :
              blockStartOf blockSize (leftBlock + 1) + 1 <=
                answerPrefix := by
            simpa [leftBlock, hleftLimitEq] using hnotLeftLe
          omega
        have hanswerCloseLtRight :
            answerClose < blockStartOf blockSize rightBlock := by
          omega
        constructor
        · have hanswerBlockGeLeftNext : leftBlock + 1 <= answerBlock := by
            by_cases hge : leftBlock + 1 <= answerBlock
            · exact hge
            · have hltBlock : answerBlock < leftBlock + 1 :=
                Nat.lt_of_not_ge hge
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := answerClose)
                  hblockSize
              have hend' :
                  answerClose <
                    blockStartOf blockSize answerBlock + blockSize := by
                simpa [answerBlock] using hend
              have hsucc :
                  blockStartOf blockSize answerBlock + blockSize =
                    blockStartOf blockSize (answerBlock + 1) :=
                blockStartOf_succ blockSize answerBlock
              have hmono :
                  blockStartOf blockSize (answerBlock + 1) <=
                    blockStartOf blockSize (leftBlock + 1) :=
                blockStartOf_mono (blockSize := blockSize) (by omega)
              have hnext :
                  answerClose < blockStartOf blockSize (leftBlock + 1) := by
                omega
              omega
          simpa [answerBlock, leftBlock] using hanswerBlockGeLeftNext
        · have hanswerBlockLtRight : answerBlock < rightBlock := by
            by_cases hlt : answerBlock < rightBlock
            · exact hlt
            · have hge : rightBlock <= answerBlock := Nat.le_of_not_gt hlt
              have hstartAns :=
                blockStartOf_blockOfClose_le
                  (blockSize := blockSize) (close := answerClose)
              have hstartAns' :
                  blockStartOf blockSize answerBlock <= answerClose := by
                simpa [answerBlock] using hstartAns
              have hmono :
                  blockStartOf blockSize rightBlock <=
                    blockStartOf blockSize answerBlock :=
                blockStartOf_mono (blockSize := blockSize) hge
              omega
          simpa [answerBlock, rightBlock, hrangeEndEq] using
            hanswerBlockLtRight
      have hanswerBlockLtRight : answerBlock < rightBlock := by
        have h := hanswerBlockMem.2
        simpa [answerBlock, rightBlock, hrangeEndEq] using h
      have hanswerBlockTarget :
          bpBlockArgMinPrefixPos shape blockSize answerBlock =
            answerPrefix := by
        have hlocalMem :
            blockStartOf blockSize answerBlock <= answerPrefix /\
              answerPrefix <
                blockStartOf blockSize answerBlock + (blockSize + 1) := by
          have hstart :=
            blockStartOf_blockOfClose_le
              (blockSize := blockSize) (close := answerClose)
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := answerClose)
              hblockSize
          constructor
          · simpa [answerBlock, answerPrefix] using
              (by omega : blockStartOf blockSize
                  (blockOfClose blockSize answerClose) <=
                answerClose + 1)
          · simpa [answerBlock, answerPrefix] using
              (by omega : answerClose + 1 <
                blockStartOf blockSize
                    (blockOfClose blockSize answerClose) +
                  (blockSize + 1))
        have hlocalBound :
            blockStartOf blockSize answerBlock + (blockSize + 1) <=
              shape.bpCode.length + 1 := by
          have hmono :
              blockStartOf blockSize (answerBlock + 1) <=
                blockStartOf blockSize rightBlock :=
            blockStartOf_mono (blockSize := blockSize) (by omega)
          have hsucc :
              blockStartOf blockSize answerBlock + blockSize =
                blockStartOf blockSize (answerBlock + 1) :=
            blockStartOf_succ blockSize answerBlock
          omega
        exact
          bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess
            hlocalMem hlocalBound
            (by
              intro pos hlo hhi
              have hinside :
                  leftClose + 1 <= pos /\ pos < rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize answerBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize answerBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        have h := hanswerBlockMem.1
                        simpa [answerBlock, leftBlock] using h)
                  omega
                have hupper :
                    pos < blockStartOf blockSize rightBlock + 1 := by
                  have hanswerBlockLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  have hmono :
                      blockStartOf blockSize (answerBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize answerBlock + blockSize =
                        blockStartOf blockSize (answerBlock + 1) :=
                    blockStartOf_succ blockSize answerBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hlo
                · have hrightStartLe' :
                    blockStartOf blockSize rightBlock <= rightClose :=
                    hrightStartLe
                  omega
              exact hmin hinside.1 hinside.2)
            (by
              intro pos hlo hhi
              have hstartLower :
                  leftClose + 1 <= blockStartOf blockSize answerBlock := by
                have hleftLeBlock :
                    blockStartOf blockSize (leftBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize)
                    (by
                      have h := hanswerBlockMem.1
                      simpa [answerBlock, leftBlock] using h)
                omega
              exact hleftmost (Nat.le_trans hstartLower hlo) hhi)
      have hmiddlePair :
          (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
            bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) =
            (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
        exact
          bpRangeWitness_eq_of_leftmost_block_candidate
            hanswerBlockMem
            hanswerBlockTarget
            (by
              intro candidateBlock hcLo hcHi
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hend :
                      blockOfClose blockSize leftClose + 1 +
                          (blockOfClose blockSize rightClose -
                            blockOfClose blockSize leftClose - 1) =
                        blockOfClose blockSize rightClose := by
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hinside :
                  leftClose + 1 <=
                      bpBlockArgMinPrefixPos shape blockSize candidateBlock /\
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        simpa [leftBlock] using hcLo)
                  omega
                have hupper :
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      blockStartOf blockSize rightBlock + 1 := by
                  have hcandidateLtRight : candidateBlock < rightBlock := by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    omega
                  have hmono :
                      blockStartOf blockSize (candidateBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize candidateBlock + blockSize =
                        blockStartOf blockSize (candidateBlock + 1) :=
                    blockStartOf_succ blockSize candidateBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hcandMem.1
                · omega
              exact hmin hinside.1 hinside.2)
            (by
              intro candidateBlock hcLo hcLt
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hABLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hlower :
                  leftClose + 1 <=
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by simpa [leftBlock] using hcLo)
                  omega
                exact Nat.le_trans hstartLower hcandMem.1
              have hbefore :
                  bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                    answerPrefix := by
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                have hanswerLower :
                    blockStartOf blockSize answerBlock + 1 <= answerPrefix := by
                  have hstart :=
                    blockStartOf_blockOfClose_le
                      (blockSize := blockSize) (close := answerClose)
                  simpa [answerBlock, answerPrefix] using
                    (by omega : blockStartOf blockSize
                        (blockOfClose blockSize answerClose) + 1 <=
                      answerClose + 1)
                omega
              exact hleftmost hlower (by simpa [answerPrefix] using hbefore))
      have hleftGt :
          bpExcessAt shape (answerClose + 1) <
            bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) := by
        have hleftCount :
            0 <
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose := by
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := leftClose)
              hblockSize
          omega
        exact
          bpPrefixRangeMinExcess_gt_of_all_prefix_gt
            hleftCount
            (by simpa [leftBlock] using hleftBound)
            (by
              intro pos hlo hhi
              have hlimit :
                  leftClose + 1 +
                      (blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize - leftClose) <= answerPrefix :=
                Nat.le_of_not_gt hanswerLeft
              exact hleftmost hlo (by simpa [answerPrefix] using
                (by omega : pos < answerPrefix)))
      have hrightLe :
          bpExcessAt shape (answerClose + 1) <=
            bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        have hrightCount :
            0 <
              rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2 := by
          omega
        exact
          bpPrefixRangeMinExcess_ge_of_all_prefix_ge
            hrightCount
            (by simpa [rightBlock] using hrightBound)
            (by
              intro pos hlo hhi
              have hinside := hrightInside hlo hhi
              exact hmin hinside.1 hinside.2)
      exact
        bpRelativeRmmCandidateMerge_exact_of_middle_leftmost
          leftClose rightClose hmiddleGap hmiddlePair hleftGt hrightLe

theorem bpRelativeRmmCandidateMerge_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (hlen := hlen) hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross hsemantic.1 hsemantic.2

def concreteBPEndpointFringeRangeMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
      fieldWidth
      (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
        fieldWidth))
      (2 * ((interiorBlockPairRanges blockCount).length * fieldWidth))
      (2 * ((endpointRightFringeRanges blockSize blockCount).length *
        fieldWidth)) where
  leftFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointLeftFringeRanges blockSize blockCount) hwidth
  interior :=
    concreteBPRangeArgMinWitnessTable shape blockSize fieldWidth
      (interiorBlockPairRanges blockCount) hwidth
  rightFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointRightFringeRanges blockSize blockCount) hwidth

theorem concreteBPEndpointFringeRangeMacro_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    component.payload.length =
        2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile := component.profile
  constructor
  · simpa [component, concreteBPEndpointFringeRangeMacro,
      endpointLeftFringeRanges_length, endpointRightFringeRanges_length,
      interiorBlockPairRanges_length] using hprofile.1
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hprofile.1]
    exact hbudget
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_query_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockOfClose blockSize leftClose < blockCount ->
                      blockOfClose blockSize rightClose < blockCount ->
                        blockOfClose blockSize leftClose <
                            blockOfClose blockSize rightClose ->
                          (component.lcaCloseCosted
                            leftClose rightClose).erase =
                            some answerClose := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    (component.profile_cross_block_exact)
  have hpayload :=
    (concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth).1
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hpayload]
    exact hbudget
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2

theorem concreteBPEndpointFringeRangeMacro_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPEndpointFringeRangeMacro.read_words_length_le_machine
      (concreteBPEndpointFringeRangeMacro
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

/-!
## Relative rmM-style close macro interface

The guarded endpoint-fringe directory above is exact, but its concrete macro
payload still contains a dense `interiorBlockPairRanges blockCount` table.  The
next surface below isolates the query-side contract needed from a compact
Navarro-Sadakane/rmM-style macro: endpoint repairs and the middle full-block
range are charged candidate reads, while the middle candidate is supplied by a
relative summary navigator rather than an all-pairs block table.
-/

/--
Payload-live relative-rmM macro for cross-block BP close/LCA queries.

The payload layout is intentionally abstract here because the concrete
relative/log-log summary builder is a separate component.  The query contract is
not abstract: `lcaCloseCosted` is built from three charged candidate reads, and
the semantic exactness theorem below consumes their decoded range-witness facts
plus the global `bpRelativeRmmCandidateMerge_exact` merge theorem.
-/
structure PayloadLiveRelativeRmmBPCloseMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount overhead middleQueryCost : Nat) where
  payload : List Bool
  payload_length_eq : payload.length = overhead
  payloadWordsRead : Nat -> Nat -> List (List Bool)
  leftFringeCosted : Nat -> Costed (Option (Nat × Nat))
  rightFringeCosted : Nat -> Costed (Option (Nat × Nat))
  interiorRmmCosted : Nat -> Nat -> Costed (Option (Nat × Nat))
  leftFringe_cost_le_two :
    forall leftClose,
      (leftFringeCosted leftClose).cost <= 2
  rightFringe_cost_le_two :
    forall rightClose,
      (rightFringeCosted rightClose).cost <= 2
  interiorRmm_cost_le :
    forall leftClose rightClose,
      (interiorRmmCosted leftClose rightClose).cost <= middleQueryCost
  leftFringe_exact :
    forall {leftClose : Nat},
      blockOfClose blockSize leftClose < blockCount ->
        (leftFringeCosted leftClose).erase =
          some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose))
  rightFringe_exact :
    forall {rightClose : Nat},
      blockOfClose blockSize rightClose < blockCount ->
        (rightFringeCosted rightClose).erase =
          some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2))
  interiorRmm_exact :
    forall {leftClose rightClose : Nat},
      blockOfClose blockSize leftClose < blockCount ->
        blockOfClose blockSize rightClose < blockCount ->
          blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose ->
            (interiorRmmCosted leftClose rightClose).erase =
              some
                (bpRangeMinExcess shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1),
                  bpRangeArgMinPrefixPos shape blockSize
                    (blockOfClose blockSize leftClose + 1)
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1))
  read_words_length_le_machine :
    forall {leftClose rightClose : Nat} {word : List Bool},
      word ∈ payloadWordsRead leftClose rightClose ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length

namespace PayloadLiveRelativeRmmBPCloseMacro

def interiorCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  if blockOfClose blockSize leftClose + 1 <
      blockOfClose blockSize rightClose then
    component.interiorRmmCosted leftClose rightClose
  else
    Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind (component.leftFringeCosted leftClose) fun left? =>
    Costed.bind (component.interiorCandidateCosted leftClose rightClose)
      fun middle? =>
        Costed.map
          (fun right? =>
            bpCandidateClose? (bpCandidateMerge3? left? middle? right?))
          (component.rightFringeCosted rightClose)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost) :
    component.payload.length = overhead := by
  exact component.payload_length_eq

theorem interiorCandidateCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (component.interiorCandidateCosted leftClose rightClose).cost <=
      middleQueryCost := by
  unfold interiorCandidateCosted
  by_cases hgap :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [hgap]
    exact component.interiorRmm_cost_le leftClose rightClose
  · simp [hgap, Costed.pure]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <=
      4 + middleQueryCost := by
  unfold lcaCloseCosted
  have hleft := component.leftFringe_cost_le_two leftClose
  have hmiddle :=
    component.interiorCandidateCosted_cost_le leftClose rightClose
  have hright := component.rightFringe_cost_le_two rightClose
  simp [Costed.bind, Costed.map]
  omega

theorem lcaCloseCosted_erase_decoded
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost leftClose rightClose : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      bpCandidateClose?
        (bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose)))
          (if blockOfClose blockSize leftClose + 1 <
                blockOfClose blockSize rightClose then
              some
                (bpRangeMinExcess shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1),
                  bpRangeArgMinPrefixPos shape blockSize
                    (blockOfClose blockSize leftClose + 1)
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1))
            else
              none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2)))) := by
  have hleft :
      (component.leftFringeCosted leftClose).value =
        some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)) := by
    simpa [Costed.erase] using component.leftFringe_exact hleftBlock
  have hright :
      (component.rightFringeCosted rightClose).value =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)) := by
    simpa [Costed.erase] using component.rightFringe_exact hrightBlock
  unfold lcaCloseCosted interiorCandidateCosted
  by_cases hgap :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · have hmiddle :
        (component.interiorRmmCosted leftClose rightClose).value =
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1)) := by
      simpa [Costed.erase] using
        component.interiorRmm_exact hleftBlock hrightBlock hgap
    simp [Costed.bind, Costed.map, Costed.erase, hleft, hright,
      hmiddle, hgap]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      hleft, hright, hgap]

theorem lcaCloseCosted_exact_of_query_semantics_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  rw [component.lcaCloseCosted_erase_decoded hleftBlock hrightBlock]
  have hmerge :=
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (hlen := hlen) hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross hmin hleftmost
  simp [hmerge, bpCandidateClose?]

theorem lcaCloseCosted_exact_of_query_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost)
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
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock
      hcross hsemantic.1 hsemantic.2

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead middleQueryCost : Nat}
    (component :
      PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
        overhead middleQueryCost) :
    component.payload.length = overhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) := by
  exact ⟨component.payload_length, component.lcaCloseCosted_cost_le⟩

end PayloadLiveRelativeRmmBPCloseMacro

def payloadLiveRelativeRmmBPCloseMacroOfInterior
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead middleQueryCost : Nat}
    (leftFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        leftOverhead (endpointLeftFringeRanges blockSize blockCount))
    (interior :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        interiorOverhead middleQueryCost)
    (rightFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        rightOverhead (endpointRightFringeRanges blockSize blockCount))
    (hblockSize : 0 < blockSize) :
    PayloadLiveRelativeRmmBPCloseMacro shape blockSize blockCount
      (leftOverhead + interiorOverhead + rightOverhead) middleQueryCost where
  payload := leftFringe.payload ++ interior.payload ++ rightFringe.payload
  payload_length_eq := by
    simp [leftFringe.payload_length, interior.payload_length_eq,
      rightFringe.payload_length]
    omega
  payloadWordsRead := fun _ _ => []
  leftFringeCosted := fun leftClose =>
    leftFringe.rangeWitnessCosted (endpointFringeSlot blockSize leftClose)
  rightFringeCosted := fun rightClose =>
    rightFringe.rangeWitnessCosted (endpointFringeSlot blockSize rightClose)
  interiorRmmCosted := fun leftClose rightClose =>
    interior.rangeMinCosted (blockOfClose blockSize leftClose + 1)
      (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1)
  leftFringe_cost_le_two := by
    intro leftClose
    exact leftFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize leftClose)
  rightFringe_cost_le_two := by
    intro rightClose
    exact rightFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize rightClose)
  interiorRmm_cost_le := by
    intro leftClose rightClose
    exact interior.rangeMin_cost_le
      (blockOfClose blockSize leftClose + 1)
      (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1)
  leftFringe_exact := by
    intro leftClose hleftBlock
    have hmin :
        (bpPrefixRangeMinExcessEntries shape
          (endpointLeftFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize leftClose]? =
          some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)) :=
      endpointLeftFringeMinExcessEntries_get?_of_close_bounds
        hblockSize
        hleftBlock
    have harg :
        (bpPrefixRangeArgMinPrefixPosEntries shape
          (endpointLeftFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize leftClose]? =
          some
            (bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)) :=
      endpointLeftFringeArgMinEntries_get?_of_close_bounds
        hblockSize
        hleftBlock
    simpa [Costed.erase, hmin, harg] using
      leftFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize leftClose)
  rightFringe_exact := by
    intro rightClose hrightBlock
    have hmin :
        (bpPrefixRangeMinExcessEntries shape
          (endpointRightFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize rightClose]? =
          some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)) :=
      endpointRightFringeMinExcessEntries_get?_of_close_bounds
        hblockSize hrightBlock
    have harg :
        (bpPrefixRangeArgMinPrefixPosEntries shape
          (endpointRightFringeRanges blockSize blockCount))[
            endpointFringeSlot blockSize rightClose]? =
          some
            (bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)) :=
      endpointRightFringeArgMinEntries_get?_of_close_bounds
        hblockSize hrightBlock
    simpa [Costed.erase, hmin, harg] using
      rightFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize rightClose)
  interiorRmm_exact := by
    intro leftClose rightClose hleftBlock hrightBlock hgap
    have hcount :
        0 <
          blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1 := by
      omega
    have hbound :
        blockOfClose blockSize leftClose + 1 +
            (blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1) <=
          blockCount := by
      omega
    exact interior.rangeMin_exact hcount hbound
  read_words_length_le_machine := by
    intro leftClose rightClose word hmem
    cases hmem

theorem payloadLiveRelativeRmmBPCloseMacroOfInterior_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead middleQueryCost : Nat}
    (leftFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        leftOverhead (endpointLeftFringeRanges blockSize blockCount))
    (interior :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        interiorOverhead middleQueryCost)
    (rightFringe :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
        rightOverhead (endpointRightFringeRanges blockSize blockCount))
    (hblockSize : 0 < blockSize) :
    let component :=
      payloadLiveRelativeRmmBPCloseMacroOfInterior
        leftFringe interior rightFringe hblockSize
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <=
          4 + middleQueryCost) := by
  exact
    (payloadLiveRelativeRmmBPCloseMacroOfInterior
      leftFringe interior rightFringe hblockSize).profile

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

end SuccinctCloseProposal
end RMQ
