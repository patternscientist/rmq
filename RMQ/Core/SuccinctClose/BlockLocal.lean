import RMQ.Core.SuccinctRankProposal

/-!
# Block-local BP close/LCA tables

Dense block-local BP close/LCA specifications, concrete tables, and the dense
all-close obstruction. The historical `RMQ.SuccinctCloseProposal` namespace is
preserved so theorem names remain stable.
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


end SuccinctCloseProposal
end RMQ
