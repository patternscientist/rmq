import RMQ.Core.SuccinctClose.BlockLocal

/-!
# BP range min/max summary tables

Absolute BP prefix-excess samples and payload-live min/max summary tables used
by the later relative-rmM close navigation layers. The historical
`RMQ.SuccinctCloseProposal` namespace is preserved.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace
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
        SuccinctRank.machineWordBits shape.bpCode.length)
    {block : Nat} {word : List Bool}
    (hword : table.minTable.store.words[block]? = some word) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
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
        SuccinctRank.machineWordBits shape.bpCode.length)
    {block : Nat} {word : List Bool}
    (hword : table.maxTable.store.words[block]? = some word) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
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
        SuccinctRank.machineWordBits shape.bpCode.length) :
    (forall {block : Nat} {word : List Bool},
      table.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
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
        SuccinctRank.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRangeMinMaxSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    (forall {block : Nat} {word : List Bool},
      table.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
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
        SuccinctRank.machineWordBits shape.bpCode.length)
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
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
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


end SuccinctCloseProposal
end RMQ
