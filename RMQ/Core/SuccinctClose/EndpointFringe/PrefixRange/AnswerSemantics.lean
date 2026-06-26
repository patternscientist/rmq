import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.LocalSparseOffset

/-!
# Endpoint-fringe answer semantics

Split from `RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange`.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

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

end SuccinctClose
end RMQ
