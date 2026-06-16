import RMQ.Core.Shape

/-!
# Shape-indexed microtables

This module starts the Fischer-Heun microtable API. A microtable is indexed by
a block's explicit Cartesian shape and answers local half-open queries by
returning an offset into that block.

The API is intentionally contract-first: later implementations can choose how
to materialize the table, while clients only need the small exactness theorem
stated here.
-/

namespace RMQ

namespace Cartesian

namespace CartesianShape

/--
Raw shape-only local query. The returned value is an offset from the start of
the block represented by the shape.

This is the recursive decision tree that a concrete microtable can materialize:
queries entirely to the left or right of the root recurse into the corresponding
child, while any query containing the root returns the root offset.
-/
def queryOffset? : CartesianShape -> Nat -> Nat -> Option Nat
  | empty, _left, _right => none
  | node leftShape rightShape, left, right =>
      let pivot := leftShape.size
      let size := leftShape.size + 1 + rightShape.size
      if _hvalid : left < right /\ right <= size then
        if _hright_left : right <= pivot then
          queryOffset? leftShape left right
        else if _hroot_left : pivot < left then
          (queryOffset? rightShape (left - (pivot + 1))
              (right - (pivot + 1))).map fun offset =>
            pivot + 1 + offset
        else
          some pivot
      else
        none

end CartesianShape

/-- A valid local query into a block of a fixed size. -/
abbrev LocalValid (blockSize left right : Nat) : Prop :=
  left < right /\ right <= blockSize

/-- The finite shape universe used by a size-`blockSize` microtable. -/
def shapeUniverse (blockSize : Nat) : List CartesianShape :=
  shapesOfSize blockSize

theorem shapeUniverse_length (blockSize : Nat) :
    (shapeUniverse blockSize).length = shapeCount blockSize := by
  rfl

theorem blockSignature_mem_shapeUniverse
    (xs : List Int) (start len : Nat) :
    blockSignature xs start len ∈ shapeUniverse len := by
  unfold shapeUniverse
  exact shapeOfSize_mem_shapesOfSize (blockSignature_shapeOfSize xs start len)

/--
The direct local answer offset for a concrete block. It is an offset from
`start`, not an absolute index.
-/
def localScanOffset
    (xs : List Int) (start left right : Nat) : Nat :=
  scanWindow xs (start + left) (right - left) - start

theorem localScanOffset_bounds
    {xs : List Int} {start blockSize left right : Nat}
    (hbound : start + blockSize <= xs.length)
    (hvalid : LocalValid blockSize left right) :
    left <= localScanOffset xs start left right /\
      localScanOffset xs start left right < right := by
  have hlen : 0 < right - left := by
    omega
  have hscan_bound : start + left + (right - left) <= xs.length := by
    omega
  have hbounds :=
    scanWindow_bounds xs (start + left) (right - left) hlen
  unfold localScanOffset
  omega

theorem localScanOffset_add_start
    {xs : List Int} {start blockSize left right : Nat}
    (hvalid : LocalValid blockSize left right) :
    start + localScanOffset xs start left right =
      scanWindow xs (start + left) (right - left) := by
  have hlen : 0 < right - left := by
    omega
  have hbounds :=
    scanWindow_bounds xs (start + left) (right - left) hlen
  unfold localScanOffset
  omega

theorem localScanOffset_leftmost
    {xs : List Int} {start blockSize left right : Nat}
    (hbound : start + blockSize <= xs.length)
    (hvalid : LocalValid blockSize left right) :
    LeftmostArgMin xs (start + left) (start + right)
      (start + localScanOffset xs start left right) := by
  have hlen : 0 < right - left := by
    omega
  have hscan_bound : start + left + (right - left) <= xs.length := by
    omega
  have hscan :=
    scanWindow_leftmost xs (start + left) (right - left) hlen hscan_bound
  have hidx := localScanOffset_add_start
    (xs := xs) (start := start) (blockSize := blockSize)
    (left := left) (right := right) hvalid
  have hend : start + left + (right - left) = start + right := by
    omega
  simpa [hidx, hend] using hscan

theorem queryOffset?_blockSignature
    {xs : List Int} {start blockSize left right : Nat}
    (hbound : start + blockSize <= xs.length) :
    (blockSignature xs start blockSize).queryOffset? left right =
      if _hvalid : LocalValid blockSize left right then
        some (localScanOffset xs start left right)
      else
        none := by
  unfold blockSignature
  exact
    Nat.strongRecOn
      (motive := fun blockSize =>
        forall start left right,
          start + blockSize <= xs.length ->
            (shapeRange xs start blockSize).queryOffset? left right =
              if _hvalid : LocalValid blockSize left right then
                some (localScanOffset xs start left right)
              else
                none)
      blockSize
      (fun blockSize ih start left right hbound => by
        cases blockSize with
        | zero =>
            simp [shapeRange, CartesianShape.queryOffset?, LocalValid]
            omega
        | succ blockSize' =>
            let width := blockSize' + 1
            let root := scanWindow xs start width
            let leftLen := root - start
            let rightStart := root + 1
            let rightLen := start + width - rightStart
            have hbounds : start <= root /\ root < start + width :=
              scanWindow_bounds xs start width (by omega)
            have hleftLen_lt : leftLen < width := by
              unfold leftLen
              omega
            have hrightLen_lt : rightLen < width := by
              unfold rightLen rightStart
              omega
            have hleftBound : start + leftLen <= xs.length := by
              unfold leftLen
              omega
            have hrightBound : rightStart + rightLen <= xs.length := by
              unfold rightStart rightLen
              omega
            have hleftSize :
                (shapeRange xs start leftLen).size = leftLen :=
              shapeRange_size xs start leftLen
            have hrightSize :
                (shapeRange xs rightStart rightLen).size = rightLen :=
              shapeRange_size xs rightStart rightLen
            have hpivot :
                (shapeRange xs start
                    (scanWindow xs start (blockSize' + 1) - start)).size =
                  leftLen := by
              simpa [width, root, leftLen] using hleftSize
            have hsize : leftLen + 1 + rightLen = width := by
              unfold leftLen rightLen rightStart
              omega
            by_cases hvalid : LocalValid width left right
            · have hvalidShape :
                  left < right /\
                    right <=
                      (shapeRange xs start leftLen).size + 1 +
                        (shapeRange xs rightStart rightLen).size := by
                simpa [LocalValid, hleftSize, hrightSize, hsize] using hvalid
              rw [dif_pos hvalid]
              simp [shapeRange, CartesianShape.queryOffset?, width, root,
                leftLen, rightStart, rightLen, hvalidShape]
              simp [hpivot]
              by_cases hleft : right <= leftLen
              · rw [dif_pos hleft]
                have hvalidLeft : LocalValid leftLen left right := by
                  unfold LocalValid at *
                  omega
                have hrec :=
                  ih leftLen hleftLen_lt start left right hleftBound
                have hrec' :
                    (shapeRange xs start
                        (scanWindow xs start (blockSize' + 1) - start)).queryOffset?
                      left right =
                        if _hvalid : LocalValid leftLen left right then
                          some (localScanOffset xs start left right)
                        else
                          none := by
                  simpa [width, root, leftLen] using hrec
                rw [hrec', dif_pos hvalidLeft]
              · rw [dif_neg hleft]
                by_cases hright : leftLen < left
                · rw [dif_pos hright]
                  have hvalidRight :
                      LocalValid rightLen
                        (left - (leftLen + 1)) (right - (leftLen + 1)) := by
                    unfold LocalValid at *
                    omega
                  have hrec :=
                    ih rightLen hrightLen_lt rightStart
                      (left - (leftLen + 1)) (right - (leftLen + 1))
                      hrightBound
                  have hrec' :
                      (shapeRange xs
                          (scanWindow xs start (blockSize' + 1) + 1)
                          (start + (blockSize' + 1) -
                            (scanWindow xs start (blockSize' + 1) + 1))).queryOffset?
                        (left - (leftLen + 1)) (right - (leftLen + 1)) =
                          if _hvalid :
                              LocalValid rightLen
                                (left - (leftLen + 1))
                                (right - (leftLen + 1)) then
                            some
                              (localScanOffset xs rightStart
                                (left - (leftLen + 1))
                                (right - (leftLen + 1)))
                          else
                            none := by
                    simpa [width, root, rightStart, rightLen] using hrec
                  rw [hrec', dif_pos hvalidRight]
                  simp
                  have hrightStart : rightStart = start + (leftLen + 1) := by
                    unfold rightStart leftLen
                    omega
                  have hchild_add := localScanOffset_add_start
                    (xs := xs) (start := rightStart) (blockSize := rightLen)
                    (left := left - (leftLen + 1))
                    (right := right - (leftLen + 1)) hvalidRight
                  have hfull_add := localScanOffset_add_start
                    (xs := xs) (start := start) (blockSize := width)
                    (left := left) (right := right) hvalid
                  have hstart_eq :
                      rightStart + (left - (leftLen + 1)) =
                        start + left := by
                    omega
                  have hlen_eq :
                      right - (leftLen + 1) - (left - (leftLen + 1)) =
                        right - left := by
                    omega
                  rw [hstart_eq, hlen_eq] at hchild_add
                  omega
                · rw [dif_neg hright]
                  have hrootArg :
                      LeftmostArgMin xs (start + left) (start + right) root := by
                    have hfullRoot :
                        LeftmostArgMin xs start (start + width) root := by
                      have hscanFull :=
                        scanWindow_leftmost xs start width (by omega) hbound
                      simpa [root] using hscanFull
                    have hroot_eq : root = start + leftLen := by
                      unfold leftLen
                      omega
                    exact leftmostArgMin_restrict_containing hfullRoot
                      (by omega) (by omega)
                      (by omega) (by omega)
                  have hscan0 :=
                    scanWindow_leftmost xs (start + left) (right - left)
                      (by omega) (by omega)
                  have hend :
                      start + left + (right - left) = start + right := by
                    omega
                  have hscan :
                      LeftmostArgMin xs (start + left) (start + right)
                        (scanWindow xs (start + left) (right - left)) := by
                    simpa [hend] using hscan0
                  have hscan_eq_root :
                      scanWindow xs (start + left) (right - left) = root :=
                    leftmostArgMin_unique xs (start + left) (start + right)
                      (scanWindow xs (start + left) (right - left)) root
                      hscan hrootArg
                  have hfull_add := localScanOffset_add_start
                    (xs := xs) (start := start) (blockSize := width)
                    (left := left) (right := right) hvalid
                  have hlocal : localScanOffset xs start left right = leftLen := by
                    unfold leftLen
                    omega
                  simp [hlocal]
            · have hinvalidShape :
                  Not
                    (left < right /\
                      right <=
                        (shapeRange xs start leftLen).size + 1 +
                          (shapeRange xs rightStart rightLen).size) := by
                intro hshapeValid
                apply hvalid
                unfold LocalValid
                omega
              rw [dif_neg hvalid]
              simp [shapeRange, CartesianShape.queryOffset?, width, root,
                leftLen, rightStart, rightLen, hinvalidShape])
      start left right hbound

/--
A certified fixed-size microtable. Only entries for shapes in
`shapeUniverse blockSize` are semantically relevant; the exactness field states
that looking up the concrete block signature returns the same local offset as
the direct scan.
-/
structure Microtable (blockSize : Nat) where
  queryOffset? : CartesianShape -> Nat -> Nat -> Option Nat
  exact :
    forall {xs : List Int} {start left right : Nat},
      start + blockSize <= xs.length ->
        queryOffset? (blockSignature xs start blockSize) left right =
          if _hvalid : LocalValid blockSize left right then
            some (localScanOffset xs start left right)
          else
            none

namespace Microtable

/-- The canonical certified microtable implemented by `CartesianShape.queryOffset?`. -/
def raw (blockSize : Nat) : Microtable blockSize where
  queryOffset? := CartesianShape.queryOffset?
  exact := by
    intro xs start left right hbound
    exact queryOffset?_blockSignature hbound

/-- Query a concrete block and lift the returned local offset to an index. -/
def queryIndex?
    {blockSize : Nat} (table : Microtable blockSize)
    (xs : List Int) (start left right : Nat) : Option Nat :=
  (table.queryOffset? (blockSignature xs start blockSize) left right).map
    fun offset => start + offset

theorem queryIndex?_eq
    {blockSize : Nat} (table : Microtable blockSize)
    {xs : List Int} {start left right : Nat}
    (hbound : start + blockSize <= xs.length) :
    table.queryIndex? xs start left right =
      if _hvalid : LocalValid blockSize left right then
        some (scanWindow xs (start + left) (right - left))
      else
        none := by
  unfold queryIndex?
  rw [table.exact hbound]
  by_cases hvalid : LocalValid blockSize left right
  · rw [dif_pos hvalid, dif_pos hvalid]
    simp [localScanOffset_add_start
      (xs := xs) (start := start) (blockSize := blockSize)
      (left := left) (right := right) hvalid]
  · rw [dif_neg hvalid, dif_neg hvalid]
    simp

theorem queryIndex?_leftmost
    {blockSize : Nat} (table : Microtable blockSize)
    {xs : List Int} {start left right : Nat}
    (hbound : start + blockSize <= xs.length)
    (hvalid : LocalValid blockSize left right) :
    exists idx,
      table.queryIndex? xs start left right = some idx /\
        LeftmostArgMin xs (start + left) (start + right) idx := by
  refine ⟨start + localScanOffset xs start left right, ?_, ?_⟩
  · unfold queryIndex?
    rw [table.exact hbound]
    rw [dif_pos hvalid]
    simp
  · exact localScanOffset_leftmost hbound hvalid

theorem queryIndex?_sound
    {blockSize : Nat} (table : Microtable blockSize)
    {xs : List Int} {start left right idx : Nat}
    (hbound : start + blockSize <= xs.length)
    (hquery : table.queryIndex? xs start left right = some idx) :
    LeftmostArgMin xs (start + left) (start + right) idx := by
  rw [queryIndex?_eq table hbound] at hquery
  by_cases hvalid : LocalValid blockSize left right
  · rw [dif_pos hvalid] at hquery
    simp at hquery
    have hscan :=
      localScanOffset_leftmost
        (xs := xs) (start := start) (blockSize := blockSize)
        (left := left) (right := right) hbound hvalid
    have hidx := localScanOffset_add_start
      (xs := xs) (start := start) (blockSize := blockSize)
      (left := left) (right := right) hvalid
    simpa [hidx, hquery] using hscan
  · rw [dif_neg hvalid] at hquery
    simp at hquery

theorem queryIndex?_complete
    {blockSize : Nat} (table : Microtable blockSize)
    {xs : List Int} {start left right idx : Nat}
    (hbound : start + blockSize <= xs.length)
    (hvalid : LocalValid blockSize left right)
    (harg : LeftmostArgMin xs (start + left) (start + right) idx) :
    table.queryIndex? xs start left right = some idx := by
  rw [queryIndex?_eq table hbound]
  rw [dif_pos hvalid]
  simp
  have hscan :=
    localScanOffset_leftmost
      (xs := xs) (start := start) (blockSize := blockSize)
      (left := left) (right := right) hbound hvalid
  have hidx := localScanOffset_add_start
    (xs := xs) (start := start) (blockSize := blockSize)
    (left := left) (right := right) hvalid
  have hsame :
      scanWindow xs (start + left) (right - left) = idx := by
    rw [← hidx]
    exact leftmostArgMin_unique xs (start + left) (start + right)
      (start + localScanOffset xs start left right) idx hscan harg
  exact hsame

theorem queryIndex?_invalid
    {blockSize : Nat} (table : Microtable blockSize)
    {xs : List Int} {start left right : Nat}
    (hbound : start + blockSize <= xs.length)
    (hbad : Not (LocalValid blockSize left right)) :
    table.queryIndex? xs start left right = none := by
  rw [queryIndex?_eq table hbound]
  simp [hbad]

/-- A certified microtable for the whole list gives a regular RMQ backend. -/
def backend (xs : List Int) (table : Microtable xs.length) :
    RMQBackend xs where
  State := Unit
  build := ()
  query _ left right := table.queryIndex? xs 0 left right
  sound := by
    intro left right idx hquery
    have hbound : 0 + xs.length <= xs.length := by
      simp
    simpa using queryIndex?_sound table hbound hquery
  complete := by
    intro left right idx harg
    have hbound : 0 + xs.length <= xs.length := by
      simp
    have hvalid : LocalValid xs.length left right := harg.valid
    have harg0 : LeftmostArgMin xs (0 + left) (0 + right) idx := by
      simpa using harg
    exact queryIndex?_complete table hbound hvalid harg0
  invalid_none := by
    intro left right hbad
    have hbound : 0 + xs.length <= xs.length := by
      simp
    exact queryIndex?_invalid table hbound hbad

/-- Whole-list RMQ backend backed by the canonical raw shape microtable. -/
def rawBackend (xs : List Int) : RMQBackend xs :=
  backend xs (raw xs.length)

end Microtable

example :
    (CartesianShape.node
      (CartesianShape.node CartesianShape.empty CartesianShape.empty)
      (CartesianShape.node
        CartesianShape.empty
        (CartesianShape.node CartesianShape.empty CartesianShape.empty))).queryOffset?
      2 4 = some 2 := by
  native_decide

example :
    (Microtable.raw 4).queryOffset?
      (blockSignature [4, 1, 1, 2] 0 4) 2 4 = some 2 := by
  native_decide

end Cartesian

end RMQ
