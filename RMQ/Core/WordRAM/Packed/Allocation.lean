import RMQ.Core.WordRAM.Packed.DensePacking
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerSpace
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerControllerProof

/-!
# Counted metadata and the concrete repacked allocation

Construction may inspect the Cartesian shape. The primitive query receives
only the resulting numeric cells. The complete old allocation, including its
header and final padding, is densely packed after a fixed metadata bank.

This module supplies a concrete builder and space theorem, not a whole-query
execution theorem. Every field of the metadata bank must be read by charged
instructions if consulted by that program.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian PackedCellProbe SuccinctSpace

/-- A constant floor addresses the fixed code even at n=0. The multiple gives
room for bounded polynomial intermediates; reachability still needs a proof. -/
def wordWidth (n : Nat) : Nat := 32 + 8 * packedReviewerCellWidth n

theorem wordWidth_pos (n : Nat) : 0 < wordWidth n := by unfold wordWidth; omega

theorem oldWidth_lt_wordWidth (n : Nat) : packedReviewerCellWidth n < wordWidth n := by
  unfold wordWidth
  omega

theorem wordWidth_le_log (n : Nat) : wordWidth n ≤ 192 * (Nat.log2 (n + 2) + 1) := by
  have h := packedReviewerCellWidth_le_log n
  unfold wordWidth
  omega

theorem wordWidth_littleO : LittleOLinear wordWidth :=
  (packedReviewerCellWidth_littleO.mul_left 8).const_add 32

theorem size_lt_wordCapacity (n : Nat) : n < 2 ^ wordWidth n := by
  have hsize := packedSize_le_reviewerBound n
  have hcap := packedReviewerCellBound_lt_two_pow_width n
  have hpow := Nat.pow_le_pow_right (by omega : 0 < 2)
    (Nat.le_of_lt (oldWidth_lt_wordWidth n))
  omega

/-- Field order is shared by the fixed program, not specialized code. -/
def metadataWordCount : Nat := 174

def regularDescriptor (n lc sc segment : Nat) : List Nat :=
  if segment = 20 then [0, 0, 0, 0]
  else if segment = 21 then
    [packedReviewerClosedFringeAddress n lc sc 0,
      packedReviewerFringeCount n * packedReviewerFringeWidth n,
      packedReviewerFringeWidth n, packedReviewerFringeCount n]
  else if segment = 22 then
    [packedReviewerClosedSelectChunkAddress n lc sc 0,
      packedReviewerSelectChunkCount n * packedReviewerSelectChunkWidth n,
      packedReviewerSelectChunkWidth n, packedReviewerSelectChunkCount n]
  else
    match packedSegmentSource? segment with
    | none => [0, 0, 0, 0]
    | some source =>
        let base := match source with
          | .bpCode | .finalRankBPCodeAlias => packedReviewerCellWidth n
          | _ => packedReviewerClosedStridedBitAddress n lc source 0
              (packedSourceStride n source)
        [base, packedReviewerSourceBitLength n lc sc source,
          packedSourceStride n source, packedReviewerLegacyWordCount n lc sc source]

theorem regularDescriptor_length (n lc sc segment : Nat) :
    (regularDescriptor n lc sc segment).length = 4 := by
  unfold regularDescriptor
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

def interiorComponents : List PackedReviewerInteriorComponentTag :=
  [.baseline, .minRel, .maxRel, .argOffset, .localOffset, .globalBlock,
    .localLevel, .globalLevel]

def interiorDescriptor (n lc sc : Nat) (component : PackedReviewerInteriorComponentTag) :
    List Nat :=
  let entryWidth := packedReviewerInteriorEntryWidth n component
  [packedReviewerInteriorComponentWordPrefix n component,
    packedReviewerInteriorComponentWordCount n component,
    packedReviewerCellWidth n + packedReviewerClosedInteriorOffset n lc sc +
      packedReviewerInteriorComponentBitPrefix n component,
    entryWidth, GenericSelect.selectCeilDiv entryWidth (packedBpCodeWordWidth n)]

@[simp] theorem interiorDescriptor_length (n lc sc : Nat)
    (component : PackedReviewerInteriorComponentTag) :
    (interiorDescriptor n lc sc component).length = 5 := rfl

def scalarMetadata (shape : CartesianShape) : List Nat :=
  let n := shape.size
  let lc := longCount shape
  let sc := packedReviewerSparseCount shape
  let oldCount := packedReviewerCellCount n lc sc
  let oldBits := oldCount * packedReviewerCellWidth n
  let layout := packedInteriorLayout n
  let offsets := packedInteriorOffsets n
  let ld := SuccinctClose.bpSparseLevelDomain layout.macroSize
  let gd := SuccinctClose.bpSparseLevelDomain layout.macroSampleCount
  [n, packedReviewerCellWidth n, oldCount, oldBits, lc, sc,
    wordWidth n, metadataWordCount + GenericSelect.selectCeilDiv oldBits (wordWidth n),
    packedSelectWordSize n, packedSelectSuperStride n, packedSelectLocalStride n,
    packedSelectLocalSlotsPerSuper n, packedSuperSlots n, packedSparseSlots n,
    packedLongFlagWordSize n, packedSparseWordSize n,
    packedBpCodeWordWidth n, layout.blockSize, packedFringeChunkBits n,
    layout.blocksPerSuper, layout.blockCount, layout.superSampleCount,
    layout.macroSize, layout.macroSampleCount, layout.levelCount, layout.globalLevelCount,
    layout.relativeWidth, layout.offsetWidth, layout.blockAddressWidth, ld, gd,
    SuccinctClose.bpSparseLevelWidth ld, SuccinctClose.bpSparseLevelWidth gd,
    offsets.baseline, offsets.minRel, offsets.maxRel, offsets.argOffset,
    offsets.localOffset, offsets.globalBlock, offsets.localLevel, offsets.globalLevel,
    packedInteriorComponentWords n]

@[simp] theorem scalarMetadata_length (shape : CartesianShape) :
    (scalarMetadata shape).length = 42 := rfl

/-- Preprocessing-only data; no proof fields or query-specific entries. -/
def metadata (shape : CartesianShape) : List Nat :=
  scalarMetadata shape ++
    ((List.range 23).map (regularDescriptor shape.size (longCount shape)
      (packedReviewerSparseCount shape))).flatten ++
    (interiorComponents.map (interiorDescriptor shape.size (longCount shape)
      (packedReviewerSparseCount shape))).flatten

theorem fixedMap_flatten_length {α : Type} (xs : List α) (f : α → List Nat)
    (count : Nat) (h : ∀ x ∈ xs, (f x).length = count) :
    (xs.map f).flatten.length = xs.length * count := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht : ∀ y ∈ xs, (f y).length = count := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih ht, Nat.succ_mul, Nat.add_comm]

theorem metadata_length (shape : CartesianShape) :
    (metadata shape).length = metadataWordCount := by
  have hregular := fixedMap_flatten_length (List.range 23)
    (regularDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape)) 4
    (by intro segment _; exact regularDescriptor_length ..)
  have hinterior := fixedMap_flatten_length interiorComponents
    (interiorDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape)) 5
    (by intro component _; exact interiorDescriptor_length ..)
  simp only [metadata, List.length_append, scalarMetadata_length, hregular, hinterior,
    List.length_range]
  rfl

def shapeMemory (shape : CartesianShape) : List Nat :=
  repackWords (metadata shape) (wordWidth shape.size) (packedReviewerMemory shape)

def buildMemory (xs : List Int) : List Nat :=
  shapeMemory (SuccinctClassic.cartesianShape xs)

def allocationRho (n : Nat) : Nat :=
  packedReviewerRho n + (metadataWordCount + 1) * wordWidth n

theorem allocationRho_littleO : LittleOLinear allocationRho :=
  packedReviewerRho_littleO.add (wordWidth_littleO.mul_left (metadataWordCount + 1))

theorem shapeMemory_capacity_le (shape : CartesianShape) :
    (shapeMemory shape).length * wordWidth shape.size ≤
      2 * shape.size + allocationRho shape.size := by
  have hnew := repackWords_capacity_le (metadata shape) (wordWidth shape.size)
    (packedReviewerCellWidth shape.size) (packedReviewerMemory shape)
    (by intro cell hc; exact packedReviewerMemory_cell_length shape hc)
  rw [metadata_length] at hnew
  have hold := packedReviewerMemory_length_mul_width_le shape
  unfold shapeMemory allocationRho
  omega

theorem buildMemory_capacity_le (xs : List Int) :
    (buildMemory xs).length * wordWidth xs.length ≤
      2 * xs.length + allocationRho xs.length := by
  have h := shapeMemory_capacity_le (SuccinctClassic.cartesianShape xs)
  have hsize : (SuccinctClassic.cartesianShape xs).size = xs.length := by
    exact packedReviewerCartesianShape_size xs
  simpa only [buildMemory, hsize] using h

/-- Any fixed program/scratch word budget can be included in the residual.
The final program must supply its actual encoded-word and register counts. -/
def allocationWithMachineRho (programWords scratchWords n : Nat) : Nat :=
  allocationRho n + (programWords + scratchWords) * wordWidth n

theorem allocationWithMachineRho_littleO (programWords scratchWords : Nat) :
    LittleOLinear (allocationWithMachineRho programWords scratchWords) :=
  allocationRho_littleO.add (wordWidth_littleO.mul_left (programWords + scratchWords))

theorem buildMemory_with_machine_capacity_le
    (xs : List Int) (programWords scratchWords : Nat) :
    ((buildMemory xs).length + programWords + scratchWords) * wordWidth xs.length ≤
      2 * xs.length + allocationWithMachineRho programWords scratchWords xs.length := by
  have h := buildMemory_capacity_le xs
  unfold allocationWithMachineRho
  simp only [Nat.add_mul]
  omega

end RMQ.SuccinctFinal.PackedWordRAM
