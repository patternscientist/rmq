import RMQ.Core.WordRAM.Construction.Spec.OpenCounts
import RMQ.Core.WordRAM.Construction.Spec.Dyck
import RMQ.Core.WordRAM.Construction.Spec.ArgMinSplit
import RMQ.Core.WordRAM.Construction.Spec.Positions
import RMQ.Core.WordRAM.Construction.Spec.Plan
import RMQ.Core.WordRAM.Construction.Spec.Envelope import Lean

/-! Independent exact-type consumers of the PRE-1 S1 machine-free specification
checkpoint (`RMQ/Core/WordRAM/Construction/Spec/*`). Every exit theorem is
restated at a fully written type that does not adapt to producer edits, and the
named plan segments are pinned to their reference expressions by `rfl`.
Kernel `decide` is used only on tiny pure reference lists and trees (rulings
Q9/Q9a); the four `#guard` lines evaluate the reference `buildMemory` and the
plan on the fixture lists `[]`, `[7]`, `[4, -3, -3, 8]` and `crossBlockInput`
with the Lean evaluator, as non-vacuity smoke checks (the equality itself is
the universal theorem). This file is separate from
`preprocessing_builder_check.lean`, whose line pins belong to the frozen
builder replay registry. -/

namespace PRE1SpecConsumer

open RMQ RMQ.Cartesian RMQ.Succinct RMQ.SuccinctSpace
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM
open RMQ.SuccinctFinal.PackedConstruction.Spec

/-! ## OpenCounts: BP law, length law, insertion law -/

theorem openCounts_equations : openCounts .empty = [] ∧
    ∀ (left right : CartesianShape), openCounts (.node left right) =
      (openCounts left ++ [0]).modifyHead (· + 1) ++ openCounts right :=
  ⟨rfl, fun _ _ => rfl⟩

theorem spec_bpCode_eq_openCounts_flatMap : ∀ (T : CartesianShape),
    T.bpCode = (openCounts T).flatMap (fun c => List.replicate c true ++ [false]) :=
  bpCode_eq_openCounts_flatMap

theorem spec_openCounts_length : ∀ (T : CartesianShape), (openCounts T).length = T.size :=
  openCounts_length

theorem insertPoint_equations :
    (∀ v : Int, StackCartesianTreeSpec.insertPoint .empty v = none) ∧
    ∀ (left : StackCartesianTree) (pivot : Int) (right : StackCartesianTree) (v : Int),
      StackCartesianTreeSpec.insertPoint (.node left pivot right) v =
        if v < pivot then some 0
        else (StackCartesianTreeSpec.insertPoint right v).map
          (fun k => left.shape.size + 1 + k) :=
  ⟨fun _ => rfl, fun _ _ _ _ => rfl⟩

theorem spec_openCounts_insertRight : ∀ (t : StackCartesianTree) (value : Int),
    openCounts (t.insertRight value).shape =
      match StackCartesianTreeSpec.insertPoint t value with
      | none => openCounts t.shape ++ [1]
      | some ld => (openCounts t.shape).modify ld (· + 1) ++ [0] :=
  StackCartesianTreeSpec.openCounts_insertRight

theorem spec_buildTree_append_singleton : ∀ (xs : List Int) (value : Int),
    StackCartesianTree.buildTree (xs ++ [value]) =
      (StackCartesianTree.buildTree xs).insertRight value :=
  StackCartesianTreeSpec.buildTree_append_singleton

theorem spec_bpCode_shape_eq_openCounts_buildTree : ∀ (xs : List Int),
    (Cartesian.shape xs).bpCode =
      (openCounts (StackCartesianTree.buildTree xs).shape).flatMap
        (fun c => List.replicate c true ++ [false]) :=
  StackCartesianTreeSpec.bpCode_shape_eq_openCounts_buildTree

/-- Leftmost tie and strict pop on tiny pure trees (kernel `decide`). -/
theorem openCounts_fixture_leftmost_tie :
    openCounts ([4, -3, -3, 8].foldl StackCartesianTree.insertRight .empty).shape =
      [2, 0, 1, 1] ∧
    ([4, -3, -3, 8].foldl StackCartesianTree.insertRight .empty).shape.bpCode =
      [true, true, false, false, true, false, true, false] ∧
    openCounts ([1, 1, 1, 1].foldl StackCartesianTree.insertRight .empty).shape =
      [1, 1, 1, 1] ∧
    StackCartesianTreeSpec.insertPoint (.node .empty 4 .empty) (-3) = some 0 ∧
    StackCartesianTreeSpec.insertPoint (.node .empty 1 .empty) 1 = none := by
  decide

/-- Open counts on the remaining plan fixture lists `[]`, `[7]` and
`crossBlockInput = [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]` (tiny pure lists, kernel
`decide`; the expected lists were derived by hand from the leftmost-minimum
Cartesian tree: inorder node `i` receives one opening bit for every node whose
subtree's leftmost node is `i`). -/
theorem openCounts_fixture_plan_lists :
    openCounts (([] : List Int).foldl StackCartesianTree.insertRight .empty).shape = [] ∧
    openCounts ([7].foldl StackCartesianTree.insertRight .empty).shape = [1] ∧
    openCounts ([9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9].foldl
      StackCartesianTree.insertRight .empty).shape = [5, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1, 1] := by
  decide

/-! ## Dyck prefix law and running excess -/

theorem spec_bpCode_closes_le_opens : ∀ (T : CartesianShape) (p : Nat),
    rankPrefix false T.bpCode p ≤ rankPrefix true T.bpCode p :=
  bpCode_closes_le_opens

theorem spec_bpExcessAt_add_closes : ∀ (T : CartesianShape) (p : Nat),
    SuccinctClose.bpExcessAt T p + rankPrefix false T.bpCode p = rankPrefix true T.bpCode p :=
  bpExcessAt_add_closes

theorem spec_bpExcessAt_succ_of_open : ∀ (T : CartesianShape) {p : Nat},
    T.bpCode[p]? = some true →
      SuccinctClose.bpExcessAt T (p + 1) = SuccinctClose.bpExcessAt T p + 1 :=
  @bpExcessAt_succ_of_open

theorem spec_bpExcessAt_succ_of_close : ∀ (T : CartesianShape) {p : Nat},
    T.bpCode[p]? = some false →
      1 ≤ SuccinctClose.bpExcessAt T p ∧
        SuccinctClose.bpExcessAt T (p + 1) = SuccinctClose.bpExcessAt T p - 1 :=
  @bpExcessAt_succ_of_close

theorem spec_bpCode_rank_full : ∀ (b : Bool) (T : CartesianShape),
    rankPrefix b T.bpCode T.bpCode.length = T.size :=
  bpCode_rank_full

/-! ## Leftmost block-argmin split -/

theorem spec_bpBetterArgMinBlock_assoc : ∀ (shape : CartesianShape) (blockSize a b c : Nat),
    SuccinctClose.bpBetterArgMinBlock shape blockSize
        (SuccinctClose.bpBetterArgMinBlock shape blockSize a b) c =
      SuccinctClose.bpBetterArgMinBlock shape blockSize a
        (SuccinctClose.bpBetterArgMinBlock shape blockSize b c) :=
  bpBetterArgMinBlock_assoc

theorem spec_bpRangeArgMinBlock_split : ∀ (shape : CartesianShape) (blockSize start a b : Nat),
    0 < b →
    SuccinctClose.bpRangeArgMinBlock shape blockSize start (a + b) =
      SuccinctClose.bpBetterArgMinBlock shape blockSize
        (SuccinctClose.bpRangeArgMinBlock shape blockSize start a)
        (SuccinctClose.bpRangeArgMinBlock shape blockSize (start + a) b) :=
  bpRangeArgMinBlock_split

theorem spec_bpRangeArgMinBlock_double : ∀ (shape : CartesianShape) (blockSize start c : Nat),
    SuccinctClose.bpRangeArgMinBlock shape blockSize start (c + c) =
      SuccinctClose.bpBetterArgMinBlock shape blockSize
        (SuccinctClose.bpRangeArgMinBlock shape blockSize start c)
        (SuccinctClose.bpRangeArgMinBlock shape blockSize (start + c) c) :=
  bpRangeArgMinBlock_double

theorem spec_bpRangeArgMinBlock_pow_succ : ∀ (shape : CartesianShape) (blockSize start l : Nat),
    SuccinctClose.bpRangeArgMinBlock shape blockSize start (2 ^ (l + 1)) =
      SuccinctClose.bpBetterArgMinBlock shape blockSize
        (SuccinctClose.bpRangeArgMinBlock shape blockSize start (2 ^ l))
        (SuccinctClose.bpRangeArgMinBlock shape blockSize (start + 2 ^ l) (2 ^ l)) :=
  bpRangeArgMinBlock_pow_succ

theorem spec_bpRangeArgMinBlock_pow_succ_mul :
    ∀ (shape : CartesianShape) (blockSize start l m : Nat),
    SuccinctClose.bpRangeArgMinBlock shape blockSize start (2 ^ (l + 1) * m) =
      SuccinctClose.bpBetterArgMinBlock shape blockSize
        (SuccinctClose.bpRangeArgMinBlock shape blockSize start (2 ^ l * m))
        (SuccinctClose.bpRangeArgMinBlock shape blockSize (start + 2 ^ l * m) (2 ^ l * m)) :=
  bpRangeArgMinBlock_pow_succ_mul

/-- Ties keep the left block, including the clamp case where both blocks start
past the BP code (tiny pure shape, kernel `decide`). -/
theorem argMin_fixture_tie_keeps_left :
    SuccinctClose.bpBetterArgMinBlock (.node .empty .empty) 1 5 7 = 5 := by
  decide

/-! ## One-pass positions and running ranks -/

theorem spec_selectFrom_scan : ∀ (target : Bool) (bits : List Bool) (base occurrence : Nat),
    selectFrom target bits base occurrence =
      (occurrencePositionsFrom target bits base)[occurrence]? :=
  selectFrom_scan

theorem spec_positionFill_spec : ∀ (bits : List Bool) (target : Bool) (arr : Nat → Nat) (k : Nat),
    positionFill target bits 0 0 arr k =
      if k < GenericSelect.occurrenceCount bits target then GenericSelect.position bits target k
      else arr k :=
  positionFill_spec

theorem spec_position_of_occurrenceCount_le : ∀ (bits : List Bool) (target : Bool) {k : Nat},
    GenericSelect.occurrenceCount bits target ≤ k → GenericSelect.position bits target k = bits.length :=
  @position_of_occurrenceCount_le

theorem spec_position_eq_fill_or_length : ∀ (bits : List Bool) (target : Bool) (arr : Nat → Nat)
    (k : Nat),
    GenericSelect.position bits target k =
      if k < GenericSelect.occurrenceCount bits target then positionFill target bits 0 0 arr k
      else bits.length :=
  position_eq_fill_or_length

theorem spec_rankPrefix_running : ∀ (target : Bool) (bits : List Bool) (c p : Nat),
    p ≤ bits.length →
      (runningRanksFrom target bits c)[p]? = some (c + rankPrefix target bits p) :=
  rankPrefix_running

theorem spec_rankSampleFill_spec : ∀ (target : Bool) {stride : Nat}, 0 < stride →
    ∀ (bits : List Bool) (arr : Nat → Nat) (w : Nat),
      rankSampleFill target stride bits 0 0 arr w =
        if w * stride ≤ bits.length then rankPrefix target bits (w * stride) else arr w :=
  @rankSampleFill_spec

theorem spec_rankSampleEntries_eq_fill : ∀ (target : Bool) (bits : List Bool) {wordSize : Nat},
    0 < wordSize → ∀ (arr : Nat → Nat),
      SuccinctRank.rankSampleEntries target bits wordSize =
        (List.range (bits.length / wordSize + 1)).map
          (rankSampleFill target wordSize bits 0 0 arr) :=
  @rankSampleEntries_eq_fill

theorem spec_canonicalSuperRankEntries_eq_fill : ∀ (target : Bool) (bits : List Bool)
    {wordSize blocksPerSuper : Nat}, 0 < wordSize → 0 < blocksPerSuper → ∀ (arr : Nat → Nat),
      SuccinctRank.canonicalSuperRankEntries target bits wordSize blocksPerSuper =
        (List.range (bits.length / wordSize / blocksPerSuper + 1)).map
          (rankSampleFill target (blocksPerSuper * wordSize) bits 0 0 arr) :=
  @canonicalSuperRankEntries_eq_fill

theorem spec_canonicalBlockRankEntries_eq_fill : ∀ (target : Bool) (bits : List Bool)
    {wordSize blocksPerSuper : Nat}, 0 < wordSize → 0 < blocksPerSuper →
    ∀ (arr arr' : Nat → Nat),
      SuccinctRank.canonicalBlockRankEntries target bits wordSize blocksPerSuper =
        (List.range (bits.length / wordSize + 1)).map
          (fun w => rankSampleFill target wordSize bits 0 0 arr w -
            rankSampleFill target (blocksPerSuper * wordSize) bits 0 0 arr' (w / blocksPerSuper)) :=
  @canonicalBlockRankEntries_eq_fill

/-- The scans against the reference on the BP code of `[4, -3, -3, 8]`
(tiny pure lists, kernel `decide`). -/
theorem positions_fixture :
    (List.range 4).map (positionFill false [true, true, false, false, true, false, true, false]
        0 0 (fun _ => 99)) = [2, 3, 5, 7] ∧
    (List.range 4).map (GenericSelect.position [true, true, false, false, true, false, true, false]
        false) = [2, 3, 5, 7] ∧
    SuccinctRank.rankSampleEntries false [true, true, false, false, true, false, true, false] 3 =
      [0, 1, 3] ∧
    (List.range 3).map (rankSampleFill false 3 [true, true, false, false, true, false, true, false]
        0 0 (fun _ => 99)) = [0, 1, 3] := by
  decide

/-! ## The emission plan of `buildMemory` -/

theorem spec_tableBits_def : ∀ (entries : List Nat) (width : Nat),
    tableBits entries width = flattenPayloadWords (entries.map (natToBitsLE width)) :=
  fun _ _ => rfl

theorem spec_table_payload : ∀ {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width),
    table.payload = flattenPayloadWords (entries.map (natToBitsLE width)) :=
  fun table => FixedWidthNatTable.payload_eq_tableBits table

theorem spec_accessSegments_def : ∀ (shape : CartesianShape),
    accessSegments shape =
      [ tableBits (SuccinctRank.canonicalSuperRankEntries false shape.bpCode
            (SuccinctRank.machineWordBits shape.bpCode.length)
            (SuccinctRank.machineWordBits shape.bpCode.length))
          (SuccinctRank.machineWordBits shape.bpCode.length),
        tableBits (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
            (SuccinctRank.machineWordBits shape.bpCode.length)
            (SuccinctRank.machineWordBits shape.bpCode.length))
          (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
            SuccinctRank.machineWordBits shape.bpCode.length)),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences
          (GenericSelect.superEntries shape.bpCode false)) (GenericSelect.superFieldWidth shape.bpCode),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices
          (GenericSelect.superEntries shape.bpCode false)) (GenericSelect.superFieldWidth shape.bpCode),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore
          (GenericSelect.superEntries shape.bpCode false)) (GenericSelect.superFieldWidth shape.bpCode),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets
          (GenericSelect.superEntries shape.bpCode false)) (GenericSelect.superFieldWidth shape.bpCode),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences
          (GenericSelect.localEntries shape.bpCode false)) (GenericSelect.localFieldWidth shape.bpCode),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices
          (GenericSelect.localEntries shape.bpCode false)) (GenericSelect.localFieldWidth shape.bpCode),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore
          (GenericSelect.localEntries shape.bpCode false)) (GenericSelect.localFieldWidth shape.bpCode),
        tableBits (GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets
          (GenericSelect.localEntries shape.bpCode false)) (GenericSelect.localFieldWidth shape.bpCode),
        tableBits (SuccinctRank.canonicalSuperRankEntries true
            (GenericSelect.longSuperFlagBits shape.bpCode false)
            (SuccinctRank.machineWordBits (GenericSelect.longSuperFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (GenericSelect.longSuperFlagBits shape.bpCode false).length),
        tableBits (SuccinctRank.canonicalBlockRankEntries true
            (GenericSelect.longSuperFlagBits shape.bpCode false)
            (SuccinctRank.machineWordBits (GenericSelect.longSuperFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (GenericSelect.longSuperFlagBits shape.bpCode false).length),
        GenericSelect.longSuperFlagBits shape.bpCode false,
        tableBits (GenericSelect.longSuperRelativeEntries shape.bpCode false)
          (GenericSelect.longSuperRelativeWidth shape.bpCode),
        tableBits (SuccinctRank.canonicalSuperRankEntries true
            (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
            (SuccinctRank.machineWordBits
              (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits
            (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length),
        tableBits (SuccinctRank.canonicalBlockRankEntries true
            (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
            (SuccinctRank.machineWordBits
              (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits
            (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length),
        GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false,
        tableBits (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false)
          (GenericSelect.sparseExceptionRelativeWidth shape.bpCode) ] :=
  fun _ => rfl

theorem spec_interiorSegments_def : ∀ (shape : CartesianShape),
    interiorSegments shape =
      [ tableBits (SuccinctClose.bpSuperblockBaselineEntries shape
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper
            (SuccinctClose.RelativeRmm.canonicalLayout shape).superSampleCount)
          ((SuccinctClose.RelativeRmm.canonicalLayout shape).superWidth shape),
        tableBits (SuccinctClose.bpBlockRelativeMinExcessEntries shape
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount)
          (SuccinctClose.RelativeRmm.canonicalLayout shape).relativeWidth,
        tableBits (SuccinctClose.bpBlockRelativeMaxExcessEntries shape
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount)
          (SuccinctClose.RelativeRmm.canonicalLayout shape).relativeWidth,
        tableBits (SuccinctClose.bpBlockArgMinLocalOffsetEntries shape
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount)
          (SuccinctClose.RelativeRmm.canonicalLayout shape).relativeWidth,
        tableBits (SuccinctClose.bpLocalSparseOffsetEntries shape
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount
            (SuccinctClose.RelativeRmm.canonicalLayout shape).levelCount)
          (SuccinctClose.RelativeRmm.canonicalLayout shape).offsetWidth,
        tableBits (SuccinctClose.bpGlobalSparseBlockEntries shape
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize
            (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount
            (SuccinctClose.RelativeRmm.canonicalLayout shape).globalLevelCount)
          (SuccinctClose.RelativeRmm.canonicalLayout shape).blockAddressWidth,
        tableBits (SuccinctClose.bpSparseLevelEntries
            (SuccinctClose.bpSparseLevelDomain (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize))
          (SuccinctClose.bpSparseLevelWidth
            (SuccinctClose.bpSparseLevelDomain (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize)),
        tableBits (SuccinctClose.bpSparseLevelEntries
            (SuccinctClose.bpSparseLevelDomain
              (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount))
          (SuccinctClose.bpSparseLevelWidth
            (SuccinctClose.bpSparseLevelDomain
              (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount)) ] :=
  fun _ => rfl

theorem spec_microtable_defs : ∀ (shape : CartesianShape),
    fringeSegment shape =
      tableBits (SuccinctClose.bpFringeChunkEntries (SuccinctClose.bpFringeChunkBits shape.bpCode.length))
        (SuccinctClose.bpFringeChunkEntryWidth (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) ∧
    selectChunkSegment shape =
      tableBits (SuccinctClose.bpChunkSelectEntries (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false)
        (SuccinctClose.bpChunkSelectEntryWidth (SuccinctClose.bpFringeChunkBits shape.bpCode.length)) :=
  fun _ => ⟨rfl, rfl⟩

theorem spec_payload_plan : ∀ (shape : CartesianShape),
    packedReviewerPayloadBits shape =
      shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++
        fringeSegment shape ++ selectChunkSegment shape :=
  canonicalReviewerPayload_eq_plan

theorem spec_metadataOf_def : ∀ (n lc sc : Nat),
    metadataOf n lc sc = scalarMetadataOf n lc sc ++
      ((List.range 23).map (regularDescriptor n lc sc)).flatten ++
      (interiorComponents.map (interiorDescriptor n lc sc)).flatten :=
  fun _ _ _ => rfl

theorem spec_metadata_eq_metadataOf : ∀ (shape : CartesianShape),
    metadata shape = metadataOf shape.size (longCount shape) (packedReviewerSparseCount shape) :=
  metadata_eq_metadataOf

theorem spec_metadataOf_eq : ∀ (shape : CartesianShape),
    metadata shape = metadataOf shape.size (longCount shape) (packedReviewerSparseCount shape) :=
  metadataOf_eq
theorem spec_metadataOf_length : ∀ (n lc sc : Nat), (metadataOf n lc sc).length = 174 :=
  metadataOf_length

theorem spec_buildMemory_eq_plan : ∀ (xs : List Int),
    buildMemory xs =
      metadataOf xs.length (longCount (SuccinctClassic.cartesianShape xs))
          (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) ++
        (List.range (GenericSelect.selectCeilDiv
            (packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
                (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
              packedReviewerCellWidth xs.length)
            (wordWidth xs.length))).map fun i =>
          bitsToNatLE (cellAt
            (natToBitsLE (packedReviewerCellWidth xs.length)
                (longCount (SuccinctClassic.cartesianShape xs)) ++
              (SuccinctClassic.cartesianShape xs).bpCode ++
              (accessSegments (SuccinctClassic.cartesianShape xs)).flatten ++
              (interiorSegments (SuccinctClassic.cartesianShape xs)).flatten ++
              fringeSegment (SuccinctClassic.cartesianShape xs) ++
              selectChunkSegment (SuccinctClassic.cartesianShape xs) ++
              List.replicate
                (packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
                    (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
                  packedReviewerCellWidth xs.length -
                  (packedReviewerCellWidth xs.length +
                    packedReviewerPayloadLength xs.length
                      (longCount (SuccinctClassic.cartesianShape xs))
                      (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)))) false ++
              List.replicate
                (GenericSelect.selectCeilDiv
                    (packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
                        (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
                      packedReviewerCellWidth xs.length)
                    (wordWidth xs.length) * wordWidth xs.length -
                  packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
                      (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
                    packedReviewerCellWidth xs.length) false)
            (wordWidth xs.length) i) :=
  buildMemory_eq_plan

theorem spec_buildMemory_plan_body_length : ∀ (xs : List Int),
    (natToBitsLE (packedReviewerCellWidth xs.length) (longCount (SuccinctClassic.cartesianShape xs)) ++
        (SuccinctClassic.cartesianShape xs).bpCode ++
        (accessSegments (SuccinctClassic.cartesianShape xs)).flatten ++
        (interiorSegments (SuccinctClassic.cartesianShape xs)).flatten ++
        fringeSegment (SuccinctClassic.cartesianShape xs) ++
        selectChunkSegment (SuccinctClassic.cartesianShape xs) ++
        List.replicate
          (packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
              (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
            packedReviewerCellWidth xs.length -
            (packedReviewerCellWidth xs.length +
              packedReviewerPayloadLength xs.length (longCount (SuccinctClassic.cartesianShape xs))
                (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)))) false).length =
      packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
          (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
        packedReviewerCellWidth xs.length :=
  buildMemory_plan_body_length

theorem spec_planPayload_length : ∀ (shape : CartesianShape),
    (shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++
        fringeSegment shape ++ selectChunkSegment shape).length =
      packedReviewerPayloadLength shape.size (longCount shape) (packedReviewerSparseCount shape) :=
  planPayload_length

/-! ## Literal all-size envelopes -/

theorem spec_tableBits_length : ∀ (entries : List Nat) (width : Nat),
    (tableBits entries width).length = entries.length * width :=
  tableBits_length

theorem spec_planPayload_length_add_two_le : ∀ (shape : CartesianShape),
    (shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++
        fringeSegment shape ++ selectChunkSegment shape).length + 2 ≤
      400000 * (shape.size + 1) :=
  planPayload_length_add_two_le

theorem spec_accessEntryCounts_le : ∀ (shape : CartesianShape),
    (SuccinctRank.canonicalSuperRankEntries false shape.bpCode
        (SuccinctRank.machineWordBits shape.bpCode.length)
        (SuccinctRank.machineWordBits shape.bpCode.length)).length ≤ 400000 * (shape.size + 1) ∧
    (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
        (SuccinctRank.machineWordBits shape.bpCode.length)
        (SuccinctRank.machineWordBits shape.bpCode.length)).length ≤ 400000 * (shape.size + 1) ∧
    (GenericSelect.superEntries shape.bpCode false).length ≤ 400000 * (shape.size + 1) ∧
    (GenericSelect.localEntries shape.bpCode false).length ≤ 400000 * (shape.size + 1) ∧
    (SuccinctRank.canonicalSuperRankEntries true (GenericSelect.longSuperFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (GenericSelect.longSuperFlagBits shape.bpCode false).length)
        1).length ≤ 400000 * (shape.size + 1) ∧
    (SuccinctRank.canonicalBlockRankEntries true (GenericSelect.longSuperFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (GenericSelect.longSuperFlagBits shape.bpCode false).length)
        1).length ≤ 400000 * (shape.size + 1) ∧
    (GenericSelect.longSuperFlagBits shape.bpCode false).length ≤ 400000 * (shape.size + 1) ∧
    (GenericSelect.longSuperRelativeEntries shape.bpCode false).length ≤ 400000 * (shape.size + 1) ∧
    (SuccinctRank.canonicalSuperRankEntries true
        (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits
          (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length)
        1).length ≤ 400000 * (shape.size + 1) ∧
    (SuccinctRank.canonicalBlockRankEntries true
        (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits
          (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length)
        1).length ≤ 400000 * (shape.size + 1) ∧
    (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false).length ≤
      400000 * (shape.size + 1) ∧
    (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length ≤
      400000 * (shape.size + 1) :=
  accessEntryCounts_le

theorem spec_selectSlotCounts_le : ∀ (shape : CartesianShape),
    GenericSelect.superSlotCount shape.bpCode false ≤ 400000 * (shape.size + 1) ∧
      GenericSelect.localSlotCount shape.bpCode false ≤ 400000 * (shape.size + 1) :=
  selectSlotCounts_le

theorem spec_interiorEntryCounts_le : ∀ (shape : CartesianShape),
    (SuccinctClose.bpSuperblockBaselineEntries shape
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper
        (SuccinctClose.RelativeRmm.canonicalLayout shape).superSampleCount).length ≤
      400000 * (shape.size + 1) ∧
    (SuccinctClose.bpBlockRelativeMinExcessEntries shape
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount).length ≤
      400000 * (shape.size + 1) ∧
    (SuccinctClose.bpBlockRelativeMaxExcessEntries shape
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blocksPerSuper
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount).length ≤
      400000 * (shape.size + 1) ∧
    (SuccinctClose.bpBlockArgMinLocalOffsetEntries shape
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount).length ≤
      400000 * (shape.size + 1) ∧
    (SuccinctClose.bpLocalSparseOffsetEntries shape
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount
        (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount
        (SuccinctClose.RelativeRmm.canonicalLayout shape).levelCount).length ≤
      400000 * (shape.size + 1) ∧
    (SuccinctClose.bpGlobalSparseBlockEntries shape
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount
        (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize
        (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount
        (SuccinctClose.RelativeRmm.canonicalLayout shape).globalLevelCount).length ≤
      400000 * (shape.size + 1) ∧
    (SuccinctClose.bpSparseLevelEntries
        (SuccinctClose.bpSparseLevelDomain
          (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSize)).length ≤
      400000 * (shape.size + 1) ∧
    (SuccinctClose.bpSparseLevelEntries
        (SuccinctClose.bpSparseLevelDomain
          (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount)).length ≤
      400000 * (shape.size + 1) :=
  interiorEntryCounts_le

theorem spec_microtableRowCounts_le : ∀ (shape : CartesianShape),
    (SuccinctClose.bpFringeChunkEntries
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length)).length ≤ 400000 * (shape.size + 1) ∧
      (SuccinctClose.bpChunkSelectEntries
        (SuccinctClose.bpFringeChunkBits shape.bpCode.length) false).length ≤
        400000 * (shape.size + 1) :=
  microtableRowCounts_le

theorem spec_oldBits_le : ∀ (n lc sc : Nat),
    packedReviewerCellCount n lc sc * packedReviewerCellWidth n ≤
      packedReviewerPayloadLength n lc sc + 2 * packedReviewerCellWidth n :=
  oldBits_le

theorem spec_wordWidth_le_linear : ∀ (n : Nat), wordWidth n ≤ 192 * n + 576 :=
  wordWidth_le_linear

theorem spec_planBuffer_le : ∀ (xs : List Int),
    packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
        (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
        packedReviewerCellWidth xs.length ≤ 400384 * xs.length + 401150 ∧
      GenericSelect.selectCeilDiv
          (packedReviewerCellCount xs.length (longCount (SuccinctClassic.cartesianShape xs))
            (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs)) *
            packedReviewerCellWidth xs.length) (wordWidth xs.length) * wordWidth xs.length ≤
        400576 * xs.length + 401726 :=
  planBuffer_le

theorem spec_buildMemory_length_le : ∀ (xs : List Int),
    (buildMemory xs).length ≤ 400576 * xs.length + 401900 :=
  buildMemory_length_le

theorem spec_layout_counts : ∀ (shape : CartesianShape),
    (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount ≤ shape.size ∧
    (SuccinctClose.RelativeRmm.canonicalLayout shape).superSampleCount ≤ shape.size + 1 ∧
    (SuccinctClose.RelativeRmm.canonicalLayout shape).macroSampleCount ≤ shape.size + 1 ∧
    (SuccinctClose.RelativeRmm.canonicalLayout shape).globalLevelCount ≤ shape.size + 2 ∧
    (SuccinctClose.RelativeRmm.canonicalLayout shape).levelCount *
        (SuccinctClose.RelativeRmm.canonicalLayout shape).blockCount ≤ 3 * shape.size :=
  fun shape => ⟨canonicalLayout_blockCount_le shape, canonicalLayout_superSampleCount_le shape,
    canonicalLayout_macroSampleCount_le shape, canonicalLayout_globalLevelCount_le shape,
    canonicalLayout_levelCount_mul_blockCount_le shape⟩

theorem spec_microtable_scans_le : ∀ (n : Nat),
    SuccinctClose.bpFringeChunkRowCount (SuccinctClose.bpFringeChunkBits (2 * n)) *
        (SuccinctClose.bpFringeChunkBits (2 * n) + 1) ≤ 256 * (n + 1) ∧
      SuccinctClose.bpChunkSelectRowCount (SuccinctClose.bpFringeChunkBits (2 * n)) *
        (SuccinctClose.bpFringeChunkBits (2 * n) + 1) ≤ 64 * (n + 1) :=
  fun n => ⟨fringeRows_mul_scan_le n, selectRows_mul_scan_le n⟩

theorem spec_log2_rounds_le : ∀ (x : Nat), Nat.log2 x + 1 ≤ x + 1 := log2_rounds_le

/-- The plan right-hand side, evaluated only in the `#guard` smoke checks. -/
def planWordsCheck (xs : List Int) : List Nat :=
  let shape := SuccinctClassic.cartesianShape xs
  let n := xs.length
  let lc := longCount shape
  let sc := packedReviewerSparseCount shape
  let oldW := packedReviewerCellWidth n
  let W := wordWidth n
  let oldBits := packedReviewerCellCount n lc sc * oldW
  let count := GenericSelect.selectCeilDiv oldBits W
  let body := natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++
    (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++
    List.replicate (oldBits - (oldW + packedReviewerPayloadLength n lc sc)) false
  metadataOf n lc sc ++ (List.range count).map fun i =>
    bitsToNatLE (cellAt (body ++ List.replicate (count * W - oldBits) false) W i)

#guard buildMemory [] == planWordsCheck []
#guard buildMemory [7] == planWordsCheck [7]
#guard buildMemory [4, -3, -3, 8] == planWordsCheck [4, -3, -3, 8]
#guard buildMemory [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9] ==
  planWordsCheck [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

/-! ## Axiom inventory (every new S1 declaration) -/

#print axioms openCounts
#print axioms bpUnit
#print axioms openCounts_empty
#print axioms openCounts_node
#print axioms openCounts_length
#print axioms modifyHead_succ_append_ne_nil
#print axioms flatMap_bpUnit_modifyHead_succ
#print axioms bpCode_eq_openCounts_flatMap
#print axioms openCounts_ne_nil_of_node
#print axioms modify_append_length
#print axioms StackCartesianTreeSpec.insertPoint
#print axioms StackCartesianTreeSpec.openCounts_insertRight
#print axioms StackCartesianTreeSpec.buildTreeAux_append_singleton
#print axioms StackCartesianTreeSpec.buildTree_append_singleton
#print axioms StackCartesianTreeSpec.buildTree_nil
#print axioms StackCartesianTreeSpec.shape_eq_buildTree_shape
#print axioms StackCartesianTreeSpec.bpCode_shape_eq_openCounts_buildTree
#print axioms rankPrefix_succ_getElem?
#print axioms bpCode_rank_full
#print axioms bpCode_closes_le_opens
#print axioms bpExcessAt_add_closes
#print axioms bpExcessAt_succ_of_open
#print axioms bpExcessAt_succ_of_close
#print axioms bpExcessAt_of_length_le
#print axioms bpBetterArgMinBlock_self
#print axioms bpBetterArgMinBlock_assoc
#print axioms bpRangeArgMinBlockFrom_better
#print axioms bpRangeArgMinBlockFrom_add
#print axioms bpRangeArgMinBlock_split
#print axioms bpRangeArgMinBlock_double
#print axioms bpRangeArgMinBlock_pow_succ
#print axioms bpRangeArgMinBlock_pow_succ_mul
#print axioms bpRangeArgMinBlock_one
#print axioms occurrencePositionsFrom
#print axioms selectFrom_scan
#print axioms occurrencePositionsFrom_length
#print axioms position_eq_scan
#print axioms positionFill
#print axioms positionFill_general
#print axioms positionFill_spec
#print axioms position_of_occurrenceCount_le
#print axioms position_eq_fill_or_length
#print axioms runningRanksFrom
#print axioms runningRanksFrom_length
#print axioms rankPrefix_running
#print axioms rankSampleFill
#print axioms sample_slot_iff
#print axioms update_slot_apply
#print axioms rankSampleFill_general
#print axioms rankSampleFill_spec
#print axioms mul_le_of_le_div'
#print axioms rankSampleEntries_eq_fill
#print axioms canonicalSuperRankEntries_eq_fill
#print axioms canonicalBlockRankEntries_eq_fill
#print axioms tableBits
#print axioms natToBitsLE_length_bitsToNatLE
#print axioms FixedWidthNatTable.payload_eq_tableBits
#print axioms accessSegments
#print axioms interiorSegments
#print axioms fringeSegment
#print axioms selectChunkSegment
#print axioms accessSegments_length
#print axioms interiorSegments_length
#print axioms liveAccessPayload_eq_segments
#print axioms interiorPayload_eq_segments
#print axioms canonicalReviewerPayload_eq_plan
#print axioms scalarMetadataOf
#print axioms metadataOf
#print axioms metadata_eq_metadataOf
#print axioms metadataOf_eq
#print axioms metadataOf_length
#print axioms oldBitsPlan
#print axioms planPayload_length
#print axioms packedReviewerPaddedBits_eq_plan
#print axioms oldBitsPlan_length
#print axioms shapeMemory_eq_plan
#print axioms shapeMemory_eq_plan_of_size
#print axioms buildMemory_eq_plan
#print axioms oldBitsPlan_length_of_size
#print axioms buildMemory_plan_body_length
#print axioms flattenPayloadWords_map_natToBitsLE_length
#print axioms tableBits_length
#print axioms entries_length_le_tableBits
#print axioms length_le_flatten_of_mem
#print axioms planPayload_length_add_two_le
#print axioms accessSegments_length_add_two_le
#print axioms interiorSegments_length_add_two_le
#print axioms microtableSegments_length_add_two_le
#print axioms entries_le_of_mem_segments
#print axioms superFieldWidth_pos
#print axioms sparseExceptionRelativeWidth_pos
#print axioms accessEntryCounts_le
#print axioms selectSlotCounts_le
#print axioms interiorEntryCounts_le
#print axioms microtableRowCounts_le
#print axioms oldBits_le
#print axioms denseBits_le
#print axioms wordWidth_le_linear
#print axioms planBuffer_le
#print axioms buildMemory_length_le
#print axioms canonicalLayout_blockCount_le
#print axioms canonicalLayout_superSampleCount_le
#print axioms canonicalLayout_macroSampleCount_le
#print axioms canonicalLayout_globalLevelCount_le
#print axioms canonicalLayout_levelCount_mul_blockCount_le
#print axioms fringeRows_mul_scan_le
#print axioms selectRows_mul_scan_le
#print axioms log2_rounds_le
#print axioms openCounts_fixture_leftmost_tie
#print axioms openCounts_fixture_plan_lists
#print axioms argMin_fixture_tie_keeps_left
#print axioms positions_fixture

/-! ## Verdict marker (repair PRE-1-R2 of audit PRE-1-A2 P2-1)

The exit code is the verdict. The marker is printed if and only if the whole
file elaborates with no error-severity message (this consumer has no witness or
guard condition; its `#guard` lines are commands of the file); otherwise nothing
is printed and no diagnostic is added. Lean 4.22 resets the command state's
message log before every command (`Lean.Language.Lean.process.doElab` sets
`messages := .empty`), so this command cannot read an earlier command's errors
from its own state. For the whole-file condition it elaborates the file a second
time in this process from the source text of its own input context, with only
this command blanked (line breaks kept), through `Lean.Parser.parseHeader`,
`Lean.Elab.processHeader` and `Lean.Elab.IO.processCommands`, which collects the
message logs of every command snapshot, and requires `MessageLog.hasErrors` to
be false for the header and for those messages: the predicate by which the
frontend decides the exit code. An error in any command kind (a declaration, an
anonymous example, a `#guard` or `run_cmd` check, a missing declaration after a
maximum-recursion-depth failure, or a command after this one) therefore
suppresses the marker. -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  -- (1) Whole file: elaborate this file again in this process from its own
  -- source text, with only this command blanked (line breaks kept), and read
  -- the message log of the header and of every command.
  let context ← read
  let source := context.fileMap.source
  let scope ← getScope
  let markerStop := (Parser.parseCommand (Parser.mkInputContext source context.fileName)
    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls } { pos := context.cmdPos } {}).2.1.pos
  let blank := (source.extract context.cmdPos markerStop).map
    fun c => if c == '\n' || c == '\r' then c else ' '
  let input := Parser.mkInputContext
    (source.extract 0 context.cmdPos ++ blank ++ source.extract markerStop source.endPos)
    context.fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader input
  let options := Elab.async.setIfNotSet (internal.cmdlineSnapshots.setIfNotSet {} true) true
  let (headerEnv, headerMessages) ← processHeader header options headerMessages input
    (trustLevel := (← getEnv).header.trustLevel) (leakEnv := true)
    (mainModule := (← getEnv).mainModule)
  let whole ← IO.processCommands input parserState (Command.mkState headerEnv {} options)
  let fileClean := !headerMessages.hasErrors && !whole.commandState.messages.hasErrors
  if fileClean then IO.println "PRE1-SPEC-TYPED-CONSUMERS PASS"
end PRE1SpecConsumer
