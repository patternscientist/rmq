import RMQ.Core.WordRAM.Packed.QueryReference
import RMQ.Core.WordRAM.Packed.InteriorCandidateProof

/-! # Canonical primitive query correctness

All source interfaces are discharged here on the same counted numeric memory.
The arithmetic-safety certificate is a separate conjunct of the final capstone.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

theorem interiorRangeBlock_lcaWrites (reader : Block) (hw : ReaderWrites reader) :
    (interiorRangeBlock reader).WritesOnly LCAInteriorWrites :=
  Block.WritesOnly.mono _ (interiorRangeBlock_writes reader hw) (by
    intro r h
    unfold InteriorRangeWrites InteriorLocalTwoWrites InteriorGlobalTwoWrites
      InteriorLocalSpanWrites InteriorGlobalSpanWrites InteriorMinWrites at h
    unfold LCAInteriorWrites
    omega)

theorem interiorRangeBlock_correct (shape : CartesianShape) :
    InteriorCandidateCorrect shape (shapeMemory shape) (interiorRangeBlock logicalReadBlock) :=
  interiorRangeBlock_source shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly

theorem lcaCloseBlock_writes (reader : Block) (hw : ReaderWrites reader) :
    (lcaCloseBlock reader).WritesOnly LCACloseWrites :=
  lcaCloseProgram_writes reader (interiorRangeBlock reader) hw
    (interiorRangeBlock_lcaWrites reader hw)

theorem lcaCloseBlock_correct (shape : CartesianShape) :
    LCACorrect shape (shapeMemory shape) (lcaCloseBlock logicalReadBlock) :=
  lcaCloseProgram_source shape (shapeMemory shape) logicalReadBlock (interiorRangeBlock logicalReadBlock)
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly
    (interiorRangeBlock_correct shape) (interiorRangeBlock_lcaWrites logicalReadBlock logicalReadBlock_writesOnly)

theorem queryRun_result (xs : List Int) (left right : Nat) :
    (queryRun (buildMemory xs) xs.length left right).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  queryRun_result_with_lca xs (lcaCloseBlock_correct (SuccinctClassic.cartesianShape xs))
    (lcaCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly) left right

theorem queryRun_halts (xs : List Int) (left right : Nat) :
    (queryRun (buildMemory xs) xs.length left right).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  queryRun_halts_with_lca xs (lcaCloseBlock_correct (SuccinctClassic.cartesianShape xs))
    (lcaCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly) left right

theorem queryNat_reference (xs : List Int) (left right : Nat) :
    queryNat (buildMemory xs) xs.length left right =
      (SuccinctClassic.queryTraceResult xs left right).value :=
  queryNat_reference_with_lca xs (lcaCloseBlock_correct (SuccinctClassic.cartesianShape xs))
    (lcaCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly) left right

theorem queryNat_exact (xs : List Int) (left right : Nat) :
    queryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  queryNat_exact_with_lca xs (lcaCloseBlock_correct (SuccinctClassic.cartesianShape xs))
    (lcaCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly) left right

theorem queryNat_leftmost (xs : List Int) (left right index : Nat)
    (hresult : queryNat (buildMemory xs) xs.length left right = some index) :
    LeftmostArgMin xs left right index :=
  queryNat_leftmost_with_lca xs (lcaCloseBlock_correct (SuccinctClassic.cartesianShape xs))
    (lcaCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly) left right index hresult

theorem queryRun_valid (shape : CartesianShape) (left right : Nat)
    (hlt : left < right) (hle : right ≤ shape.size) :
    let expected := packedWholeQueryRun (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size left right
    let actual := queryRun (shapeMemory shape) shape.size left right
    actual.result = some (optionNatPacket expected.value) ∧
      actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
        logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      actual.steps ≤ queryBudget ∧ ReadOnlyTrace expected.trace :=
  queryRun_valid_with_lca shape (lcaCloseBlock_correct shape)
    (lcaCloseBlock_writes logicalReadBlock logicalReadBlock_writesOnly) left right hlt hle

end RMQ.SuccinctFinal.PackedWordRAM
