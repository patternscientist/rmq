import RMQ.Core.WordRAM.Bitvector.AllocationLayout
import RMQ.Core.WordRAM.Bitvector.Source
import RMQ.Core.WordRAM.Bitvector.AllocationFacts
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeTableFacts

/-! # Complete retained data, code and scratch capacity of the shared allocation

The raw input has coefficient one. Both select directories, the rank sample
tables, shared chunk tables, numerical metadata, dense padding, the literal
encoded words of all three programs, and their common scratch bank are counted.
This is a capacity theorem; source execution and finite-word safety are separate.
-/

namespace RMQ.PackedBitvector

open SuccinctSpace SuccinctRank GenericSelect
open SuccinctFinal.PackedWordRAM

theorem width_littleO : LittleOLinear Experiment.width :=
  (machineWordBits_littleO.mul_left 16).const_add 32

theorem rankSegments_bits_length (bits : List Bool) :
    ((Allocation.rankSegments bits).flatMap Experiment.segmentBits).length =
      (jacobsonRankData bits).auxPayload.length := by
  simp only [Allocation.rankSegments, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, segmentBits_payload,
    TwoLevelPayloadLiveStoredWordRankData.auxPayload,
    TwoLevelPayloadLiveStoredWordRankData.superPayload,
    TwoLevelPayloadLiveStoredWordRankData.blockPayload,
    FixedWidthRankSampleTables.payload, List.length_append]
  omega

theorem rankSegments_bits_length_eq_overhead (bits : List Bool) :
    ((Allocation.rankSegments bits).flatMap Experiment.segmentBits).length =
      jacobsonRankOverhead bits.length := by
  rw [rankSegments_bits_length]
  have h := (jacobsonRankData_profile bits).1
  simpa only [jacobsonRankOverhead, twoLevelRankOverhead] using h

def bodyRho (n : Nat) : Nat :=
  jacobsonClarkRankSelectOverhead n + SuccinctClose.bpFringeTableOverhead n +
    SuccinctClose.bpChunkSelectTableOverhead n

theorem bodyRho_littleO : LittleOLinear bodyRho :=
  (jacobsonClarkRankSelectOverhead_littleO.add
    SuccinctClose.bpFringeTableOverhead_littleO).add
      SuccinctClose.bpChunkSelectTableOverhead_littleO

theorem body_capacity (bits : List Bool) :
    (Allocation.body bits).length ≤ bits.length + bodyRho bits.length := by
  have hf := directorySegments_length_le_canonical (sparseExceptionSelectData bits false)
  have ht := directorySegments_length_le_canonical (sparseExceptionSelectData bits true)
  have hr := rankSegments_bits_length_eq_overhead bits
  have hfr := SuccinctClose.bpFringeChunkTable_payload_length
    (SuccinctClose.bpFringeChunkBits (2 * bits.length))
  have hse := SuccinctClose.bpChunkSelectTable_payload_length
    (SuccinctClose.bpFringeChunkBits (2 * bits.length)) false
  simp only [Allocation.body, Allocation.allSegments, Experiment.allSegments,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    segmentBits_payload, List.length_append]
  unfold bodyRho jacobsonClarkRankSelectOverhead SuccinctClose.bpFringeTableOverhead
    SuccinctClose.bpChunkSelectTableOverhead
  omega

def dataRho (n : Nat) : Nat := bodyRho n + 208 * Experiment.width n

theorem dataRho_littleO : LittleOLinear dataRho :=
  bodyRho_littleO.add (width_littleO.mul_left 208)

theorem data_capacity (bits : List Bool) :
    (Allocation.memory bits).length * Experiment.width bits.length ≤
      bits.length + dataRho bits.length := by
  have hb := body_capacity bits
  have hp := denseWords_capacity_le (Experiment.width bits.length) (Allocation.body bits)
  simp only [Allocation.memory, List.length_append, Allocation.header_length, Nat.add_mul]
  unfold dataRho
  omega

def encodedProgramWords (operation : Operation) : Nat :=
  ((program operation).map Instruction.encoding).flatten.length

/-- All three fixed programs are retained together in this capacity. -/
def retainedProgramWords : Nat :=
  encodedProgramWords .access + encodedProgramWords .rank + encodedProgramWords .select

def registerCount : Nat := 8271

/-- The finite register bank plus program counter, status tag and result cell. -/
def scratchWords : Nat := registerCount + 3

def completeRho (n : Nat) : Nat :=
  dataRho n +
    (((program .access).map Instruction.encoding).flatten.length +
      ((program .rank).map Instruction.encoding).flatten.length +
      ((program .select).map Instruction.encoding).flatten.length +
      (registerCount + 3)) * Experiment.width n

theorem completeRho_littleO : LittleOLinear completeRho :=
  dataRho_littleO.add (width_littleO.mul_left _)

private theorem capacity_add_three_programs (dataCount codeA codeR codeS scratch width n extra : Nat)
    (h : dataCount * width ≤ n + extra) :
    (dataCount + codeA + codeR + codeS + scratch) * width ≤
      n + (extra + (codeA + codeR + codeS + scratch) * width) := by
  simp only [Nat.add_mul]
  omega

theorem complete_capacity (bits : List Bool) :
    ((Allocation.memory bits).length +
      ((program .access).map Instruction.encoding).flatten.length +
      ((program .rank).map Instruction.encoding).flatten.length +
      ((program .select).map Instruction.encoding).flatten.length +
      (registerCount + 3)) * Experiment.width bits.length ≤
        bits.length + completeRho bits.length := by
  exact capacity_add_three_programs (Allocation.memory bits).length
    ((program .access).map Instruction.encoding).flatten.length
    ((program .rank).map Instruction.encoding).flatten.length
    ((program .select).map Instruction.encoding).flatten.length
    (registerCount + 3) (Experiment.width bits.length) bits.length (dataRho bits.length)
    (data_capacity bits)

end RMQ.PackedBitvector
