import RMQ.Core.WordRAM.Construction.Proof.Flow

/-! # PRE-1 builder proofs: pointer flow of the builder source (stage S8)

Outside the builder firewall. The pointer flow of every phase of
`builderSource leaf` from the empty list, proved per phase by structural
simplification of `ptrFlow` over the phase's definitions (the 108 metadata bank
steps are each decided on their own one- to six-action lists; the chains and the
composites are proved by rewriting with the phase lemmas).
`flow_builderSource_key` and `flow_builderSource_word` give the whole source:
defined, ending with registers 10, 3, 224, 108, 119, 220 and the array bases.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

theorem ptrFlow_seq (a b : Block) (I : List Nat) :
    ptrFlow (.seq a b) I = (ptrFlow a I).bind (ptrFlow b) := rfl

/-! ## Header, constants and geometry -/

theorem flow_header : ptrFlow (.action (.load 1 0)) [] = some [] := by decide

set_option maxHeartbeats 4000000 in
theorem flow_constants : ptrFlow (constantsBlock) [] = some [] := by
  simp [acts, constantsBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_geoStep : ∀ k, ptrFlow (geoStepBlock k) [] = some [] := by
  intro k
  unfold geoStepBlock
  split <;> simp [acts, wordBitsBlock, log2Block, log2Body, minActs, ptrFlow, ptrStep]

theorem flow_geoChain : ∀ k, ptrFlow (geoChain k) [] = some [] := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [geoChain, ptrFlow_seq, ih, Option.bind_some, flow_geoStep]

set_option maxHeartbeats 4000000 in
theorem flow_interiorGeometry : ptrFlow (interiorGeometryBlock) [] = some [] := by
  simp [acts, interiorGeometryBlock, levelWidthBlock, log2Block, log2Body, ptrFlow, ptrStep]

theorem flow_geometry : ptrFlow geometryPrelude [] = some [] := by
  rw [geometryPrelude, ptrFlow_seq, flow_interiorGeometry, Option.bind_some, flow_geoChain]

/-! ## Arrays and the stack pass -/

set_option maxHeartbeats 4000000 in
theorem flow_arrays : ptrFlow (arraysBlock) [] = some [136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, arraysBlock, emitBit, reserveArray, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_stackArrays : ptrFlow (stackArraysBlock) [136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBit, reserveArray, stackArraysBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_stackPass_key : ptrFlow (stackPassBlock keyLeaf) [102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, forSlots, keyLeaf, linkBlock, popBodyBlock, popGuardBlock, pushBlock, stackPassBlock, stackStepBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_stackPass_word : ptrFlow (stackPassBlock wordLeaf) [102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, forSlots, linkBlock, popBodyBlock, popGuardBlock, pushBlock, stackPassBlock, stackStepBlock, wordLeaf, ptrFlow, ptrStep]

/-! ## Bit buffer -/

set_option maxHeartbeats 4000000 in
theorem flow_headerReserve : ptrFlow (headerReserveBlock) [102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBit, headerReserveBlock, reserveArray, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_bpEmit : ptrFlow (bpEmitBlock) [119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, bpEmitBlock, bpUnitBlock, emitBit, forSlots, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_0 : ptrFlow (posPassBlock) [119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, forSlots, posPassBlock, posStepBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_1 : ptrFlow (longFlagsBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, forSlots, longFlagBlock, longFlagsBlock, maxActs, minActs, monusActs, posActs, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_2 : ptrFlow (sparseFlagsBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, forSlots, maxActs, minActs, monusActs, posActs, sparseFlagBlock, sparseFlagsBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_3 : ptrFlow (emitTable rRSUP rWS rankSuperEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, rankSuperEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_4 : ptrFlow (emitTable rRBLK rRBW rankBlockEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, rankBlockEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_5 : ptrFlow (emitTable rSUP rWS superOccEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, superOccEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_6 : ptrFlow (emitTable rSUP rWS superWordEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, minActs, posActs, superWordEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_7 : ptrFlow (emitTable rSUP rWS superFlagEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, superFlagEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_8 : ptrFlow (emitTable rSUP rWS superOffsetEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, minActs, posActs, superOffsetEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_9 : ptrFlow (emitTable rLOC rLW localOccEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localOccEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_10 : ptrFlow (emitTable rLOC rLW localWordEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localWordEntryBlock, minActs, posActs, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_11 : ptrFlow (emitTable rLOC rLW localFlagEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localFlagEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_12 : ptrFlow (emitTable rLOC rLW localOffsetEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localOffsetEntryBlock, minActs, posActs, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_13 : ptrFlow (emitTable rLFR rLFW (flagRankEntryBlock rLFCB rLFW)) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagRankEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_14 : ptrFlow (emitTable rLFR rLFW zeroEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, zeroEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_15 : ptrFlow (emitTable rSUP rONE (flagEntryBlock rLFB)) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_16 : ptrFlow (forSlots rK rKGO rSUP longRelativeBodyBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, longRelativeBodyBlock, maxActs, minActs, monusActs, posActs, relativeOffsetEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_17 : ptrFlow (emitTable rSFR rSFW (flagRankEntryBlock rSFCB rSFW)) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagRankEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_18 : ptrFlow (emitTable rSFR rSFW zeroEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, zeroEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_19 : ptrFlow (emitTable rSP rONE (flagEntryBlock rSFB)) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_access_20 : ptrFlow (forSlots rG rGGO rLOC sparseRelativeBodyBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, maxActs, minActs, monusActs, posActs, relativeOffsetEntryBlock, sparseRelativeBodyBlock, ptrFlow, ptrStep]

theorem flow_accessHalf : ptrFlow accessHalfBlock [119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  rw [accessHalfBlock, ptrFlow_seq, flow_access_0, Option.bind_some, ptrFlow_seq, flow_access_1, Option.bind_some, ptrFlow_seq, flow_access_2, Option.bind_some, ptrFlow_seq, flow_access_3, Option.bind_some, ptrFlow_seq, flow_access_4, Option.bind_some, ptrFlow_seq, flow_access_5, Option.bind_some, ptrFlow_seq, flow_access_6, Option.bind_some, ptrFlow_seq, flow_access_7, Option.bind_some, ptrFlow_seq, flow_access_8, Option.bind_some, ptrFlow_seq, flow_access_9, Option.bind_some, ptrFlow_seq, flow_access_10, Option.bind_some, ptrFlow_seq, flow_access_11, Option.bind_some, ptrFlow_seq, flow_access_12, Option.bind_some, ptrFlow_seq, flow_access_13, Option.bind_some, ptrFlow_seq, flow_access_14, Option.bind_some, ptrFlow_seq, flow_access_15, Option.bind_some, ptrFlow_seq, flow_access_16, Option.bind_some, ptrFlow_seq, flow_access_17, Option.bind_some, ptrFlow_seq, flow_access_18, Option.bind_some, ptrFlow_seq, flow_access_19, Option.bind_some, flow_access_20]

set_option maxHeartbeats 4000000 in
theorem flow_interior_0 : ptrFlow (blockStatsBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, blockBodyBlock, blockStatsBlock, forSlots, maxActs, minActs, sampleBodyBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_interior_1 : ptrFlow (localMemoBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, betterActs, forSlots, localMemoBlock, memoCellBlock, memoLevelsBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_interior_2 : ptrFlow (globalMemoBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, betterActs, forSlots, globalMemoBlock, macroScanBlock, memoCellBlock, memoLevelsBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_interior_3 : ptrFlow (summaryTablesBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, argOffsetEntryBlock, baselineEntryBlock, emitBits, emitBitsBody, emitTable, emitTableBody, relativeEntryBlock, summaryTablesBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_interior_4 : ptrFlow (emitTable rLSCNT rOW localEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_interior_5 : ptrFlow (emitTable rGSCNT rBAW globalEntryBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, globalEntryBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_interior_6 : ptrFlow (levelTableBlock rLDOM rLWID) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, levelEntryBlock, levelTableBlock, log2Block, log2Body, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_interior_7 : ptrFlow (levelTableBlock rGDOM rGWID) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, levelEntryBlock, levelTableBlock, log2Block, log2Body, ptrFlow, ptrStep]

theorem flow_interiorClose : ptrFlow interiorCloseBlock [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  rw [interiorCloseBlock, ptrFlow_seq, flow_interior_0, Option.bind_some, ptrFlow_seq, flow_interior_1, Option.bind_some, ptrFlow_seq, flow_interior_2, Option.bind_some, ptrFlow_seq, flow_interior_3, Option.bind_some, ptrFlow_seq, flow_interior_4, Option.bind_some, ptrFlow_seq, flow_interior_5, Option.bind_some, ptrFlow_seq, flow_interior_6, Option.bind_some, flow_interior_7]

set_option maxHeartbeats 4000000 in
theorem flow_microtables : ptrFlow (microtablesBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, fringeDecodeActs, fringeEntryBlock, fringeStepBlock, microtablesBlock, selectDecodeActs, selectEntryBlock, selectStepBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_headerPatch : ptrFlow (headerPatchBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, forSlots, headerPatchBlock, headerPatchStepBlock, ptrFlow, ptrStep]

set_option maxHeartbeats 4000000 in
theorem flow_pad : ptrFlow (padBlock) [108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBit, padBlock, zerosBlock, ptrFlow, ptrStep]

theorem flow_buffer : ptrFlow bufferBlock [102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  rw [bufferBlock, ptrFlow_seq, flow_headerReserve, Option.bind_some, ptrFlow_seq, flow_bpEmit, Option.bind_some, ptrFlow_seq, flow_accessHalf, Option.bind_some, ptrFlow_seq, flow_interiorClose, Option.bind_some, ptrFlow_seq, flow_microtables, Option.bind_some, ptrFlow_seq, flow_headerPatch, Option.bind_some, flow_pad]

/-! ## Output -/

/-- Each metadata bank step is a short pure action list, decided on its own actions. -/
theorem flow_metaStep_all : ∀ i, i < 108 → ptrFlow (metaStepBlock i) [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159]
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | 10, _ => by decide
  | 11, _ => by decide
  | 12, _ => by decide
  | 13, _ => by decide
  | 14, _ => by decide
  | 15, _ => by decide
  | 16, _ => by decide
  | 17, _ => by decide
  | 18, _ => by decide
  | 19, _ => by decide
  | 20, _ => by decide
  | 21, _ => by decide
  | 22, _ => by decide
  | 23, _ => by decide
  | 24, _ => by decide
  | 25, _ => by decide
  | 26, _ => by decide
  | 27, _ => by decide
  | 28, _ => by decide
  | 29, _ => by decide
  | 30, _ => by decide
  | 31, _ => by decide
  | 32, _ => by decide
  | 33, _ => by decide
  | 34, _ => by decide
  | 35, _ => by decide
  | 36, _ => by decide
  | 37, _ => by decide
  | 38, _ => by decide
  | 39, _ => by decide
  | 40, _ => by decide
  | 41, _ => by decide
  | 42, _ => by decide
  | 43, _ => by decide
  | 44, _ => by decide
  | 45, _ => by decide
  | 46, _ => by decide
  | 47, _ => by decide
  | 48, _ => by decide
  | 49, _ => by decide
  | 50, _ => by decide
  | 51, _ => by decide
  | 52, _ => by decide
  | 53, _ => by decide
  | 54, _ => by decide
  | 55, _ => by decide
  | 56, _ => by decide
  | 57, _ => by decide
  | 58, _ => by decide
  | 59, _ => by decide
  | 60, _ => by decide
  | 61, _ => by decide
  | 62, _ => by decide
  | 63, _ => by decide
  | 64, _ => by decide
  | 65, _ => by decide
  | 66, _ => by decide
  | 67, _ => by decide
  | 68, _ => by decide
  | 69, _ => by decide
  | 70, _ => by decide
  | 71, _ => by decide
  | 72, _ => by decide
  | 73, _ => by decide
  | 74, _ => by decide
  | 75, _ => by decide
  | 76, _ => by decide
  | 77, _ => by decide
  | 78, _ => by decide
  | 79, _ => by decide
  | 80, _ => by decide
  | 81, _ => by decide
  | 82, _ => by decide
  | 83, _ => by decide
  | 84, _ => by decide
  | 85, _ => by decide
  | 86, _ => by decide
  | 87, _ => by decide
  | 88, _ => by decide
  | 89, _ => by decide
  | 90, _ => by decide
  | 91, _ => by decide
  | 92, _ => by decide
  | 93, _ => by decide
  | 94, _ => by decide
  | 95, _ => by decide
  | 96, _ => by decide
  | 97, _ => by decide
  | 98, _ => by decide
  | 99, _ => by decide
  | 100, _ => by decide
  | 101, _ => by decide
  | 102, _ => by decide
  | 103, _ => by decide
  | 104, _ => by decide
  | 105, _ => by decide
  | 106, _ => by decide
  | 107, _ => by decide
  | _ + 108, h => absurd h (by omega)

theorem flow_metaChain : ∀ k, k ≤ 108 → ptrFlow (metaChain k) [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
      intro hk
      rw [metaChain, ptrFlow_seq, ih (by omega), Option.bind_some, flow_metaStep_all k (by omega)]

theorem flow_emitBit (r : Operand) (I : List Nat) :
    ptrFlow (emitBit r) I = some (10 :: I.filter (· ≠ 10)) := by
  simp [emitBit, ptrFlow, ptrStep]

theorem filter_ne_ten_of_not_mem (I : List Nat) (hI : (10 : Nat) ∉ I) : I.filter (· ≠ 10) = I :=
  List.filter_eq_self.mpr (fun a ha => by simp only [ne_eq, decide_eq_true_eq]; intro h; exact hI (h ▸ ha))

theorem flow_emitRegs (I : List Nat) (hI : (10 : Nat) ∉ I) :
    ∀ rs, ptrFlow (emitRegs rs) (10 :: I) = some (10 :: I) := by
  have hf : (10 :: I).filter (· ≠ 10) = I := by
    rw [List.filter_cons]
    simp only [ne_eq, not_true_eq_false, decide_false]
    exact filter_ne_ten_of_not_mem I hI
  intro rs
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [emitRegs, ptrFlow_seq, flow_emitBit, hf, Option.bind_some, ih]

theorem flow_metaEmit : ptrFlow metaEmitBlock [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [10, 3, 224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  obtain ⟨r, rs, h⟩ : ∃ r rs, metaWordRegs = r :: rs := ⟨_, _, rfl⟩
  have h1 : ptrFlow (acts [.reserve rOUT, .store rOUT 1]) [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some (3 :: [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159]) := by decide
  rw [metaEmitBlock, ptrFlow_seq, h1, Option.bind_some, h, emitRegs, ptrFlow_seq, flow_emitBit,
    filter_ne_ten_of_not_mem _ (by decide), Option.bind_some, flow_emitRegs _ (by decide) rs]

set_option maxHeartbeats 4000000 in
theorem flow_repack : ptrFlow (repackBlock) [10, 3, 224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [10, 3, 224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  simp [acts, emitBit, forSlots, hornerStepBlock, repackBlock, repackWordBlock, ptrFlow, ptrStep]

theorem flow_output : ptrFlow outputBlock [224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] = some [10, 3, 224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  rw [outputBlock, ptrFlow_seq, flow_metaChain 108 (Nat.le_refl _), Option.bind_some, ptrFlow_seq, flow_metaEmit,
    Option.bind_some, flow_repack]

/-! ## The whole sources -/

theorem flow_builderSource_key : ptrFlow (builderSource keyLeaf) [] = some [10, 3, 224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  rw [builderSource, ptrFlow_seq, flow_header, Option.bind_some, builderBody, ptrFlow_seq, flow_constants,
    Option.bind_some, ptrFlow_seq, flow_geometry, Option.bind_some, ptrFlow_seq, flow_arrays, Option.bind_some,
    ptrFlow_seq, ptrFlow_seq, flow_stackArrays, Option.bind_some, ptrFlow_seq, flow_stackPass_key,
    Option.bind_some, flow_buffer, Option.bind_some, flow_output]

theorem flow_builderSource_word : ptrFlow (builderSource wordLeaf) [] = some [10, 3, 224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159] := by
  rw [builderSource, ptrFlow_seq, flow_header, Option.bind_some, builderBody, ptrFlow_seq, flow_constants,
    Option.bind_some, ptrFlow_seq, flow_geometry, Option.bind_some, ptrFlow_seq, flow_arrays, Option.bind_some,
    ptrFlow_seq, ptrFlow_seq, flow_stackArrays, Option.bind_some, ptrFlow_seq, flow_stackPass_word,
    Option.bind_some, flow_buffer, Option.bind_some, flow_output]

end RMQ.SuccinctFinal.PackedConstruction.Proof
