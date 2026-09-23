import RMQ.Core.WordRAM.Construction.ArrayRun
import RMQ.Core.WordRAM.Construction.Proof.Flow

/-! # PRE-1 builder proofs: register frames of the builder source (stage S8)

Outside the builder firewall. `Block.RegsBelow R b` states that every register
operand of every action, exit and branch condition of `b` is below `R`, and
`Block.compile_regsBelow` transports it to `Prim.RegistersBelow R` of every
compiled instruction (jump targets are immediates). Per phase, by structural
simplification of `Block.WritesOnly`, `Action.prim`, `Prim.destination?` and
literal register disequalities (CONTRACT.md V3-9), the builder body never writes
register 1 (`wo_builderBody_key`, `wo_builderBody_word`), and every register
operand of the body is below 400 (`rb_builderBody_key`, `rb_builderBody_word`).
The metadata bank steps are unfolded one at a time (`delta`, `dsimp`); no
decision procedure runs over the compiled list or the whole template.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Structured

/-- Every register operand of every action, exit and branch condition of a
block is below `R`. -/
def Block.RegsBelow (R : Nat) : Block → Prop
  | .skip => True
  | .action op => op.prim.RegistersBelow R
  | .exit src => src.val < R
  | .seq a b => a.RegsBelow R ∧ b.RegsBelow R
  | .ifZero c zero nonzero => c.val < R ∧ zero.RegsBelow R ∧ nonzero.RegsBelow R
  | .loop c body => c.val < R ∧ body.RegsBelow R

theorem Block.compile_regsBelow (R : Nat) (block : Block) (h : block.RegsBelow R) (base : Nat) :
    ∀ i ∈ block.compileAt base, i.primitive.RegistersBelow R := by
  induction block generalizing base with
  | skip => simp [Block.compileAt]
  | action op =>
      intro i hi
      simp only [Block.compileAt, List.mem_singleton] at hi
      subst hi
      exact h
  | exit src =>
      intro i hi
      simp only [Block.compileAt, List.mem_singleton] at hi
      subst hi
      exact h
  | seq a b iha ihb =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact iha h.1 _ i hi
      · exact ihb h.2 _ i hi
  | ifZero c zero nonzero ihz ihn =>
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · exact h.1
      · exact ihn h.2.2 _ i hi
      · trivial
      · exact ihz h.2.1 _ i hi
  | loop c body ih =>
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_singleton] at hi
      rcases hi with (rfl | hi) | rfl
      · exact h.1
      · exact ih h.2 _ i hi
      · trivial

end RMQ.SuccinctFinal.PackedConstruction.Structured

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

theorem Prim.dest_lt_of_registersBelow {R : Nat} {p : Prim} (h : p.RegistersBelow R) :
    ∀ d, p.destination? = some d → d.val < R := by
  intro d hd
  cases p <;> simp only [Prim.destination?, Option.some.injEq, reduceCtorEq] at hd <;> subst hd <;>
    simp only [Prim.RegistersBelow] at h <;> omega

end RMQ.SuccinctFinal.PackedConstruction.Proof

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

/-! ## Register 1 is written only by the header -/

set_option maxHeartbeats 4000000 in
theorem wo_constants : (constantsBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, constantsBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_geoStep : ∀ j, (geoStepBlock j).WritesOnly (fun r => r ≠ 1) := by
  intro j
  unfold geoStepBlock
  split <;> simp [acts, wordBitsBlock, log2Block, log2Body, minActs, Block.WritesOnly, Action.prim, Prim.destination?]

theorem wo_geoChain : ∀ j, (geoChain j).WritesOnly (fun r => r ≠ 1) := by
  intro j
  induction j with
  | zero => trivial
  | succ j ih =>
      simp only [geoChain, Block.WritesOnly]
      exact ⟨ih, wo_geoStep j⟩

set_option maxHeartbeats 4000000 in
theorem wo_interiorGeometry : (interiorGeometryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, interiorGeometryBlock, levelWidthBlock, log2Block, log2Body, Block.WritesOnly, Action.prim, Prim.destination?]

theorem wo_geometry : (geometryPrelude).WritesOnly (fun r => r ≠ 1) := by
  simp only [geometryPrelude, Block.WritesOnly]
  exact ⟨wo_interiorGeometry, wo_geoChain 39⟩

set_option maxHeartbeats 4000000 in
theorem wo_arrays : (arraysBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, arraysBlock, emitBit, reserveArray, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_stackArrays : (stackArraysBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBit, reserveArray, stackArraysBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_stackPass_key : (stackPassBlock keyLeaf).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, forSlots, keyLeaf, linkBlock, popBodyBlock, popGuardBlock, pushBlock, stackPassBlock, stackStepBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_stackPass_word : (stackPassBlock wordLeaf).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, forSlots, linkBlock, popBodyBlock, popGuardBlock, pushBlock, stackPassBlock, stackStepBlock, wordLeaf, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_headerReserve : (headerReserveBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBit, headerReserveBlock, reserveArray, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_bpEmit : (bpEmitBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, bpEmitBlock, bpUnitBlock, emitBit, forSlots, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_0 : (posPassBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, forSlots, posPassBlock, posStepBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_1 : (longFlagsBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, forSlots, longFlagBlock, longFlagsBlock, maxActs, minActs, monusActs, posActs, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_2 : (sparseFlagsBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, forSlots, maxActs, minActs, monusActs, posActs, sparseFlagBlock, sparseFlagsBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_3 : (emitTable rRSUP rWS rankSuperEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, rankSuperEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_4 : (emitTable rRBLK rRBW rankBlockEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, rankBlockEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_5 : (emitTable rSUP rWS superOccEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, superOccEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_6 : (emitTable rSUP rWS superWordEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, minActs, posActs, superWordEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_7 : (emitTable rSUP rWS superFlagEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, superFlagEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_8 : (emitTable rSUP rWS superOffsetEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, minActs, posActs, superOffsetEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_9 : (emitTable rLOC rLW localOccEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localOccEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_10 : (emitTable rLOC rLW localWordEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localWordEntryBlock, minActs, posActs, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_11 : (emitTable rLOC rLW localFlagEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localFlagEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_12 : (emitTable rLOC rLW localOffsetEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localOffsetEntryBlock, minActs, posActs, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_13 : (emitTable rLFR rLFW (flagRankEntryBlock rLFCB rLFW)).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagRankEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_14 : (emitTable rLFR rLFW zeroEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, zeroEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_15 : (emitTable rSUP rONE (flagEntryBlock rLFB)).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_16 : (forSlots rK rKGO rSUP longRelativeBodyBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, longRelativeBodyBlock, maxActs, minActs, monusActs, posActs, relativeOffsetEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_17 : (emitTable rSFR rSFW (flagRankEntryBlock rSFCB rSFW)).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagRankEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_18 : (emitTable rSFR rSFW zeroEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, zeroEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_19 : (emitTable rSP rONE (flagEntryBlock rSFB)).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_access_20 : (forSlots rG rGGO rLOC sparseRelativeBodyBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, maxActs, minActs, monusActs, posActs, relativeOffsetEntryBlock, sparseRelativeBodyBlock, Block.WritesOnly, Action.prim, Prim.destination?]

theorem wo_accessHalf : (accessHalfBlock).WritesOnly (fun r => r ≠ 1) := by
  simp only [accessHalfBlock, Block.WritesOnly]
  exact ⟨wo_access_0, wo_access_1, wo_access_2, wo_access_3, wo_access_4, wo_access_5, wo_access_6, wo_access_7, wo_access_8, wo_access_9, wo_access_10, wo_access_11, wo_access_12, wo_access_13, wo_access_14, wo_access_15, wo_access_16, wo_access_17, wo_access_18, wo_access_19, wo_access_20⟩

set_option maxHeartbeats 4000000 in
theorem wo_interior_0 : (blockStatsBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, blockBodyBlock, blockStatsBlock, forSlots, maxActs, minActs, sampleBodyBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_interior_1 : (localMemoBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, betterActs, forSlots, localMemoBlock, memoCellBlock, memoLevelsBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_interior_2 : (globalMemoBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, betterActs, forSlots, globalMemoBlock, macroScanBlock, memoCellBlock, memoLevelsBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_interior_3 : (summaryTablesBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, argOffsetEntryBlock, baselineEntryBlock, emitBits, emitBitsBody, emitTable, emitTableBody, relativeEntryBlock, summaryTablesBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_interior_4 : (emitTable rLSCNT rOW localEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_interior_5 : (emitTable rGSCNT rBAW globalEntryBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, globalEntryBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_interior_6 : (levelTableBlock rLDOM rLWID).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, levelEntryBlock, levelTableBlock, log2Block, log2Body, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_interior_7 : (levelTableBlock rGDOM rGWID).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, levelEntryBlock, levelTableBlock, log2Block, log2Body, Block.WritesOnly, Action.prim, Prim.destination?]

theorem wo_interiorClose : (interiorCloseBlock).WritesOnly (fun r => r ≠ 1) := by
  simp only [interiorCloseBlock, Block.WritesOnly]
  exact ⟨wo_interior_0, wo_interior_1, wo_interior_2, wo_interior_3, wo_interior_4, wo_interior_5, wo_interior_6, wo_interior_7⟩

set_option maxHeartbeats 4000000 in
theorem wo_microtables : (microtablesBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, fringeDecodeActs, fringeEntryBlock, fringeStepBlock, microtablesBlock, selectDecodeActs, selectEntryBlock, selectStepBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_headerPatch : (headerPatchBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, forSlots, headerPatchBlock, headerPatchStepBlock, Block.WritesOnly, Action.prim, Prim.destination?]

set_option maxHeartbeats 4000000 in
theorem wo_pad : (padBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBit, padBlock, zerosBlock, Block.WritesOnly, Action.prim, Prim.destination?]

theorem wo_buffer : (bufferBlock).WritesOnly (fun r => r ≠ 1) := by
  simp only [bufferBlock, Block.WritesOnly]
  exact ⟨wo_headerReserve, wo_bpEmit, wo_accessHalf, wo_interiorClose, wo_microtables, wo_headerPatch, wo_pad⟩

set_option maxHeartbeats 40000000 in
theorem wo_metaStep_all : ∀ i, i < 108 → (metaStepBlock i).WritesOnly (fun r => r ≠ 1)
  | 0, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 1, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 2, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 3, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 4, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 5, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 6, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 7, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 8, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 9, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 10, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 11, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 12, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 13, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 14, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 15, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 16, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 17, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 18, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 19, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 20, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 21, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 22, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 23, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 24, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 25, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 26, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 27, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 28, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 29, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 30, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 31, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 32, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 33, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 34, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 35, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 36, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 37, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 38, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 39, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 40, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 41, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 42, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 43, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 44, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 45, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 46, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 47, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 48, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 49, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 50, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 51, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 52, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 53, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 54, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 55, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 56, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 57, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 58, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 59, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 60, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 61, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 62, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 63, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 64, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 65, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 66, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 67, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 68, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 69, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 70, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 71, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 72, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 73, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 74, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 75, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 76, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 77, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 78, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 79, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 80, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 81, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 82, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 83, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 84, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 85, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 86, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 87, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 88, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 89, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 90, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 91, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 92, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 93, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 94, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 95, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 96, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 97, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 98, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 99, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 100, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 101, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 102, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 103, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 104, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 105, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 106, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | 107, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.WritesOnly, Action.prim, Prim.destination?]
  | _ + 108, h => absurd h (by omega)

theorem wo_metaChain : ∀ j, j ≤ 108 → (metaChain j).WritesOnly (fun r => r ≠ 1) := by
  intro j
  induction j with
  | zero => intro _; trivial
  | succ j ih =>
      intro hj
      simp only [metaChain, Block.WritesOnly]
      exact ⟨ih (by omega), wo_metaStep_all j (by omega)⟩

theorem wo_emitRegs : ∀ rs, (emitRegs rs).WritesOnly (fun r => r ≠ 1) := by
  intro rs
  induction rs with
  | nil => trivial
  | cons r rs ih =>
      simp only [emitRegs, Block.WritesOnly]
      exact ⟨by simp [emitBit, Block.WritesOnly, Action.prim, Prim.destination?], ih⟩

theorem wo_metaEmit : (metaEmitBlock).WritesOnly (fun r => r ≠ 1) := by
  simp only [metaEmitBlock, Block.WritesOnly]
  exact ⟨by simp [acts, Block.WritesOnly, Action.prim, Prim.destination?], wo_emitRegs metaWordRegs⟩

set_option maxHeartbeats 4000000 in
theorem wo_repack : (repackBlock).WritesOnly (fun r => r ≠ 1) := by
  simp [acts, emitBit, forSlots, hornerStepBlock, repackBlock, repackWordBlock, Block.WritesOnly, Action.prim, Prim.destination?]

theorem wo_output : (outputBlock).WritesOnly (fun r => r ≠ 1) := by
  simp only [outputBlock, Block.WritesOnly]
  exact ⟨wo_metaChain 108 (Nat.le_refl _), wo_metaEmit, wo_repack⟩

theorem wo_builderBody_key : (builderBody keyLeaf).WritesOnly (fun r => r ≠ 1) := by
  simp only [builderBody, Block.WritesOnly]
  exact ⟨wo_constants, wo_geometry, wo_arrays, ⟨wo_stackArrays, wo_stackPass_key, wo_buffer⟩, wo_output⟩

theorem wo_builderBody_word : (builderBody wordLeaf).WritesOnly (fun r => r ≠ 1) := by
  simp only [builderBody, Block.WritesOnly]
  exact ⟨wo_constants, wo_geometry, wo_arrays, ⟨wo_stackArrays, wo_stackPass_word, wo_buffer⟩, wo_output⟩

/-! ## Every register operand is below 400 -/

set_option maxHeartbeats 4000000 in
theorem rb_constants : (constantsBlock).RegsBelow 400 := by
  simp [acts, constantsBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_geoStep : ∀ j, (geoStepBlock j).RegsBelow 400 := by
  intro j
  unfold geoStepBlock
  split <;> simp [acts, wordBitsBlock, log2Block, log2Body, minActs, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

theorem rb_geoChain : ∀ j, (geoChain j).RegsBelow 400 := by
  intro j
  induction j with
  | zero => trivial
  | succ j ih =>
      simp only [geoChain, Block.RegsBelow]
      exact ⟨ih, rb_geoStep j⟩

set_option maxHeartbeats 4000000 in
theorem rb_interiorGeometry : (interiorGeometryBlock).RegsBelow 400 := by
  simp [acts, interiorGeometryBlock, levelWidthBlock, log2Block, log2Body, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

theorem rb_geometry : (geometryPrelude).RegsBelow 400 := by
  simp only [geometryPrelude, Block.RegsBelow]
  exact ⟨rb_interiorGeometry, rb_geoChain 39⟩

set_option maxHeartbeats 4000000 in
theorem rb_arrays : (arraysBlock).RegsBelow 400 := by
  simp [acts, arraysBlock, emitBit, reserveArray, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_stackArrays : (stackArraysBlock).RegsBelow 400 := by
  simp [acts, emitBit, reserveArray, stackArraysBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_stackPass_key : (stackPassBlock keyLeaf).RegsBelow 400 := by
  simp [acts, forSlots, keyLeaf, linkBlock, popBodyBlock, popGuardBlock, pushBlock, stackPassBlock, stackStepBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_stackPass_word : (stackPassBlock wordLeaf).RegsBelow 400 := by
  simp [acts, forSlots, linkBlock, popBodyBlock, popGuardBlock, pushBlock, stackPassBlock, stackStepBlock, wordLeaf, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_headerReserve : (headerReserveBlock).RegsBelow 400 := by
  simp [acts, emitBit, headerReserveBlock, reserveArray, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_bpEmit : (bpEmitBlock).RegsBelow 400 := by
  simp [acts, bpEmitBlock, bpUnitBlock, emitBit, forSlots, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_0 : (posPassBlock).RegsBelow 400 := by
  simp [acts, forSlots, posPassBlock, posStepBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_1 : (longFlagsBlock).RegsBelow 400 := by
  simp [acts, forSlots, longFlagBlock, longFlagsBlock, maxActs, minActs, monusActs, posActs, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_2 : (sparseFlagsBlock).RegsBelow 400 := by
  simp [acts, forSlots, maxActs, minActs, monusActs, posActs, sparseFlagBlock, sparseFlagsBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_3 : (emitTable rRSUP rWS rankSuperEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, rankSuperEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_4 : (emitTable rRBLK rRBW rankBlockEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, rankBlockEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_5 : (emitTable rSUP rWS superOccEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, superOccEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_6 : (emitTable rSUP rWS superWordEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, minActs, posActs, superWordEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_7 : (emitTable rSUP rWS superFlagEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, superFlagEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_8 : (emitTable rSUP rWS superOffsetEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, minActs, posActs, superOffsetEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_9 : (emitTable rLOC rLW localOccEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localOccEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_10 : (emitTable rLOC rLW localWordEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localWordEntryBlock, minActs, posActs, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_11 : (emitTable rLOC rLW localFlagEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localFlagEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_12 : (emitTable rLOC rLW localOffsetEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localDecodeActs, localOffsetEntryBlock, minActs, posActs, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_13 : (emitTable rLFR rLFW (flagRankEntryBlock rLFCB rLFW)).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagRankEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_14 : (emitTable rLFR rLFW zeroEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, zeroEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_15 : (emitTable rSUP rONE (flagEntryBlock rLFB)).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_16 : (forSlots rK rKGO rSUP longRelativeBodyBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, longRelativeBodyBlock, maxActs, minActs, monusActs, posActs, relativeOffsetEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_17 : (emitTable rSFR rSFW (flagRankEntryBlock rSFCB rSFW)).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagRankEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_18 : (emitTable rSFR rSFW zeroEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, zeroEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_19 : (emitTable rSP rONE (flagEntryBlock rSFB)).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, flagEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_access_20 : (forSlots rG rGGO rLOC sparseRelativeBodyBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, maxActs, minActs, monusActs, posActs, relativeOffsetEntryBlock, sparseRelativeBodyBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

theorem rb_accessHalf : (accessHalfBlock).RegsBelow 400 := by
  simp only [accessHalfBlock, Block.RegsBelow]
  exact ⟨rb_access_0, rb_access_1, rb_access_2, rb_access_3, rb_access_4, rb_access_5, rb_access_6, rb_access_7, rb_access_8, rb_access_9, rb_access_10, rb_access_11, rb_access_12, rb_access_13, rb_access_14, rb_access_15, rb_access_16, rb_access_17, rb_access_18, rb_access_19, rb_access_20⟩

set_option maxHeartbeats 4000000 in
theorem rb_interior_0 : (blockStatsBlock).RegsBelow 400 := by
  simp [acts, blockBodyBlock, blockStatsBlock, forSlots, maxActs, minActs, sampleBodyBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_interior_1 : (localMemoBlock).RegsBelow 400 := by
  simp [acts, betterActs, forSlots, localMemoBlock, memoCellBlock, memoLevelsBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_interior_2 : (globalMemoBlock).RegsBelow 400 := by
  simp [acts, betterActs, forSlots, globalMemoBlock, macroScanBlock, memoCellBlock, memoLevelsBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_interior_3 : (summaryTablesBlock).RegsBelow 400 := by
  simp [acts, argOffsetEntryBlock, baselineEntryBlock, emitBits, emitBitsBody, emitTable, emitTableBody, relativeEntryBlock, summaryTablesBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_interior_4 : (emitTable rLSCNT rOW localEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, localEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_interior_5 : (emitTable rGSCNT rBAW globalEntryBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, globalEntryBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_interior_6 : (levelTableBlock rLDOM rLWID).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, levelEntryBlock, levelTableBlock, log2Block, log2Body, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_interior_7 : (levelTableBlock rGDOM rGWID).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, levelEntryBlock, levelTableBlock, log2Block, log2Body, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

theorem rb_interiorClose : (interiorCloseBlock).RegsBelow 400 := by
  simp only [interiorCloseBlock, Block.RegsBelow]
  exact ⟨rb_interior_0, rb_interior_1, rb_interior_2, rb_interior_3, rb_interior_4, rb_interior_5, rb_interior_6, rb_interior_7⟩

set_option maxHeartbeats 4000000 in
theorem rb_microtables : (microtablesBlock).RegsBelow 400 := by
  simp [acts, emitBits, emitBitsBody, emitTable, emitTableBody, forSlots, fringeDecodeActs, fringeEntryBlock, fringeStepBlock, microtablesBlock, selectDecodeActs, selectEntryBlock, selectStepBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_headerPatch : (headerPatchBlock).RegsBelow 400 := by
  simp [acts, forSlots, headerPatchBlock, headerPatchStepBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

set_option maxHeartbeats 4000000 in
theorem rb_pad : (padBlock).RegsBelow 400 := by
  simp [acts, emitBit, padBlock, zerosBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

theorem rb_buffer : (bufferBlock).RegsBelow 400 := by
  simp only [bufferBlock, Block.RegsBelow]
  exact ⟨rb_headerReserve, rb_bpEmit, rb_accessHalf, rb_interiorClose, rb_microtables, rb_headerPatch, rb_pad⟩

set_option maxHeartbeats 40000000 in
theorem rb_metaStep_all : ∀ i, i < 108 → (metaStepBlock i).RegsBelow 400
  | 0, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 1, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 2, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 3, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 4, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 5, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 6, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 7, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 8, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 9, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 10, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 11, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 12, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 13, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 14, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 15, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 16, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 17, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 18, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 19, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 20, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 21, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 22, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 23, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 24, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 25, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 26, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 27, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 28, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 29, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 30, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 31, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 32, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 33, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 34, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 35, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 36, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 37, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 38, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 39, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 40, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 41, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 42, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 43, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 44, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 45, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 46, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 47, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 48, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 49, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 50, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 51, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 52, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 53, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 54, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 55, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 56, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 57, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 58, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 59, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 60, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 61, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 62, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 63, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 64, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 65, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 66, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 67, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 68, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 69, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 70, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 71, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 72, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 73, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 74, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 75, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 76, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 77, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 78, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 79, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 80, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 81, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 82, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 83, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 84, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 85, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 86, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 87, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 88, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 89, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 90, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 91, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 92, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 93, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 94, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 95, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 96, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 97, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 98, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 99, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 100, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 101, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 102, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 103, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 104, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 105, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 106, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | 107, _ => by delta metaStepBlock; dsimp only; simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow]
  | _ + 108, h => absurd h (by omega)

theorem rb_metaChain : ∀ j, j ≤ 108 → (metaChain j).RegsBelow 400 := by
  intro j
  induction j with
  | zero => intro _; trivial
  | succ j ih =>
      intro hj
      simp only [metaChain, Block.RegsBelow]
      exact ⟨ih (by omega), rb_metaStep_all j (by omega)⟩

theorem rb_emitRegs : ∀ rs : List Operand, (∀ r ∈ rs, r.val < 400) → (emitRegs rs).RegsBelow 400 := by
  intro rs
  induction rs with
  | nil => intro _; trivial
  | cons r rs ih =>
      intro h
      simp only [emitRegs, Block.RegsBelow]
      exact ⟨by simp [emitBit, Block.RegsBelow, Action.prim, Prim.RegistersBelow, h r (List.mem_cons_self ..)], ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

set_option maxRecDepth 8000 in
theorem rb_metaWordRegs : ∀ r ∈ metaWordRegs, r.val < 400 := by
  simp [metaWordRegs]

theorem rb_metaEmit : (metaEmitBlock).RegsBelow 400 := by
  simp only [metaEmitBlock, Block.RegsBelow]
  exact ⟨by simp [acts, Block.RegsBelow, Action.prim, Prim.RegistersBelow], rb_emitRegs metaWordRegs rb_metaWordRegs⟩

set_option maxHeartbeats 4000000 in
theorem rb_repack : (repackBlock).RegsBelow 400 := by
  simp [acts, emitBit, forSlots, hornerStepBlock, repackBlock, repackWordBlock, Block.RegsBelow, Action.prim, Prim.RegistersBelow]

theorem rb_output : (outputBlock).RegsBelow 400 := by
  simp only [outputBlock, Block.RegsBelow]
  exact ⟨rb_metaChain 108 (Nat.le_refl _), rb_metaEmit, rb_repack⟩

theorem rb_builderBody_key : (builderBody keyLeaf).RegsBelow 400 := by
  simp only [builderBody, Block.RegsBelow]
  exact ⟨rb_constants, rb_geometry, rb_arrays, ⟨rb_stackArrays, rb_stackPass_key, rb_buffer⟩, rb_output⟩

theorem rb_builderBody_word : (builderBody wordLeaf).RegsBelow 400 := by
  simp only [builderBody, Block.RegsBelow]
  exact ⟨rb_constants, rb_geometry, rb_arrays, ⟨rb_stackArrays, rb_stackPass_word, rb_buffer⟩, rb_output⟩

end RMQ.SuccinctFinal.PackedConstruction.Proof
