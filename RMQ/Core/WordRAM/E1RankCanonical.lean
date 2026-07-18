import RMQ.Core.WordRAM.E1RankBlock
import RMQ.Core.SuccinctFinalRAM

/-!
# E1 amended machine: rank-close block at the accepted component (M3c-1c)

Canonical instantiation of `rankCloseBlock_runsTo_hit` at the accepted
rank-close component
`concreteBPNativeRankCloseWordTraceResultAtSegment shape rankSegmentBase
pos` (frozen matrix REQ-E1-03/04): the hit-path hypotheses — presence of
the three seed reads and the in-word offset bound — are discharged from
the route's own data (`super_present`/`block_present`/`word_present`, the
fixed-width tables' `read_exact` codec, and the sentinel-chunked word
store's index characterization), so the machine block simulates the
component for EVERY shape and EVERY position, with no sampling and no
readiness guards.
-/

namespace RMQ
namespace WordRAM
namespace E1RankBlock

open E1Machine
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-- The seed word store of the built rank-close data is the sentinel-
chunked payload store (definitional). -/
private theorem builtRankData_bitWords_words (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).bitWords.store.words =
      (SuccinctSpace.chunkPayloadWords
          (builtRelativeSplitBPCloseRankData shape).wordSize shape.bpCode ++
        List.replicate (shape.bpCode.length + 1) []).toArray := rfl

/--
Offset bound for the sentinel-chunked seed word store: whatever word the
built data presents at the clamped word index, the in-word offset lies
inside it (full chunks cover the offset strictly below the word size; the
sentinel row is reached only at an exact top boundary, where the offset is
zero).
-/
theorem builtRankData_wordOffset_le
    (shape : Cartesian.CartesianShape) (pos : Nat) {w : List Bool}
    (hw : (builtRelativeSplitBPCloseRankData shape).bitWords.store.words[
        (builtRelativeSplitBPCloseRankData shape).wordIndex pos]? =
      some w) :
    (builtRelativeSplitBPCloseRankData shape).wordOffset pos <=
      w.length := by
  have hWSpos : 0 < (builtRelativeSplitBPCloseRankData shape).wordSize :=
    (builtRelativeSplitBPCloseRankData shape).wordSize_pos
  rw [builtRankData_bitWords_words] at hw
  rw [List.getElem?_toArray] at hw
  have hwidef : (builtRelativeSplitBPCloseRankData shape).wordIndex pos =
      (builtRelativeSplitBPCloseRankData shape).queryPos pos /
        (builtRelativeSplitBPCloseRankData shape).wordSize := rfl
  have hqle : (builtRelativeSplitBPCloseRankData shape).queryPos pos <=
      shape.bpCode.length := Nat.min_le_right _ _
  have hdm := Nat.div_add_mod
    ((builtRelativeSplitBPCloseRankData shape).queryPos pos)
    (builtRelativeSplitBPCloseRankData shape).wordSize
  have hmodlt := Nat.mod_lt
    ((builtRelativeSplitBPCloseRankData shape).queryPos pos) hWSpos
  have hmulcomm :
      (builtRelativeSplitBPCloseRankData shape).queryPos pos /
          (builtRelativeSplitBPCloseRankData shape).wordSize *
          (builtRelativeSplitBPCloseRankData shape).wordSize =
        (builtRelativeSplitBPCloseRankData shape).wordSize *
          ((builtRelativeSplitBPCloseRankData shape).queryPos pos /
            (builtRelativeSplitBPCloseRankData shape).wordSize) :=
    Nat.mul_comm _ _
  show (builtRelativeSplitBPCloseRankData shape).queryPos pos -
      (builtRelativeSplitBPCloseRankData shape).wordIndex pos *
        (builtRelativeSplitBPCloseRankData shape).wordSize <= w.length
  rcases Nat.lt_or_ge
      ((builtRelativeSplitBPCloseRankData shape).wordIndex pos)
      (SuccinctSpace.chunkPayloadWords
        (builtRelativeSplitBPCloseRankData shape).wordSize
        shape.bpCode).length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hw
    have hchunk := SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hw
    have hlen : w.length =
        Nat.min (builtRelativeSplitBPCloseRankData shape).wordSize
          (shape.bpCode.length -
            (builtRelativeSplitBPCloseRankData shape).wordIndex pos *
              (builtRelativeSplitBPCloseRankData shape).wordSize) := by
      rw [hchunk]
      simp [List.length_take, List.length_drop]
    rw [hlen, nat_min_eq_sub_sub, hwidef]
    rw [hwidef] at hlt
    omega
  · rw [List.getElem?_append_right hge] at hw
    have hclen := SuccinctSpace.chunkPayloadWords_length_eq_div_add_indicator
      hWSpos shape.bpCode
    have hdmL := Nat.div_add_mod shape.bpCode.length
      (builtRelativeSplitBPCloseRankData shape).wordSize
    have hdivle : (builtRelativeSplitBPCloseRankData shape).queryPos pos /
          (builtRelativeSplitBPCloseRankData shape).wordSize <=
        shape.bpCode.length /
          (builtRelativeSplitBPCloseRankData shape).wordSize :=
      Nat.div_le_div_right hqle
    rw [hwidef] at hge
    rw [hclen] at hge
    by_cases hLmod : shape.bpCode.length %
        (builtRelativeSplitBPCloseRankData shape).wordSize = 0
    · rw [if_pos hLmod] at hge
      have hpq : (builtRelativeSplitBPCloseRankData shape).queryPos pos /
            (builtRelativeSplitBPCloseRankData shape).wordSize =
          shape.bpCode.length /
            (builtRelativeSplitBPCloseRankData shape).wordSize := by
        omega
      have hmulL :
          (builtRelativeSplitBPCloseRankData shape).wordSize *
              ((builtRelativeSplitBPCloseRankData shape).queryPos pos /
                (builtRelativeSplitBPCloseRankData shape).wordSize) =
            (builtRelativeSplitBPCloseRankData shape).wordSize *
              (shape.bpCode.length /
                (builtRelativeSplitBPCloseRankData shape).wordSize) := by
        rw [hpq]
      rw [hwidef]
      omega
    · rw [if_neg hLmod] at hge
      omega

/--
Rank-close component simulation at the accepted seed store: for every
shape and every position, the hosted block runs — with exact fuel — from
block entry to `B + 60` with receipts POSITIONALLY EQUAL to the accepted
`concreteBPNativeRankCloseWordTraceResultAtSegment` trace, its value in
`rVal`, and the frozen category log; registers outside the component bank
are preserved.  All-size, no sampling, no readiness guards (REQ-E1-03/04
rank-close leg, machine side).
-/
theorem rankCloseBlock_runsTo_atSegment
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {B rankSegmentBase : Nat}
    (hhost : HostedAt program B
      (rankCloseBlock B rankSegmentBase
        (bpFringeChunkBits shape.bpCode.length)
        shape.bpCode.length
        (builtRelativeSplitBPCloseRankData shape).wordSize
        (builtRelativeSplitBPCloseRankData shape).blocksPerSuper))
    (regs0 : RegFile) :
    ∃ regsF : RegFile,
      RunsTo
          (concreteBPNativeChunkedRankCloseSeedReadStore shape
            rankSegmentBase)
          program ⟨regs0, B, false⟩ ⟨regsF, B + 60, false⟩
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape
          rankSegmentBase (regs0 rPos)).trace
        (rankCloseHitCats
          (bpWordChunkCount (bpFringeChunkBits shape.bpCode.length)
            ((builtRelativeSplitBPCloseRankData shape).wordOffset
              (regs0 rPos)))) ∧
      regsF rVal =
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape
          rankSegmentBase (regs0 rPos)).value ∧
      (forall r, r <= 8 ∨ 28 <= r -> regsF r = regs0 r) := by
  have hp : (builtRelativeSplitBPCloseRankData shape).queryPos
      (regs0 rPos) <= shape.bpCode.length := Nat.min_le_right _ _
  -- super sample presence
  obtain ⟨superSample, hsE⟩ :=
    (builtRelativeSplitBPCloseRankData shape).super_present false
      ((builtRelativeSplitBPCloseRankData shape).queryPos (regs0 rPos)) hp
  have hsMap :
      (((builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).superIndex
          (regs0 rPos)]?).map SuccinctSpace.bitsToNatLE =
      some superSample := by
    rw [(builtRelativeSplitBPCloseRankData
      shape).superTables.falseTable.read_exact]
    exact hsE
  obtain ⟨superWord, hsw⟩ :
      ∃ sw, ((builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).superIndex
          (regs0 rPos)]? = some sw := by
    cases hcase : ((builtRelativeSplitBPCloseRankData
        shape).superTables.falseTable.store.words)[
      (builtRelativeSplitBPCloseRankData shape).superIndex
        (regs0 rPos)]? with
    | none =>
        rw [hcase] at hsMap
        exact Option.noConfusion hsMap
    | some sw => exact ⟨sw, rfl⟩
  have hsuper :
      (concreteBPNativeChunkedRankCloseSeedReadStore shape
          rankSegmentBase).readWord? rankSegmentBase
        ((builtRelativeSplitBPCloseRankData shape).superIndex
          (regs0 rPos)) = some superWord := by
    rw [concreteBPNativeChunkedRankCloseSeedReadStore_super]
    exact hsw
  -- block sample presence
  obtain ⟨blockSample, hbE⟩ :=
    (builtRelativeSplitBPCloseRankData shape).block_present false
      ((builtRelativeSplitBPCloseRankData shape).queryPos (regs0 rPos)) hp
  have hbMap :
      (((builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)]?).map SuccinctSpace.bitsToNatLE =
      some blockSample := by
    rw [(builtRelativeSplitBPCloseRankData
      shape).blockTables.falseTable.read_exact]
    exact hbE
  obtain ⟨deltaWord, hbw⟩ :
      ∃ bw, ((builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)]? = some bw := by
    cases hcase : ((builtRelativeSplitBPCloseRankData
        shape).blockTables.falseTable.store.words)[
      (builtRelativeSplitBPCloseRankData shape).wordIndex
        (regs0 rPos)]? with
    | none =>
        rw [hcase] at hbMap
        exact Option.noConfusion hbMap
    | some bw => exact ⟨bw, rfl⟩
  have hblock :
      (concreteBPNativeChunkedRankCloseSeedReadStore shape
          rankSegmentBase).readWord? (rankSegmentBase + 1)
        ((builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)) = some deltaWord := by
    rw [concreteBPNativeChunkedRankCloseSeedReadStore_block]
    exact hbw
  -- packed word presence
  obtain ⟨w, hwq⟩ :=
    (builtRelativeSplitBPCloseRankData shape).word_present
      ((builtRelativeSplitBPCloseRankData shape).queryPos (regs0 rPos)) hp
  have hword :
      (concreteBPNativeChunkedRankCloseSeedReadStore shape
          rankSegmentBase).readWord? (rankSegmentBase + 2)
        ((builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)) = some w := by
    rw [concreteBPNativeChunkedRankCloseSeedReadStore_word]
    exact hwq
  -- offset bound
  have hoff : (builtRelativeSplitBPCloseRankData shape).wordOffset
      (regs0 rPos) <= w.length :=
    builtRankData_wordOffset_le shape (regs0 rPos) hwq
  -- instantiate the hit-path block theorem
  obtain ⟨regsF, hrun, hval, hpres⟩ :=
    rankCloseBlock_runsTo_hit
      (concreteBPNativeChunkedRankCloseSeedReadStore shape rankSegmentBase)
      (builtRelativeSplitBPCloseRankData shape) hhost regs0
      hsuper hblock hword hoff
  exact ⟨regsF, hrun, hval, hpres⟩

/--
Rank-close component simulation at the CANONICAL global store (segment
base `17`): for every shape, every base, and every position, the hosted
rank-close block runs against
`concreteBPNativeSuccinctRMQGlobalReadStore shape` — the single store the
whole accepted query reads — from block entry to `B + 60` with receipts
POSITIONALLY EQUAL to
`(concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape pos).trace`,
the component's `.value` in `rVal`, the frozen `rankCloseHitCats`
category log, and all registers outside the component bank preserved.
The machine store and the component store are the SAME argument, so this
is the store-swap glue form consumed by the whole-query composition
(REQ-E1-03/04 rank-close leg at the canonical store).
-/
theorem rankCloseBlock_runsTo_canonical
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {B : Nat}
    (hhost : HostedAt program B
      (rankCloseBlock B concreteBPNativeRankCloseTraceSegmentBase
        (bpFringeChunkBits shape.bpCode.length)
        shape.bpCode.length
        (builtRelativeSplitBPCloseRankData shape).wordSize
        (builtRelativeSplitBPCloseRankData shape).blocksPerSuper))
    (regs0 : RegFile) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨regs0, B, false⟩ ⟨regsF, B + 60, false⟩
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (regs0 rPos)).trace
        (rankCloseHitCats
          (bpWordChunkCount (bpFringeChunkBits shape.bpCode.length)
            ((builtRelativeSplitBPCloseRankData shape).wordOffset
              (regs0 rPos)))) ∧
      regsF rVal =
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (regs0 rPos)).value ∧
      (forall r, r <= 8 ∨ 28 <= r -> regsF r = regs0 r) := by
  have hp : (builtRelativeSplitBPCloseRankData shape).queryPos
      (regs0 rPos) <= shape.bpCode.length := Nat.min_le_right _ _
  -- super sample presence at the canonical store
  obtain ⟨superSample, hsE⟩ :=
    (builtRelativeSplitBPCloseRankData shape).super_present false
      ((builtRelativeSplitBPCloseRankData shape).queryPos (regs0 rPos)) hp
  have hsMap :
      (((builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).superIndex
          (regs0 rPos)]?).map SuccinctSpace.bitsToNatLE =
      some superSample := by
    rw [(builtRelativeSplitBPCloseRankData
      shape).superTables.falseTable.read_exact]
    exact hsE
  obtain ⟨superWord, hsw⟩ :
      ∃ sw, ((builtRelativeSplitBPCloseRankData
          shape).superTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).superIndex
          (regs0 rPos)]? = some sw := by
    cases hcase : ((builtRelativeSplitBPCloseRankData
        shape).superTables.falseTable.store.words)[
      (builtRelativeSplitBPCloseRankData shape).superIndex
        (regs0 rPos)]? with
    | none =>
        rw [hcase] at hsMap
        exact Option.noConfusion hsMap
    | some sw => exact ⟨sw, rfl⟩
  have hsuper :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          concreteBPNativeRankCloseTraceSegmentBase
        ((builtRelativeSplitBPCloseRankData shape).superIndex
          (regs0 rPos)) = some superWord := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseSuper]
    exact hsw
  -- block sample presence at the canonical store
  obtain ⟨blockSample, hbE⟩ :=
    (builtRelativeSplitBPCloseRankData shape).block_present false
      ((builtRelativeSplitBPCloseRankData shape).queryPos (regs0 rPos)) hp
  have hbMap :
      (((builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)]?).map SuccinctSpace.bitsToNatLE =
      some blockSample := by
    rw [(builtRelativeSplitBPCloseRankData
      shape).blockTables.falseTable.read_exact]
    exact hbE
  obtain ⟨deltaWord, hbw⟩ :
      ∃ bw, ((builtRelativeSplitBPCloseRankData
          shape).blockTables.falseTable.store.words)[
        (builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)]? = some bw := by
    cases hcase : ((builtRelativeSplitBPCloseRankData
        shape).blockTables.falseTable.store.words)[
      (builtRelativeSplitBPCloseRankData shape).wordIndex
        (regs0 rPos)]? with
    | none =>
        rw [hcase] at hbMap
        exact Option.noConfusion hbMap
    | some bw => exact ⟨bw, rfl⟩
  have hblock :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeRankCloseTraceSegmentBase + 1)
        ((builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)) = some deltaWord := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseBlock]
    exact hbw
  -- packed word presence at the canonical store
  obtain ⟨w, hwq⟩ :=
    (builtRelativeSplitBPCloseRankData shape).word_present
      ((builtRelativeSplitBPCloseRankData shape).queryPos (regs0 rPos)) hp
  have hword :
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
          (concreteBPNativeRankCloseTraceSegmentBase + 2)
        ((builtRelativeSplitBPCloseRankData shape).wordIndex
          (regs0 rPos)) = some w := by
    rw [concreteBPNativeSuccinctRMQGlobalReadStore_rankCloseWord]
    exact hwq
  -- offset bound
  have hoff : (builtRelativeSplitBPCloseRankData shape).wordOffset
      (regs0 rPos) <= w.length :=
    builtRankData_wordOffset_le shape (regs0 rPos) hwq
  -- instantiate the hit-path block theorem at the canonical store
  obtain ⟨regsF, hrun, hval, hpres⟩ :=
    rankCloseBlock_runsTo_hit
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (builtRelativeSplitBPCloseRankData shape) hhost regs0
      hsuper hblock hword hoff
  -- the component at the canonical bases IS the accepted canonical trace
  have htr : concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
      (regs0 rPos) =
    (builtRelativeSplitBPCloseRankData
        shape).bpChunkedRankTraceResultWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      concreteBPNativeRankCloseTraceSegmentBase
      (concreteBPNativeRankCloseTraceSegmentBase + 1)
      (concreteBPNativeRankCloseTraceSegmentBase + 2)
      (concreteBPNativeRankCloseTraceSegmentBase + 4)
      (bpFringeChunkBits shape.bpCode.length) false (regs0 rPos) := by
    rw [show concreteBPNativeRankCloseTraceSegmentBase + 4 =
      concreteBPNativeFringeChunkTraceSegment from rfl]
    rfl
  rw [htr]
  exact ⟨regsF, hrun, hval, hpres⟩

end E1RankBlock
end WordRAM
end RMQ
