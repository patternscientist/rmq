import RMQ.Core.SuccinctClose.RelativeRmmMacro.ChargedFringeChunks

/-!
# Charged chunked same-block close leaf (Option B, B6)

The accepted same-block LCA branch computed its min-excess/argmin pair by an
event-silent per-position scan: `localBPSameBlockCloseSeededCosted`
(`LocalBPDecoder.lean:1128-1143`) charges a constant `cost := 4` while
recursing over `count = rightClose - leftClose + 1` window positions, and on
the same-block branch `count` reaches `blockSize = 2 * (Nat.log2 size + 1)`,
which is unbounded in the input size.  It is the last event-silent
computation on the accepted route, and it is exactly the family the refuted
E1-R3 obstruction exhibited.

This module replaces that scan by the SAME charged chunk fold B2 already
built for the endpoint fringe.  No new table, segment, or store region is
introduced:

* the same-block window is definitionally the same object as the fringe
  window (`localBPWindowBits_eq_flatten_localBPBlockWordsRead`,
  `LocalBPDecoder.lean:228`), so `bpFringeChunkTable` applies unchanged; and
* the value equality is already proved generically by
  `bpFringeChunkFoldCosted_global_eq_localBPSeeded`
  (`ChargedFringeChunks.lean:1694`), whose window-length side condition is
  discharged all-size by `four_machineWordBits_le_32_mul_bpFringeChunkBits`.

The charged leaf therefore differs from `bpChunkedLeftFringeCandidateSeeded-
Costed` only in its range (`start := leftClose + 1`,
`count := rightClose - leftClose + 1`) and in applying `bpCandidateClose?`
to the resulting candidate, exactly as the accepted silent leaf does.
-/

namespace RMQ

namespace SuccinctClose

open SuccinctSpace

/--
Charged chunked same-block close leaf: the four charged window-word reads of
the accepted route, then at most 33 charged chunk-table reads combined by a
fixed-shape silent fold, and finally the accepted `bpCandidateClose?`
projection.

The chunk-count cap `Nat.min (relHi / c + 1) 33` is the identity on the
reachable domain (window <= 4 machine words <= 32 chunks) and makes the read
bound a literal for every argument, with no size hypothesis.
-/
def bpChunkedSameBlockCloseSeededCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) : Costed (Option Nat) :=
  let c := bpFringeChunkBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  let relLo := start - base
  let relHi := start + count - 1 - base
  Costed.bind
    (Costed.tickValue 4 (localBPWindowBits shape blockSize leftClose))
    (fun window =>
      Costed.map
        (fun st => bpCandidateClose? (bpFringeCandGlobal base seed start st.2))
        (bpFringeChunkFoldCosted (bpFringeChunkTable c) c window seed
          relLo relHi (Nat.min (relHi / c + 1) 33)))

/-- Literal all-size read bound for the charged same-block close leaf. -/
theorem bpChunkedSameBlockCloseSeededCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) :
    (bpChunkedSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed).cost <= 37 := by
  unfold bpChunkedSameBlockCloseSeededCosted
  simp [Costed.bind, Costed.map, Costed.tickValue, Costed.pure,
    bpFringeChunkFoldCosted_cost]
  exact Nat.add_le_add_left (Nat.min_le_right _ 33) 4

/--
Same-block value equivalence: under the coverage and window-validity facts
available at every accepted call site, the charged chunked same-block leaf
returns exactly the value the accepted event-silent leaf returns.
-/
theorem bpChunkedSameBlockCloseSeededCosted_value_eq
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat)
    (hvalid :
      BPFringeWindowValid (localBPWindowBits shape blockSize leftClose)
        seed)
    (hstart :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hcov :
      leftClose + 1 + (rightClose - leftClose + 1) <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length + 1) :
    (bpChunkedSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed).value =
      (localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed).value := by
  have hc := bpFringeChunkBits_pos shape.bpCode.length
  have hlen :
      (localBPWindowBits shape blockSize leftClose).length <=
        32 * bpFringeChunkBits shape.bpCode.length := by
    have h1 := localBPWindowBits_length_le shape blockSize leftClose
    have h2 :=
      four_machineWordBits_le_32_mul_bpFringeChunkBits shape.bpCode.length
    omega
  have hcount : 0 < rightClose - leftClose + 1 := Nat.succ_pos _
  have hcore :=
    bpFringeChunkFoldCosted_global_eq_localBPSeeded
      (window := localBPWindowBits shape blockSize leftClose)
      (seed := seed)
      (base := localBPWindowBase shape blockSize leftClose)
      (start := leftClose + 1)
      (count := rightClose - leftClose + 1)
      (bpFringeChunkBits shape.bpCode.length)
      hc hlen hvalid hcount hstart hcov
  show
    bpCandidateClose?
      (bpFringeCandGlobal (localBPWindowBase shape blockSize leftClose) seed
        (leftClose + 1)
        (bpFringeChunkFoldCosted
          (bpFringeChunkTable (bpFringeChunkBits shape.bpCode.length))
          (bpFringeChunkBits shape.bpCode.length)
          (localBPWindowBits shape blockSize leftClose) seed
          (leftClose + 1 - localBPWindowBase shape blockSize leftClose)
          (leftClose + 1 + (rightClose - leftClose + 1) - 1 -
            localBPWindowBase shape blockSize leftClose)
          (Nat.min
            ((leftClose + 1 + (rightClose - leftClose + 1) - 1 -
              localBPWindowBase shape blockSize leftClose) /
                bpFringeChunkBits shape.bpCode.length + 1)
            33)).value.2) =
      (localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed).value
  rw [hcore]
  simp [localBPSameBlockCloseSeededCosted,
    ← localBPWindowBits_eq_flatten_localBPBlockWordsRead]

/-! ## Decoded twins (seed threaded exactly as on the accepted route) -/

/--
Charged chunked same-block close with the directory rank seed threaded
exactly as `localBPSameBlockCloseDecodedCostedWithRankSeed` threads it: the
seed is the accepted `localBPSeedFromRankCloseCosted` value, never
reconstructed from window bits (preserving
`localBPWindowBits_alone_does_not_determine_base_excess`).
-/
def bpChunkedSameBlockCloseDecodedCostedWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize leftClose)
    fun seed =>
      bpChunkedSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed

/-- Literal all-size read bound for the charged decoded same-block close. -/
theorem bpChunkedSameBlockCloseDecodedCostedWithRankSeed_cost_le
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (bpChunkedSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).cost <= rankCost + 37 := by
  unfold bpChunkedSameBlockCloseDecodedCostedWithRankSeed
  have hseed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted blockSize
      leftClose rankCost hrankCost
  have hlocal :=
    bpChunkedSameBlockCloseSeededCosted_cost_le shape blockSize leftClose
      rightClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
        leftClose).value
  simp [Costed.bind] at hseed hlocal ⊢
  omega

/-- Decoded same-block value equivalence at the threaded rank seed. -/
theorem bpChunkedSameBlockCloseDecodedCostedWithRankSeed_value_eq
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose : Nat)
    (hvalid :
      BPFringeWindowValid (localBPWindowBits shape blockSize leftClose)
        (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
          leftClose).value)
    (hstart :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hcov :
      leftClose + 1 + (rightClose - leftClose + 1) <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length + 1) :
    (bpChunkedSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).value =
      (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).value := by
  unfold bpChunkedSameBlockCloseDecodedCostedWithRankSeed
  unfold localBPSameBlockCloseDecodedCostedWithRankSeed
  simp only [Costed.bind]
  exact
    bpChunkedSameBlockCloseSeededCosted_value_eq shape blockSize leftClose
      rightClose _ hvalid hstart hcov

/-! ## Adversarial table-corruption witness (same-block value dependency)

Corrupting one stored table entry that the charged same-block fold actually
reads changes the returned `Option Nat` CLOSE — not merely the internal
min-excess and not the trace log.  Read index `11` is exactly the slot the
witness invocation reads (`hslot` below), so the corrupted entry lies in the
actual same-block charged read footprint.

This strengthens B2's `bpFringeChunkTable_corruption_changes_fringe_value`,
whose corruption moves the min-excess component but leaves the argmin
POSITION at `0`, so it does not by itself move a close.  The witness here is
stated through the same-block leaf's own projection
`bpCandidateClose? (bpFringeCandGlobal base seed start _)`.
-/

def bpFringeSameBlockCorruptedEntriesWitness : List Nat :=
  (bpFringeChunkEntries 2).set 11 2

def bpFringeSameBlockCorruptedTableWitness :
    SuccinctSpace.FixedWidthNatTable bpFringeSameBlockCorruptedEntriesWitness
      (bpFringeChunkEntryWidth 2) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries _ _ (by
    intro entry hmem
    rcases List.mem_or_eq_of_mem_set hmem with hmem' | rfl
    · exact bpFringeChunkEntries_mem_lt_two_pow_width hmem'
    · exact Nat.lt_trans
        (show (2 : Nat) < bpFringeChunkEntryBound 2 by decide)
        (bpFringeChunkEntryBound_lt_two_pow_width 2))

theorem bpFringeChunkTable_corruption_changes_sameBlock_close_value :
    bpCandidateClose?
        (bpFringeCandGlobal 0 1 1
          (bpFringeChunkFoldCosted (bpFringeChunkTable 2) 2 [true, false] 1 0
            1 1).value.2) ≠
      bpCandidateClose?
        (bpFringeCandGlobal 0 1 1
          (bpFringeChunkFoldCosted bpFringeSameBlockCorruptedTableWitness 2
            [true, false] 1 0 1 1).value.2) := by
  have hhonest :
      (bpFringeChunkFoldCosted (bpFringeChunkTable 2) 2 [true, false] 1 0 1
          1).value.2 = some (1, 0) := by
    rw [bpFringeChunkFoldCosted_value]
    decide
  have hslot :
      bpFringeChunkSlot 2 (bpFringeWindowChunkValue 2 [true, false] 0)
        (bpFringeChunkStartOff 2 0 0) (bpFringeChunkEndOff 2 1 0) = 11 := by
    decide
  have hget : bpFringeSameBlockCorruptedEntriesWitness[11]? = some 2 := by
    decide
  have hread :
      (bpFringeSameBlockCorruptedTableWitness.readCosted 11).value = some 2 := by
    have h :=
      SuccinctSpace.FixedWidthNatTable.readCosted_erase
        bpFringeSameBlockCorruptedTableWitness 11
    rw [hget] at h
    exact h
  have hv :
      (bpFringeChunkFoldCosted bpFringeSameBlockCorruptedTableWitness 2
          [true, false] 1 0 1 1).value =
        bpFringeChunkStepDecoded 2 0 1 0 (1, none)
          ((bpFringeSameBlockCorruptedTableWitness.readCosted
            (bpFringeChunkSlot 2 (bpFringeWindowChunkValue 2 [true, false] 0)
              (bpFringeChunkStartOff 2 0 0)
              (bpFringeChunkEndOff 2 1 0))).value) := rfl
  have hcorrupt :
      (bpFringeChunkFoldCosted bpFringeSameBlockCorruptedTableWitness 2
          [true, false] 1 0 1 1).value.2 = some (0, 2) := by
    rw [hv, hslot, hread]
    decide
  rw [hhonest, hcorrupt]
  decide

end SuccinctClose

end RMQ
