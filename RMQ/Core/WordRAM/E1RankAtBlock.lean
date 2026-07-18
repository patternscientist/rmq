import RMQ.Core.WordRAM.E1RankBlock

/-!
# E1 amended machine: atomic in-word rank fold block (M3c-4b)

The seed-free rank fold sub-block for the dense two-word select leg
(worklog RESUME step 1, "atomic-fold variant"): the accepted dense leg
(`bpChunkedDenseTwoWordSelectTraceResultWithStore`,
`ChargedRankSelectLeafTrace.lean:575`) runs TWO bare
`bpChunkedWordRankTraceResultAtSegmentWithStore store S c target word
limit` folds whose inputs (decoded word, effective limit) arrive in
registers from the surrounding leg, not from seed reads.  This module
provides:

* `rankFalseLoopFold_runsTo` — the FALSE-target chunk-fold loop
  (`rankLoopBody` re-used from `E1RankBlock`) re-proved at a GENERIC loop
  base `LB` (the monolithic block pinned it at `B + 30`) and with the
  preservation widened to the loop's exact write-set complement
  (`r <= 8 ∨ 10 <= r <= 16 ∨ 24 <= r <= 26 ∨ 28 <= r`) — the dense leg
  must keep the decoded word (`rWrd`) and the sample registers across a
  fold;
* `rankAtSegmentBlock A G c` — 32 instructions at block base `A`: a
  7-instruction register-input init (zero cursor/accumulator, 8-capped
  chunk count from the effective limit in `rE`) followed by the loop
  (`A+7..A+30`) and back edge (`A+31`, target `A+7`);
* `rankAtSegmentBlock_runsTo` — exact-fuel simulation against the
  accepted atomic fold: receipts positionally equal to
  `(bpChunkedWordRankTraceResultAtSegmentWithStore store (G+4) c false w
  limit).trace`, value in `rVal`, frozen categories
  `rankAtSegmentCats` (derived length `7 + 25 * count`), write-set
  complement preserved;
* width certificate `rankAtSegmentBlock_fits`.

Inputs expected in registers at block entry: pinned constants
`rOne = 1`, `rC = c`, `rEight = 8`; effective limit
`rE = bpWordRankEffLimit w limit`; decoded word `rR = bitsToNatLE w`.
The caller discharges the effective-limit equation from its word-length
facts (`limit <= w.length` gives `bpWordRankEffLimit w limit = limit`).
-/

namespace RMQ
namespace WordRAM
namespace E1RankAtBlock

open E1Machine
open E1RankBlock
open RMQ.SuccinctClose

/-! ## Block segments -/

/-- Register-input fold init: zero the cursor and accumulator, derive the
8-capped chunk count `min ((e-1)/c + 1) 8` from the effective limit in
`rE` by the subtraction chain. -/
def rankAtInit (c : Nat) : List Instr :=
  [ .const rJC 0
  , .const rVal 0
  , .sub rA rE rOne
  , .divConst rA rA c
  , .add rK rA rOne
  , .sub rB rK rEight
  , .sub rK rK rB ]

@[simp] theorem rankAtInit_length (c : Nat) :
    (rankAtInit c).length = 7 := rfl

/--
The atomic in-word FALSE-target rank fold block at block base `A`, chunk
table at segment `G + 4`, chunk width `c`.  Layout: init `A..A+6`, loop
`A+7..A+30` (the shared `rankLoopBody`), back edge at `A+31` (target
`A+7`), block exit `A+32`.
-/
def rankAtSegmentBlock (A G c : Nat) : List Instr :=
  rankAtInit c ++ (rankLoopBody G c ++ [Instr.brNZ rK (A + 7)])

@[simp] theorem rankAtSegmentBlock_length (A G c : Nat) :
    (rankAtSegmentBlock A G c).length = 32 := rfl

/-! ## Frozen category logs -/

/-- Categories charged by the register-input init. -/
def rankAtInitCats : List Category :=
  [ .registerWrite, .registerWrite, .arithmetic, .arithmetic, .arithmetic
  , .arithmetic, .arithmetic ]

@[simp] theorem rankAtInitCats_length : rankAtInitCats.length = 7 := rfl

/-- The full frozen category log of the atomic fold block at chunk count
`count` (per-pass log shared with the seeded false block). -/
def rankAtSegmentCats (count : Nat) : List Category :=
  rankAtInitCats ++ iterLog (fun _ => rankLoopPassCats) count

/-- Derived step total: `7 + 25 * count`. -/
theorem rankAtSegmentCats_length (count : Nat) :
    (rankAtSegmentCats count).length = 7 + 25 * count := by
  unfold rankAtSegmentCats
  rw [List.length_append, iterLog_const_length]
  simp
  omega

/-! ## Hosting bundle -/

/-- Peel the block's hosting fact into the init/loop hosting facts and the
back-edge fetch fact. -/
theorem rankAtSegmentBlock_hosting {program : E1Machine.Program}
    {A G c : Nat}
    (hhost : HostedAt program A (rankAtSegmentBlock A G c)) :
    HostedAt program A (rankAtInit c) ∧
    HostedAt program (A + 7) (rankLoopBody G c) ∧
    program[A + 31]? = some (.brNZ rK (A + 7)) := by
  have hR1 := HostedAt.append_right hhost
  have hR2 := HostedAt.append_right hR1
  exact
    ⟨ HostedAt.append_left hhost
    , HostedAt.append_left hR1
    , hR2.head ⟩

/-! ## Straightness certificate -/

theorem rankAtInit_straight (c : Nat) :
    forall instr, instr ∈ rankAtInit c -> instr.isStraight = true := by
  intro instr hi
  simp only [rankAtInit, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Shared symbolic-evaluation macros (module-local instances) -/

/-- Symbolic machine-state evaluation with this module's segments and the
shared register-bank numerals. -/
local macro "regs_eval" : tactic =>
  `(tactic| straight_eval [rankAtInit, rankLoopBody,
      rPos, rVal, rP, rWI, rSI, rE, rSup, rBlk, rWrd,
      rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/-- Destination-register evaluation for preservation side conditions. -/
local macro "writes_eval" : tactic =>
  `(tactic| straight_writes [rPos, rVal, rP, rWI, rSI, rE, rSup,
      rBlk, rWrd, rR, rK, rT, rV, rSlot, rA, rB, rOne, rC, rEight, rJC])

/-! ## Loop simulation (FALSE-target chunk fold at a generic loop base) -/

/--
FALSE-target chunk-fold loop at a generic loop base `LB`: the seeded
block's loop simulation (`rankCloseBlock_loop_runsTo`) restated with the
loop base free and the preservation widened to the loop's exact write-set
complement.  From the loop entry with the fold registers initialized, the
hosted loop body plus back edge run — with exact fuel — to `LB + 25`,
emitting exactly the fold's ascending chunk-table reads, charging `count`
copies of the frozen per-pass category log, and leaving the fold's literal
iterated accumulator in `rVal`.
-/
theorem rankFalseLoopFold_runsTo
    (store : ReadStore) {program : E1Machine.Program} {LB G c : Nat}
    (hLoop : HostedAt program LB (rankLoopBody G c))
    (hbrL : program[LB + 24]? = some (.brNZ rK LB))
    (w : List Bool) (e : Nat) (regsL : RegFile)
    (hOne : regsL rOne = 1) (hC : regsL rC = c) (hE : regsL rE = e)
    (hR : regsL rR = SuccinctSpace.bitsToNatLE w)
    (hJC : regsL rJC = 0) (hVal : regsL rVal = 0)
    (hK : regsL rK = bpWordChunkCount c e) :
    ∃ regs6 : RegFile,
      RunsTo store program ⟨regsL, LB, false⟩ ⟨regs6, LB + 25, false⟩
        ((List.range (bpWordChunkCount c e)).map
          (fun j => bpWordRankChunkEventAt store (G + 4) c w e j))
        (iterLog (fun _ => rankLoopPassCats) (bpWordChunkCount c e)) ∧
      regs6 rVal =
        bpWordRankAccAt store (G + 4) c false w e (bpWordChunkCount c e) ∧
      (forall r, r <= 8 ∨ (10 <= r ∧ r <= 16) ∨ (24 <= r ∧ r <= 26) ∨
          28 <= r ->
        regs6 r = regsL r) := by
  have hcpos : 1 <= bpWordChunkCount c e := by
    rw [bpWordChunkCount_eq_sub]
    generalize (e - 1) / c = q
    omega
  -- loop invariant, indexed by the remaining iteration count
  let count := bpWordChunkCount c e
  let P : Nat -> State -> Prop := fun k s =>
    k <= count ∧ s.halted = false ∧
    s.pc = (if k = 0 then LB + 25 else LB) ∧
    s.regs rOne = 1 ∧ s.regs rC = c ∧ s.regs rE = e ∧
    s.regs rR = SuccinctSpace.bitsToNatLE w / 2 ^ ((count - k) * c) ∧
    s.regs rJC = (count - k) * c ∧
    s.regs rVal =
      bpWordRankAccAt store (G + 4) c false w e (count - k) ∧
    s.regs rK = k ∧
    (forall r, r <= 8 ∨ (10 <= r ∧ r <= 16) ∨ (24 <= r ∧ r <= 26) ∨
        28 <= r ->
      s.regs r = regsL r)
  have hstep : forall k s, P (k + 1) s ->
      ∃ s', RunsTo store program s s'
          [bpWordRankChunkEventAt store (G + 4) c w e (count - (k + 1))]
          rankLoopPassCats ∧ P k s' := by
    intro k s hP
    obtain ⟨regs, pc, halted⟩ := s
    obtain ⟨hkle, hhalt, hpc, hone, hc, he, hr, hjc, hval, hk, hpres⟩ := hP
    simp only at hhalt hpc hone hc he hr hjc hval hk hpres
    subst hhalt
    have hpcEq : (if k + 1 = 0 then LB + 25 else LB) = LB :=
      if_neg (Nat.succ_ne_zero k)
    rw [hpcEq] at hpc
    subst pc
    have hik : count - k = (count - (k + 1)) + 1 := by omega
    -- body straight run
    have hbody := RunsTo.straight store (rankLoopBody G c)
      (rankLoopBody_straight G c) LB hLoop regs
    obtain ⟨regsB, hregsB⟩ :
        ∃ x, straightRegs store (rankLoopBody G c) regs = x := ⟨_, rfl⟩
    rw [hregsB] at hbody
    -- receipts of one pass
    have hreadsB : straightReads store (rankLoopBody G c) regs =
        [bpWordRankChunkEventAt store (G + 4) c w e (count - (k + 1))] := by
      regs_eval <;>
        simp [hc, he, hjc, hr, bpWordRankChunkEventAt,
          bpWordRankChunkSlotAt, bpFringeChunkSlot,
          bpWordChunkSliceLen_eq_sub, bpFringeWindowChunkValue_eq_div_mod,
          nat_mod_eq_sub_div_mul]
    rw [hreadsB] at hbody
    -- invariant registers after the body
    have hBOne : regsB rOne = 1 := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact hone
    have hBC : regsB rC = c := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact hc
    have hBE : regsB rE = e := by
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval)]
      exact he
    have hBR : regsB rR =
        SuccinctSpace.bitsToNatLE w / 2 ^ ((count - k) * c) := by
      rw [<- hregsB, hik]
      regs_eval <;> simp [hr]
      exact div_pow_chunk_succ _ _ _
    have hBJC : regsB rJC = (count - k) * c := by
      rw [<- hregsB, hik]
      regs_eval <;> simp [hjc, hc]
      rw [Nat.succ_mul]
    have hBVal : regsB rVal =
        bpWordRankAccAt store (G + 4) c false w e (count - k) := by
      rw [<- hregsB, hik]
      regs_eval <;>
        simp [hval, hone, hc, he, hjc, hr, bpWordRankAccAt,
          bpWordRankStepDecoded, bpChunkRankOfEntry_false_eq,
          decodeRead_pred_eq_map_getD, bpWordRankChunkSlotAt,
          bpFringeChunkSlot, bpWordChunkSliceLen_eq_sub,
          bpFringeWindowChunkValue_eq_div_mod, nat_mod_eq_sub_div_mul]
    have hBK : regsB rK = k := by
      rw [<- hregsB]
      regs_eval <;> simp [hk, hone]
    have hBpres : forall r, r <= 8 ∨ (10 <= r ∧ r <= 16) ∨
        (24 <= r ∧ r <= 26) ∨ 28 <= r ->
        regsB r = regsL r := by
      intro r hrcond
      rw [<- hregsB]
      rw [straightRegs_preserves store _ _ _ (by
        intro i hi
        simp only [rankLoopBody, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> writes_eval <;> omega)]
      exact hpres r hrcond
    -- back edge
    by_cases hk0 : k = 0
    · subst hk0
      have hbr := RunsTo.brNZ_not_taken (store := store)
        (s := ⟨regsB, LB + 24, false⟩) rfl hbrL (by simpa using hBK)
      refine ⟨⟨regsB, LB + 25, false⟩, hbody.trans hbr, ?_⟩
      refine ⟨Nat.zero_le _, rfl, by simp, hBOne, hBC, hBE, ?_, ?_, ?_,
        ?_, hBpres⟩
      · simpa using hBR
      · simpa using hBJC
      · simpa using hBVal
      · simpa using hBK
    · have hbr := RunsTo.brNZ_taken (store := store)
        (s := ⟨regsB, LB + 24, false⟩) rfl hbrL (by
          rw [show (⟨regsB, LB + 24, false⟩ : State).regs = regsB from rfl,
            hBK]
          exact hk0)
      refine ⟨⟨regsB, LB, false⟩, hbody.trans hbr, ?_⟩
      refine ⟨by omega, rfl, by simp [hk0], hBOne, hBC, hBE, hBR, hBJC,
        hBVal, hBK, hBpres⟩
  -- start state satisfies the invariant at the full count
  have hstart : P count ⟨regsL, LB, false⟩ := by
    refine ⟨Nat.le_refl _, rfl, ?_, hOne, hC, hE, ?_, ?_, ?_, hK,
      fun r _ => rfl⟩
    · have : count ≠ 0 := by omega
      simp [this]
    · simp [Nat.sub_self, hR]
    · simp [Nat.sub_self, hJC]
    · simp [Nat.sub_self, hVal, bpWordRankAccAt]
  obtain ⟨sEnd, hloopRun, hPEnd⟩ :=
    RunsTo.iterate P
      (fun k => [bpWordRankChunkEventAt store (G + 4) c w e
        (count - (k + 1))])
      (fun _ => rankLoopPassCats) hstep count ⟨regsL, LB, false⟩ hstart
  obtain ⟨regsE, pcE, haltE⟩ := sEnd
  obtain ⟨_, hEhalt, hEpc, _, _, _, _, _, hEVal, _, hEpres⟩ := hPEnd
  simp only at hEhalt hEpc hEVal hEpres
  subst hEhalt
  simp at hEpc
  subst hEpc
  -- receipts in ascending chunk order
  have hreadsIter :
      iterLog (fun k => [bpWordRankChunkEventAt store (G + 4) c w e
        (count - (k + 1))]) count =
      (List.range count).map
        (fun j => bpWordRankChunkEventAt store (G + 4) c w e j) := by
    have h1 : iterLog (fun k => [bpWordRankChunkEventAt store (G + 4) c
        w e (count - (k + 1))]) count =
        iterLog (fun k => [bpWordRankChunkEventAt store (G + 4) c w e
          (0 + (count - (k + 1)))]) count := by
      apply iterLog_congr
      intro kk _
      rw [Nat.zero_add]
    rw [h1, iterLog_singleton_desc]
    apply List.map_congr_left
    intro dd _
    rw [Nat.zero_add]
  rw [hreadsIter] at hloopRun
  exact ⟨regsE, hloopRun, by simpa using hEVal, hEpres⟩

/-! ## Whole-block simulation against the accepted atomic fold -/

/--
Exact-fuel simulation of the accepted atomic in-word FALSE-target rank
fold: from block entry with the pinned constants, the effective limit in
`rE`, and the decoded word in `rR`, the hosted block runs to the block
exit at `A + 32` with

* receipts POSITIONALLY EQUAL to
  `(bpChunkedWordRankTraceResultAtSegmentWithStore store (G+4) c false w
  limit).trace`,
* that fold's value in `rVal`,
* the frozen category log `rankAtSegmentCats count` (derived length
  `7 + 25 * count`, `count <= 8`), and
* every register outside the fold's write set (`r <= 8`,
  `10 <= r <= 16`, `24 <= r <= 26`, or `28 <= r`) preserved.
-/
theorem rankAtSegmentBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A G c : Nat}
    (hhost : HostedAt program A (rankAtSegmentBlock A G c))
    (regsA : RegFile) (w : List Bool) (limit : Nat)
    (hOne : regsA rOne = 1) (hC : regsA rC = c)
    (hEight : regsA rEight = 8)
    (hE : regsA rE = bpWordRankEffLimit w limit)
    (hR : regsA rR = SuccinctSpace.bitsToNatLE w) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regsA, A, false⟩ ⟨regsF, A + 32, false⟩
        (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
          false w limit).trace
        (rankAtSegmentCats
          (bpWordChunkCount c (bpWordRankEffLimit w limit))) ∧
      regsF rVal =
        (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
          false w limit).value ∧
      (forall r, r <= 8 ∨ (10 <= r ∧ r <= 16) ∨ (24 <= r ∧ r <= 26) ∨
          28 <= r ->
        regsF r = regsA r) := by
  obtain ⟨hInit, hLoop, hbr⟩ := rankAtSegmentBlock_hosting hhost
  -- init segment
  have hrunInit := RunsTo.straight store (rankAtInit c)
    (rankAtInit_straight c) A hInit regsA
  obtain ⟨regsI, hregsI⟩ :
      ∃ x, straightRegs store (rankAtInit c) regsA = x := ⟨_, rfl⟩
  rw [hregsI] at hrunInit
  have hreadsInit : straightReads store (rankAtInit c) regsA = [] := by
    simp [rankAtInit, straightReads_cons, straightStepEvent]
  rw [hreadsInit] at hrunInit
  have hIpresRead : forall r, r ≠ 22 ∧ r ≠ 23 ∧ r ≠ 18 ∧ r ≠ 27 ∧
      r ≠ 9 -> regsI r = regsA r := by
    intro r hrcond
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrcond
    rw [<- hregsI]
    apply straightRegs_preserves
    intro i hi
    simp only [rankAtInit, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      writes_eval <;> omega
  have hIOne : regsI rOne = 1 := by
    rw [hIpresRead rOne (by decide)]
    exact hOne
  have hIC : regsI rC = c := by
    rw [hIpresRead rC (by decide)]
    exact hC
  have hIE : regsI rE = bpWordRankEffLimit w limit := by
    rw [hIpresRead rE (by decide)]
    exact hE
  have hIR : regsI rR = SuccinctSpace.bitsToNatLE w := by
    rw [hIpresRead rR (by decide)]
    exact hR
  have hIJC : regsI rJC = 0 := by
    rw [<- hregsI]
    regs_eval
  have hIVal : regsI rVal = 0 := by
    rw [<- hregsI]
    regs_eval
  have hIK : regsI rK =
      bpWordChunkCount c (bpWordRankEffLimit w limit) := by
    rw [<- hregsI, bpWordChunkCount_eq_sub]
    regs_eval <;> simp [hE, hOne, hEight]
  have hIpres : forall r, r <= 8 ∨ (10 <= r ∧ r <= 16) ∨
      (24 <= r ∧ r <= 26) ∨ 28 <= r -> regsI r = regsA r := by
    intro r hrcond
    rw [<- hregsI]
    apply straightRegs_preserves
    intro i hi
    simp only [rankAtInit, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      writes_eval <;> omega
  -- loop at base A + 7
  have hbr' : program[A + 7 + 24]? = some (.brNZ rK (A + 7)) := by
    rw [show A + 7 + 24 = A + 31 from by omega]
    exact hbr
  obtain ⟨regs6, hloop, h6Val, h6pres⟩ :=
    rankFalseLoopFold_runsTo store hLoop hbr' w
      (bpWordRankEffLimit w limit) regsI hIOne hIC hIE hIR hIJC hIVal hIK
  rw [show A + 7 + 25 = A + 32 from by omega] at hloop
  have hall := hrunInit.trans hloop
  -- accepted fold trace and value
  have htrace :
      (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
          false w limit).trace =
        (List.range (bpWordChunkCount c (bpWordRankEffLimit w limit))).map
          (fun j => bpWordRankChunkEventAt store (G + 4) c w
            (bpWordRankEffLimit w limit) j) := by
    simp only [bpChunkedWordRankTraceResultAtSegmentWithStore]
    rw [bpChunkedWordRankTraceFromWithStore_trace_map]
    apply List.map_congr_left
    intro d _
    rw [Nat.zero_add]
  have hvalue :
      (bpChunkedWordRankTraceResultAtSegmentWithStore store (G + 4) c
          false w limit).value =
        bpWordRankAccAt store (G + 4) c false w
          (bpWordRankEffLimit w limit)
          (bpWordChunkCount c (bpWordRankEffLimit w limit)) := by
    simp only [bpChunkedWordRankTraceResultAtSegmentWithStore]
    have h := bpChunkedWordRankTraceFromWithStore_value_accAt store
      (G + 4) c false w (bpWordRankEffLimit w limit)
      (bpWordChunkCount c (bpWordRankEffLimit w limit)) 0
    simpa [bpWordRankAccAt] using h
  refine ⟨regs6, ?_, ?_, ?_⟩
  · rw [htrace]
    have hcats : rankAtSegmentCats
        (bpWordChunkCount c (bpWordRankEffLimit w limit)) =
        (rankAtInit c).map Instr.category ++
          iterLog (fun _ => rankLoopPassCats)
            (bpWordChunkCount c (bpWordRankEffLimit w limit)) := by
      simp [rankAtSegmentCats, rankAtInitCats, rankAtInit, Instr.category]
    rw [hcats]
    have hreads :
        ((List.range (bpWordChunkCount c
            (bpWordRankEffLimit w limit))).map
          (fun j => bpWordRankChunkEventAt store (G + 4) c w
            (bpWordRankEffLimit w limit) j)) =
        [] ++
          (List.range (bpWordChunkCount c
            (bpWordRankEffLimit w limit))).map
            (fun j => bpWordRankChunkEventAt store (G + 4) c w
              (bpWordRankEffLimit w limit) j) := by
      simp
    rw [hreads]
    exact hall
  · rw [hvalue]
    exact h6Val
  · intro r hrcond
    rw [h6pres r hrcond]
    exact hIpres r hrcond

/-! ## Width certificate (REQ-E1-02 consumption for this block) -/

/--
Constructor-exhaustive width certificate for the atomic fold block: every
encoded field — register identifiers (bank `8..27`), the chunk-table
segment `G + 4`, the immediate `0`, the multiplier/divisor constants
`2^c`/`c+1`/`2*c+2`/`2`/`c`, and the branch target `A + 7` — fits the
modeled width `w`, with the variable divisor `c` positive.
-/
theorem rankAtSegmentBlock_fits {w A G c : Nat}
    (hreg : 28 ≤ 2 ^ w) (hG : G + 4 < 2 ^ w) (hcpos : 0 < c)
    (hpow : 2 ^ c < 2 ^ w) (hlin : 2 * c + 2 < 2 ^ w)
    (hA : A + 32 < 2 ^ w) :
    ∀ instr ∈ rankAtSegmentBlock A G c, instr.FieldsFit w := by
  have hppos : 0 < 2 ^ c := Nat.pow_pos (by omega)
  intro instr hmem
  simp only [rankAtSegmentBlock, rankAtInit, rankLoopBody,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl <;>
    simp only [Instr.FieldsFit, rVal, rE, rR, rK, rT, rV, rSlot,
      rA, rB, rOne, rC, rEight, rJC] <;>
    omega

end E1RankAtBlock
end WordRAM
end RMQ
