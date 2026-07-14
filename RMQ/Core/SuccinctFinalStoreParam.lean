import RMQ.Core.SuccinctFinalRAM
import RMQ.Core.WordRAM.ReadStoreEval
import RMQ.Core.GenericSelect.RAMStoreParam
import RMQ.Core.SuccinctClose.RelativeRmmMacro.ConcreteDirectoryRAMStoreParam

/-!
# Store-parametric leaves for the final RMQ whole-query trace

The globally segmented final-query trace (`SuccinctFinalRAM`) evaluates each
leaf against its component-local store and relabels the trace into the global
segment layout.  The store-extensional theorem there is therefore weak: value
and cost do not depend on the supplied store.

This file starts the genuine store-parameterized replay.  Each leaf gets a
`WithStore` evaluator whose reads and value are produced from a supplied
`WordRAM.ReadStore` pulled back along the leaf's segment map, together with:

* `_matchesReadStore` — for **every** store, the emitted read events report
  exactly that store's words (the by-construction anti-oracle clause);
* an agreement theorem — with the concrete global read store the evaluator is
  literally the canonical leaf trace, so exactness and cost transfer; and
* `_store_parametric` — two stores agreeing on the leaf's mapped segments
  produce the same value and trace.
-/

namespace RMQ

namespace SuccinctFinal

/-- Segment map placing the final false-rank component's three local segments
at a supplied base. -/
def concreteBPNativeRankCloseSegmentMap (rankSegmentBase : Nat) :
    Nat -> Nat :=
  WordRAM.tripleSegmentMap rankSegmentBase concreteBPNativeDeadTraceSegment

/--
The concrete global read store, pulled back along the final false-rank segment
map, is exactly the rank component's local store.
-/
theorem concreteBPNativeRankClose_pullback_globalReadStore
    (shape : Cartesian.CartesianShape) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (concreteBPNativeRankCloseSegmentMap
          concreteBPNativeRankCloseTraceSegmentBase) =
      WordRAM.ReadStore.ofStore
        ((builtRelativeSplitBPCloseRankData shape).rankRegisterWordRAMStore
          false) := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | _ | _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeRankCloseSegmentMap,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeRankCloseTraceSegmentBase,
      concreteBPNativeDeadTraceSegment,
      WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?]

private theorem natProgram_evalR_eq_of_trace_read_agreement
    (program : WordRAM.Register.NatProgram)
    (storeA storeB : WordRAM.ReadStore)
    (regs : WordRAM.Register.RegFile)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
            (program.evalR storeA regs).trace ->
          storeA.readWord? segment index = storeB.readWord? segment index) :
    program.evalR storeA regs = program.evalR storeB regs := by
  cases program with
  | pureNat value =>
      rfl
  | sampledRank target offset sampleSegment sampleIndex wordSegment wordIndex =>
      let sampleI := sampleIndex.eval regs
      let wordI := wordIndex.eval regs
      have hsample :
          storeA.readWord? sampleSegment sampleI =
            storeB.readWord? sampleSegment sampleI := by
        apply hagree sampleSegment sampleI
          (storeA.readWord? sampleSegment sampleI)
        simp only [WordRAM.Register.NatProgram.evalR]
        generalize ha : storeA.readWord? sampleSegment sampleI = a
        generalize hw : storeA.readWord? wordSegment wordI = w
        cases a <;> cases w <;>
          exact List.Mem.head _
      have hword :
          storeA.readWord? wordSegment wordI =
            storeB.readWord? wordSegment wordI := by
        apply hagree wordSegment wordI
          (storeA.readWord? wordSegment wordI)
        simp only [WordRAM.Register.NatProgram.evalR]
        generalize ha : storeA.readWord? sampleSegment sampleI = a
        generalize hw : storeA.readWord? wordSegment wordI = w
        cases a <;> cases w <;>
          exact List.Mem.tail _ (List.Mem.head _)
      simp [WordRAM.Register.NatProgram.evalR, sampleI, wordI,
        hsample, hword]
  | twoLevelSampledRank target offset superSegment superIndex blockSegment
      blockIndex wordSegment wordIndex =>
      let superI := superIndex.eval regs
      let blockI := blockIndex.eval regs
      let wordI := wordIndex.eval regs
      have hsuper :
          storeA.readWord? superSegment superI =
            storeB.readWord? superSegment superI := by
        apply hagree superSegment superI
          (storeA.readWord? superSegment superI)
        simp only [WordRAM.Register.NatProgram.evalR]
        generalize hs : storeA.readWord? superSegment superI = s
        generalize hb : storeA.readWord? blockSegment blockI = b
        generalize hw : storeA.readWord? wordSegment wordI = w
        cases s <;> cases b <;> cases w <;>
          exact List.Mem.head _
      have hblock :
          storeA.readWord? blockSegment blockI =
            storeB.readWord? blockSegment blockI := by
        apply hagree blockSegment blockI
          (storeA.readWord? blockSegment blockI)
        simp only [WordRAM.Register.NatProgram.evalR]
        generalize hs : storeA.readWord? superSegment superI = s
        generalize hb : storeA.readWord? blockSegment blockI = b
        generalize hw : storeA.readWord? wordSegment wordI = w
        cases s <;> cases b <;> cases w <;>
          exact List.Mem.tail _ (List.Mem.head _)
      have hword :
          storeA.readWord? wordSegment wordI =
            storeB.readWord? wordSegment wordI := by
        apply hagree wordSegment wordI
          (storeA.readWord? wordSegment wordI)
        simp only [WordRAM.Register.NatProgram.evalR]
        generalize hs : storeA.readWord? superSegment superI = s
        generalize hb : storeA.readWord? blockSegment blockI = b
        generalize hw : storeA.readWord? wordSegment wordI = w
        cases s <;> cases b <;> cases w <;>
          exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      simp [WordRAM.Register.NatProgram.evalR, superI, blockI, wordI,
        hsuper, hblock, hword]

private theorem program_evalR_eq_of_trace_read_agreement
    {ty : WordRAM.Ty} (program : WordRAM.Program ty)
    (storeA storeB : WordRAM.ReadStore)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
            (program.evalR storeA).trace ->
          storeA.readWord? segment index = storeB.readWord? segment index) :
    program.evalR storeA = program.evalR storeB := by
  induction program generalizing storeA storeB with
  | pure value => rfl
  | readWord segment index =>
      have hread := hagree segment index (storeA.readWord? segment index)
        (List.Mem.head [])
      simp [WordRAM.Program.evalR, hread]
  | mapOptWordNat program ih =>
      have hp := ih storeA storeB (by
        intro segment index word? hmem
        apply hagree segment index word?
        simpa [WordRAM.Program.evalR] using hmem)
      simp [WordRAM.Program.evalR, hp]
  | mapOptWordOptionNat width program ih =>
      have hp := ih storeA storeB (by
        intro segment index word? hmem
        apply hagree segment index word?
        simpa [WordRAM.Program.evalR] using hmem)
      simp [WordRAM.Program.evalR, hp]
  | joinOptOptNat program ih =>
      have hp := ih storeA storeB (by
        intro segment index word? hmem
        apply hagree segment index word?
        simpa [WordRAM.Program.evalR] using hmem)
      simp [WordRAM.Program.evalR, hp]
  | sampledRank target offset sample word sampleIH wordIH =>
      have hsample := sampleIH storeA storeB (by
        intro segment index word? hmem
        apply hagree segment index word?
        cases hs : (sample.evalR storeA).value with
        | none =>
            cases hw : (word.evalR storeA).value <;>
              simp only [WordRAM.Program.evalR, hs, hw] <;>
              exact List.mem_append_left _ hmem
        | some sampleValue =>
            cases hw : (word.evalR storeA).value with
            | none =>
                simp only [WordRAM.Program.evalR, hs, hw]
                exact List.mem_append_left _ hmem
            | some wordValue =>
                simp only [WordRAM.Program.evalR, hs, hw]
                exact List.mem_append_left _
                  (List.mem_append_left _ hmem))
      have hword := wordIH storeA storeB (by
        intro segment index word? hmem
        apply hagree segment index word?
        cases hs : (sample.evalR storeA).value with
        | none =>
            cases hw : (word.evalR storeA).value <;>
              simp only [WordRAM.Program.evalR, hs, hw] <;>
              exact List.mem_append_right _ hmem
        | some sampleValue =>
            cases hw : (word.evalR storeA).value with
            | none =>
                simp only [WordRAM.Program.evalR, hs, hw]
                exact List.mem_append_right _ hmem
            | some wordValue =>
                simp only [WordRAM.Program.evalR, hs, hw]
                exact List.mem_append_left _
                  (List.mem_append_right _ hmem))
      simp [WordRAM.Program.evalR, hsample, hword]
  | wordSelectFromOpt target occurrence word wordIH =>
      have hword := wordIH storeA storeB (by
        intro segment index word? hmem
        apply hagree segment index word?
        cases hw : (word.evalR storeA).value with
        | none =>
            simpa [WordRAM.Program.evalR, hw] using hmem
        | some value =>
            simp only [WordRAM.Program.evalR, hw]
            exact List.mem_append_left _ hmem)
      simp [WordRAM.Program.evalR, hword]

private def StoreTraceLocal {alpha : Type}
    (eval : WordRAM.ReadStore -> WordRAM.TraceResult alpha) : Prop :=
  forall storeA storeB,
    (forall segment index word?,
      List.Mem (WordRAM.TraceEvent.readWord segment index word?)
          (eval storeA).trace ->
        storeA.readWord? segment index = storeB.readWord? segment index) ->
    eval storeA = eval storeB

private theorem storeTraceLocal_const {alpha : Type}
    (result : WordRAM.TraceResult alpha) :
    StoreTraceLocal (fun _store => result) := by
  intro storeA storeB hagree
  rfl

private theorem storeTraceLocal_map {alpha beta : Type}
    (eval : WordRAM.ReadStore -> WordRAM.TraceResult alpha)
    (hlocal : StoreTraceLocal eval) (f : alpha -> beta) :
    StoreTraceLocal (fun store => WordRAM.TraceResult.map f (eval store)) := by
  intro storeA storeB hagree
  have heval := hlocal storeA storeB (by
    intro segment index word? hmem
    apply hagree segment index word?
    simpa [WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
      WordRAM.TraceResult.pure] using hmem)
  change WordRAM.TraceResult.map f (eval storeA) =
    WordRAM.TraceResult.map f (eval storeB)
  exact congrArg (WordRAM.TraceResult.map f) heval

private theorem storeTraceLocal_bind {alpha beta : Type}
    (eval : WordRAM.ReadStore -> WordRAM.TraceResult alpha)
    (next : alpha -> WordRAM.ReadStore -> WordRAM.TraceResult beta)
    (heval : StoreTraceLocal eval)
    (hnext : forall value, StoreTraceLocal (next value)) :
    StoreTraceLocal (fun store =>
      WordRAM.TraceResult.bind (eval store) (fun value => next value store)) := by
  intro storeA storeB hagree
  have hevalEq := heval storeA storeB (by
    intro segment index word? hmem
    apply hagree segment index word?
    simp only [WordRAM.TraceResult.bind]
    exact List.mem_append_left _ hmem)
  have hnextEq := hnext (eval storeA).value storeA storeB (by
    intro segment index word? hmem
    apply hagree segment index word?
    simp only [WordRAM.TraceResult.bind]
    exact List.mem_append_right _ hmem)
  have hnextEqB :
      next (eval storeB).value storeA = next (eval storeB).value storeB := by
    simpa [hevalEq] using hnextEq
  change WordRAM.TraceResult.bind (eval storeA) (fun value => next value storeA) =
    WordRAM.TraceResult.bind (eval storeB) (fun value => next value storeB)
  rw [hevalEq]
  simp only [WordRAM.TraceResult.bind]
  rw [hnextEqB]

private theorem storeTraceLocal_relabelReadSegmentsWith_pullback
    {alpha : Type} (segmentMap : Nat -> Nat)
    (eval : WordRAM.ReadStore -> WordRAM.TraceResult alpha)
    (hlocal : StoreTraceLocal eval) :
    StoreTraceLocal (fun store =>
      WordRAM.TraceResult.relabelReadSegmentsWith segmentMap
        (eval (store.pullback segmentMap))) := by
  intro storeA storeB hagree
  have hinner := hlocal
    (storeA.pullback segmentMap) (storeB.pullback segmentMap) (by
      intro segment index word? hmem
      have hglobal := hagree (segmentMap segment) index word? (by
        simp only [WordRAM.TraceResult.relabelReadSegmentsWith]
        apply List.mem_map.mpr
        exact ⟨WordRAM.TraceEvent.readWord segment index word?, hmem, by
          simp [WordRAM.TraceEvent.relabelReadSegmentWith]⟩)
      simpa [WordRAM.ReadStore.pullback] using hglobal)
  exact congrArg
    (WordRAM.TraceResult.relabelReadSegmentsWith segmentMap) hinner

private theorem ofResultProgram_storeTraceLocal
    {ty : WordRAM.Ty} (program : WordRAM.Program ty) :
    StoreTraceLocal (fun store =>
      WordRAM.TraceResult.ofResult (program.evalR store)) := by
  intro storeA storeB hagree
  exact congrArg WordRAM.TraceResult.ofResult
    (program_evalR_eq_of_trace_read_agreement program storeA storeB (by
      intro segment index word? hmem
      apply hagree segment index word?
      simpa [WordRAM.TraceResult.ofResult] using hmem))

private theorem ofProgramWithStore_storeTraceLocal
    (segmentMap : Nat -> Nat) {ty : WordRAM.Ty}
    (program : WordRAM.Program ty) :
    StoreTraceLocal (fun store =>
      WordRAM.TraceResult.ofProgramWithStore segmentMap store program) := by
  simpa [WordRAM.TraceResult.ofProgramWithStore] using
    storeTraceLocal_relabelReadSegmentsWith_pullback segmentMap
      (fun store => WordRAM.TraceResult.ofResult (program.evalR store))
      (ofResultProgram_storeTraceLocal program)

private theorem ofNatProgramWithStore_storeTraceLocal
    (segmentMap : Nat -> Nat) (program : WordRAM.Register.NatProgram)
    (regs : WordRAM.Register.RegFile) :
    StoreTraceLocal (fun store =>
      WordRAM.TraceResult.ofNatProgramWithStore segmentMap store program regs) := by
  have hinner : StoreTraceLocal (fun store =>
      WordRAM.TraceResult.ofResult (program.evalR store regs)) := by
    intro storeA storeB hagree
    exact congrArg WordRAM.TraceResult.ofResult
      (natProgram_evalR_eq_of_trace_read_agreement
        program storeA storeB regs (by
          intro segment index word? hmem
          apply hagree segment index word?
          simpa [WordRAM.TraceResult.ofResult] using hmem))
  simpa [WordRAM.TraceResult.ofNatProgramWithStore] using
    storeTraceLocal_relabelReadSegmentsWith_pullback segmentMap
      (fun store => WordRAM.TraceResult.ofResult (program.evalR store regs))
      hinner

/--
Store-parameterized final false-rank leaf: the two-level register rank program
is evaluated against the supplied read store pulled back along the rank segment
map, and the emitted trace is relabeled into the global layout.
-/
def concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat) : WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (concreteBPNativeRankCloseSegmentMap rankSegmentBase)
    (WordRAM.TraceResult.ofResult
      (((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
          false (WordRAM.Register.NatExpr.reg 0)).evalR
        (store.pullback
          (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
        (WordRAM.Register.RegFile.withNat1 pos)))

/-- For every supplied store, the store-parameterized rank leaf's read events
report exactly that store's words. -/
theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat) :
    forall event,
      List.Mem event
          (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
            shape store rankSegmentBase pos).trace ->
        event.matchesReadStore store := by
  intro event hmem
  simp only [concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
    WordRAM.TraceResult.relabelReadSegmentsWith,
    WordRAM.TraceResult.ofResult] at hmem
  rcases List.mem_map.mp hmem with ⟨inner, hinner, rfl⟩
  exact
    WordRAM.TraceEvent.relabelReadSegmentWith_matchesReadStore_of_pullback
      (concreteBPNativeRankCloseSegmentMap rankSegmentBase) store
      (WordRAM.Register.NatProgram.evalR_matchesReadStore
        ((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
          false (WordRAM.Register.NatExpr.reg 0))
        (store.pullback
          (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
        (WordRAM.Register.RegFile.withNat1 pos)
        inner hinner)

/--
With the concrete global read store, the store-parameterized rank leaf is
literally the canonical globally segmented rank leaf.
-/
theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase pos =
      concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase pos := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    concreteBPNativeRankCloseWordTraceResultAtSegment
    concreteBPNativeRankCloseWordTraceResult
  rw [concreteBPNativeRankClose_pullback_globalReadStore,
    WordRAM.Register.NatProgram.evalR_ofStore]
  rfl

/--
Whole-leaf parametricity: two read stores agreeing on the rank leaf's mapped
segments produce the same value and the same trace.
-/
theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (rankSegmentBase pos : Nat)
    (hread :
      forall segment index,
        storeA.readWord?
            (concreteBPNativeRankCloseSegmentMap rankSegmentBase segment)
            index =
          storeB.readWord?
            (concreteBPNativeRankCloseSegmentMap rankSegmentBase segment)
            index) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeA rankSegmentBase pos =
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeB rankSegmentBase pos := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [WordRAM.ReadStore.pullback_eq_of_agree_on_map
    (concreteBPNativeRankCloseSegmentMap rankSegmentBase) hread]

theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_eq_of_trace_read_agreement
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
            (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
              shape storeA rankSegmentBase pos).trace ->
          storeA.readWord? segment index = storeB.readWord? segment index) :
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeA rankSegmentBase pos =
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeB rankSegmentBase pos := by
  have hinner :=
    natProgram_evalR_eq_of_trace_read_agreement
      ((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
        false (WordRAM.Register.NatExpr.reg 0))
      (storeA.pullback
        (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
      (storeB.pullback
        (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
      (WordRAM.Register.RegFile.withNat1 pos)
      (by
        intro segment index word? hmem
        have hglobal := hagree
          (concreteBPNativeRankCloseSegmentMap rankSegmentBase segment)
          index word? (by
            simp only [
              concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore,
              WordRAM.TraceResult.relabelReadSegmentsWith,
              WordRAM.TraceResult.ofResult]
            apply List.mem_map.mpr
            refine ⟨WordRAM.TraceEvent.readWord segment index word?,
              hmem, ?_⟩
            simp [WordRAM.TraceEvent.relabelReadSegmentWith])
        simpa [WordRAM.ReadStore.pullback] using hglobal)
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [hinner]

/--
Store-parameterized positive same-block local-BP close leaf with the concrete
final false-rank seed.  Both the rank seed and the BP-code local window read
from the supplied global read store.
-/
def localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
  WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store concreteBPNativeRankCloseTraceSegmentBase)
      store blockSize leftClose rightClose

theorem localBPSameBlockCloseDecodedTraceResultWithFinalRankSeed_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (blockSize leftClose rightClose : Nat) :
    forall event,
      event ∈
          (localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
            shape store blockSize leftClose rightClose).trace ->
        event.matchesReadStore store := by
  unfold localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_matchesReadStore
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape store concreteBPNativeRankCloseTraceSegmentBase)
        store blockSize leftClose rightClose
        (fun pos event hmem =>
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
            shape store concreteBPNativeRankCloseTraceSegmentBase pos
            event hmem)

theorem localBPSameBlockCloseDecodedTraceResultWithFinalRankSeed_evalWithStore
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        blockSize leftClose rightClose =
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeed
          shape
          (concreteBPNativeRankCloseWordTraceResultAtSegment
            shape concreteBPNativeRankCloseTraceSegmentBase)
          blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
  have hrank :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore
        shape pos
  rw [hrank]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_eq_of_agree
        (concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase)
        (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape)
        blockSize leftClose rightClose

theorem localBPSameBlockCloseDecodedTraceResultWithFinalRankSeed_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hbp :
      forall index,
        storeA.readWord? 0 index = storeB.readWord? 0 index)
    (hrank :
      forall segment index,
        storeA.readWord?
            (concreteBPNativeRankCloseSegmentMap
              concreteBPNativeRankCloseTraceSegmentBase segment)
            index =
          storeB.readWord?
            (concreteBPNativeRankCloseSegmentMap
              concreteBPNativeRankCloseTraceSegmentBase segment)
            index)
    (blockSize leftClose rightClose : Nat) :
    localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
        shape storeA blockSize leftClose rightClose =
      localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
        shape storeB blockSize leftClose rightClose := by
  unfold localBPSameBlockCloseDecodedTraceResultWithFinalRankSeedWithStore
  have hrankTrace :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeA concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape storeB concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
        shape concreteBPNativeRankCloseTraceSegmentBase pos hrank
  rw [hrankTrace]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore_store_parametric
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape storeB concreteBPNativeRankCloseTraceSegmentBase)
        hbp blockSize leftClose rightClose

/--
Store-parameterized close-select leaf: the sparse-exception select tower
evaluated against a supplied read store under the final global segment layout.
-/
def concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) : WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    |>.selectTraceResultRelabeledWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout store idx

/-- For every supplied store, the store-parameterized close-select leaf's read
events report exactly that store's words. -/
theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
            shape store idx).trace ->
        event.matchesReadStore store := by
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_matchesReadStore
        concreteBPNativeSelectCloseTraceSegmentLayout store idx

section SelectClosePullbacks

variable (shape : Cartesian.CartesianShape)

private theorem selectClosePullback_superBaseOccurrence :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.baseOccurrenceTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_superBaseWordIndex :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.baseWordIndexTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_superRankBefore :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.rankBeforeTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_superFirstOffset :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).superTable.firstOffsetTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_localBaseOccurrence :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.baseOccurrenceTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_localBaseWordIndex :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.baseWordIndexTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_localRankBefore :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.rankBeforeTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_localFirstOffset :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
          concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).localTable.firstOffsetTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_longFlagRank :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment) =
      WordRAM.ReadStore.ofStore
        ((GenericSelect.sparseExceptionSelectData shape.bpCode
          false).longFlagRankData.rankRegisterWordRAMStore true) := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | _ | _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_longRelative :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).longSuperRelativeTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_sparseRank :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.tripleSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment) =
      WordRAM.ReadStore.ofStore
        ((GenericSelect.sparseExceptionSelectData shape.bpCode
          false).sparseDirectory.rankData.rankRegisterWordRAMStore true) := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | _ | _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.tripleSegmentMap, WordRAM.TraceEvent.tripleSegmentMap,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankRegisterWordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_sparseRelative :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
          concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).sparseDirectory.relativeTable.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.FixedWidthNatTable.wordRAMStore,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

private theorem selectClosePullback_bitWords :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).pullback
        (WordRAM.singletonSegmentMap
          concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
          concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment) =
      WordRAM.ReadStore.ofStore
        (GenericSelect.sparseExceptionSelectData shape.bpCode
          false).bitWords.store.wordRAMStore := by
  apply WordRAM.ReadStore.ext
  intro segment index
  rcases segment with _ | segment <;>
    simp [WordRAM.ReadStore.pullback, WordRAM.ReadStore.ofStore,
      concreteBPNativeSuccinctRMQGlobalReadStore,
      concreteBPNativeSelectCloseTraceSegmentLayout,
      concreteBPNativeDeadTraceSegment,
      WordRAM.singletonSegmentMap, WordRAM.TraceEvent.singletonSegmentMap,
      SuccinctSpace.PayloadWordStore.wordRAMStore,
      WordRAM.Store.readWord?]

end SelectClosePullbacks

/--
With the concrete global read store, the store-parameterized close-select leaf
is literally the canonical globally segmented close-select leaf.
-/
theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_globalReadStore
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape) idx =
      concreteBPNativeSelectCloseGlobalWordTraceResult shape idx := by
  unfold concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
    concreteBPNativeSelectCloseGlobalWordTraceResult
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_eq_of_pullback
        (selectClosePullback_superBaseOccurrence shape)
        (selectClosePullback_superBaseWordIndex shape)
        (selectClosePullback_superRankBefore shape)
        (selectClosePullback_superFirstOffset shape)
        (selectClosePullback_longFlagRank shape)
        (selectClosePullback_longRelative shape)
        (selectClosePullback_localBaseOccurrence shape)
        (selectClosePullback_localBaseWordIndex shape)
        (selectClosePullback_localRankBefore shape)
        (selectClosePullback_localFirstOffset shape)
        (selectClosePullback_sparseRank shape)
        (selectClosePullback_sparseRelative shape)
        (selectClosePullback_bitWords shape)
        idx

/--
Segment footprint for the supplied-store final whole-query replay.

This is a safe layout footprint, not the exact dynamic read set: it includes the
live final global segments `0..28` plus the dead sentinel segment `29` required
by the existing finite segment maps.
-/
def concreteBPNativeSuccinctRMQWholeQueryReadFootprint
    (_shape : Cartesian.CartesianShape) (segment : Nat) : Prop :=
  segment <= concreteBPNativeDeadTraceSegment

/-- Two read stores agree on every segment in the final whole-query footprint. -/
def concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) : Prop :=
  forall segment index,
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape segment ->
      storeA.readWord? segment index = storeB.readWord? segment index

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_bpCode
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape 0 := by
  simp [concreteBPNativeSuccinctRMQWholeQueryReadFootprint,
    concreteBPNativeDeadTraceSegment]

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
    (shape : Cartesian.CartesianShape) {base dead segment : Nat}
    (hbase : base <= concreteBPNativeDeadTraceSegment)
    (hdead : dead <= concreteBPNativeDeadTraceSegment) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap base dead segment) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryReadFootprint
  cases segment with
  | zero =>
      simpa [WordRAM.singletonSegmentMap] using hbase
  | succ segment =>
      simpa [WordRAM.singletonSegmentMap] using hdead

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_tripleSegmentMap
    (shape : Cartesian.CartesianShape) {base dead segment : Nat}
    (hbase : base + 2 <= concreteBPNativeDeadTraceSegment)
    (hdead : dead <= concreteBPNativeDeadTraceSegment) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.tripleSegmentMap base dead segment) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryReadFootprint
  cases segment with
  | zero =>
      exact Nat.le_trans (Nat.le_add_right base 2) hbase
  | succ segment =>
      cases segment with
      | zero =>
          exact
            Nat.le_trans
              (Nat.succ_le_succ (Nat.le_add_right base 1)) hbase
      | succ segment =>
          cases segment with
          | zero =>
              simpa [WordRAM.tripleSegmentMap] using hbase
          | succ segment =>
              simpa [WordRAM.tripleSegmentMap] using hdead

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperBaseOccurrence
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperBaseWordIndex
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperRankBefore
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperFirstOffset
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
        concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLongFlagRank
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.tripleSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_tripleSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLongRelative
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalBaseOccurrence
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalBaseWordIndex
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalRankBefore
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalFirstOffset
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
        concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSparseRank
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.tripleSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_tripleSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSparseRelative
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
        concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectBitWords
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
        concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeSelectCloseTraceSegmentLayout,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_rankClose
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (concreteBPNativeRankCloseSegmentMap
        concreteBPNativeRankCloseTraceSegmentBase segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_tripleSegmentMap
      shape
      (by simp [concreteBPNativeRankCloseTraceSegmentBase,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_interiorLocal
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeInteriorTraceSegments.localOffset
        concreteBPNativeInteriorTraceSegments.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_interiorGlobal
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeInteriorTraceSegments.globalBlock
        concreteBPNativeInteriorTraceSegments.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_summaryBaseline
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeInteriorTraceSegments.summary.baseline
        concreteBPNativeInteriorTraceSegments.summary.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_summaryMinRel
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeInteriorTraceSegments.summary.minRel
        concreteBPNativeInteriorTraceSegments.summary.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_summaryMaxRel
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeInteriorTraceSegments.summary.maxRel
        concreteBPNativeInteriorTraceSegments.summary.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])

theorem concreteBPNativeSuccinctRMQWholeQueryReadFootprint_summaryArgOffset
    (shape : Cartesian.CartesianShape) (segment : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape
      (WordRAM.singletonSegmentMap
        concreteBPNativeInteriorTraceSegments.summary.argOffset
        concreteBPNativeInteriorTraceSegments.summary.deadSegment
        segment) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryReadFootprint_singletonSegmentMap
      shape
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])
      (by simp [concreteBPNativeInteriorTraceSegments,
        concreteBPNativeDeadTraceSegment])

/-- Precise store agreement for the whole final RMQ supplied-store replay.
The fields enumerate the final global segment layout: BP code, select-close
auxiliary tables, final false-rank tables, and compact close/LCA interior
tables. -/
structure concreteBPNativeSuccinctRMQWholeQueryReadAgreement
    (_shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) : Prop where
  bpCode :
    forall index,
      storeA.readWord? 0 index = storeB.readWord? 0 index
  selectSuperBaseOccurrence :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectSuperBaseWordIndex :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectSuperRankBefore :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectSuperFirstOffset :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.superTable.deadSegment
            segment) index
  selectLongFlagRank :
    forall segment index,
      storeA.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index
  selectLongRelative :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index
  selectLocalBaseOccurrence :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectLocalBaseWordIndex :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectLocalRankBefore :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectLocalFirstOffset :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
            concreteBPNativeSelectCloseTraceSegmentLayout.localTable.deadSegment
            segment) index
  selectSparseRank :
    forall segment index,
      storeA.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.tripleSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index
  selectSparseRelative :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
            concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.deadSegment
            segment) index
  selectBitWords :
    forall segment index,
      storeA.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index =
        storeB.readWord?
          (WordRAM.singletonSegmentMap
            concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase
            concreteBPNativeSelectCloseTraceSegmentLayout.deadSegment
            segment) index
  rankClose :
    forall segment index,
      storeA.readWord?
          (concreteBPNativeRankCloseSegmentMap
            concreteBPNativeRankCloseTraceSegmentBase segment) index =
        storeB.readWord?
          (concreteBPNativeRankCloseSegmentMap
            concreteBPNativeRankCloseTraceSegmentBase segment) index
  canonicalComponent :
    forall address,
      storeA.readWord?
          concreteBPNativeInteriorTraceSegments.canonicalComponent address =
        storeB.readWord?
          concreteBPNativeInteriorTraceSegments.canonicalComponent address

namespace concreteBPNativeSuccinctRMQWholeQueryReadAgreement

theorem refl (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore) :
    concreteBPNativeSuccinctRMQWholeQueryReadAgreement
      shape store store := by
  constructor <;> intros <;> rfl

theorem of_all_segments
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    concreteBPNativeSuccinctRMQWholeQueryReadAgreement
      shape storeA storeB := by
  constructor <;> intros <;> exact hread _ _

theorem of_footprint
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape storeA storeB) :
    concreteBPNativeSuccinctRMQWholeQueryReadAgreement
      shape storeA storeB := by
  constructor
  · intro index
    exact
      hfoot 0 index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_bpCode shape)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperBaseOccurrence
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperBaseWordIndex
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperRankBefore
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSuperFirstOffset
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLongFlagRank
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLongRelative
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalBaseOccurrence
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalBaseWordIndex
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalRankBefore
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectLocalFirstOffset
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSparseRank
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectSparseRelative
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_selectBitWords
          shape segment)
  · intro segment index
    exact
      hfoot _ index
        (concreteBPNativeSuccinctRMQWholeQueryReadFootprint_rankClose
          shape segment)
  · intro address
    exact
      hfoot _ address (by
        simp [concreteBPNativeSuccinctRMQWholeQueryReadFootprint,
          concreteBPNativeInteriorTraceSegments,
          concreteBPNativeDeadTraceSegment])

end concreteBPNativeSuccinctRMQWholeQueryReadAgreement

theorem concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (rankSegmentBase pos : Nat) :
    forall event,
      event ∈
          (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
            shape store rankSegmentBase pos).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  exact
    WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
      (concreteBPNativeRankCloseSegmentMap rankSegmentBase)
      (WordRAM.TraceResult.ofResult
        (((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
            false (WordRAM.Register.NatExpr.reg 0)).evalR
          (store.pullback
            (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
          (WordRAM.Register.RegFile.withNat1 pos)))
      (by
        intro event hmem
        simpa only [WordRAM.TraceResult.ofResult_trace] using
          WordRAM.Register.NatProgram.evalR_no_syntheticCostOnlyPrimitive
            ((builtRelativeSplitBPCloseRankData shape).rankRegisterProgram
              false (WordRAM.Register.NatExpr.reg 0))
            (store.pullback
              (concreteBPNativeRankCloseSegmentMap rankSegmentBase))
            (WordRAM.Register.RegFile.withNat1 pos)
            event hmem)

theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (idx : Nat) :
    concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape storeA idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape storeB idx := by
  unfold concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_store_parametric
        (layout := concreteBPNativeSelectCloseTraceSegmentLayout)
        hagree.selectSuperBaseOccurrence
        hagree.selectSuperBaseWordIndex
        hagree.selectSuperRankBefore
        hagree.selectSuperFirstOffset
        hagree.selectLongFlagRank
        hagree.selectLongRelative
        hagree.selectLocalBaseOccurrence
        hagree.selectLocalBaseWordIndex
        hagree.selectLocalRankBefore
        hagree.selectLocalFirstOffset
        hagree.selectSparseRank
        hagree.selectSparseRelative
        hagree.selectBitWords
        idx

private theorem selectEntryReadWithStore_storeTraceLocal
    {entries : List GenericSelect.SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table : GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable
      entries fieldWidth)
    (layout : GenericSelect.SparseDenseEntryTableTraceSegmentBases)
    (i : Nat) :
    StoreTraceLocal (fun store =>
      table.readTraceResultRelabeledWithStore layout store i) := by
  unfold GenericSelect.FixedWidthSparseDenseSelectDenseLocalEntryTable.readTraceResultRelabeledWithStore
  apply storeTraceLocal_bind
  · exact ofProgramWithStore_storeTraceLocal _ _
  · intro baseOccurrence?
    apply storeTraceLocal_bind
    · exact ofProgramWithStore_storeTraceLocal _ _
    · intro baseWordIndex?
      apply storeTraceLocal_bind
      · exact ofProgramWithStore_storeTraceLocal _ _
      · intro rankBefore?
        apply storeTraceLocal_map
        exact ofProgramWithStore_storeTraceLocal _ _

private theorem rankTraceResultRelabeledWithStore_storeTraceLocal
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data : SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
      bits superOverhead blockOverhead queryCost)
    (rankBase deadSegment : Nat) (target : Bool) (pos : Nat) :
    StoreTraceLocal (fun store =>
      data.rankTraceResultRelabeledWithStore
        rankBase deadSegment store target pos) := by
  unfold SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.rankTraceResultRelabeledWithStore
  exact ofNatProgramWithStore_storeTraceLocal _ _ _

private theorem relativeOffsetReadWithStore_storeTraceLocal
    {entries : List Nat} {width : Nat}
    (segmentBase deadSegment : Nat)
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) :
    StoreTraceLocal (fun store =>
      GenericSelect.relativeOffsetReadTraceResultRelabeledWithStore
        segmentBase deadSegment table store base slot) := by
  unfold GenericSelect.relativeOffsetReadTraceResultRelabeledWithStore
  apply storeTraceLocal_map
  exact ofProgramWithStore_storeTraceLocal _ _

private theorem sparseDirectoryReadWithStore_storeTraceLocal
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory : GenericSelect.SparseExceptionDirectory
      bits target rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionDirectoryTraceSegmentBases)
    (base localSlot localOccurrence : Nat) :
    StoreTraceLocal (fun store =>
      directory.readTraceResultRelabeledWithStore
        layout store base localSlot localOccurrence) := by
  unfold GenericSelect.SparseExceptionDirectory.readTraceResultRelabeledWithStore
  apply storeTraceLocal_bind
  · exact rankTraceResultRelabeledWithStore_storeTraceLocal _ _ _ _ _
  · intro exceptionRank
    exact relativeOffsetReadWithStore_storeTraceLocal _ _ _ _ _

private theorem denseTwoWordSelectWithStoreLocal_storeTraceLocal
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    StoreTraceLocal (fun store =>
      GenericSelect.denseTwoWordSelectTraceResultWithStoreLocal
        target bitWords store basePosition baseOccurrence q) := by
  unfold GenericSelect.denseTwoWordSelectTraceResultWithStoreLocal
  apply storeTraceLocal_bind
  · exact ofResultProgram_storeTraceLocal _
  · intro firstWord?
    cases firstWord? with
    | none => exact storeTraceLocal_const _
    | some firstWord =>
        apply storeTraceLocal_bind
        · exact storeTraceLocal_const _
        · intro beforeFirst
          apply storeTraceLocal_bind
          · exact storeTraceLocal_const _
          · intro uptoFirst
            dsimp only
            split
            · apply storeTraceLocal_map
              exact storeTraceLocal_const _
            · apply storeTraceLocal_bind
              · exact ofResultProgram_storeTraceLocal _
              · intro secondWord?
                cases secondWord? with
                | none => exact storeTraceLocal_const _
                | some secondWord =>
                    apply storeTraceLocal_map
                    exact storeTraceLocal_const _

private theorem denseTwoWordSelectRelabeledWithStore_storeTraceLocal
    (bitWordSegmentBase deadSegment : Nat)
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    StoreTraceLocal (fun store =>
      GenericSelect.denseTwoWordSelectTraceResultRelabeledWithStore
        bitWordSegmentBase deadSegment target bitWords store
        basePosition baseOccurrence q) := by
  unfold GenericSelect.denseTwoWordSelectTraceResultRelabeledWithStore
  exact storeTraceLocal_relabelReadSegmentsWith_pullback _ _
    (denseTwoWordSelectWithStoreLocal_storeTraceLocal
      target bitWords basePosition baseOccurrence q)

private theorem sparseExceptionSelectWithStore_storeTraceLocal
    {bits : List Bool} {target : Bool}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data : GenericSelect.SparseExceptionSelectData
      bits target rankSuperOverhead rankBlockOverhead)
    (layout : GenericSelect.SparseExceptionSelectTraceSegmentLayout)
    (idx : Nat) :
    StoreTraceLocal (fun store =>
      data.selectTraceResultRelabeledWithStore layout store idx) := by
  unfold GenericSelect.SparseExceptionSelectData.selectTraceResultRelabeledWithStore
  dsimp only
  by_cases hvalid : idx < GenericSelect.occurrenceCount bits target
  · simp only [hvalid, if_pos]
    apply storeTraceLocal_bind
    · exact selectEntryReadWithStore_storeTraceLocal _ _ _
    · intro super?
      cases super? with
      | none => exact storeTraceLocal_const _
      | some super =>
          by_cases hmarked : GenericSelect.relativeSplitSelectEntryIsMarked super
          · simp only [hmarked, if_pos]
            apply storeTraceLocal_bind
            · exact rankTraceResultRelabeledWithStore_storeTraceLocal _ _ _ _ _
            · intro exceptionRank
              exact relativeOffsetReadWithStore_storeTraceLocal _ _ _ _ _
          · simp [hmarked]
            apply storeTraceLocal_bind
            · exact selectEntryReadWithStore_storeTraceLocal _ _ _
            · intro loc?
              cases loc? with
              | none => exact storeTraceLocal_const _
              | some loc =>
                  by_cases hlocalMarked :
                      GenericSelect.relativeSplitSelectEntryIsMarked loc
                  · simp only [hlocalMarked, if_pos]
                    exact sparseDirectoryReadWithStore_storeTraceLocal
                      _ _ _ _ _
                  · simp [hlocalMarked]
                    exact denseTwoWordSelectRelabeledWithStore_storeTraceLocal
                      _ _ _ _ _ _ _
  · simp only [hvalid]
    exact storeTraceLocal_const _

theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_eq_of_trace_read_agreement
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (idx : Nat)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
            (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
              shape storeA idx).trace ->
          storeA.readWord? segment index = storeB.readWord? segment index) :
    concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape storeA idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape storeB idx := by
  exact sparseExceptionSelectWithStore_storeTraceLocal
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
    concreteBPNativeSelectCloseTraceSegmentLayout idx storeA storeB hagree

theorem concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
            shape store idx).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
  exact
    (GenericSelect.sparseExceptionSelectData shape.bpCode false)
      |>.selectTraceResultRelabeledWithStore_no_syntheticCostOnlyPrimitive
        concreteBPNativeSelectCloseTraceSegmentLayout store idx

def concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
    shape
    (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
      shape store concreteBPNativeRankCloseTraceSegmentBase)
    concreteBPNativeInteriorTraceSegments
    store concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
    leftClose rightClose

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    forall event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
            shape store leftClose rightClose).trace ->
        event.matchesReadStore store := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_matchesReadStore
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments store
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (fun pos event hmem =>
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
          shape store concreteBPNativeRankCloseTraceSegmentBase pos
          event hmem)

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    forall event,
      event ∈
          (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
            shape store leftClose rightClose).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments store
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (fun pos event hmem =>
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
          shape store concreteBPNativeRankCloseTraceSegmentBase pos
          event hmem)

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        leftClose rightClose =
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape leftClose rightClose := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  have hrank :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegment
          shape concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore
        shape pos
  rw [hrank]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_eq_of_agree
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegment
        shape concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      (concreteBPNativeSuccinctRMQGlobalReadStore_bpCode shape)
      (concreteBPNativeSuccinctRMQGlobalReadStore_canonicalComponent shape)

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape storeA leftClose rightClose =
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape storeB leftClose rightClose := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  have hrank :
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeA concreteBPNativeRankCloseTraceSegmentBase) =
        concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape storeB concreteBPNativeRankCloseTraceSegmentBase := by
    funext pos
    exact
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
        shape concreteBPNativeRankCloseTraceSegmentBase pos
        hagree.rankClose
  rw [hrank]
  exact
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore_store_parametric
      shape
      (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape storeB concreteBPNativeRankCloseTraceSegmentBase)
      concreteBPNativeInteriorTraceSegments
      concreteBPNativeFiniteSmallSameBlockCloseTraceSegment
      leftClose rightClose
      hagree.bpCode
      hagree.canonicalComponent

private theorem finalRankCloseWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    StoreTraceLocal (fun store =>
      concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store concreteBPNativeRankCloseTraceSegmentBase pos) := by
  intro storeA storeB hagree
  exact
    concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_eq_of_trace_read_agreement
      shape storeA storeB concreteBPNativeRankCloseTraceSegmentBase pos hagree

private theorem bpCodeWordReadWithStore_storeTraceLocal (index : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResultWithStore
        store index) := by
  intro storeA storeB hagree
  have hread := hagree 0 index (storeA.readWord? 0 index) (List.Mem.head [])
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResultWithStore
    SuccinctClose.ConcreteCompactBPCloseLCADirectory.readStorePayloadWordValue
  simp [hread]

private theorem localBPBlockWordsWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResultWithStore
        shape store blockSize close) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPBlockWordsTraceResultWithStore
  apply storeTraceLocal_bind
  · exact bpCodeWordReadWithStore_storeTraceLocal _
  · intro w0
    apply storeTraceLocal_bind
    · exact bpCodeWordReadWithStore_storeTraceLocal _
    · intro w1
      apply storeTraceLocal_bind
      · exact bpCodeWordReadWithStore_storeTraceLocal _
      · intro w2
        apply storeTraceLocal_map
        exact bpCodeWordReadWithStore_storeTraceLocal _

private theorem localBPWindowBitsWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore
        shape store blockSize close) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPWindowBitsTraceResultWithStore
  apply storeTraceLocal_map
  exact localBPBlockWordsWithStore_storeTraceLocal shape blockSize close

private theorem localBPSameBlockSeededWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseSeededTraceResultWithStore
        shape store blockSize leftClose rightClose seed) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseSeededTraceResultWithStore
  apply storeTraceLocal_map
  exact localBPWindowBitsWithStore_storeTraceLocal shape blockSize leftClose

private theorem localBPLeftFringeSeededWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPLeftFringeCandidateSeededTraceResultWithStore
        shape store blockSize leftClose seed) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPLeftFringeCandidateSeededTraceResultWithStore
  apply storeTraceLocal_map
  exact localBPWindowBitsWithStore_storeTraceLocal shape blockSize leftClose

private theorem localBPRightFringeSeededWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPRightFringeCandidateSeededTraceResultWithStore
        shape store blockSize rightClose seed) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPRightFringeCandidateSeededTraceResultWithStore
  apply storeTraceLocal_map
  exact localBPWindowBitsWithStore_storeTraceLocal shape blockSize rightClose

private theorem finalRankSeedWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape store concreteBPNativeRankCloseTraceSegmentBase)
        blockSize close) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSeedFromRankCloseTraceResult
  apply storeTraceLocal_map
  exact finalRankCloseWithStore_storeTraceLocal shape _

private theorem canonicalInteriorWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape)
    (segments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (startBlock count : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        shape segments store startBlock count) := by
  intro storeA storeB hagree
  let computation :=
    SuccinctClose.canonicalRelativeRmmInteriorRangeMinComputation
      shape startBlock count
  let flatA :=
    SuccinctClose.flatWordStoreOfReadStore
      storeA segments.canonicalComponent
  let flatB :=
    SuccinctClose.flatWordStoreOfReadStore
      storeB segments.canonicalComponent
  have hexecution : computation.run flatA = computation.run flatB :=
    computation.footprint_determines flatA flatB (by
      intro address haddress
      simp only [SuccinctSpace.FlatStoreExecution.footprint] at haddress
      rcases List.mem_map.mp haddress with ⟨read, hread, hfst⟩
      have htrace := hagree segments.canonicalComponent read.1 read.2 (by
        unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
        simp only [
          SuccinctClose.flatStoreExecutionTraceResultAtSegment]
        apply List.mem_map.mpr
        exact ⟨read, hread, rfl⟩)
      cases read with
      | mk readAddress word? =>
          have hreadAddress : readAddress = address := by
            simpa using hfst
          subst address
          simpa [flatA, flatB,
            SuccinctClose.flatWordStoreOfReadStore]
            using htrace)
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  exact congrArg
    (SuccinctClose.flatStoreExecutionTraceResultAtSegment
      segments.canonicalComponent) hexecution

private theorem finalSameBlockLcaWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape store concreteBPNativeRankCloseTraceSegmentBase)
        store blockSize leftClose rightClose) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore
  apply storeTraceLocal_bind
  · exact finalRankSeedWithStore_storeTraceLocal shape blockSize leftClose
  · intro seed
    exact localBPSameBlockSeededWithStore_storeTraceLocal
      shape blockSize leftClose rightClose seed

private theorem finalCrossBlockLcaWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape)
    (segments : SuccinctClose.BPRelativeRmmInteriorTraceSegments)
    (leftClose rightClose : Nat) :
    StoreTraceLocal (fun store =>
      SuccinctClose.ConcreteCompactBPCloseLCADirectory.crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape
        (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
          shape store concreteBPNativeRankCloseTraceSegmentBase)
        segments store leftClose rightClose) := by
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftBlock := SuccinctClose.blockOfClose
    blockSize leftClose
  let rightBlock := SuccinctClose.blockOfClose
    blockSize rightClose
  dsimp only
  apply storeTraceLocal_bind
  · exact finalRankSeedWithStore_storeTraceLocal shape blockSize leftClose
  · intro leftSeed
    apply storeTraceLocal_bind
    · exact localBPLeftFringeSeededWithStore_storeTraceLocal
        shape blockSize leftClose leftSeed
    · intro left?
      apply storeTraceLocal_bind
      · by_cases hmiddle : leftBlock + 1 < rightBlock
        · dsimp only [blockSize, leftBlock, rightBlock] at hmiddle
          simp only [hmiddle, if_pos]
          exact canonicalInteriorWithStore_storeTraceLocal
            shape segments (leftBlock + 1) (rightBlock - leftBlock - 1)
        · dsimp only [blockSize, leftBlock, rightBlock] at hmiddle
          simp only [hmiddle]
          exact storeTraceLocal_const _
      · intro middle?
        apply storeTraceLocal_bind
        · exact finalRankSeedWithStore_storeTraceLocal
            shape blockSize rightClose
        · intro rightSeed
          apply storeTraceLocal_map
          exact localBPRightFringeSeededWithStore_storeTraceLocal
            shape blockSize rightClose rightSeed

private theorem finalLcaCloseWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat) :
    StoreTraceLocal (fun store =>
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape store leftClose rightClose) := by
  unfold concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  unfold SuccinctClose.ConcreteCompactBPCloseLCADirectory.lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  let blockSize := SuccinctClose.canonicalBPRelativeSummaryBlockSizeRaw shape
  dsimp only
  by_cases hsame :
      SuccinctClose.blockOfClose
          blockSize leftClose =
      SuccinctClose.blockOfClose
          blockSize rightClose
  · dsimp only [blockSize] at hsame
    simp only [hsame, if_pos]
    exact finalSameBlockLcaWithStore_storeTraceLocal
      shape blockSize leftClose rightClose
  · dsimp only [blockSize] at hsame
    simp only [hsame]
    exact finalCrossBlockLcaWithStore_storeTraceLocal
      shape concreteBPNativeInteriorTraceSegments leftClose rightClose

theorem concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_eq_of_trace_read_agreement
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (leftClose rightClose : Nat)
    (hagree :
      forall segment index word?,
        List.Mem (WordRAM.TraceEvent.readWord segment index word?)
            (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
              shape storeA leftClose rightClose).trace ->
          storeA.readWord? segment index = storeB.readWord? segment index) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape storeA leftClose rightClose =
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape storeB leftClose rightClose := by
  exact finalLcaCloseWithStore_storeTraceLocal
    shape leftClose rightClose storeA storeB hagree

namespace WholeQueryInstr

def evalGlobalWordTraceWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) : WordRAM.TraceResult WholeQueryState :=
  match instr with
  | .selectClose dst idx =>
      WordRAM.TraceResult.map
        (fun close? => state.setOpt dst close?)
        (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
          shape store (idx.eval left right state))
  | .lcaClose dst leftReg rightReg =>
      match state.opt leftReg, state.opt rightReg with
      | some leftClose, some rightClose =>
          WordRAM.TraceResult.map
            (fun answer? => state.setOpt dst answer?)
            (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
              shape store leftClose rightClose)
      | _, _ => WordRAM.TraceResult.pure (state.setOpt dst none)
  | .rankCloseIfSome dst guard pos =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.map
            (fun closeRank => state.setNat dst closeRank)
            (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
              shape store concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state))
      | none => WordRAM.TraceResult.pure state
  | .outputPredIfSome dst guard src =>
      match state.opt guard with
      | some _ =>
          WordRAM.TraceResult.pure
            (state.setOpt dst (some (state.nat src - 1)))
      | none =>
          WordRAM.TraceResult.pure (state.setOpt dst none)

private theorem evalGlobalWordTraceWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (instr : WholeQueryInstr) (state : WholeQueryState) :
    StoreTraceLocal (fun store =>
      instr.evalGlobalWordTraceWithStore shape store left right state) := by
  cases instr with
  | selectClose dst idx =>
      unfold evalGlobalWordTraceWithStore
      apply storeTraceLocal_map
      exact fun storeA storeB hagree =>
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_eq_of_trace_read_agreement
          shape storeA storeB (idx.eval left right state) hagree
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg with
          | none =>
              simp only [evalGlobalWordTraceWithStore, hleft, hright]
              exact storeTraceLocal_const _
          | some rightClose =>
              simp only [evalGlobalWordTraceWithStore, hleft, hright]
              exact storeTraceLocal_const _
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp only [evalGlobalWordTraceWithStore, hleft, hright]
              exact storeTraceLocal_const _
          | some rightClose =>
              simp only [evalGlobalWordTraceWithStore, hleft, hright]
              apply storeTraceLocal_map
              exact fun storeA storeB hagree =>
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_eq_of_trace_read_agreement
                  shape storeA storeB leftClose rightClose hagree
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp only [evalGlobalWordTraceWithStore, hguard]
          exact storeTraceLocal_const _
      | some value =>
          simp only [evalGlobalWordTraceWithStore, hguard]
          apply storeTraceLocal_map
          exact fun storeA storeB hagree =>
            concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_eq_of_trace_read_agreement
              shape storeA storeB concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state) hagree
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard with
      | none =>
          simp only [evalGlobalWordTraceWithStore, hguard]
          exact storeTraceLocal_const _
      | some value =>
          simp only [evalGlobalWordTraceWithStore, hguard]
          exact storeTraceLocal_const _

theorem evalGlobalWordTraceWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      event ∈
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).trace ->
        event.matchesReadStore store := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_matchesReadStore
          shape store (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTraceWithStore, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
          | some rightClose =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_matchesReadStore
                  shape store leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceWithStore, hguard]
      | some _ =>
        simp [evalGlobalWordTraceWithStore, hguard]
        exact
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_matchesReadStore
            shape store concreteBPNativeRankCloseTraceSegmentBase
            (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    forall event,
      event ∈
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore]
      exact
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
          shape store (idx.eval left right state)
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg with
      | none =>
          cases hright : state.opt rightReg <;>
            simp [evalGlobalWordTraceWithStore, hleft, hright] <;>
            intro event hmem <;> cases hmem
      | some leftClose =>
          cases hright : state.opt rightReg with
          | none =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
          | some rightClose =>
              simp [evalGlobalWordTraceWithStore, hleft, hright]
              exact
                concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_no_syntheticCostOnlyPrimitive
                  shape store leftClose rightClose
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceWithStore, hguard]
      | some _ =>
        simp [evalGlobalWordTraceWithStore, hguard]
        exact
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_no_syntheticCostOnlyPrimitive
            shape store concreteBPNativeRankCloseTraceSegmentBase
            (pos.eval left right state)
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, hguard] <;>
        intro event hmem <;> cases hmem

theorem evalGlobalWordTraceWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    instr.evalGlobalWordTraceWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right state =
      instr.evalGlobalWordTrace shape left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace,
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_globalReadStore]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace,
            hleft, hright,
            concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace,
          hguard,
          concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_globalReadStore]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace, hguard]

theorem evalGlobalWordTraceWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (left right : Nat) (instr : WholeQueryInstr)
    (state : WholeQueryState) :
    instr.evalGlobalWordTraceWithStore shape storeA left right state =
      instr.evalGlobalWordTraceWithStore shape storeB left right state := by
  cases instr with
  | selectClose dst idx =>
      simp [evalGlobalWordTraceWithStore,
        concreteBPNativeSelectCloseGlobalWordTraceResultWithStore_store_parametric
          shape hagree (idx.eval left right state)]
  | lcaClose dst leftReg rightReg =>
      cases hleft : state.opt leftReg <;>
        cases hright : state.opt rightReg <;>
          simp [evalGlobalWordTraceWithStore, hleft, hright,
            concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_store_parametric
              shape hagree]
  | rankCloseIfSome dst guard pos =>
      cases hguard : state.opt guard with
      | none =>
          simp [evalGlobalWordTraceWithStore, hguard]
      | some _ =>
          simp [evalGlobalWordTraceWithStore, hguard,
            concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore_store_parametric
              shape concreteBPNativeRankCloseTraceSegmentBase
              (pos.eval left right state) hagree.rankClose]
  | outputPredIfSome dst guard src =>
      cases hguard : state.opt guard <;>
        simp [evalGlobalWordTraceWithStore, hguard]

end WholeQueryInstr

namespace WholeQueryProgram

def evalGlobalWordTraceWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    WholeQueryProgram -> WholeQueryState -> WordRAM.TraceResult WholeQueryState
  | [], state => WordRAM.TraceResult.pure state
  | instr :: rest, state =>
      WordRAM.TraceResult.bind
        (instr.evalGlobalWordTraceWithStore shape store left right state)
        fun state' =>
      evalGlobalWordTraceWithStore shape store left right rest state'

private theorem evalGlobalWordTraceWithStore_storeTraceLocal
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    StoreTraceLocal (fun store =>
      evalGlobalWordTraceWithStore shape store left right program state) := by
  induction program generalizing state with
  | nil =>
      simp only [evalGlobalWordTraceWithStore]
      exact storeTraceLocal_const _
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore
      apply storeTraceLocal_bind
      · exact WholeQueryInstr.evalGlobalWordTraceWithStore_storeTraceLocal
          shape left right instr state
      · intro state'
        exact ih state'

theorem evalGlobalWordTraceWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      event ∈
          (evalGlobalWordTraceWithStore
            shape store left right program state).trace ->
        event.matchesReadStore store := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTraceWithStore_matchesReadStore
            shape store left right instr state
      · exact ih
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).value

theorem evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    forall event,
      event ∈
          (evalGlobalWordTraceWithStore
            shape store left right program state).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore
      apply WordRAM.TraceResult.bind_trace_forall
      · exact
          WholeQueryInstr.evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
            shape store left right instr state
      · exact ih
          (instr.evalGlobalWordTraceWithStore
            shape store left right state).value

theorem evalGlobalWordTraceWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    evalGlobalWordTraceWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right program state =
      evalGlobalWordTrace shape left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore, evalGlobalWordTrace]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore evalGlobalWordTrace
      rw [
        WholeQueryInstr.evalGlobalWordTraceWithStore_globalReadStore
          shape left right instr state]
      cases hfirst : instr.evalGlobalWordTrace shape left right state
      simp [WordRAM.TraceResult.bind, ih]

theorem evalGlobalWordTraceWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (left right : Nat)
    (program : WholeQueryProgram) (state : WholeQueryState) :
    evalGlobalWordTraceWithStore shape storeA left right program state =
      evalGlobalWordTraceWithStore shape storeB left right program state := by
  induction program generalizing state with
  | nil =>
      simp [evalGlobalWordTraceWithStore]
  | cons instr rest ih =>
      unfold evalGlobalWordTraceWithStore
      rw [
        WholeQueryInstr.evalGlobalWordTraceWithStore_store_parametric
          shape hagree left right instr state]
      cases hfirst :
          instr.evalGlobalWordTraceWithStore
            shape storeB left right state
      simp [WordRAM.TraceResult.bind, ih]

end WholeQueryProgram

def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.map WholeQueryState.output?
    (WholeQueryProgram.evalGlobalWordTraceWithStore shape store left right
      concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty)

def concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) : Costed (Option Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    shape store left right).toCosted

/-- One logical payload address, before the later physical-store translation. -/
abbrev ConcreteBPNativeSuccinctRMQLogicalReadAddress := Nat × Nat

/-- Ordered logical read footprint of the supplied-store execution.

This is the read-event projection of the trace itself. It retains repeated
addresses and records failed reads because the returned `word?` is deliberately
discarded only after recognizing a `readWord` event.
-/
def concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    List ConcreteBPNativeSuccinctRMQLogicalReadAddress :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape store left right).trace.filterMap fun event =>
    match event with
    | WordRAM.TraceEvent.readWord segment index _ => some (segment, index)
    | _ => none

/-- The recorded ordered footprint is exactly the execution's read projection. -/
theorem concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore_recorded
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
        shape store left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape store left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord segment index _ => some (segment, index)
        | _ => none := by
  rfl

/-- Two stores agree on every logical address actually read by the first
supplied-store execution. -/
def concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (left right : Nat) : Prop :=
  forall segment index,
    (segment, index) ∈
        concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
          shape storeA left right ->
      storeA.readWord? segment index = storeB.readWord? segment index

/-- Dynamic-footprint agreement is exactly agreement at every emitted read
event, irrespective of whether that event returned a word or failed. -/
theorem concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_iff
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
        shape storeA storeB left right ↔
      forall segment index word?,
        WordRAM.TraceEvent.readWord segment index word? ∈
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
              shape storeA left right).trace ->
          storeA.readWord? segment index =
            storeB.readWord? segment index := by
  constructor
  · intro hagree segment index word? hmem
    apply hagree segment index
    simp only [
      concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore,
      List.mem_filterMap]
    exact ⟨WordRAM.TraceEvent.readWord segment index word?, hmem, by simp⟩
  · intro hagree segment index hmem
    simp only [
      concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore,
      List.mem_filterMap] at hmem
    rcases hmem with ⟨event, hevent, hproject⟩
    cases event with
    | readWord segment' index' word? =>
        simp at hproject
        rcases hproject with ⟨rfl, rfl⟩
        exact hagree segment' index' word? hevent
    | wordRank target limit result => simp at hproject
    | wordSelect target occurrence result => simp at hproject
    | syntheticCostOnlyPrimitive => simp at hproject

/-- Agreement on the reads actually emitted by the supplied-store execution
determines the complete execution, including its result, modeled cost, ordered
trace, and failed reads. -/
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (left right : Nat)
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
        shape storeA storeB left right) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeA left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeB left right := by
  have hlocal :
      StoreTraceLocal (fun store =>
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
          shape store left right) := by
    unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    apply storeTraceLocal_map
    exact WholeQueryProgram.evalGlobalWordTraceWithStore_storeTraceLocal
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty
  exact hlocal storeA storeB
    ((concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_iff
      shape storeA storeB left right).mp hagree)

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        event.matchesReadStore store := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTraceWithStore_matchesReadStore
      shape store left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  apply WordRAM.TraceResult.map_trace_forall
  exact
    WholeQueryProgram.evalGlobalWordTraceWithStore_no_syntheticCostOnlyPrimitive
      shape store left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  rw [
    WholeQueryProgram.evalGlobalWordTraceWithStore_globalReadStore
      shape left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryReadAgreement
        shape storeA storeB)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeA left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeB left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  rw [
    WholeQueryProgram.evalGlobalWordTraceWithStore_store_parametric
      shape hagree left right concreteBPNativeSuccinctRMQWholeQueryProgram
      WholeQueryState.empty]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint
    (shape : Cartesian.CartesianShape)
    {storeA storeB : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape storeA storeB)
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeA left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeB left right := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric
      shape
      (concreteBPNativeSuccinctRMQWholeQueryReadAgreement.of_footprint
        shape hfoot)
      left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    forall {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape segment := by
  intro segment index word? hmem
  by_cases hsegment :
      concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape segment
  · exact hsegment
  let flippedWord? : Option WordRAM.Word :=
    match word? with
    | none => some []
    | some _ => none
  have hflip_ne : flippedWord? ≠ word? := by
    cases word? <;> simp [flippedWord?]
  let flippedStore : WordRAM.ReadStore :=
    { readWord? := fun segment' index' =>
        if segment' = segment ∧ index' = index then
          flippedWord?
        else
          store.readWord? segment' index' }
  have hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store flippedStore := by
    intro segment' index' hsegment'
    by_cases hsame : segment' = segment ∧ index' = index
    · rcases hsame with ⟨rfl, _⟩
      exact False.elim (hsegment hsegment')
    · simp [flippedStore, hsame]
  have htrace :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint
      shape hfoot left right
  have hmemFlipped :
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape flippedStore left right).trace := by
    rw [htrace] at hmem
    exact hmem
  have hmatch :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
      shape flippedStore left right
      (WordRAM.TraceEvent.readWord segment index word?) hmemFlipped
  have hflipped_eq : flippedWord? = word? := by
    simpa [WordRAM.TraceEvent.matchesReadStore, flippedStore] using hmatch
  exact False.elim (hflip_ne hflipped_eq)

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_reads_subset_footprint
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        concreteBPNativeSuccinctRMQWholeQueryReadFootprint shape segment := by
  intro segment index word? hmem
  rw [← concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
    shape left right] at hmem
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_reads_subset_footprint
      shape (concreteBPNativeSuccinctRMQGlobalReadStore shape) left right
      hmem

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right := by
  calc
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape store left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        left right :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint
          shape hfoot left right
    _ =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
          shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
        shape store left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint
      shape store hfoot left right]

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    forall {segment index : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord segment index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        concreteBPNativeSuccinctRMQCanonicalReviewerReadBacked
          shape segment index word := by
  intro segment index word hmem
  have hmemGlobal :
      WordRAM.TraceEvent.readWord segment index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace := by
    rw [
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_eq_global_of_footprint
        shape store hfoot left right] at hmem
    exact hmem
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
      shape left right hmemGlobal

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
      shape store hfoot left right]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_canonicalTransitional
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        3 * SuccinctSelect.sparseDenseFalseSelectQueryCost +
          SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            SuccinctSelect.sparseDenseFalseSelectQueryCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
      shape store hfoot left right]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_principledAllSizeChargedTrace
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
      shape store hfoot left right]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_cleanAllSize
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        concreteBPNativeSuccinctRMQCleanAllSizeQueryCost := by
  exact Nat.le_trans
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_principledAllSizeChargedTrace
      shape store hfoot left right)
    (by
      rw [concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq,
        concreteBPNativeSuccinctRMQCleanAllSizeQueryCost_eq]
      omega)

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_refines_canonicalInterpretedCosted
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      left right).toCosted =
      concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        shape left right := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted
      shape left right

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  unfold concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_exact_of_footprint_global
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {store : WordRAM.ReadStore}
    (hfoot :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store (concreteBPNativeSuccinctRMQGlobalReadStore shape))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
      shape store hfoot left (left + len)]
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound

/-! ### Genuine flat physical-store execution -/

/--
Adapt one caller-supplied flat physical store to the logical segment interface
expected by the existing whole-query evaluator.  Every evaluator read is
performed at the checked translated physical address in segment zero.
-/
def concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
    (shape : Cartesian.CartesianShape) (physicalStore : WordRAM.ReadStore) :
    WordRAM.ReadStore where
  readWord? segment index :=
    physicalStore.readWord? 0
      (concreteBPNativeSuccinctRMQReviewerPhysicalAddress shape segment index)

/-- The canonical flat physical store adapts exactly to the canonical logical
segmented store, including failed and dead reads. -/
theorem concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter_canonical
    (shape : Cartesian.CartesianShape) :
    concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape) =
      concreteBPNativeSuccinctRMQGlobalReadStore shape := by
  apply WordRAM.ReadStore.ext
  intro segment index
  change
    (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[
        concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index]? =
      (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        segment index
  exact
    (concreteBPNativeSuccinctRMQGlobalReadStore_eq_reviewerPhysical
      shape segment index).symm

/--
Execute the existing supplied-store whole-query evaluator against a genuinely
flat physical store.  The value is computed by that evaluator through
`ReviewerPhysicalStoreAdapter`; only the emitted logical read labels are then
translated to the physical addresses that were actually consulted.
-/
def concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
    (shape : Cartesian.CartesianShape) (physicalStore : WordRAM.ReadStore)
    (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  let logicalResult :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape
      (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
        shape physicalStore)
      left right
  { value := logicalResult.value
  , trace := logicalResult.trace.map
      (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) }

/--
The result projection of flat physical execution is literally the result
projection computed by the existing supplied-store evaluator after checked
address translation.  This exposes the semantic dependency directly, without
using equality of aggregate trace records as a proxy for answer dependency.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator
    (shape : Cartesian.CartesianShape) (physicalStore : WordRAM.ReadStore)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
      shape physicalStore left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          shape physicalStore)
        left right).value := by
  rfl

/-- Canonical genuine flat physical execution. -/
def concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
    shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
    left right

/-- Canonical flat store with one chosen physical address made unreadable.
This is a scoped semantic-corruption fixture, not part of the construction. -/
def concreteBPNativeSuccinctRMQReviewerPhysicalDropAddressStore
    (shape : Cartesian.CartesianShape) (droppedAddress : Nat) :
    WordRAM.ReadStore where
  readWord? segment address :=
    if segment = 0 && address = droppedAddress then
      none
    else
      (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape).readWord?
        segment address

/--
If two translated supplied-store evaluations differ at the result projection,
the corresponding flat physical executions differ at that same projection.
The theorem is intentionally restricted to stores and queries for which the
decisive evaluator results differ; it does not claim that every consumed word
is decisive for every query.
-/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne
    (shape : Cartesian.CartesianShape) (storeA storeB : WordRAM.ReadStore)
    (left right : Nat)
    (hneq :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeA)
        left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeB)
        left right).value) :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
      shape storeA left right).value ≠
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
      shape storeB left right).value := by
  simpa only [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator]
    using hneq

/-- Ordered physical addresses consumed by a supplied flat-store execution.
Repeated reads and failed/dead reads are retained in execution order. -/
def concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprintWithStore
    (shape : Cartesian.CartesianShape) (physicalStore : WordRAM.ReadStore)
    (left right : Nat) : List Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
      shape physicalStore left right).trace.filterMap fun event =>
    match event with
    | WordRAM.TraceEvent.readWord 0 address _ => some address
    | WordRAM.TraceEvent.readWord _ _ _ => none
    | _ => none

/-- Canonical execution-derived ordered physical footprint. -/
def concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
    (shape : Cartesian.CartesianShape) (left right : Nat) : List Nat :=
  concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprintWithStore
    shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
    left right

/-- Agreement on every physical address consumed by the first execution. -/
def concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalStoresAgreeOnOrderedFootprint
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (left right : Nat) : Prop :=
  forall address,
    address ∈
        concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprintWithStore
          shape storeA left right ->
      storeA.readWord? 0 address = storeB.readWord? 0 address

/-- Every logical evaluator read contributes its translated address to the
execution-derived physical footprint, whether it succeeds or fails. -/
theorem concreteBPNativeSuccinctRMQWholeQueryLogicalRead_mem_flatPhysicalFootprint
    (shape : Cartesian.CartesianShape) (physicalStore : WordRAM.ReadStore)
    (left right segment index : Nat) (word? : Option WordRAM.Word)
    (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          shape physicalStore)
        left right).trace) :
    concreteBPNativeSuccinctRMQReviewerPhysicalAddress
        shape segment index ∈
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprintWithStore
        shape physicalStore left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprintWithStore
  simp only [List.mem_filterMap]
  refine ⟨WordRAM.TraceEvent.readWord 0
    (concreteBPNativeSuccinctRMQReviewerPhysicalAddress shape segment index)
    word?, ?_, by simp⟩
  simp only [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore,
    List.mem_map]
  exact
    ⟨WordRAM.TraceEvent.readWord segment index word?, hmem, rfl⟩

/-- Every physical read event reports the word returned by the supplied flat
physical store at that exact address. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_matchesReadStore
    (shape : Cartesian.CartesianShape) (physicalStore : WordRAM.ReadStore)
    (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
            shape physicalStore left right).trace ->
        event.matchesReadStore physicalStore := by
  intro event hmem
  simp only [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore,
    List.mem_map] at hmem
  rcases hmem with ⟨logicalEvent, hlogical, rfl⟩
  have hmatch :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
      shape
      (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
        shape physicalStore)
      left right logicalEvent hlogical
  cases logicalEvent with
  | readWord segment index word? =>
      simpa [concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent,
        concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter,
        WordRAM.TraceEvent.matchesReadStore] using hmatch
  | wordRank target limit result => trivial
  | wordSelect target occurrence result => trivial
  | syntheticCostOnlyPrimitive => trivial

/-- Agreement on the first execution's consumed physical footprint determines
the complete flat physical execution: value, cost, ordered trace, successes,
failures, and repeated reads are all identical. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (left right : Nat)
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalStoresAgreeOnOrderedFootprint
        shape storeA storeB left right) :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeA left right =
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeB left right := by
  have hlogical :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeA)
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeB)
        left right := by
    rw [
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint_iff]
    intro segment index word? hmem
    apply hagree
    exact
      concreteBPNativeSuccinctRMQWholeQueryLogicalRead_mem_flatPhysicalFootprint
        shape storeA left right segment index word? hmem
  have heval :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
      shape
      (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeA)
      (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeB)
      left right hlogical
  unfold concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
  rw [heval]

/-- A disagreement at an address actually consumed by the first execution is
observable: the two complete physical executions cannot be equal.  This is the
checked corruption/non-agreement principle showing that the evaluator does not
ignore its supplied flat store. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_ne_of_consumed_read_disagreement
    (shape : Cartesian.CartesianShape)
    (storeA storeB : WordRAM.ReadStore) (left right address : Nat)
    (wordA? : Option WordRAM.Word)
    (hmem : WordRAM.TraceEvent.readWord 0 address wordA? ∈
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeA left right).trace)
    (hneq : storeA.readWord? 0 address ≠ storeB.readWord? 0 address) :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeA left right ≠
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeB left right := by
  intro heq
  have hmatchA :=
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_matchesReadStore
      shape storeA left right
      (WordRAM.TraceEvent.readWord 0 address wordA?) hmem
  have hmemB : WordRAM.TraceEvent.readWord 0 address wordA? ∈
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        shape storeB left right).trace := by
    rw [← heq]
    exact hmem
  have hmatchB :=
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_matchesReadStore
      shape storeB left right
      (WordRAM.TraceEvent.readWord 0 address wordA?) hmemB
  apply hneq
  calc
    storeA.readWord? 0 address = wordA? := hmatchA
    _ = storeB.readWord? 0 address := hmatchB.symm

/-- The canonical genuine physical execution is extensionally the translated
canonical logical execution because the canonical physical store adapter is
exactly the canonical logical store. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_eq_legacyTranslation
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right =
      concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult
        shape left right := by
  unfold concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
  rw [
    concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter_canonical,
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore]
  rfl

/-- Genuine flat execution refines canonical logical execution while preserving
the decoded result, modeled cost, and ordered trace under checked translation.
The read-event payload preserves both successful and failed reads verbatim. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).value /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).trace =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace.map
          (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) /\
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).toCosted =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_eq_legacyTranslation]
  exact ⟨
    (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysical_refines_logical
      shape left right).1,
    (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysical_refines_logical
      shape left right).2.1,
    (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysical_refines_logical
      shape left right).2.2.1⟩

/-- Every logical read, including a failed read, is retained at its translated
address in the genuine canonical physical execution. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_translated
    (shape : Cartesian.CartesianShape) (left right segment index : Nat)
    (word? : Option WordRAM.Word)
    (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace) :
    WordRAM.TraceEvent.readWord 0
        (concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index) word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).trace := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_eq_legacyTranslation]
  exact
    (concreteBPNativeSuccinctRMQWholeQueryReviewerPhysical_refines_logical
      shape left right).2.2.2 segment index word? hmem

/-- Every emitted logical read, successful or failed, belongs to a named live
source/region and is present at that source's checked translated address in the
genuine physical execution. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_has_listed_region
    (shape : Cartesian.CartesianShape) (left right segment index : Nat)
    (word? : Option WordRAM.Word)
    (hmem : WordRAM.TraceEvent.readWord segment index word? ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace) :
    Exists fun source : ReviewerSource =>
      Exists fun region : Nat =>
        source ∈ concreteBPNativeSuccinctRMQReviewerPhysicalSources /\
        concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
          some source /\
        source.region = region /\
        WordRAM.TraceEvent.readWord 0
            (concreteBPNativeSuccinctRMQReviewerPhysicalAddress
              shape segment index) word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace := by
  have hlt : segment < 21 :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
      shape left right hmem
  rcases
      (concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage segment).2 hlt
    with ⟨source, hsource⟩
  exact ⟨source, source.region,
    concreteBPNativeSuccinctRMQReviewerPhysicalSources_all source,
    hsource, rfl,
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_translated
      shape left right segment index word? hmem⟩

/-- The new execution-derived canonical footprint agrees with the earlier
translated-trace footprint, now as a consequence of genuine execution. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_eq_legacy
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right =
      concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint
        shape left right := by
  exact congrArg
    (fun result : WordRAM.TraceResult (Option Nat) =>
      result.trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | WordRAM.TraceEvent.readWord _ _ _ => none
        | _ => none)
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_eq_legacyTranslation
      shape left right)

/-- Successful reads of the genuine physical execution are positional reads
from the one canonical pre-execution word list. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_successful_read_backed
    (shape : Cartesian.CartesianShape) (left right : Nat)
    {address : Nat} {word : List Bool}
    (hmem : WordRAM.TraceEvent.readWord 0 address (some word) ∈
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).trace) :
    address <
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
        some word := by
  have hmatch :=
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_matchesReadStore
      shape (concreteBPNativeSuccinctRMQReviewerPhysicalReadStore shape)
      left right (WordRAM.TraceEvent.readWord 0 address (some word)) hmem
  have hread :
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? =
        some word := by
    simpa [WordRAM.TraceEvent.matchesReadStore,
      concreteBPNativeSuccinctRMQReviewerPhysicalReadStore] using hmatch
  exact ⟨(List.getElem?_eq_some_iff.mp hread).1, hread⟩

/-- Primitive operands in the genuine physical execution fit the one declared
reviewer word width. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_primitiveOperandsFit_reviewerWordBits
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event := by
  intro event hmem
  rw [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_eq_legacyTranslation]
    at hmem
  exact
    concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult_primitiveOperandsFit_reviewerWordBits
      shape left right event hmem

/-- Genuine canonical physical executions contain no synthetic cost-only
events. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_no_syntheticCostOnlyPrimitive
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive := by
  intro event hmem
  rw [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_eq_legacyTranslation]
    at hmem
  simp only [concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalTraceResult,
    List.mem_map] at hmem
  rcases hmem with ⟨logicalEvent, hlogical, rfl⟩
  have hno :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_no_syntheticCostOnlyPrimitive
      shape left right logicalEvent hlogical
  cases logicalEvent <;>
    simp [concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent,
      WordRAM.TraceEvent.isSyntheticCostOnlyPrimitive] at hno ⊢

/-- Every execution-derived canonical physical footprint address fits the one
query-independent reviewer word width. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_address_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) (left right address : Nat)
    (hmem : address ∈
      concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right) :
    address <
      2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size := by
  rw [
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_eq_legacy]
    at hmem
  exact
    concreteBPNativeSuccinctRMQWholeQueryReviewerPhysicalFootprint_address_fits_reviewerWordBits
      shape left right address hmem

/-- The canonical physical footprint is exactly the read-address projection of
the genuine canonical flat-store execution. -/
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_recorded
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        shape left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | WordRAM.TraceEvent.readWord _ _ _ => none
        | _ => none := by
  rfl

end SuccinctFinal

end RMQ
