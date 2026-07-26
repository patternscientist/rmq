import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION, round 2, against verdict S for F1.

Round 1 found no same-size divergence.  Round 2 attacks the SIDE-CLAIMS that the
S verdict rests on or advertises:

  (A) "arity at most 11 probes -- constant"  -> hunt for a store/size that exceeds it.
  (B) "segment base+3 is never read"          -> hunt for any read outside {+0,+1,+2,+4}.
  (C) CONSTRUCTIVE form of S: is there actually a shape-FREE replacement?
      If S is real, `F1 s = F1 (spine s.size)` must be a theorem, i.e. the packed
      controller can drop `shape` entirely and rebuild from n.  Checked, not evalled.
  (D) Is the leaf's VALUE computable from n alone?  (The literal reading of the
      S definition.)  Attempt to refute: same n, same base, same pos, DIFFERENT store.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace AdvF1b

def spine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (spine n)

theorem spine_size (n : Nat) : (spine n).size = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [spine, CartesianShape.size, ih]; omega

def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store base pos

/-! ### (C) CONSTRUCTIVE S: the shape argument is replaceable by `n`. -/

theorem builtData_wordSize (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).wordSize
      = SuccinctRank.machineWordBits shape.bpCode.length := rfl

theorem builtData_blocksPerSuper (shape : CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper
      = SuccinctRank.machineWordBits shape.bpCode.length := rfl

theorem chunkedRank_congr
    {bits1 bits2 : List Bool} {so1 bo1 qc1 so2 bo2 qc2 : Nat}
    (d1 : TwoLevelPayloadLiveStoredWordRankData bits1 so1 bo1 qc1)
    (d2 : TwoLevelPayloadLiveStoredWordRankData bits2 so2 bo2 qc2)
    (hlen : bits1.length = bits2.length)
    (hws : d1.wordSize = d2.wordSize)
    (hbps : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : WordRAM.ReadStore) (ss bs ws cs c1 c2 : Nat) (hc : c1 = c2)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store ss bs ws cs c1 target pos
      = d2.bpChunkedRankTraceResultWithStore store ss bs ws cs c2 target pos := by
  have hq : d1.queryPos pos = d2.queryPos pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.queryPos, hlen]
  have hwi : d1.wordIndex pos = d2.wordIndex pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.wordIndex, hq, hws]
  have hsi : d1.superIndex pos = d2.superIndex pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.superIndex, hwi, hbps]
  have hwo : d1.wordOffset pos = d2.wordOffset pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.wordOffset, hq, hwi, hws]
  unfold TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  rw [hsi, hwi, hwo, hc]

/-- CONSTRUCTIVE S: every appeal to `shape` inside F1 may be replaced by the
canonical right spine of the same size, i.e. by `n` alone.  This is the form the
packed rewrite actually needs: it exhibits the shape-free substitute. -/
theorem F1_eq_of_size (s : CartesianShape) (store : WordRAM.ReadStore)
    (base pos : Nat) :
    F1 s store base pos = F1 (spine s.size) store base pos := by
  have hlen : s.bpCode.length = (spine s.size).bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, spine_size]
  unfold F1 concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  exact
    chunkedRank_congr
      (builtRelativeSplitBPCloseRankData s)
      (builtRelativeSplitBPCloseRankData (spine s.size))
      hlen
      (by rw [builtData_wordSize, builtData_wordSize, hlen])
      (by rw [builtData_blocksPerSuper, builtData_blocksPerSuper, hlen])
      store base (base + 1) (base + 2) (base + 4) _ _ (by rw [hlen]) false pos

#print axioms F1_eq_of_size

/-! ### (A)/(B) probe-count and segment-locality hunt over adversarial stores. -/

def wideStore (len : Nat) : WordRAM.ReadStore where
  readWord? := fun s i => some ((List.range len).map (fun k => (k * 3 + s + i * 5) % 2 == 0))

def allTrue (len : Nat) : WordRAM.ReadStore where
  readWord? := fun _ _ => some (List.replicate len true)

def altStore (len : Nat) : WordRAM.ReadStore where
  readWord? := fun _ _ => some ((List.range len).map (fun k => k % 2 == 0))

def reads (r : WordRAM.TraceResult Nat) : List (Nat × Nat) :=
  r.trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

#eval show IO Unit from do
  let mut maxReads := 0
  let mut maxAt := ""
  let mut offSegment : List (Nat × Nat) := []
  let mut maxTrace := 0
  for wl in [0, 1, 2, 3, 5, 8, 16, 64, 200, 1000] do
    for st in [("wide", wideStore wl), ("allTrue", allTrue wl), ("alt", altStore wl)] do
      for n in [1, 2, 3, 5, 8, 13, 30, 64, 200] do
        let s := spine n
        for p in [0, 1, 2, 3, 5, 9, 17, 33, 100, 999, 100000] do
          let r := F1 s st.2 6 p
          let rs := reads r
          if rs.length > maxReads then
            maxReads := rs.length
            maxAt := s!"wordLen={wl} store={st.1} n={n} pos={p}"
          if r.trace.length > maxTrace then maxTrace := r.trace.length
          for (sg, _) in rs do
            if sg != 6 && sg != 7 && sg != 8 && sg != 10 then
              offSegment := (sg, n) :: offSegment
  IO.println s!"PROBECOUNT maxReads={maxReads} at [{maxAt}] maxTraceLen={maxTrace}"
  IO.println s!"SEGMENTLOCALITY readsOutside(base+0,+1,+2,+4)={offSegment.length} \
(base=6, so base+3=9 must be absent) sample={offSegment.take 3}"

/-! ### (D) Is the leaf VALUE a function of n alone?  Attempt to REFUTE the
literal reading of S ("computable from n"): fix n, base, pos; vary only the store. -/

#eval show IO Unit from do
  let s := spine 7
  let vals := [("wide16", wideStore 16), ("allTrue16", allTrue 16), ("alt16", altStore 16),
    ("wide3", wideStore 3)].map fun st => (st.1, (F1 s st.2 6 9).value, reads (F1 s st.2 6 9))
  IO.println s!"VALUE-NOT-FROM-n n=7 base=6 pos=9 {vals}"

end AdvF1b
