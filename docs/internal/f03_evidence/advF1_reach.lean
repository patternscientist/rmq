import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
REACHABILITY attack on F1 = S.
(1) Re-derive the size-only theorem with FULLY QUALIFIED names (no `open`), to rule
    out any name-resolution trick in the defender's file.
(2) Establish that F1 is genuinely ON the executed controller path, and at WHICH
    segments/positions -- the defender's table used base 6, but
    concreteBPNativeRankCloseTraceSegmentBase = 17.
(3) In-situ test: same-size, structurally different shapes, ONE fixed shape-free
    store, whole-query controller. Does anything shape-dependent survive?
-/

namespace AdvReach

open RMQ

-- (1) fully-qualified independent re-derivation
theorem F1_size_only_fullnames
    (s1 s2 : RMQ.Cartesian.CartesianShape)
    (hsize : s1.size = s2.size)
    (store : RMQ.WordRAM.ReadStore) (base pos : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        s1 store base pos
      = RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        s2 store base pos := by
  have hlen : s1.bpCode.length = s2.bpCode.length := by
    rw [RMQ.Cartesian.CartesianShape.bpCode_length,
      RMQ.Cartesian.CartesianShape.bpCode_length, hsize]
  have hws :
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s1).wordSize
        = (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s2).wordSize := by
    show RMQ.SuccinctRank.machineWordBits s1.bpCode.length
      = RMQ.SuccinctRank.machineWordBits s2.bpCode.length
    rw [hlen]
  have hbps :
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s1).blocksPerSuper
        = (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s2).blocksPerSuper := by
    show RMQ.SuccinctRank.machineWordBits s1.bpCode.length
      = RMQ.SuccinctRank.machineWordBits s2.bpCode.length
    rw [hlen]
  have hq : forall p,
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s1).queryPos p
        = (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s2).queryPos p := by
    intro p
    simp [RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.queryPos, hlen]
  have hwi : forall p,
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s1).wordIndex p
        = (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s2).wordIndex p := by
    intro p
    simp [RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordIndex, hq, hws]
  have hsi : forall p,
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s1).superIndex p
        = (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s2).superIndex p := by
    intro p
    simp [RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.superIndex, hwi, hbps]
  have hwo : forall p,
      (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s1).wordOffset p
        = (RMQ.SuccinctFinal.builtRelativeSplitBPCloseRankData s2).wordOffset p := by
    intro p
    simp [RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.wordOffset, hq, hwi, hws]
  have hc : RMQ.SuccinctClose.bpFringeChunkBits s1.bpCode.length
      = RMQ.SuccinctClose.bpFringeChunkBits s2.bpCode.length := by rw [hlen]
  unfold RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  unfold RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  rw [hsi, hwi, hwo, hc]

#print axioms F1_size_only_fullnames

-- (2)(3) executed reachability
open RMQ.Cartesian RMQ.SuccinctFinal

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

def zigzag : Nat -> Bool -> CartesianShape
  | 0, _ => CartesianShape.empty
  | Nat.succ n, true => CartesianShape.node (zigzag n false) CartesianShape.empty
  | Nat.succ n, false => CartesianShape.node CartesianShape.empty (zigzag n true)

def comb : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | 1 => CartesianShape.node CartesianShape.empty CartesianShape.empty
  | (n + 2) =>
      CartesianShape.node (CartesianShape.node CartesianShape.empty CartesianShape.empty) (comb n)

def family (n : Nat) : List (String × CartesianShape) :=
  [("rspine", rightSpine n), ("lspine", leftSpine n),
   ("zigL", zigzag n true), ("zigR", zigzag n false), ("comb", comb n)]

def hashStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 16).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

def wholeReads (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r

def wholeOut (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) : Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st l r).value

-- Is F1 reached at all in a REAL execution? Which segments does the whole query touch?
#eval show IO Unit from do
  IO.println s!"rankSegmentBase={concreteBPNativeRankCloseTraceSegmentBase}"
  for n in [4, 8] do
    let s := rightSpine n
    let st := concreteBPNativeSuccinctRMQGlobalReadStore s
    let fp := wholeReads s st 0 n
    let segs := (fp.map Prod.fst).eraseDups
    let rankSegs := fp.filter (fun p => p.1 = 17 || p.1 = 18 || p.1 = 19 || p.1 = 21)
    IO.println s!"REACH n={n} canonicalStore segsTouched={segs} rankSegReads={rankSegs} out={wholeOut s st 0 n}"

-- In-situ: same-size different shapes, ONE fixed shape-free store, full controller
#eval show IO Unit from do
  for n in [4, 6, 8, 12] do
    let fam := family n
    let mut lines : List String := []
    for (nm, s) in fam do
      let mut allfp : List (Nat × Nat) := []
      let mut outs : List (Option Nat) := []
      for l in [0, 1, 2] do
        for r in [n, n - 1, 3] do
          allfp := allfp ++ wholeReads s hashStore l r
          outs := outs ++ [wholeOut s hashStore l r]
      let rankOnly := allfp.filter (fun p => p.1 = 17 || p.1 = 18 || p.1 = 19 || p.1 = 21)
      lines := lines ++ [s!"{nm}:fp#{allfp.length}:rank#{rankOnly.length}:h{allfp.foldl (fun a p => (a * 31 + p.1 * 7 + p.2) % 1000003) 7}:o{outs.foldl (fun a o => (a * 31 + o.getD 999) % 1000003) 7}:rh{rankOnly.foldl (fun a p => (a * 31 + p.1 * 7 + p.2) % 1000003) 7}"]
    IO.println s!"INSITU n={n}"
    for l in lines do
      IO.println s!"   {l}"

end AdvReach
