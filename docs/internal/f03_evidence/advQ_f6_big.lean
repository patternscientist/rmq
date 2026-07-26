import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL / QUANTIFIER attack on F6 = leaf L1
`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore`, verdict S.

The defender's evidence quantified over: shapes of size 1..5 and bitvectors of
length 4,6,8,10; regime forcing only at size 3,4,5.  advQ_f6_thresh.lean shows
that whole range is DEGENERATE:
    bpFringeChunkBits(len) = 1 for every len <= 254 (flips to 2 at len 256)
    selectSuperSlot(q, superStride len) = 0 for every q < size when size <= 64
So the second chunk-width regime and every nonzero super slot were untested.

This file re-runs the defender's own experiments ABOVE both thresholds:
  * shape size n in {100, 128, 200, 512}  (n=100 -> 2 super slots, c=1;
    n=128 -> 2 super slots AND c=2; n=200 -> 3 slots; n=512 -> 5 slots)
  * all four forced regimes LONG / SPARSE / DENSE / NONE, driven by the
    segment-3 and segment-7 probe replies exactly as ChargedRankSelectLeafTrace
    .lean:1176 / :1201 branch on them
  * idx chosen to straddle super-slot boundaries (superStride-1, superStride,
    superStride+1, 2*superStride, n-1)
  * structurally maximal shapes at the SAME size: leftSpine (all opens then all
    closes), rightSpine (perfectly alternating), balanced, two pseudo-random.
  * plus RAW bitvectors (not BP codes) of length 256 and 512 with identical
    false-count but maximally different distributions, through the raw leaf.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace AdvQF6

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

/-- Pseudo-random shape of EXACTLY size n. -/
partial def randShape (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (randShape (seed * 7 + 3) k) (randShape (seed * 13 + 5) (n - k))

def shapesAt (n : Nat) : List (String × CartesianShape) :=
  [("leftSpine", leftSpine n), ("rightSpine", rightSpine n),
   ("balanced", balanced n), ("rand1", randShape 1 n), ("rand2", randShape 99 n)]

/-! ### raw leaf: same body, `bits` in place of `shape.bpCode` -/

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

/-- The raw leaf really is the shipped leaf, definitionally. -/
theorem L1raw_eq (s : CartesianShape) (st : WordRAM.ReadStore) (i : Nat) :
    L1raw s.bpCode st i =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s st i := rfl

/-! ### stores -/

def zeroW (w : Nat) : List Bool := List.replicate w false
def noiseW (w seg idx : Nat) : List Bool :=
  (List.range w).map fun k => (seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

/-- Segment 3 = super `rankBefore`, segment 7 = local `rankBefore`
(SuccinctFinal/RAM/Segments.lean:24-46).  Drive both directly. -/
def craft (w : Nat) (superMark localMark : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then some (if superMark then noiseW w 3 index else zeroW w)
    else if segment == 7 then some (if localMark then noiseW w 7 index else zeroW w)
    else some (noiseW w segment index)

def missingSuper (w : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 1 then none else some (noiseW w segment index)

/-! ### trace keys -/

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some x => String.mk (x.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i x? => s!"R({s},{i})->{wordStr x?}"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def key (r : WordRAM.TraceResult (Option Nat)) : String :=
  s!"{repr r.value}|" ++ String.intercalate ";" (r.trace.map evKey)

def segsOf (r : WordRAM.TraceResult (Option Nat)) : List Nat :=
  r.trace.filterMap fun ev =>
    match ev with
    | WordRAM.TraceEvent.readWord s _ _ => some s
    | _ => none

def regime (r : WordRAM.TraceResult (Option Nat)) : String :=
  let ss := segsOf r
  let has (a b : Nat) := ss.any (fun s => a <= s && s <= b)
  let l := has 9 12
  let sp := has 13 16
  let d := ss.any (fun s => s == 0)
  s!"{if l then "LONG" else ""}{if sp then "SPARSE" else ""}{if d then "DENSE" else ""}{if !l && !sp && !d then "NONE" else ""}"

/-! ### experiment 1: shapes at the SAME large size, all four regimes -/

def runShapes (n : Nat) (w : Nat) : IO Unit := do
  let ss := GenericSelect.superStride (2 * n)
  let idxs := ([0, 1, ss - 1, ss, ss + 1, 2 * ss, 2 * ss + 1, n - 1].filter
                 (fun i => i < n)).eraseDups
  IO.println s!"-- n={n} bpLen={2*n} c={SuccinctClose.bpFringeChunkBits (2*n)} superStride={ss} idxs={idxs} wordWidth={w}"
  for (lbl, st) in [("LONGforce ", craft w true true),
                    ("SPARSEforce", craft w false true),
                    ("DENSEforce ", craft w false false),
                    ("NONEforce  ", missingSuper w)] do
    let mut mism := 0
    let mut regs : List String := []
    let mut witness := ""
    for idx in idxs do
      let rs := (shapesAt n).map (fun p => (p.1, L1raw p.2.bpCode st idx))
      let ks := rs.map (fun p => (p.1, key p.2))
      let k0 := (ks.headD ("", "")).2
      for (nm, k) in ks do
        if k != k0 then
          mism := mism + 1
          if witness == "" then witness := s!" FIRST-DIVERGENCE idx={idx} shape={nm}"
      regs := (regs ++ rs.map (fun p => regime p.2)).eraseDups
    IO.println s!"   {lbl} regimes={regs} SHAPE-MISMATCHES={mism}{witness}"

#eval show IO Unit from do
  IO.println "== EXP1: identical-size shapes above the c and super-slot thresholds =="
  runShapes 100 16
  runShapes 128 16
  runShapes 200 16

end AdvQF6
