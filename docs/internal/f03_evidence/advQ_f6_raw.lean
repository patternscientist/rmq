import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL / QUANTIFIER attack on F6 (leaf L1), verdict S.

Strictly stronger than the shape sweep: run the leaf on RAW bitvectors (a
superset of BP codes) at lengths ABOVE both size thresholds the defender never
crossed:

  bpFringeChunkBits(len) = Nat.log2 len / 8 + 1  ->  1 for len <= 254, 2 at 256
  selectSuperSlot(q, superStride len)            ->  always 0 when len <= 128

The defender swept lengths 4, 6, 8, 10 only: c = 1 and super slot 0 throughout.
Here: lengths 256 and 512, false-count fixed per group (so `occurrenceCount`
matches, exactly as it must for two BP codes of one size), distributions
maximally different, and idx driven across the super-slot boundaries
(superStride-1, superStride, superStride+1, 2*superStride).  All four regimes
are forced through the segment-3 / segment-7 probe replies.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose

namespace AdvQF6Raw

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

/-- The raw leaf IS the shipped leaf at `bits := shape.bpCode`, definitionally. -/
theorem L1raw_eq (s : CartesianShape) (st : WordRAM.ReadStore) (i : Nat) :
    L1raw s.bpCode st i =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s st i := rfl

def zeroW (w : Nat) : List Bool := List.replicate w false
def noiseW (w seg idx : Nat) : List Bool :=
  (List.range w).map fun k => (seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

def craft (w : Nat) (superMark localMark : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then some (if superMark then noiseW w 3 index else zeroW w)
    else if segment == 7 then some (if localMark then noiseW w 7 index else zeroW w)
    else some (noiseW w segment index)

def missingSuper (w : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 1 then none else some (noiseW w segment index)

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

/-! ### families: length 2k, exactly k falses, maximally different layouts -/

def famBlockTF (k : Nat) : List Bool := List.replicate k true ++ List.replicate k false
def famBlockFT (k : Nat) : List Bool := List.replicate k false ++ List.replicate k true
def famAlt (k : Nat) : List Bool := (List.range (2 * k)).map fun i => i % 2 == 0
def famAltInv (k : Nat) : List Bool := (List.range (2 * k)).map fun i => i % 2 == 1
/-- pseudo-random with EXACTLY k falses: place falses at a scattered index set. -/
def famScatter (k seed : Nat) : List Bool :=
  let idxs := (List.range k).map (fun j => (j * 2 + (j * seed) % 2))
  let idxs := idxs.foldl (fun (acc : List Nat) i =>
      if acc.contains i then acc ++ [i + 1] else acc ++ [i]) []
  (List.range (2 * k)).map fun i => !(idxs.contains i)
/-- clustered: falses in the middle. -/
def famMid (k : Nat) : List Bool :=
  List.replicate (k / 2) true ++ List.replicate k false ++
    List.replicate (k - k / 2) true

def famsAt (k : Nat) : List (String × List Bool) :=
  [("blockTF", famBlockTF k), ("blockFT", famBlockFT k), ("alt", famAlt k),
   ("altInv", famAltInv k), ("scatter3", famScatter k 3), ("mid", famMid k)]

def runRaw (k : Nat) (w : Nat) : IO Unit := do
  let len := 2 * k
  let ss := GenericSelect.superStride len
  let fams := famsAt k
  IO.println s!"-- len={len} c={SuccinctClose.bpFringeChunkBits len} superStride={ss} wordBits={GenericSelect.wordBits len}"
  for (nm, b) in fams do
    IO.println s!"     fam {nm}: length={b.length} falseCount={GenericSelect.occurrenceCount b false} first16={String.mk ((b.take 16).map fun x => if x then '1' else '0')}"
  let idxs := ([0, 1, ss - 1, ss, ss + 1, 2 * ss, k - 1].filter (fun i => i < k)).eraseDups
  IO.println s!"     idxs={idxs}  maxSuperSlot={GenericSelect.selectSuperSlot (idxs.foldl Nat.max 0) ss}"
  for (lbl, st) in [("LONGforce  ", craft w true true),
                    ("SPARSEforce", craft w false true),
                    ("DENSEforce ", craft w false false),
                    ("NONEforce  ", missingSuper w)] do
    let mut mism := 0
    let mut regs : List String := []
    let mut witness := ""
    for idx in idxs do
      let rs := fams.map (fun p => (p.1, L1raw p.2 st idx))
      let ks := rs.map (fun p => (p.1, key p.2))
      let k0 := (ks.headD ("", "")).2
      for (nm2, kk) in ks do
        if kk != k0 then
          mism := mism + 1
          if witness == "" then witness := s!"  *** DIVERGENCE idx={idx} fam={nm2}"
      regs := (regs ++ rs.map (fun p => regime p.2)).eraseDups
    IO.println s!"   {lbl} regimes={regs} CONTENT-MISMATCHES={mism}{witness}"

#eval show IO Unit from do
  IO.println "== RAW bitvectors, equal length + equal falseCount, above both thresholds =="
  runRaw 64 16    -- len 128, c=1, single super slot (control: matches defender regime)
  runRaw 128 16   -- len 256, c=2 AND 2 super slots
  runRaw 256 16   -- len 512, c=2, 3 super slots

end AdvQF6Raw
