import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL ATTACK on the S verdict for F6 / leaf L1, part 2.

Adds to attack3:
  E1 boundary indices (idx at / around superStride and localSlotsPerSuper)
  E2 larger n
  E3 ANTI-VACUITY controls: the instrument must SEE a difference when the
     length or the false-count changes
  E4 raw-bitvector superset at nondegenerate length, same false-count
  E5 EXHAUSTIVE enumeration of every shape of size 6, 7, 8
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6D

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_attack4_log.txt"

def logLine (s : String) : IO Unit := do
  let h <- IO.FS.Handle.mk logFile IO.FS.Mode.append
  h.putStrLn s
  h.flush

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

theorem L1raw_eq (shape : CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    L1raw shape.bpCode store idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape store idx := rfl

def smallStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    let v := (salt + segment * 5 + index * 3) % 16
    some ((List.range 4).map fun k => (v / 2 ^ k) % 2 == 1)

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 8).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

def boundedStore (salt lim : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    if index < lim then
      some ((List.range 4).map fun k =>
        (salt + segment * 5 + index * 3 + k) % 3 == 0)
    else none

def regimeStore (salt : Nat) (superMark localMark : Bool) :
    WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then
      some (if superMark then [true, false, false, false] else [false, false, false, false])
    else if segment == 7 then
      some (if localMark then [true, false, false, false] else [false, false, false, false])
    else
      let v := (salt + segment * 5 + index * 3) % 16
      some ((List.range 4).map fun k => (v / 2 ^ k) % 2 == 1)

def stores : List (String × WordRAM.ReadStore) :=
  [ ("small7", smallStore 7)
  , ("small0", smallStore 0)
  , ("noise11", noiseStore 11)
  , ("bounded3", boundedStore 5 3)
  , ("bounded1", boundedStore 5 1)
  , ("LONG", regimeStore 7 true false)
  , ("SPARSE", regimeStore 7 false true)
  , ("DENSE", regimeStore 7 false false)
  , ("SPARSE2", regimeStore 2 false true)
  , ("DENSE2", regimeStore 2 false false) ]

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some w => String.mk (w.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i w? => s!"R({s},{i})->{wordStr w?}"
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

/-- Build `sparseExceptionSelectData` ONCE per bit list, then run all
(store, idx) pairs against it. -/
def bitsKeys (bits : List Bool) (idxs : List Nat) :
    IO (List String × List String × Nat) := do
  let t0 <- IO.monoMsNow
  let data := sparseExceptionSelectData bits false
  let c := SuccinctClose.bpFringeChunkBits bits.length
  let mut ks : List String := []
  let mut regs : List String := []
  for (_, store) in stores do
    for idx in idxs do
      let r :=
        data.bpChunkedSelectTraceResultWithStore
          concreteBPNativeSelectCloseTraceSegmentLayout
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment store c idx
      ks := ks ++ [key r]
      regs := (regs ++ [regime r]).eraseDups
  let t1 <- IO.monoMsNow
  pure (ks, regs, t1 - t0)

/-- Compare a family of bit lists; report mismatches against the first. -/
def diffFamily (label : String) (fam : List (String × List Bool))
    (idxs : List Nat) (expectSame : Bool) : IO Unit := do
  let lens := (fam.map fun p => p.2.length).eraseDups
  let occs := (fam.map fun p => occurrenceCount p.2 false).eraseDups
  let distinct := (fam.map fun p => p.2).eraseDups
  logLine s!"--- {label}: members={fam.length} distinctBits={distinct.length} lengths={lens} falseCounts={occs} idxs={idxs}"
  let mut base : Option (List String) := none
  let mut baseName := ""
  let mut mism := 0
  let mut allRegs : List String := []
  let mut totalMs := 0
  for (nm, bits) in fam do
    let (ks, regs, ms) <- bitsKeys bits idxs
    totalMs := totalMs + ms
    allRegs := (allRegs ++ regs).eraseDups
    match base with
    | none => base := some ks; baseName := nm
    | some b =>
        let bad := (List.range ks.length).filter (fun i => b[i]! != ks[i]!)
        if bad.length != 0 then
          mism := mism + bad.length
          if mism <= 2 then
            let i := bad.head!
            logLine s!"  DIFF {baseName} vs {nm} at {bad.length}/{ks.length} positions; first pos={i}"
            logLine s!"    A={b[i]!}"
            logLine s!"    B={ks[i]!}"
  let verdict :=
    if expectSame then (if mism == 0 then "OK-NO-DIFFERENCE" else "*** REFUTED: DIFFERENCE FOUND ***")
    else (if mism == 0 then "*** INSTRUMENT BLIND (no difference where one was expected) ***" else "OK-CONTROL-SEES-DIFFERENCE")
  logLine s!"=== {label} MISMATCHES={mism} regimes={allRegs} [{totalMs}ms] {verdict}"

/-! ## Shape families -/

def spine : List Bool -> CartesianShape
  | [] => CartesianShape.empty
  | true :: bs => CartesianShape.node CartesianShape.empty (spine bs)
  | false :: bs => CartesianShape.node (spine bs) CartesianShape.empty

def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node (balanced (k / 2)) (balanced (k - k / 2))

def pat (seed n : Nat) : List Bool :=
  (List.range n).map fun i => (seed * 977 + i * 1103 + i * i * 65537) % 7 < 3

def shapeFamily (n : Nat) : List (String × List Bool) :=
  ([ ("rightComb", spine (List.replicate n true))
   , ("leftComb",  spine (List.replicate n false))
   , ("alt",       spine ((List.range n).map (fun i => i % 2 == 0)))
   , ("blocks",    spine ((List.range n).map (fun i => i % 8 < 4)))
   , ("halfhalf",  spine ((List.range n).map (fun i => 2 * i < n)))
   , ("balanced",  balanced n)
   , ("rand1",     spine (pat 1 n))
   , ("rand2",     spine (pat 2 n))
   , ("rand3",     spine (pat 3 n)) ]).map fun p => (p.1, p.2.bpCode)

/-- Every shape of size `n` (fuel-driven so it is structurally recursive). -/
def allShapesF : Nat -> Nat -> List CartesianShape
  | 0, _ => [CartesianShape.empty]
  | _, 0 => [CartesianShape.empty]
  | Nat.succ n, Nat.succ f =>
      (List.range (n + 1)).flatMap fun k =>
        (allShapesF k f).flatMap fun l =>
          (allShapesF (n - k) f).map fun r => CartesianShape.node l r

def allShapes (n : Nat) : List CartesianShape := allShapesF n n

/-! ## E1 / E2: boundary indices and larger n -/

#eval show IO Unit from do
  IO.FS.writeFile logFile "attack4 start\n"
  logLine "== E1: boundary indices at nondegenerate sizes =="
  -- n=63: superStride = 49, localSlotsPerSuper = 49, superSlotCount = 2
  diffFamily "n=63 boundary" (shapeFamily 63) [47, 48, 49, 50, 51, 97, 98, 99] true
  -- n=65: superStride = 64, superSlotCount = 2
  diffFamily "n=65 boundary" (shapeFamily 65) [62, 63, 64, 65, 66, 127, 128, 129] true

#eval show IO Unit from do
  logLine "== E3: ANTI-VACUITY controls (a difference MUST be seen) =="
  -- same length, DIFFERENT false-count: must differ
  let len := 126
  diffFamily "control len=126 falseCount 63 vs 62 vs 61"
    [ ("f63", (List.range len).map (fun i => i % 2 == 1))
    , ("f62", (List.range len).map (fun i => if i == 0 then true else i % 2 == 1))
    , ("f61", (List.range len).map (fun i => if i <= 2 then true else i % 2 == 1)) ]
    [0, 1, 5, 40] false
  -- DIFFERENT length, same false-count: must differ
  diffFamily "control length 126 vs 128 vs 200, falseCount 63"
    [ ("l126", (List.range 126).map (fun i => i % 2 == 1))
    , ("l128", (List.range 126).map (fun i => i % 2 == 1) ++ [true, true])
    , ("l200", (List.range 126).map (fun i => i % 2 == 1) ++ List.replicate 74 true) ]
    [0, 1, 5, 40] false
  -- sanity: shapes of different SIZE must differ
  diffFamily "control shapes size 63 vs 64"
    [ ("s63", (spine (List.replicate 63 true)).bpCode)
    , ("s64", (spine (List.replicate 64 true)).bpCode) ]
    [0, 1, 5, 40] false

#eval show IO Unit from do
  logLine "== E4: raw-bitvector SUPERSET, length 126, falseCount 63 =="
  -- Bit lists of length 126 with exactly 63 falses, wildly different content,
  -- most of which are NOT balanced-parenthesis codes at all.
  let mk (f : Nat -> Bool) : List Bool := (List.range 126).map f
  diffFamily "len=126 falseCount=63 superset"
    [ ("alt01",   mk (fun i => i % 2 == 0))
    , ("alt10",   mk (fun i => i % 2 == 1))
    , ("halves",  mk (fun i => i < 63))
    , ("halvesR", mk (fun i => 63 <= i))
    , ("blocks7", mk (fun i => (i / 7) % 2 == 0))
    , ("blocks3", mk (fun i => (i / 3) % 2 == 0))
    , ("bpRight", (spine (List.replicate 63 true)).bpCode)
    , ("bpLeft",  (spine (List.replicate 63 false)).bpCode)
    , ("bpRand",  (spine (pat 5 63)).bpCode) ]
    [0, 1, 5, 31, 48, 49, 50, 62] true

#eval show IO Unit from do
  logLine "== E2: larger n =="
  diffFamily "n=100" (shapeFamily 100) [0, 1, 63, 64, 65, 99] true
  diffFamily "n=128" (shapeFamily 128) [0, 1, 80, 81, 82, 127] true

end AdvS6D
