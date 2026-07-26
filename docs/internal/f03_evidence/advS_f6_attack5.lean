import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL ATTACK on the S verdict for F6 / leaf L1, part 3.

  E3b fixed anti-vacuity control: same length, different false-count, with
      idx values that CROSS the domain guard `idx < occurrenceCount bits false`
  E5  EXHAUSTIVE enumeration of every shape of size 6, 7, 8
  E6  many random stores (60) at n = 63
  E7  wide-word stores (64-bit words -> huge decoded addresses)
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6E

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_attack5_log.txt"

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

/-! ## Stores -/

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

/-- Wide 32-bit words: decoded addresses become enormous. -/
def wideStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 32).map fun k =>
      (salt + segment * 31 + index * 17 + k * 13) % 5 < 2)

/-- Arbitrary pseudo-random store, parameterized by seed; word WIDTH also
varies with (segment, index, seed), and some addresses answer `none`. -/
def randStore (seed : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    let h := (seed * 2654435761 + segment * 40503 + index * 2246822519) % 1000003
    if h % 11 == 0 then none
    else
      let w := 1 + h % 12
      some ((List.range w).map fun k => (h / (k + 1) + k) % 3 == 0)

def baseStores : List (String × WordRAM.ReadStore) :=
  [ ("small7", smallStore 7)
  , ("small0", smallStore 0)
  , ("noise11", noiseStore 11)
  , ("bounded3", boundedStore 5 3)
  , ("bounded1", boundedStore 5 1)
  , ("LONG", regimeStore 7 true false)
  , ("SPARSE", regimeStore 7 false true)
  , ("DENSE", regimeStore 7 false false)
  , ("wide1", wideStore 1)
  , ("wide9", wideStore 9) ]

def manyRandStores (k : Nat) : List (String × WordRAM.ReadStore) :=
  (List.range k).map fun s => (s!"rand{s}", randStore (s + 1))

/-! ## Keys -/

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

def bitsKeys (sts : List (String × WordRAM.ReadStore))
    (bits : List Bool) (idxs : List Nat) :
    IO (List String × List String × Nat) := do
  let t0 <- IO.monoMsNow
  let data := sparseExceptionSelectData bits false
  let c := SuccinctClose.bpFringeChunkBits bits.length
  let mut ks : List String := []
  let mut regs : List String := []
  for (_, store) in sts do
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

def diffFamily (sts : List (String × WordRAM.ReadStore))
    (label : String) (fam : List (String × List Bool))
    (idxs : List Nat) (expectSame : Bool) : IO Unit := do
  let lens := (fam.map fun p => p.2.length).eraseDups
  let occs := (fam.map fun p => occurrenceCount p.2 false).eraseDups
  let distinct := (fam.map fun p => p.2).eraseDups
  let mut base : Option (List String) := none
  let mut baseName := ""
  let mut mism := 0
  let mut cmps := 0
  let mut allRegs : List String := []
  let mut totalMs := 0
  for (nm, bits) in fam do
    let (ks, regs, ms) <- bitsKeys sts bits idxs
    totalMs := totalMs + ms
    allRegs := (allRegs ++ regs).eraseDups
    match base with
    | none => base := some ks; baseName := nm
    | some b =>
        cmps := cmps + ks.length
        let bad := (List.range ks.length).filter (fun i => b[i]! != ks[i]!)
        if bad.length != 0 then
          mism := mism + bad.length
          if mism <= bad.length then
            let i := bad.head!
            logLine s!"  DIFF {baseName} vs {nm} at {bad.length}/{ks.length}; first pos={i}"
            logLine s!"    A={b[i]!}"
            logLine s!"    B={ks[i]!}"
  let verdict :=
    if expectSame then (if mism == 0 then "OK-NO-DIFFERENCE" else "*** REFUTED ***")
    else (if mism == 0 then "*** INSTRUMENT BLIND ***" else "OK-CONTROL-SEES-DIFFERENCE")
  logLine s!"=== {label} members={fam.length} distinctBits={distinct.length} lengths={lens} falseCounts={occs} comparisons={cmps} MISMATCHES={mism} regimes={allRegs} [{totalMs}ms] {verdict}"

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

def allShapesF : Nat -> Nat -> List CartesianShape
  | 0, _ => [CartesianShape.empty]
  | _, 0 => [CartesianShape.empty]
  | Nat.succ n, Nat.succ f =>
      (List.range (n + 1)).flatMap fun k =>
        (allShapesF k f).flatMap fun l =>
          (allShapesF (n - k) f).map fun r => CartesianShape.node l r

def allShapes (n : Nat) : List CartesianShape := allShapesF n n

/-! ## E3b: fixed anti-vacuity control -/

#eval show IO Unit from do
  IO.FS.writeFile logFile "attack5 start\n"
  logLine "== E3b: control -- same length, different falseCount, idx CROSSING the guard =="
  diffFamily baseStores "control len=126 falseCount 63/62/61 idx=60..63"
    [ ("f63", (List.range 126).map (fun i => i % 2 == 1))
    , ("f62", (List.range 126).map (fun i => if i == 0 then true else i % 2 == 1))
    , ("f61", (List.range 126).map (fun i => if i <= 2 then true else i % 2 == 1)) ]
    [60, 61, 62, 63] false

/-! ## E5: EXHAUSTIVE same-size shape enumeration -/

def exhaustive (n : Nat) (idxs : List Nat) : IO Unit := do
  let shapes := allShapes n
  let sizes := (shapes.map (fun s => s.size)).eraseDups
  let codes := (shapes.map (fun s => s.bpCode)).eraseDups
  let fam := (List.range shapes.length).map fun i => (s!"s{i}", shapes[i]!.bpCode)
  logLine s!"  [exhaustive n={n}] shapeCount={shapes.length} sizes={sizes} distinctBpCodes={codes.length}"
  diffFamily baseStores s!"EXHAUSTIVE n={n}" fam idxs true

#eval show IO Unit from do
  logLine "== E5: exhaustive enumeration of ALL shapes of a given size =="
  exhaustive 6 [0, 1, 2, 3, 5, 6, 7]
  exhaustive 7 [0, 1, 3, 6, 7, 8]

#eval show IO Unit from do
  exhaustive 8 [0, 1, 4, 7, 8, 9]

/-! ## E6/E7: many random stores + wide stores at nondegenerate n -/

#eval show IO Unit from do
  logLine "== E6: 60 pseudo-random stores (varying word widths, some `none`) at n=63 =="
  diffFamily (manyRandStores 60) "n=63 x 60 random stores"
    (shapeFamily 63) [0, 1, 5, 48, 49, 62] true
  logLine "== E7: wide (32-bit) word stores at n=65 and n=100 =="
  diffFamily [("wide1", wideStore 1), ("wide2", wideStore 2), ("wide3", wideStore 3)]
    "n=65 wide" (shapeFamily 65) [0, 1, 5, 63, 64, 64] true
  diffFamily [("wide1", wideStore 1), ("wide2", wideStore 2), ("wide3", wideStore 3)]
    "n=100 wide" (shapeFamily 100) [0, 1, 5, 63, 64, 99] true

end AdvS6E
