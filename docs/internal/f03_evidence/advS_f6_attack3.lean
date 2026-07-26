import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL ATTACK on the S verdict for F6 / leaf L1, at NONDEGENERATE sizes.

`L1raw bits store idx` is by definition
  (sparseExceptionSelectData bits false).bpChunkedSelectTraceResultWithStore
     LAYOUT 21 22 store (bpFringeChunkBits bits.length) idx
so I hoist the (expensive, content-dependent) `sparseExceptionSelectData`
build out of the idx/store loops -- sharing a pure `let` is semantically the
identity, and `L1shared_eq` below is the kernel-checked `rfl` witness.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6C

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_attack3_log.txt"

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

/-- The hoisted form used by the sweep, and its `rfl` witness. -/
def L1shared {bits : List Bool}
    (data :
      SparseExceptionSelectData bits false
        (sparseExceptionEffectiveFlagRankSuperOverhead bits false)
        (sparseExceptionEffectiveFlagRankBlockOverhead bits false))
    (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  data.bpChunkedSelectTraceResultWithStore
    concreteBPNativeSelectCloseTraceSegmentLayout
    concreteBPNativeFringeChunkTraceSegment
    concreteBPNativeSelectChunkTraceSegment store
    (SuccinctClose.bpFringeChunkBits bits.length) idx

theorem L1shared_eq (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    L1shared (sparseExceptionSelectData bits false) store idx
      = L1raw bits store idx := rfl

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

/-! ## Trace keys -/

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

/-! ## Same-size shape families -/

def spine : List Bool -> CartesianShape
  | [] => CartesianShape.empty
  | true :: bs => CartesianShape.node CartesianShape.empty (spine bs)
  | false :: bs => CartesianShape.node (spine bs) CartesianShape.empty

def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node (balanced (k / 2)) (balanced (k - k / 2))

def pat (seed n : Nat) : List Bool :=
  (List.range n).map fun i => (seed * 977 + i * 1103 + i * i * 65537) % 7 < 3

def family (n : Nat) : List (String × CartesianShape) :=
  [ ("rightComb", spine (List.replicate n true))
  , ("leftComb",  spine (List.replicate n false))
  , ("alt",       spine ((List.range n).map (fun i => i % 2 == 0)))
  , ("blocks",    spine ((List.range n).map (fun i => i % 8 < 4)))
  , ("halfhalf",  spine ((List.range n).map (fun i => 2 * i < n)))
  , ("balanced",  balanced n)
  , ("rand1",     spine (pat 1 n))
  , ("rand2",     spine (pat 2 n))
  , ("rand3",     spine (pat 3 n)) ]

/-- Per-shape: build the data ONCE, then run every (store, idx). -/
def shapeKeys (s : CartesianShape) (idxs : List Nat) :
    IO (List String × List String × Nat) := do
  let bits := s.bpCode
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

def report (n : Nat) (idxs : List Nat) : IO Unit := do
  let fam := family n
  let codes := (fam.map fun p => p.2.bpCode).eraseDups
  let sizes := (fam.map fun p => p.2.size).eraseDups
  logLine s!"--- n={n} shapes={fam.length} distinctBpCodes={codes.length} sizes={sizes} idxs={idxs} stores={stores.length}"
  let mut base : Option (List String) := none
  let mut baseName := ""
  let mut mism := 0
  let mut allRegs : List String := []
  for (nm, s) in fam do
    let (ks, regs, ms) <- shapeKeys s idxs
    allRegs := (allRegs ++ regs).eraseDups
    match base with
    | none => base := some ks; baseName := nm
    | some b =>
        let bad := (List.range ks.length).filter (fun i => b[i]! != ks[i]!)
        if bad.length != 0 then
          mism := mism + bad.length
          logLine s!"  *** MISMATCH {baseName} vs {nm}: {bad.length} of {ks.length} positions"
          let i := bad.head!
          logLine s!"      pos={i} A={b[i]!}"
          logLine s!"      pos={i} B={ks[i]!}"
    logLine s!"  shape={nm} keys={ks.length} buildAndRun={ms}ms regimes={regs}"
  logLine s!"=== n={n} TOTAL-MISMATCHES={mism} regimesSeen={allRegs}"

#eval show IO Unit from do
  IO.FS.writeFile logFile "attack3 start\n"
  report 63 [0, 1, 5, 31, 62, 63]
  report 65 [0, 1, 5, 33, 64, 65]
  logLine "attack3 done (part 1)"

end AdvS6C
