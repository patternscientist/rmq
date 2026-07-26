import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL ATTACK on the S verdict for F6 / leaf L1
(`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore`).

Prior evidence lived at shape size n <= 5.  advS_f6_diag.lean shows that in
that entire range superSlotCount = 1, localStride = 1 and
longFlagRankWordSize = 1: every slot address is 0.  This file re-runs the
same-size differential at n where superSlotCount >= 2.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvS6B

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_attack2_log.txt"

def logLine (s : String) : IO Unit := do
  let h <- IO.FS.Handle.mk logFile IO.FS.Mode.append
  h.putStrLn s
  h.flush

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
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

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 8).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

def boundedStore (salt lim : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    if index < lim then
      some ((List.range 8).map fun k =>
        (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)
    else none

/-- Small-valued store: every word is a 4-bit little-endian encoding of a
small number that varies with (segment, index).  Keeps addresses small so
the trace is short, while still making every address visible. -/
def smallStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    let v := (salt + segment * 5 + index * 3) % 16
    some ((List.range 4).map fun k => (v / 2 ^ k) % 2 == 1)

/-- Regime driver: control `super.rankBefore` (segment 3) and
`loc.rankBefore` (segment 7) while everything else stays small. -/
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
  ] ++ ((List.range 6).map fun s => (s!"rand{s}", spine (pat (s + 1) n)))

def report (n : Nat) (label : String) (store : WordRAM.ReadStore)
    (idxs : List Nat) : IO Unit := do
  let t0 <- IO.monoMsNow
  let fam := family n
  let codes := (fam.map fun p => p.2.bpCode).eraseDups
  let sizes := (fam.map fun p => p.2.size).eraseDups
  let mut km := 0
  let mut vm := 0
  let mut regs : List String := []
  let mut wit := ""
  let mut cmps := 0
  for idx in idxs do
    let base := L1raw (fam.head!.2).bpCode store idx
    let bk := key base
    for (nm, s) in fam do
      let r := L1raw s.bpCode store idx
      cmps := cmps + 1
      regs := (regs ++ [regime r]).eraseDups
      if key r != bk then
        km := km + 1
        if wit == "" then
          wit := s!"idx={idx} {fam.head!.1} vs {nm} | A={bk} | B={key r}"
      if r.value != base.value then vm := vm + 1
  let t1 <- IO.monoMsNow
  logLine s!"n={n} store={label} shapes={fam.length} distinctBpCodes={codes.length} sizes={sizes} comparisons={cmps} KEY-MISMATCH={km} VALUE-MISMATCH={vm} regimes={regs} [{t1-t0}ms]"
  if wit != "" then logLine s!"  WITNESS: {wit}"

#eval show IO Unit from do
  IO.FS.writeFile logFile "attack2 start\n"
  for n in [63, 65, 80, 100, 128, 200] do
    let idxs := List.range 10 ++ [n / 2, n - 2, n - 1, n, n + 1]
    report n "small7" (smallStore 7) idxs
    report n "noise11" (noiseStore 11) idxs
    report n "bounded(lim=3)" (boundedStore 5 3) idxs
    report n "bounded(lim=1)" (boundedStore 5 1) idxs
    report n "LONG" (regimeStore 7 true false) idxs
    report n "SPARSE" (regimeStore 7 false true) idxs
    report n "DENSE" (regimeStore 7 false false) idxs
  logLine "attack2 done"

end AdvS6B
