import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL ATTACK on the S verdict for F6 / leaf L1, part 4.

  E8 REAL store: `concreteBPNativeSuccinctRMQGlobalReadStore shapeA` held
     FIXED while the shape argument of the leaf ranges over the whole
     same-size family.  This is the store a genuine query would see.
  E9 EXHAUSTIVE bitvector sweep at lengths 12 and 14 (all 2^12 + 2^14
     bitvectors), grouped by false-count -- extends the prior agent's
     length <= 10 superset sweep.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6F

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def logFile : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advS_f6_attack6_log.txt"

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

def spine : List Bool -> CartesianShape
  | [] => CartesianShape.empty
  | true :: bs => CartesianShape.node CartesianShape.empty (spine bs)
  | false :: bs => CartesianShape.node (spine bs) CartesianShape.empty

def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node (balanced (k / 2)) (balanced (k - k / 2))

def pat (seed n : Nat) : List Bool :=
  (List.range n).map fun i => (seed * 977 + i * 1103 + i * i * 65537) % 7 < 3

def shapes (n : Nat) : List (String × CartesianShape) :=
  [ ("rightComb", spine (List.replicate n true))
  , ("leftComb",  spine (List.replicate n false))
  , ("alt",       spine ((List.range n).map (fun i => i % 2 == 0)))
  , ("balanced",  balanced n)
  , ("rand1",     spine (pat 1 n))
  , ("rand2",     spine (pat 2 n)) ]

/-! ## E8: the REAL store, held fixed, while the shape argument varies -/

def realStoreTest (n : Nat) (idxs : List Nat) : IO Unit := do
  let fam := shapes n
  let anchor := fam.head!
  logLine s!"  [E8] n={n} anchorStore=concreteBPNativeSuccinctRMQGlobalReadStore({anchor.1}) idxs={idxs}"
  let t0 <- IO.monoMsNow
  let store := concreteBPNativeSuccinctRMQGlobalReadStore anchor.2
  let mut base : Option (List String) := none
  let mut mism := 0
  let mut cmps := 0
  for (nm, s) in fam do
    let ks := idxs.map fun idx =>
      key (concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s store idx)
    match base with
    | none =>
        base := some ks
        logLine s!"    anchor {nm}: {ks.head!}"
    | some b =>
        cmps := cmps + ks.length
        let bad := (List.range ks.length).filter (fun i => b[i]! != ks[i]!)
        if bad.length != 0 then
          mism := mism + bad.length
          logLine s!"    *** DIFF {anchor.1} vs {nm}: {bad.length}/{ks.length}"
          let i := bad.head!
          logLine s!"        A={b[i]!}"
          logLine s!"        B={ks[i]!}"
  let t1 <- IO.monoMsNow
  logLine s!"  [E8] n={n} shapes={fam.length} comparisons={cmps} MISMATCHES={mism} [{t1-t0}ms] {if mism == 0 then "OK-NO-DIFFERENCE" else "*** REFUTED ***"}"

#eval show IO Unit from do
  IO.FS.writeFile logFile "attack6 start\n"
  logLine "== E8: real global read store, cross-shape =="
  realStoreTest 8 [0, 1, 4, 7, 8]
  realStoreTest 16 [0, 1, 8, 15, 16]

#eval show IO Unit from do
  realStoreTest 63 [5]

/-! ## E9: exhaustive bitvector sweep at lengths 12 and 14 -/

def smallStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    let v := (salt + segment * 5 + index * 3) % 16
    some ((List.range 4).map fun k => (v / 2 ^ k) % 2 == 1)

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

def sweepStores : List WordRAM.ReadStore :=
  [ smallStore 7, regimeStore 7 true false, regimeStore 7 false true,
    regimeStore 7 false false ]

def allBits : Nat -> List (List Bool)
  | 0 => [[]]
  | Nat.succ n => (allBits n).flatMap fun t => [false :: t, true :: t]

def falses (bits : List Bool) : Nat := (bits.filter (fun b => !b)).length

def bitsKey (bits : List Bool) (idxs : List Nat) : String :=
  let data := sparseExceptionSelectData bits false
  let c := SuccinctClose.bpFringeChunkBits bits.length
  String.intercalate "#"
    (sweepStores.flatMap fun store =>
      idxs.map fun idx =>
        key (data.bpChunkedSelectTraceResultWithStore
          concreteBPNativeSelectCloseTraceSegmentLayout
          concreteBPNativeFringeChunkTraceSegment
          concreteBPNativeSelectChunkTraceSegment store c idx))

def exhaustiveBits (len : Nat) (idxs : List Nat) : IO Unit := do
  let bs := allBits len
  let t0 <- IO.monoMsNow
  let mut worst := 0
  let mut groups := 0
  let mut total := 0
  for k in List.range (len + 1) do
    let group := bs.filter (fun b => falses b == k)
    if group.length != 0 then
      groups := groups + 1
      total := total + group.length
      let ks := (group.map (fun b => bitsKey b idxs)).eraseDups
      if ks.length > worst then worst := ks.length
      if ks.length != 1 then
        logLine s!"    *** len={len} falseCount={k}: {ks.length} DISTINCT outcomes among {group.length} bitvectors ***"
  let t1 <- IO.monoMsNow
  logLine s!"  [E9] length={len} bitvectors={total} groups={groups} maxDistinctOutcomesPerGroup={worst} [{t1-t0}ms] {if worst <= 1 then "OK-NO-DIFFERENCE" else "*** REFUTED ***"}"

#eval show IO Unit from do
  logLine "== E9: exhaustive bitvector superset sweep =="
  exhaustiveBits 12 [0, 1, 5, 6, 7]

#eval show IO Unit from do
  exhaustiveBits 14 [0, 1, 6, 7, 8]

end AdvS6F
