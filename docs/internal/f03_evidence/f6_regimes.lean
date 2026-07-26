import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
F6 / L1 regime coverage.

The select route branches twice
(`ChargedRankSelectLeafTrace.lean:1176` and `:1201`), both on
`relativeSplitSelectEntryIsMarked entry` = `entry.rankBefore != 0`, where
`entry` is decoded from four table reads:
  super entry  -> segments 1,2,3,4  (rankBefore is segment 3)
  local entry  -> segments 5,6,7,8  (rankBefore is segment 7)

So the regime bit lives entirely in the reply to a probe at segment 3
(long/short) and segment 7 (sparse/dense).  Here we DRIVE those two words
directly and check that (a) the regime really does flip with the probe reply
alone, and (b) inside each forced regime the leaf is still identical across
every shape of the given size.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace F6Reg

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def zeroW : List Bool := List.replicate 16 false
def noiseW (seg idx : Nat) : List Bool :=
  (List.range 16).map fun k => (seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

/-- Drive the two regime bits directly: segment 3 = super `rankBefore`,
segment 7 = local `rankBefore`. Everything else is shape-free noise. -/
def craft (superMark localMark : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then
      some (if superMark then noiseW 3 index else zeroW)
    else if segment == 7 then
      some (if localMark then noiseW 7 index else zeroW)
    else
      some (noiseW segment index)

/-- A store whose super entry table is absent, forcing the `none` exit. -/
def missingSuper : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 1 then none else some (noiseW segment index)

def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

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

def check (label : String) (store : WordRAM.ReadStore) (n : Nat)
    (idxs : List Nat) : IO Unit := do
  let shapes := shapesOfSize n
  let mut mism := 0
  let mut regs : List String := []
  for idx in idxs do
    let rs := shapes.map (fun s => leaf s store idx)
    let ks := rs.map key
    let k0 := ks.headD ""
    for k in ks do
      if k != k0 then mism := mism + 1
    regs := (regs ++ rs.map regime).eraseDups
  IO.println s!"  {label} n={n} shapes={shapes.length} idxs={idxs.length} regimes={regs} SHAPE-MISMATCHES={mism}"

#eval show IO Unit from do
  IO.println "== forced regimes, shape-independence inside each =="
  for n in [3, 4, 5] do
    check "craft(super=1,local=*) " (craft true true) n (List.range 3)
    check "craft(super=0,local=1)  " (craft false true) n (List.range 3)
    check "craft(super=0,local=0)  " (craft false false) n (List.range 3)
    check "missingSuper            " missingSuper n (List.range 3)

-- Show the regime really flips with the PROBE REPLY alone, shape fixed.
#eval show IO Unit from do
  let s := (shapesOfSize 4).headD CartesianShape.empty
  IO.println "== same shape, same idx, regime driven purely by probe replies =="
  for (lbl, st) in [("super.rankBefore != 0", craft true true),
                    ("super=0, local.rankBefore != 0", craft false true),
                    ("super=0, local=0", craft false false),
                    ("super entry absent", missingSuper)] do
    let r := leaf s st 1
    IO.println s!"  {lbl}: regime={regime r} value={r.value} segs={segsOf r}"

end F6Reg
