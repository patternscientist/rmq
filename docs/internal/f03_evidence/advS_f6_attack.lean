import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL ATTACK on the S verdict for
`concreteBPNativeSelectCloseGlobalWordTraceResultWithStore` (F6 / leaf L1).

The prior agent's executed evidence lives entirely at shape size n <= 5,
i.e. bpCode length <= 10.  My parameter diagnostic (advS_f6_diag.lean)
shows that in that whole range

    superSlotCount = ceilDiv n (superStride (2n)) = 1
    localStride    = 1
    longFlagRankWordSize = 1

so the super-slot addressing, the long-flag rank word addressing, and the
local-slot division are ALL degenerate.  Everything is address 0.  If any
content channel opened only once there is more than one super slot, or once
the flag-rank word index exceeds 0, the prior sweeps could not have seen it.

This file re-runs the same-size differential at n = 63, 65, 80, 100, 128,
200 (superSlotCount = 2 or 3, longFlagRankWordSize = 2), against several
adversarial stores, and over a wide idx range.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvS6A

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

/-- Definitional bridge (kernel-checked `rfl`): `L1raw ∘ bpCode` IS the leaf. -/
theorem L1raw_eq (shape : CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    L1raw shape.bpCode store idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape store idx := rfl

/-! ## Stores -/

/-- Total store: every (segment, address) answers with a 16-bit word that
depends on both, so any address change is visible in the trace. -/
def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    some ((List.range 16).map fun k =>
      (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

/-- Partial store: answers `none` past `lim` on every segment.  This makes the
`none` branches (and the whole NONE regime) reachable, and makes the trace
sensitive to whether an address crosses `lim`. -/
def boundedStore (salt lim : Nat) : WordRAM.ReadStore where
  readWord? segment index :=
    if index < lim then
      some ((List.range 16).map fun k =>
        (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)
    else none

/-- Regime driver: force `super.rankBefore`/`loc.rankBefore` to chosen values
by writing segment 3 / segment 7, keep everything else noisy. -/
def regimeStore (salt : Nat) (superMark localMark : Bool) :
    WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then
      some (if superMark then [true, false, false, false] else [false, false, false, false])
    else if segment == 7 then
      some (if localMark then [true, false, false, false] else [false, false, false, false])
    else
      some ((List.range 16).map fun k =>
        (salt + segment * 7919 + index * 104729 + k * 1299709) % 3 == 0)

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

/-! ## Shape families of a FIXED size -/

/-- 2^n distinct shapes of size `n`: a spine where each step chooses whether
the recursive subtree hangs left or right. -/
def spine : List Bool -> CartesianShape
  | [] => CartesianShape.empty
  | true :: bs => CartesianShape.node CartesianShape.empty (spine bs)
  | false :: bs => CartesianShape.node (spine bs) CartesianShape.empty

/-- Balanced-ish shape of size n. -/
def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node (balanced (k / 2)) (balanced (k - k / 2))

/-- Deterministic pseudo-random pattern of length n. -/
def pat (seed n : Nat) : List Bool :=
  (List.range n).map fun i => (seed * 6364136223846793005 + i * 1442695040888963407 + i * i * 2654435761) % 7 < 3

/-- A family of size-`n` shapes: combs, alternating, block patterns, balanced,
and several pseudo-random spines. -/
def family (n : Nat) : List (String × CartesianShape) :=
  [ ("rightComb", spine (List.replicate n true))
  , ("leftComb",  spine (List.replicate n false))
  , ("alt",       spine ((List.range n).map (fun i => i % 2 == 0)))
  , ("blocks",    spine ((List.range n).map (fun i => i % 8 < 4)))
  , ("halfhalf",  spine ((List.range n).map (fun i => 2 * i < n)))
  , ("balanced",  balanced n)
  ] ++ ((List.range 6).map fun s => (s!"rand{s}", spine (pat (s + 1) n)))

/-! ## The differential -/

structure Diff where
  keyMismatch : Nat
  valMismatch : Nat
  regimes : List String
  witness : String
deriving Inhabited

def differential (n : Nat) (store : WordRAM.ReadStore) (idxs : List Nat) : Diff := Id.run do
  let fam := family n
  let mut km := 0
  let mut vm := 0
  let mut regs : List String := []
  let mut wit := ""
  for idx in idxs do
    let base := L1raw (fam.head!.2).bpCode store idx
    let bk := key base
    for (nm, s) in fam do
      let r := L1raw s.bpCode store idx
      regs := (regs ++ [regime r]).eraseDups
      if key r != bk then
        km := km + 1
        if wit == "" then
          wit := s!"idx={idx} {fam.head!.1} vs {nm}\n    A={bk}\n    B={key r}"
      if r.value != base.value then
        vm := vm + 1
  pure { keyMismatch := km, valMismatch := vm, regimes := regs, witness := wit }

def report (n : Nat) (label : String) (store : WordRAM.ReadStore)
    (idxs : List Nat) : IO Unit := do
  let fam := family n
  -- sanity: the family really does have distinct bpCodes
  let codes := (fam.map fun p => p.2.bpCode).eraseDups
  let sizes := (fam.map fun p => p.2.size).eraseDups
  let d := differential n store idxs
  IO.println s!"n={n} store={label} shapes={fam.length} distinctBpCodes={codes.length} distinctSizes={sizes} KEY-MISMATCHES={d.keyMismatch} VALUE-MISMATCHES={d.valMismatch} regimes={d.regimes}"
  if d.witness != "" then
    IO.println s!"  WITNESS: {d.witness}"

#eval show IO Unit from do
  IO.println "=== A. same-size shape differential at NONDEGENERATE sizes ==="
  for n in [63, 65, 80, 100] do
    report n "noise11" (noiseStore 11) (List.range 12 ++ [n - 1, n, n + 1, 2 * n])
    report n "bounded(lim=3)" (boundedStore 5 3) (List.range 12 ++ [n - 1, n, n + 1])
    report n "bounded(lim=1)" (boundedStore 5 1) (List.range 12 ++ [n - 1, n, n + 1])
    report n "LONG" (regimeStore 7 true false) (List.range 12 ++ [n - 1, n, n + 1])
    report n "SPARSE" (regimeStore 7 false true) (List.range 12 ++ [n - 1, n, n + 1])
    report n "DENSE" (regimeStore 7 false false) (List.range 12 ++ [n - 1, n, n + 1])

end AdvS6A
