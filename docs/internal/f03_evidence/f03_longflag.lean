import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Settling the last F03 frontier: is the select long/sparse regime a FREE content
branch, or is it learned by PROBING?

Two independent lines.

LINE 1 (arithmetic, size-only). `superIsLong bits target slot` is
`superLongSpan bits.length < superSpan bits target slot`, and a span can never
exceed the string length, so `superIsLong` is IDENTICALLY FALSE -- for every
content whatsoever -- at any length m with `m <= superLongSpan m`. Since
`superLongSpan m = wordBits m ^ 3 * ell m ~ (log m)^3 log log m`, that covers all
small m. Find the exact crossover: below it the predicate is content-independent
for the trivial reason that it cannot fire, which means any experiment run below
it is VACUOUS on this row.

LINE 2 (structural, and the one that actually decides it). The read store
(RMQ/Core/BPNavigationRAM.lean:847-862) devotes segments 9/10/11 to
`selectData.longFlagRankData`, segment 12 to `selectData.longSuperRelativeTable`,
and segments 13-16 to `selectData.sparseDirectory`. Those segments exist
precisely to STORE the long/sparse decision and its exception data. If the
controller reads them at query time, the regime is a probe reply -- verdict P --
and `superIsLong` occurring in the closure is table CONSTRUCTION, verdict B.
Print the select leaf's own addresses and see which segments it actually touches.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace F03Flag

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

def cliff (K M : Nat) : CartesianShape := .node (leftSpine K) (rightSpine M)

def addrStore (salt : Nat) : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 24).map fun b => ((seg * 131 + idx * 17 + salt) >>> b) % 2 == 1)

def addrsOf (t : List WordRAM.TraceEvent) : List (Nat × Nat) :=
  t.filterMap fun
    | WordRAM.TraceEvent.readWord seg i _ => some (seg, i)
    | _ => none

-- LINE 1: where can superIsLong fire at all?
#eval show IO Unit from do
  IO.println "LINE 1: superLongSpan(m) vs m -- superIsLong is identically false while m <= superLongSpan m"
  let mut firstFireable : Option Nat := none
  for e in List.range 26 do
    let m := 2 ^ e
    let thr := superLongSpan m
    let canFire : Bool := decide (thr < m)
    if canFire && firstFireable.isNone then firstFireable := some m
    IO.println s!"  m=2^{e}={m}  wordBits={wordBits m} ell={ell m} superStride={superStride m} superLongSpan={thr}  canEverFire={canFire}"
  IO.println s!"  FIRST LENGTH AT WHICH superIsLong CAN FIRE: {firstFireable}"
  match firstFireable with
  | some m => IO.println s!"  => in shape terms, n = m/2 = {m / 2} nodes. Below that the predicate is content-independent because a span cannot exceed the string length."
  | none => IO.println "  => never fires within 2^25"

-- LINE 2: which segments does the select leaf actually read?
#eval show IO Unit from do
  IO.println "LINE 2: segments touched by the select-close leaf under a supplied store"
  IO.println "  (store segments: 9/10/11 = longFlagRankData, 12 = longSuperRelativeTable, 13-16 = sparseDirectory)"
  let st := addrStore 5
  for n in [8, 64, 256] do
    for (nm, s) in [("leftSpine", leftSpine n), ("rightSpine", rightSpine n), ("cliff", cliff (3*n/4) (n - 1 - 3*n/4))] do
      let t := concreteBPNativeSelectCloseGlobalWordTraceResultWithStore s st (n / 2)
      let a := addrsOf t.trace
      let segs := (a.map (·.1)).eraseDups
      IO.println s!"  n={n} {nm} (size={s.size}): segments={segs}"
      IO.println s!"      addresses={a}"

-- LINE 2b: the whole-query footprint, for the same question at route level.
#eval show IO Unit from do
  IO.println "LINE 2b: whole-query footprint segments"
  let st := addrStore 5
  for n in [8, 64] do
    for (nm, s) in [("leftSpine", leftSpine n), ("rightSpine", rightSpine n)] do
      let t := concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore s st 0 n
      let a := addrsOf t.trace
      let segs := (a.map (·.1)).eraseDups
      IO.println s!"  n={n} {nm}: segments={segs} events={t.trace.length}"

end F03Flag
