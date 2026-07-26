import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
COLLAPSE OF THE THREE CONTENT-DEPENDENT BRANCHES.

wq_branches.lean proves (by machine enumeration over the 917-constant controller
closure) that exactly THREE Bool-valued constants in the controller can depend
on tree contents:

    superIsLong, localIsSparseException, compactLocalEntryIsLive

Their definitions (RMQ/Core/GenericSelect/Slots.lean:103,859 and
RMQ/Core/GenericSelect/Entries.lean:47) are

    superIsLong bits t s              = superLongSpan bits.length < superSpan bits t s
    localIsSparseException bits t g   = !superIsLong bits t (localSuperSlot ..) &&
                                          wordBits bits.length < shortSuperLocalSpan bits t g
    compactLocalEntryIsLive bits t g  = !superIsLong bits t (localSuperSlot ..) &&
                                          localBaseOccurrence bits.length g < occurrenceCount bits t

so both of the latter are `!superIsLong && <second conjunct>`.  This file checks
by EXECUTION that each second conjunct is SIZE-ONLY on real Cartesian bpCodes:

  (a) `occurrenceCount shape.bpCode false = shape.size` for every shape
      (bpCode emits exactly one close per node) -- so
      compactLocalEntryIsLive's second conjunct is a function of n alone, and
      the LIVE SLOT SET, not merely its cardinality, is shape-invariant;
  (b) `shortSuperLocalSpan` never exceeds `wordBits` -- so
      localIsSparseException's second conjunct is identically false.

Together: all three collapse to `superIsLong`.
-/

open RMQ RMQ.Cartesian RMQ.GenericSelect

namespace WQCollapse

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
def zigzag : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => if n % 2 == 0 then .node (zigzag n) .empty else .node .empty (zigzag n)
def cliff (n k : Nat) : CartesianShape :=
  if n == 0 then .empty
  else .node (leftSpine (min k (n-1))) (rightSpine (n - 1 - min k (n-1)))
def deep (n : Nat) : CartesianShape :=
  if n < 2 then .empty else .node (rightSpine 1) (leftSpine (n - 2))
partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      .node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def fams (n : Nat) : List (String × CartesianShape) :=
  [ ("leftSpine", leftSpine n), ("rightSpine", rightSpine n), ("balanced", balanced n)
  , ("zigzag", zigzag n), ("cliff/2", cliff n (n/2)), ("deep", deep n)
  , ("pseudo1", pseudo 1 n), ("pseudo29", pseudo 29 n) ]

def logPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_collapse_log.txt"

#eval show IO Unit from do
  let h <- IO.FS.Handle.mk logPath IO.FS.Mode.write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush; IO.println s
  say "=== collapse of the three content-dependent branches ==="
  let mut shapesTested := 0
  let mut occBad := 0
  let mut liveSetBad := 0
  let mut excBad := 0
  let mut longBad := 0
  let mut spanBad := 0
  for n in [1,2,3,5,8,13,16,32,64,100,128,256,384,512,777,1024] do
    let fs := (fams n).filter (fun p => p.2.size == n)
    let base := fs.head!.2
    let baseLive :=
      (List.range (localSlotCount base.bpCode false)).filter
        (fun i => compactLocalEntryIsLive base.bpCode false i)
    for (nm, s) in fs do
      shapesTested := shapesTested + 1
      let bits := s.bpCode
      -- (a) occurrenceCount of closes equals the node count
      if occurrenceCount bits false != n then
        occBad := occBad + 1
        say s!"  !! occurrenceCount(false) != n at n={n} {nm}: {occurrenceCount bits false}"
      -- (a') the LIVE SLOT SET itself is shape-invariant
      let live := (List.range (localSlotCount bits false)).filter
        (fun i => compactLocalEntryIsLive bits false i)
      if live != baseLive then
        liveSetBad := liveSetBad + 1
        say s!"  !! compactLocalEntryIsLive SLOT SET differs at n={n} {nm}"
      -- (b) sparse-exception second conjunct: shortSuperLocalSpan <= wordBits
      let w := wordBits bits.length
      let bad := (List.range (localSlotCount bits false)).filter
        (fun i => decide (w < shortSuperLocalSpan bits false i))
      if !bad.isEmpty then
        spanBad := spanBad + 1
        say s!"  !! shortSuperLocalSpan > wordBits at n={n} {nm}: {bad.length} slots"
      if (List.range (localSlotCount bits false)).any (fun i => localIsSparseException bits false i) then
        excBad := excBad + 1
        say s!"  !! localIsSparseException FIRES at n={n} {nm}"
      if (List.range (superSlotCount bits false)).any (fun i => superIsLong bits false i) then
        longBad := longBad + 1
        say s!"  !! superIsLong FIRES at n={n} {nm}"
    say s!"  n={n}: {fs.length} shapes, liveSlots={baseLive.length}, localSlotCount={localSlotCount base.bpCode false}, superSlotCount={superSlotCount base.bpCode false}"
  say s!"TOTAL shapes tested={shapesTested}"
  say s!"  occurrenceCount(false) != size            : {occBad}"
  say s!"  compactLocalEntryIsLive slot set differs  : {liveSetBad}"
  say s!"  shortSuperLocalSpan > wordBits            : {spanBad}"
  say s!"  localIsSparseException fired              : {excBad}"
  say s!"  superIsLong fired                         : {longBad}"
  h.flush

end WQCollapse
