import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL E2: REAL Cartesian shapes past the degeneracy boundary.

From E0: a shape of size n has bpCode length 2n and occurrenceCount false = n,
so superSlotCount = ceil(n / wordBits(2n)^2).  That is 1 for every n <= 5 (in
fact for every n <= 24), which is the ONLY regime the S dossier tested.
At n = 50 (len 100, superStride 49) and n = 65 (len 130, superStride 64) the
super level finally has 2 slots.  Extremal shapes are compared there.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace Adv6B

def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

def zeroW : List Bool := List.replicate 16 false
def noiseW (salt seg idx : Nat) : List Bool :=
  (List.range 16).map fun k =>
    (salt + seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index := some (noiseW salt segment index)

def craft (salt : Nat) (superMark localMark : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then
      some (if superMark then noiseW salt 3 index else zeroW)
    else if segment == 7 then
      some (if localMark then noiseW salt 7 index else zeroW)
    else
      some (noiseW salt segment index)

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

/-! ### extremal shapes of a given size -/

def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node CartesianShape.empty (rightSpine k)

def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node (leftSpine k) CartesianShape.empty

def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k => CartesianShape.node (balanced (k / 2)) (balanced (k - k / 2))

def zig : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k =>
      if k % 2 == 0 then CartesianShape.node CartesianShape.empty (zig k)
      else CartesianShape.node (zig k) CartesianShape.empty

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

/-- pseudo-random shape: split the remaining nodes by a hash. -/
partial def rnd (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ k =>
      let cut := (seed * 2654435761 + k * 40503 + k * k * 97 + 11) % (k + 1)
      CartesianShape.node (rnd (seed + 7) cut) (rnd (seed + 13) (k - cut))

def family (n : Nat) : List CartesianShape :=
  [rightSpine n, leftSpine n, balanced n, zig n,
   rnd 1 n, rnd 2 n, rnd 5 n, rnd 9 n]

def check (n : Nat) (store : WordRAM.ReadStore) (label : String)
    (idxs : List Nat) : IO Unit := do
  let fam := family n
  let sizes := (fam.map CartesianShape.size).eraseDups
  let codes := (fam.map (fun s => s.bpCode)).eraseDups
  let sc := (fam.map (fun s =>
    GenericSelect.superSlotCount s.bpCode false)).eraseDups
  let ents := (fam.map (fun s =>
    String.intercalate ";" ((GenericSelect.superEntries s.bpCode false).map
      (fun e => s!"({e.baseOccurrence},{e.baseWordIndex},{e.rankBefore},{e.firstOffset})")))).eraseDups
  let mut worst := 0
  let mut witness := ""
  for idx in idxs do
    let ks := (fam.map (fun s => key (leaf s store idx))).eraseDups
    if ks.length > worst then
      worst := ks.length
      witness := s!"idx={idx} -> {ks.length} distinct"
  IO.println s!"  {label} n={n} sizes={sizes} distinctBPcodes={codes.length} superSlotCount={sc} distinctSuperEntryTables={ents.length} MAXDISTINCTOUTCOMES={worst} {witness}"

#eval show IO Unit from do
  IO.println "== E2. real shapes, non-degenerate super level =="
  for n in [50, 65] do
    check n (noiseStore 11) "noise(11)" [0, 1, 48, 63, 64]
    check n (craft 11 true true) "LONG     " [0, 1, 48, 63, 64]
    check n (craft 11 false true) "SPARSE   " [0, 1, 48, 63, 64]
    check n (craft 11 false false) "DENSE    " [0, 1, 48, 63, 64]

#eval show IO Unit from do
  IO.println "== E2b. degenerate-regime control: same test at n=5 and n=24 =="
  for n in [5, 24] do
    check n (noiseStore 11) "noise(11)" [0, 1, 4]

end Adv6B
