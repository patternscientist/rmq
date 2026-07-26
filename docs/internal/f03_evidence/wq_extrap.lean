import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! Tighten the superIsLong frontier: measure the span-maximising family's
    achieved maxSuperSpan as an exact function of n, then scan for the first n
    where that achieved span would exceed superLongSpan(2n). -/

open RMQ RMQ.Cartesian RMQ.GenericSelect

namespace WQExtrap

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty
def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)
/-- bp = T (TF) F T^(n-2) F^(n-2) : one early close, then a maximal descending
    chain.  Empirically the span-maximising family. -/
def deep (n : Nat) : CartesianShape :=
  if n < 2 then .empty else .node (rightSpine 1) (leftSpine (n - 2))

def maxSuperSpan (s : CartesianShape) (tgt : Bool) : Nat :=
  let bits := s.bpCode
  (List.range (superSlotCount bits tgt)).foldl
    (fun acc i => max acc (superSpan bits tgt i)) 0

def logPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_extrap_log.txt"

#eval show IO Unit from do
  let h <- IO.FS.Handle.mk logPath IO.FS.Mode.write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush; IO.println s
  say "n | superStride(2n) | achieved maxSuperSpan (deep) | span - n | superLongSpan(2n)"
  for n in [64, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072] do
    let s := deep n
    if s.size != n then say s!"  GENBUG n={n} size={s.size}"
    else
      let ms := maxSuperSpan s false
      say s!"n={n} superStride={superStride (2*n)} achieved={ms} achieved-n={ms - n} superLongSpan={superLongSpan (2*n)} fires={decide (superLongSpan (2*n) < ms)}"
  say "-- frontier under the EMPIRICAL law  span = n + superStride(2n)  --"
  let mut firstEmp : Option Nat := none
  for i in List.range 40000 do
    let n := i + 1
    if decide (superLongSpan (2 * n) < n + superStride (2 * n)) then
      if firstEmp.isNone then
        firstEmp := some n
        say s!"EMPIRICAL-LAW frontier: first n with superLongSpan(2n) < n + superStride(2n) is n={n} (superLongSpan={superLongSpan (2*n)}, n+superStride={n + superStride (2*n)})"
  say s!"empirical-law frontier over n=1..40000 = {firstEmp}"
  h.flush

end WQExtrap
