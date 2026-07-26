import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-! Cheap continuation of the segment-20 liveness scan: one shape, one endpoint
pair per size, written incrementally so partial progress survives a timeout. -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace AdvF5Seg20B

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (balanced (n / 2)) (balanced (n - n / 2))

def fp (sh : CartesianShape) (l r : Nat) : List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore sh
    (BPNavigation.concreteBPCloseNavigationGlobalReadStore sh) l r

def segCount (f : List (Nat × Nat)) (s : Nat) : Nat :=
  (f.filter (fun p => p.1 == s)).length

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_seg20b_out.txt"

def row (n : Nat) : String := Id.run do
  let sh := balanced n
  let f := fp sh 0 n
  let L := RelativeRmm.canonicalLayout sh
  let segsUsed := (f.map Prod.fst).eraseDups.mergeSort (· <= ·)
  let msg :=
    s!"n={n} bpLen={sh.bpCode.length} traceLen={f.length} " ++
    s!"seg20={segCount f 20} seg23={segCount f 23} seg24={segCount f 24} " ++
    s!"seg25={segCount f 25} segsUsed={segsUsed} " ++
    s!"| blockSize={L.blockSize} blockCount={L.blockCount} macroSize={L.macroSize}"
  return msg

run_cmd do
  let mut acc : Array String := #[]
  for n in [6, 8, 10, 12, 14, 16, 20, 24, 32] do
    let l := AdvF5Seg20B.row n
    acc := acc.push l
    IO.FS.writeFile AdvF5Seg20B.outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5Seg20B
