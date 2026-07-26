import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
WHERE DOES THE CONTROLLER ACTUALLY READ THE bpExcessAt REGION?

Segment 20 of the global read store is
`SuccinctClose.canonicalRelativeRmmInteriorComponentStore shape`
(RMQ/Core/BPNavigationRAM.lean:869-871) -- the flat region whose CONTENTS are
produced by `bpExcessAt`.

If the top-level controller never probes segment 20 at the sizes used in the F5
defence, then every top-level cross-shape determinism run at those sizes is
VACUOUS with respect to F5.  This scan finds the sizes where segment 20 is
genuinely probed.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace AdvF5Seg20

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (balanced (n / 2)) (balanced (n - n / 2))

def leftComb : Nat -> CartesianShape
  | 0 => .empty
  | n + 1 => .node (leftComb n) .empty

def realStore (s : CartesianShape) : WordRAM.ReadStore :=
  BPNavigation.concreteBPCloseNavigationGlobalReadStore s

def fp (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore sh st l r

def segCount (f : List (Nat × Nat)) (s : Nat) : Nat :=
  (f.filter (fun p => p.1 == s)).length

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_seg20_out.txt"

def row (n : Nat) : String := Id.run do
  let sh := balanced n
  let st := realStore sh
  let pairs := [(0, n), (n / 4, 3 * n / 4), (1, n - 1), (n / 2, n / 2 + 1)]
  let fps := pairs.map fun p => fp st sh p.1 p.2
  let s20 := fps.map fun f => segCount f 20
  let s23 := fps.map fun f => segCount f 23
  let s24 := fps.map fun f => segCount f 24
  let s25 := fps.map fun f => segCount f 25
  let lens := fps.map List.length
  let L := RelativeRmm.canonicalLayout sh
  let msg :=
    s!"n={n} bpLen={sh.bpCode.length} traceLens={lens} " ++
    s!"seg20={s20} seg23={s23} seg24={s24} seg25={s25} " ++
    s!"| layout blockSize={L.blockSize} bps={L.blocksPerSuper} blockCount={L.blockCount} " ++
    s!"macroSize={L.macroSize} macroSampleCount={L.macroSampleCount} " ++
    s!"summaryActive={decide (canonicalBPRelativeMinMaxArgSummaryTableActive sh)}"
  return msg

run_cmd do
  let mut acc : Array String := #[]
  for n in [4, 8, 12, 16, 24, 32, 48, 64, 96, 128] do
    let l := AdvF5Seg20.row n
    acc := acc.push l
    IO.FS.writeFile AdvF5Seg20.outPath (String.intercalate "\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5Seg20
