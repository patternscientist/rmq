import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5 ATTACK (size-only lens), TOP LEVEL.

The prior F5 defence tested `canonicalRelativeRmmInteriorRangeMinComputation`
and `canonicalRelativeRmmMachineSummaryComputation` with `startBlock`/`count`/
`block` SUPPLIED BY THE TEST HARNESS.  That cannot detect a leak in which the
shape decides *which* block/count to ask for.  Here we drive the real public
controller end to end:

  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
  concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore

over ALL Cartesian shapes of a given size, ALL endpoint pairs, with a FIXED
SHAPE-FREE store.  Under the claimed closure the (n, left, right) triple plus
the store determines the whole transcript; any divergence between two same-size
shapes is a direct witness that semantic shape content is a live input.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctClose

namespace AdvF5Top

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
    (List.range (n + 1)).flatMap fun l =>
      (shapesOfSize l).flatMap fun L =>
        (shapesOfSize (n - l)).map fun R => CartesianShape.node L R

/-- Constant shape-free store. -/
def constStore : WordRAM.ReadStore where
  readWord? := fun _ _ => some ((List.range 8).map fun i => i % 2 == 0)

/-- Address-dependent but shape-free store: replies vary with (segment,index),
    exercising far more content branches than a constant word. -/
def prngStore : WordRAM.ReadStore where
  readWord? := fun s i =>
    some ((List.range 12).map fun k => (7 * s + 13 * i + 5 * k + 3) % 3 == 0)

def fp (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    List (Nat × Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore sh st l r

def outv (st : WordRAM.ReadStore) (sh : CartesianShape) (l r : Nat) :
    Option Nat :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    sh st l r).value

structure Rep where
  fpDiff : Nat := 0
  valDiff : Nat := 0
  groups : Nat := 0
  fpLens : List Nat := []
  witness : String := ""
deriving Repr

/-- For each (l,r) compare every shape against the FIRST shape of that size. -/
def scan (st : WordRAM.ReadStore) (n : Nat) : Rep := Id.run do
  let ss := shapesOfSize n
  let head := ss.headD .empty
  let mut rep : Rep := {}
  let mut lens : List Nat := []
  for l in List.range (n + 1) do
    for r in List.range (n + 1) do
      if l <= r then
        let f0 := fp st head l r
        let v0 := outv st head l r
        lens := lens ++ [f0.length]
        rep := { rep with groups := rep.groups + 1 }
        for sh in ss do
          let f := fp st sh l r
          let v := outv st sh l r
          if f != f0 then
            if rep.witness == "" then
              rep := { rep with witness :=
                s!"FP l={l} r={r} A={head.bpCode} B={sh.bpCode} fpA={f0} fpB={f}" }
            rep := { rep with fpDiff := rep.fpDiff + 1 }
          if v != v0 then
            if rep.witness == "" then
              rep := { rep with witness :=
                s!"VAL l={l} r={r} A={head.bpCode} B={sh.bpCode} vA={v0} vB={v}" }
            rep := { rep with valDiff := rep.valDiff + 1 }
  return { rep with fpLens := lens.eraseDups }

def outPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/advF5_top_out.txt"

run_cmd do
  let mut acc : Array String := #[]
  for n in [2, 3, 4, 5, 6] do
    let ss := AdvF5Top.shapesOfSize n
    let rc := AdvF5Top.scan AdvF5Top.constStore n
    let rp := AdvF5Top.scan AdvF5Top.prngStore n
    let l := s!"n={n} shapes={ss.length} endpointGroups={rc.groups} " ++
      s!"CONST[fpDiff={rc.fpDiff} valDiff={rc.valDiff} fpLens={rc.fpLens}] " ++
      s!"PRNG[fpDiff={rp.fpDiff} valDiff={rp.valDiff} fpLens={rp.fpLens}] " ++
      s!"witnessConst=<{rc.witness}> witnessPrng=<{rp.witness}>"
    acc := acc.push l
    IO.FS.writeFile AdvF5Top.outPath (String.intercalate "\n\n" acc.toList)
    Lean.logInfo m!"{l}"

end AdvF5Top
