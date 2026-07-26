import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Executed size-only test, quantified over ALL shapes of a size (not rows).

For a function f of the shape alone: if f really factors through n, then across
every shape of a fixed size the value must be CONSTANT. So `distinct = 1` is
consistent with size-only and `distinct > 1` REFUTES size-only outright.
This decides the coordinator's LENGTHONLY bucket by execution.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

namespace AtkSO

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def distinctCount (xs : List String) : Nat := xs.eraseDups.length

def probe (nm : String) (f : CartesianShape -> String) : IO Unit := do
  let mut row := s!"  {nm}"
  for sz in [3, 4, 5, 6] do
    let shapes := shapesOfSize sz
    let vals := shapes.map f
    row := row ++ s!" | n={sz}: {distinctCount vals}/{shapes.length}"
  IO.println row

#eval show IO Unit from do
  IO.println "distinct values / number of shapes, per size. >1 REFUTES size-only."
  IO.println ""
  IO.println "-- sanity controls --"
  probe "bpCode.length          (must be 1)" (fun s => toString s.bpCode.length)
  probe "size                   (must be 1)" (fun s => toString s.size)
  probe "bpCode                 (must be >1)" (fun s => toString s.bpCode)
  IO.println ""
  IO.println "-- coordinator's acknowledged CONTENT users --"
  probe "bpExcessAt _ 3                    " (fun s => toString (bpExcessAt s 3))
  probe "builtRelSplitBPCloseRankBlockOvhd " (fun s => toString (builtRelativeSplitBPCloseRankBlockOverhead s))
  probe "builtRelSplitBPCloseRankSuperOvhd " (fun s => toString (builtRelativeSplitBPCloseRankSuperOverhead s))
  IO.println ""
  IO.println "-- coordinator's LENGTHONLY bucket: 'derivable from n' --"
  probe "builtRelSplitBPCloseRankWordSize  " (fun s => toString (builtRelativeSplitBPCloseRankWordSize s))
  probe "localBPWindowBase _ 2 3           " (fun s => toString (localBPWindowBase s 2 3))
  probe "bpBlockMinExcess _ 2 1            " (fun s => toString (bpBlockMinExcess s 2 1))
  probe "bpBlockArgMinPrefixPos _ 2 1      " (fun s => toString (bpBlockArgMinPrefixPos s 2 1))
  probe "bpBlockArgMinPrefixPosFrom _ 1 4 3" (fun s => toString (bpBlockArgMinPrefixPosFrom s 1 4 3))
  probe "canonicalRelRmmInteriorCompOffsets" (fun s => toString (repr (canonicalRelativeRmmInteriorComponentOffsets s)))

end AtkSO
