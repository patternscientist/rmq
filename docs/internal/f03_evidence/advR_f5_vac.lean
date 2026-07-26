import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ANTI-VACUITY CONTROL for advR_f5_root.

VALUE_CONST=true is worthless if every output is `none`, and FOOTPRINT_CONST is
worthless if the footprint is a store-insensitive constant.  This file checks:
  (1) outputs are actually `some _` (not a uniformly-failing controller);
  (2) the footprint genuinely REACTS to probe replies (store-adaptive), so the
      instrument can detect an address-stream change at all;
  (3) shapes of the same size really do have different bpCode contents.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal

namespace AdvVac

partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def store1 : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 8).map fun i => ((seg * 7 + idx * 3 + i) % 5 == 0))

def store2 : WordRAM.ReadStore where
  readWord? := fun seg idx =>
    some ((List.range 12).map fun i => ((seg * 13 + idx * 11 + i * i) % 7 < 3))

def store3 : WordRAM.ReadStore where
  readWord? := fun _ _ => some (List.replicate 8 true)

def outValue (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
    s st l r).value

def footprint (s : CartesianShape) (st : WordRAM.ReadStore) (l r : Nat) :=
  concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore s st l r

#eval show IO Unit from do
  for n in [4, 5] do
    let ss := shapesOfSize n
    let vals := ss.map (fun s => outValue s store1 0 n)
    let someCount := (vals.filter (fun v => v.isSome)).length
    IO.println s!"n={n} shapes={ss.length} outputs_some={someCount} sample={vals.take 4}"
    -- store sensitivity on ONE fixed shape: does the address stream react?
    let s0 := ss.headD CartesianShape.empty
    let f1 := footprint s0 store1 0 n
    let f2 := footprint s0 store2 0 n
    let f3 := footprint s0 store3 0 n
    IO.println s!"   STORE_SENSITIVITY fixed shape: len1={f1.length} len2={f2.length} len3={f3.length}"
    IO.println s!"   f1==f2? {f1 == f2}  f1==f3? {f1 == f3}"
    IO.println s!"   v1={outValue s0 store1 0 n} v2={outValue s0 store2 0 n} v3={outValue s0 store3 0 n}"
    -- content divergence control
    IO.println s!"   bpCode[0]={(ss.headD CartesianShape.empty).bpCode}"
    IO.println s!"   bpCode[last]={((ss.getLast?).getD CartesianShape.empty).bpCode}"

end AdvVac
