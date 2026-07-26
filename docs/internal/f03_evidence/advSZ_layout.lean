import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack, stage 3': the STORE LAYOUT LENGTHS, computed directly.

For the packed target these payload lengths ARE the segment offsets inside
`header ++ buildPayload ++ padding`.  If any of them differs between two
shapes of the same size, the packing offsets are content-dependent and the
size-only story fails at the layout level.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.BPNavigation

namespace AdvSZLayout

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def shapesN : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | Nat.succ n =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesN k).flatMap fun l =>
          (shapesN (n - k)).map fun r => CartesianShape.node l r

partial def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

partial def randShape (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let s := (seed * 1103515245 + 12345) % 2147483648
      let k := s % (n + 1)
      CartesianShape.node (randShape (s / 7 + 1) k) (randShape (s / 11 + 3) (n - k))

def familyOf (n : Nat) : List CartesianShape :=
  [leftSpine n, rightSpine n, balanced n, randShape 1 n, randShape 7 n,
   randShape 99 n]

def lengths (s : CartesianShape) : List (String × Nat) :=
  [ ("summaryTable.payload",
      (concreteBPRelativeMinMaxArgSummaryTable_canonical s).payload.length)
  , ("interiorLocalTable.payload",
      (concreteBPRelativeRmmInteriorLocalTable s).payload.length)
  , ("interiorGlobalTable.payload",
      (concreteBPRelativeRmmInteriorGlobalTable s).payload.length)
  , ("interiorDirectoryPayloadLength",
      concreteBPRelativeRmmInteriorDirectoryPayloadLength s)
  , ("componentStore.words",
      (canonicalRelativeRmmInteriorComponentStore s).store.words.size)
  , ("fringeChunkTable.words",
      (bpFringeChunkTable (bpFringeChunkBits s.bpCode.length)).store.words.size)
  , ("chunkSelectTable.words",
      (bpChunkSelectTable (bpFringeChunkBits s.bpCode.length) false).store.words.size)
  , ("rankRegisterStore.seg0",
      (((builtRelativeSplitBPCloseRankData s).rankRegisterWordRAMStore false).readWord? 0 0).isSome.toNat)
  , ("F4 superOverhead", builtRelativeSplitBPCloseRankSuperOverhead s)
  , ("F3 blockOverhead", builtRelativeSplitBPCloseRankBlockOverhead s)
  ]

/-- The select directory's segment geometry: `payload.length = entries * width`
    for every FixedWidthNatTable that backs one of the 26 store segments. -/
def selectLengths (s : CartesianShape) : List (String × Nat) :=
  let dir := concreteBPCloseNavigationRelativeSplitAccessFamily.directory s
  let sd := dir.selectData
  [ ("sel.superEntries.count", sd.superEntries.length)
  , ("sel.superFieldWidth", sd.superFieldWidth)
  , ("sel.localEntries.count", sd.localEntries.length)
  , ("sel.localFieldWidth", sd.localFieldWidth)
  , ("sel.longSuperRelativeEntries.count", sd.longSuperRelativeEntries.length)
  , ("sel.longSuperRelativeWidth", sd.longSuperRelativeWidth)
  , ("sel.sparse.relativeEntries.count", sd.sparseDirectory.relativeEntries.length)
  , ("sel.sparse.relativeWidth", sd.sparseDirectory.relativeWidth)
  , ("seg1 superBaseOccurrence.payload", sd.superTable.baseOccurrenceTable.payload.length)
  , ("seg2 superBaseWordIndex.payload", sd.superTable.baseWordIndexTable.payload.length)
  , ("seg3 superRankBefore.payload", sd.superTable.rankBeforeTable.payload.length)
  , ("seg4 superFirstOffset.payload", sd.superTable.firstOffsetTable.payload.length)
  , ("seg5 localBaseOccurrence.payload", sd.localTable.baseOccurrenceTable.payload.length)
  , ("seg6 localBaseWordIndex.payload", sd.localTable.baseWordIndexTable.payload.length)
  , ("seg7 localRankBefore.payload", sd.localTable.rankBeforeTable.payload.length)
  , ("seg8 localFirstOffset.payload", sd.localTable.firstOffsetTable.payload.length)
  , ("seg12 longSuperRelative.payload", sd.longSuperRelativeTable.payload.length)
  , ("seg16 sparseRelative.payload", sd.sparseDirectory.relativeTable.payload.length)
  ]

def diffReport (label : String) (n : Nat) (ss : List CartesianShape)
    (f : CartesianShape -> List (String × Nat)) : IO Unit := do
  match ss with
  | [] => pure ()
  | s0 :: _ =>
    let rows := ss.map f
    let r0 := f s0
    let mut diffs : List String := []
    for k in r0.map (fun q => q.1) do
      let vals := rows.map (fun r => (r.lookup k).getD 0)
      let dv := vals.foldl (fun acc v => if acc.contains v then acc else v :: acc) []
      if dv.length > 1 then diffs := s!"{k}::{dv.reverse}" :: diffs
    IO.println s!"{label} n={n} shapes={ss.length} DIFFS={diffs.reverse}  baseline={r0}"

#eval show IO Unit from do
  IO.println "--- EXHAUSTIVE over ALL shapes of the size: SELECT-DIRECTORY segment geometry ---"
  for n in [1,2,3,4,5,6] do
    diffReport "SEL-EXH" n (shapesN n) selectLengths

#eval show IO Unit from do
  IO.println "--- family shapes: SELECT-DIRECTORY segment geometry, larger n ---"
  for n in [8,16,32,64,128] do
    diffReport "SEL-FAM" n (familyOf n) selectLengths

#eval show IO Unit from do
  IO.println "--- EXHAUSTIVE over ALL shapes of the size, other layout lengths ---"
  for n in [1,2,3,4,5,6] do
    diffReport "LEN-EXH" n (shapesN n) lengths

#eval show IO Unit from do
  IO.println "--- family shapes, other layout lengths, larger n ---"
  for n in [16,32,64,128,256] do
    diffReport "LEN-FAM" n (familyOf n) lengths

end AdvSZLayout
