import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL attack, stage 5: try to MAKE a same-size counterexample.

The select directory has two sparse-exception layers (store segments 12 and 16)
whose sizes are `entries.length * width`.  In every run so far both entry lists
were EMPTY, which is exactly what would hide a content-dependent segment
length.  The left spine has bpCode `true^n ++ false^n` (falses maximally
clustered -- the whole first half is false-free, the best chance of a "long"
superblock) and the right spine has bpCode `(true false)^n` (falses maximally
spread).  If any content-dependent segment geometry exists, these two shapes of
equal size are where it shows up.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.BPNavigation

namespace AdvSZSparse2

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

/-- half spine on the left, half balanced on the right: a lopsided false-run -/
partial def lopsided (n : Nat) : CartesianShape :=
  match n with
  | 0 => CartesianShape.empty
  | Nat.succ m => CartesianShape.node (leftSpine (m / 2)) (balanced (m - m / 2))

def selGeom (s : CartesianShape) : List (String × Nat) :=
  let dir := concreteBPCloseNavigationRelativeSplitAccessFamily.directory s
  let sd := dir.selectData
  [ ("superEntries", sd.superEntries.length)
  , ("superFieldWidth", sd.superFieldWidth)
  , ("localEntries", sd.localEntries.length)
  , ("localFieldWidth", sd.localFieldWidth)
  , ("LONGsuperRelEntries", sd.longSuperRelativeEntries.length)
  , ("longSuperRelWidth", sd.longSuperRelativeWidth)
  , ("SPARSErelEntries", sd.sparseDirectory.relativeEntries.length)
  , ("sparseRelWidth", sd.sparseDirectory.relativeWidth)
  , ("seg12payload", sd.longSuperRelativeTable.payload.length)
  , ("seg16payload", sd.sparseDirectory.relativeTable.payload.length)
  , ("sel.wordSize", sd.wordSize)
  , ("bitWords.words", sd.bitWords.store.words.size)
  ]

def run (n : Nat) : IO Unit := do
  let fam := [("leftSpine", leftSpine n), ("rightSpine", rightSpine n),
              ("balanced", balanced n), ("lopsided", lopsided n)]
  if (fam.map (fun p => p.2.size)).any (fun k => k != n) then
    IO.println s!"n={n} *** SIZE MISMATCH {fam.map (fun p => p.2.size)} ***"
  else
    let rows := fam.map (fun p => (p.1, selGeom p.2))
    match rows with
    | [] => pure ()
    | (_, r0) :: _ =>
      let mut diffs : List String := []
      for k in r0.map (fun q => q.1) do
        let vals := rows.map (fun r => (r.2.lookup k).getD 0)
        let dv := vals.foldl (fun acc v => if acc.contains v then acc else v :: acc) []
        if dv.length > 1 then diffs := s!"{k}::{dv.reverse}" :: diffs
      -- also show that the two codes really are the extreme opposites
      let l := (leftSpine n).bpCode
      let r := (rightSpine n).bpCode
      IO.println s!"n={n} leftSpineCodePrefix={l.take 8} rightSpineCodePrefix={r.take 8} DIFFS={diffs.reverse} baseline={r0}"

#eval show IO Unit from do
  for n in [64, 128, 200, 256] do
    run n

end AdvSZSparse2
