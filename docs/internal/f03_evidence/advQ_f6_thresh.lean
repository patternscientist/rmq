import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL / QUANTIFIER attack on the F6 (leaf L1) verdict S.

Step 0: establish that the SIZES the defender swept (shapes of size 1..5,
bitvectors of length 4,6,8,10) are a DEGENERATE regime of the very code they
are quantifying over.  Three size-driven parameters gate the routes:

  bpFringeChunkBits m = Nat.log2 m / 8 + 1          (ChargedFringeChunks.lean:42)
  wordBits n = Nat.log2 n + 1                       (Params.lean:19, SuccinctRank.lean:38)
  superStride n = wordBits n * wordBits n           (Params.lean:25)
  localStride n = max 1 (wordBits n / (ell n * ell n))  (Params.lean:28)
  localSlotsPerSuper n                              (Slots.lean:30)
  superSlotCount bits t = ceil(occurrenceCount / superStride)  (Slots.lean:25)

If at length<=10 we always get c=1 and superSlotCount=1 then the defender's
exhaustive sweep never executed the second chunk-width regime nor a nonzero
super slot, and "exhaustive over lengths 4,6,8,10" is a representative-rows
claim about the code.
-/

open RMQ
open RMQ.Cartesian
open RMQ.GenericSelect
open RMQ.SuccinctClose

namespace AdvQF6T

#eval show IO Unit from do
  IO.println "len | c=bpFringeChunkBits | wordBits | superStride | localStride | localSlotsPerSuper"
  for m in [4, 6, 8, 10, 32, 64, 128, 200, 254, 256, 258, 512, 1024, 2048] do
    IO.println s!"{m} | {bpFringeChunkBits m} | {wordBits m} | {superStride m} | {localStride m} | {localSlotsPerSuper m}"

/-- Max super slot index actually reachable for a BP code of a shape of size n:
`selectSuperSlot q (superStride (2n))` for q < n. -/
#eval show IO Unit from do
  IO.println ""
  IO.println "shape size n | bpLen=2n | c | superStride | maxSuperSlot (q=n-1) | #distinct super slots"
  for n in [1,2,3,4,5, 16, 40, 64, 100, 128, 200, 256, 512] do
    let len := 2 * n
    let ss := superStride len
    let maxSlot := if n = 0 then 0 else selectSuperSlot (n - 1) ss
    IO.println s!"{n} | {len} | {bpFringeChunkBits len} | {ss} | {maxSlot} | {maxSlot + 1}"

end AdvQF6T
