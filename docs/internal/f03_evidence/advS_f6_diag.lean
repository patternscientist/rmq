import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL / F6 (L1) — attack the S verdict through the SIZE-ONLY lens.

Step 0: find where the prior agent's evidence regime (n <= 5) sits relative
to the parameter thresholds.  If `superSlotCount = 1` and
`localSlotCount = 1` for all n <= 5, then their sweeps never exercised
multi-slot addressing and the S claim is untested where it matters.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.GenericSelect

namespace AdvS6

/-- BP code of a size-n shape has length 2n and `occurrenceCount _ false = n`. -/
def paramsAt (n : Nat) : String :=
  let m := 2 * n
  let wb := wordBits m
  let ss := superStride m
  let e := ell m
  let ls := localStride m
  let lsps := localSlotsPerSuper m
  let occ := n
  let ssc := selectCeilDiv occ ss
  let lsc := ssc * lsps
  let elsc := Nat.min lsc occ
  s!"n={n} len={m} wordBits={wb} ell={e} superStride={ss} localStride={ls} localSlotsPerSuper={lsps} superSlotCount={ssc} localSlotCount={lsc} effLocalSlotCount={elsc} longFlagRankWordSize={SuccinctRank.machineWordBits ssc} effFlagRankWordSize={SuccinctRank.machineWordBits elsc}"

#eval show IO Unit from do
  for n in [1,2,3,4,5,6,7,8,10,12,16,20,24,32,40,48,63,64,65,80,100,128,200,300,512,1000] do
    IO.println (paramsAt n)

end AdvS6
