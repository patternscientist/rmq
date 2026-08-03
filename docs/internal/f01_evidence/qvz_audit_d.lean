import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL AUDIT part D.

The K = 1 decision needs EVERY live-access segment length to be a function of
`n` alone (otherwise a region base is content dependent and the header cannot be
one field).  `sdk_select_header_e.lean` hand-assigns the verdicts; two of the 18
live sources (`.finalRankSuperFalse`, `.finalRankBlockFalse`) get NO size-only
verdict at all -- they are marked `.notSelectSide`.  And they come FIRST in the
live source order, so every later region base depends on them.

This is an EXECUTED falsification test: over all shapes of a given size, does
each segment length take exactly one value?
-/

namespace QvzD

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

def allSources : List ConcreteBPNativeSuccinctRMQFlatPayloadSource :=
  concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessSources

def segLen (shape : CartesianShape)
    (s : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat :=
  (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape s).length

/-- (min, max) of a nonempty Nat list; `min = max` iff the value is constant. -/
def range (xs : List Nat) : Nat × Nat :=
  (xs.foldl Nat.min 1000000000, xs.foldl Nat.max 0)

def isConst (xs : List Nat) : Bool := (range xs).1 == (range xs).2

/-- For size `n`, the (min, max) length each source takes over every shape of
that size.  `min < max` refutes "size only". -/
def spread (n : Nat) (s : ConcreteBPNativeSuccinctRMQFlatPayloadSource) :
    Nat × Nat :=
  range ((Cartesian.shapesOfSize n).map (fun sh => segLen sh s))

#eval "D0. number of shapes per size 0..7"
#eval (List.range 8).map (fun n => (n, (Cartesian.shapesOfSize n).length))

#eval "D1. per source (in live order): is the length CONSTANT over all shapes of each size 0..7?"
#eval allSources.map (fun s =>
  ((List.range 8).all (fun n =>
    isConst ((Cartesian.shapesOfSize n).map (fun sh => segLen sh s)))))

#eval "D2. THE TWO UNADJUDICATED ROWS -- (n, finalRankSuperFalse (min,max), finalRankBlockFalse (min,max))"
#eval (List.range 8).map (fun n =>
  (n, spread n .finalRankSuperFalse, spread n .finalRankBlockFalse))

#eval "D3. full live-access payload length (min,max) per size -- min=max means size only"
#eval (List.range 8).map (fun n =>
  (n, range ((Cartesian.shapesOfSize n).map (fun sh =>
    (concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload sh).length))))

#eval "D4. (n, close (min,max), fringe (min,max), selectChunk (min,max))"
#eval (List.range 8).map (fun n =>
  (n,
   range ((Cartesian.shapesOfSize n).map (fun sh =>
     (SuccinctClose.canonicalRelativeRmmInteriorDirectory sh).payload.length)),
   range ((Cartesian.shapesOfSize n).map (fun sh =>
     (SuccinctClose.bpFringeChunkTable
       (SuccinctClose.bpFringeChunkBits sh.bpCode.length)).payload.length)),
   range ((Cartesian.shapesOfSize n).map (fun sh =>
     (SuccinctClose.bpChunkSelectTable
       (SuccinctClose.bpFringeChunkBits sh.bpCode.length) false).payload.length))))

#eval "D5. TOTAL frozen reviewer payload length (min,max) per size"
#eval (List.range 8).map (fun n =>
  (n, range ((Cartesian.shapesOfSize n).map (fun sh =>
    (concreteBPNativeSuccinctRMQCanonicalReviewerPayload sh).length))))

end QvzD
