import RMQ.Core.SuccinctSelect.CloseSelect.BuiltRouting.SpanBudgets
import RMQ.Core.SuccinctFinal

open RMQ
open RMQ.SuccinctSelect

/-! Adversarial check of the lane's gap G2 ("cell width is not uniform").
Compare the frozen route word size `machineWordBits shape.bpCode.length`
against the flag-rank directory's own word size
`GenericSelect.flagRankWordSize` on the long-super flag vector. -/

def av_shape (n : Nat) : Cartesian.CartesianShape :=
  Cartesian.shape ((List.range n).map (fun i : Nat => (Int.ofNat i)))

-- (n, frozen route w(n), flagRankWordSize of the long-super flag vector,
--     length of that flag vector)
#eval [1, 2, 4, 8, 16, 32, 64].map fun n =>
  let s := av_shape n
  let flags := builtRelativeSplitFalseSelectLongSuperFlagBits s
  (n,
   SuccinctRank.machineWordBits s.bpCode.length,
   GenericSelect.flagRankWordSize flags,
   flags.length)
