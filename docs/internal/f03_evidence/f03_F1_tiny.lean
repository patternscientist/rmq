import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace F03F1Tiny

def s3a : CartesianShape :=
  CartesianShape.node (CartesianShape.node (CartesianShape.node CartesianShape.empty CartesianShape.empty) CartesianShape.empty) CartesianShape.empty
def s3b : CartesianShape :=
  CartesianShape.node CartesianShape.empty (CartesianShape.node CartesianShape.empty (CartesianShape.node CartesianShape.empty CartesianShape.empty))
def s3c : CartesianShape :=
  CartesianShape.node (CartesianShape.node CartesianShape.empty CartesianShape.empty) (CartesianShape.node CartesianShape.empty CartesianShape.empty)

def hashStore : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 16).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

#eval s3a.bpCode
#eval s3b.bpCode
#eval (builtRelativeSplitBPCloseRankData s3a).wordSize
#eval (builtRelativeSplitBPCloseRankData s3a).blocksPerSuper
#eval (concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore s3a hashStore 6 3).trace.length

end F03F1Tiny
