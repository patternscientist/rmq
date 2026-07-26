import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-! F03 / F1: are the chunk-segment addresses probe-obtained (P) or static (S)? -/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace F03F1Addr

def spine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (spine n)

/-- Store whose word at the PACKED-WORD segment (base+2) is chosen by `w`,
    everything else constant. base is 6, so the word segment is 8. -/
def storeWithWord (w : List Bool) : WordRAM.ReadStore where
  readWord? := fun seg _ => if seg == 8 then some w else some [true, true, false, false, true]

def F1reads (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    List (Nat × Nat) :=
  ((concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store base pos).trace).filterMap
    fun e =>
      match e with
      | WordRAM.TraceEvent.readWord s i _ => some (s, i)
      | _ => none

#eval show IO Unit from do
  let s := spine 9      -- bpLen = 18, wordSize = 5, c = bpFringeChunkBits 18 = 1
  IO.println s!"bpLen={s.bpCode.length} wordSize={(builtRelativeSplitBPCloseRankData s).wordSize} \
c={RMQ.SuccinctClose.bpFringeChunkBits s.bpCode.length}"
  for w in [[false,false,false,false,false,false,false,false],
            [true,true,true,true,true,true,true,true],
            [true,false,true,false,true,false,true,false],
            [false,true,false,true,false,true,false,true]] do
    IO.println s!"  wordReply={w} reads={F1reads s (storeWithWord w) 6 4}"

end F03F1Addr
