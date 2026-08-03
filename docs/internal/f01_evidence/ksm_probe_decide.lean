import RMQ.Core.SuccinctFinalStoreParam

namespace KsmProbe

example : Nat.log2 512 = 9 := by decide

example : Nat.log2 1024 = 10 := by decide

def base (n : Nat) : Nat := Nat.log2 n + 1

example : ((List.range 64).all (fun n => decide (base n <= 7))) = true := by decide

open RMQ in
example : RMQ.SuccinctSpace.idDivLogLogOverhead 512 (2 * 1024) = 0 := by decide

end KsmProbe
