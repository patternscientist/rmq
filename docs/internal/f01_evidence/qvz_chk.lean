import RMQ.Core.SuccinctFinalStoreParam
#check @Nat.le_log2
#check @Nat.log2_pos
#check @Nat.lt_log2_self
example (m : Nat) (h : 2 <= m) : 1 <= Nat.log2 m := Nat.log2_pos h
