import RMQRankSelect

/-!
# Minimal rank/select import example

This is the small reusable spoke surface for plain bitvectors. It avoids the
final RMQ capstone import root while exposing the public Jacobson/Clark
rank/select family theorem.
-/

namespace RMQ.Examples.RankSelectImport

abbrev Directory := RMQ.RankSelect.Directory

abbrev Family := RMQ.RankSelect.Family

abbrev CompressedFamily := RMQ.RankSelect.CompressedFamily

abbrev fixedWeightPayloadBudget :=
  RMQ.RankSelect.fixedWeightPayloadBudget

abbrev fixedWeightBitstringsLength :=
  RMQ.RankSelect.fixedWeightBitstringsLength

abbrev compressedProfile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : RMQ.RankSelect.CompressedFamily overhead queryCost) :=
  RMQ.RankSelect.compressedFixedWeightConstantQueryProfile family

abbrev jacobsonClarkDirectory :=
  RMQ.RankSelect.jacobsonClarkDirectory

abbrev jacobsonClarkProfile :=
  RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery

abbrev jacobsonClarkWordBoundedProfile :=
  RMQ.RankSelect.jacobsonClarkWordBoundedNPlusOConstantQuery

end RMQ.Examples.RankSelectImport
