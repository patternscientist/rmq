import RMQRankSelect

/-!
# Minimal rank/select import demo

This is the small reusable spoke surface for plain bitvectors. It avoids the
final RMQ capstone import root while exposing the public Jacobson/Clark
rank/select family theorem.
-/

namespace RMQ.Examples.RankSelectImport

abbrev Directory := RMQ.RankSelect.Directory

abbrev Family := RMQ.RankSelect.Family

abbrev jacobsonClarkDirectory :=
  RMQ.RankSelect.jacobsonClarkDirectory

abbrev jacobsonClarkProfile :=
  RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery

end RMQ.Examples.RankSelectImport
