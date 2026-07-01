import RMQ.Headlines

/-!
# Minimal headline import example

This file shows the short public theorem aliases intended for talks, READMEs,
and external reuse. The aliases point at the full construction-heavy theorem
names; they do not change statements or proof dependencies.
-/

namespace RMQ.Examples.RMQHeadlines

abbrev lowerBound :=
  RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack

abbrev rankSelect :=
  RMQ.Headlines.rankSelectNPlusOConstantQuery

abbrev rankSelectWordBounded :=
  RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery

abbrev rankSelectCompressedFID :=
  RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile

abbrev rankSelectCompressedFIDInterpreted :=
  RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile

abbrev succinctRMQ :=
  RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery

abbrev succinctRMQInterpreted :=
  RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted

abbrev bpCloseNavigationInterpreted
    {rankSlots selectSlots lcaSlots : Nat}
    (family :
      RMQ.SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
        rankSlots selectSlots lcaSlots) :=
  RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery family

end RMQ.Examples.RMQHeadlines
