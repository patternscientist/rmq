import RMQ.Core.WordRAM.Lifecycle.Capstone

/-! Additive candidate import for the continuous lifecycle model. Publication
integration and independent coordinator acceptance are separate campaign steps. -/

namespace RMQ.Headlines

open SuccinctFinal SuccinctFinal.PackedLifecycle

theorem succinctRMQContinuousLifecycle (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2 ^ PackedWordRAM.wordWidth xs.length)
    (hr : right < 2 ^ PackedWordRAM.wordWidth xs.length) :
    ContinuousConstructionQuery model xs left right :=
  continuousConstructionQuery_holds model xs left right domain hl hr

end RMQ.Headlines
