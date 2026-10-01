import RMQ.Core.WordRAM.Lifecycle.Capstone

/-! Additive import for the continuous lifecycle model. The theorem below
concerns modeled construction, retained capacity and reusable queries; native
compiler, FFI and allocator behavior have separate evidence boundaries. -/

namespace RMQ.Headlines

open SuccinctFinal SuccinctFinal.PackedLifecycle

theorem succinctRMQContinuousLifecycle (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2 ^ PackedWordRAM.wordWidth xs.length)
    (hr : right < 2 ^ PackedWordRAM.wordWidth xs.length) :
    ContinuousConstructionQuery model xs left right :=
  continuousConstructionQuery_holds model xs left right domain hl hr

end RMQ.Headlines
