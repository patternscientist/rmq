import RMQ.Core.WordRAM.Packed.Guard
import RMQ.Core.WordRAM.Packed.PhysicalRead
import RMQ.Core.WordRAM.Packed.SelectSource
import RMQ.Core.WordRAM.Packed.FringeSource

/-!
# One fixed primitive packed-query program

Only preprocessing receives a value list. The query program below is a closed
constant: endpoints and public size enter through the three input registers,
and every varying geometry/count field is loaded by metadataSetupBlock. In
particular there is no sparse-count scan or size-specialized code prelude.

This module defines the actual entry point and elementary budget/rejection
facts. Canonical valid-query semantics and every reachable word bound must
still be joined before the fully charged capstone can be stated as proved.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Structured

def queryAnswerPrepareBlock : Block :=
  .seq (natSubBlock 1200 2049 2048 2051) (natSubBlock 1201 2050 2048 2051)

def queryRankFinishBlock : Block :=
  .seq (natSubBlock 3 360 2048 2051) (.action (.arithmetic .add 3 3 2048))

def queryFinalRankBlock (reader : Block) : Block :=
  .seq (.action (.move 352 1202)) (.seq (rankCloseBlock reader) queryRankFinishBlock)

def queryAfterLCABlock (reader : Block) : Block := .ifZero 1202 .skip (queryFinalRankBlock reader)

def queryAnswerProgram (reader lca : Block) : Block :=
  .seq queryAnswerPrepareBlock (.seq lca (queryAfterLCABlock reader))

def queryAnswerBlock : Block := queryAnswerProgram logicalReadBlock (lcaCloseBlock logicalReadBlock)

def queryLeftSelectBlock (reader : Block) : Block :=
  .seq (.action (.move 512 0)) (.seq (selectCloseBlock reader) (.action (.move 2049 513)))

def queryRightSelectBlock (reader : Block) : Block :=
  .seq (natSubBlock 512 1 2048 2051) (.seq (selectCloseBlock reader) (.action (.move 2050 513)))

def queryAfterSelectsProgram (reader lca : Block) : Block :=
  .ifZero 2049 .skip (.ifZero 2050 .skip (queryAnswerProgram reader lca))

def querySelectedProgram (reader lca : Block) : Block :=
  .seq (queryLeftSelectBlock reader) (.seq (queryRightSelectBlock reader) (queryAfterSelectsProgram reader lca))

def queryReadyProgram (reader lca : Block) : Block :=
  .seq (.action (.constant 2048 1)) (querySelectedProgram reader lca)

def queryBody : Block :=
  .seq metadataSetupBlock (queryReadyProgram logicalReadBlock (lcaCloseBlock logicalReadBlock))

def querySource : Block := guardedBlock queryBody
def queryProgram : Program := guardedProgram queryBody
def queryBudget : Nat := queryBody.size + 10

def queryRun (memory : Memory) (n left right : Nat) : Run :=
  run memory queryProgram queryBudget (initialState n left right)

/-- Total mathematical wrapper. The outer word-domain check has no assigned
primitive cost; valid mathematical endpoints always pass it. -/
def queryNat (memory : Memory) (n left right : Nat) : Option Nat :=
  match encodeInputs n left right with
  | none => none
  | some state =>
      ((run memory queryProgram queryBudget state).result).bind fun packet =>
        if packet = 0 then none else some (packet - 1)

theorem guardedProgram_refines_source (body : Block) (memory : Memory)
    (s : State) (hpc : s.pc = 0) :
    let source := (guardedBlock body).eval memory (Data.ofState s)
    let actual := run memory (guardedProgram body) (body.size + 10) s
    actual.result = (match source.final.status with
      | .running => some (source.final.regs 3)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ body.size + 10 := by
  have h := (guardedBlock body).compile_with_halt memory 3 s hpc
  simpa only [guardedProgram, guardedBlock_size, List.length_append,
    Block.compile_length, List.length_singleton, Nat.add_assoc] using h.2

/-- The full compiled entry point has exactly its independently evaluated
source result and ordered reads, at the fixed source-derived budget. -/
theorem queryRun_refines_source (memory : Memory) (n left right : Nat) :
    let source := querySource.eval memory (Data.ofState (initialState n left right))
    let actual := queryRun memory n left right
    actual.result = (match source.final.status with
      | .running => some (source.final.regs 3)
      | .halted value => some value
      | .fault => none) ∧
    actual.reads = source.reads ∧ actual.steps ≤ queryBudget :=
  guardedProgram_refines_source queryBody memory (initialState n left right) rfl

theorem queryProgram_length : queryProgram.length = queryBudget := by
  have general : ∀ body : Block, (guardedProgram body).length = body.size + 10 := by
    intro body
    simp [guardedProgram, Nat.add_assoc]
  exact general queryBody

theorem queryRun_steps_le (memory : Memory) (n left right : Nat) :
    (queryRun memory n left right).steps ≤ queryBudget :=
  run_steps_le_fuel _ _ _ _

theorem queryRun_invalid (memory : Memory) (n left right : Nat)
    (hinvalid : ¬ (left < right ∧ right ≤ n)) :
    (queryRun memory n left right).result = some 0 ∧
    (queryRun memory n left right).reads = [] ∧
    (queryRun memory n left right).steps ≤ queryBudget :=
  guardedProgram_invalid queryBody memory n left right hinvalid

theorem queryNat_invalid (memory : Memory) (n left right : Nat)
    (hinvalid : ¬ (left < right ∧ right ≤ n)) :
    queryNat memory n left right = none := by
  by_cases hcap : left < 2 ^ wordWidth n ∧ right < 2 ^ wordWidth n
  · rw [queryNat, encodeInputs, if_pos hcap]
    change ((run memory queryProgram queryBudget (initialState n left right)).result).bind
      (fun packet => if packet = 0 then none else some (packet - 1)) = none
    have hresult := (queryRun_invalid memory n left right hinvalid).1
    change (run memory queryProgram queryBudget (initialState n left right)).result = some 0 at hresult
    rw [hresult]
    rfl
  · rw [queryNat, encodeInputs, if_neg hcap]

end RMQ.SuccinctFinal.PackedWordRAM
