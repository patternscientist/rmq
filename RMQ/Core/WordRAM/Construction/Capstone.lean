import RMQ.Core.WordRAM.Construction.Proof.RunFacts
import RMQ.Core.WordRAM.Construction.Proof.Query
import RMQ.Core.WordRAM.Construction.Proof.Lift
import RMQ.Core.WordRAM.Construction.Proof.Static

/-! # PRE-1 construction-and-query capstone (stage S8)

One statement joins the uniform efficient builder and the accepted fully charged
packed query on the same emitted cells.

Recorded limit (coordinator ruling Q3): the query is joined to the builder
through (a) positional store provenance for every output cell on
`[outBase, extent)` (`BuilderRunFacts.outputProvenance`), (b) the accepted PQ1
capstone transported over the list equality `efficientBuild xs = buildMemory xs`
(`queryOnEmitted`), and (c) a lifted Conservative simulation of the accepted
query program in the construction instruction set on the detached emitted list
(`translatedQueryRun`, `translatedQueryOnEmitted`). An offset-relocated query
execution inside the builder's own memory is not claimed. The work and
workspace literals are crude upper bounds; no tightness or optimality is claimed.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

open RMQ.SuccinctFinal.PackedWordRAM hiding State Registers Transition Memory Status Run run Instruction execute
  Program initialState

/-- The PRE-1 construction-and-query capstone. -/
structure ConstructionAndQueryCapstone : Prop where
  exactComparison : ∀ xs : List Int, efficientBuild xs = buildMemory xs
  exactWord : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
    efficientBuildWord (wordWidth xs.length) xs = buildMemory xs
  programContract : ProgramContract builderProgram (fun _ => builderProgram) 2107 8079
  programContractWord : ProgramContract builderProgramWord (fun _ => builderProgramWord) 2107 8089
  leafDifference :
    builderProgram.length = builderProgramWord.length ∧
    (List.range builderProgram.length).filter
        (fun i => builderProgram[i]? ≠ builderProgramWord[i]?) = [411, 412, 413, 414, 415, 429, 430, 431, 432, 433] ∧
    ([411, 412, 413, 414, 415, 429, 430, 431, 432, 433] : List Nat).map (fun i => builderProgram[i]?) =
      [some ⟨.loadKey 0 4⟩, some ⟨.loadKey 1 5⟩, some ⟨.compareKey 6 0 1⟩, some ⟨.move 6 6⟩,
        some ⟨.move 6 6⟩, some ⟨.loadKey 0 4⟩, some ⟨.loadKey 1 5⟩, some ⟨.compareKey 6 0 1⟩,
        some ⟨.move 6 6⟩, some ⟨.move 6 6⟩] ∧
    ([411, 412, 413, 414, 415, 429, 430, 431, 432, 433] : List Nat).map (fun i => builderProgramWord[i]?) =
      [some ⟨.arithmetic .add 7 4 2⟩, some ⟨.load 7 7⟩, some ⟨.arithmetic .add 8 5 2⟩,
        some ⟨.load 8 8⟩, some ⟨.comparison .lt 6 7 8⟩, some ⟨.arithmetic .add 7 4 2⟩,
        some ⟨.load 7 7⟩, some ⟨.arithmetic .add 8 5 2⟩, some ⟨.load 8 8⟩,
        some ⟨.comparison .lt 6 7 8⟩]
  budgetBody : ∀ n : Nat, builderBudget n = 1000000000 * n + 1000000000
  headerUse : HeaderUse builderProgram
  headerUseWord : HeaderUse builderProgramWord
  comparisonInput : ∀ xs : List Int, (comparisonInputState xs).extent = 1 ∧
    (comparisonInputState xs).memory 0 = some xs.length ∧
    (∀ a, a ≠ 0 → (comparisonInputState xs).memory a = none) ∧
    (comparisonInputState xs).keys = fun i => xs[i]?
  wordInput : ∀ (width : Nat) (xs : List Int), (wordInputState width xs).extent = xs.length + 1 ∧
    (wordInputState width xs).memory = encodeInput width xs ∧
    (wordInputState width xs).keys = fun _ => none
  zeroFamily : ∀ n : Nat, InputFits (wordWidth n) (List.replicate n (0 : Int))
  comparisonRun : ∀ xs : List Int, BuilderRunFacts builderProgram (comparisonInputState xs) xs
  wordRun : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
    BuilderRunFacts builderProgramWord (wordInputState (wordWidth xs.length) xs) xs
  jointResidualLittleO : SuccinctSpace.LittleOLinear constructionCompleteRho
  jointCapacity : ∀ xs : List Int,
    ((buildMemory xs).length + (queryProgramWords + programWords builderProgram + programWords builderProgramWord) +
      (queryScratchWords + 400)) * wordWidth xs.length ≤ 2 * xs.length + constructionCompleteRho xs.length
  queryCapstone : FullyChargedPackedQueryCapstone
  queryOnEmitted : ∀ xs : List Int, PackedQueryOn (efficientBuild xs) xs
  queryOnEmittedWord : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
    PackedQueryOn (efficientBuildWord (wordWidth xs.length) xs) xs
  translatedQueryFits : ∀ i ∈ queryProgram, i.Fits 32
  translatedQueryRun : ∀ (memory : PackedWordRAM.Memory) (fuel : Nat) (s : PackedWordRAM.State),
    (run Conservative.translatedQueryProgram fuel (Conservative.state memory s)).final =
      Conservative.state memory (PackedWordRAM.run memory queryProgram fuel s).final ∧
    (run Conservative.translatedQueryProgram fuel (Conservative.state memory s)).steps =
      (PackedWordRAM.run memory queryProgram fuel s).steps
  translatedQueryOnEmitted : ∀ (xs : List Int) (left right : Nat),
    left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
    (run Conservative.translatedQueryProgram queryBudget
        (Conservative.state (efficientBuild xs) (PackedWordRAM.initialState xs.length left right))).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
    (run Conservative.translatedQueryProgram queryBudget
        (Conservative.state (efficientBuild xs) (PackedWordRAM.initialState xs.length left right))).steps ≤ queryBudget
  programStatic : ∀ n : Nat, ∀ i ∈ builderProgram, i.primitive.OperandsFit (wordWidth n) ∧
    i.primitive.RegistersBelow 400 ∧
    (∀ c t, i.primitive = .branchZero c t → t.val < builderProgram.length) ∧
    (∀ t, i.primitive = .jump t → t.val < builderProgram.length) ∧
    (∀ src, i.primitive ≠ .jumpRegister src)
  programStaticWord : ∀ n : Nat, ∀ i ∈ builderProgramWord, i.primitive.OperandsFit (wordWidth n) ∧
    i.primitive.RegistersBelow 400 ∧
    (∀ c t, i.primitive = .branchZero c t → t.val < builderProgramWord.length) ∧
    (∀ t, i.primitive = .jump t → t.val < builderProgramWord.length) ∧
    (∀ src, i.primitive ≠ .jumpRegister src)

theorem translated_status_of (memory : PackedWordRAM.Memory) (R : PackedWordRAM.Run) (Rn : Run) (v : Nat)
    (hfin : Rn.final = Conservative.state memory R.final) (hhalt : R.final.status = .halted v) :
    Rn.final.status = .halted v := by
  rw [hfin]
  simp [Conservative.state, hhalt, Conservative.status]

/-- **The PRE-1 construction-and-query capstone holds.** -/
theorem constructionAndQueryCapstone_holds : ConstructionAndQueryCapstone where
  exactComparison := Proof.efficientBuild_eq_buildMemory
  exactWord := Proof.efficientBuildWord_eq_buildMemory
  programContract := Proof.builderProgram_contract
  programContractWord := Proof.builderProgramWord_contract
  leafDifference := Proof.builder_leaf_difference
  budgetBody := Proof.builderBudget_eq_mul_add
  headerUse := Proof.builderProgram_headerUse
  headerUseWord := Proof.builderProgramWord_headerUse
  comparisonInput xs := ⟨rfl, by simp [comparisonInputState], fun a ha => by simp [comparisonInputState, ha], rfl⟩
  wordInput width xs := ⟨rfl, rfl, rfl⟩
  zeroFamily n := zero_inputFits (by have := Proof.wordWidth_ge_32 n; omega)
    (by simpa using Proof.length_lt_wordWidth n)
  comparisonRun := Proof.comparisonRunFacts
  wordRun := Proof.wordRunFacts
  jointResidualLittleO := constructionCompleteRho_littleO
  jointCapacity := construction_complete_capacity
  queryCapstone := fullyChargedPackedQueryCapstone_holds
  queryOnEmitted := packedQueryOn_efficientBuild
  queryOnEmittedWord := packedQueryOn_efficientBuildWord
  translatedQueryFits := Conservative.queryProgram_fits32
  translatedQueryRun memory fuel s := Conservative.translated_run memory fuel s
  translatedQueryOnEmitted xs left right hl hr := by
    obtain ⟨hfin, hsteps⟩ := Conservative.translated_run (efficientBuild xs) queryBudget
      (PackedWordRAM.initialState xs.length left right)
    have q := packedQueryOn_efficientBuild xs
    exact ⟨translated_status_of _ _ _ _ hfin (q.halt left right hl hr),
      Nat.le_trans (Nat.le_of_eq hsteps) (q.stepBound left right)⟩
  programStatic := Proof.builderProgram_static
  programStaticWord := Proof.builderProgramWord_static

end RMQ.SuccinctFinal.PackedConstruction
