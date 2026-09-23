import RMQ.Core.WordRAM.Construction.Capstone
import Lean

/-! # Independent exact-type consumer of the PRE-1 construction-and-query capstone

Every field of `ConstructionAndQueryCapstone` is projected below at a type
written out in full: the builder run facts of both program constants and the
accepted query's facts on both emitted allocations field by field, the header
certificate and contract fields of both constants, and every scalar field. The
literals `2107`, `8079`, `8089`, `1000000000`, `3200000` and `400` are pinned
here. The marker is printed only when the whole file elaborates without an error
and the witness is free of `sorryAx`. This file is not imported by `RMQ.lean` (coordinator integration step).
-/

namespace RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks

open RMQ.SuccinctFinal.PackedConstruction
open RMQ.SuccinctFinal.PackedWordRAM hiding State Registers Transition Memory Status Run run Instruction execute
  Program initialState
open Structured

theorem capstone : ConstructionAndQueryCapstone := constructionAndQueryCapstone_holds

theorem check_exactComparison :
  ∀ xs : List Int, efficientBuild xs = buildMemory xs :=
  capstone.exactComparison

theorem check_exactWord :
  ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
      efficientBuildWord (wordWidth xs.length) xs = buildMemory xs :=
  capstone.exactWord

theorem check_programContract_uniform :
  Uniform builderProgram (fun _ => builderProgram) :=
  capstone.programContract.uniform

theorem check_programContract_lengthPinned :
  builderProgram.length = 2107 :=
  capstone.programContract.lengthPinned

theorem check_programContract_encodedPinned :
  programWords builderProgram = 8079 :=
  capstone.programContract.encodedPinned

theorem check_programContract_codeBits :
  ∀ width, CodeAccounting builderProgram width (8079 * width) :=
  capstone.programContract.codeBits

theorem check_programContractWord_uniform :
  Uniform builderProgramWord (fun _ => builderProgramWord) :=
  capstone.programContractWord.uniform

theorem check_programContractWord_lengthPinned :
  builderProgramWord.length = 2107 :=
  capstone.programContractWord.lengthPinned

theorem check_programContractWord_encodedPinned :
  programWords builderProgramWord = 8089 :=
  capstone.programContractWord.encodedPinned

theorem check_programContractWord_codeBits :
  ∀ width, CodeAccounting builderProgramWord width (8089 * width) :=
  capstone.programContractWord.codeBits

theorem check_leafDifference :
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
          some ⟨.comparison .lt 6 7 8⟩] :=
  capstone.leafDifference

theorem check_budgetBody :
  ∀ n : Nat, builderBudget n = 1000000000 * n + 1000000000 :=
  capstone.budgetBody

theorem check_headerUse_headerFirst :
  builderProgram[0]? = some headerInstruction :=
  capstone.headerUse.headerFirst

theorem check_headerUse_tailNeverWritesR1 :
  ∀ i ∈ builderProgram.tail, WritesOnly (fun r => r ≠ 1) i :=
  capstone.headerUse.tailNeverWritesR1

theorem check_headerUse_wordMissingHeaderFault :
  ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      (run builderProgram fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.status =
          .fault ∧
      (run builderProgram fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).steps = 1 ∧
      (run builderProgram fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).writes = [] ∧
      (run builderProgram fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).reserves = [] ∧
      (run builderProgram fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.extent =
          (wordInputState width xs).extent :=
  capstone.headerUse.wordMissingHeaderFault

theorem check_headerUse_comparisonMissingHeaderFault :
  ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      (run builderProgram fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).final.status = .fault ∧
      (run builderProgram fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).steps = 1 ∧
      (run builderProgram fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).writes = [] ∧
      (run builderProgram fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).reserves = [] ∧
      (run builderProgram fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).final.extent =
          (comparisonInputState xs).extent :=
  capstone.headerUse.comparisonMissingHeaderFault

theorem check_headerUse_wordHeaderReceipt :
  ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      ∃ t : Transition, (run builderProgram fuel (wordInputState width xs)).transitions[0]? = some t ∧
        t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
        t.after.regs 1 = xs.length ∧ t.after.status = .running :=
  capstone.headerUse.wordHeaderReceipt

theorem check_headerUse_comparisonHeaderReceipt :
  ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      ∃ t : Transition, (run builderProgram fuel (comparisonInputState xs)).transitions[0]? = some t ∧
        t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
        t.after.regs 1 = xs.length ∧ t.after.status = .running :=
  capstone.headerUse.comparisonHeaderReceipt

theorem check_headerUse_oracleExtentOne :
  ∀ xs : List Int, (comparisonInputState xs).extent = 1 :=
  capstone.headerUse.oracleExtentOne

theorem check_headerUseWord_headerFirst :
  builderProgramWord[0]? = some headerInstruction :=
  capstone.headerUseWord.headerFirst

theorem check_headerUseWord_tailNeverWritesR1 :
  ∀ i ∈ builderProgramWord.tail, WritesOnly (fun r => r ≠ 1) i :=
  capstone.headerUseWord.tailNeverWritesR1

theorem check_headerUseWord_wordMissingHeaderFault :
  ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      (run builderProgramWord fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.status =
          .fault ∧
      (run builderProgramWord fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).steps = 1 ∧
      (run builderProgramWord fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).writes = [] ∧
      (run builderProgramWord fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).reserves = [] ∧
      (run builderProgramWord fuel
        { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.extent =
          (wordInputState width xs).extent :=
  capstone.headerUseWord.wordMissingHeaderFault

theorem check_headerUseWord_comparisonMissingHeaderFault :
  ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      (run builderProgramWord fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).final.status = .fault ∧
      (run builderProgramWord fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).steps = 1 ∧
      (run builderProgramWord fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).writes = [] ∧
      (run builderProgramWord fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).reserves = [] ∧
      (run builderProgramWord fuel
        { comparisonInputState xs with
          memory := put (comparisonInputState xs).memory 0 none }).final.extent =
          (comparisonInputState xs).extent :=
  capstone.headerUseWord.comparisonMissingHeaderFault

theorem check_headerUseWord_wordHeaderReceipt :
  ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      ∃ t : Transition, (run builderProgramWord fuel (wordInputState width xs)).transitions[0]? = some t ∧
        t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
        t.after.regs 1 = xs.length ∧ t.after.status = .running :=
  capstone.headerUseWord.wordHeaderReceipt

theorem check_headerUseWord_comparisonHeaderReceipt :
  ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
      ∃ t : Transition, (run builderProgramWord fuel (comparisonInputState xs)).transitions[0]? = some t ∧
        t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
        t.after.regs 1 = xs.length ∧ t.after.status = .running :=
  capstone.headerUseWord.comparisonHeaderReceipt

theorem check_headerUseWord_oracleExtentOne :
  ∀ xs : List Int, (comparisonInputState xs).extent = 1 :=
  capstone.headerUseWord.oracleExtentOne

theorem check_comparisonInput :
  ∀ xs : List Int, (comparisonInputState xs).extent = 1 ∧
      (comparisonInputState xs).memory 0 = some xs.length ∧
      (∀ a, a ≠ 0 → (comparisonInputState xs).memory a = none) ∧
      (comparisonInputState xs).keys = fun i => xs[i]? :=
  capstone.comparisonInput

theorem check_wordInput :
  ∀ (width : Nat) (xs : List Int), (wordInputState width xs).extent = xs.length + 1 ∧
      (wordInputState width xs).memory = encodeInput width xs ∧
      (wordInputState width xs).keys = fun _ => none :=
  capstone.wordInput

theorem check_zeroFamily :
  ∀ n : Nat, InputFits (wordWidth n) (List.replicate n (0 : Int)) :=
  capstone.zeroFamily

theorem check_comparisonRun_halts : ∀ xs : List Int,
  ∃ outBase, (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status = .halted outBase :=
  fun xs => (capstone.comparisonRun xs).halts

theorem check_comparisonRun_work : ∀ xs : List Int,
  (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).steps ≤ 1000000000 * xs.length + 1000000000 :=
  fun xs => (capstone.comparisonRun xs).work

theorem check_comparisonRun_fuelInsensitive : ∀ xs : List Int,
  ∀ extra,
      run builderProgram (builderBudget xs.length + extra) (comparisonInputState xs) = run builderProgram (builderBudget xs.length) (comparisonInputState xs) :=
  fun xs => (capstone.comparisonRun xs).fuelInsensitive

theorem check_comparisonRun_categoryPartition : ∀ xs : List Int,
  (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).steps =
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .read +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .register +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .arithmetic +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .comparison +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .branch +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .control +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .write +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .allocation +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .keyRead +
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).categoryCount .oracleComparison :=
  fun xs => (capstone.comparisonRun xs).categoryPartition

theorem check_comparisonRun_outputCells : ∀ xs : List Int,
  ∀ outBase, (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status = .halted outBase →
      (comparisonInputState xs).extent ≤ outBase ∧
      (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.extent =
        outBase + (PackedWordRAM.buildMemory xs).length ∧
      ∀ i, i < (PackedWordRAM.buildMemory xs).length →
        (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.memory (outBase + i) =
          some ((PackedWordRAM.buildMemory xs).getD i 0) :=
  fun xs => (capstone.comparisonRun xs).outputCells

theorem check_comparisonRun_outputProvenance : ∀ xs : List Int,
  ∀ outBase i, (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status = .halted outBase →
      i < (PackedWordRAM.buildMemory xs).length →
      ∃ (k : Nat) (t : Transition), (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).transitions[k]? = some t ∧
        t.write? = some (outBase + i, (PackedWordRAM.buildMemory xs).getD i 0) ∧
        ∀ (k' : Nat) (t' : Transition), k < k' →
          (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).transitions[k']? = some t' →
          ∀ e : Nat × Nat, t'.write? = some e → e.1 ≠ outBase + i :=
  fun xs => (capstone.comparisonRun xs).outputProvenance

theorem check_comparisonRun_workspace : ∀ xs : List Int,
  ∀ outBase, (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status = .halted outBase →
      outBase - (comparisonInputState xs).extent ≤ 3200000 * xs.length + 3200000 :=
  fun xs => (capstone.comparisonRun xs).workspace

theorem check_comparisonRun_peakExtent : ∀ xs : List Int,
  ∀ fuel,
      (run builderProgram fuel (comparisonInputState xs)).final.extent ≤ (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.extent :=
  fun xs => (capstone.comparisonRun xs).peakExtent

theorem check_comparisonRun_prefixExtent : ∀ xs : List Int,
  ∀ fuel outBase, (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status = .halted outBase →
      (run builderProgram fuel (comparisonInputState xs)).final.extent ≤
        (comparisonInputState xs).extent + (3200000 * xs.length + 3200000) + (PackedWordRAM.buildMemory xs).length :=
  fun xs => (capstone.comparisonRun xs).prefixExtent

theorem check_comparisonRun_registerBank : ∀ xs : List Int,
  ∀ fuel reg, 400 ≤ reg → (run builderProgram fuel (comparisonInputState xs)).final.regs reg = 0 :=
  fun xs => (capstone.comparisonRun xs).registerBank

theorem check_comparisonRun_initialFits : ∀ xs : List Int,
  (comparisonInputState xs).Fits (PackedWordRAM.wordWidth xs.length) :=
  fun xs => (capstone.comparisonRun xs).initialFits

theorem check_comparisonRun_runSafe : ∀ xs : List Int,
  Run.Safe (PackedWordRAM.wordWidth xs.length) builderProgram (run builderProgram (builderBudget xs.length) (comparisonInputState xs)) :=
  fun xs => (capstone.comparisonRun xs).runSafe

theorem check_comparisonRun_finalFits : ∀ xs : List Int,
  (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.Fits (PackedWordRAM.wordWidth xs.length) :=
  fun xs => (capstone.comparisonRun xs).finalFits

theorem check_comparisonRun_noInputWrites : ∀ xs : List Int,
  ∀ e ∈ (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).writes, (comparisonInputState xs).extent ≤ e.1 :=
  fun xs => (capstone.comparisonRun xs).noInputWrites

theorem check_comparisonRun_inputRetained : ∀ xs : List Int,
  (∀ a, a < (comparisonInputState xs).extent → (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.memory a = (comparisonInputState xs).memory a) ∧
      (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.keys = (comparisonInputState xs).keys :=
  fun xs => (capstone.comparisonRun xs).inputRetained

theorem check_comparisonRun_replay : ∀ xs : List Int,
  Replays (comparisonInputState xs).memory (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).writes
      (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.memory :=
  fun xs => (capstone.comparisonRun xs).replay

theorem check_comparisonRun_cleanTail : ∀ xs : List Int,
  ∀ fuel, CleanTail (run builderProgram fuel (comparisonInputState xs)).final :=
  fun xs => (capstone.comparisonRun xs).cleanTail

theorem check_comparisonRun_readAgreement : ∀ xs : List Int,
  ∀ s', State.Agree (comparisonInputState xs) s' →
      (∀ a ∈ (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).loads, s'.memory a = (comparisonInputState xs).memory a) →
      (∀ i ∈ (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).keyReads, s'.keys i = (comparisonInputState xs).keys i) →
      Run.Agree (run builderProgram (builderBudget xs.length) (comparisonInputState xs)) (run builderProgram (builderBudget xs.length) s') :=
  fun xs => (capstone.comparisonRun xs).readAgreement

theorem check_comparisonRun_suppliedAgreement : ∀ xs : List Int,
  ∀ s', State.Agree (comparisonInputState xs) s' → CleanTail s' →
      (∀ a, a < (comparisonInputState xs).extent → s'.memory a = (comparisonInputState xs).memory a) →
      (∀ i ∈ (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).keyReads, s'.keys i = (comparisonInputState xs).keys i) →
      s'.memory = (comparisonInputState xs).memory ∧
        Run.Agree (run builderProgram (builderBudget xs.length) (comparisonInputState xs)) (run builderProgram (builderBudget xs.length) s') :=
  fun xs => (capstone.comparisonRun xs).suppliedAgreement

theorem check_comparisonRun_arrayReflects : ∀ xs : List Int,
  ∀ (es : ExecState) fuel, es.abstract = (comparisonInputState xs) → es.regs.size = 400 → es.keyRegs.size = 400 →
      (runArray builderProgram.toArray fuel es).steps = (run builderProgram fuel (comparisonInputState xs)).steps ∧
      (runArray builderProgram.toArray fuel es).categories = (run builderProgram fuel (comparisonInputState xs)).categories ∧
      (runArray builderProgram.toArray fuel es).writes = (run builderProgram fuel (comparisonInputState xs)).writes ∧
      (runArray builderProgram.toArray fuel es).reserves = (run builderProgram fuel (comparisonInputState xs)).reserves ∧
      (runArray builderProgram.toArray fuel es).result = (run builderProgram fuel (comparisonInputState xs)).result ∧
      (runArray builderProgram.toArray fuel es).final.abstract = (run builderProgram fuel (comparisonInputState xs)).final :=
  fun xs => (capstone.comparisonRun xs).arrayReflects

theorem check_wordRun_halts : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∃ outBase, (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.status = .halted outBase :=
  fun xs h => (capstone.wordRun xs h).halts

theorem check_wordRun_work : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).steps ≤ 1000000000 * xs.length + 1000000000 :=
  fun xs h => (capstone.wordRun xs h).work

theorem check_wordRun_fuelInsensitive : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ extra,
      run builderProgramWord (builderBudget xs.length + extra) (wordInputState (wordWidth xs.length) xs) = run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs) :=
  fun xs h => (capstone.wordRun xs h).fuelInsensitive

theorem check_wordRun_categoryPartition : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).steps =
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .read +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .register +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .arithmetic +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .comparison +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .branch +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .control +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .write +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .allocation +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .keyRead +
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).categoryCount .oracleComparison :=
  fun xs h => (capstone.wordRun xs h).categoryPartition

theorem check_wordRun_outputCells : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ outBase, (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.status = .halted outBase →
      (wordInputState (wordWidth xs.length) xs).extent ≤ outBase ∧
      (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.extent =
        outBase + (PackedWordRAM.buildMemory xs).length ∧
      ∀ i, i < (PackedWordRAM.buildMemory xs).length →
        (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.memory (outBase + i) =
          some ((PackedWordRAM.buildMemory xs).getD i 0) :=
  fun xs h => (capstone.wordRun xs h).outputCells

theorem check_wordRun_outputProvenance : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ outBase i, (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.status = .halted outBase →
      i < (PackedWordRAM.buildMemory xs).length →
      ∃ (k : Nat) (t : Transition), (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).transitions[k]? = some t ∧
        t.write? = some (outBase + i, (PackedWordRAM.buildMemory xs).getD i 0) ∧
        ∀ (k' : Nat) (t' : Transition), k < k' →
          (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).transitions[k']? = some t' →
          ∀ e : Nat × Nat, t'.write? = some e → e.1 ≠ outBase + i :=
  fun xs h => (capstone.wordRun xs h).outputProvenance

theorem check_wordRun_workspace : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ outBase, (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.status = .halted outBase →
      outBase - (wordInputState (wordWidth xs.length) xs).extent ≤ 3200000 * xs.length + 3200000 :=
  fun xs h => (capstone.wordRun xs h).workspace

theorem check_wordRun_peakExtent : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ fuel,
      (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).final.extent ≤ (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.extent :=
  fun xs h => (capstone.wordRun xs h).peakExtent

theorem check_wordRun_prefixExtent : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ fuel outBase, (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.status = .halted outBase →
      (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).final.extent ≤
        (wordInputState (wordWidth xs.length) xs).extent + (3200000 * xs.length + 3200000) + (PackedWordRAM.buildMemory xs).length :=
  fun xs h => (capstone.wordRun xs h).prefixExtent

theorem check_wordRun_registerBank : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ fuel reg, 400 ≤ reg → (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).final.regs reg = 0 :=
  fun xs h => (capstone.wordRun xs h).registerBank

theorem check_wordRun_initialFits : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  (wordInputState (wordWidth xs.length) xs).Fits (PackedWordRAM.wordWidth xs.length) :=
  fun xs h => (capstone.wordRun xs h).initialFits

theorem check_wordRun_runSafe : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  Run.Safe (PackedWordRAM.wordWidth xs.length) builderProgramWord (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)) :=
  fun xs h => (capstone.wordRun xs h).runSafe

theorem check_wordRun_finalFits : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.Fits (PackedWordRAM.wordWidth xs.length) :=
  fun xs h => (capstone.wordRun xs h).finalFits

theorem check_wordRun_noInputWrites : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ e ∈ (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).writes, (wordInputState (wordWidth xs.length) xs).extent ≤ e.1 :=
  fun xs h => (capstone.wordRun xs h).noInputWrites

theorem check_wordRun_inputRetained : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  (∀ a, a < (wordInputState (wordWidth xs.length) xs).extent → (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.memory a = (wordInputState (wordWidth xs.length) xs).memory a) ∧
      (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.keys = (wordInputState (wordWidth xs.length) xs).keys :=
  fun xs h => (capstone.wordRun xs h).inputRetained

theorem check_wordRun_replay : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  Replays (wordInputState (wordWidth xs.length) xs).memory (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).writes
      (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).final.memory :=
  fun xs h => (capstone.wordRun xs h).replay

theorem check_wordRun_cleanTail : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ fuel, CleanTail (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).final :=
  fun xs h => (capstone.wordRun xs h).cleanTail

theorem check_wordRun_readAgreement : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ s', State.Agree (wordInputState (wordWidth xs.length) xs) s' →
      (∀ a ∈ (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).loads, s'.memory a = (wordInputState (wordWidth xs.length) xs).memory a) →
      (∀ i ∈ (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).keyReads, s'.keys i = (wordInputState (wordWidth xs.length) xs).keys i) →
      Run.Agree (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)) (run builderProgramWord (builderBudget xs.length) s') :=
  fun xs h => (capstone.wordRun xs h).readAgreement

theorem check_wordRun_suppliedAgreement : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ s', State.Agree (wordInputState (wordWidth xs.length) xs) s' → CleanTail s' →
      (∀ a, a < (wordInputState (wordWidth xs.length) xs).extent → s'.memory a = (wordInputState (wordWidth xs.length) xs).memory a) →
      (∀ i ∈ (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)).keyReads, s'.keys i = (wordInputState (wordWidth xs.length) xs).keys i) →
      s'.memory = (wordInputState (wordWidth xs.length) xs).memory ∧
        Run.Agree (run builderProgramWord (builderBudget xs.length) (wordInputState (wordWidth xs.length) xs)) (run builderProgramWord (builderBudget xs.length) s') :=
  fun xs h => (capstone.wordRun xs h).suppliedAgreement

theorem check_wordRun_arrayReflects : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ (es : ExecState) fuel, es.abstract = (wordInputState (wordWidth xs.length) xs) → es.regs.size = 400 → es.keyRegs.size = 400 →
      (runArray builderProgramWord.toArray fuel es).steps = (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).steps ∧
      (runArray builderProgramWord.toArray fuel es).categories = (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).categories ∧
      (runArray builderProgramWord.toArray fuel es).writes = (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).writes ∧
      (runArray builderProgramWord.toArray fuel es).reserves = (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).reserves ∧
      (runArray builderProgramWord.toArray fuel es).result = (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).result ∧
      (runArray builderProgramWord.toArray fuel es).final.abstract = (run builderProgramWord fuel (wordInputState (wordWidth xs.length) xs)).final :=
  fun xs h => (capstone.wordRun xs h).arrayReflects

theorem check_jointResidualLittleO :
  SuccinctSpace.LittleOLinear constructionCompleteRho :=
  capstone.jointResidualLittleO

theorem check_jointCapacity :
  ∀ xs : List Int,
      ((buildMemory xs).length + (queryProgramWords + programWords builderProgram + programWords builderProgramWord) +
        (queryScratchWords + 400)) * wordWidth xs.length ≤ 2 * xs.length + constructionCompleteRho xs.length :=
  capstone.jointCapacity

theorem check_queryCapstone :
  FullyChargedPackedQueryCapstone :=
  capstone.queryCapstone

theorem check_queryOnEmitted_dataCapacity : ∀ xs : List Int,
  (efficientBuild xs).length * wordWidth xs.length ≤ 2 * xs.length + allocationRho xs.length :=
  fun xs => (capstone.queryOnEmitted xs).dataCapacity

theorem check_queryOnEmitted_completeCapacity : ∀ xs : List Int,
  ((efficientBuild xs).length + (queryProgram.map PackedWordRAM.Instruction.encoding).flatten.length +
        (queryRegisterCount + 3)) * wordWidth xs.length ≤ 2 * xs.length + queryCompleteRho xs.length :=
  fun xs => (capstone.queryOnEmitted xs).completeCapacity

theorem check_queryOnEmitted_memoryWordsFit : ∀ xs : List Int,
  ∀ word, word ∈ (efficientBuild xs) → word < 2 ^ wordWidth xs.length :=
  fun xs => (capstone.queryOnEmitted xs).memoryWordsFit

theorem check_queryOnEmitted_allocationAddressesFit : ∀ xs : List Int,
  ∀ address, address ≤ (efficientBuild xs).length → address < 2 ^ wordWidth xs.length :=
  fun xs => (capstone.queryOnEmitted xs).allocationAddressesFit

theorem check_queryOnEmitted_unusedRegisters : ∀ xs : List Int,
  ∀ left right fuel r, queryRegisterCount ≤ r →
      (PackedWordRAM.run (efficientBuild xs) queryProgram fuel (PackedWordRAM.initialState xs.length left right)).final.regs r = 0 :=
  fun xs => (capstone.queryOnEmitted xs).unusedRegisters

theorem check_queryOnEmitted_natContract : ∀ xs : List Int,
  ∀ left right,
      queryNat (efficientBuild xs) xs.length left right =
        if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  fun xs => (capstone.queryOnEmitted xs).natContract

theorem check_queryOnEmitted_leftmost : ∀ xs : List Int,
  ∀ left right index,
      queryNat (efficientBuild xs) xs.length left right = some index → LeftmostArgMin xs left right index :=
  fun xs => (capstone.queryOnEmitted xs).leftmost

theorem check_queryOnEmitted_result : ∀ xs : List Int,
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result =
        some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  fun xs => (capstone.queryOnEmitted xs).result

theorem check_queryOnEmitted_halt : ∀ xs : List Int,
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).final.status =
        .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  fun xs => (capstone.queryOnEmitted xs).halt

theorem check_queryOnEmitted_invalidGuard : ∀ xs : List Int,
  ∀ left right,
      left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result = some 0 ∧
        (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads = [] :=
  fun xs => (capstone.queryOnEmitted xs).invalidGuard

theorem check_queryOnEmitted_stepBound : ∀ xs : List Int,
  ∀ left right,
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).steps ≤ queryBudget :=
  fun xs => (capstone.queryOnEmitted xs).stepBound

theorem check_queryOnEmitted_categoryPartition : ∀ xs : List Int,
  ∀ left right,
      let actual := PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)
      actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
        actual.categoryCount .arithmetic + actual.categoryCount .comparison +
        actual.categoryCount .branch + actual.categoryCount .control :=
  fun xs => (capstone.queryOnEmitted xs).categoryPartition

theorem check_queryOnEmitted_finalStateFit : ∀ xs : List Int,
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).final.Fits
        (wordWidth xs.length) :=
  fun xs => (capstone.queryOnEmitted xs).finalStateFit

theorem check_queryOnEmitted_transitionSafety : ∀ xs : List Int,
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      ∀ (index : Nat) (t : PackedWordRAM.Transition),
        (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
          some t →
        PackedWordRAM.Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length) :=
  fun xs => (capstone.queryOnEmitted xs).transitionSafety

theorem check_queryOnEmitted_prefixSafety : ∀ xs : List Int,
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      ∀ fuel, fuel ≤ queryBudget →
        (PackedWordRAM.run (efficientBuild xs) queryProgram fuel (PackedWordRAM.initialState xs.length left right)).final.Fits
          (wordWidth xs.length) :=
  fun xs => (capstone.queryOnEmitted xs).prefixSafety

theorem check_queryOnEmitted_readWidth : ∀ xs : List Int,
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      ∀ (index : Nat) (t : PackedWordRAM.Transition) (receipt : Receipt),
        (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
          some t →
        t.receipt = some receipt →
        receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (efficientBuild xs)[receipt.address]? ∧
          (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) :=
  fun xs => (capstone.queryOnEmitted xs).readWidth

theorem check_queryOnEmitted_positionalReadBacking : ∀ xs : List Int,
  ∀ left right index (t : PackedWordRAM.Transition) (receipt : Receipt),
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
        some t →
      t.receipt = some receipt →
      t.before = (PackedWordRAM.run (efficientBuild xs) queryProgram index (PackedWordRAM.initialState xs.length left right)).final ∧
        t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
        PackedWordRAM.execute (efficientBuild xs) t.instruction t.before = (t.after, t.receipt) ∧
        ∃ dst addrReg, t.instruction = .load dst addrReg ∧
          receipt.address = t.before.regs addrReg ∧ receipt.reply = (efficientBuild xs)[receipt.address]? :=
  fun xs => (capstone.queryOnEmitted xs).positionalReadBacking

theorem check_queryOnEmitted_orderedLogicalRefinement : ∀ xs : List Int,
  ∀ left right,
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads =
        if ValidRange xs left right then
          (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
            logicalTraceReads (SuccinctClassic.cartesianShape xs) (efficientBuild xs)
              (SuccinctClassic.queryTraceResult xs left right).trace
        else [] :=
  fun xs => (capstone.queryOnEmitted xs).orderedLogicalRefinement

theorem check_queryOnEmitted_suppliedMemoryAgreement : ∀ xs : List Int,
  ∀ (other : PackedWordRAM.Memory) left right,
      (∀ receipt ∈ (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads,
        other[receipt.address]? = (efficientBuild xs)[receipt.address]?) →
      PackedWordRAM.run other queryProgram queryBudget (PackedWordRAM.initialState xs.length left right) =
        PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right) :=
  fun xs => (capstone.queryOnEmitted xs).suppliedMemoryAgreement

theorem check_queryOnEmitted_specResult : ∀ xs : List Int,
  ∀ left right, ValidRange xs left right →
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result =
        some (scanWindow xs left (right - left) + 1) :=
  fun xs => (capstone.queryOnEmitted xs).specResult

theorem check_queryOnEmitted_noFailedLoads : ∀ xs : List Int,
  ∀ left right, ValidRange xs left right →
      ∀ receipt ∈ (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads,
        ∃ value, receipt.reply = some value :=
  fun xs => (capstone.queryOnEmitted xs).noFailedLoads

theorem check_queryOnEmitted_invalidGuardSteps : ∀ xs : List Int,
  ∀ left right, ¬ ValidRange xs left right →
      (PackedWordRAM.run (efficientBuild xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).steps ≤ 6 :=
  fun xs => (capstone.queryOnEmitted xs).invalidGuardSteps

theorem check_queryOnEmittedWord_dataCapacity : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  (efficientBuildWord (wordWidth xs.length) xs).length * wordWidth xs.length ≤ 2 * xs.length + allocationRho xs.length :=
  fun xs h => (capstone.queryOnEmittedWord xs h).dataCapacity

theorem check_queryOnEmittedWord_completeCapacity : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ((efficientBuildWord (wordWidth xs.length) xs).length + (queryProgram.map PackedWordRAM.Instruction.encoding).flatten.length +
        (queryRegisterCount + 3)) * wordWidth xs.length ≤ 2 * xs.length + queryCompleteRho xs.length :=
  fun xs h => (capstone.queryOnEmittedWord xs h).completeCapacity

theorem check_queryOnEmittedWord_memoryWordsFit : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ word, word ∈ (efficientBuildWord (wordWidth xs.length) xs) → word < 2 ^ wordWidth xs.length :=
  fun xs h => (capstone.queryOnEmittedWord xs h).memoryWordsFit

theorem check_queryOnEmittedWord_allocationAddressesFit : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ address, address ≤ (efficientBuildWord (wordWidth xs.length) xs).length → address < 2 ^ wordWidth xs.length :=
  fun xs h => (capstone.queryOnEmittedWord xs h).allocationAddressesFit

theorem check_queryOnEmittedWord_unusedRegisters : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right fuel r, queryRegisterCount ≤ r →
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram fuel (PackedWordRAM.initialState xs.length left right)).final.regs r = 0 :=
  fun xs h => (capstone.queryOnEmittedWord xs h).unusedRegisters

theorem check_queryOnEmittedWord_natContract : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right,
      queryNat (efficientBuildWord (wordWidth xs.length) xs) xs.length left right =
        if ValidRange xs left right then some (scanWindow xs left (right - left)) else none :=
  fun xs h => (capstone.queryOnEmittedWord xs h).natContract

theorem check_queryOnEmittedWord_leftmost : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right index,
      queryNat (efficientBuildWord (wordWidth xs.length) xs) xs.length left right = some index → LeftmostArgMin xs left right index :=
  fun xs h => (capstone.queryOnEmittedWord xs h).leftmost

theorem check_queryOnEmittedWord_result : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result =
        some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).result

theorem check_queryOnEmittedWord_halt : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).final.status =
        .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).halt

theorem check_queryOnEmittedWord_invalidGuard : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right,
      left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length → ¬ ValidRange xs left right →
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result = some 0 ∧
        (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads = [] :=
  fun xs h => (capstone.queryOnEmittedWord xs h).invalidGuard

theorem check_queryOnEmittedWord_stepBound : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right,
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).steps ≤ queryBudget :=
  fun xs h => (capstone.queryOnEmittedWord xs h).stepBound

theorem check_queryOnEmittedWord_categoryPartition : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right,
      let actual := PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)
      actual.steps = actual.categoryCount .memoryRead + actual.categoryCount .registerWrite +
        actual.categoryCount .arithmetic + actual.categoryCount .comparison +
        actual.categoryCount .branch + actual.categoryCount .control :=
  fun xs h => (capstone.queryOnEmittedWord xs h).categoryPartition

theorem check_queryOnEmittedWord_finalStateFit : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).final.Fits
        (wordWidth xs.length) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).finalStateFit

theorem check_queryOnEmittedWord_transitionSafety : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      ∀ (index : Nat) (t : PackedWordRAM.Transition),
        (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
          some t →
        PackedWordRAM.Instruction.Safe (wordWidth xs.length) t.before t.instruction ∧ t.after.Fits (wordWidth xs.length) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).transitionSafety

theorem check_queryOnEmittedWord_prefixSafety : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      ∀ fuel, fuel ≤ queryBudget →
        (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram fuel (PackedWordRAM.initialState xs.length left right)).final.Fits
          (wordWidth xs.length) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).prefixSafety

theorem check_queryOnEmittedWord_readWidth : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      ∀ (index : Nat) (t : PackedWordRAM.Transition) (receipt : Receipt),
        (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
          some t →
        t.receipt = some receipt →
        receipt.address < 2 ^ wordWidth xs.length ∧ receipt.reply = (efficientBuildWord (wordWidth xs.length) xs)[receipt.address]? ∧
          (∀ value, receipt.reply = some value → value < 2 ^ wordWidth xs.length) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).readWidth

theorem check_queryOnEmittedWord_positionalReadBacking : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right index (t : PackedWordRAM.Transition) (receipt : Receipt),
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).transitions[index]? =
        some t →
      t.receipt = some receipt →
      t.before = (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram index (PackedWordRAM.initialState xs.length left right)).final ∧
        t.before.status = .running ∧ queryProgram[t.before.pc]? = some t.instruction ∧
        PackedWordRAM.execute (efficientBuildWord (wordWidth xs.length) xs) t.instruction t.before = (t.after, t.receipt) ∧
        ∃ dst addrReg, t.instruction = .load dst addrReg ∧
          receipt.address = t.before.regs addrReg ∧ receipt.reply = (efficientBuildWord (wordWidth xs.length) xs)[receipt.address]? :=
  fun xs h => (capstone.queryOnEmittedWord xs h).positionalReadBacking

theorem check_queryOnEmittedWord_orderedLogicalRefinement : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right,
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads =
        if ValidRange xs left right then
          (List.range 174).map (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ++
            logicalTraceReads (SuccinctClassic.cartesianShape xs) (efficientBuildWord (wordWidth xs.length) xs)
              (SuccinctClassic.queryTraceResult xs left right).trace
        else [] :=
  fun xs h => (capstone.queryOnEmittedWord xs h).orderedLogicalRefinement

theorem check_queryOnEmittedWord_suppliedMemoryAgreement : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ (other : PackedWordRAM.Memory) left right,
      (∀ receipt ∈ (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads,
        other[receipt.address]? = (efficientBuildWord (wordWidth xs.length) xs)[receipt.address]?) →
      PackedWordRAM.run other queryProgram queryBudget (PackedWordRAM.initialState xs.length left right) =
        PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).suppliedMemoryAgreement

theorem check_queryOnEmittedWord_specResult : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, ValidRange xs left right →
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).result =
        some (scanWindow xs left (right - left) + 1) :=
  fun xs h => (capstone.queryOnEmittedWord xs h).specResult

theorem check_queryOnEmittedWord_noFailedLoads : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, ValidRange xs left right →
      ∀ receipt ∈ (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).reads,
        ∃ value, receipt.reply = some value :=
  fun xs h => (capstone.queryOnEmittedWord xs h).noFailedLoads

theorem check_queryOnEmittedWord_invalidGuardSteps : ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
  ∀ left right, ¬ ValidRange xs left right →
      (PackedWordRAM.run (efficientBuildWord (wordWidth xs.length) xs) queryProgram queryBudget (PackedWordRAM.initialState xs.length left right)).steps ≤ 6 :=
  fun xs h => (capstone.queryOnEmittedWord xs h).invalidGuardSteps

theorem check_translatedQueryFits :
  ∀ i ∈ queryProgram, i.Fits 32 :=
  capstone.translatedQueryFits

theorem check_translatedQueryRun :
  ∀ (memory : PackedWordRAM.Memory) (fuel : Nat) (s : PackedWordRAM.State),
      (run Conservative.translatedQueryProgram fuel (Conservative.state memory s)).final =
        Conservative.state memory (PackedWordRAM.run memory queryProgram fuel s).final ∧
      (run Conservative.translatedQueryProgram fuel (Conservative.state memory s)).steps =
        (PackedWordRAM.run memory queryProgram fuel s).steps :=
  capstone.translatedQueryRun

theorem check_translatedQueryOnEmitted :
  ∀ (xs : List Int) (left right : Nat),
      left < 2 ^ wordWidth xs.length → right < 2 ^ wordWidth xs.length →
      (run Conservative.translatedQueryProgram queryBudget
          (Conservative.state (efficientBuild xs) (PackedWordRAM.initialState xs.length left right))).final.status =
        .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) ∧
      (run Conservative.translatedQueryProgram queryBudget
          (Conservative.state (efficientBuild xs) (PackedWordRAM.initialState xs.length left right))).steps ≤ queryBudget :=
  capstone.translatedQueryOnEmitted

theorem check_programStatic :
  ∀ n : Nat, ∀ i ∈ builderProgram, i.primitive.OperandsFit (wordWidth n) ∧
      i.primitive.RegistersBelow 400 ∧
      (∀ c t, i.primitive = .branchZero c t → t.val < builderProgram.length) ∧
      (∀ t, i.primitive = .jump t → t.val < builderProgram.length) ∧
      (∀ src, i.primitive ≠ .jumpRegister src) :=
  capstone.programStatic

theorem check_programStaticWord :
  ∀ n : Nat, ∀ i ∈ builderProgramWord, i.primitive.OperandsFit (wordWidth n) ∧
      i.primitive.RegistersBelow 400 ∧
      (∀ c t, i.primitive = .branchZero c t → t.val < builderProgramWord.length) ∧
      (∀ t, i.primitive = .jump t → t.val < builderProgramWord.length) ∧
      (∀ src, i.primitive ≠ .jumpRegister src) :=
  capstone.programStaticWord

#print axioms constructionAndQueryCapstone_holds

/-! ## Axiom inventory of the S7 and S8 producer declarations -/

#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_lit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ptrStep
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ptrFlow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.PtrsAbove
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.StoreAbove
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ptrStep_sound
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EvalG.ptrFlow_sound
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ptrFlow_seq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_header
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_constants
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_geoStep
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_geoChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interiorGeometry
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_geometry
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_arrays
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_stackArrays
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_stackPass_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_stackPass_word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_headerReserve
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_bpEmit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_access_20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_accessHalf
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interior_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_interiorClose
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_microtables
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_headerPatch
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_pad
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_buffer
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_metaStep_all
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_metaChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_emitBit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.filter_ne_ten_of_not_mem
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_emitRegs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_metaEmit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_repack
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_output
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_builderSource_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flow_builderSource_word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Structured.Block.RegsBelow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Structured.Block.compile_regsBelow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Prim.dest_lt_of_registersBelow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_constants
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_geoStep
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_geoChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interiorGeometry
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_geometry
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_arrays
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_stackArrays
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_stackPass_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_stackPass_word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_headerReserve
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_bpEmit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_access_20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_accessHalf
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interior_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_interiorClose
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_microtables
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_headerPatch
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_pad
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_buffer
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_metaStep_all
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_metaChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_emitRegs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_metaEmit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_repack
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_output
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_builderBody_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wo_builderBody_word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_constants
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_geoStep
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_geoChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interiorGeometry
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_geometry
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_arrays
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_stackArrays
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_stackPass_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_stackPass_word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_headerReserve
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_bpEmit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_access_20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_accessHalf
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interior_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_interiorClose
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_microtables
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_headerPatch
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_pad
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_buffer
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_metaStep_all
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_metaChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_emitRegs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_metaWordRegs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_metaEmit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_repack
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_output
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_builderBody_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rb_builderBody_word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.getElem?_lt_of_some
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.write_fold_cell
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.run_last_write
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.StoreAbove.pc_set
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.TransitionShape.left
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.TransitionShape.write_above
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderRun_full
#print axioms RMQ.SuccinctFinal.PackedConstruction.BuilderRunFacts
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.run_extent_le_final
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderRunFacts_of
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_head
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_head
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_tail
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_tail
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.tail_writesOnly_of_body
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_tailNeverWritesR1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_tailNeverWritesR1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_headerUse
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_headerUse
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.registersBelow_of_source
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_registersBelow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_registersBelow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.length_lt_wordWidth
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.comparisonInputState_fits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordInputState_fits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.program_length_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.comparisonRunFacts
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordRunFacts
#print axioms RMQ.SuccinctFinal.PackedConstruction.PackedQueryOn
#print axioms RMQ.SuccinctFinal.PackedConstruction.packedQueryOn_of_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.packedQueryOn_efficientBuild
#print axioms RMQ.SuccinctFinal.PackedConstruction.packedQueryOn_efficientBuildWord
#print axioms RMQ.SuccinctFinal.PackedConstruction.constructionCompleteRho
#print axioms RMQ.SuccinctFinal.PackedConstruction.constructionCompleteRho_littleO
#print axioms RMQ.SuccinctFinal.PackedConstruction.construction_complete_capacity
#print axioms RMQ.SuccinctFinal.PackedConstruction.Conservative.querySource_size_lt32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Conservative.queryProgram_fits32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Conservative.translate
#print axioms RMQ.SuccinctFinal.PackedConstruction.Conservative.translatedQueryProgram
#print axioms RMQ.SuccinctFinal.PackedConstruction.Conservative.translate_of_fits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Conservative.translated_run
#print axioms RMQ.SuccinctFinal.PackedConstruction.ConstructionAndQueryCapstone
#print axioms RMQ.SuccinctFinal.PackedConstruction.translated_status_of
#print axioms RMQ.SuccinctFinal.PackedConstruction.constructionAndQueryCapstone_holds
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderBudget_eq_mul_add
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderSource_size_keyLeaf_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderSource_size_wordLeaf_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderSource_size_keyLeaf
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderSource_size_wordLeaf
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.diffPositionsFrom
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.filter_range'_eq_diffPositionsFrom
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.filter_range_ne_eq_diffPositions
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_length_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_length_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builder_diffPositions_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builder_leaf_difference
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_programWords
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_programWords
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_contract
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_contract
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.fringeOverhead_ge_two
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.two_n_four_lt_cellPow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bankcap_wordWidth
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cap_wordWidth
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.header_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderSource_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderRun_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitted_eq_of_stored
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.run_of_halting
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordWidth_ge_32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.budget_ge
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builder_run_comparison
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.efficientBuild_eq_buildMemory
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.efficientBuildWord_eq_buildMemory
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.keyLeaf_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordLeaf_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cartesianBP_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cartesianBP_word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Structured.Block.compile_targets
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.program_static
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_static
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_static

/-! ## Verdict marker (repair PRE-1-R2 of audit PRE-1-A2 P2-1)

The exit code is the verdict. The marker is printed if and only if (1) the whole
file elaborates with no error-severity message and (2) `consumerWitness`, which
refers to each declaration above, exists and collects no `sorryAx`; otherwise
nothing is printed and no diagnostic is added, so the failing line set of a
rejected mutation stays exactly the lines above. Lean 4.22 resets the command
state's message log before every command (`Lean.Language.Lean.process.doElab`
sets `messages := .empty`), so this command cannot read an earlier command's
errors from its own state. For the whole-file condition it elaborates the file a
second time in this process from the source text of its own input context, with
only this command blanked (line breaks kept), through `Lean.Parser.parseHeader`,
`Lean.Elab.processHeader` and `Lean.Elab.IO.processCommands`, which collects the
message logs of every command snapshot, and requires `MessageLog.hasErrors` to
be false for the header and for those messages: the predicate by which the
frontend decides the exit code. An error in any command kind (a declaration, an
anonymous example, a `#guard` or `run_cmd` check, a missing declaration after a
maximum-recursion-depth failure, or a command after this one) therefore
suppresses the marker. -/

def consumerWitness : Unit :=
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.capstone
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_exactComparison
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_exactWord
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContract_uniform
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContract_lengthPinned
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContract_encodedPinned
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContract_codeBits
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContractWord_uniform
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContractWord_lengthPinned
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContractWord_encodedPinned
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programContractWord_codeBits
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_leafDifference
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_budgetBody
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUse_headerFirst
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUse_tailNeverWritesR1
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUse_wordMissingHeaderFault
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUse_comparisonMissingHeaderFault
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUse_wordHeaderReceipt
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUse_comparisonHeaderReceipt
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUse_oracleExtentOne
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUseWord_headerFirst
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUseWord_tailNeverWritesR1
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUseWord_wordMissingHeaderFault
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUseWord_comparisonMissingHeaderFault
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUseWord_wordHeaderReceipt
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUseWord_comparisonHeaderReceipt
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_headerUseWord_oracleExtentOne
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonInput
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordInput
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_zeroFamily
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_halts
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_work
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_fuelInsensitive
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_categoryPartition
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_outputCells
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_outputProvenance
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_workspace
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_peakExtent
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_prefixExtent
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_registerBank
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_initialFits
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_runSafe
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_finalFits
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_noInputWrites
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_inputRetained
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_replay
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_cleanTail
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_readAgreement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_suppliedAgreement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_comparisonRun_arrayReflects
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_halts
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_work
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_fuelInsensitive
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_categoryPartition
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_outputCells
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_outputProvenance
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_workspace
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_peakExtent
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_prefixExtent
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_registerBank
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_initialFits
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_runSafe
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_finalFits
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_noInputWrites
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_inputRetained
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_replay
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_cleanTail
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_readAgreement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_suppliedAgreement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_wordRun_arrayReflects
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_jointResidualLittleO
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_jointCapacity
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryCapstone
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_dataCapacity
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_completeCapacity
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_memoryWordsFit
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_allocationAddressesFit
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_unusedRegisters
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_natContract
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_leftmost
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_result
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_halt
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_invalidGuard
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_stepBound
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_categoryPartition
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_finalStateFit
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_transitionSafety
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_prefixSafety
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_readWidth
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_positionalReadBacking
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_orderedLogicalRefinement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_suppliedMemoryAgreement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_specResult
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_noFailedLoads
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmitted_invalidGuardSteps
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_dataCapacity
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_completeCapacity
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_memoryWordsFit
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_allocationAddressesFit
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_unusedRegisters
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_natContract
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_leftmost
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_result
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_halt
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_invalidGuard
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_stepBound
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_categoryPartition
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_finalStateFit
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_transitionSafety
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_prefixSafety
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_readWidth
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_positionalReadBacking
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_orderedLogicalRefinement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_suppliedMemoryAgreement
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_specResult
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_noFailedLoads
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_queryOnEmittedWord_invalidGuardSteps
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_translatedQueryFits
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_translatedQueryRun
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_translatedQueryOnEmitted
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programStatic
  let _ := @RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.check_programStaticWord
  ()

open Lean Elab Command in
#eval show CommandElabM Unit from do
  -- (1) Whole file: elaborate this file again in this process from its own
  -- source text, with only this command blanked (line breaks kept), and read
  -- the message log of the header and of every command.
  let context ← read
  let source := context.fileMap.source
  let scope ← getScope
  let markerStop := (Parser.parseCommand (Parser.mkInputContext source context.fileName)
    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls } { pos := context.cmdPos } {}).2.1.pos
  let blank := (source.extract context.cmdPos markerStop).map
    fun c => if c == '\n' || c == '\r' then c else ' '
  let input := Parser.mkInputContext
    (source.extract 0 context.cmdPos ++ blank ++ source.extract markerStop source.endPos)
    context.fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader input
  let options := Elab.async.setIfNotSet (internal.cmdlineSnapshots.setIfNotSet {} true) true
  let (headerEnv, headerMessages) ← processHeader header options headerMessages input
    (trustLevel := (← getEnv).header.trustLevel) (leakEnv := true)
    (mainModule := (← getEnv).mainModule)
  let whole ← IO.processCommands input parserState (Command.mkState headerEnv {} options)
  let fileClean := !headerMessages.hasErrors && !whole.commandState.messages.hasErrors
  -- (2) The witness exists and collects no `sorryAx`.
  let witness := `RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks.consumerWitness
  let witnessClean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  if fileClean && witnessClean then IO.println "PRE1-CAPSTONE-TYPED-CONSUMERS PASS"

end RMQ.SuccinctFinal.PackedConstruction.CapstoneChecks
