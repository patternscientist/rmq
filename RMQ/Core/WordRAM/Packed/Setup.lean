import RMQ.Core.WordRAM.Packed.Width
import RMQ.Core.WordRAM.Packed.Compiler

/-!+# Charged loading of the fixed metadata bank

The setup source contains 174 constant/load pairs. Each destination receives
its own raw physical reply. The compiler theorem supplies actual instruction
execution; the source evaluator supplies only its compositional specification.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian PackedCellProbe Structured

def metadataLoadPair (index : Nat) : Block :=
  .seq (.action (.constant 6 index)) (.action (.load (16 + index) 6))

def metadataSetupFrom (start : Nat) : Nat → Block
  | 0 => .skip
  | count + 1 => .seq (metadataLoadPair start) (metadataSetupFrom (start + 1) count)

/-- One fixed source term, independent of the data and query endpoints. -/
def metadataSetupBlock : Block := metadataSetupFrom 0 174

theorem metadataSetupFrom_size (start count : Nat) :
    (metadataSetupFrom start count).size = 2 * count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp [metadataSetupFrom, metadataLoadPair, Block.size, ih]
      omega

theorem metadataSetupBlock_size : metadataSetupBlock.size = 348 :=
  metadataSetupFrom_size 0 174

theorem metadataSetupFrom_compile (start count base : Nat) :
    (metadataSetupFrom start count).compileAt base =
      ((List.range count).map fun i =>
        [Instruction.constant 6 (start + i), Instruction.load (16 + (start + i)) 6]).flatten := by
  induction count generalizing start base with
  | zero => rfl
  | succ count ih =>
      simp [metadataSetupFrom, metadataLoadPair, Block.compileAt, Action.instruction,
        Block.size, ih, List.range_succ_eq_map, List.map_map,
        Function.comp_def, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The emitted code contains exactly the advertised constant/load pairs. -/
theorem metadataSetupBlock_compile (base : Nat) :
    metadataSetupBlock.compileAt base =
      ((List.range 174).map fun i =>
        [Instruction.constant 6 i, Instruction.load (16 + i) 6]).flatten := by
  simpa [metadataSetupBlock] using metadataSetupFrom_compile 0 174 base

private theorem metadataLoadPair_eval (memory : Memory) (index value : Nat)
    (s : Data) (hs : s.status = .running)
    (hget : memory[index]? = some value) :
    (metadataLoadPair index).eval memory s =
      ⟨⟨(s.regs.write 6 index).write (16 + index) value, .running⟩,
        [⟨index, some value⟩]⟩ := by
  simp [metadataLoadPair, Block.eval, hs, Action.eval, Action.instruction,
    execute, State.writeNext, Data.ofState, hget]

/-- Generic prefix loading retains actual memory values, receipt order and frame. -/
theorem metadataSetupFrom_eval (memory : Memory) (start count : Nat)
    (s : Data) (hs : s.status = .running) (hmem : start + count ≤ memory.length) :
    let actual := (metadataSetupFrom start count).eval memory s
    actual.final.status = .running ∧
    (∀ i < count, actual.final.regs (16 + (start + i)) = (memory[start + i]?).getD 0) ∧
    (0 < count → actual.final.regs 6 = start + count - 1) ∧
    (∀ r, r ≠ 6 → (r < 16 + start ∨ 16 + start + count ≤ r) →
      actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range count).map (fun i => ⟨start + i, memory[start + i]?⟩) := by
  induction count generalizing start s with
  | zero =>
      simp [metadataSetupFrom, Block.eval, hs]
  | succ count ih =>
      have hindex : start < memory.length := by omega
      let value := (memory[start]?).getD 0
      have hget : memory[start]? = some value := by
        simp [value, List.getElem?_eq_getElem hindex]
      let loaded : Data := ⟨(s.regs.write 6 start).write (16 + start) value, .running⟩
      have ht := ih (start + 1) loaded rfl (by omega)
      let tail := (metadataSetupFrom (start + 1) count).eval memory loaded
      have heval : (metadataSetupFrom start (count + 1)).eval memory s =
          ⟨tail.final, ⟨start, some value⟩ :: tail.reads⟩ := by
        rw [metadataSetupFrom, Block.eval_seq,
          metadataLoadPair_eval memory start value s hs hget]
        rfl
      rw [heval]
      dsimp only
      refine ⟨ht.1, ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hz : i = 0
        · subst i
          have hf := ht.2.2.2.1 (16 + start) (by omega) (Or.inl (by omega))
          simpa [loaded, value, tail] using hf
        · have hh := ht.2.1 (i - 1) (by omega)
          have heq : start + 1 + (i - 1) = start + i := by omega
          simpa [tail, heq] using hh
      · intro _
        by_cases hc : count = 0
        · subst count
          have hne : 6 ≠ 16 + start := by omega
          simp [tail, metadataSetupFrom, Block.eval, loaded, Registers.write, hne]
        · have hh := ht.2.2.1 (by omega)
          have heq : start + 1 + count - 1 = start + (count + 1) - 1 := by omega
          simpa only [tail, heq] using hh
      · intro r h6 hr
        have htframe := ht.2.2.2.1 r h6 (by omega)
        have hd : r ≠ 16 + start := by omega
        simpa [tail, loaded, Registers.write, h6, hd] using htframe
      · rw [ht.2.2.2.2]
        simp [List.range_succ_eq_map, List.map_map, Function.comp_def,
          Nat.add_left_comm, Nat.add_comm, hget]

theorem metadataSetupBlock_eval (memory : Memory) (s : Data)
    (hs : s.status = .running) (hmem : 174 ≤ memory.length) :
    let actual := metadataSetupBlock.eval memory s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) = (memory[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map (fun i => ⟨i, memory[i]?⟩) := by
  have h := metadataSetupFrom_eval memory 0 174 s hs (by simpa using hmem)
  simpa [metadataSetupBlock] using h

theorem shapeMemory_metadata_prefix (shape : CartesianShape) (i : Nat) (hi : i < 174) :
    (shapeMemory shape)[i]? = (metadata shape)[i]? := by
  apply List.getElem?_append_left
  rw [metadata_length]
  exact hi

theorem buildMemory_metadata_prefix (xs : List Int) (i : Nat) (hi : i < 174) :
    (buildMemory xs)[i]? = (metadata (SuccinctClassic.cartesianShape xs))[i]? :=
  shapeMemory_metadata_prefix _ i hi

theorem shapeMemory_metadata_length_le (shape : CartesianShape) :
    174 ≤ (shapeMemory shape).length := by
  simp only [shapeMemory, repackWords, List.length_append, metadata_length,
    metadataWordCount]
  omega

theorem shapeMemory_setup (shape : CartesianShape) (s : Data)
    (hs : s.status = .running) :
    let actual := metadataSetupBlock.eval (shapeMemory shape) s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) = ((metadata shape)[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) := by
  have h := metadataSetupBlock_eval (shapeMemory shape) s hs (shapeMemory_metadata_length_le shape)
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, ?_⟩
  · intro i hi
    rw [h.2.1 i hi, shapeMemory_metadata_prefix shape i hi]
  · rw [h.2.2.2.2]
    apply List.map_congr_left
    intro i hi
    rw [shapeMemory_metadata_prefix shape i (List.mem_range.mp hi)]

theorem buildMemory_setup (xs : List Int) (s : Data) (hs : s.status = .running) :
    let actual := metadataSetupBlock.eval (buildMemory xs) s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) =
      ((metadata (SuccinctClassic.cartesianShape xs))[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map
      (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) :=
  shapeMemory_setup _ s hs

private theorem smallConstant_lt_capacity (n : Nat) : 348 < 2 ^ wordWidth n := by
  apply Nat.lt_of_lt_of_le (show 348 < 2 ^ 32 by decide)
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  unfold wordWidth
  omega

private theorem metadataSetupFrom_fieldsFit (start count n : Nat)
    (hbound : start + count ≤ 174) : (metadataSetupFrom start count).FieldsFit (wordWidth n) := by
  induction count generalizing start with
  | zero => trivial
  | succ count ih =>
      have hcap := smallConstant_lt_capacity n
      have hw := wordWidth_pos n
      refine ⟨?_, ih (start + 1) (by omega)⟩
      simp [metadataLoadPair, Block.FieldsFit, Action.instruction,
        Instruction.Fits, Instruction.encoding, Instruction.operands]
      omega

theorem metadataSetupBlock_fieldsFit (n : Nat) :
    metadataSetupBlock.FieldsFit (wordWidth n) := metadataSetupFrom_fieldsFit 0 174 n (by omega)

theorem metadataSetupBlock_compiled_fieldsFit (n base : Nat) :
    ∀ instruction ∈ metadataSetupBlock.compileAt base, instruction.Fits (wordWidth n) := by
  have h := metadataSetupBlock.compile_fits (wordWidth n) 0
    (metadataSetupBlock_fieldsFit n) (by rw [Nat.zero_add, metadataSetupBlock_size]; exact smallConstant_lt_capacity n)
  simpa only [metadataSetupBlock_compile] using h

theorem shapeMemory_setup_registers_fit (shape : CartesianShape) (s : Data)
    (hs : s.status = .running) (hregs : ∀ r, s.regs r < 2 ^ wordWidth shape.size) :
    ∀ r, (metadataSetupBlock.eval (shapeMemory shape) s).final.regs r <
      2 ^ wordWidth shape.size := by
  have h := metadataSetupBlock_eval (shapeMemory shape) s hs (shapeMemory_metadata_length_le shape)
  intro r
  by_cases h6 : r = 6
  · subst r
    rw [h.2.2.1]
    have := smallConstant_lt_capacity shape.size
    omega
  · by_cases hr : r < 16 ∨ 190 ≤ r
    · rw [h.2.2.2.1 r h6 hr]
      exact hregs r
    · have hi : r - 16 < 174 := by omega
      have heq : 16 + (r - 16) = r := by omega
      have hindex : r - 16 < (shapeMemory shape).length := by
        have := shapeMemory_metadata_length_le shape
        omega
      have hv := shapeMemory_words_fit shape ((shapeMemory shape)[r - 16]) (List.getElem_mem hindex)
      have hfield := h.2.1 (r - 16) hi
      rw [heq] at hfield
      rw [hfield]
      simpa only [List.getElem?_eq_getElem hindex, Option.getD_some] using hv

theorem buildMemory_setup_registers_fit (xs : List Int) (s : Data)
    (hs : s.status = .running) (hregs : ∀ r, s.regs r < 2 ^ wordWidth xs.length) :
    ∀ r, (metadataSetupBlock.eval (buildMemory xs) s).final.regs r <
      2 ^ wordWidth xs.length := by
  have h := shapeMemory_setup_registers_fit (SuccinctClassic.cartesianShape xs) s hs
    (by simpa only [packedReviewerCartesianShape_size] using hregs)
  simpa only [buildMemory, packedReviewerCartesianShape_size] using h

theorem metadataSetupBlock_run (memory : Memory) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running) (hmem : 174 ≤ memory.length) :
    let actual := run memory (metadataSetupBlock.compileAt 0) 348 s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) = (memory[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map (fun i => ⟨i, memory[i]?⟩) ∧
    actual.steps ≤ 348 ∧ actual.final.pc = 348 := by
  have hc := metadataSetupBlock.compile_run memory s hpc
  rw [metadataSetupBlock_size] at hc
  have he := metadataSetupBlock_eval memory (Data.ofState s) hs hmem
  have hstatus : (run memory (metadataSetupBlock.compileAt 0) 348 s).final.status = .running := by
    change (Data.ofState _).status = _
    rw [hc.1]
    exact he.1
  refine ⟨hstatus, ?_, ?_, ?_, ?_, hc.2.2.1, hc.2.2.2 hstatus⟩
  · intro i hi
    change (Data.ofState _).regs _ = _
    rw [hc.1]
    exact he.2.1 i hi
  · change (Data.ofState _).regs 6 = _
    rw [hc.1]
    exact he.2.2.1
  · intro r h6 hr
    change (Data.ofState _).regs _ = _
    rw [hc.1]
    exact he.2.2.2.1 r h6 hr
  · rw [hc.2.1]
    exact he.2.2.2.2

/-- Arbitrary code placement, consumed through the actual hosted compiler run. -/
theorem metadataSetupBlock_hosted_run (memory : Memory) (program : Program)
    (base : Nat) (s : State) (hpc : s.pc = base) (hs : s.status = .running)
    (hmem : 174 ≤ memory.length)
    (host : HostedAt program base (metadataSetupBlock.compileAt base)) :
    ∃ used, used ≤ 348 ∧
      let actual := run memory program used s
      actual.final.status = .running ∧
      (∀ i < 174, actual.final.regs (16 + i) = (memory[i]?).getD 0) ∧
      actual.final.regs 6 = 173 ∧
      (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
      actual.reads = (List.range 174).map (fun i => ⟨i, memory[i]?⟩) ∧
      actual.steps = used ∧ actual.final.pc = base + 348 := by
  obtain ⟨used, hu, hd, hr, hc, hp⟩ :=
    metadataSetupBlock.compile_correct memory program base s hpc host
  rw [metadataSetupBlock_size] at hu hp
  have he := metadataSetupBlock_eval memory (Data.ofState s) hs hmem
  have hstatus : (run memory program used s).final.status = .running := by
    change (Data.ofState _).status = _
    rw [hd]
    exact he.1
  refine ⟨used, hu, hstatus, ?_, ?_, ?_, ?_, hc, hp hstatus⟩
  · intro i hi
    change (Data.ofState _).regs _ = _
    rw [hd]
    exact he.2.1 i hi
  · change (Data.ofState _).regs 6 = _
    rw [hd]
    exact he.2.2.1
  · intro r h6 hframe
    change (Data.ofState _).regs _ = _
    rw [hd]
    exact he.2.2.2.1 r h6 hframe
  · rw [hr]
    exact he.2.2.2.2

/-- Canonical metadata, all-register fit and instruction budget concern one run. -/
theorem buildMemory_setup_run (xs : List Int) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running)
    (hregs : ∀ r, s.regs r < 2 ^ wordWidth xs.length) :
    let actual := run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) =
      ((metadata (SuccinctClassic.cartesianShape xs))[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map
      (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ∧
    actual.steps ≤ 348 ∧ actual.final.pc = 348 ∧
    (∀ r, actual.final.regs r < 2 ^ wordWidth xs.length) := by
  have h := metadataSetupBlock_run (buildMemory xs) s hpc hs
    (shapeMemory_metadata_length_le _)
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2, ?_⟩
  · intro i hi
    rw [h.2.1 i hi, buildMemory_metadata_prefix xs i hi]
  · rw [h.2.2.2.2.1]
    apply List.map_congr_left
    intro i hi
    rw [buildMemory_metadata_prefix xs i (List.mem_range.mp hi)]
  · have he := metadataSetupBlock.compile_run (buildMemory xs) s hpc
    rw [metadataSetupBlock_size] at he
    intro r
    change (Data.ofState _).regs r < _
    rw [he.1]
    exact buildMemory_setup_registers_fit xs (Data.ofState s) hs hregs r

theorem buildMemory_setup_hosted_run (xs : List Int) (program : Program)
    (base : Nat) (s : State) (hpc : s.pc = base) (hs : s.status = .running)
    (hregs : ∀ r, s.regs r < 2 ^ wordWidth xs.length)
    (host : HostedAt program base (metadataSetupBlock.compileAt base)) :
    ∃ used, used ≤ 348 ∧
      let actual := run (buildMemory xs) program used s
      actual.final.status = .running ∧
      (∀ i < 174, actual.final.regs (16 + i) =
        ((metadata (SuccinctClassic.cartesianShape xs))[i]?).getD 0) ∧
      actual.final.regs 6 = 173 ∧
      (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
      actual.reads = (List.range 174).map
        (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ∧
      actual.steps = used ∧ actual.final.pc = base + 348 ∧
      (∀ r, actual.final.regs r < 2 ^ wordWidth xs.length) := by
  obtain ⟨used, hu, hd, hr, hc, hp⟩ :=
    metadataSetupBlock.compile_correct (buildMemory xs) program base s hpc host
  rw [metadataSetupBlock_size] at hu hp
  have he := buildMemory_setup xs (Data.ofState s) hs
  have hstatus : (run (buildMemory xs) program used s).final.status = .running := by
    change (Data.ofState _).status = _
    rw [hd]
    exact he.1
  refine ⟨used, hu, hstatus, ?_, ?_, ?_, ?_, hc, hp hstatus, ?_⟩
  · intro i hi
    change (Data.ofState _).regs _ = _
    rw [hd]
    exact he.2.1 i hi
  · change (Data.ofState _).regs 6 = _
    rw [hd]
    exact he.2.2.1
  · intro r h6 hframe
    change (Data.ofState _).regs _ = _
    rw [hd]
    exact he.2.2.2.1 r h6 hframe
  · rw [hr]
    exact he.2.2.2.2
  · intro r
    change (Data.ofState _).regs r < _
    rw [hd]
    exact buildMemory_setup_registers_fit xs (Data.ofState s) hs hregs r

/-- Indexed receipt backing and the installed value share the same physical slot. -/
theorem metadataSetupBlock_run_field_receipt (memory : Memory) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running) (hmem : 174 ≤ memory.length)
    (i : Nat) (hi : i < 174) :
    let actual := run memory (metadataSetupBlock.compileAt 0) 348 s
    actual.final.regs (16 + i) = (memory[i]?).getD 0 ∧
    actual.reads[i]? = some ⟨i, memory[i]?⟩ := by
  have h := metadataSetupBlock_run memory s hpc hs hmem
  refine ⟨h.2.1 i hi, ?_⟩
  rw [h.2.2.2.2.1]
  simp [hi]

/-- A changed loaded value changes the actual destination, even with the same
initial registers. This challenges value projection rather than just read logs. -/
theorem metadataSetupBlock_run_value_dependency (first second : Memory) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running)
    (hfirst : 174 ≤ first.length) (hsecond : 174 ≤ second.length)
    (i : Nat) (hi : i < 174)
    (hvalue : (first[i]?).getD 0 ≠ (second[i]?).getD 0) :
    (run first (metadataSetupBlock.compileAt 0) 348 s).final.regs (16 + i) ≠
      (run second (metadataSetupBlock.compileAt 0) 348 s).final.regs (16 + i) := by
  rw [(metadataSetupBlock_run first s hpc hs hfirst).2.1 i hi,
    (metadataSetupBlock_run second s hpc hs hsecond).2.1 i hi]
  exact hvalue

/-- Independent exact-type consumer of the full canonical source theorem. -/
theorem setup_source_requiredFacts (xs : List Int) (s : Data) (hs : s.status = .running) :
    let actual := metadataSetupBlock.eval (buildMemory xs) s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) =
      ((metadata (SuccinctClassic.cartesianShape xs))[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map
      (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) :=
  buildMemory_setup xs s hs

/-- Independent exact-type consumer of the full canonical primitive theorem. -/
theorem setup_run_requiredFacts (xs : List Int) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running)
    (hregs : ∀ r, s.regs r < 2 ^ wordWidth xs.length) :
    let actual := run (buildMemory xs) (metadataSetupBlock.compileAt 0) 348 s
    actual.final.status = .running ∧
    (∀ i < 174, actual.final.regs (16 + i) =
      ((metadata (SuccinctClassic.cartesianShape xs))[i]?).getD 0) ∧
    actual.final.regs 6 = 173 ∧
    (∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → actual.final.regs r = s.regs r) ∧
    actual.reads = (List.range 174).map
      (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ∧
    actual.steps ≤ 348 ∧ actual.final.pc = 348 ∧
    (∀ r, actual.final.regs r < 2 ^ wordWidth xs.length) :=
  buildMemory_setup_run xs s hpc hs hregs

example : (metadataSetupBlock.eval (buildMemory []) ⟨fun _ => 0, .running⟩).final.status =
    .running := (buildMemory_setup [] _ rfl).1

example (value : Int) :
    (run (buildMemory [value]) (metadataSetupBlock.compileAt 0) 348
      ⟨fun _ => 0, 0, .running⟩).final.pc = 348 := by
  have h := buildMemory_setup_run [value] ⟨fun _ => 0, 0, .running⟩ rfl rfl
    (by intro r; exact Nat.two_pow_pos _)
  exact h.2.2.2.2.2.2.1

end RMQ.SuccinctFinal.PackedWordRAM
