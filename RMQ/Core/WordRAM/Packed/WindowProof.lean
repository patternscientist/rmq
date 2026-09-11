import RMQ.Core.WordRAM.Packed.FringeSource
import RMQ.Core.WordRAM.Packed.ReadInterface
import RMQ.Core.WordRAM.Packed.PhysicalRead

/-! # The four charged reads that produce the fringe window

Each reply contributes its actual bits and length, including absent and empty
replies. The interpreter computes the numeric concatenation from these reads.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

private theorem eval_move (memory : Memory) (regs : Registers) (dst src : Nat) :
    (Block.action (.move dst src)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (regs src), .running⟩, []⟩ := rfl

private theorem eval_constant (memory : Memory) (regs : Registers) (dst value : Nat) :
    (Block.action (.constant dst value)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst value, .running⟩, []⟩ := rfl

private theorem eval_arithmetic (memory : Memory) (regs : Registers)
    (op : Arithmetic) (dst lhs rhs : Nat) :
    (Block.action (.arithmetic op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_skip (memory : Memory) (regs : Registers) :
    Block.skip.eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := rfl

private theorem data_eq_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

def WindowPartWrites (part r : Nat) : Prop :=
  r = 1027 ∨ r = 1028 ∨ r = 1056 + part ∨ r = 1060 + part ∨ (8192 ≤ r ∧ r < 8271)

theorem loadWindowPart_writes (reader : Block) (hr : ReaderWrites reader) (part : Nat) :
    (loadWindowPart reader part).WritesOnly (WindowPartWrites part) := by
  have hreader : reader.WritesOnly (WindowPartWrites part) :=
    Block.WritesOnly.mono reader hr (by intro r h; unfold WindowPartWrites; omega)
  simpa [loadWindowPart, Block.sequence, Block.WritesOnly, Action.destination,
    WindowPartWrites, natSubBlock] using hreader

theorem loadWindowPart_frame (reader : Block) (hr : ReaderWrites reader)
    (part : Nat) (memory : Memory) (s : Data) (r : Nat) (outside : ¬ WindowPartWrites part r) :
    ((loadWindowPart reader part).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (loadWindowPart_writes reader hr part) r outside s

theorem loadWindowPart_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (part : Nat) (hp : part < 4)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1026 = 1) :
    let actual := (loadWindowPart reader part).eval memory ⟨regs, .running⟩
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 (regs 1025 + part)
    actual.final.status = .running ∧
      actual.final.regs (1056 + part) = bitsToNatLE (expected.getD []) ∧
      actual.final.regs (1060 + part) = (expected.getD []).length ∧
      actual.reads = readerReceipts shape memory 0 (regs 1025 + part) := by
  let prepared := ((regs.write 1028 part).write 8193 (regs 1025 + part)).write 8192 0
  have hmeta : MetadataMatches shape prepared := by
    apply MetadataMatches.write shape _ _ 8192 0 (Or.inr (by decide))
    apply MetadataMatches.write shape _ _ 8193 _ (Or.inr (by decide))
    exact MetadataMatches.write shape regs hm 1028 part (Or.inr (by decide))
  have h := hreader prepared hmeta
  generalize he : reader.eval memory ⟨prepared, .running⟩ = loaded at h
  rcases loaded with ⟨⟨out, status⟩, reads⟩
  dsimp only at h
  obtain ⟨hstatus, hpacket, hlength, hreads, hframe⟩ := h
  subst status
  have hone' := hframe 1026 (Or.inl (by decide))
  simp [prepared, Registers.write, hone] at he hpacket hlength hreads hone'
  have hsub := natSubBlock_source (1056 + part) 8194 1026 1027 memory out
    (by decide) (by decide)
  have hn1 : 8195 ≠ 1056 + part := by omega
  have hpval (word : Option (List Bool)) : logicalPacket word - 1 = bitsToNatLE (word.getD []) := by
    cases word <;> simp [logicalPacket, bitsToNatLE]
  have hplen (word : Option (List Bool)) : logicalLength word = (word.getD []).length := by
    cases word <;> rfl
  simp [loadWindowPart, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
    eval_arithmetic, eval_move, eval_skip, Arithmetic.eval, Registers.write, he,
    hsub, hn1, hone', hpacket, hlength, hreads, hpval, hplen]

def WindowPartsWrites (part count r : Nat) : Prop :=
  r = 1027 ∨ r = 1028 ∨
  (1056 + part ≤ r ∧ r < 1056 + part + count) ∨
  (1060 + part ≤ r ∧ r < 1060 + part + count) ∨ (8192 ≤ r ∧ r < 8271)

theorem loadWindowParts_writes (reader : Block) (hr : ReaderWrites reader) (part count : Nat) :
    (loadWindowParts reader part count).WritesOnly (WindowPartsWrites part count) := by
  induction count generalizing part with
  | zero => trivial
  | succ count ih =>
    refine ⟨Block.WritesOnly.mono _ (loadWindowPart_writes reader hr part) ?_,
      Block.WritesOnly.mono _ (ih (part + 1)) ?_⟩
    all_goals intro r h; simp only [WindowPartsWrites, WindowPartWrites] at *; omega

theorem loadWindowParts_frame (reader : Block) (hr : ReaderWrites reader)
    (part count : Nat) (memory : Memory) (s : Data) (r : Nat)
    (outside : ¬ WindowPartsWrites part count r) :
    ((loadWindowParts reader part count).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (loadWindowParts_writes reader hr part count) r outside s

def windowPartsReceipts (shape : CartesianShape) (memory : Memory) (first part : Nat) :
    Nat → List Receipt
  | 0 => []
  | count + 1 => readerReceipts shape memory 0 (first + part) ++
      windowPartsReceipts shape memory first (part + 1) count

theorem loadWindowParts_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (part count : Nat) (hp : part + count ≤ 4)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1026 = 1) :
    let actual := (loadWindowParts reader part count).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      (∀ j < count, let expected :=
          (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 0 (regs 1025 + (part + j))
        actual.final.regs (1056 + (part + j)) = bitsToNatLE (expected.getD []) ∧
        actual.final.regs (1060 + (part + j)) = (expected.getD []).length) ∧
      actual.reads = windowPartsReceipts shape memory (regs 1025) part count := by
  induction count generalizing part regs with
  | zero => simp [loadWindowParts, eval_skip, windowPartsReceipts]
  | succ count ih =>
    have hs := loadWindowPart_source shape memory reader hreader part (by omega) regs hm hone
    let middle := ((loadWindowPart reader part).eval memory ⟨regs, .running⟩).final
    have hmid : middle = ⟨middle.regs, .running⟩ := data_eq_running middle hs.1
    have hf (r : Nat) (outside : ¬ WindowPartWrites part r) : middle.regs r = regs r :=
      loadWindowPart_frame reader hwrites part memory _ r outside
    have hm' : MetadataMatches shape middle.regs := by
      intro i hi
      rw [hf _ (by unfold WindowPartWrites; omega)]
      exact hm i hi
    have ho' : middle.regs 1026 = 1 := (hf _ (by unfold WindowPartWrites; omega)).trans hone
    have hfirst : middle.regs 1025 = regs 1025 := hf _ (by unfold WindowPartWrites; omega)
    have ht := ih (part + 1) (by omega) middle.regs hm' ho'
    have hkeep0 := loadWindowParts_frame reader hwrites (part + 1) count memory
      ⟨middle.regs, .running⟩ (1056 + part) (by unfold WindowPartsWrites; omega)
    have hkeep1 := loadWindowParts_frame reader hwrites (part + 1) count memory
      ⟨middle.regs, .running⟩ (1060 + part) (by unfold WindowPartsWrites; omega)
    dsimp only at hs ht ⊢
    simp only [loadWindowParts, Block.eval_seq, Evaluation.bind]
    change _ ∧ (∀ j < count + 1, _) ∧ _
    rw [show ((loadWindowPart reader part).eval memory ⟨regs, .running⟩).final =
      ⟨middle.regs, .running⟩ from hmid]
    refine ⟨ht.1, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        simpa only [Nat.add_zero] using And.intro (hkeep0.trans hs.2.1) (hkeep1.trans hs.2.2.1)
      | succ j =>
        simpa only [hfirst, Nat.add_assoc, Nat.add_comm 1 j] using ht.2.1 j (by omega)
    · rw [hs.2.2.2, ht.2.2, hfirst]
      rfl

def windowFirstWord (regs : Registers) : Nat := regs 1024 / regs 33 * regs 33 / regs 32

theorem loadWindowInit_source (memory : Memory) (regs : Registers) :
    loadWindowInit.eval memory ⟨regs, .running⟩ =
      ⟨⟨(regs.write 1026 1).write 1025 (windowFirstWord regs), .running⟩, []⟩ := by
  simp [loadWindowInit, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_constant, eval_arithmetic, eval_skip, Registers.write, Arithmetic.eval, windowFirstWord]
  funext r
  by_cases h : r = 1025 <;> simp [Registers.write, h]

def WindowWrites (r : Nat) : Prop :=
  (1025 ≤ r ∧ r < 1029) ∨ (1056 ≤ r ∧ r < 1065) ∨ (8192 ≤ r ∧ r < 8271)

theorem loadWindowBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (loadWindowBlock reader).WritesOnly WindowWrites := by
  have hparts : (loadWindowParts reader 0 4).WritesOnly WindowWrites :=
    Block.WritesOnly.mono _ (loadWindowParts_writes reader hr 0 4)
      (by intro r h; unfold WindowWrites WindowPartsWrites at *; omega)
  simpa [loadWindowBlock, loadWindowInit, raggedWindowBlock, Block.sequence,
    Block.WritesOnly, Action.destination, WindowWrites] using hparts

theorem loadWindowBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ WindowWrites r) :
    ((loadWindowBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (loadWindowBlock_writes reader hr) r outside s

theorem loadWindowBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((loadWindowBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [loadWindowBlock_frame reader hr memory s (16 + i) (by unfold WindowWrites; omega)]
  exact hm i hi

def windowReadBits (store : WordRAM.ReadStore) (first : Nat) : List Bool :=
  (store.readWord? 0 first).getD [] ++ (store.readWord? 0 (first + 1)).getD [] ++
    (store.readWord? 0 (first + 2)).getD [] ++ (store.readWord? 0 (first + 3)).getD []

theorem loadWindowBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let actual := (loadWindowBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      actual.final.regs 1064 = bitsToNatLE (windowReadBits
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) (windowFirstWord regs)) ∧
      actual.reads = windowPartsReceipts shape memory (windowFirstWord regs) 0 4 := by
  let prepared := (regs.write 1026 1).write 1025 (windowFirstWord regs)
  have hm' : MetadataMatches shape prepared :=
    MetadataMatches.write shape _
      (MetadataMatches.write shape regs hm 1026 1 (Or.inr (by decide)))
      1025 _ (Or.inr (by decide))
  have hs := loadWindowParts_source shape memory reader hreader hwrites 0 4 (by decide)
    prepared hm' (by simp [prepared, Registers.write])
  generalize he : (loadWindowParts reader 0 4).eval memory ⟨prepared, .running⟩ = parts at hs
  rcases parts with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨hstatus, hwords, hreads⟩ := hs
  subst status
  have h0 := hwords 0 (by decide)
  have h1 := hwords 1 (by decide)
  have h2 := hwords 2 (by decide)
  have h3 := hwords 3 (by decide)
  simp only [prepared, Registers.write, ite_true, Nat.zero_add, Nat.add_zero] at h0 h1 h2 h3 hreads
  have hv := raggedWindowBlock_source 1056 memory out
  have hval := hv.2.2.1
  rw [h0.1, h1.1, h2.1, h3.1, h0.2, h1.2, h2.2, raggedWindowValue_eq_bits] at hval
  have hwhole := hv.1
  have hr := hv.2.1
  generalize hew : (raggedWindowBlock 1056).eval memory ⟨out, .running⟩ = window at hval hwhole hr
  rcases window with ⟨⟨outw, statusw⟩, readsw⟩
  dsimp only at hval hwhole hr
  subst statusw
  subst readsw
  simp [loadWindowBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
    loadWindowInit_source, eval_skip, he, hew, hval, hreads, windowReadBits, prepared]

@[simp] theorem loadWindowPart_size (reader : Block) (part : Nat) :
    (loadWindowPart reader part).size = 9 + reader.size := by
  simp [loadWindowPart, Block.sequence, Block.size, natSubBlock]
  omega

@[simp] theorem loadWindowParts_size (reader : Block) (part count : Nat) :
    (loadWindowParts reader part count).size = count * (9 + reader.size) := by
  induction count generalizing part with
  | zero => simp [loadWindowParts, Block.size]
  | succ count ih => simp [loadWindowParts, Block.size, ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem loadWindowBlock_size (reader : Block) :
    (loadWindowBlock reader).size = 46 + 4 * reader.size := by
  simp [loadWindowBlock, loadWindowInit, Block.sequence, Block.size, Nat.mul_add]
  omega

theorem windowReadBits_eq_packedRead (store : WordRAM.ReadStore) (n blockSize close : Nat) :
    windowReadBits store (close / blockSize * blockSize / packedBpCodeWordWidth n) =
      (packedLocalBPWindowBitsRead store n blockSize close).value := by
  simp only [windowReadBits, packedLocalBPWindowBitsRead, packedLocalBPBlockWordsRead,
    ConcreteCompactBPCloseLCADirectory.bpCodeWordReadTraceResultWithStore,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map, blockStartOf, blockOfClose,
    ConcreteCompactBPCloseLCADirectory.readStorePayloadWordValue]
  cases store.readWord? 0 (close / blockSize * blockSize / packedBpCodeWordWidth n) <;>
    cases store.readWord? 0 (close / blockSize * blockSize / packedBpCodeWordWidth n + 1) <;>
    cases store.readWord? 0 (close / blockSize * blockSize / packedBpCodeWordWidth n + 2) <;>
    cases store.readWord? 0 (close / blockSize * blockSize / packedBpCodeWordWidth n + 3) <;>
    simp [flattenPayloadWords, List.append_assoc]

theorem packedLocalBPWindowBitsRead_trace (store : WordRAM.ReadStore) (n blockSize close : Nat) :
    let first := close / blockSize * blockSize / packedBpCodeWordWidth n
    (packedLocalBPWindowBitsRead store n blockSize close).trace =
      [.readWord 0 first (store.readWord? 0 first),
       .readWord 0 (first + 1) (store.readWord? 0 (first + 1)),
       .readWord 0 (first + 2) (store.readWord? 0 (first + 2)),
       .readWord 0 (first + 3) (store.readWord? 0 (first + 3))] := rfl

theorem packedLocalBPWindowBitsRead_readOnly (store : WordRAM.ReadStore) (n blockSize close : Nat) :
    ReadOnlyTrace (packedLocalBPWindowBitsRead store n blockSize close).trace := by
  rw [packedLocalBPWindowBitsRead_trace]
  simp [ReadOnlyTrace, WordRAM.TraceEvent.isReadWord]

theorem windowPartsReceipts_eq_trace (shape : CartesianShape) (memory : Memory)
    (store : WordRAM.ReadStore) (n blockSize close : Nat) :
    windowPartsReceipts shape memory
      (close / blockSize * blockSize / packedBpCodeWordWidth n) 0 4 =
      logicalTraceReads shape memory (packedLocalBPWindowBitsRead store n blockSize close).trace := by
  rw [packedLocalBPWindowBitsRead_trace]
  simp [windowPartsReceipts, logicalTraceReads]

theorem windowFirstWord_canonical (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    windowFirstWord regs = regs 1024 / (packedInteriorLayout shape.size).blockSize *
      (packedInteriorLayout shape.size).blockSize / packedBpCodeWordWidth shape.size := by
  have hw : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hb : regs 33 = (packedInteriorLayout shape.size).blockSize := hm 17 (by decide)
  simp only [windowFirstWord, hw, hb]

theorem loadWindowBlock_reference (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedLocalBPWindowBitsRead (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (packedInteriorLayout shape.size).blockSize (regs 1024)
    let actual := (loadWindowBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 1064 = bitsToNatLE expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have h := loadWindowBlock_source shape memory reader hreader hwrites regs hm
  dsimp only at h ⊢
  rw [windowFirstWord_canonical shape regs hm, windowReadBits_eq_packedRead,
    windowPartsReceipts_eq_trace shape memory (concreteBPNativeSuccinctRMQGlobalReadStore shape)] at h
  exact ⟨h.1, h.2.1, h.2.2, packedLocalBPWindowBitsRead_readOnly _ _ _ _⟩

theorem loadWindowBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedLocalBPWindowBitsRead (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (packedInteriorLayout shape.size).blockSize (regs 1024)
    let actual := run memory ((loadWindowBlock reader).compileAt 0 ++ [.halt 1064])
      (47 + 4 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some (bitsToNatLE expected.value) ∧
      actual.final.status = .halted (bitsToNatLE expected.value) ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧
      actual.steps ≤ 47 + 4 * reader.size ∧
      (∀ r, ¬ WindowWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  have hs := loadWindowBlock_reference shape memory reader hreader hwrites regs hm
  have hc := (loadWindowBlock reader).compile_with_halt memory 1064 ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hs hc ⊢
  rw [hs.1] at hc
  have hsize : (loadWindowBlock reader).size + 1 = 47 + 4 * reader.size := by
    rw [loadWindowBlock_size]; omega
  rw [hsize] at hc
  have hd := hc.1
  simp only [Block.eval, hs.1] at hd
  refine ⟨hc.2.1.trans (congrArg some hs.2.1), ?_, hc.2.2.1.trans hs.2.2.1,
    ?_, ?_, hs.2.2.2⟩
  · exact (congrArg Data.status hd).trans (congrArg Status.halted hs.2.1)
  · simpa only [List.length_append, Block.compile_length, List.length_singleton, hsize]
      using hc.2.2.2
  · intro r hr
    exact (congrArg (fun d : Data => d.regs r) hd).trans
      (loadWindowBlock_frame reader hwrites memory _ r hr)

/-- The fixed reader is instantiated on the counted allocation in this consumer.
No supplied-reader certificate remains. -/
theorem loadWindowBlock_canonical_machine (shape : CartesianShape)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedLocalBPWindowBitsRead (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (packedInteriorLayout shape.size).blockSize (regs 1024)
    let actual := run (shapeMemory shape)
      ((loadWindowBlock logicalReadBlock).compileAt 0 ++ [.halt 1064])
      4319 ⟨regs, 0, .running⟩
    actual.result = some (bitsToNatLE expected.value) ∧
      actual.final.status = .halted (bitsToNatLE expected.value) ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      actual.steps ≤ 4319 ∧
      (∀ r, ¬ WindowWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  exact loadWindowBlock_machine shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm

end RMQ.SuccinctFinal.PackedWordRAM
