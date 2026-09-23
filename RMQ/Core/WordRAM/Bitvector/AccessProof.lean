import RMQ.Core.WordRAM.Bitvector.Source
import RMQ.Core.WordRAM.Bitvector.CompleteReader
import RMQ.Core.WordRAM.Bitvector.SafetyInterface
import RMQ.Core.WordRAM.Bitvector.Width

/-! # Original-bit access by the actual shared physical reader -/

namespace RMQ.PackedBitvector.AccessProof

open SuccinctSpace SuccinctRank
open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

def AccessMetadata (bits : List Bool) (regs : Registers) : Prop :=
  regs 3 = 0 ∧ regs 18 = bits.length ∧
  regs 19 = machineWordBits bits.length ∧
  regs 22 = Experiment.width bits.length

def accessPacket (bits : List Bool) (index : Nat) : Nat :=
  ((bits[index]?).map fun bit => bit.toNat + 1).getD 0

def accessReceipts (bits : List Bool) (index : Nat) : List Receipt :=
  if index < bits.length then
    Allocation.readerReceipts bits false 19 (index / machineWordBits bits.length)
  else []

private theorem shiftRight_numeric (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b :=
  Nat.shiftRight_eq_div_pow a b

private theorem extract_bit (word : List Bool) (index : Nat) (bit : Bool)
    (found : word[index]? = some bit) :
    (bitsToNatLE word >>> index) % 2 = bit.toNat := by
  induction index generalizing word with
  | zero =>
      cases word with
      | nil => simp at found
      | cons head rest =>
          have hb : head = bit := by simpa using found
          subst head
          cases bit <;> simp [bitsToNatLE, bitToNat] <;> omega
  | succ index ih =>
      cases word with
      | nil => simp at found
      | cons head rest =>
          have hf : rest[index]? = some bit := by simpa using found
          have hd : bitsToNatLE (head :: rest) / 2 = bitsToNatLE rest := by
            cases head <;> simp [bitsToNatLE, bitToNat] <;> omega
          rw [Nat.shiftRight_succ_inside, hd]
          exact ih rest hf

private theorem raw_access_word (bits : List Bool) (index : Nat) (hi : index < bits.length) :
    ∃ word,
      (Allocation.readStore bits false).readWord? 19 (index / machineWordBits bits.length) = some word ∧
      (bitsToNatLE word >>> (index % machineWordBits bits.length)) % 2 + 1 =
        accessPacket bits index := by
  let m := machineWordBits bits.length
  have mp : 0 < m := machineWordBits_pos bits.length
  have hstart : index / m * m < bits.length :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self index m) hi
  obtain ⟨word, found⟩ := chunkPayloadWords_get?_some_of_mul_lt mp hstart
  have hc : index / m < (chunkPayloadWords m bits).length :=
    (List.getElem?_eq_some_iff.mp found).1
  have hs : (Allocation.readStore bits false).readWord? 19 (index / m) = some word := by
    simp only [Allocation.readStore, Allocation.logicalWord, Allocation.logicalWords,
      normalizedSegmentWord, Nat.reduceEqDiff, if_false, if_true]
    rw [jacobson_raw_words_eq]
    change (chunkPayloadWords m bits ++ List.replicate (bits.length + 1) []).toArray[index / m]? = _
    rw [List.getElem?_toArray, List.getElem?_append_left hc]
    exact found
  refine ⟨word, hs, ?_⟩
  have hslice := chunkPayloadWords_get?_eq_take_drop found
  have hrem : index % m < m := Nat.mod_lt index mp
  have hindex : index / m * m + index % m = index := Nat.div_add_mod' index m
  have hbit : word[index % m]? = some bits[index] := by
    rw [hslice, List.getElem?_take_of_lt hrem, List.getElem?_drop, hindex]
    exact List.getElem?_eq_getElem hi
  rw [extract_bit word _ _ hbit]
  simp [accessPacket, List.getElem?_eq_getElem hi]

private theorem eval_action (memory : Memory) (op : Action) (regs : Registers) :
    (Block.action op).eval memory ⟨regs, .running⟩ = op.eval memory ⟨regs, .running⟩ := rfl

private theorem eval_skip (memory : Memory) (s : Data) :
    Block.skip.eval memory s = ⟨s, []⟩ := by
  cases s with
  | mk regs status => cases status <;> rfl

private theorem eval_ifZero (memory : Memory) (r : Nat) (zero nonzero : Block) (regs : Registers) :
    (Block.ifZero r zero nonzero).eval memory ⟨regs, .running⟩ =
      if regs r = 0 then zero.eval memory ⟨regs, .running⟩
      else nonzero.eval memory ⟨regs, .running⟩ := rfl

private def prepared (regs : Registers) : Registers :=
  (((regs.write 705 0).write 706 1).write 8192 19).write 8193 (regs 704 / regs 19)

theorem accessQuery_writes :
    accessQuery.WritesOnly (fun r => (705 ≤ r ∧ r < 710) ∨ (8192 ≤ r ∧ r < 8271)) := by
  have hr := Block.WritesOnly.mono _ physicalReader_writes
    (show ∀ r, 8194 ≤ r ∧ r < 8271 →
      (705 ≤ r ∧ r < 710) ∨ (8192 ≤ r ∧ r < 8271) by omega)
  simpa [accessQuery, Block.sequence, Block.WritesOnly, Action.destination] using hr

theorem accessQuery_source (bits : List Bool) (regs : Registers)
    (hm : AccessMetadata bits regs) :
    let actual := accessQuery.eval (Allocation.memory bits) ⟨regs, .running⟩
    actual.final.status = .running ∧
    actual.final.regs 705 = accessPacket bits (regs 704) ∧
    actual.reads = accessReceipts bits (regs 704) ∧
    (∀ r, r < 705 ∨ (710 ≤ r ∧ r < 8192) ∨ 8271 ≤ r →
      actual.final.regs r = regs r) := by
  have frame : ∀ r, r < 705 ∨ (710 ≤ r ∧ r < 8192) ∨ 8271 ≤ r →
      (accessQuery.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs r = regs r := by
    intro r hr
    exact Block.eval_frame _ _ _ accessQuery_writes r (by omega) _
  suffices h : (accessQuery.eval (Allocation.memory bits) ⟨regs, .running⟩).final.status = .running ∧
      (accessQuery.eval (Allocation.memory bits) ⟨regs, .running⟩).final.regs 705 = accessPacket bits (regs 704) ∧
      (accessQuery.eval (Allocation.memory bits) ⟨regs, .running⟩).reads = accessReceipts bits (regs 704) from
    ⟨h.1, h.2.1, h.2.2, frame⟩
  rcases hm with ⟨ht, hn, hw, hwidth⟩
  by_cases valid : regs 704 < bits.length
  · obtain ⟨word, hword, hbit⟩ := raw_access_word bits (regs 704) valid
    rw [Nat.shiftRight_eq_div_pow] at hbit
    have hp : GenericReaderMetadata bits false (prepared regs) := by
      simp [GenericReaderMetadata, prepared, Registers.write, ht, hwidth]
    have hr := Allocation.physicalReader_correct bits false (prepared regs) hp
    have hrequest : (prepared regs) 8192 = 19 ∧
        (prepared regs) 8193 = regs 704 / machineWordBits bits.length := by
      simp [prepared, Registers.write, hw]
    simp only [hrequest.1, hrequest.2, hword, logicalPacket, logicalLength,
      Option.map_some, Option.getD_some] at hr
    generalize he : Experiment.physicalReader.eval (Allocation.memory bits)
      ⟨prepared regs, .running⟩ = loaded at hr
    rcases loaded with ⟨⟨out, status⟩, reads⟩
    dsimp only at hr
    obtain ⟨rfl, packet, length, hreads, hframe⟩ := hr
    have hi : out 704 = regs 704 := by simpa [prepared, Registers.write] using hframe 704 (Or.inl (by decide))
    have hm : out 19 = machineWordBits bits.length := by
      simpa [prepared, Registers.write, hw] using hframe 19 (Or.inl (by decide))
    simp only [prepared, hw] at he
    simp [accessQuery, Block.sequence, Block.eval_seq, Evaluation.bind,
      eval_action, eval_skip, eval_ifZero, Action.eval, Action.instruction,
      SuccinctFinal.PackedWordRAM.execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, Comparison.eval, hn, hw, valid,
      he, packet, hi, hm, shiftRight_numeric, hbit, hreads, accessReceipts]
  · simp [accessQuery, Block.sequence, Block.eval_seq, Evaluation.bind,
      eval_action, eval_skip, eval_ifZero, Action.eval, Action.instruction,
      SuccinctFinal.PackedWordRAM.execute, State.writeNext, Data.ofState,
      Registers.write, Comparison.eval, hn, valid, accessPacket, accessReceipts]

private theorem checks_of_safe (memory : Memory) (width : Nat) (block : Block)
    (s : Data) (safe : block.Safe memory width s) : ScalarChecks memory width block s := by
  induction block generalizing s with
  | skip => exact fun _ => True.intro
  | action op => exact safe.2
  | exit src => exact safe.2
  | seq a b iha ihb =>
      intro hs
      exact ⟨iha s (safe.2 hs).1, ihb _ (safe.2 hs).2⟩
  | ifZero r a b iha ihb =>
      intro hs
      have h := safe.2 hs
      by_cases hz : s.regs r = 0
      · simpa [hz] using iha s (by simpa [hz] using h)
      · simpa [hz] using ihb s (by simpa [hz] using h)
  | «repeat» count body ih =>
      intro hs
      have h := safe.2 hs
      clear safe hs
      induction count generalizing s with
      | zero => trivial
      | succ count iht => exact ⟨ih s h.1, iht _ h.2⟩

private theorem checks_seq (memory : Memory) (width : Nat) (a b : Block) (s : Data) :
    ScalarChecks memory width (.seq a b) s ↔
      (s.status = .running → ScalarChecks memory width a s ∧
        ScalarChecks memory width b (a.eval memory s).final) := Iff.rfl

private theorem checks_action (memory : Memory) (width : Nat) (op : Action) (regs : Registers) :
    ScalarChecks memory width (.action op) ⟨regs, .running⟩ ↔
      op.LocalSafe memory width ⟨regs, .running⟩ := by simp [ScalarChecks]

private theorem checks_ifZero (memory : Memory) (width r : Nat) (a b : Block) (regs : Registers) :
    ScalarChecks memory width (.ifZero r a b) ⟨regs, .running⟩ ↔
      (if regs r = 0 then ScalarChecks memory width a ⟨regs, .running⟩
        else ScalarChecks memory width b ⟨regs, .running⟩) := by simp [ScalarChecks]

private theorem checks_skip (memory : Memory) (width : Nat) (s : Data) :
    ScalarChecks memory width Block.skip s := fun _ => True.intro

private theorem write_fit (width : Nat) (regs : Registers) (dst value : Nat)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (hv : value < 2 ^ width) :
    (⟨regs.write dst value, .running⟩ : Data).Fits width := by
  constructor
  · intro r
    by_cases h : r = dst
    · simpa [Registers.write, h] using hv
    · simpa [Registers.write, h] using fit.1 r
  · intro v h; cases h

private theorem finish_safe (memory : Memory) (width : Nat) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits width) (cap : 2 < 2 ^ width)
    (hm : 0 < regs 19) (hshift : regs 19 < width) :
    (Block.ifZero 8194 .skip (Block.sequence [
      .action (.constant 707 1), .action (.arithmetic .sub 708 8194 707),
      .action (.arithmetic .mod 709 704 19),
      .action (.arithmetic .shr 708 708 709),
      .action (.constant 707 2), .action (.arithmetic .mod 708 708 707),
      .action (.constant 707 1), .action (.arithmetic .add 705 708 707)])).Safe
      memory width ⟨regs, .running⟩ := by
  have hp := fit.1 8194
  have hword := fit.1 19
  dsimp only at hp hword
  have rem := Nat.mod_lt (regs 704) hm
  have shr := Nat.shiftRight_le (regs 8194 - 1) (regs 704 % regs 19)
  have bit := Nat.mod_lt ((regs 8194 - 1) >>> (regs 704 % regs 19)) (by decide : 0 < 2)
  simp only [Nat.shiftRight_eq_div_pow] at shr bit
  apply ScalarChecks_safe memory width _ _ fit
  by_cases hz : regs 8194 = 0
  · simp [checks_ifZero, checks_skip, hz]
  · simp [Block.sequence, checks_seq, checks_action, checks_ifZero, checks_skip,
      eval_action,
      Action.eval, Action.instruction, Action.LocalSafe,
      SuccinctFinal.PackedWordRAM.execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, shiftRight_numeric, hz] <;> omega

theorem accessQuery_safe (bits : List Bool) (regs : Registers)
    (hm : AccessMetadata bits regs)
    (fit : (⟨regs, .running⟩ : Data).Fits (Experiment.width bits.length))
    (readerSafe : Controller.ReaderSafe
      (Allocation.controllerModel bits false regs) (Experiment.width bits.length)
      (Allocation.memory bits) Experiment.physicalReader) :
    accessQuery.Safe (Allocation.memory bits) (Experiment.width bits.length)
      ⟨regs, .running⟩ := by
  let width := Experiment.width bits.length
  change accessQuery.Safe (Allocation.memory bits) width ⟨regs, .running⟩
  change (⟨regs, .running⟩ : Data).Fits width at fit
  have cap : 23 < 2 ^ width := fixed_floor_capacity bits.length 23 (by decide)
  rcases hm with ⟨ht, hn, hw, hwidth⟩
  have wp : 0 < regs 19 := by rw [hw]; exact machineWordBits_pos _
  have wlt : regs 19 < width := by rw [hw]; exact machineWordBits_lt_width _
  have quot : regs 704 / regs 19 < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (fit.1 704)
  by_cases valid : regs 704 < bits.length
  · have f1 := write_fit width regs 705 0 fit (by omega)
    have f2 := write_fit width (regs.write 705 0) 706 1 f1 (by omega)
    have f3 := write_fit width ((regs.write 705 0).write 706 1) 8192 19 f2 (by omega)
    have fp : (⟨prepared regs, .running⟩ : Data).Fits width :=
      write_fit width _ 8193 _ f3 quot
    have mp : Controller.MetadataMatches (Allocation.controllerModel bits false regs) (prepared regs) := by
      intro r hr
      have h705 : r ≠ 705 := by omega
      have h706 : r ≠ 706 := by omega
      have h8192 : r ≠ 8192 := by omega
      have h8193 : r ≠ 8193 := by omega
      simp [Allocation.controllerModel, prepared, Registers.write, h705, h706, h8192, h8193]
    have rs := readerSafe ⟨prepared regs, .running⟩ fp mp
    have rf := Block.eval_fits (Allocation.memory bits) width _ _ rs
    have rc := checks_of_safe (Allocation.memory bits) width Experiment.physicalReader
      ⟨prepared regs, .running⟩ rs
    have readerMetadata : GenericReaderMetadata bits false (prepared regs) := by
      simp [GenericReaderMetadata, prepared, Registers.write, ht, hwidth]
    have exactRead := Allocation.physicalReader_correct bits false (prepared regs) readerMetadata
    let tail : Block := .ifZero 8194 .skip (Block.sequence [
      .action (.constant 707 1), .action (.arithmetic .sub 708 8194 707),
      .action (.arithmetic .mod 709 704 19),
      .action (.arithmetic .shr 708 708 709),
      .action (.constant 707 2), .action (.arithmetic .mod 708 708 707),
      .action (.constant 707 1), .action (.arithmetic .add 705 708 707)])
    have tc : ScalarChecks (Allocation.memory bits) width tail
        (Experiment.physicalReader.eval (Allocation.memory bits) ⟨prepared regs, .running⟩).final := by
      generalize he : Experiment.physicalReader.eval (Allocation.memory bits)
        ⟨prepared regs, .running⟩ = loaded at exactRead rf ⊢
      rcases loaded with ⟨⟨out, status⟩, reads⟩
      dsimp only at exactRead rf ⊢
      obtain ⟨rfl, _, _, _, frame⟩ := exactRead
      have hmout : out 19 = regs 19 := by
        simpa [prepared, Registers.write] using frame 19 (Or.inl (by decide))
      exact checks_of_safe (Allocation.memory bits) width tail ⟨out, .running⟩
        (finish_safe _ _ _ rf (by omega) (by omega) (by omega))
    simp only [prepared, hw] at rc
    simp only [tail, prepared, hw, Block.sequence,
      List.foldr_cons, List.foldr_nil] at tc
    apply ScalarChecks_safe (Allocation.memory bits) width _ _ fit
    rw [hw] at quot
    simp [accessQuery, Block.sequence, checks_seq, checks_action, checks_ifZero, checks_skip,
      Block.eval_seq, Evaluation.bind, eval_action, eval_skip, eval_ifZero,
      Action.eval, Action.instruction, Action.LocalSafe,
      SuccinctFinal.PackedWordRAM.execute, State.writeNext, Data.ofState,
      Registers.write, Arithmetic.eval, Comparison.eval, hn, hw, valid, rc, tc] <;> omega
  · apply ScalarChecks_safe (Allocation.memory bits) width _ _ fit
    simp [accessQuery, Block.sequence, checks_seq, checks_action, checks_ifZero, checks_skip,
      eval_action, eval_skip, eval_ifZero,
      Action.eval, Action.instruction, Action.LocalSafe,
      SuccinctFinal.PackedWordRAM.execute, State.writeNext, Data.ofState,
      Registers.write, Comparison.eval, hn, valid] <;> omega

#print axioms accessQuery_source
#print axioms accessQuery_safe

end RMQ.PackedBitvector.AccessProof
