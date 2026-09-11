import RMQ.Core.WordRAM.Packed.InteriorSource
import RMQ.Core.WordRAM.Packed.ReadInterface
import RMQ.Core.WordRAM.Packed.PhysicalRead

/-! # Primitive implementation of the seven-copy interior table reader -/

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

private theorem eval_comparison (memory : Memory) (regs : Registers)
    (op : Comparison) (dst lhs rhs : Nat) :
    (Block.action (.comparison op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_skip (memory : Memory) (regs : Registers) :
    Block.skip.eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := rfl

private theorem eval_ifZero (memory : Memory) (regs : Registers) (condition : Nat)
    (zero nonzero : Block) :
    (Block.ifZero condition zero nonzero).eval memory ⟨regs, .running⟩ =
      if regs condition = 0 then zero.eval memory ⟨regs, .running⟩
      else nonzero.eval memory ⟨regs, .running⟩ := rfl

private theorem data_eq_running (s : Data) (hs : s.status = .running) :
    s = ⟨s.regs, .running⟩ := by cases s; simp_all

private theorem eval_seq_of_results (memory : Memory) (first second : Block) (s : Data)
    (a b : Evaluation) (ha : first.eval memory s = a)
    (hb : second.eval memory a.final = b) :
    (Block.seq first second).eval memory s = ⟨b.final, a.reads ++ b.reads⟩ := by
  rw [Block.eval_seq, ha]
  simp only [Evaluation.bind, hb]

def InteriorBodyWrites (r : Nat) : Prop :=
  (710 ≤ r ∧ r < 714) ∨ (715 ≤ r ∧ r < 719) ∨ (8192 ≤ r ∧ r < 8271)

theorem interiorReadBody_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorReadBody reader).WritesOnly InteriorBodyWrites := by
  have hreader : reader.WritesOnly InteriorBodyWrites :=
    Block.WritesOnly.mono reader hr (by intro r h; unfold InteriorBodyWrites; omega)
  simpa [interiorReadBody, interiorReadAddress, interiorReadDecode, Block.sequence,
    Block.WritesOnly, Action.destination, InteriorBodyWrites, natSubBlock] using hreader

theorem interiorReadBody_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorBodyWrites r) :
    ((interiorReadBody reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorReadBody_writes reader hr) r outside s

theorem interiorReadBody_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorReadBody reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorReadBody_frame reader hr memory s (16 + i) (by unfold InteriorBodyWrites; omega)]
  exact hm i hi

theorem interiorReadAddress_source (memory : Memory) (regs : Registers) :
    let actual := interiorReadAddress.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 8192 = 20 ∧
      actual.final.regs 8193 = regs 706 + regs 707 * regs 709 + regs 710 ∧
      (∀ r, r ≠ 715 → r ≠ 8192 → r ≠ 8193 → actual.final.regs r = regs r) := by
  simp [interiorReadAddress, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
    eval_arithmetic, eval_skip, Arithmetic.eval, Registers.write]
  intro r h1 h2 h3
  simp [h1, h2, h3]

theorem interiorReadDecode_source (memory : Memory) (regs : Registers) (hone : regs 714 = 1) :
    let actual := interiorReadDecode.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 710 = regs 710 + 1 ∧
      actual.final.regs 713 = (if regs 8194 = 0 then 0 else regs 713) ∧
      actual.final.regs 711 = (if regs 8194 = 0 then regs 711 else
        regs 711 + (regs 8194 - 1) * 2 ^ regs 712) ∧
      actual.final.regs 712 = (if regs 8194 = 0 then regs 712 else regs 712 + regs 8195) := by
  have shiftLeft_numeric (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
  have hsub := natSubBlock_source 716 8194 714 718 memory regs (by decide) (by decide)
  by_cases hz : regs 8194 = 0 <;>
    simp [interiorReadDecode, Block.sequence, Block.eval_seq, Evaluation.bind,
      eval_ifZero, eval_constant, eval_arithmetic, eval_skip, Arithmetic.eval,
      Registers.write, hz, hone, hsub, shiftLeft_numeric]

theorem interiorReadBody_inactive (reader : Block) (memory : Memory) (regs : Registers)
    (hstop : regs 709 ≤ regs 710) :
    (interiorReadBody reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write 717 0, .running⟩, []⟩ := by
  simp [interiorReadBody, Block.eval_seq, eval_comparison, eval_ifZero,
    eval_skip, Evaluation.bind, Comparison.eval, Registers.write, Nat.not_lt.mpr hstop]

theorem interiorReadBody_active (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) (hone : regs 714 = 1) (hactive : regs 710 < regs 709) :
    let actual := (interiorReadBody reader).eval memory ⟨regs, .running⟩
    let address := regs 706 + regs 707 * regs 709 + regs 710
    let word := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 address
    actual.final.status = .running ∧ actual.reads = readerReceipts shape memory 20 address ∧
      actual.final.regs 710 = regs 710 + 1 ∧
      actual.final.regs 713 = (if word = none then 0 else regs 713) ∧
      actual.final.regs 711 = regs 711 + bitsToNatLE (word.getD []) * 2 ^ regs 712 ∧
      actual.final.regs 712 = regs 712 + (word.getD []).length := by
  let compared := regs.write 717 1
  have ha := interiorReadAddress_source memory compared
  generalize hea : interiorReadAddress.eval memory ⟨compared, .running⟩ = addressResult at ha
  rcases addressResult with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha
  obtain ⟨hast, hareads, hsegment, haddress, haframe⟩ := ha
  subst ast
  subst areads
  have ham : MetadataMatches shape ar := by
    intro i hi
    rw [haframe _ (by omega) (by omega) (by omega)]
    simp only [compared, Registers.write, if_neg (show 16 + i ≠ 717 by omega)]
    exact hm i hi
  have hb := hreader ar ham
  generalize heb : reader.eval memory ⟨ar, .running⟩ = readResult at hb
  rcases readResult with ⟨⟨br, bst⟩, breads⟩
  dsimp only at hb
  obtain ⟨hbst, hpacket, hlength, hreads, hbframe⟩ := hb
  subst bst
  have hf (r : Nat) (hlo : r < 715) : br r = regs r := by
    rw [hbframe _ (Or.inl (by omega)), haframe _ (by omega) (by omega) (by omega)]
    simp [compared, Registers.write, show r ≠ 717 by omega]
  have hc := interiorReadDecode_source memory br ((hf 714 (by decide)).trans hone)
  generalize hec : interiorReadDecode.eval memory ⟨br, .running⟩ = decoded at hc
  rcases decoded with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc
  obtain ⟨hcst, hcreads, hindex, hflag, hvalue, hlen⟩ := hc
  subst cst
  subst creads
  have heval : (interiorReadBody reader).eval memory ⟨regs, .running⟩ =
      ⟨⟨cr, .running⟩, breads⟩ := by
    have hinner : (Block.seq interiorReadAddress (.seq reader interiorReadDecode)).eval
        memory ⟨compared, .running⟩ = ⟨⟨cr, .running⟩, breads⟩ := by
      rw [Block.eval_seq, hea]
      change (Block.seq reader interiorReadDecode).eval memory ⟨ar, .running⟩ = _
      rw [Block.eval_seq, heb]
      simp [Evaluation.bind, hec]
    have hgate : (Block.ifZero 717 .skip
        (.seq interiorReadAddress (.seq reader interiorReadDecode))).eval
        memory ⟨compared, .running⟩ = ⟨⟨cr, .running⟩, breads⟩ := by
      rw [eval_ifZero, if_neg (by simp [compared])]
      exact hinner
    dsimp only [compared] at hgate
    rw [interiorReadBody, Block.eval_seq, eval_comparison]
    have hcmp : Comparison.lt.eval (regs 710) (regs 709) = 1 := by simp [Comparison.eval, hactive]
    simp only [hcmp, Evaluation.bind, hgate, List.nil_append]
  rw [heval]
  dsimp only
  simp [hsegment, haddress, compared, Registers.write] at hpacket hlength hreads
  refine ⟨rfl, hreads, hindex.trans (congrArg (· + 1) (hf 710 (by decide))), ?_, ?_, ?_⟩
  · simp only [hflag, hpacket, logicalPacket_zero_iff, hf 713 (by decide)]
  · rw [hvalue, hpacket, hf 711 (by decide), hf 712 (by decide)]
    cases (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
      (regs 706 + regs 707 * regs 709 + regs 710) <;> simp [logicalPacket, bitsToNatLE]
  · rw [hlen, hpacket, hlength, hf 712 (by decide)]
    cases (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
      (regs 706 + regs 707 * regs 709 + regs 710) <;> simp [logicalPacket, logicalLength]

def InteriorAccumMatches (acc : Option (List Bool)) (regs : Registers) : Prop :=
  match acc with
  | none => regs 713 = 0
  | some bits => regs 713 = 1 ∧ regs 711 = bitsToNatLE bits ∧ regs 712 = bits.length

def interiorAppendReply (acc word : Option (List Bool)) : Option (List Bool) :=
  acc.bind fun bits => word.map fun tail => bits ++ tail

def interiorFoldWords (store : FlatWordStore) (start : Nat) : Nat → Option (List Bool) → Option (List Bool)
  | 0, acc => acc
  | count + 1, acc => interiorFoldWords store (start + 1) count (interiorAppendReply acc (store start))

def interiorFoldReceipts (shape : CartesianShape) (memory : Memory) (start : Nat) : Nat → List Receipt
  | 0 => []
  | count + 1 => readerReceipts shape memory 20 start ++ interiorFoldReceipts shape memory (start + 1) count

structure InteriorFoldState (base index total j : Nat) (acc : Option (List Bool))
    (regs : Registers) : Prop where
  base_eq : regs 706 = base
  entry_eq : regs 707 = index
  total_eq : regs 709 = total
  index_eq : regs 710 = j
  one_eq : regs 714 = 1
  accumulator : InteriorAccumMatches acc regs

theorem interiorReadBody_active_accumulator (shape : CartesianShape) (memory : Memory)
    (reader : Block) (hreader : ReaderCorrect shape memory reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 714 = 1)
    (hactive : regs 710 < regs 709) (acc : Option (List Bool))
    (hacc : InteriorAccumMatches acc regs) :
    InteriorAccumMatches (interiorAppendReply acc
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
        (regs 706 + regs 707 * regs 709 + regs 710)))
      ((interiorReadBody reader).eval memory ⟨regs, .running⟩).final.regs := by
  have h := interiorReadBody_active shape memory reader hreader regs hm hone hactive
  dsimp only at h ⊢
  cases acc with
  | none =>
    simp only [InteriorAccumMatches, interiorAppendReply, Option.bind_none] at hacc ⊢
    rw [h.2.2.2.1, hacc]
    split <;> rfl
  | some bits =>
    rcases hacc with ⟨hflag, hvalue, hlength⟩
    cases hw : (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
        (regs 706 + regs 707 * regs 709 + regs 710) with
    | none => simpa [interiorAppendReply, InteriorAccumMatches, hw] using h.2.2.2.1
    | some word =>
      simp only [interiorAppendReply, Option.bind_some, Option.map_some, InteriorAccumMatches]
      refine ⟨?_, ?_, ?_⟩
      · simpa [hw, hflag] using h.2.2.2.1
      · rw [h.2.2.2.2.1, hw, Option.getD_some, hvalue, hlength, bitsToNatLE_append]
        simp only [Nat.mul_comm]
      · simpa [hw, hlength, List.length_append] using h.2.2.2.2.2

theorem interiorReadRepeat_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (base index total cycles j : Nat) (acc : Option (List Bool))
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hs : InteriorFoldState base index total j acc regs) (hcover : total ≤ j + cycles) :
    let actual := (Block.repeat cycles (interiorReadBody reader)).eval memory ⟨regs, .running⟩
    let start := base + index * total + j
    actual.final.status = .running ∧
      InteriorAccumMatches (interiorFoldWords
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20) start (total - j) acc)
        actual.final.regs ∧
      actual.reads = interiorFoldReceipts shape memory start (total - j) := by
  induction cycles generalizing j acc regs with
  | zero =>
    have hz : total - j = 0 := by omega
    simpa [Block.eval_repeat, iterate, hz, interiorFoldWords, interiorFoldReceipts] using hs.accumulator
  | succ cycles ih =>
    by_cases hactive : j < total
    · have ha : regs 710 < regs 709 := by rw [hs.index_eq, hs.total_eq]; exact hactive
      have hb := interiorReadBody_active shape memory reader hreader regs hm hs.one_eq ha
      have hac := interiorReadBody_active_accumulator shape memory reader hreader regs hm hs.one_eq ha acc hs.accumulator
      have hmeta := interiorReadBody_metadata shape reader hwrites memory ⟨regs, .running⟩ hm
      have hframe (r : Nat) (ho : ¬ InteriorBodyWrites r) :=
        interiorReadBody_frame reader hwrites memory ⟨regs, .running⟩ r ho
      generalize he : (interiorReadBody reader).eval memory ⟨regs, .running⟩ = first
        at hb hac hmeta hframe
      rcases first with ⟨⟨fr, fst⟩, freceipts⟩
      dsimp only at hb hac hmeta hframe
      obtain ⟨hfst, hreads, hindex, _⟩ := hb
      subst fst
      let nextAcc := interiorAppendReply acc
        ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 (base + index * total + j))
      have hnext : InteriorFoldState base index total (j + 1) nextAcc fr := by
        constructor
        · rw [hframe 706 (by simp [InteriorBodyWrites])]; exact hs.base_eq
        · rw [hframe 707 (by simp [InteriorBodyWrites])]; exact hs.entry_eq
        · rw [hframe 709 (by simp [InteriorBodyWrites])]; exact hs.total_eq
        · simpa only [hs.index_eq] using hindex
        · rw [hframe 714 (by simp [InteriorBodyWrites])]; exact hs.one_eq
        · simpa only [hs.base_eq, hs.entry_eq, hs.total_eq, hs.index_eq] using hac
      have ht := ih (j + 1) nextAcc fr hmeta hnext (by omega)
      have hremaining : total - j = (total - (j + 1)) + 1 := by omega
      rw [Block.eval_repeat_succ, he]
      dsimp only [Evaluation.bind]
      rw [hremaining, interiorFoldWords, interiorFoldReceipts]
      refine ⟨ht.1, ?_, ?_⟩
      · simpa only [nextAcc, Nat.add_assoc] using ht.2.1
      · rw [hreads, ht.2.2, hs.base_eq, hs.entry_eq, hs.total_eq, hs.index_eq]
        simp only [Nat.add_assoc]
    · have hstop : regs 709 ≤ regs 710 := by rw [hs.total_eq, hs.index_eq]; omega
      have hnext : InteriorFoldState base index total j acc (regs.write 717 0) := by
        constructor
        · exact hs.base_eq
        · exact hs.entry_eq
        · exact hs.total_eq
        · exact hs.index_eq
        · exact hs.one_eq
        · cases acc <;> simpa only [InteriorAccumMatches, Registers.write, reduceIte] using hs.accumulator
      have ht := ih j acc (regs.write 717 0)
        (MetadataMatches.write shape regs hm 717 0 (Or.inr (by decide))) hnext (by omega)
      rw [Block.eval_repeat_succ, interiorReadBody_inactive reader memory regs hstop]
      simpa only [Evaluation.bind, List.nil_append] using ht

theorem interiorFoldWords_collect (store : FlatWordStore) (start count : Nat) (acc : Option (List Bool)) :
    interiorFoldWords store start count acc =
      interiorAppendReply acc (collectPayloadWords ((consecutiveWordIndices start count).map store)) := by
  induction count generalizing start acc with
  | zero => cases acc <;> simp [interiorFoldWords, consecutiveWordIndices, collectPayloadWords, interiorAppendReply]
  | succ count ih =>
    simp only [interiorFoldWords, ih, consecutiveWordIndices, List.map_cons]
    cases acc <;> cases store start <;>
      cases ht : collectPayloadWords ((consecutiveWordIndices (start + 1) count).map store) <;>
      simp [interiorAppendReply, collectPayloadWords, List.append_assoc, ht]

theorem interiorReadInit_writes :
    interiorReadInit.WritesOnly (fun r => 709 ≤ r ∧ r < 714 ∨ r = 715) := by
  simp [interiorReadInit, Block.sequence, Block.WritesOnly, Action.destination]

theorem interiorReadInit_source (memory : Memory) (regs : Registers) (hone : regs 714 = 1) :
    let actual := interiorReadInit.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 709 = fixedWidthNatTableMachineChunkCount (regs 705) (regs 32) ∧
      actual.final.regs 710 = 0 ∧ actual.final.regs 711 = 0 ∧
      actual.final.regs 712 = 0 ∧ actual.final.regs 713 = 1 := by
  by_cases hz : regs 705 % regs 32 = 0 <;>
    simp [interiorReadInit, Block.sequence, Block.eval_seq, Evaluation.bind,
      eval_constant, eval_arithmetic, eval_ifZero, eval_skip, Arithmetic.eval,
      Registers.write, hz, hone, fixedWidthNatTableMachineChunkCount]

theorem interiorReadFinish_source (memory : Memory) (regs : Registers)
    (acc : Option (List Bool)) (hacc : InteriorAccumMatches acc regs)
    (hone : regs 714 = 1) (hzero : regs 708 = 0) :
    let actual := interiorReadFinish.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 708 = logicalPacket acc := by
  cases acc with
  | none =>
    simp only [InteriorAccumMatches] at hacc
    simp [interiorReadFinish, eval_ifZero, hacc, eval_skip, logicalPacket, hzero]
  | some bits =>
    obtain ⟨hflag, hval, _⟩ := hacc
    simp [interiorReadFinish, eval_ifZero, hflag, eval_arithmetic, Arithmetic.eval,
      Registers.write, hval, hone, logicalPacket]

def InteriorReadWrites (r : Nat) : Prop :=
  (708 ≤ r ∧ r < 719) ∨ (8192 ≤ r ∧ r < 8271)

theorem interiorReadBlock_writes (reader : Block) (hr : ReaderWrites reader) :
    (interiorReadBlock reader).WritesOnly InteriorReadWrites := by
  have hreader : reader.WritesOnly InteriorReadWrites :=
    Block.WritesOnly.mono reader hr (by intro r h; unfold InteriorReadWrites; omega)
  have hbody : (interiorReadBody reader).WritesOnly InteriorReadWrites :=
    Block.WritesOnly.mono _ (interiorReadBody_writes reader hr)
      (by intro r h; unfold InteriorReadWrites InteriorBodyWrites at *; omega)
  simpa [interiorReadBlock, interiorReadHead, interiorReadInvalid, interiorReadValid,
    interiorReadFinish, interiorReadInit, Block.sequence, Block.WritesOnly,
    Action.destination, InteriorReadWrites] using And.intro hreader hbody

theorem interiorReadBlock_frame (reader : Block) (hr : ReaderWrites reader)
    (memory : Memory) (s : Data) (r : Nat) (outside : ¬ InteriorReadWrites r) :
    ((interiorReadBlock reader).eval memory s).final.regs r = s.regs r :=
  Block.eval_frame memory _ _ (interiorReadBlock_writes reader hr) r outside s

theorem interiorReadBlock_metadata (shape : CartesianShape) (reader : Block)
    (hr : ReaderWrites reader) (memory : Memory) (s : Data) (hm : MetadataMatches shape s.regs) :
    MetadataMatches shape ((interiorReadBlock reader).eval memory s).final.regs := by
  intro i hi
  rw [interiorReadBlock_frame reader hr memory s (16 + i) (by unfold InteriorReadWrites; omega)]
  exact hm i hi

private theorem interiorReadInitialized_source (shape : CartesianShape) (memory : Memory) (reader : Block) (copies : Nat)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 714 = 1) (hzero : regs 708 = 0)
    (hcount : fixedWidthNatTableMachineChunkCount (regs 705) (regs 32) ≤ copies) :
    let count := fixedWidthNatTableMachineChunkCount (regs 705) (regs 32)
    let first := regs 706 + regs 707 * count
    let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
    let actual := (Block.seq interiorReadInit (.seq (.repeat copies (interiorReadBody reader)) interiorReadFinish)).eval
      memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 708 =
      logicalPacket (collectPayloadWords ((consecutiveWordIndices first count).map store)) ∧
      actual.reads = interiorFoldReceipts shape memory first count := by
  have hi := interiorReadInit_source memory regs hone
  have hframe (r : Nat) (ho : r < 709 ∨ 715 < r ∨ r = 714) :=
    Block.eval_frame memory interiorReadInit _ interiorReadInit_writes r (by omega) ⟨regs, .running⟩
  generalize hei : interiorReadInit.eval memory ⟨regs, .running⟩ = initialized at hi hframe
  rcases initialized with ⟨⟨ir, ist⟩, ireads⟩
  dsimp only at hi hframe
  obtain ⟨hist, hireads, htotal, hindex, hvalue, hlength, hflag⟩ := hi
  subst ist
  subst ireads
  have him : MetadataMatches shape ir := by
    intro i hi
    rw [hframe _ (Or.inl (by omega))]
    exact hm i hi
  let total := fixedWidthNatTableMachineChunkCount (regs 705) (regs 32)
  have hstate : InteriorFoldState (regs 706) (regs 707) total 0 (some []) ir :=
    ⟨hframe _ (Or.inl (by decide)), hframe _ (Or.inl (by decide)), htotal, hindex,
      (hframe _ (Or.inr (Or.inr rfl))).trans hone, hflag, hvalue, hlength⟩
  have hr := interiorReadRepeat_source shape memory reader hreader hwrites
    (regs 706) (regs 707) total copies 0 (some []) ir him hstate (by simpa only [Nat.zero_add] using hcount)
  have hrframe (r : Nat) (ho : ¬ InteriorBodyWrites r) := Block.eval_frame memory
    (.repeat copies (interiorReadBody reader)) _ (interiorReadBody_writes reader hwrites) r ho ⟨ir, .running⟩
  generalize her : (Block.repeat copies (interiorReadBody reader)).eval memory ⟨ir, .running⟩ = repeated at hr hrframe
  rcases repeated with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr hrframe
  obtain ⟨hrst, hracc, hrreads⟩ := hr
  subst rst
  have hrone : rr 714 = 1 := (hrframe 714 (by simp [InteriorBodyWrites])).trans hstate.one_eq
  have hrzero : rr 708 = 0 := (hrframe 708 (by simp [InteriorBodyWrites])).trans
    ((hframe 708 (Or.inl (by decide))).trans hzero)
  have hf := interiorReadFinish_source memory rr _ hracc hrone hrzero
  generalize hef : interiorReadFinish.eval memory ⟨rr, .running⟩ = finished at hf
  rcases finished with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfreads, hfvalue⟩ := hf
  subst fst
  subst freads
  have heval : (Block.seq interiorReadInit (.seq (.repeat copies (interiorReadBody reader)) interiorReadFinish)).eval
      memory ⟨regs, .running⟩ =
      ⟨⟨fr, .running⟩, rreads⟩ := by
    have htail := eval_seq_of_results memory (.repeat copies (interiorReadBody reader))
      interiorReadFinish ⟨ir, .running⟩ ⟨⟨rr, .running⟩, rreads⟩ ⟨⟨fr, .running⟩, []⟩ her hef
    simp only [List.append_nil] at htail
    have hfull := eval_seq_of_results memory interiorReadInit
      (.seq (.repeat copies (interiorReadBody reader)) interiorReadFinish)
      ⟨regs, .running⟩ ⟨⟨ir, .running⟩, []⟩ ⟨⟨fr, .running⟩, rreads⟩ hei htail
    simpa only [List.nil_append] using hfull
  rw [heval]
  dsimp only
  simp only [Nat.add_zero, Nat.sub_zero, interiorFoldWords_collect,
    interiorAppendReply, Option.bind_some, List.nil_append] at hfvalue hrreads
  have hmap (word : Option (List Bool)) : (word.map fun tail => tail) = word := by cases word <;> rfl
  rw [hmap] at hfvalue
  exact ⟨rfl, hfvalue, hrreads⟩

theorem interiorReadValid_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 714 = 1) (hzero : regs 708 = 0)
    (hcount : fixedWidthNatTableMachineChunkCount (regs 705) (regs 32) ≤ 7) :
    let count := fixedWidthNatTableMachineChunkCount (regs 705) (regs 32)
    let first := regs 706 + regs 707 * count
    let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
    let actual := (interiorReadValid reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 708 =
      logicalPacket (collectPayloadWords ((consecutiveWordIndices first count).map store)) ∧
      actual.reads = interiorFoldReceipts shape memory first count :=
  interiorReadInitialized_source shape memory reader 7 hreader hwrites regs hm hone hzero hcount

def interiorReadHeadRegs (regs : Registers) : Registers :=
  ((regs.write 708 0).write 714 1).write 717 (if regs 707 < regs 704 then 1 else 0)

theorem interiorReadHead_source (memory : Memory) (regs : Registers) :
    interiorReadHead.eval memory ⟨regs, .running⟩ =
      ⟨⟨interiorReadHeadRegs regs, .running⟩, []⟩ := by
  simp [interiorReadHead, interiorReadHeadRegs, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_constant, eval_comparison, eval_skip, Comparison.eval, Registers.write]

theorem interiorReadInvalid_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    let actual := (interiorReadInvalid reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 708 = logicalPacket
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20 (regs 57)) ∧
      actual.reads = readerReceipts shape memory 20 (regs 57) := by
  let prepared := (regs.write 8192 20).write 8193 (regs 57)
  have hp : MetadataMatches shape prepared :=
    MetadataMatches.write shape _ (MetadataMatches.write shape regs hm 8192 20 (Or.inr (by decide)))
      8193 _ (Or.inr (by decide))
  have hs := hreader prepared hp
  generalize he : reader.eval memory ⟨prepared, .running⟩ = loaded at hs
  rcases loaded with ⟨⟨out, status⟩, reads⟩
  dsimp only at hs
  obtain ⟨hstatus, hpacket, _hlength, hreads, _hframe⟩ := hs
  subst status
  simp [prepared, Registers.write] at he hpacket hreads
  simp [interiorReadInvalid, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_constant, eval_move, eval_skip, Registers.write, he, hpacket, hreads]

def interiorRequests (regs : Registers) : List Nat :=
  if regs 707 < regs 704 then
    let count := fixedWidthNatTableMachineChunkCount (regs 705) (regs 32)
    consecutiveWordIndices (regs 706 + regs 707 * count) count
  else [regs 57]

theorem interiorFoldReceipts_flatMap (shape : CartesianShape) (memory : Memory) (start count : Nat) :
    interiorFoldReceipts shape memory start count =
      (consecutiveWordIndices start count).flatMap (readerReceipts shape memory 20) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [interiorFoldReceipts, consecutiveWordIndices, ih]

theorem interiorReadBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hcount : fixedWidthNatTableMachineChunkCount (regs 705) (regs 32) ≤ 7) :
    let store := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20
    let actual := (interiorReadBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 708 =
      logicalPacket (collectPayloadWords ((interiorRequests regs).map store)) ∧
      actual.reads = (interiorRequests regs).flatMap (readerReceipts shape memory 20) := by
  let pr := interiorReadHeadRegs regs
  have hp (r : Nat) (h1 : r ≠ 708) (h2 : r ≠ 714) (h3 : r ≠ 717) : pr r = regs r := by
    simp [pr, interiorReadHeadRegs, Registers.write, h1, h2, h3]
  have hpm : MetadataMatches shape pr := by
    intro i hi
    rw [hp _ (by omega) (by omega) (by omega)]
    exact hm i hi
  by_cases hvalid : regs 707 < regs 704
  · have hs := interiorReadValid_source shape memory reader hreader hwrites pr hpm
      (by simp [pr, interiorReadHeadRegs, Registers.write])
      (by simp [pr, interiorReadHeadRegs, Registers.write])
      (by simpa only [hp 705 (by decide) (by decide) (by decide),
        hp 32 (by decide) (by decide) (by decide)] using hcount)
    dsimp only at hs ⊢
    simp only [hp 705 (by decide) (by decide) (by decide), hp 32 (by decide) (by decide) (by decide),
      hp 706 (by decide) (by decide) (by decide), hp 707 (by decide) (by decide) (by decide),
      interiorFoldReceipts_flatMap] at hs
    rw [interiorReadBlock, Block.eval_seq, interiorReadHead_source]
    dsimp only [Evaluation.bind]
    rw [eval_ifZero, if_neg (by simp [interiorReadHeadRegs, Registers.write, hvalid])]
    simpa only [List.nil_append, interiorRequests, if_pos hvalid] using hs
  · have hs := interiorReadInvalid_source shape memory reader hreader pr hpm
    dsimp only at hs ⊢
    simp only [hp 57 (by decide) (by decide) (by decide)] at hs
    rw [interiorReadBlock, Block.eval_seq, interiorReadHead_source]
    dsimp only [Evaluation.bind]
    rw [eval_ifZero, if_pos (by simp [interiorReadHeadRegs, Registers.write, hvalid])]
    have hcollect (word : Option (List Bool)) : collectPayloadWords [word] = word := by
      cases word <;> simp [collectPayloadWords]
    simpa only [List.nil_append, interiorRequests, if_neg hvalid, List.map_cons, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, hcollect] using hs

theorem seven_chunks_of_width (width wordSize : Nat) (hword : 0 < wordSize)
    (hwidth : width ≤ 7 * wordSize) : fixedWidthNatTableMachineChunkCount width wordSize ≤ 7 := by
  have hd : width / wordSize ≤ 7 := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hword).2
    omega
  by_cases hz : width % wordSize = 0
  · simpa [fixedWidthNatTableMachineChunkCount, hz] using hd
  · have hlt : width / wordSize < 7 := by
      by_cases hn : width / wordSize < 7
      · exact hn
      · have heq : width / wordSize = 7 := by omega
        have h := Nat.mod_add_div width wordSize
        rw [heq] at h
        omega
    simp [fixedWidthNatTableMachineChunkCount, hz]
    omega

theorem canonical_interior_chunks_le_seven (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) :
    fixedWidthNatTableMachineChunkCount (packedReviewerInteriorEntryWidth shape.size component)
      (packedBpCodeWordWidth shape.size) ≤ 7 :=
  seven_chunks_of_width _ _ (packedBpCodeWordWidth_pos shape.size) (interiorEntryWidth_le_seven shape component)

theorem consecutiveWordIndices_map_add (base start count : Nat) :
    (consecutiveWordIndices start count).map (fun i => base + i) =
      consecutiveWordIndices (base + start) count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [consecutiveWordIndices, List.map_cons, ih, Nat.add_assoc]

theorem interiorRequests_canonical (shape : CartesianShape) (regs : Registers)
    (hm : MetadataMatches shape regs) :
    interiorRequests regs =
      if regs 707 < regs 704 then fixedWidthNatTableMachineFootprintAt (regs 706) (regs 705)
        (packedBpCodeWordWidth shape.size) (regs 707)
      else [(packedInteriorOffsets shape.size).deadAddress] := by
  have hw : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hdead : regs 57 = (packedInteriorOffsets shape.size).deadAddress := hm 41 (by decide)
  simp only [interiorRequests, hw, hdead, fixedWidthNatTableMachineFootprintAt,
    fixedWidthNatTableMachineFootprint, consecutiveWordIndices_map_add]

theorem flatExecution_readOnly (segment : Nat) (execution : FlatStoreExecution α) :
    ReadOnlyTrace (flatStoreExecutionTraceResultAtSegment segment execution).trace := by
  intro event he
  obtain ⟨read, _hr, rfl⟩ := List.mem_map.mp he
  trivial

theorem logicalTraceReads_flatExecution (shape : CartesianShape) (memory : Memory)
    (segment : Nat) (execution : FlatStoreExecution α) :
    logicalTraceReads shape memory (flatStoreExecutionTraceResultAtSegment segment execution).trace =
      execution.reads.flatMap (fun read => readerReceipts shape memory segment read.1) := by
  simp [logicalTraceReads, flatStoreExecutionTraceResultAtSegment, List.flatMap_map]

theorem interiorReadBlock_reference (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hcount : fixedWidthNatTableMachineChunkCount (regs 705) (packedBpCodeWordWidth shape.size) ≤ 7) :
    let execution := (packedInteriorReadNatOf shape.size (regs 704) (regs 705) (regs 706) (regs 707)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let actual := (interiorReadBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 708 =
      (expected.value.map (· + 1)).getD 0 ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hw : regs 32 = packedBpCodeWordWidth shape.size := hm 16 (by decide)
  have hs := interiorReadBlock_source shape memory reader hreader hwrites regs hm (by simpa only [hw] using hcount)
  dsimp only at hs ⊢
  rw [interiorRequests_canonical shape regs hm] at hs
  refine ⟨hs.1, ?_, ?_, flatExecution_readOnly 20 _⟩
  · dsimp only [flatStoreExecutionTraceResultAtSegment, packedInteriorReadNatOf]
    rw [FlatStoreComputation.map_run_value, FlatStoreComputation.readMany_run_value]
    rw [hs.2.1]
    unfold fixedWidthNatTableMachineDecode
    cases collectPayloadWords _ <;> simp [logicalPacket]
  · rw [logicalTraceReads_flatExecution]
    simp only [packedInteriorReadNatOf, FlatStoreComputation.map_run_reads, FlatStoreComputation.readMany_run_reads,
      List.flatMap_map]
    exact hs.2.2

@[simp] theorem interiorReadBody_size (reader : Block) :
    (interiorReadBody reader).size = 19 + reader.size := by
  simp [interiorReadBody, interiorReadAddress, interiorReadDecode, Block.sequence,
    Block.size, natSubBlock]
  omega

@[simp] theorem interiorReadBlock_size (reader : Block) :
    (interiorReadBlock reader).size = 153 + 8 * reader.size := by
  simp [interiorReadBlock, interiorReadHead, interiorReadInvalid, interiorReadValid,
    interiorReadInit, interiorReadFinish, Block.sequence, Block.size, Nat.mul_add]
  omega

theorem interiorReadBlock_machine (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs)
    (hcount : fixedWidthNatTableMachineChunkCount (regs 705) (packedBpCodeWordWidth shape.size) ≤ 7) :
    let execution := (packedInteriorReadNatOf shape.size (regs 704) (regs 705) (regs 706) (regs 707)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let value := (expected.value.map (· + 1)).getD 0
    let actual := run memory ((interiorReadBlock reader).compileAt 0 ++ [.halt 708])
      (154 + 8 * reader.size) ⟨regs, 0, .running⟩
    actual.result = some value ∧ actual.final.status = .halted value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧
      actual.steps ≤ 154 + 8 * reader.size ∧
      (∀ r, ¬ InteriorReadWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  have hs := interiorReadBlock_reference shape memory reader hreader hwrites regs hm hcount
  have hc := (interiorReadBlock reader).compile_with_halt memory 708 ⟨regs, 0, .running⟩ rfl
  dsimp only [Data.ofState] at hs hc ⊢
  rw [hs.1] at hc
  have hsize : (interiorReadBlock reader).size + 1 = 154 + 8 * reader.size := by
    rw [interiorReadBlock_size]; omega
  rw [hsize] at hc
  have hd := hc.1
  simp only [Block.eval, hs.1] at hd
  refine ⟨hc.2.1.trans (congrArg some hs.2.1), ?_, hc.2.2.1.trans hs.2.2.1,
    ?_, ?_, hs.2.2.2⟩
  · exact (congrArg Data.status hd).trans (congrArg Status.halted hs.2.1)
  · simpa only [List.length_append, Block.compile_length, List.length_singleton, hsize] using hc.2.2.2
  · intro r hr
    exact (congrArg (fun d : Data => d.regs r) hd).trans
      (interiorReadBlock_frame reader hwrites memory _ r hr)

/-- Every canonical interior field width fits the seven-copy reader, including
the widest sparse-level fields. Entry indices remain arbitrary. -/
theorem interiorReadBlock_canonical_machine (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) (regs : Registers)
    (hm : MetadataMatches shape regs)
    (hwidth : regs 705 = packedReviewerInteriorEntryWidth shape.size component) :
    let execution := (packedInteriorReadNatOf shape.size (regs 704) (regs 705) (regs 706) (regs 707)).run
      ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
    let expected := flatStoreExecutionTraceResultAtSegment 20 execution
    let value := (expected.value.map (· + 1)).getD 0
    let actual := run (shapeMemory shape)
      ((interiorReadBlock logicalReadBlock).compileAt 0 ++ [.halt 708]) 8698 ⟨regs, 0, .running⟩
    actual.result = some value ∧ actual.final.status = .halted value ∧
      actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      actual.steps ≤ 8698 ∧
      (∀ r, ¬ InteriorReadWrites r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace := by
  exact interiorReadBlock_machine shape (shapeMemory shape) logicalReadBlock
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly regs hm
    (by rw [hwidth]; exact canonical_interior_chunks_le_seven shape component)

end RMQ.SuccinctFinal.PackedWordRAM
