import RMQ.Core.WordRAM.Packed.FringeProof
import RMQ.Core.WordRAM.Packed.SelectProof

/-! # Charged fringe and interior composition for close LCA -/

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

private theorem eval_seq_of_results (memory : Memory) (first second : Block) (s : Data)
    (a b : Evaluation) (ha : first.eval memory s = a)
    (hb : second.eval memory a.final = b) :
    (Block.seq first second).eval memory s = ⟨b.final, a.reads ++ b.reads⟩ := by
  rw [Block.eval_seq, ha]
  simp only [Evaluation.bind, hb]

def LCAPrepareWrites (r : Nat) : Prop := (1104 ≤ r ∧ r < 1107) ∨ r = 1215

theorem lcaSamePrepareBlock_writes : lcaSamePrepareBlock.WritesOnly LCAPrepareWrites := by
  simp [lcaSamePrepareBlock, Block.sequence, Block.WritesOnly, Action.destination,
    natSubBlock, LCAPrepareWrites]

theorem lcaSamePrepareBlock_source (memory : Memory) (regs : Registers) (hone : regs 1214 = 1) :
    let actual := lcaSamePrepareBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1104 = regs 1200 ∧ actual.final.regs 1105 = regs 1200 + 1 ∧
      actual.final.regs 1106 = regs 1201 - regs 1200 + 1 := by
  have hsub (r : Registers) := natSubBlock_source 1106 1201 1200 1215 memory r (by decide) (by decide)
  simp [lcaSamePrepareBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_arithmetic, eval_skip, Arithmetic.eval, Registers.write, hsub, hone]

theorem lcaCrossLeftPrepareBlock_writes : lcaCrossLeftPrepareBlock.WritesOnly LCAPrepareWrites := by
  simp [lcaCrossLeftPrepareBlock, Block.sequence, Block.WritesOnly, Action.destination,
    natSubBlock, LCAPrepareWrites]

theorem lcaCrossLeftPrepareBlock_source (memory : Memory) (regs : Registers) (hone : regs 1214 = 1) :
    let actual := lcaCrossLeftPrepareBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1104 = regs 1200 ∧ actual.final.regs 1105 = regs 1200 + 1 ∧
      actual.final.regs 1106 = regs 1203 * regs 33 + regs 33 - regs 1200 := by
  have hsub (r : Registers) := natSubBlock_source 1106 1106 1200 1215 memory r (by decide) (by decide)
  simp [lcaCrossLeftPrepareBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_arithmetic, eval_skip, Arithmetic.eval, Registers.write, hsub, hone]

theorem lcaCrossRightPrepareBlock_writes : lcaCrossRightPrepareBlock.WritesOnly LCAPrepareWrites := by
  simp [lcaCrossRightPrepareBlock, Block.sequence, Block.WritesOnly, Action.destination,
    natSubBlock, LCAPrepareWrites]

theorem lcaCrossRightPrepareBlock_source (memory : Memory) (regs : Registers) :
    let actual := lcaCrossRightPrepareBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1104 = regs 1201 ∧ actual.final.regs 1105 = regs 1204 * regs 33 ∧
      actual.final.regs 1106 = regs 1201 - regs 1204 * regs 33 + 2 := by
  have hsub (r : Registers) := natSubBlock_source 1106 1201 1105 1215 memory r (by decide) (by decide)
  simp [lcaCrossRightPrepareBlock, Block.sequence, Block.eval_seq, Evaluation.bind,
    eval_move, eval_constant, eval_arithmetic, eval_skip, Arithmetic.eval, Registers.write, hsub]

theorem lcaInitBlock_writes : lcaInitBlock.WritesOnly
    (fun r => (1202 ≤ r ∧ r < 1205) ∨ r = 1214 ∨ r = 1215) := by
  simp [lcaInitBlock, Block.sequence, Block.WritesOnly, Action.destination]

theorem lcaInitBlock_source (memory : Memory) (regs : Registers) :
    let actual := lcaInitBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 1202 = 0 ∧
      actual.final.regs 1214 = 1 ∧ actual.final.regs 1203 = regs 1200 / regs 33 ∧
      actual.final.regs 1204 = regs 1201 / regs 33 ∧
      actual.final.regs 1215 = if regs 1200 / regs 33 = regs 1201 / regs 33 then 1 else 0 := by
  simp [lcaInitBlock, Block.sequence, Block.eval_seq, Evaluation.bind, eval_constant,
    eval_arithmetic, eval_comparison, eval_skip, Arithmetic.eval, Comparison.eval, Registers.write]

theorem lcaFinishBlock_writes : lcaFinishBlock.WritesOnly (fun r => r = 1202 ∨ r = 1215) := by
  simp [lcaFinishBlock, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock]

theorem lcaFinishBlock_source (memory : Memory) (regs : Registers)
    (hzero : regs 1202 = 0) (hone : regs 1214 = 1) :
    let actual := lcaFinishBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1202 = optionNatPacket (bpCandidateClose? (candidateOfRegs 7000 regs)) := by
  have hsub (r : Registers) := natSubBlock_source 1202 7002 1214 1215 memory r (by decide) (by decide)
  by_cases hz : regs 7000 = 0 <;>
    simp [lcaFinishBlock, eval_ifZero, Block.sequence, Block.eval_seq, Evaluation.bind,
      hsub, eval_arithmetic, eval_skip, Arithmetic.eval, Registers.write, hz, hone, hzero,
      optionNatPacket, bpCandidateClose?, candidateOfRegs]

def LCASameWrites (r : Nat) : Prop := LCAPrepareWrites r ∨ FringeWrites r

theorem lcaSameBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (lcaSameBlock reader).WritesOnly LCASameWrites :=
  ⟨Block.WritesOnly.mono _ lcaSamePrepareBlock_writes (by intro r h; exact Or.inl h),
   Block.WritesOnly.mono _ (fringeBlock_writes reader hwrites) (by intro r h; exact Or.inr h)⟩

theorem lcaSameBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1214 = 1) :
    let expected := fringeReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1200) (regs 1200 + 1) (regs 1201 - regs 1200 + 1)
    let actual := (lcaSameBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := lcaSamePrepareBlock_source memory regs hone
  have hpf (r : Nat) (ho : ¬ LCAPrepareWrites r) :=
    Block.eval_frame memory _ _ lcaSamePrepareBlock_writes r ho ⟨regs, .running⟩
  generalize hep : lcaSamePrepareBlock.eval memory ⟨regs, .running⟩ = prepared at hp hpf
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hpf
  obtain ⟨hpst, hpreads, hclose, hstart, hspan⟩ := hp
  subst pst
  subst preads
  have hpm : MetadataMatches shape pr := by
    intro i hi
    rw [hpf _ (by unfold LCAPrepareWrites; omega)]
    exact hm i hi
  have hf := fringeBlock_source shape memory reader hreader hwrites pr hpm
  generalize hef : (fringeBlock reader).eval memory ⟨pr, .running⟩ = fringed at hf
  rcases fringed with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfvalue, hfreads, hfreadonly⟩ := hf
  subst fst
  have heval := eval_seq_of_results memory lcaSamePrepareBlock (fringeBlock reader)
    ⟨regs, .running⟩ ⟨⟨pr, .running⟩, []⟩ ⟨⟨fr, .running⟩, freads⟩ hep hef
  simp only [List.nil_append] at heval
  change (lcaSameBlock reader).eval memory ⟨regs, .running⟩ = _ at heval
  rw [heval]
  simp only [hclose, hstart, hspan] at hfvalue hfreads hfreadonly
  exact ⟨rfl, hfvalue, hfreads, hfreadonly⟩

private theorem preparedFringe_source (shape : CartesianShape) (memory : Memory)
    (reader prepare : Block) (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hpwrites : prepare.WritesOnly LCAPrepareWrites) (regs : Registers)
    (hm : MetadataMatches shape regs) (close start span : Nat)
    (hp : let actual := prepare.eval memory ⟨regs, .running⟩
      actual.final.status = .running ∧ actual.reads = [] ∧
        actual.final.regs 1104 = close ∧ actual.final.regs 1105 = start ∧
        actual.final.regs 1106 = span) :
    let expected := fringeReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size close start span
    let actual := (Block.seq prepare (fringeBlock reader)).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hpf (r : Nat) (ho : ¬ LCAPrepareWrites r) :=
    Block.eval_frame memory prepare _ hpwrites r ho ⟨regs, .running⟩
  generalize hep : prepare.eval memory ⟨regs, .running⟩ = prepared at hp hpf
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hpf
  obtain ⟨hpst, hpreads, hclose, hstart, hspan⟩ := hp
  subst pst
  subst preads
  have hpm : MetadataMatches shape pr := by
    intro i hi
    rw [hpf _ (by unfold LCAPrepareWrites; omega)]
    exact hm i hi
  have hf := fringeBlock_source shape memory reader hreader hwrites pr hpm
  generalize hef : (fringeBlock reader).eval memory ⟨pr, .running⟩ = fringed at hf
  rcases fringed with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfvalue, hfreads, hfreadonly⟩ := hf
  subst fst
  have heval := eval_seq_of_results memory prepare (fringeBlock reader)
    ⟨regs, .running⟩ ⟨⟨pr, .running⟩, []⟩ ⟨⟨fr, .running⟩, freads⟩ hep hef
  simp only [List.nil_append] at heval
  rw [heval]
  simp only [hclose, hstart, hspan] at hfvalue hfreads hfreadonly
  exact ⟨rfl, hfvalue, hfreads, hfreadonly⟩

private theorem eval_seq_assoc (memory : Memory) (a b c : Block) (s : Data) :
    (Block.seq a (.seq b c)).eval memory s = (Block.seq (.seq a b) c).eval memory s := by
  simp only [Block.eval_seq, Evaluation.bind, List.append_assoc]

def LCALeftWrites (r : Nat) : Prop := LCASameWrites r ∨ (1205 ≤ r ∧ r < 1208)

theorem lcaCrossLeftBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (lcaCrossLeftBlock reader).WritesOnly LCALeftWrites := by
  refine ⟨Block.WritesOnly.mono _ lcaCrossLeftPrepareBlock_writes ?_,
    Block.WritesOnly.mono _ (fringeBlock_writes reader hwrites) ?_, ?_⟩
  · intro r h; exact Or.inl (Or.inl h)
  · intro r h; exact Or.inl (Or.inr h)
  · simp [candidateSaveBlock, Block.sequence, Block.WritesOnly, Action.destination, LCALeftWrites]

theorem lcaCrossLeftBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1214 = 1) :
    let expected := fringeReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1200) (regs 1200 + 1) (regs 1203 * regs 33 + regs 33 - regs 1200)
    let actual := (lcaCrossLeftBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 1205 actual.final.regs = expected.value ∧
      candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hf := preparedFringe_source shape memory reader lcaCrossLeftPrepareBlock hreader hwrites
    lcaCrossLeftPrepareBlock_writes regs hm _ _ _ (lcaCrossLeftPrepareBlock_source memory regs hone)
  generalize hef : (Block.seq lcaCrossLeftPrepareBlock (fringeBlock reader)).eval memory
    ⟨regs, .running⟩ = fringed at hf
  rcases fringed with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfvalue, hfreads, hfreadonly⟩ := hf
  subst fst
  have hs := candidateSaveBlock_source 1205 (by decide) memory fr
  generalize hes : (candidateSaveBlock 1205).eval memory ⟨fr, .running⟩ = saved at hs
  rcases saved with ⟨⟨sr, sst⟩, sreads⟩
  dsimp only at hs
  obtain ⟨hsst, hsreads, hsaved, hglobal⟩ := hs
  subst sst
  subst sreads
  have heval := eval_seq_of_results memory (.seq lcaCrossLeftPrepareBlock (fringeBlock reader))
    (candidateSaveBlock 1205) ⟨regs, .running⟩ ⟨⟨fr, .running⟩, freads⟩ ⟨⟨sr, .running⟩, []⟩ hef hes
  simp only [List.append_nil] at heval
  rw [lcaCrossLeftBlock, eval_seq_assoc, heval]
  exact ⟨rfl, hsaved.trans hfvalue, hglobal.trans hfvalue, hfreads, hfreadonly⟩

def LCARightWrites (r : Nat) : Prop := LCASameWrites r ∨ (7000 ≤ r ∧ r < 7004)

theorem lcaCrossRightBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (lcaCrossRightBlock reader).WritesOnly LCARightWrites := by
  refine ⟨Block.WritesOnly.mono _ lcaCrossRightPrepareBlock_writes ?_,
    Block.WritesOnly.mono _ (fringeBlock_writes reader hwrites) ?_,
    Block.WritesOnly.mono _ (candidateMergeLeftBlock_writesOnly 1208) ?_⟩
  · intro r h; exact Or.inl (Or.inl h)
  · intro r h; exact Or.inl (Or.inr h)
  · intro r h; unfold LCARightWrites; omega

theorem lcaCrossRightBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := fringeReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1201) (regs 1204 * regs 33) (regs 1201 - regs 1204 * regs 33 + 2)
    let actual := (lcaCrossRightBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs =
      bpCandidateMerge? (candidateOfRegs 1208 regs) expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hf := preparedFringe_source shape memory reader lcaCrossRightPrepareBlock hreader hwrites
    lcaCrossRightPrepareBlock_writes regs hm _ _ _ (lcaCrossRightPrepareBlock_source memory regs)
  have hframe (r : Nat) (ho : ¬ LCASameWrites r) :=
    Block.eval_frame memory (.seq lcaCrossRightPrepareBlock (fringeBlock reader)) LCASameWrites
      ⟨Block.WritesOnly.mono _ lcaCrossRightPrepareBlock_writes (by intro r h; exact Or.inl h),
        Block.WritesOnly.mono _ (fringeBlock_writes reader hwrites) (by intro r h; exact Or.inr h)⟩
      r ho ⟨regs, .running⟩
  generalize hef : (Block.seq lcaCrossRightPrepareBlock (fringeBlock reader)).eval memory
    ⟨regs, .running⟩ = fringed at hf hframe
  rcases fringed with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf hframe
  obtain ⟨hfst, hfvalue, hfreads, hfreadonly⟩ := hf
  subst fst
  have hs := candidateMergeLeftBlock_source 1208 (by decide) memory fr
  generalize hes : (candidateMergeLeftBlock 1208).eval memory ⟨fr, .running⟩ = merged at hs
  rcases merged with ⟨⟨mr, mst⟩, mreads⟩
  dsimp only at hs
  obtain ⟨hmst, hmreads, hmvalue⟩ := hs
  subst mst
  subst mreads
  have heval := eval_seq_of_results memory (.seq lcaCrossRightPrepareBlock (fringeBlock reader))
    (candidateMergeLeftBlock 1208) ⟨regs, .running⟩ ⟨⟨fr, .running⟩, freads⟩ ⟨⟨mr, .running⟩, []⟩ hef hes
  simp only [List.append_nil] at heval
  rw [lcaCrossRightBlock, eval_seq_assoc, heval]
  refine ⟨rfl, ?_, hfreads, hfreadonly⟩
  rw [hmvalue, hfvalue]
  have hout (r : Nat) (hr : 1208 ≤ r ∧ r < 1211) : ¬ LCASameWrites r := by
    unfold LCASameWrites LCAPrepareWrites FringeWrites FringeSeedWrites RankWrapperWrites
      FringeWindowWrites WindowWrites FringeFoldWrites
    omega
  simp only [candidateOfRegs, hframe 1208 (hout _ (by decide)), hframe 1209 (hout _ (by decide)),
    hframe 1210 (hout _ (by decide))]

def LCAInteriorWrites (r : Nat) : Prop :=
  (704 ≤ r ∧ r < 912) ∨ (7000 ≤ r ∧ r < 7004) ∨ (8192 ≤ r ∧ r < 8271)

def InteriorCandidateCorrect (shape : CartesianShape) (memory : Memory) (interior : Block) : Prop :=
  ∀ regs : Registers, MetadataMatches shape regs →
    let actual := interior.eval memory ⟨regs, .running⟩
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace

theorem lcaCrossMiddleInitBlock_writes :
    lcaCrossMiddleInitBlock.WritesOnly (fun r => r = 896 ∨ r = 1215) := by
  simp [lcaCrossMiddleInitBlock, Block.sequence, Block.WritesOnly, Action.destination]

theorem lcaCrossMiddleInitBlock_source (memory : Memory) (regs : Registers) (hone : regs 1214 = 1) :
    let actual := lcaCrossMiddleInitBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 896 = regs 1203 + 1 ∧
      actual.final.regs 1215 = if regs 1203 + 1 < regs 1204 then 1 else 0 := by
  simp [lcaCrossMiddleInitBlock, Block.sequence, Block.eval_seq, Evaluation.bind, eval_arithmetic,
    eval_comparison, eval_skip, Arithmetic.eval, Comparison.eval, Registers.write, hone]

theorem lcaCrossMiddleCountBlock_writes :
    lcaCrossMiddleCountBlock.WritesOnly (fun r => r = 897 ∨ r = 1215) := by
  simp [lcaCrossMiddleCountBlock, Block.WritesOnly, natSubBlock, Action.destination]

theorem lcaCrossMiddleCountBlock_source (memory : Memory) (regs : Registers) (hone : regs 1214 = 1) :
    let actual := lcaCrossMiddleCountBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 897 = regs 1204 - regs 1203 - 1 := by
  have ha (r : Registers) := natSubBlock_source 897 1204 1203 1215 memory r (by decide) (by decide)
  have hb (r : Registers) := natSubBlock_source 897 897 1214 1215 memory r (by decide) (by decide)
  simp [lcaCrossMiddleCountBlock, Block.eval_seq, Evaluation.bind, ha, hb,
    Registers.write, hone]

def LCAMiddleWrites (r : Nat) : Prop := LCAInteriorWrites r ∨ r = 1215

theorem lcaCrossMiddleProgram_writes (interior : Block)
    (hwrites : interior.WritesOnly LCAInteriorWrites) :
    (lcaCrossMiddleProgram interior).WritesOnly LCAMiddleWrites := by
  refine ⟨Block.WritesOnly.mono _ lcaCrossMiddleInitBlock_writes ?_, ?_,
    Block.WritesOnly.mono _ lcaCrossMiddleCountBlock_writes ?_,
    Block.WritesOnly.mono _ hwrites ?_⟩
  · intro r h; unfold LCAMiddleWrites LCAInteriorWrites; omega
  · simp [candidateNoneBlock, Block.sequence, Block.WritesOnly, Action.destination,
      LCAMiddleWrites, LCAInteriorWrites]
  · intro r h; unfold LCAMiddleWrites LCAInteriorWrites; omega
  · intro r h; exact Or.inl h

private theorem interiorWithCount_source (shape : CartesianShape) (memory : Memory) (interior : Block)
    (hinterior : InteriorCandidateCorrect shape memory interior)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1214 = 1) :
    let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 1204 - regs 1203 - 1)
    let actual := (Block.seq lcaCrossMiddleCountBlock interior).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := lcaCrossMiddleCountBlock_source memory regs hone
  have hpf (r : Nat) (ho : r ≠ 897 ∧ r ≠ 1215) :=
    Block.eval_frame memory _ _ lcaCrossMiddleCountBlock_writes r (by omega) ⟨regs, .running⟩
  generalize hep : lcaCrossMiddleCountBlock.eval memory ⟨regs, .running⟩ = prepared at hp hpf
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hpf
  obtain ⟨hpst, hpreads, hcount⟩ := hp
  subst pst
  subst preads
  have hpm : MetadataMatches shape pr := by
    intro i hi; rw [hpf _ (by omega)]; exact hm i hi
  have hi := hinterior pr hpm
  generalize hei : interior.eval memory ⟨pr, .running⟩ = ranged at hi
  rcases ranged with ⟨⟨ir, ist⟩, ireads⟩
  dsimp only at hi
  obtain ⟨hist, hivalue, hireads, hireadonly⟩ := hi
  subst ist
  have heval := eval_seq_of_results memory lcaCrossMiddleCountBlock interior
    ⟨regs, .running⟩ ⟨⟨pr, .running⟩, []⟩ ⟨⟨ir, .running⟩, ireads⟩ hep hei
  simp only [List.nil_append] at heval
  rw [heval]
  simp only [hcount, hpf 896 (by decide)] at hivalue hireads hireadonly
  exact ⟨rfl, hivalue, hireads, hireadonly⟩

def lcaMiddleReference (store : WordRAM.ReadStore) (n leftBlock rightBlock : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  if leftBlock + 1 < rightBlock then
    packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments store n
      (leftBlock + 1) (rightBlock - leftBlock - 1)
  else WordRAM.TraceResult.pure none

theorem lcaCrossMiddleProgram_source (shape : CartesianShape) (memory : Memory) (interior : Block)
    (hinterior : InteriorCandidateCorrect shape memory interior)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1214 = 1) :
    let expected := lcaMiddleReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1203) (regs 1204)
    let actual := (lcaCrossMiddleProgram interior).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := lcaCrossMiddleInitBlock_source memory regs hone
  have hpf (r : Nat) (ho : r ≠ 896 ∧ r ≠ 1215) :=
    Block.eval_frame memory _ _ lcaCrossMiddleInitBlock_writes r (by omega) ⟨regs, .running⟩
  generalize hep : lcaCrossMiddleInitBlock.eval memory ⟨regs, .running⟩ = prepared at hp hpf
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hpf
  obtain ⟨hpst, hpreads, hstart, htest⟩ := hp
  subst pst
  subst preads
  have hpm : MetadataMatches shape pr := by
    intro i hi; rw [hpf _ (by omega)]; exact hm i hi
  by_cases hactive : regs 1203 + 1 < regs 1204
  · have hi := interiorWithCount_source shape memory interior hinterior pr hpm
      ((hpf 1214 (by decide)).trans hone)
    have htest' : pr 1215 ≠ 0 := by simp only [hactive, if_true] at htest; omega
    rw [lcaCrossMiddleProgram, Block.eval_seq, hep]
    dsimp only [Evaluation.bind]
    rw [eval_ifZero, if_neg htest']
    simp only [lcaMiddleReference, if_pos hactive]
    simpa only [List.nil_append, hstart, hpf 1203 (by decide), hpf 1204 (by decide)] using hi
  · have hn := candidateNoneBlock_source memory pr
    have htest' : pr 1215 = 0 := by simpa only [if_neg hactive] using htest
    rw [lcaCrossMiddleProgram, Block.eval_seq, hep]
    dsimp only [Evaluation.bind]
    rw [eval_ifZero, if_pos htest']
    refine ⟨hn.1, ?_, ?_, ?_⟩
    · simpa only [lcaMiddleReference, if_neg hactive, WordRAM.TraceResult.pure] using hn.2.2
    · simp only [hn.2.1, List.nil_append, lcaMiddleReference, if_neg hactive,
        WordRAM.TraceResult.pure, logicalTraceReads, List.flatMap_nil]
    · simp [lcaMiddleReference, hactive, WordRAM.TraceResult.pure, ReadOnlyTrace]

def LCAMergeSaveWrites (r : Nat) : Prop :=
  (1208 ≤ r ∧ r < 1211) ∨ (7000 ≤ r ∧ r < 7004)

theorem lcaCrossMergeSaveBlock_writes : lcaCrossMergeSaveBlock.WritesOnly LCAMergeSaveWrites := by
  refine ⟨Block.WritesOnly.mono _ (candidateMergeLeftBlock_writesOnly 1205) ?_, ?_⟩
  · intro r h; exact Or.inr h
  · simp [candidateSaveBlock, Block.sequence, Block.WritesOnly, Action.destination, LCAMergeSaveWrites]

theorem lcaCrossMergeSaveBlock_source (memory : Memory) (regs : Registers) :
    let actual := lcaCrossMergeSaveBlock.eval memory ⟨regs, .running⟩
    let expected := bpCandidateMerge? (candidateOfRegs 1205 regs) (candidateOfRegs 7000 regs)
    actual.final.status = .running ∧ actual.reads = [] ∧
      candidateOfRegs 1208 actual.final.regs = expected ∧ candidateOfRegs 7000 actual.final.regs = expected := by
  have hm := candidateMergeLeftBlock_source 1205 (by decide) memory regs
  generalize hem : (candidateMergeLeftBlock 1205).eval memory ⟨regs, .running⟩ = merged at hm
  rcases merged with ⟨⟨mr, mst⟩, mreads⟩
  dsimp only at hm
  obtain ⟨hmst, hmreads, hmvalue⟩ := hm
  subst mst
  subst mreads
  have hs := candidateSaveBlock_source 1208 (by decide) memory mr
  rw [lcaCrossMergeSaveBlock, Block.eval_seq, hem]
  dsimp only [Evaluation.bind]
  exact ⟨hs.1, by simpa only [List.nil_append] using hs.2.1,
    hs.2.2.1.trans hmvalue, hs.2.2.2.trans hmvalue⟩

def lcaCrossCandidateReference (store : WordRAM.ReadStore) (n left right leftBlock rightBlock : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let b := (packedInteriorLayout n).blockSize
  (fringeReference store n left (left + 1) (leftBlock * b + b - left)).bind fun l =>
    (lcaMiddleReference store n leftBlock rightBlock).bind fun m =>
      (fringeReference store n right (rightBlock * b) (right - rightBlock * b + 2)).map
        (bpCandidateMerge3? l m)

def LCACrossWrites (r : Nat) : Prop :=
  LCALeftWrites r ∨ LCAMiddleWrites r ∨ LCAMergeSaveWrites r ∨ LCARightWrites r

theorem lcaCrossProgram_writes (reader interior : Block) (hwrites : ReaderWrites reader)
    (hiwrites : interior.WritesOnly LCAInteriorWrites) :
    (lcaCrossProgram (lcaCrossLeftBlock reader) (lcaCrossMiddleProgram interior)
      (lcaCrossRightBlock reader)).WritesOnly LCACrossWrites := by
  refine ⟨Block.WritesOnly.mono _ (lcaCrossLeftBlock_writes reader hwrites) ?_,
    Block.WritesOnly.mono _ (lcaCrossMiddleProgram_writes interior hiwrites) ?_,
    Block.WritesOnly.mono _ lcaCrossMergeSaveBlock_writes ?_,
    Block.WritesOnly.mono _ (lcaCrossRightBlock_writes reader hwrites) ?_⟩
  · intro r h; exact Or.inl h
  · intro r h; exact Or.inr (Or.inl h)
  · intro r h; exact Or.inr (Or.inr (Or.inl h))
  · intro r h; exact Or.inr (Or.inr (Or.inr h))

private theorem lcaCross_preserves_caller (r : Nat)
    (hr : r < 190 ∨ r = 1200 ∨ r = 1201 ∨ r = 1202 ∨ r = 1203 ∨ r = 1204 ∨ r = 1214) :
    ¬ LCACrossWrites r := by
  unfold LCACrossWrites LCALeftWrites LCAMiddleWrites LCAMergeSaveWrites LCARightWrites
    LCASameWrites LCAPrepareWrites LCAInteriorWrites FringeWrites FringeSeedWrites
    RankWrapperWrites FringeWindowWrites WindowWrites FringeFoldWrites
  omega

theorem lcaCrossProgram_source (shape : CartesianShape) (memory : Memory) (reader interior : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hinterior : InteriorCandidateCorrect shape memory interior)
    (hiwrites : interior.WritesOnly LCAInteriorWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1214 = 1) :
    let expected := lcaCrossCandidateReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1200) (regs 1201) (regs 1203) (regs 1204)
    let actual := (lcaCrossProgram (lcaCrossLeftBlock reader) (lcaCrossMiddleProgram interior)
      (lcaCrossRightBlock reader)).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hl := lcaCrossLeftBlock_source shape memory reader hreader hwrites regs hm hone
  have hlf (r : Nat) (ho : ¬ LCALeftWrites r) :=
    Block.eval_frame memory _ _ (lcaCrossLeftBlock_writes reader hwrites) r ho ⟨regs, .running⟩
  generalize hel : (lcaCrossLeftBlock reader).eval memory ⟨regs, .running⟩ = leftRun at hl hlf
  rcases leftRun with ⟨⟨lr, lst⟩, lreads⟩
  dsimp only at hl hlf
  obtain ⟨hlst, hlsaved, hlvalue, hlreads, hlreadonly⟩ := hl
  subst lst
  have hlkeep (r : Nat) (hr : r < 190 ∨ r = 1200 ∨ r = 1201 ∨ r = 1202 ∨ r = 1203 ∨ r = 1204 ∨ r = 1214) :
      lr r = regs r := hlf r (by intro h; exact lcaCross_preserves_caller r hr (Or.inl h))
  have hlm : MetadataMatches shape lr := by
    intro i hi; rw [hlkeep _ (Or.inl (by omega))]; exact hm i hi
  have hmid := lcaCrossMiddleProgram_source shape memory interior hinterior lr hlm
    ((hlkeep 1214 (by simp)).trans hone)
  have hmf (r : Nat) (ho : ¬ LCAMiddleWrites r) :=
    Block.eval_frame memory _ _ (lcaCrossMiddleProgram_writes interior hiwrites) r ho ⟨lr, .running⟩
  generalize hem : (lcaCrossMiddleProgram interior).eval memory ⟨lr, .running⟩ = middleRun at hmid hmf
  rcases middleRun with ⟨⟨mr, mst⟩, mreads⟩
  dsimp only at hmid hmf
  obtain ⟨hmst, hmvalue, hmreads, hmreadonly⟩ := hmid
  subst mst
  have hmkeep (r : Nat) (hr : r < 190 ∨ r = 1200 ∨ r = 1201 ∨ r = 1202 ∨ r = 1203 ∨ r = 1204 ∨ r = 1214) :
      mr r = regs r := (hmf r (by intro h; exact lcaCross_preserves_caller r hr (Or.inr (Or.inl h)))).trans (hlkeep r hr)
  have hmsaved : candidateOfRegs 1205 mr = candidateOfRegs 1205 lr := by
    simp only [candidateOfRegs, hmf 1205 (by simp [LCAMiddleWrites, LCAInteriorWrites]),
      hmf 1206 (by simp [LCAMiddleWrites, LCAInteriorWrites]),
      hmf 1207 (by simp [LCAMiddleWrites, LCAInteriorWrites])]
  have hs := lcaCrossMergeSaveBlock_source memory mr
  have hsf (r : Nat) (ho : ¬ LCAMergeSaveWrites r) :=
    Block.eval_frame memory _ _ lcaCrossMergeSaveBlock_writes r ho ⟨mr, .running⟩
  generalize hes : lcaCrossMergeSaveBlock.eval memory ⟨mr, .running⟩ = savedRun at hs hsf
  rcases savedRun with ⟨⟨sr, sst⟩, sreads⟩
  dsimp only at hs hsf
  obtain ⟨hsst, hsreads, hssaved, hsvalue⟩ := hs
  subst sst
  subst sreads
  have hskeep (r : Nat) (hr : r < 190 ∨ r = 1200 ∨ r = 1201 ∨ r = 1202 ∨ r = 1203 ∨ r = 1204 ∨ r = 1214) :
      sr r = regs r := (hsf r (by intro h; exact lcaCross_preserves_caller r hr (Or.inr (Or.inr (Or.inl h))))).trans (hmkeep r hr)
  have hsm : MetadataMatches shape sr := by
    intro i hi; rw [hskeep _ (Or.inl (by omega))]; exact hm i hi
  have hr := lcaCrossRightBlock_source shape memory reader hreader hwrites sr hsm
  generalize her : (lcaCrossRightBlock reader).eval memory ⟨sr, .running⟩ = rightRun at hr
  rcases rightRun with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr
  obtain ⟨hrst, hrvalue, hrreads, hrreadonly⟩ := hr
  subst rst
  have hlast := eval_seq_of_results memory lcaCrossMergeSaveBlock (lcaCrossRightBlock reader)
    ⟨mr, .running⟩ ⟨⟨sr, .running⟩, []⟩ ⟨⟨rr, .running⟩, rreads⟩ hes her
  simp only [List.nil_append] at hlast
  have hmiddle := eval_seq_of_results memory (lcaCrossMiddleProgram interior)
    (.seq lcaCrossMergeSaveBlock (lcaCrossRightBlock reader))
    ⟨lr, .running⟩ ⟨⟨mr, .running⟩, mreads⟩ ⟨⟨rr, .running⟩, rreads⟩ hem hlast
  have hwhole := eval_seq_of_results memory (lcaCrossLeftBlock reader)
    (.seq (lcaCrossMiddleProgram interior) (.seq lcaCrossMergeSaveBlock (lcaCrossRightBlock reader)))
    ⟨regs, .running⟩ ⟨⟨lr, .running⟩, lreads⟩ ⟨⟨rr, .running⟩, mreads ++ rreads⟩ hel hmiddle
  change (lcaCrossProgram (lcaCrossLeftBlock reader) (lcaCrossMiddleProgram interior)
    (lcaCrossRightBlock reader)).eval memory ⟨regs, .running⟩ = _ at hwhole
  rw [hwhole]
  dsimp only
  have hb : regs 33 = (packedInteriorLayout shape.size).blockSize := hm 17 (by decide)
  simp only [hlkeep 1203 (by simp), hlkeep 1204 (by simp)] at hmvalue hmreads hmreadonly
  rw [hssaved, hmsaved, hlsaved, hmvalue] at hrvalue
  simp only [hskeep 1201 (by simp), hskeep 1204 (by simp), hskeep 33 (by decide), hb]
    at hrvalue hrreads hrreadonly
  simp only [hb] at hlreads hlreadonly
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa only [lcaCrossCandidateReference, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, bpCandidateMerge3?, hb] using hrvalue
  · simp only [lcaCrossCandidateReference, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, List.append_nil, rank_logicalTraceReads_append]
    rw [hlreads, hmreads, hrreads]
  · simp only [lcaCrossCandidateReference, WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
      WordRAM.TraceResult.pure, List.append_nil, ReadOnlyTrace, List.mem_append]
    intro e he
    rcases he with he | he | he
    · exact hlreadonly e he
    · exact hmreadonly e he
    · exact hrreadonly e he

theorem lcaCrossCandidateReference_close (store : WordRAM.ReadStore) (n left right : Nat) :
    (lcaCrossCandidateReference store n left right
      (left / (packedInteriorLayout n).blockSize) (right / (packedInteriorLayout n).blockSize)).map bpCandidateClose? =
      packedCrossBlockCloseRead (packedRankCloseLeaf store n) concreteBPNativeInteriorTraceSegments
        21 store n left right := by
  simp [lcaCrossCandidateReference, lcaMiddleReference, fringeReference, fringeWindowReference,
    packedCrossBlockCloseRead, packedLeftFringeCandidateRead, packedRightFringeCandidateRead,
    WordRAM.TraceResult.bind, WordRAM.TraceResult.map, WordRAM.TraceResult.pure,
    blockOfClose, blockStartOf, packedInteriorLayout, List.append_assoc]

def lcaCandidateReference (store : WordRAM.ReadStore) (n left right : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  let b := (packedInteriorLayout n).blockSize
  if left / b = right / b then fringeReference store n left (left + 1) (right - left + 1)
  else lcaCrossCandidateReference store n left right (left / b) (right / b)

theorem lcaCandidateReference_close (store : WordRAM.ReadStore) (n left right : Nat) :
    (lcaCandidateReference store n left right).map bpCandidateClose? =
      packedLcaCloseLeaf store n left right := by
  have hb : (packedInteriorLayout n).blockSize = packedSummaryBlockSizeRaw n := rfl
  by_cases heq : left / (packedInteriorLayout n).blockSize = right / (packedInteriorLayout n).blockSize
  · simp only [lcaCandidateReference, if_pos heq, fringeReference_sameBlock]
    simp only [packedLcaCloseLeaf, packedLcaCloseRead, blockOfClose, ← hb, if_pos heq]
    rfl
  · simp only [lcaCandidateReference, if_neg heq, lcaCrossCandidateReference_close]
    simp only [packedLcaCloseLeaf, packedLcaCloseRead, blockOfClose, ← hb, if_neg heq]
    rfl

def LCAChooseWrites (r : Nat) : Prop := LCACrossWrites r ∨ LCASameWrites r

theorem lcaChooseProgram_writes (reader interior : Block) (hwrites : ReaderWrites reader)
    (hiwrites : interior.WritesOnly LCAInteriorWrites) :
    (lcaChooseProgram reader interior).WritesOnly LCAChooseWrites :=
  ⟨Block.WritesOnly.mono _ (lcaCrossProgram_writes reader interior hwrites hiwrites) (by intro r h; exact Or.inl h),
   Block.WritesOnly.mono _ (lcaSameBlock_writes reader hwrites) (by intro r h; exact Or.inr h)⟩

private theorem lcaChoose_preserves_caller (r : Nat)
    (hr : r < 190 ∨ r = 1200 ∨ r = 1201 ∨ r = 1202 ∨ r = 1203 ∨ r = 1204 ∨ r = 1214) :
    ¬ LCAChooseWrites r := by
  intro h
  rcases h with h | h
  · exact lcaCross_preserves_caller r hr h
  · exact lcaCross_preserves_caller r hr (Or.inl (Or.inl h))

theorem lcaChooseProgram_source (shape : CartesianShape) (memory : Memory) (reader interior : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hinterior : InteriorCandidateCorrect shape memory interior)
    (hiwrites : interior.WritesOnly LCAInteriorWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 1214 = 1)
    (hl : regs 1203 = regs 1200 / regs 33) (hr : regs 1204 = regs 1201 / regs 33)
    (htest : regs 1215 = if regs 1203 = regs 1204 then 1 else 0) :
    let expected := lcaCandidateReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1200) (regs 1201)
    let actual := (lcaChooseProgram reader interior).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hb : regs 33 = (packedInteriorLayout shape.size).blockSize := hm 17 (by decide)
  by_cases heq : regs 1203 = regs 1204
  · have htest' : regs 1215 ≠ 0 := by simp only [if_pos heq] at htest; omega
    have hsame := lcaSameBlock_source shape memory reader hreader hwrites regs hm hone
    have heq' : regs 1200 / (packedInteriorLayout shape.size).blockSize =
        regs 1201 / (packedInteriorLayout shape.size).blockSize := by simpa only [hl, hr, hb] using heq
    rw [lcaChooseProgram, eval_ifZero, if_neg htest']
    simpa only [lcaCandidateReference, if_pos heq'] using hsame
  · have htest' : regs 1215 = 0 := by simpa only [if_neg heq] using htest
    have hcross := lcaCrossProgram_source shape memory reader interior hreader hwrites hinterior hiwrites regs hm hone
    have heq' : regs 1200 / (packedInteriorLayout shape.size).blockSize ≠
        regs 1201 / (packedInteriorLayout shape.size).blockSize := by simpa only [hl, hr, hb] using heq
    rw [lcaChooseProgram, eval_ifZero, if_pos htest']
    simpa only [lcaCandidateReference, if_neg heq', hl, hr, hb] using hcross

def LCACloseWrites (r : Nat) : Prop :=
  LCAChooseWrites r ∨ (1202 ≤ r ∧ r < 1205) ∨ r = 1214 ∨ r = 1215

theorem lcaCloseProgram_writes (reader interior : Block) (hwrites : ReaderWrites reader)
    (hiwrites : interior.WritesOnly LCAInteriorWrites) :
    (lcaCloseProgram reader interior).WritesOnly LCACloseWrites := by
  refine ⟨Block.WritesOnly.mono _ lcaInitBlock_writes ?_,
    Block.WritesOnly.mono _ (lcaChooseProgram_writes reader interior hwrites hiwrites) ?_,
    Block.WritesOnly.mono _ lcaFinishBlock_writes ?_⟩
  · intro r h; unfold LCACloseWrites; omega
  · intro r h; exact Or.inl h
  · intro r h; unfold LCACloseWrites; omega

theorem lcaCloseProgram_source (shape : CartesianShape) (memory : Memory) (reader interior : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hinterior : InteriorCandidateCorrect shape memory interior)
    (hiwrites : interior.WritesOnly LCAInteriorWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedLcaCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1200) (regs 1201)
    let actual := (lcaCloseProgram reader interior).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 1202 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hi := lcaInitBlock_source memory regs
  have hif (r : Nat) (ho : r < 1202 ∨ (1205 ≤ r ∧ r ≠ 1214 ∧ r ≠ 1215)) :=
    Block.eval_frame memory _ _ lcaInitBlock_writes r (by omega) ⟨regs, .running⟩
  generalize hei : lcaInitBlock.eval memory ⟨regs, .running⟩ = initialized at hi hif
  rcases initialized with ⟨⟨ir, ist⟩, ireads⟩
  dsimp only at hi hif
  obtain ⟨hist, hireads, hizero, hione, hileft, hiright, hitest⟩ := hi
  subst ist
  subst ireads
  have him : MetadataMatches shape ir := by
    intro i hi; rw [hif _ (Or.inl (by omega))]; exact hm i hi
  have hc := lcaChooseProgram_source shape memory reader interior hreader hwrites hinterior hiwrites ir him hione
    (by rw [hif 1200 (by decide), hif 33 (by decide)]; exact hileft)
    (by rw [hif 1201 (by decide), hif 33 (by decide)]; exact hiright)
    (by rw [hileft, hiright]; exact hitest)
  have hcf (r : Nat) (hr : r < 190 ∨ r = 1200 ∨ r = 1201 ∨ r = 1202 ∨ r = 1203 ∨ r = 1204 ∨ r = 1214) :=
    Block.eval_frame memory _ _ (lcaChooseProgram_writes reader interior hwrites hiwrites)
      r (lcaChoose_preserves_caller r hr) ⟨ir, .running⟩
  generalize hec : (lcaChooseProgram reader interior).eval memory ⟨ir, .running⟩ = chosen at hc hcf
  rcases chosen with ⟨⟨cr, cst⟩, creads⟩
  dsimp only at hc hcf
  obtain ⟨hcst, hcvalue, hcreads, hcreadonly⟩ := hc
  subst cst
  have hf := lcaFinishBlock_source memory cr ((hcf 1202 (by simp)).trans hizero)
    ((hcf 1214 (by simp)).trans hione)
  generalize hef : lcaFinishBlock.eval memory ⟨cr, .running⟩ = finished at hf
  rcases finished with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfreads, hfvalue⟩ := hf
  subst fst
  subst freads
  have htail := eval_seq_of_results memory (lcaChooseProgram reader interior) lcaFinishBlock
    ⟨ir, .running⟩ ⟨⟨cr, .running⟩, creads⟩ ⟨⟨fr, .running⟩, []⟩ hec hef
  simp only [List.append_nil] at htail
  have hwhole := eval_seq_of_results memory lcaInitBlock (.seq (lcaChooseProgram reader interior) lcaFinishBlock)
    ⟨regs, .running⟩ ⟨⟨ir, .running⟩, []⟩ ⟨⟨fr, .running⟩, creads⟩ hei htail
  simp only [List.nil_append] at hwhole
  change (lcaCloseProgram reader interior).eval memory ⟨regs, .running⟩ = _ at hwhole
  rw [hwhole]
  dsimp only
  simp only [hif 1200 (by decide), hif 1201 (by decide)] at hcvalue hcreads hcreadonly
  rw [hcvalue] at hfvalue
  have href := lcaCandidateReference_close (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    shape.size (regs 1200) (regs 1201)
  have hv := congrArg WordRAM.TraceResult.value href
  have ht := congrArg WordRAM.TraceResult.trace href
  simp only [WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
    List.append_nil] at hv ht
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa only [hv] using hfvalue
  · simpa only [ht] using hcreads
  · simpa only [ht] using hcreadonly

end RMQ.SuccinctFinal.PackedWordRAM
