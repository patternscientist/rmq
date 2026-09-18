import RMQ.Core.WordRAM.Packed.ReadInterface

/-! # Shape-free proof interface for the shared rank and select controllers

The model below is a proof parameter. Executable blocks remain the existing
Packed blocks, and obtain their answers only from their supplied reader.
-/

namespace RMQ.PackedBitvector.Controller

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

structure ControllerModel where
  metadata : Registers
  store : WordRAM.ReadStore
  receipts : Nat → Nat → List Receipt

def MetadataMatches (model : ControllerModel) (regs : Registers) : Prop :=
  ∀ r < 190, regs r = model.metadata r

def traceReads (receipts : Nat → Nat → List Receipt)
    (trace : List WordRAM.TraceEvent) : List Receipt :=
  trace.flatMap fun event => match event with
    | .readWord segment index _ => receipts segment index
    | _ => []

def logicalTraceReads (model : ControllerModel) (_memory : Memory)
    (trace : List WordRAM.TraceEvent) : List Receipt :=
  traceReads model.receipts trace

def ReaderSimulation (model : ControllerModel) (memory : Memory) (reader : Block) : Prop :=
  ∀ regs, MetadataMatches model regs →
    let actual := reader.eval memory ⟨regs, .running⟩
    let expected := model.store.readWord? (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = logicalPacket expected ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = model.receipts (regs 8192) (regs 8193) ∧
    ReaderFrame regs actual.final.regs

theorem MetadataMatches.write (model : ControllerModel) (regs : Registers)
    (hm : MetadataMatches model regs) (dst value : Nat)
    (outside : dst < 0 ∨ 190 ≤ dst) : MetadataMatches model (regs.write dst value) := by
  intro r hr
  have hn : r ≠ dst := by omega
  simp only [Registers.write, if_neg hn]
  exact hm r hr

theorem readerFrame_metadata (model : ControllerModel) (before after : Registers)
    (frame : ReaderFrame before after) (hm : MetadataMatches model before) :
    MetadataMatches model after := by
  intro r hr
  rw [frame r (Or.inl (by omega))]
  exact hm r hr

theorem writes_metadata (model : ControllerModel) (memory : Memory)
    (block : Block) (allowed : Nat → Prop) (writes : block.WritesOnly allowed)
    (outside : ∀ r, 0 ≤ r → r < 190 → ¬ allowed r)
    (s : Data) (hm : MetadataMatches model s.regs) :
    MetadataMatches model (block.eval memory s).final.regs := by
  intro r hr
  rw [Block.eval_frame memory block allowed writes r (outside r (by omega) hr)]
  exact hm r hr

@[simp] theorem traceReads_append (receipts : Nat → Nat → List Receipt)
    (first second : List WordRAM.TraceEvent) :
    traceReads receipts (first ++ second) = traceReads receipts first ++ traceReads receipts second := by
  simp [traceReads]

/-- A reader which merely keeps its old output cannot satisfy the universal
interface: its two arbitrary initial output values receive the same request. -/
theorem readerSimulation_rejects_skip (model : ControllerModel) (memory : Memory) :
    ¬ ReaderSimulation model memory .skip := by
  intro h
  have hm : MetadataMatches model model.metadata := by intro r hr; rfl
  have h0 := h (model.metadata.write 8194 0)
    (MetadataMatches.write model model.metadata hm 8194 0 (Or.inr (by decide)))
  have h1 := h (model.metadata.write 8194 1)
    (MetadataMatches.write model model.metadata hm 8194 1 (Or.inr (by decide)))
  have hp0 := h0.2.1
  have hp1 := h1.2.1
  change (model.metadata.write 8194 0) 8194 =
    logicalPacket (model.store.readWord? ((model.metadata.write 8194 0) 8192)
      ((model.metadata.write 8194 0) 8193)) at hp0
  change (model.metadata.write 8194 1) 8194 =
    logicalPacket (model.store.readWord? ((model.metadata.write 8194 1) 8192)
      ((model.metadata.write 8194 1) 8193)) at hp1
  simp [Registers.write] at hp0 hp1
  omega

end RMQ.PackedBitvector.Controller
