import RMQ.Core.WordRAM.Packed.Setup
import RMQ.Core.WordRAM.Packed.Frame
import RMQ.Core.WordRAM.Packed.LogicalSpan
import RMQ.Core.WordRAM.Packed.SpanAssembly

/-!
# Proof interface for the fixed physical logical-word subroutine

Only source code is passed when assembling a caller. The semantic store and
shape below occur in proof statements, never in the source interpreter or its
compiled program. Canonical reader correctness must be derived from the counted
allocation before any whole-query theorem can consume this interface.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe

def logicalReadBase : Nat := 8192

def MetadataMatches (shape : CartesianShape) (regs : Registers) : Prop :=
  ∀ i < 174, regs (16 + i) = ((metadata shape)[i]?).getD 0

def logicalPacket (word : Option (List Bool)) : Nat :=
  match word with
  | none => 0
  | some bits => bitsToNatLE bits + 1

def logicalLength (word : Option (List Bool)) : Nat :=
  (word.map List.length).getD 0

def ReaderFrame (before after : Registers) : Prop :=
  ∀ r, r < 8194 ∨ 8271 ≤ r → after r = before r

def ReaderWrites (reader : Block) : Prop :=
  reader.WritesOnly (fun r => 8194 ≤ r ∧ r < 8271)

/-- Ordered raw attempts for one logical request. A request with no numeric span
(a logically absent word, or a segment or index outside the layout) and a span
of length zero make no physical load at all; this is a choice of the reader
model, not a suppressed failure. Otherwise every primitive load the reader
issues is listed, in order. A primitive load whose address is outside the
allocation faults the machine and is still logged, with no reply; the canonical
query run performs no such load. This is a specification of the physical
reader's output, not executable code. -/
def readerReceipts (shape : CartesianShape) (memory : Memory)
    (segment index : Nat) : List Receipt :=
  match reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) segment index with
  | none => []
  | some span => spanAttemptReceipts (wordWidth shape.size)
      (174 * wordWidth shape.size + span.position) span.length memory

/-- Expand logical read occurrences in order. Clients also prove `ReadOnlyTrace`
so that this projection cannot discard a logical primitive or synthetic event. -/
def logicalTraceReads (shape : CartesianShape) (memory : Memory)
    (trace : List WordRAM.TraceEvent) : List Receipt :=
  trace.flatMap fun event => match event with
    | .readWord segment index _ => readerReceipts shape memory segment index
    | _ => []

def ReadOnlyTrace (trace : List WordRAM.TraceEvent) : Prop :=
  ∀ event ∈ trace, event.isReadWord

theorem MetadataMatches.write (shape : CartesianShape) (regs : Registers)
    (hmetadata : MetadataMatches shape regs) (dst value : Nat)
    (outside : dst < 16 ∨ 190 ≤ dst) : MetadataMatches shape (regs.write dst value) := by
  intro i hi
  have hn : 16 + i ≠ dst := by omega
  simp only [Registers.write, if_neg hn]
  exact hmetadata i hi

/-- A proof-side interface, with no semantic callback in the source block.
The metadata premise is installed by the charged setup theorem. -/
def ReaderCorrect (shape : CartesianShape) (memory : Memory) (reader : Block) : Prop :=
  ∀ regs, MetadataMatches shape regs →
    let actual := reader.eval memory ⟨regs, .running⟩
    let expected := (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
      (regs 8192) (regs 8193)
    actual.final.status = .running ∧
    actual.final.regs 8194 = logicalPacket expected ∧
    actual.final.regs 8195 = logicalLength expected ∧
    actual.reads = readerReceipts shape memory (regs 8192) (regs 8193) ∧
    ReaderFrame regs actual.final.regs

theorem ReaderFrame.metadata (shape : CartesianShape) (before after : Registers)
    (frame : ReaderFrame before after) (hmetadata : MetadataMatches shape before) :
    MetadataMatches shape after := by
  intro i hi
  rw [frame (16 + i) (Or.inl (by omega))]
  exact hmetadata i hi

theorem setup_metadataMatches (xs : List Int) (s : Data) (hs : s.status = .running) :
    MetadataMatches (SuccinctClassic.cartesianShape xs)
      (metadataSetupBlock.eval (buildMemory xs) s).final.regs :=
  (buildMemory_setup xs s hs).2.1

@[simp] theorem logicalPacket_none : logicalPacket none = 0 := rfl
@[simp] theorem logicalPacket_some (bits : List Bool) :
    logicalPacket (some bits) = bitsToNatLE bits + 1 := rfl

@[simp] theorem logicalLength_none : logicalLength none = 0 := rfl
@[simp] theorem logicalLength_some (bits : List Bool) :
    logicalLength (some bits) = bits.length := rfl

theorem logicalPacket_pred (word : Option (List Bool)) :
    logicalPacket word - 1 = (word.map bitsToNatLE).getD 0 := by
  cases word <;> simp [logicalPacket]

theorem logicalPacket_zero_iff (word : Option (List Bool)) :
    logicalPacket word = 0 ↔ word = none := by
  cases word <;> simp [logicalPacket]

end RMQ.SuccinctFinal.PackedWordRAM
