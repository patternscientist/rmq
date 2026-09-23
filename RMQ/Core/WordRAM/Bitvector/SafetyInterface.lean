import RMQ.Core.WordRAM.Bitvector.ControllerInterface
import RMQ.Core.WordRAM.Packed.ScalarSafety

/-! # Numeric hypotheses for the unchanged generic controllers

Raw word lengths control shifts. Directory and chunk-table reply bounds control
values separately; none of these proof parameters is executable controller data.
-/

namespace RMQ.PackedBitvector.Controller

open SuccinctFinal.PackedWordRAM Structured

structure SafetyLimits where
  width : Nat
  rawWidth : Nat
  directoryBound : Nat
  tableBound : Nat
  envelope : Nat
  width32 : 32 ≤ width
  rawShift : 8 * rawWidth < width
  rawCapacity : 2 ^ rawWidth ≤ directoryBound
  output : 8 * rawWidth + 2 * max directoryBound tableBound ≤ envelope
  cubic : 32 * (envelope * envelope * envelope) < 2 ^ width
  square : 256 * (envelope * envelope) < 2 ^ width

def SafetyLimits.packetBound (limits : SafetyLimits) : Nat :=
  max limits.directoryBound limits.tableBound

theorem SafetyLimits.output_bound (limits : SafetyLimits) :
    8 * limits.rawWidth + 2 * limits.packetBound ≤ limits.envelope := limits.output

structure ControllerSafetyBounds (model : ControllerModel) (limits : SafetyLimits) : Prop where
  metadata_bound : ∀ r, 16 ≤ r → r < 190 → model.metadata r ≤ limits.envelope
  super_stride_pos : 0 < model.metadata 25
  local_stride_pos : 0 < model.metadata 26
  long_word_pos : 0 < model.metadata 30
  sparse_word_pos : 0 < model.metadata 31
  word_pos : 0 < model.metadata 32
  chunk_pos : 0 < model.metadata 34
  word_le : model.metadata 32 ≤ limits.rawWidth
  chunk_le : model.metadata 34 ≤ limits.rawWidth
  directory_packet : ∀ segment index, segment ≠ 21 → segment ≠ 22 →
    logicalPacket (model.store.readWord? segment index) ≤ limits.directoryBound
  table_packet : ∀ segment index, segment = 21 ∨ segment = 22 →
    logicalPacket (model.store.readWord? segment index) ≤ limits.tableBound
  raw_length : ∀ segment index, segment = 0 ∨ segment = 11 ∨ segment = 15 →
    logicalLength (model.store.readWord? segment index) ≤ limits.rawWidth

def ReaderSafe (model : ControllerModel) (width : Nat) (memory : Memory) (reader : Block) : Prop :=
  ∀ s, s.Fits width → MetadataMatches model s.regs → reader.Safe memory width s

theorem SafetyLimits.packet_pos (limits : SafetyLimits) : 0 < limits.packetBound := by
  have hp := Nat.two_pow_pos limits.rawWidth
  have hd := limits.rawCapacity
  have hm := Nat.le_max_left limits.directoryBound limits.tableBound
  unfold SafetyLimits.packetBound
  omega

theorem SafetyLimits.raw_lt_packet (limits : SafetyLimits) : limits.rawWidth < limits.packetBound := by
  have hp := Nat.lt_two_pow_self (n := limits.rawWidth)
  have hd := limits.rawCapacity
  have hm := Nat.le_max_left limits.directoryBound limits.tableBound
  unfold SafetyLimits.packetBound
  omega

theorem SafetyLimits.packet_le_envelope (limits : SafetyLimits) :
    limits.packetBound ≤ limits.envelope := by
  have h := limits.output
  unfold SafetyLimits.packetBound
  omega

theorem SafetyLimits.envelope_pos (limits : SafetyLimits) : 0 < limits.envelope := by
  have hp := limits.packet_pos
  have he := limits.packet_le_envelope
  omega

theorem SafetyLimits.envelope_lt_capacity (limits : SafetyLimits) :
    limits.envelope < 2 ^ limits.width := by
  have pos := limits.envelope_pos
  have square : limits.envelope ≤ limits.envelope * limits.envelope := by
    simpa using Nat.mul_le_mul_left limits.envelope (show 1 ≤ limits.envelope by omega)
  have cap := limits.square
  omega

theorem SafetyLimits.reader_polynomial_fit (limits : SafetyLimits) :
    175 * limits.envelope + 2 * (limits.envelope * limits.envelope) < 2 ^ limits.width := by
  have pos := limits.envelope_pos
  have square : limits.envelope ≤ limits.envelope * limits.envelope := by
    simpa using Nat.mul_le_mul_left limits.envelope (show 1 ≤ limits.envelope by omega)
  have cap := limits.square
  omega

theorem SafetyLimits.constant_fit (limits : SafetyLimits) (value : Nat) (small : value < 2 ^ 32) :
    value < 2 ^ limits.width :=
  Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) limits.width32)

theorem SafetyLimits.chunk_slot_fit (limits : SafetyLimits) (c : Nat)
    (hc : c ≤ limits.rawWidth) :
    (2 ^ c * (c + 1) + c) * (c + 1) + c < 2 ^ limits.width := by
  let e := limits.envelope
  have ep : 0 < e := limits.envelope_pos
  have env := limits.output
  have cp : c + 1 ≤ e := by
    have hp := limits.packet_pos
    dsimp only [e]
    change 8 * limits.rawWidth + 2 * limits.packetBound ≤ limits.envelope at env
    omega
  have pp : 2 ^ c ≤ e := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hc
    have hdir := limits.rawCapacity
    have hm := Nat.le_max_left limits.directoryBound limits.tableBound
    have he := limits.packet_le_envelope
    change max limits.directoryBound limits.tableBound ≤ limits.envelope at he
    dsimp only [e]
    omega
  have square : e ≤ e * e := by
    simpa using Nat.mul_le_mul_left e (show 1 ≤ e by omega)
  have cube : e * e ≤ e * e * e := by
    simpa using Nat.mul_le_mul_left (e * e) (show 1 ≤ e by omega)
  have p := Nat.mul_le_mul pp cp
  have q := Nat.mul_le_mul (show 2 ^ c * (c + 1) + c ≤ 2 * (e * e) by omega) cp
  have cap := limits.cubic
  change 32 * (e * e * e) < _ at cap
  simp only [Nat.mul_assoc] at q cap cube
  omega

theorem logicalPacket_bound (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (segment index : Nat) :
    logicalPacket (model.store.readWord? segment index) ≤ limits.packetBound := by
  by_cases htable : segment = 21 ∨ segment = 22
  · exact Nat.le_trans (bounds.table_packet segment index htable) (Nat.le_max_right _ _)
  · have h := bounds.directory_packet segment index (by omega) (by omega)
    exact Nat.le_trans h (Nat.le_max_left _ _)

theorem metadata_envelope (model : ControllerModel) (limits : SafetyLimits)
    (bounds : ControllerSafetyBounds model limits) (regs : Registers)
    (hm : MetadataMatches model regs) (r : Nat) (hr : 16 ≤ r ∧ r < 190) :
    regs r ≤ limits.envelope := by
  rw [hm r hr.2]
  exact bounds.metadata_bound r hr.1 hr.2

end RMQ.PackedBitvector.Controller
