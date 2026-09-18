import RMQ.Core.WordRAM.Bitvector.Allocation

/-! # Fixed source for three operations over the shared numerical allocation

Each operation installs its geometry through actual memory loads. The source
and compiled program do not depend on the input bitvector or query argument.
The natural-number interface rejects arguments outside the declared word range
before constructing a machine input; the physical runs remain explicit below.
-/

namespace RMQ.PackedBitvector

open SuccinctFinal.PackedWordRAM SuccinctFinal.PackedWordRAM.Structured

inductive Operation where
  | access
  | rank
  | select
  deriving DecidableEq, Repr

def rankPrepare : Block := Block.sequence [
  .action (.move 353 18), .action (.move 354 19), .action (.move 355 20),
  .action (.constant 356 17), .action (.constant 357 18),
  .action (.constant 358 19), .action (.move 359 3)]

def rankQuery : Block := Block.sequence [
  .action (.constant 360 0), .action (.comparison .lt 371 18 352),
  .ifZero 371 (Block.sequence [rankPrepare, rankBlock Experiment.physicalReader,
    .action (.constant 370 1), .action (.arithmetic .add 360 360 370)]) .skip]

def accessQuery : Block := Block.sequence [
  .action (.constant 705 0), .action (.comparison .lt 706 704 18),
  .ifZero 706 .skip (Block.sequence [
    .action (.constant 8192 19), .action (.arithmetic .div 8193 704 19),
    Experiment.physicalReader,
    .ifZero 8194 .skip (Block.sequence [
      .action (.constant 707 1), .action (.arithmetic .sub 708 8194 707),
      .action (.arithmetic .mod 709 704 19),
      .action (.arithmetic .shr 708 708 709),
      .action (.constant 707 2), .action (.arithmetic .mod 708 708 707),
      .action (.constant 707 1), .action (.arithmetic .add 705 708 707)])])]

def operationBody : Operation → Block
  | .access => accessQuery
  | .rank => rankQuery
  | .select => .seq Experiment.targetSetup (selectCloseBlock Experiment.physicalReader)

def source (operation : Operation) : Block :=
  .seq Experiment.setup (operationBody operation)

def argumentRegister : Operation → Nat
  | .access => 704
  | .rank => 352
  | .select => 512

def resultRegister : Operation → Nat
  | .access => 705
  | .rank => 360
  | .select => 513

def program (operation : Operation) : Program :=
  (source operation).compileAt 0 ++ [.halt (resultRegister operation)]

def initial (operation : Operation) (target : Bool) (argument : Nat) : State :=
  ⟨fun r => if r = 3 then target.toNat
    else if r = argumentRegister operation then argument else 0, 0, .running⟩

def execute (bits : List Bool) (operation : Operation) (target : Bool) (argument : Nat) : Run :=
  run (Allocation.memory bits) (program operation) ((source operation).size + 1)
    (initial operation target argument)

def decodeNatPacket : Nat → Option Nat
  | 0 => none
  | value + 1 => some value

def decodeBoolPacket : Nat → Option Bool
  | 1 => some false
  | 2 => some true
  | _ => none

def queryPacket (bits : List Bool) (operation : Operation) (target : Bool)
    (argument : Nat) : Nat :=
  if argument < 2 ^ Experiment.width bits.length then
    (execute bits operation target argument).final.regs (resultRegister operation)
  else 0

def access (bits : List Bool) (index : Nat) : Option Bool :=
  decodeBoolPacket (queryPacket bits .access false index)

def rank (bits : List Bool) (target : Bool) (endPos : Nat) : Option Nat :=
  decodeNatPacket (queryPacket bits .rank target endPos)

def select (bits : List Bool) (target : Bool) (occurrence : Nat) : Option Nat :=
  decodeNatPacket (queryPacket bits .select target occurrence)

end RMQ.PackedBitvector
