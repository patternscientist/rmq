import RMQ.Core.WordRAM.Native.Machine

/-! Independent theorem consumers and direct limb-machine boundary examples. -/

namespace RMQ.SuccinctFinal.PackedNative.LimbMachine.Checks

open PackedWordRAM

example (width capacity : Nat) (memory : PackedWordRAM.Memory) (program : Program)
    (fuel : Nat) (s : PackedWordRAM.State)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (hsafe : ∀ t ∈ (PackedWordRAM.run memory program fuel s).transitions,
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) :
    (LimbMachine.run width (encodeMemory width memory) (encodeCode width program) fuel
      (State.encode width capacity s)).decode = PackedWordRAM.run memory program fuel s :=
  run_reference width capacity memory program fuel s hm hp hw hf hz hsafe

example (width capacity : Nat) (memory : PackedWordRAM.Memory) (program : Program)
    (fuel : Nat) (s : PackedWordRAM.State)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (hsafe : ∀ t ∈ (PackedWordRAM.run memory program fuel s).transitions,
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) :
    let got := (LimbMachine.run width (encodeMemory width memory) (encodeCode width program)
      fuel (State.encode width capacity s)).decode
    let expected := PackedWordRAM.run memory program fuel s
    got.result = expected.result ∧ got.final.status = expected.final.status ∧
    got.reads = expected.reads ∧ got.steps = expected.steps ∧
    got.categoryCount .memoryRead = expected.categoryCount .memoryRead ∧
    got.categoryCount .registerWrite = expected.categoryCount .registerWrite ∧
    got.categoryCount .arithmetic = expected.categoryCount .arithmetic ∧
    got.categoryCount .comparison = expected.categoryCount .comparison ∧
    got.categoryCount .branch = expected.categoryCount .branch ∧
    got.categoryCount .control = expected.categoryCount .control := by
  rw [run_reference _ _ _ _ _ _ hm hp hw hf hz hsafe]
  simp

example (width : Nat) (memory : LimbMachine.Memory) (program : Program)
    (code : Code) (fuel : Nat) (s : LimbMachine.State)
    (hm : ∀ word ∈ memory.toList, LimbWord.Canonical width word)
    (hc : s.Canonical width) (hcode : code = encodeCode width program)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < s.regs.size))
    (hsafe : ∀ t ∈ (PackedWordRAM.run (decodeMemory memory) program fuel s.decode).transitions,
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) :
    (LimbMachine.run width memory code fuel s).decode =
      PackedWordRAM.run (decodeMemory memory) program fuel s.decode :=
  run_loaded_reference width memory program code fuel s hm hc hcode hp hw hsafe

example (reads : Bool) (width : Nat) (memory : LimbMachine.Memory)
    (code : Code) (fuel : Nat) (s : LimbMachine.State) (a : Stats) :
    LimbMachine.runThin reads width memory code fuel s a =
      ((LimbMachine.run width memory code fuel s).final,
       (LimbMachine.run width memory code fuel s).transitions.foldl
         (LimbMachine.recordTransition reads) a) :=
  runThin_projection reads width memory code fuel s a

example (width : Nat) (memory : LimbMachine.Memory) (code : Code) (fuel : Nat)
    (s : LimbMachine.State) (a : Stats) :
    (LimbMachine.runThin false width memory code fuel s a).2.readsRev = a.readsRev :=
  runThin_no_reads width memory code fuel s a

example (width : Nat) (s : LimbMachine.State) (hc : s.Canonical width) :
    State.encode width s.regs.size s.decode = s := State.encode_decode width s hc

example (width : Nat) (i : Instruction) (hf : i.Fits width) :
    decodeInstruction width (encodeInstruction width i) = .ok i := decodeInstruction_encode width i hf

def initialReference : PackedWordRAM.State := ⟨fun _ => 0, 0, .running⟩
def initial (width : Nat) : LimbMachine.State := State.encode width 2 initialReference
def readProgram : Program := [.constant 0 0, .load 1 0, .halt 1]
def readOutput (width value : Nat) : LimbMachine.State × Stats :=
  LimbMachine.runThin true width (encodeMemory width [value])
    (encodeCode width readProgram) 3 (initial width) {}

example : (readOutput 8 173).1.status.decode = .halted 173 := by rfl
example : (readOutput 8 173).2.steps = 3 := by rfl
example : (readOutput 8 173).2.readsRev.reverse = [⟨0, some 173⟩] := by rfl
example : (readOutput 8 173).2.counts = ⟨1, 1, 0, 0, 0, 1⟩ := by rfl
example : (readOutput 168 (2 ^ 167 + 19)).1.status.decode = .halted (2 ^ 167 + 19) := by rfl
example : (readOutput 176 (2 ^ 175 + 37)).1.status.decode = .halted (2 ^ 175 + 37) := by rfl

def missingOutput : LimbMachine.State × Stats :=
  LimbMachine.runThin true 8 #[] (encodeCode 8 [.load 0 0]) 3 (initial 8) {}
example : missingOutput.1.status.decode = .fault := by rfl
example : missingOutput.2.steps = 1 := by rfl
example : missingOutput.2.readsRev.reverse = [⟨0, none⟩] := by rfl
example : missingOutput.2.counts = ⟨1, 0, 0, 0, 0, 0⟩ := by rfl

def noFetchOutput : LimbMachine.State × Stats :=
  LimbMachine.runThin true 8 #[] #[] 3 (initial 8) {}
example : noFetchOutput.1.status.decode = .running := by rfl
example : noFetchOutput.2.steps = 0 := by rfl

def badCodeOutput : LimbMachine.State × Stats :=
  LimbMachine.runThin true 8 #[] #[#[LimbWord.encode 8 99]] 3 (initial 8) {}
example : badCodeOutput.1.status.decode = .fault := by rfl
example : badCodeOutput.2.steps = 0 := by rfl

def divisorOutput : LimbMachine.State × Stats :=
  LimbMachine.runThin true 8 #[]
    (encodeCode 8 [.constant 0 17, .arithmetic .div 0 0 1, .halt 0]) 3 (initial 8) {}
example : divisorOutput.1.status.decode = .fault := by rfl
example : divisorOutput.2.steps = 2 := by rfl
example : divisorOutput.2.counts = ⟨0, 1, 1, 0, 0, 0⟩ := by rfl

def haltedOutput : LimbMachine.State × Stats :=
  LimbMachine.runThin true 8 #[] (encodeCode 8 [.halt 0, .load 1 1]) 3 (initial 8) {}
example : haltedOutput.1.status.decode = .halted 0 := by rfl
example : haltedOutput.2.steps = 1 := by rfl
example : haltedOutput.2.readsRev = [] := by rfl

def badPaddingState : LimbMachine.State := ⟨#[LimbWord.encode 8 0], #[0, 1], .running⟩
example : (LimbMachine.runThin true 8 #[] #[] 3 badPaddingState {}).1.status.decode = .fault := by rfl
example : (LimbMachine.runThin true 8 #[] #[] 3 badPaddingState {}).2.steps = 0 := by rfl

#print axioms State.decode_encode
#print axioms State.encode_decode
#print axioms decodeMemory_encode
#print axioms encodeMemory_decode
#print axioms decodeInstruction_encode
#print axioms execute_encode
#print axioms step_encode
#print axioms run_encode
#print axioms run_reference
#print axioms run_loaded_reference
#print axioms runThin_projection
#print axioms runThin_no_reads
#print axioms runThin_reference
#print axioms runThin_loaded_reference
#print axioms run_final_canonical
#print axioms execute_missing_memory
#print axioms step_missing_fetch

end RMQ.SuccinctFinal.PackedNative.LimbMachine.Checks
