import RMQ.Core.WordRAM.Native.Limbs
import RMQ.Core.WordRAM.Native.Route

/-!
# Direct interpreter over byte-limb code, memory and registers

Only the fetched instruction and scalar operands are decoded temporarily. State,
memory, program fields, PC and halted packet persist as byte arrays. The reference
Nat interpreter appears only in proofs and decoded observations.
-/

namespace RMQ.SuccinctFinal.PackedNative.LimbMachine

open PackedWordRAM LimbWord

abbrev Memory := Array Word
abbrev Code := Array (Array Word)

inductive Status where
  | running | halted (packet : Word) | fault
deriving Repr

def Status.decode : Status → PackedWordRAM.Status
  | .running => .running
  | .halted packet => .halted (LimbWord.decode packet)
  | .fault => .fault

def Status.encode (width : Nat) : PackedWordRAM.Status → Status
  | .running => .running
  | .halted packet => .halted (LimbWord.encode width packet)
  | .fault => .fault

structure State where
  regs : Array Word
  pc : Word
  status : Status
deriving Repr

def State.readWord (width : Nat) (s : State) (r : Nat) : Word :=
  s.regs[r]?.getD (LimbWord.encode width 0)

def State.decode (s : State) : PackedWordRAM.State :=
  ⟨fun r => (s.regs[r]?.map LimbWord.decode).getD 0,
    LimbWord.decode s.pc, s.status.decode⟩

def State.encode (width capacity : Nat) (s : PackedWordRAM.State) : State :=
  ⟨Array.ofFn (fun r : Fin capacity => LimbWord.encode width (s.regs r.val)),
    LimbWord.encode width s.pc, Status.encode width s.status⟩

def encodeMemory (width : Nat) (memory : PackedWordRAM.Memory) : Memory :=
  (memory.map (LimbWord.encode width)).toArray

def decodeMemory (memory : Memory) : PackedWordRAM.Memory :=
  memory.toList.map LimbWord.decode

def encodeInstruction (width : Nat) (i : Instruction) : Array Word :=
  (i.encoding.map (LimbWord.encode width)).toArray

def encodeCode (width : Nat) (program : Program) : Code :=
  (program.map (encodeInstruction width)).toArray

/-- The size check precedes the at-most-five-word canonical scan. -/
def decodeInstruction (width : Nat) (fields : Array Word) : Except String Instruction :=
  if fields.size ≤ 5 then
    if fields.toList.all (fun word => decide (Canonical width word)) then
      parseInstruction (fields.toList.map LimbWord.decode)
    else .error "noncanonical instruction word"
  else .error "oversized instruction"

@[simp] theorem State.encode_size (width capacity : Nat) (s : PackedWordRAM.State) :
    (State.encode width capacity s).regs.size = capacity := by simp [State.encode]

theorem State.readWord_encode (width capacity : Nat) (s : PackedWordRAM.State)
    (hz : ∀ r, capacity ≤ r → s.regs r = 0) (r : Nat) :
    (State.encode width capacity s).readWord width r = LimbWord.encode width (s.regs r) := by
  by_cases hr : r < capacity
  · simp [State.readWord, State.encode, hr]
  · have hzero := hz r (by omega)
    simp [State.readWord, State.encode, hr, hzero]

theorem State.decode_encode (width capacity : Nat) (s : PackedWordRAM.State)
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0) :
    (State.encode width capacity s).decode = s := by
  cases s with
  | mk regs pc status =>
      rcases hf with ⟨hpc, hregs, hstatus⟩
      unfold State.encode State.decode
      simp only [LimbWord.decode_encode _ _ hpc]
      congr 1
      · funext r
        by_cases hr : r < capacity
        · simp [hr, LimbWord.decode_encode _ _ (hregs r)]
        · have hzero := hz r (by omega)
          change regs r = 0 at hzero
          simp [hr, hzero]
      · cases status with
        | running => rfl
        | fault => rfl
        | halted value =>
            simp [Status.encode, Status.decode, LimbWord.decode_encode _ _ (hstatus _ rfl)]

theorem decodeMemory_encode (width : Nat) (memory : PackedWordRAM.Memory)
    (hf : ∀ value ∈ memory, value < 2 ^ width) :
    decodeMemory (encodeMemory width memory) = memory := by
  simp only [decodeMemory, encodeMemory, List.toList_toArray, List.map_map]
  calc
    _ = memory.map id := List.map_congr_left fun value hv => LimbWord.decode_encode _ _ (hf value hv)
    _ = memory := List.map_id memory

theorem instruction_length (i : Instruction) : i.encoding.length ≤ 5 := by
  cases i <;> simp [Instruction.encoding, Instruction.operands]

theorem decodeInstruction_encode (width : Nat) (i : Instruction) (hf : i.Fits width) :
    decodeInstruction width (encodeInstruction width i) = .ok i := by
  have hc : ∀ value ∈ i.encoding, Canonical width (LimbWord.encode width value) :=
    fun value hv => canonical_encode _ _ (hf value hv)
  have hd : i.encoding.map (fun value => LimbWord.decode (LimbWord.encode width value)) =
      i.encoding := by
    calc
      _ = i.encoding.map id := List.map_congr_left fun value hv => LimbWord.decode_encode _ _ (hf value hv)
      _ = i.encoding := List.map_id i.encoding
  simp only [decodeInstruction, encodeInstruction, List.size_toArray, List.length_map,
    instruction_length, if_true, List.toList_toArray, List.all_map, List.all_eq_true,
    decide_eq_true_eq, List.map_map, Function.comp_def]
  rw [if_pos hc, hd, parseInstruction_encoding]

inductive Fault where
  | word (cause : WordFault) | destination | missingMemory | malformedCode
deriving Repr, DecidableEq

structure Execution where
  next : State
  receipt : Option Receipt := none
  error : Option Fault := none
deriving Repr

def fail (s : State) (why : Fault) (receipt : Option Receipt := none) : Execution :=
  ⟨{ s with status := .fault }, receipt, some why⟩

/-- Local destination/result/PC checks; this never scans the register bank. -/
def writeNext (width : Nat) (s : State) (dst : Nat) (value : Word)
    (receipt : Option Receipt := none) : Execution :=
  if dst < s.regs.size then
    if Canonical width value then
      match checkedNat width (LimbWord.decode s.pc + 1) with
      | .ok pc => ⟨⟨s.regs.setIfInBounds dst value, pc, .running⟩, receipt, none⟩
      | .error why => fail s (.word why) receipt
    else fail s (.word .malformedWord) receipt
  else fail s .destination receipt

def writeResult (width : Nat) (s : State) (dst : Nat)
    (result : Except WordFault Word) : Execution :=
  match result with
  | .ok word => writeNext width s dst word
  | .error why => fail s (.word why)

def setPC (width : Nat) (s : State) (target : Word) : Execution :=
  if Canonical width target then ⟨{ s with pc := target }, none, none⟩
  else fail s (.word .malformedWord)

def setPCResult (width : Nat) (s : State) (target : Except WordFault Word) : Execution :=
  match target with
  | .ok word => setPC width s word
  | .error why => fail s (.word why)

def execute (width : Nat) (memory : Memory) (i : Instruction) (s : State) : Execution :=
  match i with
  | .load dst address =>
      let addr := s.readWord width address
      if Canonical width addr then
        let a := LimbWord.decode addr
        let reply := memory[a]?
        let receipt := some (Receipt.mk a (reply.map LimbWord.decode))
        match reply with
        | none => fail s .missingMemory receipt
        | some word => writeNext width s dst word receipt
      else fail s (.word .malformedWord)
  | .constant dst value => writeResult width s dst (checkedNat width value)
  | .move dst src => writeNext width s dst (s.readWord width src)
  | .arithmetic op dst lhs rhs =>
      writeResult width s dst
        (checkedArithmetic width op (s.readWord width lhs) (s.readWord width rhs))
  | .comparison op dst lhs rhs =>
      writeResult width s dst
        (checkedComparison width op (s.readWord width lhs) (s.readWord width rhs))
  | .jump target => setPCResult width s (checkedNat width target)
  | .jumpRegister src => setPC width s (s.readWord width src)
  | .branchZero condition target =>
      let word := s.readWord width condition
      if Canonical width word then
        if LimbWord.decode word = 0 then
          setPCResult width s (checkedNat width target)
        else setPCResult width s (checkedNat width (LimbWord.decode s.pc + 1))
      else fail s (.word .malformedWord)
  | .halt src =>
      let packet := s.readWord width src
      if Canonical width packet then ⟨{ s with status := .halted packet }, none, none⟩
      else fail s (.word .malformedWord)

structure Transition where
  before : State
  instruction : Instruction
  after : State
  receipt : Option Receipt
deriving Repr

def Transition.decode (t : Transition) : PackedWordRAM.Transition :=
  ⟨t.before.decode, t.instruction, t.after.decode, t.receipt⟩

inductive Step where
  | stopped
  | rejected (state : State) (error : Fault)
  | executed (transition : Transition)
deriving Repr

/-- Missing fetch has no transition; bad fetched code rejects before execution. -/
def step (width : Nat) (memory : Memory) (program : Code) (s : State) : Step :=
  match s.status with
  | .running =>
      if Canonical width s.pc then
        match program[LimbWord.decode s.pc]? with
        | none => .stopped
        | some fields =>
            match decodeInstruction width fields with
            | .error _ => .rejected { s with status := .fault } .malformedCode
            | .ok i =>
                let result := execute width memory i s
                .executed ⟨s, i, result.next, result.receipt⟩
      else .rejected { s with status := .fault } (.word .malformedWord)
  | _ => .stopped

structure Run where
  final : State
  transitions : List Transition
deriving Repr

def Run.decode (r : Run) : PackedWordRAM.Run :=
  ⟨r.final.decode, r.transitions.map Transition.decode⟩

def run (width : Nat) (memory : Memory) (program : Code) : Nat → State → Run
  | 0, s => ⟨s, []⟩
  | fuel + 1, s =>
      match step width memory program s with
      | .stopped => ⟨s, []⟩
      | .rejected failed _ => ⟨failed, []⟩
      | .executed t =>
          let rest := run width memory program fuel t.after
          ⟨rest.final, t :: rest.transitions⟩

def recordTransition (observeReads : Bool) (a : Stats) (t : Transition) : Stats :=
  a.record observeReads t.instruction.category t.receipt

/-- Production loop calls the same limb step and never constructs a trace list. -/
def runThin (observeReads : Bool) (width : Nat) (memory : Memory) (program : Code) :
    Nat → State → Stats → State × Stats
  | 0, s, a => (s, a)
  | fuel + 1, s, a =>
      match step width memory program s with
      | .stopped => (s, a)
      | .rejected failed _ => (failed, a)
      | .executed t => runThin observeReads width memory program fuel t.after
          (recordTransition observeReads a t)

theorem runThin_projection (observeReads : Bool) (width : Nat) (memory : Memory)
    (program : Code) (fuel : Nat) (s : State) (a : Stats) :
    runThin observeReads width memory program fuel s a =
      ((run width memory program fuel s).final,
        (run width memory program fuel s).transitions.foldl (recordTransition observeReads) a) := by
  induction fuel generalizing s a with
  | zero => rfl
  | succ fuel ih =>
      simp only [runThin, run]
      cases step width memory program s with
      | stopped => rfl
      | rejected failed why => rfl
      | executed t =>
          simpa only [List.foldl_cons] using ih t.after (recordTransition observeReads a t)

theorem runThin_no_reads (width : Nat) (memory : Memory) (program : Code)
    (fuel : Nat) (s : State) (a : Stats) :
    (runThin false width memory program fuel s a).2.readsRev = a.readsRev := by
  induction fuel generalizing s a with
  | zero => rfl
  | succ fuel ih =>
      simp only [runThin]
      cases step width memory program s with
      | stopped => rfl
      | rejected failed why => rfl
      | executed t => exact (ih t.after (recordTransition false a t)).trans rfl

theorem State.encode_writeNext (width capacity : Nat) (s : PackedWordRAM.State)
    (dst value : Nat) :
    State.encode width capacity (s.writeNext dst value) =
      ⟨(State.encode width capacity s).regs.setIfInBounds dst (LimbWord.encode width value),
        LimbWord.encode width (s.pc + 1), .running⟩ := by
  simp only [State.encode, PackedWordRAM.State.writeNext, Status.encode]
  congr 1
  apply Array.ext
  · simp
  · intro r hr hl
    by_cases hd : r = dst
    · subst r
      simp_all [Registers.write]
    · have hr' : r < capacity := by simpa using hr
      rw [Array.getElem_setIfInBounds (by simpa using hr')]
      simp [Registers.write, hd, Ne.symm hd]

theorem writeNext_encode (width capacity : Nat) (s : PackedWordRAM.State)
    (dst value : Nat) (receipt : Option Receipt)
    (hd : dst < capacity) (hpc : s.pc < 2 ^ width)
    (hv : value < 2 ^ width) (hn : s.pc + 1 < 2 ^ width) :
    writeNext width (State.encode width capacity s) dst (LimbWord.encode width value) receipt =
      ⟨State.encode width capacity (s.writeNext dst value), receipt, none⟩ := by
  rw [State.encode_writeNext]
  simp only [writeNext, State.encode_size, hd, if_true, canonical_encode _ _ hv]
  simp only [State.encode, LimbWord.decode_encode _ _ hpc, checkedNat_of_lt _ _ hn]

theorem writeNext_fits_fields (width : Nat) (s : PackedWordRAM.State) (dst value : Nat)
    (h : (s.writeNext dst value).Fits width) :
    s.pc + 1 < 2 ^ width ∧ value < 2 ^ width := by
  exact ⟨h.1, by simpa [PackedWordRAM.State.writeNext] using h.2.1 dst⟩

theorem State.zero_tail_writeNext (capacity : Nat) (s : PackedWordRAM.State)
    (dst value : Nat) (hd : dst < capacity)
    (hz : ∀ r, capacity ≤ r → s.regs r = 0) :
    ∀ r, capacity ≤ r → (s.writeNext dst value).regs r = 0 := by
  intro r hr
  have hn : r ≠ dst := by omega
  simp [PackedWordRAM.State.writeNext, Registers.write, hn, hz r hr]

theorem execute_zero_tail (memory : PackedWordRAM.Memory) (i : Instruction)
    (capacity : Nat) (s : PackedWordRAM.State)
    (hd : i.WritesOnly (fun r => r < capacity))
    (hz : ∀ r, capacity ≤ r → s.regs r = 0) :
    ∀ r, capacity ≤ r → (PackedWordRAM.execute memory i s).1.regs r = 0 := by
  cases i <;> simp only [PackedWordRAM.execute]
  · split
    · exact State.zero_tail_writeNext capacity s _ _ hd hz
    · exact hz
  · exact State.zero_tail_writeNext capacity s _ _ hd hz
  · exact State.zero_tail_writeNext capacity s _ _ hd hz
  · exact State.zero_tail_writeNext capacity s _ _ hd hz
  · exact State.zero_tail_writeNext capacity s _ _ hd hz
  · exact hz
  · exact hz
  · exact hz
  · exact hz

/-- Every safe source constructor updates the stored byte state directly. -/
theorem execute_encode (width capacity : Nat) (memory : PackedWordRAM.Memory)
    (i : Instruction) (s : PackedWordRAM.State)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hs : Instruction.Safe width s i)
    (ha : (PackedWordRAM.execute memory i s).1.Fits width)
    (hd : i.WritesOnly (fun r => r < capacity))
    (hz : ∀ r, capacity ≤ r → s.regs r = 0) :
    ((execute width (encodeMemory width memory) i (State.encode width capacity s)).next,
      (execute width (encodeMemory width memory) i (State.encode width capacity s)).receipt) =
    (State.encode width capacity (PackedWordRAM.execute memory i s).1,
      (PackedWordRAM.execute memory i s).2) := by
  have hstate := hs.2.1
  have hpc := hstate.1
  have hregs := hstate.2.1
  cases i with
  | load dst address =>
      simp only [execute, State.readWord_encode _ _ _ hz,
        canonical_encode _ _ (hregs address), if_true, LimbWord.decode_encode _ _ (hregs address)]
      cases hr : memory[s.regs address]? with
      | none =>
          simp [encodeMemory, hr, PackedWordRAM.execute, fail, State.encode, Status.encode]
      | some value =>
          have hv := hm value (List.mem_of_getElem? hr)
          have haf : (s.writeNext dst value).Fits width := by
            simpa [PackedWordRAM.execute, hr] using ha
          have hn := (writeNext_fits_fields width s dst value haf).1
          simp [encodeMemory, hr, LimbWord.decode_encode _ _ hv,
            writeNext_encode _ _ _ _ _ _ hd hpc hv hn, PackedWordRAM.execute]
  | constant dst value =>
      have haf : (s.writeNext dst value).Fits width := ha
      obtain ⟨hn, hv⟩ := writeNext_fits_fields width s dst value haf
      simp [execute, checkedNat_of_lt _ _ hv, writeResult,
        writeNext_encode _ _ _ _ _ _ hd hpc hv hn, PackedWordRAM.execute]
  | move dst src =>
      have haf : (s.writeNext dst (s.regs src)).Fits width := ha
      have hn := (writeNext_fits_fields width s dst (s.regs src) haf).1
      simp [execute, State.readWord_encode _ _ _ hz,
        writeNext_encode _ _ _ _ _ _ hd hpc (hregs src) hn, PackedWordRAM.execute]
  | arithmetic op dst lhs rhs =>
      have haf : (s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs))).Fits width := ha
      obtain ⟨hn, hv⟩ := writeNext_fits_fields width s dst _ haf
      have hop := arithmeticSafe_of_instructionSafe width s op dst lhs rhs hs
      simp [execute, State.readWord_encode _ _ _ hz,
        checkedArithmetic_encode_of_safe _ _ _ _ (hregs lhs) (hregs rhs) hop, writeResult,
        writeNext_encode _ _ _ _ _ _ hd hpc hv hn, PackedWordRAM.execute]
  | comparison op dst lhs rhs =>
      have haf : (s.writeNext dst (op.eval (s.regs lhs) (s.regs rhs))).Fits width := ha
      obtain ⟨hn, hv⟩ := writeNext_fits_fields width s dst _ haf
      simp [execute, State.readWord_encode _ _ _ hz, checkedComparison,
        canonical_encode _ _ (hregs lhs), canonical_encode _ _ (hregs rhs),
        LimbWord.decode_encode _ _ (hregs lhs), LimbWord.decode_encode _ _ (hregs rhs),
        checkedNat_of_lt _ _ hv, writeResult,
        writeNext_encode _ _ _ _ _ _ hd hpc hv hn, PackedWordRAM.execute]
  | jump target =>
      have ht : target < 2 ^ width := ha.1
      simp [execute, setPCResult, checkedNat_of_lt _ _ ht, setPC,
        canonical_encode _ _ ht, PackedWordRAM.execute, State.encode]
  | jumpRegister src =>
      simp only [execute, State.readWord_encode _ _ _ hz, setPC,
        canonical_encode _ _ (hregs src), if_true]
      rfl
  | branchZero condition target =>
      simp only [execute, State.readWord_encode _ _ _ hz,
        canonical_encode _ _ (hregs condition), if_true, LimbWord.decode_encode _ _ (hregs condition)]
      by_cases hc : s.regs condition = 0
      · have ht : target < 2 ^ width := by
          simpa [PackedWordRAM.execute, hc] using ha.1
        simp [hc, setPCResult, checkedNat_of_lt _ _ ht, setPC, canonical_encode _ _ ht,
          PackedWordRAM.execute, State.encode]
      · have hn : s.pc + 1 < 2 ^ width := by
          simpa [PackedWordRAM.execute, hc] using ha.1
        simp [hc, State.encode, LimbWord.decode_encode _ _ hpc,
          setPCResult, checkedNat_of_lt _ _ hn, setPC, canonical_encode _ _ hn,
          PackedWordRAM.execute]
  | halt src =>
      simp only [execute, State.readWord_encode _ _ _ hz, canonical_encode _ _ (hregs src), if_true]
      rfl

def Transition.encode (width capacity : Nat) (t : PackedWordRAM.Transition) : Transition :=
  ⟨State.encode width capacity t.before, t.instruction,
    State.encode width capacity t.after, t.receipt⟩

def Run.encode (width capacity : Nat) (r : PackedWordRAM.Run) : Run :=
  ⟨State.encode width capacity r.final, r.transitions.map (Transition.encode width capacity)⟩

@[simp] theorem State.encode_pc (width capacity : Nat) (s : PackedWordRAM.State) :
    (State.encode width capacity s).pc = LimbWord.encode width s.pc := rfl

@[simp] theorem State.encode_status (width capacity : Nat) (s : PackedWordRAM.State) :
    (State.encode width capacity s).status = Status.encode width s.status := rfl

@[simp] theorem encodeCode_getElem? (width : Nat) (program : Program) (pc : Nat) :
    (encodeCode width program)[pc]? = (program[pc]?).map (encodeInstruction width) := by
  simp [encodeCode]

theorem step_encode (width capacity : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (s : PackedWordRAM.State)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (hsafe : ∀ t, PackedWordRAM.step memory program s = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) :
    step width (encodeMemory width memory) (encodeCode width program) (State.encode width capacity s) =
      match PackedWordRAM.step memory program s with
      | none => .stopped
      | some t => .executed (Transition.encode width capacity t) := by
  cases hstatus : s.status with
  | halted packet =>
      simp [step, State.encode_status, Status.encode, hstatus, PackedWordRAM.step]
  | fault =>
      simp [step, State.encode_status, Status.encode, hstatus, PackedWordRAM.step]
  | running =>
      simp only [step, State.encode_status, hstatus, Status.encode, State.encode_pc,
        canonical_encode _ _ hf.1, if_true, LimbWord.decode_encode _ _ hf.1, encodeCode_getElem?]
      cases hi : program[s.pc]? with
      | none => simp [hi, PackedWordRAM.step, hstatus]
      | some i =>
          have himem : i ∈ program := List.mem_of_getElem? hi
          have hst := hsafe ⟨s, i, (PackedWordRAM.execute memory i s).1,
            (PackedWordRAM.execute memory i s).2⟩ (by simp [PackedWordRAM.step, hstatus, hi])
          have he := execute_encode width capacity memory i s hm hst.1 hst.2 (hw i himem) hz
          have hn := congrArg Prod.fst he
          have hr := congrArg Prod.snd he
          dsimp only at hn hr
          simp only [hi, Option.map_some, decodeInstruction_encode _ _ (hp i himem),
            PackedWordRAM.step, hstatus, Transition.encode, hn, hr]

/-- The safety premise quantifies over the actual reference transitions. -/
def RunSafe (width : Nat) (r : PackedWordRAM.Run) : Prop :=
  ∀ t ∈ r.transitions, Instruction.Safe width t.before t.instruction ∧ t.after.Fits width

theorem run_encode (width capacity : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (fuel : Nat) (s : PackedWordRAM.State)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (hsafe : RunSafe width (PackedWordRAM.run memory program fuel s)) :
    run width (encodeMemory width memory) (encodeCode width program) fuel
      (State.encode width capacity s) =
      Run.encode width capacity (PackedWordRAM.run memory program fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      have hcurrent : ∀ t, PackedWordRAM.step memory program s = some t →
          Instruction.Safe width t.before t.instruction ∧ t.after.Fits width := by
        intro t ht
        exact hsafe t (by simp [PackedWordRAM.run, ht])
      have hstep := step_encode width capacity memory program s hm hp hw hf hz hcurrent
      cases ht : PackedWordRAM.step memory program s with
      | none => simp [run, hstep, ht, PackedWordRAM.run, Run.encode]
      | some t =>
          have hspec := PackedWordRAM.step_spec ht
          have hmem : t.instruction ∈ program := List.mem_of_getElem? hspec.2.2.1
          have hz' : ∀ r, capacity ≤ r → t.after.regs r = 0 := by
            have hzexec := execute_zero_tail memory t.instruction capacity s (hw _ hmem) hz
            simpa [hspec.2.2.2] using hzexec
          have hrest : RunSafe width (PackedWordRAM.run memory program fuel t.after) := by
            intro u hu
            exact hsafe u (by simp [PackedWordRAM.run, ht, hu])
          have heq := ih t.after (hcurrent t ht).2 hz' hrest
          simp only [run, hstep, ht, PackedWordRAM.run, Transition.encode, heq,
            Run.encode, List.map_cons]

theorem reference_run_final_fits (width : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (fuel : Nat) (s : PackedWordRAM.State)
    (hf : s.Fits width) (hsafe : RunSafe width (PackedWordRAM.run memory program fuel s)) :
    (PackedWordRAM.run memory program fuel s).final.Fits width := by
  induction fuel generalizing s with
  | zero => exact hf
  | succ fuel ih =>
      cases ht : PackedWordRAM.step memory program s with
      | none => simpa [PackedWordRAM.run, ht] using hf
      | some t =>
          have hfirst := hsafe t (by simp [PackedWordRAM.run, ht])
          have hrest : RunSafe width (PackedWordRAM.run memory program fuel t.after) := by
            intro u hu; exact hsafe u (by simp [PackedWordRAM.run, ht, hu])
          simpa [PackedWordRAM.run, ht] using ih t.after hfirst.2 hrest

theorem reference_run_zero_tail (capacity : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (fuel : Nat) (s : PackedWordRAM.State)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hz : ∀ r, capacity ≤ r → s.regs r = 0) :
    ∀ r, capacity ≤ r → (PackedWordRAM.run memory program fuel s).final.regs r = 0 := by
  induction fuel generalizing s with
  | zero => exact hz
  | succ fuel ih =>
      cases ht : PackedWordRAM.step memory program s with
      | none => simpa [PackedWordRAM.run, ht] using hz
      | some t =>
          have hspec := PackedWordRAM.step_spec ht
          have hz' := execute_zero_tail memory t.instruction capacity s
            (hw _ (List.mem_of_getElem? hspec.2.2.1)) hz
          rw [hspec.2.2.2] at hz'
          simpa [PackedWordRAM.run, ht] using ih t.after hz'

theorem reference_transition_zero_tail (capacity : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (fuel : Nat) (s : PackedWordRAM.State)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (t : PackedWordRAM.Transition) (ht : t ∈ (PackedWordRAM.run memory program fuel s).transitions) :
    (∀ r, capacity ≤ r → t.before.regs r = 0) ∧
    (∀ r, capacity ≤ r → t.after.regs r = 0) := by
  induction fuel generalizing s with
  | zero => simp [PackedWordRAM.run] at ht
  | succ fuel ih =>
      cases hstep : PackedWordRAM.step memory program s with
      | none => simp [PackedWordRAM.run, hstep] at ht
      | some first =>
          have hspec := PackedWordRAM.step_spec hstep
          have hz' := execute_zero_tail memory first.instruction capacity s
            (hw _ (List.mem_of_getElem? hspec.2.2.1)) hz
          rw [hspec.2.2.2] at hz'
          simp only [PackedWordRAM.run, hstep, List.mem_cons] at ht
          rcases ht with heq | hmem
          · subst t
            exact ⟨by simpa [hspec.1] using hz, hz'⟩
          · exact ih first.after hz' hmem

/-- Complete equality with the original run: states, ordered transitions and replies. -/
theorem run_reference (width capacity : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (fuel : Nat) (s : PackedWordRAM.State)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (hsafe : RunSafe width (PackedWordRAM.run memory program fuel s)) :
    (run width (encodeMemory width memory) (encodeCode width program) fuel
      (State.encode width capacity s)).decode = PackedWordRAM.run memory program fuel s := by
  rw [run_encode _ _ _ _ _ _ hm hp hw hf hz hsafe]
  unfold Run.decode Run.encode
  rw [State.decode_encode _ _ _ (reference_run_final_fits _ _ _ _ _ hf hsafe)
    (reference_run_zero_tail _ _ _ _ _ hw hz)]
  congr 1
  rw [List.map_map]
  calc
    _ = (PackedWordRAM.run memory program fuel s).transitions.map id := by
      apply List.map_congr_left
      intro t ht
      have hst := hsafe t ht
      have hzt := reference_transition_zero_tail _ _ _ _ _ hw hz t ht
      simp only [Function.comp_def, Transition.encode, Transition.decode,
        State.decode_encode _ _ _ hst.1.2.1 hzt.1,
        State.decode_encode _ _ _ hst.2 hzt.2, id_eq]
    _ = _ := List.map_id _

/-- Native observations are a projection of the exact original operational run. -/
theorem runThin_reference (observeReads : Bool) (width capacity : Nat)
    (memory : PackedWordRAM.Memory) (program : Program) (fuel : Nat)
    (s : PackedWordRAM.State) (a : Stats)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (hsafe : RunSafe width (PackedWordRAM.run memory program fuel s)) :
    let output := runThin observeReads width (encodeMemory width memory)
      (encodeCode width program) fuel (State.encode width capacity s) a
    (output.1.decode, output.2) =
      observeRun observeReads (PackedWordRAM.run memory program fuel s) a := by
  rw [runThin_projection, ← run_reference _ _ _ _ _ _ hm hp hw hf hz hsafe]
  simp only [observeRun, Run.decode, List.foldl_map]
  rfl

def State.Canonical (width : Nat) (s : State) : Prop :=
  LimbWord.Canonical width s.pc ∧
  (∀ word ∈ s.regs.toList, LimbWord.Canonical width word) ∧
  match s.status with | .halted packet => LimbWord.Canonical width packet | _ => True

theorem State.decode_zero_tail (s : State) :
    ∀ r, s.regs.size ≤ r → s.decode.regs r = 0 := by
  intro r hr
  simp [State.decode, Array.getElem?_eq_none hr]

theorem State.decode_fits (width : Nat) (s : State) (hc : s.Canonical width) :
    s.decode.Fits width := by
  refine ⟨hc.1.2, ?_, ?_⟩
  · intro r
    cases hr : s.regs[r]? with
    | none => simpa [State.decode, hr] using Nat.two_pow_pos width
    | some word =>
        have hm : word ∈ s.regs.toList := List.mem_of_getElem? (by simpa using hr)
        simpa [State.decode, hr] using (hc.2.1 word hm).2
  · intro value hv
    cases hs : s.status with
    | running => simp [State.decode, Status.decode, hs] at hv
    | fault => simp [State.decode, Status.decode, hs] at hv
    | halted packet =>
        have hp : LimbWord.Canonical width packet := by simpa [State.Canonical, hs] using hc.2.2
        simp only [State.decode, hs, Status.decode, PackedWordRAM.Status.halted.injEq] at hv
        simpa [hv] using hp.2

/-- Every canonical loaded byte-state is exactly the encoding of its own decode. -/
theorem State.encode_decode (width : Nat) (s : State) (hc : s.Canonical width) :
    State.encode width s.regs.size s.decode = s := by
  cases s with
  | mk regs pc status =>
      rcases hc with ⟨hpc, hregs, hstatus⟩
      unfold State.encode State.decode
      simp only [LimbWord.encode_decode width pc hpc.1]
      congr 1
      · apply Array.ext
        · simp
        · intro r hr hl
          have hm : regs[r] ∈ regs.toList := by simp
          have hw := hregs _ hm
          simp only [Array.getElem_ofFn, Array.getElem?_eq_getElem hl, Option.map_some, Option.getD_some]
          exact LimbWord.encode_decode _ _ hw.1
      · cases status with
        | running => rfl
        | fault => rfl
        | halted packet =>
            simp only [Status.decode, Status.encode]
            congr 1
            exact LimbWord.encode_decode _ _ hstatus.1

theorem execute_missing_memory (width : Nat) (memory : Memory) (s : State) (dst address : Nat)
    (ha : LimbWord.Canonical width (s.readWord width address))
    (hm : memory[LimbWord.decode (s.readWord width address)]? = none) :
    execute width memory (.load dst address) s =
      fail s .missingMemory (some ⟨LimbWord.decode (s.readWord width address), none⟩) := by
  simp [execute, ha, hm]

theorem step_missing_fetch (width : Nat) (memory : Memory) (program : Code) (s : State)
    (hs : s.status = .running) (hp : LimbWord.Canonical width s.pc)
    (hf : program[LimbWord.decode s.pc]? = none) :
    step width memory program s = .stopped := by
  simp [step, hs, hp, hf]

theorem run_of_stopped (width : Nat) (memory : Memory) (program : Code)
    (fuel : Nat) (s : State) (h : step width memory program s = .stopped) :
    run width memory program fuel s = ⟨s, []⟩ := by
  cases fuel <;> simp [run, h]

theorem step_malformed_code (width : Nat) (memory : Memory) (program : Code) (s : State)
    (fields : Array Word) (message : String)
    (hs : s.status = .running) (hp : LimbWord.Canonical width s.pc)
    (hf : program[LimbWord.decode s.pc]? = some fields)
    (hc : decodeInstruction width fields = .error message) :
    step width memory program s = .rejected { s with status := .fault } .malformedCode := by
  simp [step, hs, hp, hf, hc]

theorem execute_arithmetic_rejected (width : Nat) (memory : Memory) (s : State)
    (op : Arithmetic) (dst lhs rhs : Nat) (why : WordFault)
    (h : checkedArithmetic width op (s.readWord width lhs) (s.readWord width rhs) = .error why) :
    execute width memory (.arithmetic op dst lhs rhs) s = fail s (.word why) := by
  simp [execute, h, writeResult]

def MemoryCanonical (width : Nat) (memory : Memory) : Prop :=
  ∀ word ∈ memory.toList, LimbWord.Canonical width word

theorem decodeMemory_fits (width : Nat) (memory : Memory) (hc : MemoryCanonical width memory) :
    ∀ value ∈ decodeMemory memory, value < 2 ^ width := by
  intro value hv
  obtain ⟨word, hw, rfl⟩ := List.mem_map.1 hv
  exact (hc word hw).2

/-- No replacement store: re-encoding the loaded canonical cells gives the same array. -/
theorem encodeMemory_decode (width : Nat) (memory : Memory) (hc : MemoryCanonical width memory) :
    encodeMemory width (decodeMemory memory) = memory := by
  unfold encodeMemory decodeMemory
  rw [List.map_map]
  have he : memory.toList.map (LimbWord.encode width ∘ LimbWord.decode) = memory.toList := by
    calc
      _ = memory.toList.map id := List.map_congr_left fun word hw =>
        LimbWord.encode_decode _ _ (hc word hw).1
      _ = _ := List.map_id _
  rw [he]

/-- Canonical loaded bytes use the same machine as encoded reference inputs. -/
theorem run_loaded_reference (width : Nat) (memory : Memory) (program : Program)
    (code : Code) (fuel : Nat) (s : State)
    (hm : MemoryCanonical width memory) (hc : s.Canonical width)
    (hcode : code = encodeCode width program)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < s.regs.size))
    (hsafe : RunSafe width (PackedWordRAM.run (decodeMemory memory) program fuel s.decode)) :
    (run width memory code fuel s).decode =
      PackedWordRAM.run (decodeMemory memory) program fuel s.decode := by
  have he := run_reference width s.regs.size (decodeMemory memory) program fuel s.decode
    (decodeMemory_fits _ _ hm) hp hw (State.decode_fits _ _ hc) (State.decode_zero_tail s) hsafe
  rw [encodeMemory_decode _ _ hm, State.encode_decode _ _ hc, ← hcode] at he
  exact he

theorem runThin_loaded_reference (observeReads : Bool) (width : Nat) (memory : Memory)
    (program : Program) (code : Code) (fuel : Nat) (s : State) (a : Stats)
    (hm : MemoryCanonical width memory) (hc : s.Canonical width)
    (hcode : code = encodeCode width program)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < s.regs.size))
    (hsafe : RunSafe width (PackedWordRAM.run (decodeMemory memory) program fuel s.decode)) :
    let output := runThin observeReads width memory code fuel s a
    (output.1.decode, output.2) =
      observeRun observeReads (PackedWordRAM.run (decodeMemory memory) program fuel s.decode) a := by
  rw [runThin_projection, ← run_loaded_reference _ _ _ _ _ _ hm hc hcode hp hw hsafe]
  simp only [observeRun, Run.decode, List.foldl_map]
  rfl

@[simp] theorem encodeMemory_size (width : Nat) (memory : PackedWordRAM.Memory) :
    (encodeMemory width memory).size = memory.length := by simp [encodeMemory]

@[simp] theorem encodeInstruction_size (width : Nat) (i : Instruction) :
    (encodeInstruction width i).size = i.encoding.length := by simp [encodeInstruction]

@[simp] theorem encodeCode_size (width : Nat) (program : Program) :
    (encodeCode width program).size = program.length := by simp [encodeCode]

theorem State.canonical_encode (width capacity : Nat) (s : PackedWordRAM.State)
    (hf : s.Fits width) : (State.encode width capacity s).Canonical width := by
  refine ⟨LimbWord.canonical_encode _ _ hf.1, ?_, ?_⟩
  · intro word hw
    simp only [State.encode, Array.mem_toList_iff, Array.mem_ofFn] at hw
    obtain ⟨r, rfl⟩ := hw
    exact LimbWord.canonical_encode _ _ (hf.2.1 r.val)
  · cases hs : s.status with
    | running => simp [State.encode, Status.encode, hs]
    | fault => simp [State.encode, Status.encode, hs]
    | halted packet =>
        simpa [State.encode, Status.encode, hs] using
          (LimbWord.canonical_encode width packet (hf.2.2 packet hs))

theorem memoryCanonical_encode (width : Nat) (memory : PackedWordRAM.Memory)
    (hm : ∀ value ∈ memory, value < 2 ^ width) :
    MemoryCanonical width (encodeMemory width memory) := by
  intro word hw
  simp only [encodeMemory, List.toList_toArray, List.mem_map] at hw
  obtain ⟨value, hv, rfl⟩ := hw
  exact LimbWord.canonical_encode _ _ (hm value hv)

theorem run_final_canonical (width capacity : Nat) (memory : PackedWordRAM.Memory)
    (program : Program) (fuel : Nat) (s : PackedWordRAM.State)
    (hm : ∀ value ∈ memory, value < 2 ^ width)
    (hp : ∀ i ∈ program, i.Fits width)
    (hw : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hf : s.Fits width) (hz : ∀ r, capacity ≤ r → s.regs r = 0)
    (hsafe : RunSafe width (PackedWordRAM.run memory program fuel s)) :
    (run width (encodeMemory width memory) (encodeCode width program) fuel
      (State.encode width capacity s)).final.Canonical width ∧
    (run width (encodeMemory width memory) (encodeCode width program) fuel
      (State.encode width capacity s)).final.regs.size = capacity := by
  rw [run_encode _ _ _ _ _ _ hm hp hw hf hz hsafe]
  exact ⟨State.canonical_encode _ _ _ (reference_run_final_fits _ _ _ _ _ hf hsafe),
    State.encode_size _ _ _⟩

theorem reference_prefix_transition_mem (memory : PackedWordRAM.Memory) (program : Program)
    (fuel budget : Nat) (s : PackedWordRAM.State) (hbudget : fuel ≤ budget)
    (t : PackedWordRAM.Transition) (ht : t ∈ (PackedWordRAM.run memory program fuel s).transitions) :
    t ∈ (PackedWordRAM.run memory program budget s).transitions := by
  have hsplit : budget = fuel + (budget - fuel) := by omega
  rw [hsplit, PackedWordRAM.run_add]
  simp [ht]

/-- Safety of the actual full trace implies safety of every fuel prefix. -/
theorem RunSafe.prefix (width : Nat) (memory : PackedWordRAM.Memory) (program : Program)
    (fuel budget : Nat) (s : PackedWordRAM.State) (hbudget : fuel ≤ budget)
    (hsafe : RunSafe width (PackedWordRAM.run memory program budget s)) :
    RunSafe width (PackedWordRAM.run memory program fuel s) := by
  intro t ht
  exact hsafe t (reference_prefix_transition_mem _ _ _ _ _ hbudget t ht)

end RMQ.SuccinctFinal.PackedNative.LimbMachine
