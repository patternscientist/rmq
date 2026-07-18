import RMQ.Core.WordRAM.E1MachineCalculus

/-!
# E1 amended machine: straight-line segment execution (M3c-1b)

Symbolic execution of branch-free code segments in one lemma.  The concrete
component blocks (rank-close, select-close, close/LCA) are long chains of
`const`/`sub`/`divConst`/`mulConst`/`readMem` instructions punctuated by a
few `brNZ` branches.  Proving them step by step in the `RunsTo.const` style
of the guard prologue would repeat the same mechanical state-threading
hundreds of times, so this module packages it once:

* `Instr.isStraight` — every constructor except `brNZ`/`halt` advances the
  pc by one and never redirects control;
* `straightStepRegs`/`straightStepEvent` — the register-file effect and the
  at-most-one read receipt of one straight instruction (the same formulas
  as `execInstr`, exposed as plain functions so `simp` can evaluate them
  register by register);
* `straightRegs`/`straightReads` — their fold over a code segment;
* `RunsTo.straight` — a hosted, all-straight code segment runs from any
  register file to the folded register file, with the folded receipts and
  exactly one charge category tick per instruction
  (`code.map Instr.category`).

Everything is machine-generic; nothing mentions the RMQ route.
-/

namespace RMQ
namespace WordRAM
namespace E1Machine

/-- Straight-line instructions: advance the pc by one, never redirect. -/
def Instr.isStraight : Instr -> Bool
  | .brNZ .. => false
  | .halt => false
  | _ => true

/-- Register-file effect of one straight instruction (the `execInstr`
register formula, exposed as a plain function). -/
def straightStepRegs (store : ReadStore) (regs : RegFile) : Instr -> RegFile
  | .readMem dst segment addrReg =>
      regs.write dst (decodeRead (store.readWord? segment (regs addrReg)))
  | .const dst value => regs.write dst value
  | .move dst src => regs.write dst (regs src)
  | .add dst src₁ src₂ => regs.write dst (regs src₁ + regs src₂)
  | .sub dst src₁ src₂ => regs.write dst (regs src₁ - regs src₂)
  | .mulConst dst src k => regs.write dst (regs src * k)
  | .divConst dst src k => regs.write dst (regs src / k)
  | .natLt dst src₁ src₂ =>
      regs.write dst (if regs src₁ < regs src₂ then 1 else 0)
  | .natLe dst src₁ src₂ =>
      regs.write dst (if regs src₁ <= regs src₂ then 1 else 0)
  | .natEq dst src₁ src₂ =>
      regs.write dst (if regs src₁ = regs src₂ then 1 else 0)
  | .brNZ .. => regs
  | .halt => regs

/-- Receipt of one straight instruction: `readMem` emits its read, nothing
else emits. -/
def straightStepEvent (store : ReadStore) (regs : RegFile) :
    Instr -> Option TraceEvent
  | .readMem _dst segment addrReg =>
      some
        (.readWord segment (regs addrReg)
          (store.readWord? segment (regs addrReg)))
  | _ => none

/-- Folded register file of a straight code segment. -/
def straightRegs (store : ReadStore) : List Instr -> RegFile -> RegFile
  | [], regs => regs
  | instr :: rest, regs =>
      straightRegs store rest (straightStepRegs store regs instr)

@[simp] theorem straightRegs_nil (store : ReadStore) (regs : RegFile) :
    straightRegs store [] regs = regs := rfl

theorem straightRegs_cons (store : ReadStore) (instr : Instr)
    (rest : List Instr) (regs : RegFile) :
    straightRegs store (instr :: rest) regs =
      straightRegs store rest (straightStepRegs store regs instr) := rfl

/-- Folded receipts of a straight code segment. -/
def straightReads (store : ReadStore) : List Instr -> RegFile -> List TraceEvent
  | [], _ => []
  | instr :: rest, regs =>
      (straightStepEvent store regs instr).toList ++
        straightReads store rest (straightStepRegs store regs instr)

@[simp] theorem straightReads_nil (store : ReadStore) (regs : RegFile) :
    straightReads store [] regs = [] := rfl

theorem straightReads_cons (store : ReadStore) (instr : Instr)
    (rest : List Instr) (regs : RegFile) :
    straightReads store (instr :: rest) regs =
      (straightStepEvent store regs instr).toList ++
        straightReads store rest (straightStepRegs store regs instr) := rfl

/-- One straight instruction executes to the step formulas. -/
theorem execInstr_straight (store : ReadStore) {instr : Instr}
    (hstraight : instr.isStraight = true) (regs : RegFile) (pcv : Nat) :
    execInstr store instr ⟨regs, pcv, false⟩ =
      (⟨straightStepRegs store regs instr, pcv + 1, false⟩,
        instr.category, straightStepEvent store regs instr) := by
  cases instr <;>
    first
      | rfl
      | exact absurd hstraight (by simp [Instr.isStraight])

/--
Straight-line segment execution: a hosted, all-straight code segment runs
from any register file at its base to the folded register file one past the
segment, emitting the folded receipts and exactly one charge category tick
per instruction.
-/
theorem RunsTo.straight (store : ReadStore) {program : Program} :
    forall (code : List Instr),
      (forall instr, instr ∈ code -> instr.isStraight = true) ->
      forall (base : Nat), HostedAt program base code ->
      forall (regs : RegFile),
        RunsTo store program ⟨regs, base, false⟩
          ⟨straightRegs store code regs, base + code.length, false⟩
          (straightReads store code regs) (code.map Instr.category) := by
  intro code
  induction code with
  | nil =>
      intro _ base _ regs
      show RunsTo store program ⟨regs, base, false⟩
        ⟨regs, base + 0, false⟩ [] []
      exact RunsTo.refl store program ⟨regs, base, false⟩
  | cons instr rest ih =>
      intro hstraight base hhost regs
      have hhead : program[base]? = some instr := hhost.head
      have hstep :
          RunsTo store program ⟨regs, base, false⟩
            ⟨straightStepRegs store regs instr, base + 1, false⟩
            (straightStepEvent store regs instr).toList
            [instr.category] :=
        RunsTo.step rfl hhead
          (execInstr_straight store (hstraight instr (by simp)) regs base)
      have hrest :=
        ih (fun i hi => hstraight i (by simp [hi])) (base + 1) hhost.tail
          (straightStepRegs store regs instr)
      have hall := hstep.trans hrest
      rw [straightReads_cons, straightRegs_cons]
      show RunsTo store program ⟨regs, base, false⟩
        ⟨straightRegs store rest (straightStepRegs store regs instr),
          base + (rest.length + 1), false⟩ _ _
      have harith : base + 1 + rest.length = base + (rest.length + 1) := by
        omega
      rw [harith] at hall
      exact hall

/-! ## Register-preservation helpers -/

/-- Destination register of an instruction, if it writes one. -/
def Instr.writesTo : Instr -> Option Nat
  | .readMem dst .. => some dst
  | .const dst .. => some dst
  | .move dst .. => some dst
  | .add dst .. => some dst
  | .sub dst .. => some dst
  | .mulConst dst .. => some dst
  | .divConst dst .. => some dst
  | .natLt dst .. => some dst
  | .natLe dst .. => some dst
  | .natEq dst .. => some dst
  | .brNZ .. => none
  | .halt => none

/-- A straight step leaves every register it does not target unchanged. -/
theorem straightStepRegs_preserves (store : ReadStore) (regs : RegFile)
    (instr : Instr) (r : Nat) (h : instr.writesTo ≠ some r) :
    straightStepRegs store regs instr r = regs r := by
  cases instr <;>
    first
      | rfl
      | exact
          RegFile.write_other _ _
            (fun hcontra => h (by simp [Instr.writesTo, hcontra]))

/-- A straight segment leaves every register it never targets unchanged. -/
theorem straightRegs_preserves (store : ReadStore) :
    forall (code : List Instr) (regs : RegFile) (r : Nat),
      (forall instr, instr ∈ code -> instr.writesTo ≠ some r) ->
      straightRegs store code regs r = regs r := by
  intro code
  induction code with
  | nil =>
      intro regs r _
      rfl
  | cons instr rest ih =>
      intro regs r h
      rw [straightRegs_cons,
        ih (straightStepRegs store regs instr) r
          (fun i hi => h i (by simp [hi])),
        straightStepRegs_preserves store regs instr r (h instr (by simp))]

/-! ## Branch step helpers -/

/-- A `brNZ` whose condition register holds zero falls through. -/
theorem RunsTo.brNZ_not_taken {store : ReadStore} {program : Program}
    {s : State} {cond target : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.brNZ cond target))
    (hcond : s.regs cond = 0) :
    RunsTo store program s ⟨s.regs, s.pc + 1, false⟩ [] [.branch] := by
  have h := RunsTo.brNZ (store := store) hhalt hfetch
  rw [hcond] at h
  simpa using h

/-- A `brNZ` whose condition register holds nonzero jumps to its target. -/
theorem RunsTo.brNZ_taken {store : ReadStore} {program : Program}
    {s : State} {cond target : Nat} (hhalt : s.halted = false)
    (hfetch : program[s.pc]? = some (.brNZ cond target))
    (hcond : s.regs cond ≠ 0) :
    RunsTo store program s ⟨s.regs, target, false⟩ [] [.branch] := by
  have h := RunsTo.brNZ (store := store) hhalt hfetch
  rw [if_neg hcond] at h
  exact h

end E1Machine
end WordRAM
end RMQ
