import RMQ.Core.WordRAM.Lifecycle.QueryBridge
import RMQ.Core.WordRAM.Lifecycle.QueryEntry
import RMQ.Core.WordRAM.Lifecycle.Calculus

/-! # One fixed reusable query-service prefix

The request slots are copied only after a charged load of n from the retained
allocation. Full finite-bank clearing and the jump then use the checked entry
adapter. This prefix can be followed by the construction and retirement code.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Service

open PackedWordRAM.Optimization

set_option maxRecDepth 30000

attribute [local irreducible] compactQueryProgram QueryEntry.setupCode

abbrev QueryState := PackedWordRAM.State
abbrev QueryProgram := PackedWordRAM.Program
abbrev QueryMemory := PackedWordRAM.Memory

def prepare : QueryProgram := [.constant 2 0, .load 2 2, .move 0 300, .move 1 301]
def program : QueryProgram := compactQueryProgram ++ (prepare ++ QueryEntry.setupCode)
def entry : Nat := 212964
def budget : Nat := 4 + QueryEntry.setupCost + compactQueryBudget

attribute [local irreducible] program entry budget

theorem entry_eq : entry = 212964 := by rw [entry]

theorem entry_length : entry = compactQueryProgram.length := by
  rw [entry]
  exact compactQueryProgram_length_eq.symm
theorem prepare_length : prepare.length = 4 := rfl
theorem budget_eq : budget = 160253 := by
  rw [budget, QueryEntry.setupCost_eq, compactQueryBudget_eq]

theorem program_length : program.length = 221239 := by
  rw [program, List.length_append, compactQueryProgram_length_eq,
    List.length_append, prepare_length, QueryEntry.setupCode_length, QueryEntry.setupCost_eq]

def Inputs (left right : Nat) (s : QueryState) : Prop :=
  s.status = .running ∧ s.pc = entry ∧ s.regs 300 = left ∧ s.regs 301 = right ∧
    ∀ r, 8273 ≤ r → s.regs r = 0

def preparedAt (base n : Nat) (s : QueryState) : QueryState :=
  { regs := ((s.regs.write 2 n).write 0 (s.regs 300)).write 1 (s.regs 301)
    pc := base + 4
    status := .running }

abbrev prepared (n : Nat) (s : QueryState) : QueryState := preparedAt entry n s

theorem middle_host (pre fragment suffix : QueryProgram) :
    PackedWordRAM.Structured.HostedAt (pre ++ (fragment ++ suffix)) pre.length fragment := by
  intro i hi
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

theorem tail_host (pre middle suffix : QueryProgram) :
    PackedWordRAM.Structured.HostedAt (pre ++ (middle ++ suffix))
      (pre.length + middle.length) suffix := by
  intro i hi
  rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem prepare_fetch (i : Nat) (hi : i < 4) :
    program[entry + i]? = prepare[i]? := by
  rw [program, entry_length]
  exact middle_host compactQueryProgram prepare QueryEntry.setupCode i
    (by simpa only [prepare_length] using hi)

theorem preparation_tail_host (pre suffix : QueryProgram) :
    PackedWordRAM.Structured.HostedAt (pre ++ (prepare ++ suffix)) (pre.length + 4) suffix := by
  have h := tail_host pre prepare suffix
  rw [prepare_length] at h
  exact h

theorem setup_host : PackedWordRAM.Structured.HostedAt program (entry + 4)
    QueryEntry.setupCode := by
  rw [program, entry_length]
  exact preparation_tail_host compactQueryProgram QueryEntry.setupCode

theorem prepare_exec_at (memory : QueryMemory) (p : QueryProgram) (base n : Nat) (s : QueryState)
    (header : memory[0]? = some n) (hr : s.status = .running) (hpc : s.pc = base)
    (host : ∀ i, i < 4 → p[base+i]? = prepare[i]?) :
    (PackedWordRAM.run memory p 4 s).final = preparedAt base n s ∧
    (PackedWordRAM.run memory p 4 s).steps = 4 ∧
    (PackedWordRAM.run memory p 4 s).reads = [⟨0, some n⟩] := by
  have h0 := host 0 (by decide)
  have h1 := host 1 (by decide)
  have h2 := host 2 (by decide)
  have h3 := host 3 (by decide)
  simp only [prepare, List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.add_zero] at h0 h1 h2 h3
  simp [PackedWordRAM.run, PackedWordRAM.step, PackedWordRAM.execute, hpc, hr,
    h0, h1, h2, h3, header, PackedWordRAM.State.writeNext,
    PackedWordRAM.Registers.write, Nat.add_assoc, preparedAt,
    PackedWordRAM.Run.steps, PackedWordRAM.Run.reads]
  funext r
  by_cases h : r = 2 <;> simp [PackedWordRAM.Registers.write, h]

theorem prepare_exec (memory : QueryMemory) (n left right : Nat) (s : QueryState)
    (header : memory[0]? = some n) (inputs : Inputs left right s) :
    (PackedWordRAM.run memory program 4 s).final = prepared n s ∧
    (PackedWordRAM.run memory program 4 s).steps = 4 ∧
    (PackedWordRAM.run memory program 4 s).reads = [⟨0, some n⟩] :=
  prepare_exec_at memory program entry n s header inputs.1 inputs.2.1 prepare_fetch

theorem prepared_inputs (n left right : Nat) (s : QueryState) (inputs : Inputs left right s) :
    QueryEntry.SetupInputs n left right (prepared n s) := by
  obtain ⟨_, _, hl, hr, ht⟩ := inputs
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [prepared, preparedAt, PackedWordRAM.Registers.write, hl]
  · simp [prepared, preparedAt, PackedWordRAM.Registers.write, hr]
  · simp [prepared, preparedAt, PackedWordRAM.Registers.write]
  · intro r hout
    have hh : 8273 ≤ r := by rw [compactQueryRegisterCount_eq] at hout; exact hout
    simp [prepared, preparedAt, PackedWordRAM.Registers.write, show r ≠ 0 by omega,
      show r ≠ 1 by omega, show r ≠ 2 by omega, ht r hh]

theorem completed (memory : QueryMemory) (n left right : Nat) (s : QueryState)
    (header : memory[0]? = some n) (inputs : Inputs left right s) :
    ∃ setupTransitions,
      PackedWordRAM.run memory program budget s =
        ⟨(compactQueryRun memory n left right).final,
          (PackedWordRAM.run memory program 4 s).transitions ++ setupTransitions ++
            (compactQueryRun memory n left right).transitions⟩ ∧
      setupTransitions.length = QueryEntry.setupCost ∧
      setupTransitions.filterMap (·.receipt) = [] := by
  have hp := prepare_exec memory n left right s header inputs
  obtain ⟨ts, _, hlen, hreads, hrun⟩ := QueryEntry.chargedEntry_compactQuery
    memory (prepare ++ QueryEntry.setupCode) n left right (prepared n s)
      (prepared_inputs n left right s inputs) (by simpa only [prepared, preparedAt, program] using setup_host)
  rw [← program] at hrun
  refine ⟨ts, ?_, hlen, hreads⟩
  rw [budget, Nat.add_assoc, PackedWordRAM.run_add]
  dsimp only
  rw [hp.1]
  rw [hrun]
  simp [List.append_assoc]

theorem observations (memory : QueryMemory) (n left right : Nat) (s : QueryState)
    (header : memory[0]? = some n) (inputs : Inputs left right s) :
    let actual := PackedWordRAM.run memory program budget s
    let query := compactQueryRun memory n left right
    actual.final = query.final ∧ actual.result = query.result ∧
      actual.reads = ⟨0, some n⟩ :: query.reads ∧
      actual.steps = 4 + QueryEntry.setupCost + query.steps ∧
      actual.steps ≤ 160253 ∧ actual.final.status ≠ .running := by
  obtain ⟨ts, he, hlen, hreads⟩ := completed memory n left right s header inputs
  have hp := prepare_exec memory n left right s header inputs
  have hbound := compactQueryRun_steps_le memory n left right
  have hstop := compactQueryRun_stopped memory n left right
  have hplen : (PackedWordRAM.run memory program 4 s).transitions.length = 4 := hp.2.1
  have hpreads : (PackedWordRAM.run memory program 4 s).transitions.filterMap (·.receipt) =
      [⟨0, some n⟩] := hp.2.2
  dsimp only
  rw [he]
  simp only [PackedWordRAM.Run.result, PackedWordRAM.Run.reads, PackedWordRAM.Run.steps,
    List.filterMap_append, List.length_append, hlen, hreads, List.append_nil,
    hplen, hpreads, List.cons_append, List.nil_append, true_and]
  refine ⟨?_, hstop⟩
  rw [QueryEntry.setupCost_eq]
  rw [compactQueryBudget_eq] at hbound
  change (compactQueryRun memory n left right).transitions.length ≤ 151978 at hbound
  omega

end RMQ.SuccinctFinal.PackedLifecycle.Service
