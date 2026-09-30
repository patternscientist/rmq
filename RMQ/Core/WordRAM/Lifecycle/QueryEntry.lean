import RMQ.Core.WordRAM.Optimization.QuerySafety
import RMQ.Core.WordRAM.Optimization.QueryProof

/-! # Charged compact-query entry in an arbitrary host

Each finite-bank clear and the final jump is an actual packed instruction.
The caller supplies already produced ABI values and running control; these
lemmas do not implement or assume a free external request-admission step.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.QueryEntry
open PackedWordRAM PackedWordRAM.Structured PackedWordRAM.Optimization
set_option maxRecDepth 30000

/- A successful old fetch is unchanged by append. No confinement assumption. -/
theorem step_append_of_some {memory : Memory} {program suffix : Program}
    {s : State} {t : Transition} (h : step memory program s = some t) :
    step memory (program ++ suffix) s = some t := by
  obtain ⟨hb, hs, hf, he⟩ := step_spec h
  have bound : s.pc < program.length := (List.getElem?_eq_some_iff.mp hf).choose
  have fetch : (program ++ suffix)[s.pc]? = some t.instruction := by
    rw [List.getElem?_append_left bound, hf]
  cases t
  simp_all [step]

theorem run_append_of_stopped (memory : Memory) (program suffix : Program)
    (fuel : Nat) (s : State)
    (stopped : (run memory program fuel s).final.status ≠ .running) :
    run memory (program ++ suffix) fuel s = run memory program fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
      cases hs : step memory program s with
      | none =>
          have hn : s.status ≠ .running := by simpa [run, hs] using stopped
          have he : step memory (program ++ suffix) s = none := by
            cases hstatus : s.status <;> simp_all [step]
          simp [run, hs, he]
      | some t =>
          have he := step_append_of_some (suffix := suffix) hs
          have ht : (run memory program fuel t.after).final.status ≠ .running := by
            simpa [run, hs] using stopped
          simp only [run, hs, he]
          rw [ih t.after ht]

/-- The compiler-derived stop closes the append proof, even on arbitrary memory. -/
theorem compactQuery_prefix (memory : Memory) (n left right : Nat) (suffix : Program) :
    run memory (compactQueryProgram ++ suffix) compactQueryBudget
      (initialState n left right) = compactQueryRun memory n left right :=
  run_append_of_stopped memory compactQueryProgram suffix compactQueryBudget
    (initialState n left right) (compactQueryRun_stopped memory n left right)

/-- Every preserved occurrence fetched an instruction from the old prefix. -/
theorem compactQuery_fetch_confined (memory : Memory) (n left right : Nat)
    (suffix : Program) (k : Nat) (t : Transition)
    (occurrence : (run memory (compactQueryProgram ++ suffix) compactQueryBudget
      (initialState n left right)).transitions[k]? = some t) :
    t.before.pc < compactQueryProgram.length ∧
    compactQueryProgram[t.before.pc]? = some t.instruction := by
  rw [compactQuery_prefix] at occurrence
  have fetch := (run_transition_spec occurrence).2.2.1
  exact ⟨(List.getElem?_eq_some_iff.mp fetch).choose, fetch⟩

def clearCode (first : Nat) : Nat → Program
  | 0 => []
  | count + 1 => .constant first 0 :: clearCode (first + 1) count

theorem clearCode_length (first count : Nat) : (clearCode first count).length = count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih => simp [clearCode, ih]

def cleared (s : State) (first count : Nat) : State :=
  ⟨fun r => if first ≤ r ∧ r < first + count then 0 else s.regs r,
    s.pc + count, .running⟩

theorem cleared_zero (s : State) (first : Nat) (hs : s.status = .running) :
    cleared s first 0 = s := by
  cases s with
  | mk regs pc status =>
    cases hs
    simp only [cleared, Nat.add_zero]
    congr 1
    funext r
    rw [if_neg (show ¬ (first ≤ r ∧ r < first) by omega)]

theorem cleared_succ (s : State) (first count : Nat) :
    cleared (s.writeNext first 0) (first + 1) count = cleared s first (count + 1) := by
  simp only [cleared, State.writeNext]
  congr 1
  · funext r
    simp only [Registers.write]
    split <;> split <;> (try split) <;> simp_all <;> omega
  · omega

theorem hosted_cons_tail {program : Program} {base : Nat} {i : Instruction}
    {code : Program} (host : HostedAt program base (i :: code)) :
    HostedAt program (base + 1) code := by
  intro j hj
  have h := host (j + 1) (by simp; omega)
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Each zeroing assignment is one actual primitive, with its actual prestate. -/
theorem clearCode_exec (memory : Memory) (program : Program) (s : State)
    (first count : Nat) (hs : s.status = .running)
    (host : HostedAt program s.pc (clearCode first count)) :
    ∃ ts, RunsTo memory program s (cleared s first count) ts ∧
      ts.length = count ∧ ts.filterMap (·.receipt) = [] := by
  induction count generalizing first s with
  | zero =>
      refine ⟨[], ?_, rfl, rfl⟩
      rw [cleared_zero s first hs]
      exact RunsTo.refl memory program s
  | succ count ih =>
      let t : Transition := ⟨s, .constant first 0, s.writeNext first 0, none⟩
      have hstep : RunsTo memory program s (s.writeNext first 0) [t] :=
        RunsTo.instruction hs host.head
      obtain ⟨ts, hexec, hlen, hreads⟩ := ih (s.writeNext first 0) (first + 1) rfl
        (hosted_cons_tail host)
      refine ⟨[t] ++ ts, ?_, by simp [hlen], by simp [t, hreads]⟩
      rw [← cleared_succ]
      exact hstep.trans hexec

def clearCount : Nat := compactQueryRegisterCount - 3
def setupCode : Program := clearCode 3 clearCount ++ [.jump 0]
def setupCost : Nat := clearCount + 1

theorem clearCount_eq : clearCount = 8270 := by
  rw [clearCount, compactQueryRegisterCount_eq]

theorem setupCost_eq : setupCost = 8271 := by rw [setupCost, clearCount_eq]

theorem setupCode_length : setupCode.length = setupCost := by
  simp [setupCode, clearCode_length, setupCost]

/-- The caller derives these values and finite support from its actual handoff.
There is no assumed entry PC: hosting below is at the caller's actual PC. -/
def SetupInputs (n left right : Nat) (s : State) : Prop :=
  s.status = .running ∧ s.regs 0 = left ∧ s.regs 1 = right ∧ s.regs 2 = n ∧
    (∀ r, compactQueryRegisterCount ≤ r → s.regs r = 0)

theorem cleared_setup_regs (n left right : Nat) (s : State)
    (inputs : SetupInputs n left right s) :
    (cleared s 3 clearCount).regs = (initialState n left right).regs := by
  funext r
  obtain ⟨_, h0, h1, h2, outside⟩ := inputs
  simp only [cleared, initialState, inputRegisters, Registers.write]
  rw [clearCount_eq]
  split
  · split <;> (try split) <;> (try split) <;> omega
  · by_cases r0 : r = 0
    · subst r; simp_all
    by_cases r1 : r = 1
    · subst r; simp_all
    by_cases r2 : r = 2
    · subst r; simp_all
    simp only [if_neg r0, if_neg r1, if_neg r2]
    apply outside
    rw [compactQueryRegisterCount_eq]
    omega

theorem clearJump_exec (memory : Memory) (program : Program) (s : State)
    (first count : Nat) (hs : s.status = .running)
    (host : HostedAt program s.pc (clearCode first count ++ [.jump 0])) :
    ∃ ts, run memory program (count + 1) s = ⟨{ cleared s first count with pc := 0 }, ts⟩ ∧
      ts.length = count + 1 ∧ ts.filterMap (·.receipt) = [] := by
  obtain ⟨ts, hx, hlen, hreads⟩ := clearCode_exec memory program s first count hs host.append_left
  let c := cleared s first count
  have hfetch : program[c.pc]? = some (.jump 0) := by
    have h := host.append_right.head
    simpa [c, cleared, clearCode_length] using h
  let j : Transition := ⟨c, .jump 0, { c with pc := 0 }, none⟩
  have hj : RunsTo memory program c { c with pc := 0 } [j] :=
    RunsTo.instruction rfl hfetch
  have both := hx.trans hj
  refine ⟨ts ++ [j], ?_, by simp [hlen], by simp [j, hreads]⟩
  have len : (ts ++ [j]).length = count + 1 := by simp [hlen]
  simpa only [RunsTo, len] using both

/-- Exact complete ABI state follows from scalar clears and one real jump. -/
theorem setup_exec (memory : Memory) (program : Program) (n left right : Nat) (s : State)
    (inputs : SetupInputs n left right s) (host : HostedAt program s.pc setupCode) :
    ∃ ts, run memory program setupCost s = ⟨initialState n left right, ts⟩ ∧
      ts.length = setupCost ∧ ts.filterMap (·.receipt) = [] := by
  have hfinal : { cleared s 3 clearCount with pc := 0 } = initialState n left right := by
    have hregs := cleared_setup_regs n left right s inputs
    change State.mk (cleared s 3 clearCount).regs 0 .running = initialState n left right
    rw [hregs]
    rfl
  simpa only [hfinal, setupCost] using
    clearJump_exec memory program s 3 clearCount inputs.1 host

/-- The setup is hosted anywhere in the suffix; the fixed compact code stays at zero. -/
theorem chargedEntry_compactQuery (memory : Memory) (suffix : Program)
    (n left right : Nat) (s : State) (inputs : SetupInputs n left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode) :
    ∃ setupTransitions,
      run memory (compactQueryProgram ++ suffix) setupCost s =
        ⟨initialState n left right, setupTransitions⟩ ∧
      setupTransitions.length = setupCost ∧ setupTransitions.filterMap (·.receipt) = [] ∧
      run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s =
        ⟨(compactQueryRun memory n left right).final,
          setupTransitions ++ (compactQueryRun memory n left right).transitions⟩ := by
  obtain ⟨ts, hs, hc, hr⟩ := setup_exec memory (compactQueryProgram ++ suffix) n left right s inputs host
  refine ⟨ts, hs, hc, hr, ?_⟩
  rw [run_add, hs]
  dsimp only
  rw [compactQuery_prefix]

theorem chargedEntry_observations (memory : Memory) (suffix : Program)
    (n left right : Nat) (s : State) (inputs : SetupInputs n left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode) :
    let actual := run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s
    let core := compactQueryRun memory n left right
    actual.final = core.final ∧ actual.result = core.result ∧ actual.reads = core.reads ∧
      actual.steps = setupCost + core.steps := by
  obtain ⟨ts, _, hc, hr, he⟩ := chargedEntry_compactQuery memory suffix n left right s inputs host
  dsimp only
  rw [he]
  simp [Run.result, Run.reads, Run.steps, hc, hr]

theorem chargedEntry_bound (memory : Memory) (suffix : Program)
    (n left right : Nat) (s : State) (inputs : SetupInputs n left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode) :
    (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).steps ≤ 160249 ∧
    (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).final.status ≠ .running := by
  have obs := chargedEntry_observations memory suffix n left right s inputs host
  have bound := compactQueryRun_steps_le memory n left right
  dsimp only at obs
  constructor
  · rw [obs.2.2.2, setupCost_eq]
    rw [compactQueryBudget_eq] at bound
    omega
  · rw [obs.1]
    exact compactQueryRun_stopped memory n left right

theorem chargedEntry_canonical (xs : List Int) (suffix : Program) (left right : Nat) (s : State)
    (inputs : SetupInputs xs.length left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode) :
    (run (buildMemory xs) (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) := by
  rw [(chargedEntry_observations (buildMemory xs) suffix xs.length left right s inputs host).1]
  exact compactQueryRun_halts xs left right

theorem chargedEntry_invalid (memory : Memory) (suffix : Program) (n left right : Nat) (s : State)
    (inputs : SetupInputs n left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode)
    (invalid : ¬ (left < right ∧ right ≤ n)) :
    (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).result = some 0 ∧
    (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).reads = [] := by
  have obs := chargedEntry_observations memory suffix n left right s inputs host
  have h := compactQueryRun_invalid memory n left right invalid
  exact ⟨obs.2.1.trans h.1, obs.2.2.1.trans h.2⟩

/-- Every query occurrence remains at its precise shifted position in the host. -/
theorem chargedEntry_read_occurrence (memory : Memory) (suffix : Program)
    (n left right : Nat) (s : State) (inputs : SetupInputs n left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode)
    (k : Nat) (t : Transition) (receipt : Receipt)
    (coreOccurrence : (compactQueryRun memory n left right).transitions[k]? = some t)
    (read : t.receipt = some receipt) :
    (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).transitions[setupCost + k]? = some t ∧
    t.before = (run memory (compactQueryProgram ++ suffix) (setupCost + k) s).final ∧
    t.before.status = .running ∧ (compactQueryProgram ++ suffix)[t.before.pc]? = some t.instruction ∧
    execute memory t.instruction t.before = (t.after, t.receipt) ∧
    ∃ dst addrReg, t.instruction = .load dst addrReg ∧
      receipt.address = t.before.regs addrReg ∧ receipt.reply = memory[receipt.address]? := by
  obtain ⟨ts, _, hlen, _, hrun⟩ := chargedEntry_compactQuery memory suffix n left right s inputs host
  have occurrence : (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).transitions[setupCost + k]? = some t := by
    rw [hrun]
    simp only
    rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]
    exact coreOccurrence
  exact ⟨occurrence, run_read_at occurrence read⟩

/-- The general finite-bank frame needed by a subsequent charged admission. -/
theorem chargedEntry_zero_tail (memory : Memory) (suffix : Program)
    (n left right : Nat) (s : State) (inputs : SetupInputs n left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode)
    (r : Nat) (outside : compactQueryRegisterCount ≤ r) :
    (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).final.regs r = 0 := by
  rw [(chargedEntry_observations memory suffix n left right s inputs host).1]
  exact compactQuery_finite_registers memory n left right compactQueryBudget r outside

theorem clearCode_fields (width first count : Nat) (tag : 1 < 2 ^ width)
    (bound : first + count ≤ 2 ^ width) :
    ∀ i ∈ clearCode first count, i.Fits width := by
  induction count generalizing first with
  | zero => simp [clearCode]
  | succ count ih =>
      intro i hi
      simp only [clearCode, List.mem_cons] at hi
      rcases hi with rfl | hi
      · intro operand mem
        simp only [Instruction.encoding, Instruction.operands, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl <;> omega
      · exact ih (first + 1) (by omega) i hi

theorem clearCode_encoding (first count : Nat) :
    ((clearCode first count).map Instruction.encoding).flatten.length = 3 * count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      simp [clearCode, Instruction.encoding, Instruction.operands, ih]
      omega

theorem setupCode_encoding : (setupCode.map Instruction.encoding).flatten.length = 24812 := by
  simp only [setupCode, List.map_append, List.flatten_append, List.length_append,
    clearCode_encoding, clearCount_eq]
  rfl

theorem clearCode_safe (memory : Memory) (program : Program) (s : State)
    (width first count : Nat) (hs : s.status = .running)
    (host : HostedAt program s.pc (clearCode first count))
    (fit : s.Fits width) (tag : 1 < 2 ^ width)
    (fields : first + count ≤ 2 ^ width) (pc : s.pc + count < 2 ^ width) :
    TraceSafe width (run memory program count s).transitions := by
  induction count generalizing first s with
  | zero => intro t ht; simp [run] at ht
  | succ count ih =>
      have hf : program[s.pc]? = some (.constant first 0) := host.head
      let t : Transition := ⟨s, .constant first 0, s.writeNext first 0, none⟩
      have stepEq : step memory program s = some t := by simp [step, hs, hf, execute, t]
      have ifit : (Instruction.constant first 0).Fits width := by
        intro operand mem
        simp only [Instruction.encoding, Instruction.operands, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at mem
        rcases mem with rfl | rfl | rfl <;> omega
      have safe := Action.execute_safe memory width (.constant first 0) s fit ifit
        (by change 0 < 2 ^ width; omega) (by omega)
      have tail := ih (s.writeNext first 0) (first + 1) rfl (hosted_cons_tail host)
        safe.2 (by omega) (by change s.pc + 1 + count < 2 ^ width; omega)
      intro u hu
      simp only [run, stepEq, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact safe
      · exact tail u hu

theorem clearJump_safe (memory : Memory) (program : Program) (s : State)
    (width first count : Nat) (hs : s.status = .running)
    (host : HostedAt program s.pc (clearCode first count ++ [.jump 0]))
    (fit : s.Fits width) (tag : 5 < 2 ^ width)
    (fields : first + count ≤ 2 ^ width) (pc : s.pc + count < 2 ^ width) :
    TraceSafe width (run memory program (count + 1) s).transitions := by
  obtain ⟨ts, hx, hlen, _⟩ := clearCode_exec memory program s first count hs host.append_left
  have execClear : run memory program count s = ⟨cleared s first count, ts⟩ := by
    simpa only [RunsTo, hlen] using hx
  have safeClear := clearCode_safe memory program s width first count hs host.append_left
    fit (by omega) fields pc
  have cfit := run_prefix_fits memory program width count s fit safeClear count (Nat.le_refl _)
  rw [execClear] at safeClear cfit
  let c := cleared s first count
  have hf : program[c.pc]? = some (.jump 0) := by
    simpa [c, cleared, clearCode_length] using host.append_right.head
  let j : Transition := ⟨c, .jump 0, { c with pc := 0 }, none⟩
  have js : step memory program c = some j := by
    have cs : c.status = .running := rfl
    simp only [step, cs, hf, execute]
    rfl
  have jumpFit : (Instruction.jump 0).Fits width := by
    simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
    omega
  have safeJump : TraceSafe width [j] := by
    intro t ht
    have he := List.mem_singleton.mp ht
    subst t
    exact ⟨⟨jumpFit, cfit, trivial⟩,
      show ({ c with pc := 0 } : State).Fits width from ⟨by change 0 < 2 ^ width; omega, cfit.2⟩⟩
  rw [run_add, execClear]
  change TraceSafe width (ts ++ (run memory program 1 c).transitions)
  simpa only [run, js] using compact_traceSafe_append safeClear safeJump

theorem setupCode_fields (n : Nat) : ∀ i ∈ setupCode, i.Fits (wordWidth n) := by
  have cap := query_small_fields_fit n
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact clearCode_fields (wordWidth n) 3 clearCount (by omega)
      (by rw [clearCount_eq]; omega) i hi
  · have he : i = .jump 0 := List.mem_singleton.mp hi
    rw [he]
    simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
    omega

theorem setup_trace_safe (memory : Memory) (program : Program) (n left right : Nat) (s : State)
    (inputs : SetupInputs n left right s) (host : HostedAt program s.pc setupCode)
    (fit : s.Fits (wordWidth n)) (pcBound : s.pc + clearCount < 2 ^ wordWidth n) :
    TraceSafe (wordWidth n) (run memory program setupCost s).transitions := by
  apply clearJump_safe memory program s (wordWidth n) 3 clearCount inputs.1 host fit
  · have cap := query_small_fields_fit n; omega
  · rw [clearCount_eq]; have cap := query_small_fields_fit n; omega
  · exact pcBound

/-- Whole-program field fit is explicit: dormant host instructions are not omitted. -/
theorem chargedEntry_execution_safe (xs : List Int) (suffix : Program)
    (left right : Nat) (s : State) (inputs : SetupInputs xs.length left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode)
    (fit : s.Fits (wordWidth xs.length))
    (pcBound : s.pc + clearCount < 2 ^ wordWidth xs.length)
    (fields : ∀ i ∈ compactQueryProgram ++ suffix, i.Fits (wordWidth xs.length))
    (hl : left < 2 ^ wordWidth xs.length) (hr : right < 2 ^ wordWidth xs.length) :
    RankExecutionSafety (buildMemory xs) (wordWidth xs.length)
      (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s := by
  obtain ⟨ts, hsetup, _, _, hrun⟩ :=
    chargedEntry_compactQuery (buildMemory xs) suffix xs.length left right s inputs host
  have sq := compactQueryRun_execution_safe xs left right hl hr
  have ss := setup_trace_safe (buildMemory xs) (compactQueryProgram ++ suffix)
    xs.length left right s inputs host fit pcBound
  rw [hsetup] at ss
  have queryTrace : TraceSafe (wordWidth xs.length)
      (compactQueryRun (buildMemory xs) xs.length left right).transitions := by
    intro t ht
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht
    exact sq.2.2.1 i t hi
  have allTrace : TraceSafe (wordWidth xs.length)
      (run (buildMemory xs) (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).transitions := by
    rw [hrun]
    exact compact_traceSafe_append ss queryTrace
  refine ⟨fields, ?_, ?_, ?_, ?_⟩
  · rw [hrun]; exact sq.2.1
  · intro i t hi; exact allTrace t (List.mem_of_getElem? hi)
  · exact run_prefix_fits (buildMemory xs) (compactQueryProgram ++ suffix)
      (wordWidth xs.length) (setupCost + compactQueryBudget) s fit allTrace
  · intro i t receipt hi hr
    have st := allTrace t (List.mem_of_getElem? hi)
    exact run_read_fits hi hr st.1 st.2

theorem clearCode_categories (memory : Memory) (program : Program) (s : State)
    (first count : Nat) (hs : s.status = .running)
    (host : HostedAt program s.pc (clearCode first count)) :
    (run memory program count s).categories = List.replicate count .registerWrite := by
  induction count generalizing first s with
  | zero => rfl
  | succ count ih =>
      have hf : program[s.pc]? = some (.constant first 0) := host.head
      have he : step memory program s =
          some ⟨s, .constant first 0, s.writeNext first 0, none⟩ := by
        simp [step, hs, hf, execute]
      have tail := ih (s.writeNext first 0) (first + 1) rfl (hosted_cons_tail host)
      simp only [run, he, Run.categories, List.map_cons, Instruction.category]
      change Category.registerWrite :: (run memory program count (s.writeNext first 0)).categories = _
      rw [tail, List.replicate_succ]

/-- Category accounting distinguishes the zero writes from the jump. -/
theorem setup_categories (memory : Memory) (program : Program) (s : State)
    (hs : s.status = .running) (host : HostedAt program s.pc setupCode) :
    (run memory program setupCost s).categories =
      List.replicate clearCount .registerWrite ++ [.branch] := by
  obtain ⟨ts, hx, hlen, _⟩ := clearCode_exec memory program s 3 clearCount hs host.append_left
  have he : run memory program clearCount s = ⟨cleared s 3 clearCount, ts⟩ := by
    simpa only [RunsTo, hlen] using hx
  have cats := clearCode_categories memory program s 3 clearCount hs host.append_left
  rw [he] at cats
  have hf : program[(cleared s 3 clearCount).pc]? = some (.jump 0) := by
    simpa [cleared, clearCode_length] using host.append_right.head
  have hj : step memory program (cleared s 3 clearCount) =
      some ⟨cleared s 3 clearCount, .jump 0, { cleared s 3 clearCount with pc := 0 }, none⟩ := by
    have hc : (cleared s 3 clearCount).status = .running := rfl
    simp only [step, hc, hf, execute]
  rw [setupCost, run_add, he]
  simpa [run, hj, Run.categories, Instruction.category] using
    congrArg (fun tail => tail ++ [Category.branch]) cats

theorem chargedEntry_categories (memory : Memory) (suffix : Program)
    (n left right : Nat) (s : State) (inputs : SetupInputs n left right s)
    (host : HostedAt (compactQueryProgram ++ suffix) s.pc setupCode) :
    (run memory (compactQueryProgram ++ suffix) (setupCost + compactQueryBudget) s).categories =
      List.replicate clearCount .registerWrite ++ [.branch] ++
        (compactQueryRun memory n left right).categories := by
  obtain ⟨ts, hs, _, _, hrun⟩ := chargedEntry_compactQuery memory suffix n left right s inputs host
  have cats := setup_categories memory (compactQueryProgram ++ suffix) s inputs.1 host
  rw [hs] at cats
  rw [hrun]
  simp only [Run.categories, List.map_append] at cats ⊢
  rw [cats]

end RMQ.SuccinctFinal.PackedLifecycle.QueryEntry
