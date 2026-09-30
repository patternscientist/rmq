import RMQ.Core.WordRAM.Native.Lifecycle.Run

/-! # Separately owned lifecycle diagnostics

The observation accumulator contains fifteen category counters, thirteen route
counters, a step count, and ordered numeric read/reply pairs. It contains no owner, transition,
input, or state-valued closure. The executable evaluator records prestate scalars
before calling the unchanged `executeArray`, and is unconditionally equal to the
`stepArray` evaluator. Histories appear only in the statements and proofs of its
fold theorem. These are model observations, not native allocator measurements.
-/

namespace RMQ.SuccinctFinal.PackedNative.Lifecycle

open PackedLifecycle

namespace Observations

/-- One scalar for each constructor of the existing finite category universe. -/
structure Counts where
  read : Nat := 0
  register : Nat := 0
  arithmetic : Nat := 0
  comparison : Nat := 0
  branch : Nat := 0
  control : Nat := 0
  write : Nat := 0
  allocation : Nat := 0
  keyRead : Nat := 0
  oracleComparison : Nat := 0
  numericRelease : Nat := 0
  keyRelease : Nat := 0
  keyRegisterRelease : Nat := 0
  requestAdmission : Nat := 0
  controlEntry : Nat := 0
deriving Repr, DecidableEq

def Counts.get (n : Counts) : Category → Nat
  | .old .read => n.read
  | .old .register => n.register
  | .old .arithmetic => n.arithmetic
  | .old .comparison => n.comparison
  | .old .branch => n.branch
  | .old .control => n.control
  | .old .write => n.write
  | .old .allocation => n.allocation
  | .old .keyRead => n.keyRead
  | .old .oracleComparison => n.oracleComparison
  | .numericRelease => n.numericRelease
  | .keyRelease => n.keyRelease
  | .keyRegisterRelease => n.keyRegisterRelease
  | .requestAdmission => n.requestAdmission
  | .controlEntry => n.controlEntry

def Counts.bump (n : Counts) : Category → Counts
  | .old .read => { n with read := n.read + 1 }
  | .old .register => { n with register := n.register + 1 }
  | .old .arithmetic => { n with arithmetic := n.arithmetic + 1 }
  | .old .comparison => { n with comparison := n.comparison + 1 }
  | .old .branch => { n with branch := n.branch + 1 }
  | .old .control => { n with control := n.control + 1 }
  | .old .write => { n with write := n.write + 1 }
  | .old .allocation => { n with allocation := n.allocation + 1 }
  | .old .keyRead => { n with keyRead := n.keyRead + 1 }
  | .old .oracleComparison => { n with oracleComparison := n.oracleComparison + 1 }
  | .numericRelease => { n with numericRelease := n.numericRelease + 1 }
  | .keyRelease => { n with keyRelease := n.keyRelease + 1 }
  | .keyRegisterRelease => { n with keyRegisterRelease := n.keyRegisterRelease + 1 }
  | .requestAdmission => { n with requestAdmission := n.requestAdmission + 1 }
  | .controlEntry => { n with controlEntry := n.controlEntry + 1 }

theorem Counts.get_bump (n : Counts) (a c : Category) :
    (n.bump a).get c = n.get c + if a = c then 1 else 0 := by
  cases a <;> cases c
  all_goals first
    | rename_i a c; cases a <;> cases c <;> simp [Counts.bump, Counts.get]
    | rename_i a; cases a <;> simp [Counts.bump, Counts.get]
    | simp [Counts.bump, Counts.get]

theorem Counts.get_zero (c : Category) : ({} : Counts).get c = 0 := by
  cases c
  · rename_i c; cases c <;> rfl
  all_goals rfl

/-- Phase visits and source-discriminator occurrences. A decision counter says
the corresponding comparison was executed on its recorded input values. The
separate interior-reader and crossing-load counters record actual instructions,
not a predicted route. Native labels must also check the fixed program's
signature inventory and successful completion. -/
inductive RouteMark where
  | compactQuery | servicePrepare | serviceSetup | builder | descriptor | finalizer | retirement
  | sameBlockDecision | crossBlockDecision | interiorNonemptyDecision | interiorEmptyDecision
  | interiorReadMarker | crossingSecondLoad
deriving Repr, DecidableEq

def signature : RouteMark → Instruction → Bool
  | .sameBlockDecision, i | .crossBlockDecision, i =>
      i == .old (.comparison .eq 1215 1203 1204)
  | .interiorNonemptyDecision, i | .interiorEmptyDecision, i =>
      i == .old (.comparison .lt 1215 896 1204)
  | .interiorReadMarker, i => i == .old (.constant 8192 20)
  | .crossingSecondLoad, i => i == .old (.load 8266 8261)
  | _, _ => false

/-- Numeric ranges are the fixed `Layout`/`Service` boundaries. The retirement
range is comparison-specific; the word program's final service jump at 223370
is explicitly excluded. -/
def routeMarked (mark : RouteMark) (t : ArrayTransition) : Bool :=
  match t.action with
  | .boundary _ => false
  | .instruction i =>
      let pc := t.before.pc
      match mark with
      | .compactQuery => decide (pc < 212964)
      | .servicePrepare => decide (212964 ≤ pc ∧ pc < 212968)
      | .serviceSetup => decide (212968 ≤ pc ∧ pc < 221239)
      | .builder => decide (221239 ≤ pc ∧ pc < 223345)
      | .descriptor => decide (223345 ≤ pc ∧ pc < 223356)
      | .finalizer => decide (223356 ≤ pc ∧ pc < 223370)
      | .retirement => decide (223370 ≤ pc ∧ pc < 223378) &&
          !(i == .old (.jump Layout.serviceEntry))
      | .sameBlockDecision => decide (pc < 212964) && signature mark i &&
          (t.before.regs.getD 1203 0 == t.before.regs.getD 1204 0)
      | .crossBlockDecision => decide (pc < 212964) && signature mark i &&
          !(t.before.regs.getD 1203 0 == t.before.regs.getD 1204 0)
      | .interiorNonemptyDecision => decide (pc < 212964) && signature mark i &&
          decide (t.before.regs.getD 896 0 < t.before.regs.getD 1204 0)
      | .interiorEmptyDecision => decide (pc < 212964) && signature mark i &&
          !decide (t.before.regs.getD 896 0 < t.before.regs.getD 1204 0)
      | .interiorReadMarker | .crossingSecondLoad =>
          decide (pc < 212964) && signature mark i

theorem sameBlockDecision_iff (t : ArrayTransition) :
    routeMarked .sameBlockDecision t = true ↔
      t.before.pc < 212964 ∧
      t.action = .instruction (.old (.comparison .eq 1215 1203 1204)) ∧
      t.before.regs.getD 1203 0 = t.before.regs.getD 1204 0 := by
  cases h : t.action <;> simp [routeMarked, signature, h, and_assoc]

theorem crossBlockDecision_iff (t : ArrayTransition) :
    routeMarked .crossBlockDecision t = true ↔
      t.before.pc < 212964 ∧
      t.action = .instruction (.old (.comparison .eq 1215 1203 1204)) ∧
      t.before.regs.getD 1203 0 ≠ t.before.regs.getD 1204 0 := by
  cases h : t.action <;> simp [routeMarked, signature, h, and_assoc]

theorem interiorNonemptyDecision_iff (t : ArrayTransition) :
    routeMarked .interiorNonemptyDecision t = true ↔
      t.before.pc < 212964 ∧
      t.action = .instruction (.old (.comparison .lt 1215 896 1204)) ∧
      t.before.regs.getD 896 0 < t.before.regs.getD 1204 0 := by
  cases h : t.action <;> simp [routeMarked, signature, h, and_assoc]

theorem interiorEmptyDecision_iff (t : ArrayTransition) :
    routeMarked .interiorEmptyDecision t = true ↔
      t.before.pc < 212964 ∧
      t.action = .instruction (.old (.comparison .lt 1215 896 1204)) ∧
      ¬ t.before.regs.getD 896 0 < t.before.regs.getD 1204 0 := by
  cases h : t.action <;> simp [routeMarked, signature, h, and_assoc]

theorem interiorReadMarker_iff (t : ArrayTransition) :
    routeMarked .interiorReadMarker t = true ↔
      t.before.pc < 212964 ∧ t.action = .instruction (.old (.constant 8192 20)) := by
  cases h : t.action <;> simp [routeMarked, signature, h]

theorem crossingSecondLoad_iff (t : ArrayTransition) :
    routeMarked .crossingSecondLoad t = true ↔
      t.before.pc < 212964 ∧ t.action = .instruction (.old (.load 8266 8261)) := by
  cases h : t.action <;> simp [routeMarked, signature, h]

/-- This checks the actual fixed code before any native client interprets a
decision signature. Phases are PC ranges and deliberately have no signature. -/
def programSignatureCount (model : InputModel) (mark : RouteMark) : Nat :=
  ((cachedProgram model).toList.take 212964).countP (signature mark)

theorem programSignatureCount_source (model : InputModel) (mark : RouteMark) :
    programSignatureCount model mark =
      ((Layout.program model).take 212964).countP (signature mark) := by
  simp [programSignatureCount, cachedProgram_eq]

structure RouteCounts where
  compactQuery : Nat := 0
  servicePrepare : Nat := 0
  serviceSetup : Nat := 0
  builder : Nat := 0
  descriptor : Nat := 0
  finalizer : Nat := 0
  retirement : Nat := 0
  sameBlockDecision : Nat := 0
  crossBlockDecision : Nat := 0
  interiorNonemptyDecision : Nat := 0
  interiorEmptyDecision : Nat := 0
  interiorReadMarker : Nat := 0
  crossingSecondLoad : Nat := 0
deriving Repr, DecidableEq

def RouteCounts.get (r : RouteCounts) : RouteMark → Nat
  | .compactQuery => r.compactQuery
  | .servicePrepare => r.servicePrepare
  | .serviceSetup => r.serviceSetup
  | .builder => r.builder
  | .descriptor => r.descriptor
  | .finalizer => r.finalizer
  | .retirement => r.retirement
  | .sameBlockDecision => r.sameBlockDecision
  | .crossBlockDecision => r.crossBlockDecision
  | .interiorNonemptyDecision => r.interiorNonemptyDecision
  | .interiorEmptyDecision => r.interiorEmptyDecision
  | .interiorReadMarker => r.interiorReadMarker
  | .crossingSecondLoad => r.crossingSecondLoad

def RouteCounts.record (r : RouteCounts) (t : ArrayTransition) : RouteCounts :=
  { compactQuery := r.compactQuery + if routeMarked .compactQuery t then 1 else 0
    servicePrepare := r.servicePrepare + if routeMarked .servicePrepare t then 1 else 0
    serviceSetup := r.serviceSetup + if routeMarked .serviceSetup t then 1 else 0
    builder := r.builder + if routeMarked .builder t then 1 else 0
    descriptor := r.descriptor + if routeMarked .descriptor t then 1 else 0
    finalizer := r.finalizer + if routeMarked .finalizer t then 1 else 0
    retirement := r.retirement + if routeMarked .retirement t then 1 else 0
    sameBlockDecision := r.sameBlockDecision + if routeMarked .sameBlockDecision t then 1 else 0
    crossBlockDecision := r.crossBlockDecision + if routeMarked .crossBlockDecision t then 1 else 0
    interiorNonemptyDecision := r.interiorNonemptyDecision + if routeMarked .interiorNonemptyDecision t then 1 else 0
    interiorEmptyDecision := r.interiorEmptyDecision + if routeMarked .interiorEmptyDecision t then 1 else 0
    interiorReadMarker := r.interiorReadMarker + if routeMarked .interiorReadMarker t then 1 else 0
    crossingSecondLoad := r.crossingSecondLoad + if routeMarked .crossingSecondLoad t then 1 else 0 }

theorem RouteCounts.get_record (r : RouteCounts) (t : ArrayTransition) (mark : RouteMark) :
    (r.record t).get mark = r.get mark + if routeMarked mark t then 1 else 0 := by
  cases mark <;> rfl

theorem RouteCounts.get_zero (mark : RouteMark) : ({} : RouteCounts).get mark = 0 := by
  cases mark <;> rfl

structure Stats where
  steps : Nat := 0
  counts : Counts := {}
  readsRev : List (Nat × Option Nat) := []
  routes : RouteCounts := {}
deriving Repr, DecidableEq

def Stats.reads (s : Stats) : List (Nat × Option Nat) := s.readsRev.reverse

def Stats.record (s : Stats) (t : ArrayTransition) : Stats :=
  { steps := s.steps + 1
    counts := s.counts.bump t.action.category
    readsRev := match t.read? with | none => s.readsRev | some r => r :: s.readsRev
    routes := s.routes.record t }

/-- Finish every scalar observation before executing the instruction. The
temporary transition is local to this non-inlined call; neither owner field
can escape in the returned `Stats`. Its after field is never inspected. -/
@[noinline] def Stats.recordBefore (s : Stats) (action : Action) (before : Owner) : Stats :=
  s.record ⟨before, action, before⟩

theorem Stats.record_eq_recordBefore (s : Stats) (t : ArrayTransition) :
    s.record t = s.recordBefore t.action t.before := by
  cases t
  rfl

def Stats.fold (s : Stats) (ts : List ArrayTransition) : Stats :=
  ts.foldl Stats.record s

theorem Stats.fold_append (s : Stats) (a b : List ArrayTransition) :
    s.fold (a ++ b) = (s.fold a).fold b := by
  simp [Stats.fold, List.foldl_append]

theorem Stats.fold_steps (s : Stats) (ts : List ArrayTransition) :
    (s.fold ts).steps = s.steps + ts.length := by
  induction ts generalizing s with
  | nil => simp [Stats.fold]
  | cons t ts ih =>
      change ((s.record t).fold ts).steps = _
      rw [ih]
      simp [Stats.record, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Stats.fold_count (s : Stats) (ts : List ArrayTransition) (c : Category) :
    (s.fold ts).counts.get c = s.counts.get c + (ts.map (·.action.category)).count c := by
  induction ts generalizing s with
  | nil => simp [Stats.fold]
  | cons t ts ih =>
      change ((s.record t).fold ts).counts.get c = _
      rw [ih]
      simp only [Stats.record, Counts.get_bump, List.map_cons, List.count_cons]
      by_cases h : t.action.category = c
      · simp [h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [h, Ne.symm h]

theorem Stats.fold_readsRev (s : Stats) (ts : List ArrayTransition) :
    (s.fold ts).readsRev = (ts.filterMap ArrayTransition.read?).reverse ++ s.readsRev := by
  induction ts generalizing s with
  | nil => simp [Stats.fold]
  | cons t ts ih =>
      change ((s.record t).fold ts).readsRev = _
      rw [ih]
      cases h : t.read? <;> simp [Stats.record, h, List.reverse_cons, List.append_assoc]

theorem Stats.fold_reads (s : Stats) (ts : List ArrayTransition) :
    (s.fold ts).reads = s.reads ++ ts.filterMap ArrayTransition.read? := by
  simp [Stats.reads, Stats.fold_readsRev, List.reverse_append]

theorem Stats.empty_fold_reads (ts : List ArrayTransition) :
    (({} : Stats).fold ts).reads = ts.filterMap ArrayTransition.read? :=
  (Stats.fold_reads {} ts).trans (by rfl)

theorem Stats.fold_route (s : Stats) (ts : List ArrayTransition) (mark : RouteMark) :
    (s.fold ts).routes.get mark = s.routes.get mark + ts.countP (routeMarked mark) := by
  induction ts generalizing s with
  | nil => simp [Stats.fold]
  | cons t ts ih =>
      change ((s.record t).fold ts).routes.get mark = _
      rw [ih]
      simp [Stats.record, RouteCounts.get_record, List.countP_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Tail recursion retains scalar diagnostics, never a transition history. -/
def runAcc (program : Array Instruction) : Nat → Owner → Stats → Owner × Stats
  | 0, owner, stats => (owner, stats)
  | fuel + 1, owner, stats =>
      match stepArray program owner with
      | none => (owner, stats)
      | some t => runAcc program fuel t.after (stats.record t)

theorem runAcc_exact (program : Array Instruction) (fuel : Nat) (owner : Owner) (stats : Stats) :
    runAcc program fuel owner stats =
      (runOwner program fuel owner, stats.fold (runArray program fuel owner).transitions) := by
  induction fuel generalizing owner stats with
  | zero => rfl
  | succ fuel ih =>
      cases h : stepArray program owner with
      | none => simp [runAcc, runOwner, runArray, h, Stats.fold]
      | some t => simpa [runAcc, runOwner, runArray, h, Stats.fold] using ih t.after (stats.record t)

/-- The reference transition's prestate is consumed by scalar observation
before the same primitive mutates the owner. No transition crosses that call. -/
def runAccThin (program : Array Instruction) : Nat → Owner → Stats → Owner × Stats
  | 0, owner, stats => (owner, stats)
  | fuel + 1, owner, stats =>
      if owner.status = .running then
        match program[owner.pc]? with
        | none => (owner, stats)
        | some i =>
            let nextStats := stats.recordBefore (.instruction i) owner
            let nextOwner := executeArray i owner
            runAccThin program fuel nextOwner nextStats
      else (owner, stats)

/-- Exact accumulator equality for all programs, fuels, owners, and initial
diagnostics, including stopped owners, missing fetches, and failed operations. -/
theorem runAccThin_eq_runAcc (program : Array Instruction) (fuel : Nat)
    (owner : Owner) (stats : Stats) :
    runAccThin program fuel owner stats = runAcc program fuel owner stats := by
  induction fuel generalizing owner stats with
  | zero => rfl
  | succ fuel ih =>
      by_cases hs : owner.status = .running
      · cases hf : program[owner.pc]? with
        | none => simp [runAccThin, runAcc, stepArray, hs, hf]
        | some i =>
            simp [runAccThin, runAcc, stepArray, hs, hf, ih, Stats.record_eq_recordBefore]
      · simp [runAccThin, runAcc, stepArray, hs]

def run (program : Array Instruction) (fuel : Nat) (owner : Owner) : Owner × Stats :=
  runAccThin program fuel owner {}

theorem run_owner (program : Array Instruction) (fuel : Nat) (owner : Owner) :
    (run program fuel owner).1 = runOwner program fuel owner := by
  simp [run, runAccThin_eq_runAcc, runAcc_exact]

theorem run_steps (program : Array Instruction) (fuel : Nat) (owner : Owner) :
    (run program fuel owner).2.steps = (runArray program fuel owner).steps := by
  simp [run, runAccThin_eq_runAcc, runAcc_exact, Stats.fold_steps, ArrayRun.steps]

theorem run_count (program : Array Instruction) (fuel : Nat) (owner : Owner) (c : Category) :
    (run program fuel owner).2.counts.get c = (runArray program fuel owner).categoryCount c := by
  simp [run, runAccThin_eq_runAcc, runAcc_exact, Stats.fold_count, Counts.get_zero,
    ArrayRun.categoryCount, ArrayRun.categories]

theorem run_reads (program : Array Instruction) (fuel : Nat) (owner : Owner) :
    (run program fuel owner).2.reads = (runArray program fuel owner).reads := by
  rw [run, runAccThin_eq_runAcc, runAcc_exact, Stats.fold_reads]
  rfl

theorem run_route (program : Array Instruction) (fuel : Nat) (owner : Owner) (mark : RouteMark) :
    (run program fuel owner).2.routes.get mark =
      (runArray program fuel owner).transitions.countP (routeMarked mark) := by
  simp [run, runAccThin_eq_runAcc, runAcc_exact, Stats.fold_route, RouteCounts.get_zero]

/-- Indexed source occurrences preserve multiplicity and their actual prestates.
Together with `run_reads`, this identifies every stored pair's producing run;
equal pairs at distinct positions remain distinct occurrences. -/
theorem source_occurrence {program : Array Instruction} {fuel : Nat} {owner : Owner}
    {index : Nat} {t : ArrayTransition}
    (h : (runArray program fuel owner).transitions[index]? = some t) :
    t.before = runOwner program index owner ∧ stepArray program t.before = some t := by
  induction fuel generalizing owner index with
  | zero => simp [runArray] at h
  | succ fuel ih =>
      cases hs : stepArray program owner with
      | none => simp [runArray, hs] at h
      | some first =>
          cases index with
          | zero =>
              simp only [runArray, hs, List.getElem?_cons_zero, Option.some.injEq] at h
              subst t
              have hb := (stepArray_spec hs).1
              exact ⟨hb, by simpa [hb] using hs⟩
          | succ index =>
              simp only [runArray, hs, List.getElem?_cons_succ] at h
              obtain ⟨hb, ht⟩ := ih h
              exact ⟨by simpa [runOwner, hs] using hb, ht⟩

/-- The concrete output splits at each producing transition occurrence. This
retains order and multiplicity even when earlier or later pairs are equal. -/
theorem read_occurrence_output {program : Array Instruction} {fuel : Nat} {owner : Owner}
    {index : Nat} {t : ArrayTransition} {reply : Nat × Option Nat}
    (occurs : (runArray program fuel owner).transitions[index]? = some t)
    (read : t.read? = some reply) :
    (run program fuel owner).2.reads =
      ((runArray program fuel owner).transitions.take index).filterMap ArrayTransition.read? ++
        reply :: ((runArray program fuel owner).transitions.drop (index + 1)).filterMap
          ArrayTransition.read? ∧
    t.before = runOwner program index owner ∧ stepArray program t.before = some t := by
  refine ⟨?_, source_occurrence occurs⟩
  have split : (runArray program fuel owner).transitions =
      (runArray program fuel owner).transitions.take index ++
        t :: (runArray program fuel owner).transitions.drop (index + 1) := by
    have h := List.take_append_drop (index + 1) (runArray program fuel owner).transitions
    rw [List.take_succ, occurs] at h
    simpa [List.append_assoc] using h.symm
  rw [run_reads]
  change (runArray program fuel owner).transitions.filterMap ArrayTransition.read? = _
  simpa [read] using congrArg (List.filterMap ArrayTransition.read?) split

def boundaryAcc : List Boundary → Owner → Stats → Owner × Stats
  | [], owner, stats => (owner, stats)
  | b :: bs, owner, stats =>
      match boundaryStepArray b owner with
      | none => (owner, stats)
      | some t => boundaryAcc bs t.after (stats.record t)

theorem boundaryAcc_exact (bs : List Boundary) (owner : Owner) (stats : Stats) :
    boundaryAcc bs owner stats =
      (runBoundaryOwner bs owner, stats.fold (runBoundaryArray bs owner).transitions) := by
  induction bs generalizing owner stats with
  | nil => rfl
  | cons b bs ih =>
      cases h : boundaryStepArray b owner with
      | none => simp [boundaryAcc, runBoundaryOwner, runBoundaryArray, h, Stats.fold]
      | some t =>
          simpa [boundaryAcc, runBoundaryOwner, runBoundaryArray, h, Stats.fold] using
            ih t.after (stats.record t)

/-- Observe each admitted boundary action before its unchanged state update. -/
def boundaryAccThin : List Boundary → Owner → Stats → Owner × Stats
  | [], owner, stats => (owner, stats)
  | b :: bs, owner, stats =>
      match owner.status with
      | .halted _ =>
          let nextStats := stats.recordBefore (.boundary b) owner
          let nextOwner := executeBoundaryArray b owner
          boundaryAccThin bs nextOwner nextStats
      | _ => (owner, stats)

theorem boundaryAccThin_eq_boundaryAcc (bs : List Boundary) (owner : Owner) (stats : Stats) :
    boundaryAccThin bs owner stats = boundaryAcc bs owner stats := by
  induction bs generalizing owner stats with
  | nil => rfl
  | cons b bs ih =>
      cases hs : owner.status <;>
        simp [boundaryAccThin, boundaryAcc, boundaryStepArray, hs, ih,
          Stats.record_eq_recordBefore]

/-- These four events are observed exactly once on a halted owner's re-entry.
They do not read the payload; subsequent service instructions do. -/
theorem boundary_four (entry : PackedConstruction.Operand) (left right answer : Nat)
    (owner : Owner) (stats : Stats) (halted : owner.status = .halted answer) :
    let result := boundaryAcc [.left left, .right right, .entry entry, .activate] owner stats
    result.2.steps = stats.steps + 4 ∧
    result.2.counts.get .requestAdmission = stats.counts.get .requestAdmission + 2 ∧
    result.2.counts.get .controlEntry = stats.counts.get .controlEntry + 2 ∧
    result.2.reads = stats.reads := by
  simp [boundaryAcc, boundaryStepArray, executeBoundaryArray, halted, Stats.record,
    ArrayTransition.read?, Action.category, Counts.bump, Counts.get, Nat.add_assoc, Stats.reads]

/-- The real first request starts directly at the supplied constructor owner. -/
def buildFirst (model : InputModel) (xs : List Int) (left right : Nat) : Owner × Stats :=
  run (cachedProgram model) (Continuous.lifecycleBudget xs.length)
    (Executable.initialOwner model xs left right)

theorem buildFirst_owner (model : InputModel) (xs : List Int) (left right : Nat) :
    (buildFirst model xs left right).1 = Lifecycle.buildFirst model xs left right := by
  simpa only [buildFirst, Lifecycle.buildFirst, runThin_eq_runOwner] using
    run_owner (cachedProgram model) (Continuous.lifecycleBudget xs.length)
      (Executable.initialOwner model xs left right)

theorem buildFirst_stats (model : InputModel) (xs : List Int) (left right : Nat) :
    (buildFirst model xs left right).2 =
      ({} : Stats).fold (Ownership.observations model xs left right).transitions := by
  simp [buildFirst, run, runAccThin_eq_runAcc, runAcc_exact, cachedProgram_eq,
    Ownership.observations]

theorem buildFirst_steps (model : InputModel) (xs : List Int) (left right : Nat) :
    (buildFirst model xs left right).2.steps =
      (Ownership.observations model xs left right).steps := by
  simp [buildFirst_stats, Stats.fold_steps, ArrayRun.steps]

theorem buildFirst_count (model : InputModel) (xs : List Int) (left right : Nat) (c : Category) :
    (buildFirst model xs left right).2.counts.get c =
      (Ownership.observations model xs left right).categoryCount c := by
  simp [buildFirst_stats, Stats.fold_count, Counts.get_zero,
    ArrayRun.categoryCount, ArrayRun.categories]

theorem buildFirst_reads (model : InputModel) (xs : List Int) (left right : Nat) :
    (buildFirst model xs left right).2.reads =
      (Ownership.observations model xs left right).reads :=
  (congrArg Stats.reads (buildFirst_stats model xs left right)).trans
    (Stats.empty_fold_reads (Ownership.observations model xs left right).transitions)

theorem buildFirst_route (model : InputModel) (xs : List Int) (left right : Nat) (mark : RouteMark) :
    (buildFirst model xs left right).2.routes.get mark =
      (Ownership.observations model xs left right).transitions.countP (routeMarked mark) := by
  simp [buildFirst_stats, Stats.fold_route, RouteCounts.get_zero]

/-- Every advertised fold projection is transported to the same abstract run,
not inferred merely from the final-owner equality. -/
theorem fold_toRun (stats : Stats) (actual : ArrayRun) :
    (stats.fold actual.transitions).steps = stats.steps + actual.toRun.steps ∧
    (∀ c, (stats.fold actual.transitions).counts.get c =
      stats.counts.get c + actual.toRun.categoryCount c) ∧
    (stats.fold actual.transitions).reads = stats.reads ++ actual.toRun.reads := by
  obtain ⟨steps, categories, reads, _⟩ := actual.observations_toRun
  refine ⟨?_, ?_, ?_⟩
  · rw [Stats.fold_steps, steps]; rfl
  · intro c
    rw [Stats.fold_count]
    simp only [PackedLifecycle.Run.categoryCount, categories, ArrayRun.categories]
  · rw [Stats.fold_reads, reads]; rfl

/-- Transport through generic objects first, so kernel conversion never needs
to expand a fixed program or its input-dependent complete lifecycle run. -/
theorem observations_of_fold {stats : Stats} {actual : ArrayRun} {modelRun : PackedLifecycle.Run}
    (folded : stats = ({} : Stats).fold actual.transitions) (refined : actual.toRun = modelRun) :
    stats.steps = modelRun.steps ∧
    (∀ c, stats.counts.get c = modelRun.categoryCount c) ∧ stats.reads = modelRun.reads := by
  subst stats
  have projections := fold_toRun ({} : Stats) actual
  rw [refined] at projections
  simpa only [Counts.get_zero, Stats.reads, List.reverse_nil,
    List.nil_append, Nat.zero_add] using projections

theorem buildFirst_model_observations (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2 ^ PackedWordRAM.wordWidth xs.length)
    (hr : right < 2 ^ PackedWordRAM.wordWidth xs.length) :
    (buildFirst model xs left right).2.steps =
        (Continuous.continuousRun model xs left right).steps ∧
    (∀ c, (buildFirst model xs left right).2.counts.get c =
        (Continuous.continuousRun model xs left right).categoryCount c) ∧
    (buildFirst model xs left right).2.reads =
        (Continuous.continuousRun model xs left right).reads :=
  observations_of_fold (buildFirst_stats model xs left right)
    (Ownership.refinement model xs left right domain hl hr).2.2

/-- Later requests perform the original four events before service execution. -/
def queryAcc (model : InputModel) (left right : Nat) (owner : Owner) (stats : Stats) : Owner × Stats :=
  let admission := boundaryAccThin [.left left, .right right, .entry Layout.serviceEntry, .activate]
    owner stats
  runAccThin (cachedProgram model) Service.budget admission.1 admission.2

theorem queryAcc_exact (model : InputModel) (left right : Nat) (owner : Owner) (stats : Stats) :
    queryAcc model left right owner stats =
      (Lifecycle.query model left right owner,
        stats.fold (Executable.queryArray model left right owner).transitions) := by
  simp only [queryAcc, boundaryAccThin_eq_boundaryAcc, boundaryAcc_exact,
    runAccThin_eq_runAcc, runAcc_exact, Lifecycle.query, runThin_eq_runOwner,
    requestProtocolThin_eq_requestProtocolOwner,
    Executable.queryArray, requestProtocolArray, requestProtocolOwner,
    runBoundaryOwner_projection, cachedProgram_eq, Stats.fold_append]

def query (model : InputModel) (left right : Nat) (owner : Owner) : Owner × Stats :=
  queryAcc model left right owner {}

theorem query_owner (model : InputModel) (left right : Nat) (owner : Owner) :
    (query model left right owner).1 = Lifecycle.query model left right owner := by
  simp [query, queryAcc_exact]

theorem query_steps (model : InputModel) (left right : Nat) (owner : Owner) :
    (query model left right owner).2.steps = (Executable.queryArray model left right owner).steps := by
  simp [query, queryAcc_exact, Stats.fold_steps, ArrayRun.steps]

theorem query_count (model : InputModel) (left right : Nat) (owner : Owner) (c : Category) :
    (query model left right owner).2.counts.get c =
      (Executable.queryArray model left right owner).categoryCount c := by
  simp [query, queryAcc_exact, Stats.fold_count, Counts.get_zero,
    ArrayRun.categoryCount, ArrayRun.categories]

theorem query_reads (model : InputModel) (left right : Nat) (owner : Owner) :
    (query model left right owner).2.reads = (Executable.queryArray model left right owner).reads := by
  rw [query, queryAcc_exact, Stats.fold_reads]
  rfl

theorem query_route (model : InputModel) (left right : Nat) (owner : Owner) (mark : RouteMark) :
    (query model left right owner).2.routes.get mark =
      (Executable.queryArray model left right owner).transitions.countP (routeMarked mark) := by
  simp [query, queryAcc_exact, Stats.fold_route, RouteCounts.get_zero]

theorem query_model_observations (model : InputModel) (xs : List Int) (left right answer : Nat)
    (owner : Owner) (ready : Ownership.Ready xs owner) (halted : owner.status = .halted answer)
    (hl : left < 2 ^ PackedWordRAM.wordWidth xs.length)
    (hr : right < 2 ^ PackedWordRAM.wordWidth xs.length) :
    (query model left right owner).2.steps =
        (Reusable.queryRun model left right owner.toState).steps ∧
    (∀ c, (query model left right owner).2.counts.get c =
        (Reusable.queryRun model left right owner.toState).categoryCount c) ∧
    (query model left right owner).2.reads =
        (Reusable.queryRun model left right owner.toState).reads :=
  observations_of_fold (congrArg Prod.snd (queryAcc_exact model left right owner {}))
    (Executable.query_array_refinement model xs left right answer owner
      ready.1 ready.2 halted hl hr).1

/-- An explicit accumulated session includes the complete first segment and
later segment in order. No claim identifies this whole history with query-only
evidence. The returned production owner is still the same continuation owner. -/
theorem first_then_query (model : InputModel) (xs : List Int) (left right nextLeft nextRight : Nat) :
    let first := buildFirst model xs left right
    queryAcc model nextLeft nextRight first.1 first.2 =
      (Lifecycle.query model nextLeft nextRight (Lifecycle.buildFirst model xs left right),
        ({} : Stats).fold ((Ownership.observations model xs left right).transitions ++
          (Executable.queryArray model nextLeft nextRight
            (Lifecycle.buildFirst model xs left right)).transitions)) := by
  dsimp only
  rw [queryAcc_exact, buildFirst_owner, buildFirst_stats, Stats.fold_append]

/-! Small kernel controls for observation branches. These arbitrary test
programs do not claim to be reachable canonical lifecycle runs. Their owners
are theorem-local, so no test input or trace is initialized by a native import. -/

example :
    let owner : Owner := ⟨#[0, 0], #[some 9], #[], #[], 0, .running⟩
    let actual := run #[.old (.load 1 0), .old (.load 1 0), .old (.halt 1)] 4 owner
    actual.1.status = .halted 9 ∧ actual.2.steps = 3 ∧
      actual.2.counts.read = 2 ∧ actual.2.reads = [(0, some 9), (0, some 9)] := by
  decide

example :
    let owner : Owner := ⟨#[0, 0], #[], #[], #[], 0, .running⟩
    let actual := run #[.old (.load 1 0)] 4 owner
    actual.1.status = .fault ∧ actual.2.steps = 1 ∧
      actual.2.counts.read = 1 ∧ actual.2.reads = [(0, none)] := by
  decide

example :
    let owner : Owner := ⟨#[], #[], #[], #[], 0, .running⟩
    let actual := run #[] 4 owner
    actual.1.status = .running ∧ actual.2.steps = 0 ∧ actual.2.reads = [] := by
  decide

example :
    let owner : Owner := ⟨#[], #[], #[], #[], 0, .halted 7⟩
    let actual := run #[.releaseCell] 4 owner
    actual.1.status = .halted 7 ∧ actual.2.steps = 0 ∧ actual.2.reads = [] := by
  decide

end Observations
end RMQ.SuccinctFinal.PackedNative.Lifecycle
