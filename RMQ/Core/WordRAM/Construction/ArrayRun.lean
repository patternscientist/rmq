import RMQ.Core.WordRAM.Construction.Program

/-! # Array-backed evaluation of the construction machine

`run` operates on a functional `State` whose registers, memory and key banks
are functions, and fetches from a `List`. Executing it costs time linear in the
program counter per fetch and allocates a closure per write. `runArray` keeps
registers, memory, keys and key registers in arrays of fixed size, fetches from
an `Array`, and accumulates the projections `run` would report. The theorem
`runArray_abstract` makes it an exact stand-in for `run` in executable
validation: every recorded projection and the abstraction of the final state
agree with the frozen interpreter. It is not used by any proof of the
construction contract.
-/

namespace RMQ.SuccinctFinal.PackedConstruction

/-- Array-backed machine state for executable validation. `regs` and `keyRegs`
have a fixed literal size `R`; `memory.size` is the extent; absent cells are `none`. -/
structure ExecState where
  regs : Array Nat
  memory : Array (Option Nat)
  keys : Array (Option Int)
  keyRegs : Array Int
  pc : Nat
  status : Status

def ExecState.abstract (es : ExecState) : State where
  regs := fun r => es.regs.getD r 0
  memory := fun a => es.memory.getD a none
  extent := es.memory.size
  keys := fun i => es.keys.getD i none
  keyRegs := fun r => es.keyRegs.getD r 0
  pc := es.pc
  status := es.status

/-- Every numeric-register and key-register operand of the primitive is below `R`.
Register operands: load dst address; constant dst; move dst src; arithmetic dst lhs rhs;
comparison dst lhs rhs; jumpRegister src; branchZero condition; halt src; store address value;
reserve dst; loadKey dst (a KEY register) address (a numeric register); compareKey dst (numeric)
lhs rhs (key registers). Immediates (constant value, jump target, branchZero target) are NOT registers. -/
def Prim.RegistersBelow (R : Nat) : Prim → Prop
  | .load dst address => dst.val < R ∧ address.val < R
  | .constant dst _value => dst.val < R
  | .move dst src => dst.val < R ∧ src.val < R
  | .arithmetic _op dst lhs rhs => dst.val < R ∧ lhs.val < R ∧ rhs.val < R
  | .comparison _op dst lhs rhs => dst.val < R ∧ lhs.val < R ∧ rhs.val < R
  | .jump _target => True
  | .jumpRegister src => src.val < R
  | .branchZero condition _target => condition.val < R
  | .halt src => src.val < R
  | .store address value => address.val < R ∧ value.val < R
  | .reserve dst => dst.val < R
  | .loadKey dst address => dst.val < R ∧ address.val < R
  | .compareKey dst lhs rhs => dst.val < R ∧ lhs.val < R ∧ rhs.val < R

structure ArrayRun where
  final : ExecState
  steps : Nat
  categories : List Category
  writes : List (Nat × Nat)
  reserves : List Nat
  result : Option Nat

/-! ## Primitive execution -/

private def ExecState.writeNext (es : ExecState) (dst value : Nat) : ExecState :=
  { es with regs := es.regs.setIfInBounds dst value, pc := es.pc + 1 }

private def ExecState.writeKeyNext (es : ExecState) (dst : Nat) (key : Int) : ExecState :=
  { es with keyRegs := es.keyRegs.setIfInBounds dst key, pc := es.pc + 1 }

/-- Arm-by-arm mirror of `execPrim` on array state. -/
def execPrimArray (p : Prim) (es : ExecState) : ExecState :=
  match p with
  | .load dst address =>
      if es.regs.getD address.val 0 < es.memory.size then
        match es.memory.getD (es.regs.getD address.val 0) none with
        | some value => es.writeNext dst.val value
        | none => { es with status := .fault }
      else { es with status := .fault }
  | .constant dst value => es.writeNext dst.val value.val
  | .move dst src => es.writeNext dst.val (es.regs.getD src.val 0)
  | .arithmetic op dst lhs rhs =>
      es.writeNext dst.val (op.eval (es.regs.getD lhs.val 0) (es.regs.getD rhs.val 0))
  | .comparison op dst lhs rhs =>
      es.writeNext dst.val (op.eval (es.regs.getD lhs.val 0) (es.regs.getD rhs.val 0))
  | .jump target => { es with pc := target.val }
  | .jumpRegister src => { es with pc := es.regs.getD src.val 0 }
  | .branchZero condition target =>
      { es with pc := if es.regs.getD condition.val 0 = 0 then target.val else es.pc + 1 }
  | .halt src => { es with status := .halted (es.regs.getD src.val 0) }
  | .store address value =>
      if es.regs.getD address.val 0 < es.memory.size then
        { es with
          memory := es.memory.setIfInBounds (es.regs.getD address.val 0)
            (some (es.regs.getD value.val 0)),
          pc := es.pc + 1 }
      else { es with status := .fault }
  | .reserve dst =>
      { es with
        regs := es.regs.setIfInBounds dst.val es.memory.size,
        memory := es.memory.push none,
        pc := es.pc + 1 }
  | .loadKey dst address =>
      match es.keys.getD (es.regs.getD address.val 0) none with
      | some key => es.writeKeyNext dst.val key
      | none => { es with status := .fault }
  | .compareKey dst lhs rhs =>
      es.writeNext dst.val (if es.keyRegs.getD lhs.val 0 < es.keyRegs.getD rhs.val 0 then 1 else 0)

/-! ## Abstraction lemmas -/

private theorem ExecState.abstract_regs (es : ExecState) (r : Nat) :
    es.abstract.regs r = es.regs.getD r 0 := rfl

private theorem ExecState.abstract_memory (es : ExecState) (a : Nat) :
    es.abstract.memory a = es.memory.getD a none := rfl

private theorem ExecState.abstract_extent (es : ExecState) :
    es.abstract.extent = es.memory.size := rfl

private theorem ExecState.abstract_keys (es : ExecState) (i : Nat) :
    es.abstract.keys i = es.keys.getD i none := rfl

private theorem ExecState.abstract_pc (es : ExecState) : es.abstract.pc = es.pc := rfl

private theorem ExecState.abstract_status (es : ExecState) :
    es.abstract.status = es.status := rfl

theorem ExecState.abstract_cleanTail (es : ExecState) : CleanTail es.abstract := by
  intro a ha
  change es.memory.getD a none = none
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha]
  rfl

/-- Reading an in-bounds update through `getD` is the functional `put`. -/
private theorem abstract_setIfInBounds {α : Type} (xs : Array α) (i : Nat) (v d : α)
    (hi : i < xs.size) :
    (fun j => (xs.setIfInBounds i v).getD j d) = put (fun j => xs.getD j d) i v := by
  funext j
  simp only [put, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : j = i
  · subst h
    simp [hi]
  · simp [h, Ne.symm h]

/-- Pushing an absent cell is invisible through `getD _ none`. -/
private theorem abstract_push_none {α : Type} (xs : Array (Option α)) :
    (fun j => (xs.push none).getD j none) = fun j => xs.getD j none := by
  funext j
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  by_cases h : j = xs.size
  · subst h
    simp
  · simp [h]

private theorem writeNext_abstract (es : ExecState) (dst value : Nat)
    (hdst : dst < es.regs.size) :
    (es.writeNext dst value).abstract = es.abstract.writeNext dst value := by
  simp only [ExecState.writeNext, ExecState.abstract, State.writeNext, State.next,
    abstract_setIfInBounds _ _ _ _ hdst]

private theorem writeNext_regs_size (es : ExecState) (dst value : Nat) :
    (es.writeNext dst value).regs.size = es.regs.size := Array.size_setIfInBounds

private theorem writeNext_keyRegs_size (es : ExecState) (dst value : Nat) :
    (es.writeNext dst value).keyRegs.size = es.keyRegs.size := rfl

private theorem writeKeyNext_abstract (es : ExecState) (dst : Nat) (key : Int)
    (hdst : dst < es.keyRegs.size) :
    (es.writeKeyNext dst key).abstract =
      { es.abstract.next with keyRegs := put es.abstract.keyRegs dst key } := by
  simp only [ExecState.writeKeyNext, ExecState.abstract, State.next,
    abstract_setIfInBounds _ _ _ _ hdst]

theorem execPrimArray_abstract (p : Prim) (es : ExecState) (R : Nat)
    (hp : p.RegistersBelow R) (hregs : es.regs.size = R) (hkeys : es.keyRegs.size = R) :
    (execPrimArray p es).abstract = execPrim p es.abstract ∧
    (execPrimArray p es).regs.size = R ∧ (execPrimArray p es).keyRegs.size = R := by
  subst hregs
  cases p with
  | load dst address =>
      obtain ⟨hdst, -⟩ := hp
      simp only [execPrimArray, execPrim, ExecState.abstract_regs, ExecState.abstract_extent,
        ExecState.abstract_memory]
      by_cases ha : es.regs.getD address.val 0 < es.memory.size
      · rw [if_pos ha, if_pos ha]
        cases es.memory.getD (es.regs.getD address.val 0) none with
        | some value =>
            exact ⟨writeNext_abstract es _ _ hdst, writeNext_regs_size es _ _,
              (writeNext_keyRegs_size es _ _).trans hkeys⟩
        | none => exact ⟨rfl, rfl, hkeys⟩
      · rw [if_neg ha, if_neg ha]
        exact ⟨rfl, rfl, hkeys⟩
  | constant dst value =>
      have hdst : dst.val < es.regs.size := hp
      exact ⟨writeNext_abstract es _ _ hdst, writeNext_regs_size es _ _,
        (writeNext_keyRegs_size es _ _).trans hkeys⟩
  | move dst src =>
      obtain ⟨hdst, -⟩ := hp
      exact ⟨writeNext_abstract es _ _ hdst, writeNext_regs_size es _ _,
        (writeNext_keyRegs_size es _ _).trans hkeys⟩
  | arithmetic op dst lhs rhs =>
      obtain ⟨hdst, -, -⟩ := hp
      exact ⟨writeNext_abstract es _ _ hdst, writeNext_regs_size es _ _,
        (writeNext_keyRegs_size es _ _).trans hkeys⟩
  | comparison op dst lhs rhs =>
      obtain ⟨hdst, -, -⟩ := hp
      exact ⟨writeNext_abstract es _ _ hdst, writeNext_regs_size es _ _,
        (writeNext_keyRegs_size es _ _).trans hkeys⟩
  | jump target => exact ⟨rfl, rfl, hkeys⟩
  | jumpRegister src => exact ⟨rfl, rfl, hkeys⟩
  | branchZero condition target => exact ⟨rfl, rfl, hkeys⟩
  | halt src => exact ⟨rfl, rfl, hkeys⟩
  | store address value =>
      simp only [execPrimArray, execPrim, ExecState.abstract_regs, ExecState.abstract_extent]
      by_cases ha : es.regs.getD address.val 0 < es.memory.size
      · rw [if_pos ha, if_pos ha]
        refine ⟨?_, rfl, hkeys⟩
        simp only [ExecState.abstract, State.next, abstract_setIfInBounds _ _ _ _ ha,
          Array.size_setIfInBounds]
      · rw [if_neg ha, if_neg ha]
        exact ⟨rfl, rfl, hkeys⟩
  | reserve dst =>
      have hdst : dst.val < es.regs.size := hp
      refine ⟨?_, ?_, hkeys⟩
      · simp only [execPrimArray, execPrim, ExecState.abstract, State.writeNext, State.next,
          abstract_setIfInBounds _ _ _ _ hdst, abstract_push_none, Array.size_push]
      · simp only [execPrimArray, Array.size_setIfInBounds]
  | loadKey dst address =>
      obtain ⟨hdst, -⟩ := hp
      have hdst' : dst.val < es.keyRegs.size := by rw [hkeys]; exact hdst
      simp only [execPrimArray, execPrim, ExecState.abstract_regs, ExecState.abstract_keys]
      cases es.keys.getD (es.regs.getD address.val 0) none with
      | some key =>
          refine ⟨writeKeyNext_abstract es _ _ hdst', rfl, ?_⟩
          simp only [ExecState.writeKeyNext, Array.size_setIfInBounds, hkeys]
      | none => exact ⟨rfl, rfl, hkeys⟩
  | compareKey dst lhs rhs =>
      obtain ⟨hdst, -, -⟩ := hp
      exact ⟨writeNext_abstract es _ _ hdst, writeNext_regs_size es _ _,
        (writeNext_keyRegs_size es _ _).trans hkeys⟩

/-! ## Fuel-indexed array run with reversed accumulators -/

private def consOpt {α : Type} : Option α → List α → List α
  | none, acc => acc
  | some x, acc => x :: acc

/-- The write event of a primitive about to execute on `es`, read from the
pre-state; mirrors `Transition.write?`. -/
private def writeEvent? (p : Prim) (es : ExecState) : Option (Nat × Nat) :=
  match p with
  | .store address value =>
      if es.regs.getD address.val 0 < es.memory.size then
        some (es.regs.getD address.val 0, es.regs.getD value.val 0)
      else none
  | _ => none

/-- The reservation of a primitive about to execute on `es`; mirrors
`Transition.reserve?`. -/
private def reserveEvent? (p : Prim) (es : ExecState) : Option Nat :=
  match p with
  | .reserve _ => some es.memory.size
  | _ => none

private def finishRun (es : ExecState) (steps : Nat) (cats : List Category)
    (writes : List (Nat × Nat)) (reserves : List Nat) : ArrayRun where
  final := es
  steps := steps
  categories := cats.reverse
  writes := writes.reverse
  reserves := reserves.reverse
  result :=
    match es.status with
    | .halted value => some value
    | _ => none

private def runArrayAux (program : Array BInstr) : Nat → ExecState → Nat → List Category →
    List (Nat × Nat) → List Nat → ArrayRun
  | 0, es, steps, cats, writes, reserves => finishRun es steps cats writes reserves
  | fuel + 1, es, steps, cats, writes, reserves =>
      match program[es.pc]? with
      | none => finishRun es steps cats writes reserves
      | some i =>
          match es.status with
          | .running =>
              let w := writeEvent? i.primitive es
              let r := reserveEvent? i.primitive es
              runArrayAux program fuel (execPrimArray i.primitive es) (steps + 1)
                (i.primitive.category :: cats) (consOpt w writes) (consOpt r reserves)
          | .halted _ => finishRun es steps cats writes reserves
          | .fault => finishRun es steps cats writes reserves

def runArray (program : Array BInstr) (fuel : Nat) (es : ExecState) : ArrayRun :=
  runArrayAux program fuel es 0 [] [] []

private theorem writeEvent?_eq (i : BInstr) (es : ExecState) (s' : State) :
    writeEvent? i.primitive es = Transition.write? ⟨es.abstract, i, s'⟩ := by
  cases h : i.primitive <;> simp only [writeEvent?, Transition.write?, h] <;> rfl

private theorem reserveEvent?_eq (i : BInstr) (es : ExecState) (s' : State) :
    reserveEvent? i.primitive es = Transition.reserve? ⟨es.abstract, i, s'⟩ := by
  cases h : i.primitive <;> simp only [reserveEvent?, Transition.reserve?, h] <;> rfl

private theorem consOpt_reverse_append_none {α : Type} (acc L : List α) :
    (consOpt none acc).reverse ++ L = acc.reverse ++ L := rfl

private theorem consOpt_reverse_append_some {α : Type} (x : α) (acc L : List α) :
    (consOpt (some x) acc).reverse ++ L = acc.reverse ++ (x :: L) := by
  simp [consOpt, List.reverse_cons, List.append_assoc]

private theorem finishRun_spec (es : ExecState) (steps : Nat) (cats : List Category)
    (writes : List (Nat × Nat)) (reserves : List Nat) :
    (finishRun es steps cats writes reserves).final.abstract = (Run.mk es.abstract []).final ∧
    (finishRun es steps cats writes reserves).steps = steps + (Run.mk es.abstract []).steps ∧
    (finishRun es steps cats writes reserves).categories =
      cats.reverse ++ (Run.mk es.abstract []).categories ∧
    (finishRun es steps cats writes reserves).writes =
      writes.reverse ++ (Run.mk es.abstract []).writes ∧
    (finishRun es steps cats writes reserves).reserves =
      reserves.reverse ++ (Run.mk es.abstract []).reserves ∧
    (finishRun es steps cats writes reserves).result = (Run.mk es.abstract []).result := by
  obtain ⟨regs, memory, keys, keyRegs, pc, status⟩ := es
  refine ⟨rfl, rfl, (List.append_nil _).symm, (List.append_nil _).symm,
    (List.append_nil _).symm, ?_⟩
  cases status <;> rfl

private theorem runArrayAux_spec (program : List BInstr) (R : Nat)
    (hprog : ∀ i ∈ program, i.primitive.RegistersBelow R) (fuel : Nat) (es : ExecState)
    (hregs : es.regs.size = R) (hkeys : es.keyRegs.size = R)
    (steps : Nat) (cats : List Category) (writes : List (Nat × Nat)) (reserves : List Nat) :
    (runArrayAux program.toArray fuel es steps cats writes reserves).final.abstract =
      (run program fuel es.abstract).final ∧
    (runArrayAux program.toArray fuel es steps cats writes reserves).steps =
      steps + (run program fuel es.abstract).steps ∧
    (runArrayAux program.toArray fuel es steps cats writes reserves).categories =
      cats.reverse ++ (run program fuel es.abstract).categories ∧
    (runArrayAux program.toArray fuel es steps cats writes reserves).writes =
      writes.reverse ++ (run program fuel es.abstract).writes ∧
    (runArrayAux program.toArray fuel es steps cats writes reserves).reserves =
      reserves.reverse ++ (run program fuel es.abstract).reserves ∧
    (runArrayAux program.toArray fuel es steps cats writes reserves).result =
      (run program fuel es.abstract).result := by
  induction fuel generalizing es steps cats writes reserves with
  | zero =>
      simp only [runArrayAux, run]
      exact finishRun_spec es steps cats writes reserves
  | succ fuel ih =>
      simp only [runArrayAux, run, stepProgram, fetch, checkedStep, bstep, List.getElem?_toArray,
        ExecState.abstract_pc, ExecState.abstract_status]
      cases h : program[es.pc]? with
      | none =>
          simp only []
          exact finishRun_spec es steps cats writes reserves
      | some i =>
          cases hs : es.status with
          | running =>
              simp only []
              obtain ⟨hab, hregs', hkeys'⟩ :=
                execPrimArray_abstract i.primitive es R (hprog i (List.mem_of_getElem? h))
                  hregs hkeys
              obtain ⟨hf, hst, hc, hw, hr, hres⟩ := ih (execPrimArray i.primitive es) hregs' hkeys'
                (steps + 1) (i.primitive.category :: cats)
                (consOpt (writeEvent? i.primitive es) writes)
                (consOpt (reserveEvent? i.primitive es) reserves)
              rw [hab] at hf hst hc hw hr hres
              refine ⟨hf, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hst]
                simp only [Run.steps, List.length_cons]
                omega
              · rw [hc]
                simp [Run.categories, List.reverse_cons, List.append_assoc]
              · rw [hw]
                simp only [Run.writes, List.filterMap_cons,
                  writeEvent?_eq i es (execPrim i.primitive es.abstract)]
                cases Transition.write? ⟨es.abstract, i, execPrim i.primitive es.abstract⟩ with
                | none => exact consOpt_reverse_append_none _ _
                | some w => exact consOpt_reverse_append_some _ _ _
              · rw [hr]
                simp only [Run.reserves, List.filterMap_cons,
                  reserveEvent?_eq i es (execPrim i.primitive es.abstract)]
                cases Transition.reserve? ⟨es.abstract, i, execPrim i.primitive es.abstract⟩ with
                | none => exact consOpt_reverse_append_none _ _
                | some a => exact consOpt_reverse_append_some _ _ _
              · rw [hres]
                rfl
          | halted value =>
              simp only []
              exact finishRun_spec es steps cats writes reserves
          | fault =>
              simp only []
              exact finishRun_spec es steps cats writes reserves

theorem runArray_abstract (program : List BInstr) (R : Nat)
    (hprog : ∀ i ∈ program, i.primitive.RegistersBelow R) (fuel : Nat) (es : ExecState)
    (hregs : es.regs.size = R) (hkeys : es.keyRegs.size = R) :
    (runArray program.toArray fuel es).steps = (run program fuel es.abstract).steps ∧
    (runArray program.toArray fuel es).categories = (run program fuel es.abstract).categories ∧
    (runArray program.toArray fuel es).writes = (run program fuel es.abstract).writes ∧
    (runArray program.toArray fuel es).reserves = (run program fuel es.abstract).reserves ∧
    (runArray program.toArray fuel es).result = (run program fuel es.abstract).result ∧
    (runArray program.toArray fuel es).final.abstract = (run program fuel es.abstract).final := by
  obtain ⟨hf, hst, hc, hw, hr, hres⟩ :=
    runArrayAux_spec program R hprog fuel es hregs hkeys 0 [] [] []
  exact ⟨by rw [runArray, hst, Nat.zero_add], by rw [runArray, hc]; rfl,
    by rw [runArray, hw]; rfl, by rw [runArray, hr]; rfl, by rw [runArray, hres],
    by rw [runArray, hf]⟩

/-! ## Initial array states -/

/-- Initial array states whose abstraction is exactly the frozen initial state. -/
def ExecState.ofWordInput (R width : Nat) (xs : List Int) : ExecState where
  regs := Array.replicate R 0
  memory := (some xs.length :: xs.map (fun x => some (encodeInt width x))).toArray
  keys := #[]
  keyRegs := Array.replicate R 0
  pc := 0
  status := .running

def ExecState.ofComparisonInput (R : Nat) (xs : List Int) : ExecState where
  regs := Array.replicate R 0
  memory := #[some xs.length]
  keys := (xs.map some).toArray
  keyRegs := Array.replicate R 0
  pc := 0
  status := .running

private theorem state_ext {s t : State} (hregs : s.regs = t.regs) (hmem : s.memory = t.memory)
    (hext : s.extent = t.extent) (hkeys : s.keys = t.keys) (hkr : s.keyRegs = t.keyRegs)
    (hpc : s.pc = t.pc) (hst : s.status = t.status) : s = t := by
  cases s
  cases t
  cases hregs
  cases hmem
  cases hext
  cases hkeys
  cases hkr
  cases hpc
  cases hst
  rfl

private theorem getD_replicate {α : Type} (n : Nat) (d : α) (i : Nat) :
    (Array.replicate n d).getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem ExecState.ofWordInput_abstract (R width : Nat) (xs : List Int) :
    (ExecState.ofWordInput R width xs).abstract = wordInputState width xs := by
  apply state_ext
  · funext r
    exact getD_replicate R 0 r
  · funext a
    change ((some xs.length :: xs.map (fun x => some (encodeInt width x))).toArray).getD a none =
      encodeInput width xs a
    cases a with
    | zero => simp [Array.getD_eq_getD_getElem?]
    | succ i =>
        simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_succ,
          List.getElem?_map, encodeInput_succ]
        cases xs[i]? <;> rfl
  · change ((some xs.length :: xs.map (fun x => some (encodeInt width x))).toArray).size =
      inputCellCount xs
    simp [inputCellCount]
  · funext i
    change (#[] : Array (Option Int)).getD i none = none
    simp [Array.getD_eq_getD_getElem?]
  · funext r
    exact getD_replicate R 0 r
  · rfl
  · rfl

theorem ExecState.ofComparisonInput_abstract (R : Nat) (xs : List Int) :
    (ExecState.ofComparisonInput R xs).abstract = comparisonInputState xs := by
  apply state_ext
  · funext r
    exact getD_replicate R 0 r
  · funext a
    change (#[some xs.length] : Array (Option Nat)).getD a none =
      (if a = 0 then some xs.length else none)
    cases a with
    | zero => simp [Array.getD_eq_getD_getElem?]
    | succ i => simp [Array.getD_eq_getD_getElem?]
  · rfl
  · funext i
    change ((xs.map some).toArray).getD i none = xs[i]?
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
    cases xs[i]? <;> rfl
  · funext r
    exact getD_replicate R 0 r
  · rfl
  · rfl

theorem ExecState.ofWordInput_sizes (R width : Nat) (xs : List Int) :
    (ExecState.ofWordInput R width xs).regs.size = R ∧
    (ExecState.ofWordInput R width xs).keyRegs.size = R :=
  ⟨Array.size_replicate, Array.size_replicate⟩

theorem ExecState.ofComparisonInput_sizes (R : Nat) (xs : List Int) :
    (ExecState.ofComparisonInput R xs).regs.size = R ∧
    (ExecState.ofComparisonInput R xs).keyRegs.size = R :=
  ⟨Array.size_replicate, Array.size_replicate⟩

/-! ## Executable sanity checks

`[3]` has length 1, so the header load puts 1 in register 1; the reservation
returns the extent 2 into register 2; the store writes cell 2 := regs 1 = 1;
`halt 1` returns 1. Four transitions, one write, one reservation, extent 3. -/

private def toy : List BInstr := [⟨.load 1 0⟩, ⟨.reserve 2⟩, ⟨.store 2 1⟩, ⟨.halt 1⟩]

private def toyStart : ExecState := ExecState.ofWordInput 4 40 [3]

#guard (runArray toy.toArray 10 toyStart).steps = 4
#guard (runArray toy.toArray 10 toyStart).writes = [(2, 1)]
#guard (runArray toy.toArray 10 toyStart).reserves = [2]
#guard (runArray toy.toArray 10 toyStart).categories = [.read, .allocation, .write, .control]
#guard (runArray toy.toArray 10 toyStart).result = some 1
#guard (runArray toy.toArray 10 toyStart).final.memory.size = 3

end RMQ.SuccinctFinal.PackedConstruction
