import RMQ.Core.WordRAM.Packed.InteriorLocate
import RMQ.Core.WordRAM.Packed.Setup
import RMQ.Core.WordRAM.Packed.Frame
import RMQ.Core.WordRAM.Packed.LogicalSpan

/-!
# Fixed descriptor selection from the charged metadata register bank

Register operands are fixed when the source is constructed. Pure register-field
specifications below are proof references; primitive code uses finite branches
and explicit moves, never an indirect register-read operation.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian PackedCellProbe Structured

def spanPresence : Option NumericSpan → Nat
  | none => 0
  | some _ => 1

def spanPosition (span : Option NumericSpan) : Nat := (span.map (·.position)).getD 0
def spanLength (span : Option NumericSpan) : Nat := (span.map (·.length)).getD 0

def LocationResult (base : Nat) (span : Option NumericSpan) (data : Data) : Prop :=
  data.status = .running ∧ data.regs (base + 2) = spanPresence span ∧
    data.regs (base + 3) = spanPosition span ∧ data.regs (base + 4) = spanLength span

def LocateFrame (base : Nat) (before after : Registers) : Prop :=
  ∀ r, r < base + 2 ∨ base + 49 ≤ r → after r = before r

private theorem data_eq_running (data : Data) (hs : data.status = .running) :
    data = ⟨data.regs, .running⟩ := by
  cases data
  simp_all

def copyInputsFrom (destination : Nat) : List Nat → Block
  | [] => .skip
  | source :: rest =>
      .seq (.action (.move destination source)) (copyInputsFrom (destination + 1) rest)

theorem copyInputsFrom_size (destination : Nat) (sources : List Nat) :
    (copyInputsFrom destination sources).size = sources.length := by
  induction sources generalizing destination with
  | nil => rfl
  | cons source rest ih => simp [copyInputsFrom, Block.size, ih, Nat.add_comm]

/-- Every source is below the destination bank, so earlier copies cannot alter
any later source. The list is compile-time syntax, not runtime metadata. -/
theorem copyInputsFrom_source (destination : Nat) (sources : List Nat)
    (memory : Memory) (regs : Registers)
    (hsource : ∀ r ∈ sources, r < destination) :
    let actual := (copyInputsFrom destination sources).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
    (∀ i (hi : i < sources.length), actual.final.regs (destination + i) = regs sources[i]) ∧
    (∀ r, r < destination ∨ destination + sources.length ≤ r → actual.final.regs r = regs r) ∧
    actual.reads = [] := by
  induction sources generalizing destination regs with
  | nil => simp [copyInputsFrom, Block.eval]
  | cons source rest ih =>
      have hhead := hsource source (by simp)
      have hrest : ∀ r ∈ rest, r < destination := by
        intro r hr
        exact hsource r (by simp [hr])
      let next := regs.write destination (regs source)
      have ht := ih (destination + 1) next (by intro r hr; have := hrest r hr; omega)
      have heval : (copyInputsFrom destination (source :: rest)).eval memory ⟨regs, .running⟩ =
          (copyInputsFrom (destination + 1) rest).eval memory ⟨next, .running⟩ := by
        simp [copyInputsFrom, Block.eval_seq, Evaluation.bind, Block.eval, Action.eval,
          Action.instruction, execute, State.writeNext, Data.ofState, next]
      rw [heval]
      refine ⟨ht.1, ?_, ?_, ht.2.2.2⟩
      · intro i hi
        cases i with
        | zero =>
            have hf := ht.2.2.1 destination (Or.inl (by omega))
            simpa [next] using hf
        | succ i =>
            have hi' : i < rest.length := by simpa using hi
            have hh := ht.2.1 i hi'
            have hs := hrest rest[i] (List.getElem_mem hi')
            simpa [next, Registers.write, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
              show rest[i] ≠ destination by omega] using hh
      · intro r hr
        have hf := ht.2.2.1 r (by simp only [List.length_cons] at hr; omega)
        have hn : r ≠ destination := by simp only [List.length_cons] at hr; omega
        simpa [next, Registers.write, hn] using hf

def exportSpanBlock (base offset : Nat) : Block :=
  Block.sequence [
    .action (.move (base + 2) (base + offset)),
    .action (.move (base + 3) (base + offset + 1)),
    .action (.move (base + 4) (base + offset + 2))]

theorem exportSpanBlock_eval (base offset : Nat) (hoffset : 7 ≤ offset)
    (memory : Memory) (data : Data) (hs : data.status = .running) :
    (exportSpanBlock base offset).eval memory data =
      ⟨⟨((data.regs.write (base + 2) (data.regs (base + offset))).write
          (base + 3) (data.regs (base + offset + 1))).write
          (base + 4) (data.regs (base + offset + 2)), .running⟩, []⟩ := by
  have h0 : offset ≠ 0 := by omega
  have h1 : offset ≠ 1 := by omega
  simp (disch := omega) [exportSpanBlock, Block.sequence, Block.eval, hs, Action.eval,
    Action.instruction, execute, State.writeNext, Data.ofState, Registers.write, h0, h1]

theorem exportSpanBlock_frame (base offset : Nat) (hoffset : 7 ≤ offset)
    (memory : Memory) (data : Data) (hs : data.status = .running)
    (r : Nat) (hr : r < base + 2 ∨ base + 5 ≤ r) :
    ((exportSpanBlock base offset).eval memory data).final.regs r = data.regs r := by
  rw [exportSpanBlock_eval base offset hoffset memory data hs]
  have h2 : r ≠ base + 2 := by omega
  have h3 : r ≠ base + 3 := by omega
  have h4 : r ≠ base + 4 := by omega
  simp [Registers.write, h2, h3, h4]

def storedRegularSpan (regs : Registers) (segment index : Nat) : Option NumericSpan :=
  regularSpan index (regs (58 + 4 * segment)) (regs (58 + 4 * segment + 1))
    (regs (58 + 4 * segment + 2)) (regs (58 + 4 * segment + 3))

def interiorComponentIndex : PackedReviewerInteriorComponentTag → Nat
  | .baseline => 0 | .minRel => 1 | .maxRel => 2 | .argOffset => 3
  | .localOffset => 4 | .globalBlock => 5 | .localLevel => 6 | .globalLevel => 7

theorem interiorComponentIndex_lt (component : PackedReviewerInteriorComponentTag) :
    interiorComponentIndex component < 8 := by cases component <;> decide

def storedInteriorSpan (regs : Registers) (index : Nat)
    (component : PackedReviewerInteriorComponentTag) : Option NumericSpan :=
  let field := 150 + 5 * interiorComponentIndex component
  interiorSpan index (regs field) (regs (field + 1)) (regs (field + 2))
    (regs (field + 3)) (regs (field + 4)) (regs 32)

def regularCaseInputs (base segment : Nat) : List Nat :=
  [base + 1, 58 + 4 * segment, 58 + 4 * segment + 1,
    58 + 4 * segment + 2, 58 + 4 * segment + 3]

def regularCaseBlock (base segment : Nat) : Block :=
  .seq (copyInputsFrom (base + 32) (regularCaseInputs base segment))
    (.seq (regularLocateBlock (base + 32)) (exportSpanBlock base 37))

theorem regularCaseBlock_source (base segment : Nat) (hb : 256 ≤ base)
    (hsegment : segment < 23) (memory : Memory) (regs : Registers) :
    let actual := (regularCaseBlock base segment).eval memory ⟨regs, .running⟩
    LocationResult base (storedRegularSpan regs segment (regs (base + 1))) actual.final ∧
    actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  let prepared := (copyInputsFrom (base + 32) (regularCaseInputs base segment)).eval memory
    ⟨regs, .running⟩
  have hp := copyInputsFrom_source (base + 32) (regularCaseInputs base segment) memory regs
    (by intro r hr; simp only [regularCaseInputs, List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
  have hv0 := hp.2.1 0 (by simp [regularCaseInputs])
  have hv1 := hp.2.1 1 (by simp [regularCaseInputs])
  have hv2 := hp.2.1 2 (by simp [regularCaseInputs])
  have hv3 := hp.2.1 3 (by simp [regularCaseInputs])
  have hv4 := hp.2.1 4 (by simp [regularCaseInputs])
  simp only [regularCaseInputs, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_zero] at hv0 hv1 hv2 hv3 hv4
  have hc := regularLocateBlock_source (base + 32) memory prepared.final.regs
  have hspan : regularSpan (prepared.final.regs (base + 32))
      (prepared.final.regs (base + 32 + 1)) (prepared.final.regs (base + 32 + 2))
      (prepared.final.regs (base + 32 + 3)) (prepared.final.regs (base + 32 + 4)) =
      storedRegularSpan regs segment (regs (base + 1)) := by
    dsimp only [prepared, regularCaseInputs]
    rw [hv0, hv1, hv2, hv3, hv4]
    rfl
  rw [hspan] at hc
  let child := (regularLocateBlock (base + 32)).eval memory ⟨prepared.final.regs, .running⟩
  have hcs : child.final.status = .running := hc.1.1
  have heval : (regularCaseBlock base segment).eval memory ⟨regs, .running⟩ =
      (exportSpanBlock base 37).eval memory child.final := by
    simp only [regularCaseBlock, Block.eval_seq, Evaluation.bind]
    rw [data_eq_running _ hp.1]
    rw [hp.2.2.2, hc.2]
    simp
    rfl
  rw [heval, exportSpanBlock_eval base 37 (by omega) memory child.final hcs]
  refine ⟨?_, rfl, ?_⟩
  · have hl := hc.1
    cases ho : storedRegularSpan regs segment (regs (base + 1)) with
    | none =>
        simp only [ho, LocatedSpan] at hl
        simp [LocationResult, spanPresence, spanPosition, spanLength, Registers.write,
          child, Nat.add_assoc] at hl ⊢
        exact hl.2
    | some span =>
        simp only [ho, LocatedSpan] at hl
        simp [LocationResult, spanPresence, spanPosition, spanLength, Registers.write,
          child, Nat.add_assoc] at hl ⊢
        exact hl.2
  · intro r hr
    have h2 : r ≠ base + 2 := by omega
    have h3 : r ≠ base + 3 := by omega
    have h4 : r ≠ base + 4 := by omega
    have hf := regularLocateBlock_frame (base + 32) memory prepared.final.regs r (by omega)
    have hpf := hp.2.2.1 r (by simp only [regularCaseInputs, List.length_cons, List.length_nil]; omega)
    simpa [LocateFrame, Registers.write, child, prepared, h2, h3, h4] using hf.trans hpf

def interiorCaseInputs (base : Nat) (component : PackedReviewerInteriorComponentTag) : List Nat :=
  let field := 150 + 5 * interiorComponentIndex component
  [base + 1, field, field + 1, field + 2, field + 3, field + 4, 32]

def interiorCaseBlock (base : Nat) (component : PackedReviewerInteriorComponentTag) : Block :=
  .seq (copyInputsFrom (base + 32) (interiorCaseInputs base component))
    (.seq (interiorLocateBlock (base + 32)) (exportSpanBlock base 39))

theorem interiorCaseBlock_source (base : Nat) (hb : 256 ≤ base)
    (component : PackedReviewerInteriorComponentTag) (memory : Memory) (regs : Registers) :
    let actual := (interiorCaseBlock base component).eval memory ⟨regs, .running⟩
    LocationResult base (storedInteriorSpan regs (regs (base + 1)) component) actual.final ∧
    actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  have hcomponent := interiorComponentIndex_lt component
  let prepared := (copyInputsFrom (base + 32) (interiorCaseInputs base component)).eval memory
    ⟨regs, .running⟩
  have hp := copyInputsFrom_source (base + 32) (interiorCaseInputs base component) memory regs
    (by intro r hr; simp only [interiorCaseInputs, List.mem_cons, List.not_mem_nil, or_false] at hr; omega)
  have hv0 := hp.2.1 0 (by simp [interiorCaseInputs])
  have hv1 := hp.2.1 1 (by simp [interiorCaseInputs])
  have hv2 := hp.2.1 2 (by simp [interiorCaseInputs])
  have hv3 := hp.2.1 3 (by simp [interiorCaseInputs])
  have hv4 := hp.2.1 4 (by simp [interiorCaseInputs])
  have hv5 := hp.2.1 5 (by simp [interiorCaseInputs])
  have hv6 := hp.2.1 6 (by simp [interiorCaseInputs])
  simp only [interiorCaseInputs, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_zero] at hv0 hv1 hv2 hv3 hv4 hv5 hv6
  have hc := interiorLocateBlock_source (base + 32) memory prepared.final.regs
  have hspan : interiorSpan (prepared.final.regs (base + 32))
      (prepared.final.regs (base + 32 + 1)) (prepared.final.regs (base + 32 + 2))
      (prepared.final.regs (base + 32 + 3)) (prepared.final.regs (base + 32 + 4))
      (prepared.final.regs (base + 32 + 5)) (prepared.final.regs (base + 32 + 6)) =
      storedInteriorSpan regs (regs (base + 1)) component := by
    dsimp only [prepared, interiorCaseInputs]
    rw [hv0, hv1, hv2, hv3, hv4, hv5, hv6]
    rfl
  rw [hspan] at hc
  let child := (interiorLocateBlock (base + 32)).eval memory ⟨prepared.final.regs, .running⟩
  have hcs : child.final.status = .running := hc.1.1
  have heval : (interiorCaseBlock base component).eval memory ⟨regs, .running⟩ =
      (exportSpanBlock base 39).eval memory child.final := by
    simp only [interiorCaseBlock, Block.eval_seq, Evaluation.bind]
    rw [data_eq_running _ hp.1]
    rw [hp.2.2.2, hc.2]
    simp
    rfl
  rw [heval, exportSpanBlock_eval base 39 (by omega) memory child.final hcs]
  refine ⟨?_, rfl, ?_⟩
  · have hl := hc.1
    cases ho : storedInteriorSpan regs (regs (base + 1)) component with
    | none =>
        simp only [ho, InteriorLocatedSpan] at hl
        simp [LocationResult, spanPresence, spanPosition, spanLength, Registers.write,
          child, Nat.add_assoc] at hl ⊢
        exact hl.2
    | some span =>
        simp only [ho, InteriorLocatedSpan] at hl
        simp [LocationResult, spanPresence, spanPosition, spanLength, Registers.write,
          child, Nat.add_assoc] at hl ⊢
        exact hl.2
  · intro r hr
    have h2 : r ≠ base + 2 := by omega
    have h3 : r ≠ base + 3 := by omega
    have h4 : r ≠ base + 4 := by omega
    have hf := interiorLocateBlock_frame (base + 32) memory prepared.final.regs r (by omega)
    have hpf := hp.2.2.1 r (by simp only [interiorCaseInputs, List.length_cons, List.length_nil]; omega)
    simpa [LocateFrame, Registers.write, child, prepared, h2, h3, h4] using hf.trans hpf

theorem LocateFrame.trans {base : Nat} {first second third : Registers}
    (hsecond : LocateFrame base second third) (hfirst : LocateFrame base first second) :
    LocateFrame base first third := fun r hr => (hsecond r hr).trans (hfirst r hr)

theorem storedRegularSpan_frame (base segment index : Nat) (hb : 256 ≤ base)
    (hsegment : segment < 23) (first second : Registers) (hf : LocateFrame base first second) :
    storedRegularSpan second segment index = storedRegularSpan first segment index := by
  unfold storedRegularSpan
  rw [hf _ (Or.inl (by omega)), hf _ (Or.inl (by omega)),
    hf _ (Or.inl (by omega)), hf _ (Or.inl (by omega))]

theorem storedInteriorSpan_frame (base index : Nat) (hb : 256 ≤ base)
    (component : PackedReviewerInteriorComponentTag) (first second : Registers)
    (hf : LocateFrame base first second) :
    storedInteriorSpan second index component = storedInteriorSpan first index component := by
  have hc := interiorComponentIndex_lt component
  dsimp only [storedInteriorSpan]
  rw [hf _ (Or.inl (by omega)), hf _ (Or.inl (by omega)), hf _ (Or.inl (by omega)),
    hf _ (Or.inl (by omega)), hf _ (Or.inl (by omega)), hf _ (Or.inl (by omega))]

theorem storedInteriorFind_frame (base index : Nat) (hb : 256 ≤ base)
    (components : List PackedReviewerInteriorComponentTag) (first second : Registers)
    (hf : LocateFrame base first second) :
    components.findSome? (storedInteriorSpan second index) =
      components.findSome? (storedInteriorSpan first index) := by
  have heq : storedInteriorSpan second index = storedInteriorSpan first index := by
    funext component
    exact storedInteriorSpan_frame base index hb component first second hf
  rw [heq]

def absentLocationBlock (base : Nat) : Block :=
  Block.sequence [.action (.constant (base + 2) 0),
    .action (.constant (base + 3) 0), .action (.constant (base + 4) 0)]

theorem absentLocationBlock_source (base : Nat) (memory : Memory) (regs : Registers) :
    let actual := (absentLocationBlock base).eval memory ⟨regs, .running⟩
    LocationResult base none actual.final ∧ actual.reads = [] ∧
      LocateFrame base regs actual.final.regs := by
  constructor
  · simp [absentLocationBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState, Registers.write, LocationResult,
      spanPresence, spanPosition, spanLength]
  constructor
  · rfl
  · intro r hr
    have h2 : r ≠ base + 2 := by omega
    have h3 : r ≠ base + 3 := by omega
    have h4 : r ≠ base + 4 := by omega
    simp [absentLocationBlock, Block.sequence, Block.eval, Action.eval, Action.instruction,
      execute, State.writeNext, Data.ofState, Registers.write, h2, h3, h4]

private theorem seq_ifZero_noReads (memory : Memory) (first zero nonzero : Block)
    (condition : Nat) (data : Data)
    (hs : (first.eval memory data).final.status = .running)
    (hr : (first.eval memory data).reads = []) :
    (Block.seq first (.ifZero condition zero nonzero)).eval memory data =
      if (first.eval memory data).final.regs condition = 0 then
        zero.eval memory (first.eval memory data).final
      else nonzero.eval memory (first.eval memory data).final := by
  rw [Block.eval_seq]
  simp only [Evaluation.bind, Block.eval, hs, hr, List.nil_append]

private theorem eval_skip (memory : Memory) (data : Data) :
    Block.skip.eval memory data = ⟨data, []⟩ := by
  cases data with
  | mk regs status => cases status <;> rfl

def interiorDispatch (base : Nat) : List PackedReviewerInteriorComponentTag → Block
  | [] => absentLocationBlock base
  | component :: rest =>
      .seq (interiorCaseBlock base component)
        (.ifZero (base + 2) (interiorDispatch base rest) .skip)

theorem interiorDispatch_source (base : Nat) (hb : 256 ≤ base)
    (components : List PackedReviewerInteriorComponentTag) (memory : Memory) (regs : Registers) :
    let actual := (interiorDispatch base components).eval memory ⟨regs, .running⟩
    LocationResult base (components.findSome? (storedInteriorSpan regs (regs (base + 1))))
      actual.final ∧ actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  induction components generalizing regs with
  | nil => simpa [interiorDispatch] using absentLocationBlock_source base memory regs
  | cons component rest ih =>
      have hc := interiorCaseBlock_source base hb component memory regs
      let child := (interiorCaseBlock base component).eval memory ⟨regs, .running⟩
      change LocationResult base (storedInteriorSpan regs (regs (base + 1)) component)
        child.final ∧ child.reads = [] ∧ LocateFrame base regs child.final.regs at hc
      have hs : child.final.status = .running := hc.1.1
      have hidx : child.final.regs (base + 1) = regs (base + 1) := hc.2.2 _ (Or.inl (by omega))
      have heval := seq_ifZero_noReads memory (interiorCaseBlock base component)
        (interiorDispatch base rest) .skip (base + 2) ⟨regs, .running⟩ hc.1.1 hc.2.1
      change (interiorDispatch base (component :: rest)).eval memory _ = _ at heval
      rw [heval]
      cases ho : storedInteriorSpan regs (regs (base + 1)) component with
      | none =>
          have hf : child.final.regs (base + 2) = 0 := by simpa [ho, spanPresence] using hc.1.2.1
          rw [if_pos hf, data_eq_running _ hs]
          have ht := ih child.final.regs
          rw [hidx, storedInteriorFind_frame base (regs (base + 1)) hb rest regs child.final.regs hc.2.2] at ht
          refine ⟨?_, ht.2.1, ht.2.2.trans hc.2.2⟩
          simpa [List.findSome?_cons, ho] using ht.1
      | some span =>
          have hf : child.final.regs (base + 2) ≠ 0 := by
            have hflag : child.final.regs (base + 2) = 1 := by
              simpa only [ho, spanPresence] using hc.1.2.1
            rw [hflag]
            decide
          rw [if_neg hf, eval_skip]
          refine ⟨?_, rfl, hc.2.2⟩
          simpa [List.findSome?_cons, ho] using hc.1

def segmentTestBlock (base segment : Nat) : Block :=
  .seq (.action (.constant (base + 5) segment))
    (.action (.comparison .eq (base + 6) base (base + 5)))

theorem segmentTestBlock_eval (base segment : Nat) (memory : Memory) (regs : Registers) :
    (segmentTestBlock base segment).eval memory ⟨regs, .running⟩ =
      ⟨⟨(regs.write (base + 5) segment).write (base + 6)
        (Comparison.eq.eval (regs base) segment), .running⟩, []⟩ := by
  simp [segmentTestBlock, Block.eval, Action.eval, Action.instruction, execute,
    State.writeNext, Data.ofState, Registers.write]

theorem segmentTestBlock_frame (base segment : Nat) (memory : Memory) (regs : Registers) :
    LocateFrame base regs ((segmentTestBlock base segment).eval memory ⟨regs, .running⟩).final.regs := by
  intro r hr
  rw [segmentTestBlock_eval]
  have h5 : r ≠ base + 5 := by omega
  have h6 : r ≠ base + 6 := by omega
  simp [Registers.write, h5, h6]

private theorem segmentTestBlock_branch (base segment : Nat) (zero nonzero : Block)
    (memory : Memory) (regs : Registers) :
    (Block.seq (segmentTestBlock base segment) (.ifZero (base + 6) zero nonzero)).eval memory
        ⟨regs, .running⟩ =
      let tested := (regs.write (base + 5) segment).write (base + 6)
        (Comparison.eq.eval (regs base) segment)
      if regs base = segment then nonzero.eval memory ⟨tested, .running⟩
      else zero.eval memory ⟨tested, .running⟩ := by
  rw [seq_ifZero_noReads memory _ _ _ _ _
    (by rw [segmentTestBlock_eval]) (by rw [segmentTestBlock_eval])]
  rw [segmentTestBlock_eval]
  dsimp only
  rw [Registers.write_same]
  by_cases heq : regs base = segment <;>
    simp only [Comparison.eval, heq, if_true, if_false, Nat.one_ne_zero]

def regularDispatch (base : Nat) : List Nat → Block
  | [] => absentLocationBlock base
  | segment :: rest => .seq (segmentTestBlock base segment)
      (.ifZero (base + 6) (regularDispatch base rest) (regularCaseBlock base segment))

def regularDispatchSpec (regs : Registers) (segment index : Nat) : List Nat → Option NumericSpan
  | [] => none
  | head :: rest => if segment = head then storedRegularSpan regs head index
      else regularDispatchSpec regs segment index rest

theorem regularDispatchSpec_eq (regs : Registers) (segment index : Nat) (segments : List Nat) :
    regularDispatchSpec regs segment index segments =
      if segment ∈ segments then storedRegularSpan regs segment index else none := by
  induction segments with
  | nil => simp [regularDispatchSpec]
  | cons head rest ih =>
      by_cases hh : segment = head
      · subst head; simp [regularDispatchSpec]
      · simp [regularDispatchSpec, hh, ih]

theorem regularDispatchSpec_frame (base segment index : Nat) (hb : 256 ≤ base)
    (segments : List Nat) (hsegments : ∀ s ∈ segments, s < 23)
    (first second : Registers) (hf : LocateFrame base first second) :
    regularDispatchSpec second segment index segments = regularDispatchSpec first segment index segments := by
  induction segments with
  | nil => rfl
  | cons head rest ih =>
      by_cases heq : segment = head
      · simp only [regularDispatchSpec, heq, if_true]
        exact storedRegularSpan_frame base head index hb (hsegments head (by simp)) first second hf
      · simp only [regularDispatchSpec, heq, if_false]
        exact ih (by intro s hs; exact hsegments s (by simp [hs]))

theorem regularDispatch_source (base : Nat) (hb : 256 ≤ base)
    (segments : List Nat) (hsegments : ∀ s ∈ segments, s < 23)
    (memory : Memory) (regs : Registers) :
    let actual := (regularDispatch base segments).eval memory ⟨regs, .running⟩
    LocationResult base (regularDispatchSpec regs (regs base) (regs (base + 1)) segments)
      actual.final ∧ actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  induction segments generalizing regs with
  | nil => exact absentLocationBlock_source base memory regs
  | cons head rest ih =>
      have hhead := hsegments head (by simp)
      have hrest : ∀ s ∈ rest, s < 23 := by intro s hs; exact hsegments s (by simp [hs])
      let tested : Registers := (regs.write (base + 5) head).write (base + 6)
        (Comparison.eq.eval (regs base) head)
      have hframe : LocateFrame base regs tested := by
        simpa only [segmentTestBlock_eval] using segmentTestBlock_frame base head memory regs
      have hinput : tested base = regs base := hframe _ (Or.inl (by omega))
      have hindex : tested (base + 1) = regs (base + 1) := hframe _ (Or.inl (by omega))
      have heval : (regularDispatch base (head :: rest)).eval memory ⟨regs, .running⟩ =
          if regs base = head then (regularCaseBlock base head).eval memory ⟨tested, .running⟩
          else (regularDispatch base rest).eval memory ⟨tested, .running⟩ := by
        exact segmentTestBlock_branch base head _ _ memory regs
      rw [heval]
      by_cases heq : regs base = head
      · rw [if_pos heq]
        have hc := regularCaseBlock_source base head hb hhead memory tested
        rw [hindex, storedRegularSpan_frame base head (regs (base + 1)) hb hhead regs tested hframe] at hc
        exact ⟨by simpa [regularDispatchSpec, heq] using hc.1, hc.2.1, hc.2.2.trans hframe⟩
      · rw [if_neg heq]
        have hc := ih hrest tested
        rw [hinput, hindex, regularDispatchSpec_frame base (regs base) (regs (base + 1)) hb rest hrest regs tested hframe] at hc
        exact ⟨by simpa [regularDispatchSpec, heq] using hc.1, hc.2.1, hc.2.2.trans hframe⟩

def storedLogicalSpan (regs : Registers) (segment index : Nat) : Option NumericSpan :=
  if segment = 20 then interiorComponents.findSome? (storedInteriorSpan regs index)
  else if segment < 23 then storedRegularSpan regs segment index else none

def locateBlock (base : Nat) : Block :=
  .seq (segmentTestBlock base 20)
    (.ifZero (base + 6) (regularDispatch base (List.range 23))
      (interiorDispatch base interiorComponents))

theorem locateBlock_source (base : Nat) (hb : 256 ≤ base) (memory : Memory) (regs : Registers) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    LocationResult base (storedLogicalSpan regs (regs base) (regs (base + 1))) actual.final ∧
      actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  let tested : Registers := (regs.write (base + 5) 20).write (base + 6)
    (Comparison.eq.eval (regs base) 20)
  have hframe : LocateFrame base regs tested := by
    simpa only [segmentTestBlock_eval] using segmentTestBlock_frame base 20 memory regs
  have hinput : tested base = regs base := hframe _ (Or.inl (by omega))
  have hindex : tested (base + 1) = regs (base + 1) := hframe _ (Or.inl (by omega))
  have heval : (locateBlock base).eval memory ⟨regs, .running⟩ =
      if regs base = 20 then (interiorDispatch base interiorComponents).eval memory ⟨tested, .running⟩
      else (regularDispatch base (List.range 23)).eval memory ⟨tested, .running⟩ := by
    exact segmentTestBlock_branch base 20 _ _ memory regs
  rw [heval]
  by_cases heq : regs base = 20
  · rw [if_pos heq]
    have h := interiorDispatch_source base hb interiorComponents memory tested
    rw [hindex, storedInteriorFind_frame base (regs (base + 1)) hb interiorComponents regs tested hframe] at h
    exact ⟨by simpa [storedLogicalSpan, heq] using h.1, h.2.1, h.2.2.trans hframe⟩
  · rw [if_neg heq]
    have hs : ∀ s ∈ List.range 23, s < 23 := by intro s hs; exact List.mem_range.mp hs
    have h := regularDispatch_source base hb (List.range 23) hs memory tested
    rw [hinput, hindex, regularDispatchSpec_frame base (regs base) (regs (base + 1)) hb
      (List.range 23) hs regs tested hframe, regularDispatchSpec_eq] at h
    exact ⟨by simpa [storedLogicalSpan, heq] using h.1, h.2.1, h.2.2.trans hframe⟩

@[simp] theorem regularCaseBlock_size (base segment : Nat) :
    (regularCaseBlock base segment).size = 27 := by
  simp [regularCaseBlock, Block.size, copyInputsFrom_size, regularCaseInputs,
    exportSpanBlock, Block.sequence]

@[simp] theorem interiorCaseBlock_size (base : Nat)
    (component : PackedReviewerInteriorComponentTag) :
    (interiorCaseBlock base component).size = 37 := by
  simp [interiorCaseBlock, Block.size, copyInputsFrom_size, interiorCaseInputs,
    exportSpanBlock, Block.sequence]

@[simp] theorem regularDispatch_size (base : Nat) (segments : List Nat) :
    (regularDispatch base segments).size = 31 * segments.length + 3 := by
  induction segments with
  | nil => rfl
  | cons head rest ih =>
      simp only [regularDispatch, Block.size, segmentTestBlock, regularCaseBlock_size,
        ih, List.length_cons]
      omega

@[simp] theorem interiorDispatch_size (base : Nat)
    (components : List PackedReviewerInteriorComponentTag) :
    (interiorDispatch base components).size = 39 * components.length + 3 := by
  induction components with
  | nil => rfl
  | cons head rest ih =>
      simp only [interiorDispatch, Block.size, interiorCaseBlock_size, ih, List.length_cons]
      omega

@[simp] theorem locateBlock_size (base : Nat) : (locateBlock base).size = 1035 := by
  simp [locateBlock, Block.size, segmentTestBlock, interiorComponents]

/-- Agreement is a refinement hypothesis about registers populated by setup. -/
def MetadataRegistersAgree (shape : CartesianShape) (regs : Registers) : Prop :=
  ∀ i < 174, regs (16 + i) = (metadata shape)[i]?.getD 0

private theorem fixedMap_flatten_get {α : Type} (xs : List α) (f : α → List Nat)
    (count : Nat) (hlen : ∀ x ∈ xs, (f x).length = count)
    (i : Nat) (x : α) (hx : xs[i]? = some x) (j : Nat) (hj : j < count) :
    (xs.map f).flatten[count * i + j]? = (f x)[j]? := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons head rest ih =>
      have hh := hlen head (by simp)
      have ht : ∀ x ∈ rest, (f x).length = count := by
        intro x hx; exact hlen x (by simp [hx])
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst head
          simp only [List.map_cons, List.flatten_cons, Nat.mul_zero, Nat.zero_add]
          exact List.getElem?_append_left (by omega)
      | succ i =>
          simp only [List.getElem?_cons_succ] at hx
          simp only [List.map_cons, List.flatten_cons, Nat.mul_add, Nat.mul_one]
          rw [List.getElem?_append_right (by omega)]
          rw [hh]
          have heq : count * i + count + j - count = count * i + j := by omega
          rw [heq]
          exact ih ht i hx

theorem metadata_regular_field (shape : CartesianShape) (segment j : Nat)
    (hsegment : segment < 23) (hj : j < 4) :
    (metadata shape)[42 + 4 * segment + j]? =
      (regularDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape) segment)[j]? := by
  let f := regularDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape)
  have hlen : ∀ s ∈ List.range 23, (f s).length = 4 := by
    intro s _; exact regularDescriptor_length ..
  have hflat := fixedMap_flatten_length (List.range 23) f 4 hlen
  have hget := fixedMap_flatten_get (List.range 23) f 4 hlen segment segment
    (by simp [hsegment]) j hj
  unfold metadata
  rw [List.append_assoc, List.getElem?_append_right (by simp; omega)]
  rw [scalarMetadata_length]
  have heq : 42 + 4 * segment + j - 42 = 4 * segment + j := by omega
  rw [heq, List.getElem?_append_left (by simpa only [hflat, List.length_range] using (by omega : 4 * segment + j < 23 * 4))]
  exact hget

theorem metadata_interior_field (shape : CartesianShape)
    (component : PackedReviewerInteriorComponentTag) (j : Nat) (hj : j < 5) :
    (metadata shape)[134 + 5 * interiorComponentIndex component + j]? =
      (interiorDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape) component)[j]? := by
  let f := interiorDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape)
  have hlen : ∀ c ∈ interiorComponents, (f c).length = 5 := by intro c _; rfl
  have hc := interiorComponentIndex_lt component
  have hindex : interiorComponents[interiorComponentIndex component]? = some component := by
    cases component <;> rfl
  have hget := fixedMap_flatten_get interiorComponents f 5 hlen _ component hindex j hj
  have hregular := fixedMap_flatten_length (List.range 23)
    (regularDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape)) 4
    (by intro s _; exact regularDescriptor_length ..)
  unfold metadata
  rw [List.getElem?_append_right (by
    simp only [List.length_append, scalarMetadata_length, hregular, List.length_range]
    omega)]
  simp only [List.length_append, scalarMetadata_length, hregular, List.length_range]
  have heq : 134 + 5 * interiorComponentIndex component + j - (42 + 23 * 4) =
      5 * interiorComponentIndex component + j := by omega
  rw [heq]
  exact hget

theorem metadata_bpWidth_field (shape : CartesianShape) :
    (metadata shape)[16]? = some (packedBpCodeWordWidth shape.size) := by
  unfold metadata
  rw [List.append_assoc, List.getElem?_append_left (by rw [scalarMetadata_length]; decide)]
  rfl

theorem storedRegularSpan_canonical (shape : CartesianShape) (regs : Registers)
    (hmeta : MetadataRegistersAgree shape regs) (segment index : Nat) (hsegment : segment < 23) :
    storedRegularSpan regs segment index =
      regularDescriptorSpan shape.size (longCount shape) (packedReviewerSparseCount shape) segment index := by
  have hfield (j : Nat) (hj : j < 4) : regs (58 + 4 * segment + j) =
      (regularDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape) segment)[j]?.getD 0 := by
    have hm := hmeta (42 + 4 * segment + j) (by omega)
    rw [metadata_regular_field shape segment j hsegment hj] at hm
    have heq : 16 + (42 + 4 * segment + j) = 58 + 4 * segment + j := by omega
    simpa only [heq] using hm
  unfold storedRegularSpan regularDescriptorSpan
  rw [show 58 + 4 * segment = 58 + 4 * segment + 0 by omega,
    hfield 0 (by decide), hfield 1 (by decide), hfield 2 (by decide), hfield 3 (by decide)]

theorem storedInteriorSpan_canonical (shape : CartesianShape) (regs : Registers)
    (hmeta : MetadataRegistersAgree shape regs) (index : Nat)
    (component : PackedReviewerInteriorComponentTag) :
    storedInteriorSpan regs index component =
      interiorDescriptorSpan shape.size (longCount shape) (packedReviewerSparseCount shape) index component := by
  have hc := interiorComponentIndex_lt component
  have hfield (j : Nat) (hj : j < 5) : regs (150 + 5 * interiorComponentIndex component + j) =
      (interiorDescriptor shape.size (longCount shape) (packedReviewerSparseCount shape) component)[j]?.getD 0 := by
    have hm := hmeta (134 + 5 * interiorComponentIndex component + j) (by omega)
    rw [metadata_interior_field shape component j hj] at hm
    have heq : 16 + (134 + 5 * interiorComponentIndex component + j) =
        150 + 5 * interiorComponentIndex component + j := by omega
    simpa only [heq] using hm
  have hbp : regs 32 = packedBpCodeWordWidth shape.size := by
    have hm := hmeta 16 (by decide)
    rw [metadata_bpWidth_field] at hm
    exact hm
  dsimp only [storedInteriorSpan, interiorDescriptorSpan]
  rw [show 150 + 5 * interiorComponentIndex component =
      150 + 5 * interiorComponentIndex component + 0 by omega,
    hfield 0 (by decide), hfield 1 (by decide), hfield 2 (by decide),
    hfield 3 (by decide), hfield 4 (by decide), hbp]

theorem storedLogicalSpan_canonical (shape : CartesianShape) (regs : Registers)
    (hmeta : MetadataRegistersAgree shape regs) (segment index : Nat) :
    storedLogicalSpan regs segment index =
      reviewerLogicalSpan shape.size (longCount shape) (packedReviewerSparseCount shape) segment index := by
  by_cases h20 : segment = 20
  · subst segment
    rw [storedLogicalSpan, if_pos rfl, reviewerLogicalSpan_interior_descriptors]
    congr 1
    funext component
    exact storedInteriorSpan_canonical shape regs hmeta index component
  · rw [storedLogicalSpan, if_neg h20]
    by_cases hs : segment < 23
    · rw [if_pos hs, reviewerLogicalSpan_regular _ _ _ _ _ hs h20]
      exact storedRegularSpan_canonical shape regs hmeta segment index hs
    · rw [if_neg hs, reviewerLogicalSpan_outside _ _ _ _ _ (by omega)]

theorem locateBlock_canonical (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (memory : Memory) (regs : Registers) (hmeta : MetadataRegistersAgree shape regs) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    LocationResult base (reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) (regs base) (regs (base + 1))) actual.final ∧
      actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  have h := locateBlock_source base hb memory regs
  rw [storedLogicalSpan_canonical shape regs hmeta] at h
  exact h

theorem regularLocateBlock_fieldsFit (base width : Nat) (hbound : base + 11 < 2 ^ width) :
    (regularLocateBlock base).FieldsFit width := by
  have hw : width ≠ 0 := by intro h; simp [h] at hbound
  simp [regularLocateBlock, Block.sequence, Block.FieldsFit, natSubBlock, minBlock,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, Comparison.code, hw]
  omega

theorem interiorLocateBlock_fieldsFit (base width : Nat) (hbound : base + 17 < 2 ^ width) :
    (interiorLocateBlock base).FieldsFit width := by
  have hw : width ≠ 0 := by intro h; simp [h] at hbound
  simp [interiorLocateBlock, Block.sequence, Block.FieldsFit, natSubBlock, minBlock,
    Action.instruction, Instruction.Fits, Instruction.encoding, Instruction.operands,
    Arithmetic.code, Comparison.code, hw]
  omega

private theorem copyInputsFrom_fieldsFit (destination : Nat) (sources : List Nat)
    (width : Nat) (hbound : destination + sources.length + 3 < 2 ^ width)
    (hsources : ∀ r ∈ sources, r < 2 ^ width) :
    (copyInputsFrom destination sources).FieldsFit width := by
  induction sources generalizing destination with
  | nil => trivial
  | cons head rest ih =>
      refine ⟨?_, ih (destination + 1) (by simp only [List.length_cons] at hbound; omega)
        (by intro r hr; exact hsources r (by simp [hr]))⟩
      have hh := hsources head (by simp)
      simp [Block.FieldsFit, Action.instruction, Instruction.Fits, Instruction.encoding,
        Instruction.operands]
      omega

private theorem exportSpanBlock_fieldsFit (base offset width : Nat)
    (hoffset : 7 ≤ offset) (hbound : base + offset + 3 < 2 ^ width) :
    (exportSpanBlock base offset).FieldsFit width := by
  simp [exportSpanBlock, Block.sequence, Block.FieldsFit, Action.instruction,
    Instruction.Fits, Instruction.encoding, Instruction.operands]
  omega

private theorem regularCaseBlock_fieldsFit (base segment width : Nat)
    (hb : 256 ≤ base) (hs : segment < 23) (hbound : base + 49 < 2 ^ width) :
    (regularCaseBlock base segment).FieldsFit width := by
  refine ⟨copyInputsFrom_fieldsFit _ _ width ?_ ?_,
    regularLocateBlock_fieldsFit (base + 32) width (by omega),
    exportSpanBlock_fieldsFit base 37 width (by decide) (by omega)⟩
  · simp only [regularCaseInputs, List.length_cons, List.length_nil]; omega
  · intro r hr
    simp only [regularCaseInputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    omega

private theorem interiorCaseBlock_fieldsFit (base width : Nat)
    (hb : 256 ≤ base) (component : PackedReviewerInteriorComponentTag)
    (hbound : base + 49 < 2 ^ width) :
    (interiorCaseBlock base component).FieldsFit width := by
  have hc := interiorComponentIndex_lt component
  refine ⟨copyInputsFrom_fieldsFit _ _ width ?_ ?_,
    interiorLocateBlock_fieldsFit (base + 32) width (by omega),
    exportSpanBlock_fieldsFit base 39 width (by decide) (by omega)⟩
  · simp only [interiorCaseInputs, List.length_cons, List.length_nil]; omega
  · intro r hr
    simp only [interiorCaseInputs, List.mem_cons, List.not_mem_nil, or_false] at hr
    omega

private theorem absentLocationBlock_fieldsFit (base width : Nat)
    (hbound : base + 49 < 2 ^ width) : (absentLocationBlock base).FieldsFit width := by
  have hw : width ≠ 0 := by intro h; simp [h] at hbound
  simp [absentLocationBlock, Block.sequence, Block.FieldsFit, Action.instruction,
    Instruction.Fits, Instruction.encoding, Instruction.operands, hw]
  omega

private theorem segmentTestBlock_fieldsFit (base segment width : Nat)
    (hb : 256 ≤ base) (hs : segment < 23) (hbound : base + 49 < 2 ^ width) :
    (segmentTestBlock base segment).FieldsFit width := by
  have hw : width ≠ 0 := by intro h; simp [h] at hbound
  simp [segmentTestBlock, Block.FieldsFit, Action.instruction,
    Instruction.Fits, Instruction.encoding, Instruction.operands, Comparison.code, hw]
  omega

private theorem branchFieldsFit (base width offset : Nat) (hoffset : offset ≤ 48)
    (hbound : base + 49 < 2 ^ width) :
    (Instruction.branchZero (base + offset) 0).Fits width ∧ (Instruction.jump 0).Fits width := by
  simp [Instruction.Fits, Instruction.encoding, Instruction.operands]
  omega

private theorem regularDispatch_fieldsFit (base width : Nat) (segments : List Nat)
    (hb : 256 ≤ base) (hs : ∀ segment ∈ segments, segment < 23)
    (hbound : base + 49 < 2 ^ width) : (regularDispatch base segments).FieldsFit width := by
  induction segments with
  | nil => exact absentLocationBlock_fieldsFit base width hbound
  | cons head rest ih =>
      have hh := hs head (by simp)
      have hbranch := branchFieldsFit base width 6 (by decide) hbound
      exact ⟨segmentTestBlock_fieldsFit base head width hb hh hbound,
        hbranch.1, hbranch.2, ih (by intro s hs'; exact hs s (by simp [hs'])),
        regularCaseBlock_fieldsFit base head width hb hh hbound⟩

private theorem interiorDispatch_fieldsFit (base width : Nat)
    (components : List PackedReviewerInteriorComponentTag)
    (hb : 256 ≤ base) (hbound : base + 49 < 2 ^ width) :
    (interiorDispatch base components).FieldsFit width := by
  induction components with
  | nil => exact absentLocationBlock_fieldsFit base width hbound
  | cons head rest ih =>
      have hbranch := branchFieldsFit base width 2 (by decide) hbound
      exact ⟨interiorCaseBlock_fieldsFit base width hb head hbound,
        hbranch.1, hbranch.2, ih, trivial⟩

/-- Every source operand, including inactive branches, fits from one concrete bound. -/
theorem locateBlock_fieldsFit (base width : Nat) (hb : 256 ≤ base)
    (hbound : base + 49 < 2 ^ width) : (locateBlock base).FieldsFit width := by
  have hbranch := branchFieldsFit base width 6 (by decide) hbound
  exact ⟨segmentTestBlock_fieldsFit base 20 width hb (by decide) hbound,
    hbranch.1, hbranch.2,
    regularDispatch_fieldsFit base width (List.range 23) hb (by simp) hbound,
    interiorDispatch_fieldsFit base width interiorComponents hb hbound⟩

theorem locateBlock_compiled_fieldsFit (base codeBase width : Nat) (hb : 256 ≤ base)
    (hregisters : base + 49 < 2 ^ width) (hcode : codeBase + 1035 < 2 ^ width) :
    ∀ instruction ∈ (locateBlock base).compileAt codeBase, instruction.Fits width :=
  (locateBlock base).compile_fits width codeBase (locateBlock_fieldsFit base width hb hregisters)
    (by simpa only [locateBlock_size] using hcode)

theorem locateBlock_run (base : Nat) (hb : 256 ≤ base) (memory : Memory)
    (s : State) (hpc : s.pc = 0) (hs : s.status = .running) :
    let actual := run memory ((locateBlock base).compileAt 0) 1035 s
    LocationResult base (storedLogicalSpan s.regs (s.regs base) (s.regs (base + 1)))
      (Data.ofState actual.final) ∧ actual.reads = [] ∧
      LocateFrame base s.regs actual.final.regs ∧ actual.steps ≤ 1035 ∧ actual.final.pc = 1035 := by
  have h := (locateBlock base).compile_run memory s hpc
  rw [locateBlock_size] at h
  have hd : Data.ofState s = ⟨s.regs, .running⟩ := by cases s; simp_all [Data.ofState]
  have he := locateBlock_source base hb memory s.regs
  rw [hd] at h
  have hr : LocationResult base (storedLogicalSpan s.regs (s.regs base) (s.regs (base + 1)))
      (Data.ofState (run memory ((locateBlock base).compileAt 0) 1035 s).final) := by
    rw [h.1]; exact he.1
  refine ⟨hr, h.2.1.trans he.2.1, ?_, h.2.2.1, h.2.2.2 hr.1⟩
  change LocateFrame base s.regs (Data.ofState _).regs
  rw [h.1]
  exact he.2.2

theorem locateBlock_hosted_run (base codeBase : Nat) (hb : 256 ≤ base)
    (memory : Memory) (program : Program) (s : State)
    (hpc : s.pc = codeBase) (hs : s.status = .running)
    (host : HostedAt program codeBase ((locateBlock base).compileAt codeBase)) :
    ∃ used, used ≤ 1035 ∧
      let actual := run memory program used s
      LocationResult base (storedLogicalSpan s.regs (s.regs base) (s.regs (base + 1)))
        (Data.ofState actual.final) ∧ actual.reads = [] ∧
        LocateFrame base s.regs actual.final.regs ∧ actual.steps = used ∧
        actual.final.pc = codeBase + 1035 := by
  obtain ⟨used, hu, hd, hr, hc, hp⟩ :=
    (locateBlock base).compile_correct memory program codeBase s hpc host
  rw [locateBlock_size] at hu hp
  have hdata : Data.ofState s = ⟨s.regs, .running⟩ := by cases s; simp_all [Data.ofState]
  rw [hdata] at hd hr
  have he := locateBlock_source base hb memory s.regs
  have hresult : LocationResult base (storedLogicalSpan s.regs (s.regs base) (s.regs (base + 1)))
      (Data.ofState (run memory program used s).final) := by rw [hd]; exact he.1
  refine ⟨used, hu, hresult, hr.trans he.2.1, ?_, hc, hp hresult.1⟩
  change LocateFrame base s.regs (Data.ofState _).regs
  rw [hd]
  exact he.2.2

theorem locateBlock_canonical_run (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (memory : Memory) (s : State) (hpc : s.pc = 0) (hs : s.status = .running)
    (hmeta : MetadataRegistersAgree shape s.regs) :
    let actual := run memory ((locateBlock base).compileAt 0) 1035 s
    LocationResult base (reviewerLogicalSpan shape.size (longCount shape)
      (packedReviewerSparseCount shape) (s.regs base) (s.regs (base + 1)))
      (Data.ofState actual.final) ∧ actual.reads = [] ∧
      LocateFrame base s.regs actual.final.regs ∧ actual.steps ≤ 1035 ∧ actual.final.pc = 1035 := by
  have h := locateBlock_run base hb memory s hpc hs
  rw [storedLogicalSpan_canonical shape s.regs hmeta] at h
  exact h

theorem locateBlock_canonical_hosted_run (base codeBase : Nat) (hb : 256 ≤ base)
    (shape : CartesianShape) (memory : Memory) (program : Program) (s : State)
    (hpc : s.pc = codeBase) (hs : s.status = .running)
    (hmeta : MetadataRegistersAgree shape s.regs)
    (host : HostedAt program codeBase ((locateBlock base).compileAt codeBase)) :
    ∃ used, used ≤ 1035 ∧
      let actual := run memory program used s
      LocationResult base (reviewerLogicalSpan shape.size (longCount shape)
        (packedReviewerSparseCount shape) (s.regs base) (s.regs (base + 1)))
        (Data.ofState actual.final) ∧ actual.reads = [] ∧
        LocateFrame base s.regs actual.final.regs ∧ actual.steps = used ∧
        actual.final.pc = codeBase + 1035 := by
  have h := locateBlock_hosted_run base codeBase hb memory program s hpc hs host
  rw [storedLogicalSpan_canonical shape s.regs hmeta] at h
  exact h

/-- This composition obtains the bank from the concrete allocation by charged loads. -/
def setupLocateBlock (base : Nat) : Block := .seq metadataSetupBlock (locateBlock base)

@[simp] theorem setupLocateBlock_size (base : Nat) : (setupLocateBlock base).size = 1383 := by
  simp [setupLocateBlock, Block.size, metadataSetupBlock_size]

theorem buildMemory_setup_locate (xs : List Int) (base : Nat) (hb : 256 ≤ base)
    (regs : Registers) :
    let actual := (setupLocateBlock base).eval (buildMemory xs) ⟨regs, .running⟩
    LocationResult base (reviewerLogicalSpan xs.length
      (longCount (SuccinctClassic.cartesianShape xs))
      (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs))
      (regs base) (regs (base + 1))) actual.final ∧
      actual.reads = (List.range 174).map
        (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ∧
      MetadataRegistersAgree (SuccinctClassic.cartesianShape xs) actual.final.regs := by
  rw [setupLocateBlock, Block.eval_seq]
  generalize hprepared : metadataSetupBlock.eval (buildMemory xs) ⟨regs, .running⟩ = prepared
  have hp := buildMemory_setup xs ⟨regs, .running⟩ rfl
  rw [hprepared] at hp
  have hmeta : MetadataRegistersAgree (SuccinctClassic.cartesianShape xs) prepared.final.regs := hp.2.1
  have hs : prepared.final.status = .running := hp.1
  have hsegment : prepared.final.regs base = regs base := hp.2.2.2.1 base (by omega) (Or.inr (by omega))
  have hindex : prepared.final.regs (base + 1) = regs (base + 1) :=
    hp.2.2.2.1 (base + 1) (by omega) (Or.inr (by omega))
  have hl := locateBlock_canonical base hb (SuccinctClassic.cartesianShape xs)
    (buildMemory xs) prepared.final.regs hmeta
  have hsize := packedReviewerCartesianShape_size xs
  have hvalue := hl.1
  rw [hsize, hsegment, hindex] at hvalue
  change LocationResult base _ (Evaluation.bind prepared _).final ∧
    (Evaluation.bind prepared _).reads = _ ∧
    MetadataRegistersAgree _ (Evaluation.bind prepared _).final.regs
  unfold Evaluation.bind
  rw [data_eq_running _ hs]
  simp only [hl.2.1, List.append_nil]
  refine ⟨hvalue, hp.2.2.2.2, ?_⟩
  intro i hi
  rw [hl.2.2 (16 + i) (Or.inl (by omega))]
  exact hmeta i hi

theorem buildMemory_setup_locate_run (xs : List Int) (base : Nat) (hb : 256 ≤ base)
    (s : State) (hpc : s.pc = 0) (hs : s.status = .running) :
    let actual := run (buildMemory xs) ((setupLocateBlock base).compileAt 0) 1383 s
    LocationResult base (reviewerLogicalSpan xs.length
      (longCount (SuccinctClassic.cartesianShape xs))
      (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs))
      (s.regs base) (s.regs (base + 1))) (Data.ofState actual.final) ∧
      actual.reads = (List.range 174).map
        (fun i => ⟨i, (metadata (SuccinctClassic.cartesianShape xs))[i]?⟩) ∧
      MetadataRegistersAgree (SuccinctClassic.cartesianShape xs) actual.final.regs ∧
      actual.steps ≤ 1383 ∧ actual.final.pc = 1383 := by
  have h := (setupLocateBlock base).compile_run (buildMemory xs) s hpc
  rw [setupLocateBlock_size] at h
  have hdata : Data.ofState s = ⟨s.regs, .running⟩ := by cases s; simp_all [Data.ofState]
  rw [hdata] at h
  have he := buildMemory_setup_locate xs base hb s.regs
  have hresult : LocationResult base (reviewerLogicalSpan xs.length
      (longCount (SuccinctClassic.cartesianShape xs))
      (packedReviewerSparseCount (SuccinctClassic.cartesianShape xs))
      (s.regs base) (s.regs (base + 1)))
      (Data.ofState (run (buildMemory xs) ((setupLocateBlock base).compileAt 0) 1383 s).final) := by
    rw [h.1]; exact he.1
  refine ⟨hresult, h.2.1.trans he.2.1, ?_, h.2.2.1, h.2.2.2 hresult.1⟩
  change MetadataRegistersAgree _ (Data.ofState _).regs
  rw [h.1]
  exact he.2.2

/-- Independent exact-type source consumer, retaining every quantified canonical case. -/
theorem locate_canonical_requiredFacts (base : Nat) (hb : 256 ≤ base) (shape : CartesianShape)
    (memory : Memory) (regs : Registers) (hmeta : MetadataRegistersAgree shape regs) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧
      actual.final.regs (base + 2) = spanPresence (reviewerLogicalSpan shape.size
        (longCount shape) (packedReviewerSparseCount shape) (regs base) (regs (base + 1))) ∧
      actual.final.regs (base + 3) = spanPosition (reviewerLogicalSpan shape.size
        (longCount shape) (packedReviewerSparseCount shape) (regs base) (regs (base + 1))) ∧
      actual.final.regs (base + 4) = spanLength (reviewerLogicalSpan shape.size
        (longCount shape) (packedReviewerSparseCount shape) (regs base) (regs (base + 1))) ∧
      actual.reads = [] ∧
      (∀ r, r < base + 2 ∨ base + 49 ≤ r → actual.final.regs r = regs r) := by
  have h := locateBlock_canonical base hb shape memory regs hmeta
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.1, h.2.2⟩

theorem locate_non20_requiredFacts (base : Nat) (hb : 256 ≤ base)
    (memory : Memory) (regs : Registers) (hsegment : regs base < 23) (h20 : regs base ≠ 20) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    LocationResult base (regularSpan (regs (base + 1)) (regs (58 + 4 * regs base))
      (regs (58 + 4 * regs base + 1)) (regs (58 + 4 * regs base + 2))
      (regs (58 + 4 * regs base + 3))) actual.final ∧
      actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  simpa only [storedLogicalSpan, if_neg h20, if_pos hsegment, storedRegularSpan] using
    locateBlock_source base hb memory regs

theorem locate_interior_requiredFacts (base : Nat) (hb : 256 ≤ base)
    (memory : Memory) (regs : Registers) (hsegment : regs base = 20) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    LocationResult base (interiorComponents.findSome? (storedInteriorSpan regs (regs (base + 1))))
      actual.final ∧ actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  simpa only [storedLogicalSpan, hsegment, if_true] using locateBlock_source base hb memory regs

theorem locate_invalid_requiredFacts (base : Nat) (hb : 256 ≤ base)
    (memory : Memory) (regs : Registers) (hsegment : 23 ≤ regs base) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    LocationResult base none actual.final ∧ actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  simpa only [storedLogicalSpan, if_neg (show regs base ≠ 20 by omega),
    if_neg (show ¬regs base < 23 by omega)] using locateBlock_source base hb memory regs

theorem locate_invalid_index_requiredFacts (base : Nat) (hb : 256 ≤ base)
    (memory : Memory) (regs : Registers) (hsegment : regs base < 23) (h20 : regs base ≠ 20)
    (hindex : regs (58 + 4 * regs base + 3) ≤ regs (base + 1)) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    LocationResult base none actual.final ∧ actual.reads = [] ∧ LocateFrame base regs actual.final.regs := by
  simpa only [regularSpan, if_neg (Nat.not_lt.mpr hindex)] using
    locate_non20_requiredFacts base hb memory regs hsegment h20

/-- Positive stored count keeps a zero-bit sentinel present. -/
theorem locate_empty_sentinel_requiredFacts (base : Nat) (hb : 256 ≤ base)
    (memory : Memory) (regs : Registers) (hsegment : regs base < 23) (h20 : regs base ≠ 20)
    (hindex : regs (base + 1) = 0) (hcount : 0 < regs (58 + 4 * regs base + 3))
    (hbits : regs (58 + 4 * regs base + 1) = 0) :
    let actual := (locateBlock base).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs (base + 2) = 1 ∧
      actual.final.regs (base + 3) = regs (58 + 4 * regs base) ∧
      actual.final.regs (base + 4) = 0 ∧ actual.reads = [] ∧
      LocateFrame base regs actual.final.regs := by
  have h := locate_non20_requiredFacts base hb memory regs hsegment h20
  simpa [regularSpan, hindex, hcount, hbits, LocationResult, spanPresence, spanPosition,
    spanLength] using And.intro h.1.1 (And.intro h.1.2.1
      (And.intro h.1.2.2.1 (And.intro h.1.2.2.2 h.2)))

/-- Returned position depends on the stored bit-base field, not merely on receipts. -/
theorem locate_run_position_dependency (base : Nat) (hb : 256 ≤ base) (memory : Memory)
    (first second : State) (hpc1 : first.pc = 0) (hpc2 : second.pc = 0)
    (hs1 : first.status = .running) (hs2 : second.status = .running)
    (hseg1 : first.regs base < 23) (hseg2 : second.regs base < 23)
    (h20a : first.regs base ≠ 20) (h20b : second.regs base ≠ 20)
    (hi1 : first.regs (base + 1) = 0) (hi2 : second.regs (base + 1) = 0)
    (hc1 : 0 < first.regs (58 + 4 * first.regs base + 3))
    (hc2 : 0 < second.regs (58 + 4 * second.regs base + 3))
    (hbase : first.regs (58 + 4 * first.regs base) ≠ second.regs (58 + 4 * second.regs base)) :
    (run memory ((locateBlock base).compileAt 0) 1035 first).final.regs (base + 3) ≠
      (run memory ((locateBlock base).compileAt 0) 1035 second).final.regs (base + 3) := by
  have h1 := (locateBlock_run base hb memory first hpc1 hs1).1.2.2.1
  have h2 := (locateBlock_run base hb memory second hpc2 hs2).1.2.2.1
  simp only [storedLogicalSpan, if_neg h20a, if_neg h20b, if_pos hseg1, if_pos hseg2,
    storedRegularSpan, regularSpan, hi1, hi2, hc1, hc2, if_true, Nat.zero_mul,
    Nat.add_zero, spanPosition, Option.map_some, Option.getD_some, Data.ofState] at h1 h2
  rw [h1, h2]
  exact hbase

private theorem copyInputsFrom_writesOnly (base destination : Nat) (sources : List Nat)
    (hlower : base + 2 ≤ destination) (hupper : destination + sources.length ≤ base + 49) :
    (copyInputsFrom destination sources).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  induction sources generalizing destination with
  | nil => trivial
  | cons head rest ih =>
      refine ⟨?_, ih (destination + 1) (by omega) (by simp only [List.length_cons] at hupper; omega)⟩
      change base + 2 ≤ destination ∧ destination < base + 49
      simp only [List.length_cons] at hupper
      omega

private theorem exportSpanBlock_writesOnly (base offset : Nat) :
    (exportSpanBlock base offset).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  simp [exportSpanBlock, Block.sequence, Block.WritesOnly, Action.destination]

private theorem regularCaseBlock_writesOnly (base segment : Nat) :
    (regularCaseBlock base segment).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  refine ⟨copyInputsFrom_writesOnly base (base + 32) _ (by omega) (by simp [regularCaseInputs]),
    ?_, exportSpanBlock_writesOnly base 37⟩
  simp [regularLocateBlock, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]

private theorem interiorCaseBlock_writesOnly (base : Nat) (component : PackedReviewerInteriorComponentTag) :
    (interiorCaseBlock base component).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  refine ⟨copyInputsFrom_writesOnly base (base + 32) _ (by omega) (by simp [interiorCaseInputs]),
    ?_, exportSpanBlock_writesOnly base 39⟩
  simp [interiorLocateBlock, Block.sequence, Block.WritesOnly, Action.destination, natSubBlock, minBlock]

private theorem absentLocationBlock_writesOnly (base : Nat) :
    (absentLocationBlock base).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  simp [absentLocationBlock, Block.sequence, Block.WritesOnly, Action.destination]

private theorem segmentTestBlock_writesOnly (base segment : Nat) :
    (segmentTestBlock base segment).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  simp [segmentTestBlock, Block.WritesOnly, Action.destination]

private theorem regularDispatch_writesOnly (base : Nat) (segments : List Nat) :
    (regularDispatch base segments).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  induction segments with
  | nil => exact absentLocationBlock_writesOnly base
  | cons head rest ih => exact ⟨segmentTestBlock_writesOnly base head, ih, regularCaseBlock_writesOnly base head⟩

private theorem interiorDispatch_writesOnly (base : Nat) (components : List PackedReviewerInteriorComponentTag) :
    (interiorDispatch base components).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) := by
  induction components with
  | nil => exact absentLocationBlock_writesOnly base
  | cons head rest ih => exact ⟨interiorCaseBlock_writesOnly base head, ih, trivial⟩

/-- Syntactic inventory applies to every dormant branch and every initial status. -/
theorem locateBlock_writesOnly (base : Nat) :
    (locateBlock base).WritesOnly (fun r => base + 2 ≤ r ∧ r < base + 49) :=
  ⟨segmentTestBlock_writesOnly base 20, regularDispatch_writesOnly base (List.range 23),
    interiorDispatch_writesOnly base interiorComponents⟩

/-- Independent exact-type consumer includes the actual hosted run and all projections. -/
theorem locate_machine_requiredFacts (base codeBase : Nat) (hb : 256 ≤ base)
    (shape : CartesianShape) (memory : Memory) (program : Program) (s : State)
    (hpc : s.pc = codeBase) (hs : s.status = .running)
    (hmeta : ∀ i < 174, s.regs (16 + i) = (metadata shape)[i]?.getD 0)
    (host : HostedAt program codeBase ((locateBlock base).compileAt codeBase)) :
    ∃ used, used ≤ 1035 ∧
      let actual := run memory program used s
      LocationResult base (reviewerLogicalSpan shape.size (longCount shape)
        (packedReviewerSparseCount shape) (s.regs base) (s.regs (base + 1)))
        (Data.ofState actual.final) ∧ actual.reads = [] ∧
        (∀ r, r < base + 2 ∨ base + 49 ≤ r → actual.final.regs r = s.regs r) ∧
        actual.steps = used ∧ actual.final.pc = codeBase + 1035 :=
  locateBlock_canonical_hosted_run base codeBase hb shape memory program s hpc hs hmeta host

end RMQ.SuccinctFinal.PackedWordRAM
