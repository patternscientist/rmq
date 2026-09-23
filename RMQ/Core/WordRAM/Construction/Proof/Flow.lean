import RMQ.Core.WordRAM.Construction.Builder.Program

/-! # PRE-1 builder proofs: static pointer flow (stage S8)

Outside the builder firewall. `ptrStep I op` and `ptrFlow b I` compute, from a
list `I` of registers known to hold a value at least a base `e0`, the list after
an action or a block, or `none` when some `store` goes through a register not
in the list. A `reserve` adds its destination (the fresh address is the extent,
at least `e0`); a `move` or an `add` whose first source is in the list adds its
destination; every other register write removes it. A zero test keeps the
registers of both arms; a loop requires its body to re-establish its entry
list. `EvalG.ptrFlow_sound` proves that along any evaluation whose pointer flow
is defined, every executed store addresses at least `e0` (`StoreAbove`), the
listed registers stay at least `e0` on running results, and the extent stays at
least `e0`. With `e0` the initial extent, this is the ownership argument that
the builder never writes an input cell.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

/-- The value of an `Operand` numeral (every register literal of the builder text). -/
@[simp] theorem operand_val_lit (n : Nat) :
    ((no_index (OfNat.ofNat n : Operand)) : Nat) = n % 4294967296 := rfl

/-- Registers known to hold a value at least `e0` after one action, or `none`
when the action stores through a register not known to. -/
def ptrStep (I : List Nat) : Action → Option (List Nat)
  | .store a _ => if (a : Nat) ∈ I then some I else none
  | .reserve d => some ((d : Nat) :: I.filter (· ≠ (d : Nat)))
  | .move d p => some (if (p : Nat) ∈ I then (d : Nat) :: I.filter (· ≠ (d : Nat)) else I.filter (· ≠ (d : Nat)))
  | .arithmetic .add d p _ =>
      some (if (p : Nat) ∈ I then (d : Nat) :: I.filter (· ≠ (d : Nat)) else I.filter (· ≠ (d : Nat)))
  | .arithmetic _ d _ _ => some (I.filter (· ≠ (d : Nat)))
  | .constant d _ => some (I.filter (· ≠ (d : Nat)))
  | .comparison _ d _ _ => some (I.filter (· ≠ (d : Nat)))
  | .load d _ => some (I.filter (· ≠ (d : Nat)))
  | .compareKey d _ _ => some (I.filter (· ≠ (d : Nat)))
  | .loadKey _ _ => some I

/-- Static pointer flow of a block from a set of known pointer registers. -/
def ptrFlow : Block → List Nat → Option (List Nat)
  | .skip, I => some I
  | .action op, I => ptrStep I op
  | .exit _, I => some I
  | .seq a b, I => (ptrFlow a I).bind (ptrFlow b)
  | .ifZero _ z nz, I =>
      match ptrFlow z I, ptrFlow nz I with
      | some Iz, some In => some (Iz.filter (· ∈ In))
      | _, _ => none
  | .loop _ body, I =>
      match ptrFlow body I with
      | some I' => if I.all (· ∈ I') then some I else none
      | none => none

/-- Every listed register holds at least `e0`. -/
def PtrsAbove (e0 : Nat) (I : List Nat) (s : State) : Prop := ∀ r ∈ I, e0 ≤ s.regs r

/-- A store action stores through an address at least `e0`. -/
def StoreAbove (e0 : Nat) (s : State) : Action → Prop
  | .store a _ => e0 ≤ s.regs a
  | _ => True

theorem ptrStep_sound (e0 : Nat) (I I' : List Nat) (op : Action) (s : State)
    (h : ptrStep I op = some I') (hI : PtrsAbove e0 I s) (hext : e0 ≤ s.extent) :
    StoreAbove e0 s op ∧ PtrsAbove e0 I' (execPrim op.prim s) ∧
      e0 ≤ (execPrim op.prim s).extent := by
  have hextle := execPrim_extent_le op.prim s
  have keep : ∀ r, (∀ d, op.prim.destination? = some d → r ≠ d.val) →
      (execPrim op.prim s).regs r = s.regs r := fun r hr =>
    execPrim_frame op.prim s (fun x => x ≠ r) (fun d hd => (hr d hd).symm) r (by simp)
  refine ⟨?_, ?_, by omega⟩
  · cases op <;> simp only [StoreAbove]
    rename_i a v
    simp only [ptrStep] at h
    split at h
    · exact hI a (by assumption)
    · simp at h
  · intro r hr
    cases op with
    | store a v =>
        simp only [ptrStep] at h
        split at h
        · cases h
          rw [keep r (fun d hd => by simp [Action.prim, Prim.destination?] at hd)]
          exact hI r hr
        · simp at h
    | reserve d =>
        simp only [ptrStep, Option.some.injEq] at h
        subst h
        simp only [Action.prim, execPrim, State.writeNext, State.next, put]
        rcases List.mem_cons.mp hr with h1 | h1
        · subst h1; simp; exact hext
        · have ⟨h2, h3⟩ := List.mem_filter.mp h1
          have h3' : r ≠ d := by simpa using h3
          simp [h3']
          exact hI r h2
    | move d p =>
        simp only [ptrStep, Option.some.injEq] at h
        subst h
        simp only [Action.prim, execPrim, State.writeNext, State.next, put]
        split at hr
        · rename_i hp
          rcases List.mem_cons.mp hr with h1 | h1
          · subst h1; simp; exact hI p hp
          · have ⟨h2, h3⟩ := List.mem_filter.mp h1
            have h3' : r ≠ d := by simpa using h3
            simp [h3']
            exact hI r h2
        · have ⟨h1, h2⟩ := List.mem_filter.mp hr
          have h2' : r ≠ d := by simpa using h2
          simp [h2']
          exact hI r h1
    | arithmetic aop d p x =>
        cases aop
        case add =>
            simp only [ptrStep, Option.some.injEq] at h
            subst h
            simp only [Action.prim, execPrim, State.writeNext, State.next, put, Arithmetic.eval]
            split at hr
            · rename_i hp
              rcases List.mem_cons.mp hr with h1 | h1
              · subst h1; simp; have := hI p hp; omega
              · have ⟨h2, h3⟩ := List.mem_filter.mp h1
                have h3' : r ≠ d := by simpa using h3
                simp [h3']
                exact hI r h2
            · have ⟨h1, h2⟩ := List.mem_filter.mp hr
              have h2' : r ≠ d := by simpa using h2
              simp [h2']
              exact hI r h1
        all_goals
          simp only [ptrStep, Option.some.injEq] at h
          subst h
          have ⟨h1, h2⟩ := List.mem_filter.mp hr
          have h2' : r ≠ d := by simpa using h2
          simp only [Action.prim, execPrim, State.writeNext, State.next, put, h2', if_false]
          exact hI r h1
    | constant d v =>
        simp only [ptrStep, Option.some.injEq] at h
        subst h
        have ⟨h1, h2⟩ := List.mem_filter.mp hr
        have h2' : r ≠ d := by simpa using h2
        simp only [Action.prim, execPrim, State.writeNext, State.next, put, h2', if_false]
        exact hI r h1
    | comparison cop d l x =>
        simp only [ptrStep, Option.some.injEq] at h
        subst h
        have ⟨h1, h2⟩ := List.mem_filter.mp hr
        have h2' : r ≠ d := by simpa using h2
        simp only [Action.prim, execPrim, State.writeNext, State.next, put, h2', if_false]
        exact hI r h1
    | load d a =>
        simp only [ptrStep, Option.some.injEq] at h
        subst h
        have ⟨h1, h2⟩ := List.mem_filter.mp hr
        have h2' : r ≠ d := by simpa using h2
        rw [keep r (fun e he => by simp [Action.prim, Prim.destination?] at he; subst he; exact h2')]
        exact hI r h1
    | compareKey d a b =>
        simp only [ptrStep, Option.some.injEq] at h
        subst h
        have ⟨h1, h2⟩ := List.mem_filter.mp hr
        have h2' : r ≠ d := by simpa using h2
        simp only [Action.prim, execPrim, State.writeNext, State.next, put, h2', if_false]
        exact hI r h1
    | loadKey d a =>
        simp only [ptrStep, Option.some.injEq] at h
        subst h
        rw [keep r (fun e he => by simp [Action.prim, Prim.destination?] at he)]
        exact hI r hr

/-- **Pointer flow soundness.** Along an evaluation whose static pointer flow is
defined, every executed store addresses at least `e0`. -/
theorem EvalG.ptrFlow_sound {P : State → Action → Prop} (e0 : Nat) {b : Block} {s s' : State}
    {k : Nat} (h : EvalG P b s s' k) :
    ∀ I I', ptrFlow b I = some I' → PtrsAbove e0 I s → e0 ≤ s.extent →
      EvalG (fun u op => P u op ∧ StoreAbove e0 u op) b s s' k ∧
        (s'.status = .running → PtrsAbove e0 I' s') ∧ e0 ≤ s'.extent := by
  induction h with
  | stopped b s hs =>
      intro I I' _ _ hext
      exact ⟨EvalG.stopped b s hs, fun hr => (hs hr).elim, hext⟩
  | skip s hs =>
      intro I I' hf hI hext
      simp only [ptrFlow, Option.some.injEq] at hf
      subst hf
      exact ⟨EvalG.skip s hs, fun _ => hI, hext⟩
  | action op s hs hp =>
      intro I I' hf hI hext
      obtain ⟨hst, hI', hext'⟩ := ptrStep_sound e0 I I' op s hf hI hext
      exact ⟨EvalG.action op s hs ⟨hp, hst⟩, fun _ => hI', hext'⟩
  | exit src s hs =>
      intro I I' hf hI hext
      simp only [ptrFlow, Option.some.injEq] at hf
      subst hf
      exact ⟨EvalG.exit src s hs, fun hr => by simp at hr, hext⟩
  | @seq a b s s₁ s₂ k₁ k₂ ha hb iha ihb =>
      intro I I' hf hI hext
      simp only [ptrFlow] at hf
      cases hA : ptrFlow a I with
      | none => rw [hA] at hf; simp at hf
      | some I1 =>
          rw [hA] at hf
          obtain ⟨ea, hI1, hext1⟩ := iha I I1 hA hI hext
          by_cases hr1 : s₁.status = .running
          · obtain ⟨eb, hI2, hext2⟩ := ihb I1 I' hf (hI1 hr1) hext1
            exact ⟨EvalG.seq ea eb, hI2, hext2⟩
          · obtain ⟨rfl, rfl⟩ := hb.stopped_eq hr1
            exact ⟨EvalG.seq ea (EvalG.stopped b _ hr1), fun hr => (hr1 hr).elim, hext1⟩
  | @ifZeroTaken c zero nonzero s s' k hs hc hz ih =>
      intro I I' hf hI hext
      simp only [ptrFlow] at hf
      cases hZ : ptrFlow zero I with
      | none => rw [hZ] at hf; simp at hf
      | some Iz =>
          cases hN : ptrFlow nonzero I with
          | none => rw [hZ, hN] at hf; simp at hf
          | some In =>
              rw [hZ, hN] at hf
              simp only [Option.some.injEq] at hf
              subst hf
              obtain ⟨ez, hIz, hextz⟩ := ih I Iz hZ hI hext
              refine ⟨EvalG.ifZeroTaken hs hc ez, fun hr r hmem => hIz hr r (List.mem_filter.mp hmem).1, hextz⟩
  | @ifZeroFallthrough c zero nonzero s s' k hs hc hn hr ih =>
      intro I I' hf hI hext
      simp only [ptrFlow] at hf
      cases hZ : ptrFlow zero I with
      | none => rw [hZ] at hf; simp at hf
      | some Iz =>
          cases hN : ptrFlow nonzero I with
          | none => rw [hZ, hN] at hf; simp at hf
          | some In =>
              rw [hZ, hN] at hf
              simp only [Option.some.injEq] at hf
              subst hf
              obtain ⟨en, hIn, hextn⟩ := ih I In hN hI hext
              refine ⟨EvalG.ifZeroFallthrough hs hc en hr, fun hr' r hmem => hIn hr' r ?_, hextn⟩
              simpa using (List.mem_filter.mp hmem).2
  | @ifZeroFallthroughStopped c zero nonzero s s' k hs hc hn hr ih =>
      intro I I' hf hI hext
      simp only [ptrFlow] at hf
      cases hZ : ptrFlow zero I with
      | none => rw [hZ] at hf; simp at hf
      | some Iz =>
          cases hN : ptrFlow nonzero I with
          | none => rw [hZ, hN] at hf; simp at hf
          | some In =>
              rw [hZ, hN] at hf
              obtain ⟨en, _, hextn⟩ := ih I In hN hI hext
              exact ⟨EvalG.ifZeroFallthroughStopped hs hc en hr, fun hr' => (hr hr').elim, hextn⟩
  | @loopExit c body s hs hc =>
      intro I I' hf hI hext
      simp only [ptrFlow] at hf
      cases hB : ptrFlow body I with
      | none => rw [hB] at hf; simp at hf
      | some I1 =>
          rw [hB] at hf
          simp only at hf
          split at hf
          · simp only [Option.some.injEq] at hf
            subst hf
            exact ⟨EvalG.loopExit hs hc, fun _ => hI, hext⟩
          · simp at hf
  | @loopStep c body s s₁ s₂ k₁ k₂ hs hc hbody hr hrest ihb ihr =>
      intro I I' hf hI hext
      have hf' := hf
      simp only [ptrFlow] at hf
      cases hB : ptrFlow body I with
      | none => rw [hB] at hf; simp at hf
      | some I1 =>
          rw [hB] at hf
          simp only at hf
          split at hf
          · rename_i hall
            simp only [Option.some.injEq] at hf
            subst hf
            obtain ⟨eb, hI1, hext1⟩ := ihb I I1 hB hI hext
            have hIs1 : PtrsAbove e0 I s₁ := fun r hmem =>
              hI1 hr r (by simpa using List.all_eq_true.mp hall r hmem)
            obtain ⟨er, hI2, hext2⟩ := ihr I I hf' hIs1 hext1
            exact ⟨EvalG.loopStep hs hc eb hr er, hI2, hext2⟩
          · simp at hf
  | @loopStopped c body s s₁ k₁ hs hc hbody hr ih =>
      intro I I' hf hI hext
      simp only [ptrFlow] at hf
      cases hB : ptrFlow body I with
      | none => rw [hB] at hf; simp at hf
      | some I1 =>
          obtain ⟨eb, _, hext1⟩ := ih I I1 hB hI hext
          exact ⟨EvalG.loopStopped hs hc eb hr, fun hr' => (hr hr').elim, hext1⟩

end RMQ.SuccinctFinal.PackedConstruction.Proof
