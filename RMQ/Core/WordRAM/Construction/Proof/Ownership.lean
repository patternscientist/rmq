import RMQ.Core.WordRAM.Construction.Proof.Exact
import RMQ.Core.WordRAM.Construction.Proof.FlowFacts

/-! # PRE-1 builder proofs: the run with safety and ownership (stage S8)

Outside the builder firewall. `builderRun_full` strengthens `builderRun_spec`:
the stage evaluation of the source is re-checked with the pointer flow
(`EvalG.ptrFlow_sound` at the initial extent), compiled with
`EvalG.compile_realizes`, and extended by the final `halt 3`; every transition
of the resulting run is `Prim.Safe` at width `W` with a fitting post-state
(`Run.Safe.of_transitions`), and every write event addresses at least the
initial extent. `write_fold_cell` and `run_last_write` give positional
last-write provenance: a cell absent at the start that holds `v` at the end was
written `(a, v)` by some transition, and by no later transition.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder

theorem getElem?_lt_of_some {α : Type} {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) : k < l.length := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · exact hk
  · rw [List.getElem?_eq_none hk] at h; cases h

/-- Folding the write events of a transition list into a memory: the cell `a`
holds `v` afterwards either because some transition writes `(a, v)` and no later
one writes `a`, or because no transition writes `a` and it held `v` before. -/
theorem write_fold_cell (ts : List Transition) :
    ∀ (m0 : Memory) (a v : Nat),
      (ts.filterMap Transition.write?).foldl (fun m e => put m e.1 (some e.2)) m0 a = some v →
      (∃ (k : Nat) (t : Transition), ts[k]? = some t ∧ t.write? = some (a, v) ∧
        ∀ (k' : Nat) (t' : Transition), k < k' → ts[k']? = some t' →
          ∀ e : Nat × Nat, t'.write? = some e → e.1 ≠ a) ∨
      (m0 a = some v ∧ ∀ (k' : Nat) (t' : Transition), ts[k']? = some t' →
          ∀ e : Nat × Nat, t'.write? = some e → e.1 ≠ a) := by
  induction ts with
  | nil =>
      intro m0 a v h
      right
      simp only [List.filterMap_nil, List.foldl_nil] at h
      exact ⟨h, fun k' t' hk' => by simp at hk'⟩
  | cons t rest ih =>
      intro m0 a v h
      cases ht : t.write? with
      | none =>
          simp only [List.filterMap_cons, ht] at h
          rcases ih m0 a v h with ⟨k, u, hk, hu, hlast⟩ | ⟨hm, hno⟩
          · left
            refine ⟨k + 1, u, by simpa using hk, hu, ?_⟩
            intro k' t' hkk hk' e he
            cases k' with
            | zero => omega
            | succ k' => exact hlast k' t' (by omega) (by simpa using hk') e he
          · right
            refine ⟨hm, ?_⟩
            intro k' t' hk' e he
            cases k' with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
                subst hk'; rw [ht] at he; cases he
            | succ k' => exact hno k' t' (by simpa using hk') e he
      | some e0 =>
          simp only [List.filterMap_cons, ht, List.foldl_cons] at h
          rcases ih _ a v h with ⟨k, u, hk, hu, hlast⟩ | ⟨hm, hno⟩
          · left
            refine ⟨k + 1, u, by simpa using hk, hu, ?_⟩
            intro k' t' hkk hk' e he
            cases k' with
            | zero => omega
            | succ k' => exact hlast k' t' (by omega) (by simpa using hk') e he
          · by_cases hb : e0.1 = a
            · left
              have hv : e0.2 = v := by
                simp only [put, hb, if_true, Option.some.injEq] at hm
                exact hm
              refine ⟨0, t, rfl, ?_, ?_⟩
              · rw [ht]; obtain ⟨b, w⟩ := e0; simp only at hb hv; subst hb; subst hv; rfl
              · intro k' t' hkk hk' e he
                cases k' with
                | zero => omega
                | succ k' => exact hno k' t' (by simpa using hk') e he
            · right
              refine ⟨by simpa only [put, if_neg (Ne.symm hb)] using hm, ?_⟩
              intro k' t' hk' e he
              cases k' with
              | zero =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at hk'
                  subst hk'; rw [ht] at he; simp only [Option.some.injEq] at he; subst he; exact hb
              | succ k' => exact hno k' t' (by simpa using hk') e he

/-- **Positional last-write provenance of a run.** If a cell absent at the start
of a run holds `v` at its end, some transition of the run writes `(a, v)` and no
later transition writes address `a`. -/
theorem run_last_write (program : List BInstr) (fuel : Nat) (s : State) (a v : Nat)
    (hfinal : (run program fuel s).final.memory a = some v) (hinit : s.memory a = none) :
    ∃ (k : Nat) (t : Transition), (run program fuel s).transitions[k]? = some t ∧ t.write? = some (a, v) ∧
      ∀ (k' : Nat) (t' : Transition), k < k' → (run program fuel s).transitions[k']? = some t' →
        ∀ e : Nat × Nat, t'.write? = some e → e.1 ≠ a := by
  have h := writes_replay program fuel s
  rw [h] at hfinal
  rcases write_fold_cell _ s.memory a v hfinal with hw | ⟨hm, _⟩
  · exact hw
  · rw [hinit] at hm; cases hm

open RMQ.SuccinctFinal.PackedWordRAM (buildMemory wordWidth)

theorem StoreAbove.pc_set {e0 : Nat} {s : State} {op : Action} (h : StoreAbove e0 s op) (q : Nat) :
    StoreAbove e0 { s with pc := q } op := by
  cases op <;> exact h

theorem TransitionShape.left {P Q : State → Action → Prop} {base size : Nat} {t : Transition}
    (h : TransitionShape (fun u op => P u op ∧ Q u op) base size t) : TransitionShape P base size t := by
  rcases h with ⟨op, hi, hp, _⟩ | h | h | h
  · exact Or.inl ⟨op, hi, hp⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- A classified transition whose actions store above `e0` writes only above `e0`. -/
theorem TransitionShape.write_above {P : State → Action → Prop} {e0 base size : Nat} {t : Transition}
    (h : TransitionShape (fun u op => P u op ∧ StoreAbove e0 u op) base size t) :
    ∀ e, t.write? = some e → e0 ≤ e.1 := by
  intro e he
  unfold Transition.write? at he
  rcases h with ⟨op, hi, _, hst⟩ | ⟨c, target, hi, _⟩ | ⟨target, hi, _⟩ | ⟨src, hi⟩
  · rw [hi] at he
    cases op with
    | store a v =>
        simp only [Action.prim] at he
        split at he
        · simp only [Option.some.injEq] at he
          subst he
          exact hst
        · simp at he
    | _ => simp [Action.prim] at he
  · rw [hi] at he; simp at he
  · rw [hi] at he; simp at he
  · rw [hi] at he; simp at he

/-- **The builder run with safety and input ownership.** The run of the compiled
source followed by `halt 3` halts with `outBase` in register 3 within the stage
cost bound, holds `buildMemory xs` from `outBase` to the extent, keeps the memory
below the initial extent and the keys, every transition is safe at width `W`
with a fitting post-state, and every write event addresses at least the initial
extent. -/
theorem builderRun_full {W : Nat} (hW : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (hleaf : KeySpec W xs Inp leaf) (hsize : (builderSource leaf).size < 2 ^ 32)
    (J : List Nat) (hflow : ptrFlow (builderSource leaf) [] = some J)
    (hlenW : (builderSource leaf).size + 1 < 2 ^ W)
    (s : State) (hpc : s.pc = 0) (hrun : s.status = .running)
    (hregs : ∀ r, s.regs r = 0) (hext : 0 < s.extent) (hmem : s.memory 0 = some xs.length)
    (hinp : Inp s) (hInp : InpBelow Inp s.extent)
    (hbankcap : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W)
    (hcap : s.extent + 64 * (400000 * (xs.length + 1)) < 2 ^ W)
    (hWW : wordWidth xs.length ≤ W) (hfit : s.Fits W) :
    ∃ sF ts, RunsTo ((builderSource leaf).compileAt 0 ++ [⟨.halt 3⟩]) s sF ts ∧
      ts.length ≤ 4 + (25 * W + 40 + 39 * (5 * W + 20)) + 2100 * (400000 * (xs.length + 1)) ∧
      sF.status = .halted (sF.regs 3) ∧ s.extent ≤ sF.regs 3 ∧
      sF.regs 3 ≤ s.extent + 8 * (400000 * (xs.length + 1)) ∧
      sF.extent = sF.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        sF.memory (sF.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < s.extent → sF.memory a = s.memory a) ∧ sF.keys = s.keys ∧
      Run.Safe W ((builderSource leaf).compileAt 0 ++ [⟨.halt 3⟩]) ⟨sF, ts⟩ ∧
      (∀ t ∈ ts, ∀ e, t.write? = some e → s.extent ≤ e.1) := by
  obtain ⟨t, k, e, hk, htr, h3a, h3b, htext, htmem, htbelow, htk⟩ :=
    builderSource_spec hW xs Inp leaf hleaf s hrun hregs hext hmem hinp hInp hbankcap hcap hWW
  obtain ⟨e', _, _⟩ := EvalG.ptrFlow_sound s.extent e [] J hflow (fun r h => absurd h (List.not_mem_nil))
    (Nat.le_refl _)
  let prog := (builderSource leaf).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)]
  have host : HostedAt prog 0 ((builderSource leaf).compileAt 0) :=
    HostedAt.append_left (HostedAt.self prog)
  obtain ⟨s'', ts, hR, hlen, hagree, hpc'', hshape⟩ :=
    e'.compile_realizes (fun _ q _ hp => ⟨Action.Safe.pc_set hp.1 q, StoreAbove.pc_set hp.2 q⟩)
      prog 0 host (by simpa using hsize)
  have hagree' := hagree.eq_set
  have hs0 : ({ s with pc := 0 } : State) = s := by
    cases s; simp only at hpc; subst hpc; rfl
  rw [hs0] at hR
  have hs''r : s''.status = .running := by rw [hagree']; exact htr
  have hs''pc : s''.pc = (builderSource leaf).size := by
    have := hpc'' hs''r; simpa using this
  have hfetch : prog[s''.pc]? = some ⟨.halt 3⟩ := by
    rw [hs''pc]
    show ((builderSource leaf).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)])[(builderSource leaf).size]? = _
    rw [List.getElem?_append_right (by simp)]
    simp
  have hstep := RunsTo.instruction hs''r hfetch
  have hall := hR.trans hstep
  have hfin : execPrim (Prim.halt 3) s'' = { s'' with status := .halted (s''.regs 3) } := rfl
  have hreg : s''.regs = t.regs := by rw [hagree']
  have hproglen : prog.length = (builderSource leaf).size + 1 := by simp [prog]
  have hsafeTs : ∀ u ∈ ts ++ [(⟨s'', ⟨.halt 3⟩, execPrim (Prim.halt 3) s''⟩ : Transition)],
      Prim.Safe W prog.length u.before u.instruction.primitive := by
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact (TransitionShape.left (hshape u hu)).safe hW (by rw [hproglen]; simp)
    · simp only [List.mem_singleton] at hu
      subst hu
      exact ⟨Prim.operandsFit_of_width _ hW, trivial⟩
  have hRun : run prog (ts ++ [(⟨s'', ⟨.halt 3⟩, execPrim (Prim.halt 3) s''⟩ : Transition)]).length s =
      ⟨execPrim (Prim.halt 3) s'', ts ++ [⟨s'', ⟨.halt 3⟩, execPrim (Prim.halt 3) s''⟩]⟩ := hall
  have hsafe := Run.Safe.of_transitions prog W (by rw [hproglen]; exact hlenW) _ s hfit
    (by rw [hRun]; exact hsafeTs)
  rw [hRun] at hsafe
  refine ⟨_, _, hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsafe, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · show (execPrim (Prim.halt 3) s'').status = .halted ((execPrim (Prim.halt 3) s'').regs 3)
    rw [hfin]
  · show s.extent ≤ (execPrim (Prim.halt 3) s'').regs 3
    rw [hfin]; rw [hreg]; exact h3a
  · show (execPrim (Prim.halt 3) s'').regs 3 ≤ _
    rw [hfin]; rw [hreg]; exact h3b
  · show (execPrim (Prim.halt 3) s'').extent = (execPrim (Prim.halt 3) s'').regs 3 + _
    rw [hfin]; rw [hreg, hagree']; exact htext
  · intro i hi
    show (execPrim (Prim.halt 3) s'').memory ((execPrim (Prim.halt 3) s'').regs 3 + i) = _
    rw [hfin]; rw [hreg, hagree']; exact htmem i hi
  · intro a ha
    show (execPrim (Prim.halt 3) s'').memory a = _
    rw [hfin]; simp only; rw [hagree']; exact htbelow a ha
  · show (execPrim (Prim.halt 3) s'').keys = _
    rw [hfin]; simp only; rw [hagree']; exact htk
  · intro u hu e he
    rcases List.mem_append.mp hu with hu | hu
    · exact TransitionShape.write_above (hshape u hu) e he
    · simp only [List.mem_singleton] at hu
      subst hu
      simp [Transition.write?] at he

end RMQ.SuccinctFinal.PackedConstruction.Proof
