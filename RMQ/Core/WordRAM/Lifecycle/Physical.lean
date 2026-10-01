import RMQ.Core.WordRAM.Lifecycle.Accounting
import RMQ.Core.WordRAM.Lifecycle.ArrayRun
import RMQ.Core.WordRAM.Lifecycle.Retained

/-! # One numeric physical view of the lifecycle state

The fixed code, numeric bank, eight controls, and currently owned arena occupy
disjoint consecutive ranges. This is a finite observation of the existing
machine, not another interpreter. `Option Nat` retains its uninitialized-cell
meaning; initialization is a proof predicate, not a stored bitmap. Comparison
keys remain separately counted Int resources. Logical array ownership is not a
claim about native allocation capacity or external aliases.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Physical

open PackedConstruction (Operand Prim put execPrim)
set_option maxRecDepth 30000

def codeLength (model : InputModel) : Nat := (encodedProgram model).length
def registerBase (model : InputModel) : Nat := codeLength model
def controlBase (model : InputModel) : Nat := registerBase model + numericBank
def arenaBase (model : InputModel) : Nat := controlBase model + controlWords

def codeAddress (_model : InputModel) (i : Nat) : Nat := i
def registerAddress (model : InputModel) (r : Nat) : Nat := registerBase model + r
def controlAddress (model : InputModel) (i : Nat) : Nat := controlBase model + i
def arenaAddress (model : InputModel) (a : Nat) : Nat := arenaBase model + a

def extent (model : InputModel) (s : State) : Nat := arenaBase model + s.core.extent

def statusTag : PackedConstruction.Status → Nat
  | .running => 0
  | .halted _ => 1
  | .fault => 2

def haltValue : PackedConstruction.Status → Nat
  | .halted value => value
  | _ => 0

/-- PC, status, halted result, arena extent, numeric-bank extent, key extent,
key-register extent, and one reserved zero control word, in this order. -/
def control (s : State) : Nat → Nat
  | 0 => s.core.pc
  | 1 => statusTag s.core.status
  | 2 => haltValue s.core.status
  | 3 => s.core.extent
  | 4 => numericBank
  | 5 => s.keyExtent
  | 6 => s.keyRegExtent
  | _ => 0

def lookup (model : InputModel) (s : State) (p : Nat) : Option Nat :=
  if p < codeLength model then (encodedProgram model)[p]?
  else if p < controlBase model then some (s.core.regs (p - registerBase model))
  else if p < arenaBase model then some (control s (p - controlBase model))
  else if p < extent model s then s.core.memory (p - arenaBase model)
  else none

/-- A finite specification view. Producing this list is not a charged machine
operation and is not an executable implementation of an instruction. -/
def view (model : InputModel) (s : State) : List (Option Nat) :=
  List.ofFn (fun p : Fin (extent model s) => lookup model s p.val)

theorem view_length (model : InputModel) (s : State) :
    (view model s).length = extent model s := by simp [view]

theorem lookup_code (model : InputModel) (s : State) (i : Nat) (hi : i < codeLength model) :
    lookup model s (codeAddress model i) = (encodedProgram model)[i]? := by
  simp [lookup, codeAddress, hi]

theorem lookup_register (model : InputModel) (s : State) (r : Nat) (hr : r < numericBank) :
    lookup model s (registerAddress model r) = some (s.core.regs r) := by
  simp only [lookup, registerAddress, registerBase, controlBase]
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem lookup_control (model : InputModel) (s : State) (i : Nat) (hi : i < controlWords) :
    lookup model s (controlAddress model i) = some (control s i) := by
  have hc : codeLength model ≤ controlBase model := by unfold controlBase registerBase; omega
  simp only [lookup, controlAddress]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by unfold arenaBase; omega),
    Nat.add_sub_cancel_left]

theorem lookup_arena (model : InputModel) (s : State) (a : Nat) :
    lookup model s (arenaAddress model a) =
      if a < s.core.extent then s.core.memory a else none := by
  have hc : codeLength model ≤ arenaBase model := by
    unfold arenaBase controlBase registerBase; omega
  have hr : controlBase model ≤ arenaBase model := by unfold arenaBase; omega
  simp only [lookup, arenaAddress]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  simp only [extent, Nat.add_lt_add_iff_left, Nat.add_sub_cancel_left]

theorem lookup_arena_closed (model : InputModel) (s : State) (closed : s.Closed) (a : Nat) :
    lookup model s (arenaAddress model a) = s.core.memory a := by
  rw [lookup_arena]
  split
  · rfl
  · exact (closed.1 a (by omega)).symm

theorem lookup_outside (model : InputModel) (s : State) (p : Nat)
    (outside : extent model s ≤ p) : lookup model s p = none := by
  have hb : arenaBase model ≤ p := by unfold extent at outside; omega
  have hc : codeLength model ≤ arenaBase model := by unfold arenaBase controlBase registerBase; omega
  have hr : controlBase model ≤ arenaBase model := by unfold arenaBase; omega
  simp [lookup, show ¬p < codeLength model by omega,
    show ¬p < controlBase model by omega, show ¬p < arenaBase model by omega,
    show ¬p < extent model s by omega]

private theorem finite_lookup (n : Nat) (f : Nat → Option Nat)
    (outside : ∀ p, n ≤ p → f p = none) (p : Nat) :
    ((List.ofFn (fun i : Fin n => f i.val))[p]?).join = f p := by
  by_cases hp : p < n
  · simp [hp]
  · rw [List.getElem?_eq_none_iff.mpr (by simp; omega)]
    exact (outside p (by omega)).symm

theorem view_lookup (model : InputModel) (s : State) (p : Nat) :
    ((view model s)[p]?).join = lookup model s p :=
  finite_lookup (extent model s) (lookup model s) (lookup_outside model s) p

inductive Slot (model : InputModel) where
  | code (i : Fin (codeLength model))
  | register (r : Fin numericBank)
  | control (i : Fin controlWords)
  | arena (a : Nat)

def address {model : InputModel} : Slot model → Nat
  | .code i => codeAddress model i
  | .register r => registerAddress model r
  | .control i => controlAddress model i
  | .arena a => arenaAddress model a

theorem address_injective (model : InputModel) :
    ∀ x y : Slot model, address x = address y → x = y := by
  intro x y equal
  cases x with
  | code i =>
    have hi := i.isLt
    cases y with
    | code j => exact congrArg Slot.code (Fin.ext equal)
    | register j => simp only [address, codeAddress, registerAddress, registerBase] at equal; omega
    | control j => simp only [address, codeAddress, controlAddress, controlBase, registerBase] at equal; omega
    | arena a => simp only [address, codeAddress, arenaAddress, arenaBase, controlBase, registerBase] at equal; omega
  | register r =>
    have hr := r.isLt
    cases y with
    | code j => have hj := j.isLt; simp only [address, codeAddress, registerAddress, registerBase] at equal; omega
    | register j => apply congrArg Slot.register; apply Fin.ext; simp only [address, registerAddress] at equal; omega
    | control j => simp only [address, registerAddress, controlAddress, controlBase] at equal; omega
    | arena a => simp only [address, registerAddress, arenaAddress, arenaBase, controlBase] at equal; omega
  | control i =>
    have hi := i.isLt
    cases y with
    | code j => have hj := j.isLt; simp only [address, codeAddress, controlAddress, controlBase, registerBase] at equal; omega
    | register j => have hj := j.isLt; simp only [address, controlAddress, registerAddress, controlBase] at equal; omega
    | control j => apply congrArg Slot.control; apply Fin.ext; simp only [address, controlAddress] at equal; omega
    | arena a => simp only [address, controlAddress, arenaAddress, arenaBase] at equal; omega
  | arena a =>
    cases y with
    | code j => have hj := j.isLt; simp only [address, codeAddress, arenaAddress, arenaBase, controlBase, registerBase] at equal; omega
    | register j => have hj := j.isLt; simp only [address, registerAddress, arenaAddress, arenaBase, controlBase] at equal; omega
    | control j => have hj := j.isLt; simp only [address, controlAddress, arenaAddress, arenaBase] at equal; omega
    | arena b => apply congrArg Slot.arena; simp only [address, arenaAddress] at equal; omega

/-- Finite-bank reads use the same zero default as the existing array owner. -/
def registerRead (model : InputModel) (s : State) (r : Nat) : Option Nat :=
  if r < numericBank then lookup model s (registerAddress model r) else some 0

theorem registerRead_complete (model : InputModel) (s : State)
    (bank : ∀ r, numericBank ≤ r → s.core.regs r = 0) (r : Nat) :
    registerRead model s r = some (s.core.regs r) := by
  unfold registerRead
  split
  · exact lookup_register model s r ‹_›
  · rw [bank r (by omega)]

def Initialized (s : State) : Prop :=
  ∀ a, a < s.core.extent → ∃ value, s.core.memory a = some value

theorem canonical_initialized {xs : List Int} {s : State}
    (canonical : Retained.Canonical xs s) : Initialized s := by
  intro a ha
  rw [canonical.1.2.1] at ha
  rw [canonical.1.1]
  exact ⟨(PackedWordRAM.buildMemory xs)[a], List.getElem?_eq_getElem ha⟩

theorem lookup_initialized (model : InputModel) (s : State) (initialized : Initialized s)
    (p : Nat) (inside : p < extent model s) : ∃ value, lookup model s p = some value := by
  unfold lookup
  split
  · exact ⟨(encodedProgram model)[p], List.getElem?_eq_getElem ‹_›⟩
  · split
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact initialized _ (by unfold extent at inside; omega)

def wordView (model : InputModel) (s : State) : List Nat :=
  (view model s).map (fun value => value.getD 0)

/-- Once initialized, the entire owned view is exactly a list of Nat words.
There is no retained initialization mask in this statement or in the owner. -/
theorem wordView_exact (model : InputModel) (s : State) (initialized : Initialized s) :
    (wordView model s).map some = view model s := by
  unfold wordView
  rw [List.map_map]
  refine Eq.trans ?_ (List.map_id (view model s))
  apply List.map_congr_left
  intro cell member
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.mp member
  have inside : p < extent model s := by
    have h := (List.getElem?_eq_some_iff.mp hp).1
    simpa only [view_length] using h
  have lookupCell : lookup model s p = cell := by
    have h := view_lookup model s p
    rw [hp] at h
    exact h.symm
  obtain ⟨value, hv⟩ := lookup_initialized model s initialized p inside
  rw [← lookupCell, hv]
  rfl

theorem arenaBase_le (model : InputModel) : arenaBase model ≤ 1125176 := by
  have h := encodedProgram_length_le model
  change (encodedProgram model).length ≤ 1116895 at h
  unfold arenaBase controlBase registerBase codeLength numericBank controlWords
  omega

/-- Static layout overhead plus the declared allocation peak fits the existing,
query-independent word width. The endpoint itself is representable. -/
theorem peak_address_fit (model : InputModel) (n a : Nat) (bound : a ≤ 5000000 * (n + 1)) :
    arenaAddress model a < 2 ^ PackedWordRAM.wordWidth n := by
  have cap := PackedConstruction.Proof.bankcap_wordWidth n
  have power : 2 * n + 4 ≤ (2 * n + 4) ^ 8 := Nat.le_self_pow (by decide) _
  have overhead := arenaBase_le model
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [h32] at cap
  unfold arenaAddress
  omega

theorem extent_fit (model : InputModel) (n : Nat) (s : State)
    (peak : s.core.extent ≤ 5000000 * (n + 1)) :
    extent model s < 2 ^ PackedWordRAM.wordWidth n :=
  peak_address_fit model n s.core.extent peak

theorem owned_address_fit (model : InputModel) (n : Nat) (s : State)
    (peak : s.core.extent ≤ 5000000 * (n + 1)) (p : Nat) (owned : p < extent model s) :
    p < 2 ^ PackedWordRAM.wordWidth n := Nat.lt_trans owned (extent_fit model n s peak)

theorem control_fits (s : State) (W : Nat) (fit : s.Fits W) (bank : numericBank < 2 ^ W)
    (i : Nat) (hi : i < controlWords) : control s i < 2 ^ W := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    change i < 8 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fit.1.2.1
  · cases hs : s.core.status <;> simp only [control, hs, statusTag] <;>
      change 8273 < 2 ^ W at bank <;> omega
  · cases hs : s.core.status with
    | running => simpa only [control, hs, haltValue] using Nat.two_pow_pos W
    | fault => simpa only [control, hs, haltValue] using Nat.two_pow_pos W
    | halted value => simpa only [control, hs, haltValue] using fit.1.2.2.2.2 value hs
  · exact fit.1.2.2.1
  · exact bank
  · exact fit.2.1
  · exact fit.2.2
  · exact Nat.two_pow_pos _

theorem lookup_word_fits (model : InputModel) (n : Nat) (s : State)
    (fit : s.Fits (PackedWordRAM.wordWidth n)) (p value : Nat)
    (reply : lookup model s p = some value) : value < 2 ^ PackedWordRAM.wordWidth n := by
  unfold lookup at reply
  split at reply
  · exact all_encoded_fields_fit model n value (List.mem_of_getElem? reply)
  · split at reply
    · rw [← Option.some.inj reply]; exact fit.1.1 _
    · split at reply
      · rw [← Option.some.inj reply]
        apply control_fits s _ fit
        · have h := PackedWordRAM.query_small_fields_fit n; change 8273 < _; omega
        · unfold arenaBase at *; omega
      · split at reply
        · exact fit.1.2.2.2.1 _ _ reply
        · cases reply

theorem code_unchanged (model : InputModel) (s t : State) (i : Nat) (hi : i < codeLength model) :
    lookup model t (codeAddress model i) = lookup model s (codeAddress model i) := by
  rw [lookup_code model t i hi, lookup_code model s i hi]

theorem store_extent (model : InputModel) (s : State) (a v : Operand) :
    extent model (execute (.old (.store a v)) s) = extent model s := by
  simp only [execute, execPrim]
  split <;> rfl

theorem store_registers (s : State) (a v : Operand) :
    (execute (.old (.store a v)) s).core.regs = s.core.regs := by
  simp only [execute, execPrim]
  split <;> rfl

theorem store_arena (model : InputModel) (s : State) (a v : Operand)
    (inside : s.core.regs a < s.core.extent) (j : Nat) :
    lookup model (execute (.old (.store a v)) s) (arenaAddress model j) =
      if j = s.core.regs a then some (s.core.regs v)
      else lookup model s (arenaAddress model j) := by
  rw [lookup_arena, lookup_arena]
  simp only [execute, execPrim, if_pos inside, PackedConstruction.State.next, put]
  by_cases hj : j = s.core.regs a
  · simp [hj, inside]
  · simp [hj]

theorem store_control (s : State) (a v : Operand) (inside : s.core.regs a < s.core.extent)
    (i : Nat) (hi : i < controlWords) :
    control (execute (.old (.store a v)) s) i =
      if i = 0 then s.core.pc + 1 else control s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    change i < 8 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [control, execute, execPrim, inside, PackedConstruction.State.next]

theorem reserve_extent (model : InputModel) (s : State) (dst : Operand) :
    extent model (execute (.old (.reserve dst)) s) = extent model s + 1 := by
  change arenaBase model + (s.core.extent + 1) = arenaBase model + s.core.extent + 1
  omega

/-- Reservation changes ownership and its destination register. The newly
owned arena cell stays uninitialized, exactly as in the existing evaluator. -/
theorem reserve_arena (model : InputModel) (s : State) (dst : Operand)
    (closed : s.Closed) (a : Nat) :
    lookup model (execute (.old (.reserve dst)) s) (arenaAddress model a) =
      lookup model s (arenaAddress model a) := by
  rw [lookup_arena, lookup_arena]
  change (if a < s.core.extent + 1 then s.core.memory a else none) = _
  by_cases ha : a < s.core.extent
  · simp [ha, show a < s.core.extent + 1 by omega]
  · rw [if_neg ha]
    split
    · exact closed.1 a (by omega)
    · rfl

theorem reserve_register (model : InputModel) (s : State) (dst : Operand)
    (r : Nat) (hr : r < numericBank) :
    lookup model (execute (.old (.reserve dst)) s) (registerAddress model r) =
      some (if r = dst.val then s.core.extent else s.core.regs r) := by
  rw [lookup_register model _ r hr]
  rfl

theorem reserve_control (s : State) (dst : Operand) (i : Nat) (hi : i < controlWords) :
    control (execute (.old (.reserve dst)) s) i =
      if i = 0 then s.core.pc + 1 else if i = 3 then s.core.extent + 1 else control s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    change i < 8 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [control, execute, execPrim, PackedConstruction.State.writeNext, PackedConstruction.State.next]

theorem release_extent (model : InputModel) (s : State) (positive : 0 < s.core.extent) :
    extent model (execute .releaseCell s) + 1 = extent model s := by
  simp only [execute, if_neg (by omega : s.core.extent ≠ 0), extent,
    PackedConstruction.State.next]
  omega

theorem release_registers (s : State) : (execute .releaseCell s).core.regs = s.core.regs := by
  simp only [execute]
  split <;> rfl

theorem release_arena (model : InputModel) (s : State) (positive : 0 < s.core.extent) (a : Nat) :
    lookup model (execute .releaseCell s) (arenaAddress model a) =
      if a = s.core.extent - 1 then none else lookup model s (arenaAddress model a) := by
  rw [lookup_arena, lookup_arena]
  simp only [execute, if_neg (by omega : s.core.extent ≠ 0), PackedConstruction.State.next, put]
  by_cases ha : a = s.core.extent - 1
  · simp [ha]
  · by_cases small : a < s.core.extent - 1
    · simp [ha, small, show a < s.core.extent by omega]
    · simp [ha, small, show ¬ a < s.core.extent by omega]

theorem release_control (s : State) (positive : 0 < s.core.extent)
    (i : Nat) (hi : i < controlWords) :
    control (execute .releaseCell s) i =
      if i = 0 then s.core.pc + 1 else if i = 3 then s.core.extent - 1 else control s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    change i < 8 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [control, execute, show s.core.extent ≠ 0 by omega, PackedConstruction.State.next]

/-- Comparison retirement changes its separately counted resources and the
control bank; it preserves every numeric arena cell and numeric register. -/
theorem releaseKey_numeric (model : InputModel) (s : State) :
    extent model (execute .releaseKey s) = extent model s ∧
      (execute .releaseKey s).core.regs = s.core.regs ∧
      ∀ a, lookup model (execute .releaseKey s) (arenaAddress model a) =
        lookup model s (arenaAddress model a) := by
  simp only [execute]
  split <;> refine ⟨rfl, rfl, ?_⟩ <;> intro a <;>
    rw [lookup_arena, lookup_arena] <;> rfl

theorem releaseKeyRegister_numeric (model : InputModel) (s : State) :
    extent model (execute .releaseKeyRegister s) = extent model s ∧
      (execute .releaseKeyRegister s).core.regs = s.core.regs ∧
      ∀ a, lookup model (execute .releaseKeyRegister s) (arenaAddress model a) =
        lookup model s (arenaAddress model a) := by
  simp only [execute]
  split <;> refine ⟨rfl, rfl, ?_⟩ <;> intro a <;>
    rw [lookup_arena, lookup_arena] <;> rfl

theorem releaseKey_control (s : State) (positive : 0 < s.keyExtent)
    (i : Nat) (hi : i < controlWords) :
    control (execute .releaseKey s) i =
      if i = 0 then s.core.pc + 1 else if i = 5 then s.keyExtent - 1 else control s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    change i < 8 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [control, execute, show s.keyExtent ≠ 0 by omega, PackedConstruction.State.next]

theorem releaseKeyRegister_control (s : State) (positive : 0 < s.keyRegExtent)
    (i : Nat) (hi : i < controlWords) :
    control (execute .releaseKeyRegister s) i =
      if i = 0 then s.core.pc + 1 else if i = 6 then s.keyRegExtent - 1 else control s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    change i < 8 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [control, execute, show s.keyRegExtent ≠ 0 by omega, PackedConstruction.State.next]

theorem boundary_arena (model : InputModel) (s : State) (b : Boundary) (a : Nat) :
    lookup model (executeBoundary b s) (arenaAddress model a) =
      lookup model s (arenaAddress model a) := by
  rw [lookup_arena, lookup_arena]
  cases b <;> rfl

theorem boundary_extent (model : InputModel) (s : State) (b : Boundary) :
    extent model (executeBoundary b s) = extent model s := by cases b <;> rfl

theorem boundary_register (model : InputModel) (s : State) (b : Boundary)
    (r : Nat) (hr : r < numericBank) :
    lookup model (executeBoundary b s) (registerAddress model r) = some
      (match b with
       | .left value => if r = requestLeftRegister then value else s.core.regs r
       | .right value => if r = requestRightRegister then value else s.core.regs r
       | _ => s.core.regs r) := by
  rw [lookup_register model _ r hr]
  cases b <;> rfl

theorem boundary_control (s : State) (b : Boundary) (i : Nat) (hi : i < controlWords) :
    control (executeBoundary b s) i =
      match b with
      | .entry target => if i = 0 then target.val else control s i
      | .activate => if i = 1 ∨ i = 2 then 0 else control s i
      | _ => control s i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    change i < 8 at hi; omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases b <;> simp [control, executeBoundary, statusTag, haltValue]

/-- Only an in-extent logical attempt is translated into a physical fetch.
An out-of-extent attempt retains its logical address but performs no fetch. -/
def checkedAddress (model : InputModel) (s : State) (a : Nat) : Option Nat :=
  if a < s.core.extent then some (arenaAddress model a) else none

theorem checkedAddress_none (model : InputModel) (s : State) (a : Nat) :
    checkedAddress model s a = none ↔ s.core.extent ≤ a := by
  simp [checkedAddress]

theorem checkedAddress_some (model : InputModel) (s : State) (a p : Nat) :
    checkedAddress model s a = some p ↔ a < s.core.extent ∧ p = arenaAddress model a := by
  by_cases h : a < s.core.extent
  · simp [checkedAddress, h, eq_comm]
  · simp [checkedAddress, h]

theorem read_source (t : Transition) (a : Nat) (reply : Option Nat)
    (read : t.read? = some (a, reply)) :
    ∃ dst address, t.action = .instruction (.old (.load dst address)) ∧
      a = t.before.core.regs address ∧
      reply = (if a < t.before.core.extent then t.before.core.memory a else none) := by
  cases ha : t.action with
  | boundary b => simp [Transition.read?, ha] at read
  | instruction i =>
    cases i with
    | old p =>
      cases p <;> simp [Transition.read?, ha] at read
      case load dst address =>
        obtain ⟨rfl, rfl⟩ := read
        exact ⟨dst, address, rfl, rfl, rfl⟩
    | releaseCell => simp [Transition.read?, ha] at read
    | releaseKey => simp [Transition.read?, ha] at read
    | releaseKeyRegister => simp [Transition.read?, ha] at read

theorem read_provenance (model : InputModel) (t : Transition) (a : Nat) (reply : Option Nat)
    (read : t.read? = some (a, reply)) :
    reply = lookup model t.before (arenaAddress model a) ∧
      (∀ p, checkedAddress model t.before a = some p → lookup model t.before p = reply) ∧
      (checkedAddress model t.before a = none ↔ t.before.core.extent ≤ a) := by
  obtain ⟨_, _, _, _, backed⟩ := read_source t a reply read
  have lookupEq : reply = lookup model t.before (arenaAddress model a) := by
    rw [lookup_arena]; exact backed
  refine ⟨lookupEq, ?_, checkedAddress_none model t.before a⟩
  intro p hp
  rw [(checkedAddress_some model t.before a p).mp hp |>.2]
  exact lookupEq.symm

/-- Failed extent checks are the existing evaluator's one scalar fault step;
they change neither arena allocation nor backing and perform no physical fetch. -/
theorem failed_load (model : InputModel) (s : State) (dst address : Operand)
    (outside : s.core.extent ≤ s.core.regs address) :
    checkedAddress model s (s.core.regs address) = none ∧
      execute (.old (.load dst address)) s =
        { s with core := { s.core with status := .fault } } := by
  exact ⟨(checkedAddress_none model s _).mpr outside,
    by simp [execute, execPrim, show ¬s.core.regs address < s.core.extent by omega]⟩

theorem read_width (model : InputModel) (n : Nat) (t : Transition) (a : Nat) (reply : Option Nat)
    (read : t.read? = some (a, reply)) (fit : t.before.Fits (PackedWordRAM.wordWidth n))
    (peak : t.before.core.extent ≤ 5000000 * (n + 1)) :
    a < 2 ^ PackedWordRAM.wordWidth n ∧
      (∀ p, checkedAddress model t.before a = some p → p < 2 ^ PackedWordRAM.wordWidth n) ∧
      (∀ value, reply = some value → value < 2 ^ PackedWordRAM.wordWidth n) := by
  obtain ⟨dst, address, _, source, backed⟩ := read_source t a reply read
  refine ⟨by rw [source]; exact fit.1.1 address, ?_, ?_⟩
  · intro p hp
    obtain ⟨inside, rfl⟩ := (checkedAddress_some model t.before a p).mp hp
    exact peak_address_fit model n a (by omega)
  · intro value hv
    exact lookup_word_fits model n t.before fit _ value
      ((read_provenance model t a reply read).1.symm.trans hv)

/-- Strong actual primitive safety supplies the physical-fetch guard and
successful backing; no separate address or answer assumption is required. -/
theorem safe_read (model : InputModel) (n len : Nat) (t : Transition) (a : Nat) (reply : Option Nat)
    (read : t.read? = some (a, reply)) (safe : t.Safe (PackedWordRAM.wordWidth n) len)
    (fit : t.before.Fits (PackedWordRAM.wordWidth n))
    (peak : t.before.core.extent ≤ 5000000 * (n + 1)) :
    ∃ p value, checkedAddress model t.before a = some p ∧ reply = some value ∧
      lookup model t.before p = some value ∧ p < 2 ^ PackedWordRAM.wordWidth n ∧
      a < 2 ^ PackedWordRAM.wordWidth n ∧ value < 2 ^ PackedWordRAM.wordWidth n := by
  obtain ⟨dst, address, action, source, backed⟩ := read_source t a reply read
  obtain ⟨i, hi, hs⟩ := safe
  have same : i = .old (.load dst address) := by
    rw [action] at hi
    exact Action.instruction.inj hi.symm
  subst i
  have loaded : t.before.core.regs address < t.before.core.extent ∧
      ∃ value, t.before.core.memory (t.before.core.regs address) = some value ∧
        value < 2 ^ PackedWordRAM.wordWidth n := hs.2
  obtain ⟨inside, value, valueAt, valueFit⟩ := loaded
  have ha : a < t.before.core.extent := by rw [source]; exact inside
  have hv : reply = some value := by rw [backed, if_pos ha, source]; exact valueAt
  have checked : checkedAddress model t.before a = some (arenaAddress model a) := by
    simp [checkedAddress, ha]
  have widths := read_width model n t a reply read fit peak
  exact ⟨arenaAddress model a, value, checked, hv,
    ((read_provenance model t a reply read).2.1 _ checked).trans hv,
    widths.2.1 _ checked, widths.1, valueFit⟩

structure Read where
  logical : Nat
  physical : Option Nat
  reply : Option Nat

def Read.logicalReceipt (r : Read) : Nat × Option Nat := (r.logical, r.reply)

def translateRead (model : InputModel) (s : State) (r : Nat × Option Nat) : Read :=
  ⟨r.1, checkedAddress model s r.1, r.2⟩

def physicalRead (model : InputModel) (t : Transition) : Option Read :=
  t.read?.map (translateRead model t.before)

def physicalReads (model : InputModel) (ts : List Transition) : List Read :=
  ts.filterMap (physicalRead model)

/-- Logical receipts are preserved for the entire list, in order and with
multiplicity. Rejected attempts are not dropped from the observation. -/
theorem physicalReads_exact (model : InputModel) (ts : List Transition) :
    (physicalReads model ts).map Read.logicalReceipt = ts.filterMap Transition.read? := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    unfold physicalReads at ih ⊢
    simp only [List.filterMap_cons, physicalRead]
    cases hr : t.read? with
    | none => simpa [hr] using ih
    | some r =>
      cases r
      simpa [hr, translateRead, Read.logicalReceipt] using ih

structure ImageTransition where
  before : List (Option Nat)
  action : Action
  after : List (Option Nat)

def imageTransition (model : InputModel) (t : Transition) : ImageTransition :=
  ⟨view model t.before, t.action, view model t.after⟩

def imageTrace (model : InputModel) (ts : List Transition) : List ImageTransition :=
  ts.map (imageTransition model)

theorem imageTrace_length (model : InputModel) (ts : List Transition) :
    (imageTrace model ts).length = ts.length := by simp [imageTrace]

theorem imageTrace_actions (model : InputModel) (ts : List Transition) :
    (imageTrace model ts).map (·.action) = ts.map (·.action) := by
  simp [imageTrace, List.map_map, imageTransition]

theorem image_occurrence (model : InputModel) (ts : List Transition) (k : Nat) (t : Transition)
    (occurs : ts[k]? = some t) :
    (imageTrace model ts)[k]? = some ⟨view model t.before, t.action, view model t.after⟩ := by
  simp [imageTrace, List.getElem?_map, occurs, imageTransition]

/-- The whole actual instruction run supplies the producing prefix state;
there is no restart or suffix-only replay in this positional statement. -/
theorem run_read_at (model : InputModel) (program : List Instruction) (fuel : Nat) (s : State)
    (k : Nat) (t : Transition) (a : Nat) (reply : Option Nat)
    (occurs : (run program fuel s).transitions[k]? = some t)
    (read : t.read? = some (a, reply)) :
    t.before = (run program k s).final ∧
      (imageTrace model (run program fuel s).transitions)[k]? =
        some ⟨view model (run program k s).final, t.action, view model t.after⟩ ∧
      reply = lookup model (run program k s).final (arenaAddress model a) ∧
      physicalRead model t = some (translateRead model (run program k s).final (a, reply)) := by
  have before := (PackedLifecycle.run_transition_at occurs).1
  refine ⟨before, ?_, ?_, ?_⟩
  · simpa only [← before] using image_occurrence model _ k t occurs
  · rw [← before]; exact (read_provenance model t a reply read).1
  · simp [physicalRead, read, before]

theorem whole_trace_width (model : InputModel) (n : Nat) (ts : List Transition)
    (fits : ∀ t ∈ ts, t.before.Fits (PackedWordRAM.wordWidth n) ∧
      t.after.Fits (PackedWordRAM.wordWidth n))
    (peak : ∀ t ∈ ts, t.before.core.extent ≤ 5000000 * (n + 1) ∧
      t.after.core.extent ≤ 5000000 * (n + 1)) :
    ∀ (k : Nat) (t : Transition), ts[k]? = some t →
      (view model t.before).length < 2 ^ PackedWordRAM.wordWidth n ∧
      (view model t.after).length < 2 ^ PackedWordRAM.wordWidth n ∧
      (∀ p value, lookup model t.before p = some value → value < 2 ^ PackedWordRAM.wordWidth n) ∧
      (∀ p value, lookup model t.after p = some value → value < 2 ^ PackedWordRAM.wordWidth n) ∧
      (∀ a reply, t.read? = some (a, reply) →
        a < 2 ^ PackedWordRAM.wordWidth n ∧
        (∀ p, checkedAddress model t.before a = some p → p < 2 ^ PackedWordRAM.wordWidth n) ∧
        (∀ value, reply = some value → value < 2 ^ PackedWordRAM.wordWidth n)) := by
  intro k t occurs
  have member := List.mem_of_getElem? occurs
  have hf := fits t member
  have hp := peak t member
  refine ⟨?_, ?_, lookup_word_fits model n t.before hf.1,
    lookup_word_fits model n t.after hf.2, ?_⟩
  · rw [view_length]; exact extent_fit model n t.before hp.1
  · rw [view_length]; exact extent_fit model n t.after hp.2
  · intro a reply read; exact read_width model n t a reply read hf.1 hp.1

/-- The actual finite array owner has exactly the same arena lookup, including
absent and uninitialized cells. Comparison bank sizes remain separate. -/
theorem owner_closed (owner : Owner) : owner.toState.Closed := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    change owner.memory.getD a none = none
    change owner.memory.size ≤ a at ha
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha]
  · intro a ha
    change owner.keys.getD a none = none
    change owner.keys.size ≤ a at ha
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none ha]
  · intro r hr
    change owner.keyRegs.getD r 0 = 0
    change owner.keyRegs.size ≤ r at hr
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hr]

theorem owner_arena (model : InputModel) (owner : Owner) (a : Nat) :
    lookup model owner.toState (arenaAddress model a) = owner.memory.getD a none :=
  lookup_arena_closed model owner.toState (owner_closed owner) a

theorem owner_numeric_bank (owner : Owner) (size : owner.regs.size = numericBank) :
    ∀ r, numericBank ≤ r → owner.toState.core.regs r = 0 := by
  intro r hr
  change owner.regs.getD r 0 = 0
  have outside : owner.regs.size ≤ r := by omega
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none outside]

theorem executeArray_image (model : InputModel) (i : Instruction) (owner : Owner)
    (fits : i.DestinationsFit owner) :
    view model (executeArray i owner).toState = view model (execute i owner.toState) := by
  rw [executeArray_toState i owner fits]

theorem executeBoundaryArray_image (model : InputModel) (b : Boundary) (owner : Owner)
    (fits : b.DestinationsFit owner) :
    view model (executeBoundaryArray b owner).toState = view model (executeBoundary b owner.toState) := by
  rw [executeBoundaryArray_toState b owner fits]

theorem runArray_image (model : InputModel) (program : List Instruction) (fuel : Nat) (owner : Owner)
    (fits : RunDestinationsFit program.toArray fuel owner) :
    imageTrace model ((runArray program.toArray fuel owner).toRun.transitions) =
      imageTrace model (run program fuel owner.toState).transitions ∧
      view model (runArray program.toArray fuel owner).final.toState =
        view model (run program fuel owner.toState).final := by
  have exactRun := runArray_toState program fuel owner fits
  refine ⟨by rw [exactRun], ?_⟩
  exact congrArg (fun r : Run => view model r.final) exactRun

/-- Int comparison values are deliberately not recoded as numeric W-bit words.
Only their separately owned extents occupy numeric control words. -/
theorem oracle_values_irrelevant (model : InputModel) (s : State)
    (keys : Nat → Option Int) (keyRegs : Nat → Int) :
    view model { s with core := { s.core with keys := keys, keyRegs := keyRegs } } = view model s := by
  have controls : control { s with core := { s.core with keys := keys, keyRegs := keyRegs } } =
      control s := by
    funext i
    unfold control
    split <;> rfl
  have lookups : lookup model { s with core := { s.core with keys := keys, keyRegs := keyRegs } } =
      lookup model s := by
    funext p
    unfold lookup
    rw [controls]
    rfl
  exact congrArg (fun f : Fin (extent model s) → Option Nat => List.ofFn f)
    (funext (fun p => congrFun lookups p.val))

theorem canonical_capacity (model : InputModel) (xs : List Int) (s : State)
    (canonical : Retained.Canonical xs s) :
    (wordView model s).map some = view model s ∧
      (wordView model s).length * PackedWordRAM.wordWidth xs.length ≤
        2 * xs.length + retainedRho xs.length := by
  refine ⟨wordView_exact model s (canonical_initialized canonical), ?_⟩
  have count : (wordView model s).length = (PackedWordRAM.buildMemory xs).length +
      (encodedProgram model).length + numericBank + controlWords := by
    simp only [wordView, List.length_map, view_length, extent, arenaBase, controlBase,
      registerBase, codeLength, canonical.1.2.1]
    omega
  rw [count]
  exact retained_capacity model xs

end RMQ.SuccinctFinal.PackedLifecycle.Physical
