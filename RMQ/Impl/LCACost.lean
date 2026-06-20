import RMQ.Core.Cost
import RMQ.Core.RAM
import RMQ.Core.SuccinctReduction
import RMQ.Core.TableModel
import RMQ.Core.Reduction

/-!
# Costed LCA bridge scaffolding

This module gives the first costed wrapper around the existing LCA-via-RMQ
correctness layer.  The costs are model-level charges: building an Euler trace
is charged by the depth-list length, and a supplied LCA backend query is charged
as one abstract backend query.
-/

namespace RMQ

namespace LCACost

/-- Model cost charged to materialize a generated Euler trace. -/
def eulerTraceBuildCost (tree : RoseTree) : Nat :=
  tree.eulerTrace.depths.length

/-- Costed generated Euler-trace construction. -/
def eulerTraceCosted (tree : RoseTree) : Costed EulerTrace :=
  Costed.tickValue (eulerTraceBuildCost tree) tree.eulerTrace

theorem eulerTraceCosted_erase (tree : RoseTree) :
    (eulerTraceCosted tree).erase = tree.eulerTrace := by
  rfl

theorem eulerTraceCosted_cost (tree : RoseTree) :
    (eulerTraceCosted tree).cost = eulerTraceBuildCost tree := by
  rfl

theorem eulerTraceCosted_run (tree : RoseTree) :
    (eulerTraceCosted tree).run =
      (tree.eulerTrace, eulerTraceBuildCost tree) := by
  rfl

/-- First-occurrence table, modeled as a unit-cost indexed access by node label. -/
def firstOccurrenceIndex (trace : EulerTrace) :
    TableModel.IndexedAccess Nat Nat where
  get? node := trace.firstOccurrence? node

@[simp] theorem firstOccurrenceIndex_get?
    (trace : EulerTrace) (node : Nat) :
    (firstOccurrenceIndex trace).get? node = trace.firstOccurrence? node := by
  rfl

/-- Costed lookup in the modeled first-occurrence table. -/
def firstOccurrenceCosted (trace : EulerTrace) (node : Nat) :
    Costed (Option Nat) :=
  (firstOccurrenceIndex trace).getCosted node

@[simp] theorem firstOccurrenceCosted_erase
    (trace : EulerTrace) (node : Nat) :
    (firstOccurrenceCosted trace node).erase =
      trace.firstOccurrence? node := by
  rfl

theorem firstOccurrenceCosted_cost
    (trace : EulerTrace) (node : Nat) :
    (firstOccurrenceCosted trace node).cost =
      TableModel.indexedReadCost := by
  rfl

theorem firstOccurrenceCosted_run
    (trace : EulerTrace) (node : Nat) :
    (firstOccurrenceCosted trace node).run =
      (trace.firstOccurrence? node, TableModel.indexedReadCost) := by
  rfl

/--
Direct-address first-occurrence rows for dense natural-number labels.

This is a semantic table view, not yet a costed construction theorem: row
`label` stores the first Euler occurrence of node label `label`.
-/
def firstOccurrenceDirectRows (tree : RoseTree) :
    List (Option Nat) :=
  (List.range tree.labelsPreorder.length).map fun label =>
    tree.eulerTrace.firstOccurrence? label

/-- Direct-address first-occurrence slots as a finite indexed sequence. -/
def firstOccurrenceDirectSlots (tree : RoseTree) :
    TableModel.IndexedSeq (Option Nat) :=
  TableModel.IndexedSeq.ofList (firstOccurrenceDirectRows tree)

/-- Array-backed direct-address first-occurrence store. -/
def firstOccurrenceDirectStore (tree : RoseTree) :
    TableModel.StoredSeq (Option Nat) (firstOccurrenceDirectRows tree) :=
  TableModel.StoredSeq.ofList (firstOccurrenceDirectRows tree)

@[simp] theorem firstOccurrenceDirectRows_length
    (tree : RoseTree) :
    (firstOccurrenceDirectRows tree).length =
      tree.labelsPreorder.length := by
  unfold firstOccurrenceDirectRows
  simp

@[simp] theorem firstOccurrenceDirectSlots_length
    (tree : RoseTree) :
    (firstOccurrenceDirectSlots tree).length =
      tree.labelsPreorder.length := by
  unfold firstOccurrenceDirectSlots
  simp

@[simp] theorem firstOccurrenceDirectStore_erases
    (tree : RoseTree) :
    (firstOccurrenceDirectStore tree).repr.toList =
      firstOccurrenceDirectRows tree := by
  exact TableModel.StoredSeq.erases_eq (firstOccurrenceDirectStore tree)

theorem firstOccurrenceDirectSlots_get?_of_lt
    (tree : RoseTree) {label : Nat}
    (hlabel : label < tree.labelsPreorder.length) :
    (firstOccurrenceDirectSlots tree).get? label =
      some (tree.eulerTrace.firstOccurrence? label) := by
  unfold firstOccurrenceDirectSlots firstOccurrenceDirectRows
  simp [List.getElem?_map, List.getElem?_range hlabel]

theorem firstOccurrenceDirectSlots_get?_of_ge
    (tree : RoseTree) {label : Nat}
    (hlabel : tree.labelsPreorder.length <= label) :
    (firstOccurrenceDirectSlots tree).get? label = none := by
  unfold firstOccurrenceDirectSlots
  change (firstOccurrenceDirectRows tree)[label]? = none
  exact List.getElem?_eq_none (by simpa using hlabel)

theorem firstOccurrenceDirectStore_get?_of_lt
    (tree : RoseTree) {label : Nat}
    (hlabel : label < tree.labelsPreorder.length) :
    Refine.StoredSeq.get? (firstOccurrenceDirectStore tree) label =
      some (tree.eulerTrace.firstOccurrence? label) := by
  rw [TableModel.StoredSeq.get?_eq_absGet?]
  unfold Refine.StoredSeq.absGet?
  simpa [firstOccurrenceDirectSlots] using
    firstOccurrenceDirectSlots_get?_of_lt tree hlabel

theorem firstOccurrenceDirectStore_get?_of_ge
    (tree : RoseTree) {label : Nat}
    (hlabel : tree.labelsPreorder.length <= label) :
    Refine.StoredSeq.get? (firstOccurrenceDirectStore tree) label = none := by
  rw [TableModel.StoredSeq.get?_eq_absGet?]
  unfold Refine.StoredSeq.absGet?
  exact List.getElem?_eq_none (by
    rw [firstOccurrenceDirectRows_length]
    exact hlabel)

theorem firstOccurrence?_eq_none_of_ge_labelsPreorder_length
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    {label : Nat} (hge : tree.labelsPreorder.length <= label) :
    tree.eulerTrace.firstOccurrence? label = none := by
  cases hfirst : tree.eulerTrace.firstOccurrence? label with
  | none => rfl
  | some idx =>
      have hnodes : label ∈ tree.eulerTrace.nodes := by
        exact firstIndexOf?_mem (by
          simpa [EulerTrace.firstOccurrence?] using hfirst)
      have hlabels : label ∈ tree.labelsPreorder := by
        apply RoseTree.mem_labelsPreorder_of_mem_eulerNodes
        simpa [RoseTree.eulerTrace, RoseTree.eulerTraceAt] using hnodes
      have hlt : label < tree.labelsPreorder.length :=
        hbounded label hlabels
      exact False.elim ((Nat.not_lt_of_ge hge) hlt)

/--
Direct-address first-occurrence table as a modeled indexed access.  Labels
outside the stored range return `none`; boundedness proves that matches the
generated Euler trace semantics for all labels.
-/
def firstOccurrenceDirectIndex (tree : RoseTree) :
    TableModel.IndexedAccess Nat Nat where
  get? label := (Refine.StoredSeq.get?
    (firstOccurrenceDirectStore tree) label).join

theorem firstOccurrenceDirectIndex_get?_of_bounded
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    (firstOccurrenceDirectIndex tree).get? label =
      tree.eulerTrace.firstOccurrence? label := by
  unfold firstOccurrenceDirectIndex
  change (Refine.StoredSeq.get?
      (firstOccurrenceDirectStore tree) label).join =
    tree.eulerTrace.firstOccurrence? label
  by_cases hlt : label < tree.labelsPreorder.length
  · rw [firstOccurrenceDirectStore_get?_of_lt tree hlt]
    simp
  · have hge : tree.labelsPreorder.length <= label :=
      Nat.le_of_not_gt hlt
    rw [firstOccurrenceDirectStore_get?_of_ge tree hge,
      firstOccurrence?_eq_none_of_ge_labelsPreorder_length
        tree hbounded hge]
    rfl

/-- Costed lookup in the direct-address first-occurrence table. -/
def firstOccurrenceDirectCosted (tree : RoseTree) (label : Nat) :
    Costed (Option Nat) :=
  (firstOccurrenceDirectIndex tree).getCosted label

@[simp] theorem firstOccurrenceDirectCosted_erase_of_bounded
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    (firstOccurrenceDirectCosted tree label).erase =
      tree.eulerTrace.firstOccurrence? label := by
  unfold firstOccurrenceDirectCosted
  simp [firstOccurrenceDirectIndex_get?_of_bounded tree hbounded label]

@[simp] theorem firstOccurrenceDirectCosted_value_of_bounded
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    (firstOccurrenceDirectCosted tree label).value =
      tree.eulerTrace.firstOccurrence? label := by
  simpa [Costed.erase] using
    firstOccurrenceDirectCosted_erase_of_bounded tree hbounded label

theorem firstOccurrenceDirectCosted_cost
    (tree : RoseTree) (label : Nat) :
    (firstOccurrenceDirectCosted tree label).cost =
      TableModel.indexedReadCost := by
  rfl

theorem firstOccurrenceDirectCosted_run_of_bounded
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    (firstOccurrenceDirectCosted tree label).run =
      (tree.eulerTrace.firstOccurrence? label, TableModel.indexedReadCost) := by
  simp [Costed.run, firstOccurrenceDirectCosted_value_of_bounded
    tree hbounded label, firstOccurrenceDirectCosted_cost]

theorem firstOccurrenceDirectCosted_eq_firstOccurrenceCosted_of_bounded
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    firstOccurrenceDirectCosted tree label =
      firstOccurrenceCosted tree.eulerTrace label := by
  unfold firstOccurrenceDirectCosted firstOccurrenceCosted
    TableModel.IndexedAccess.getCosted Costed.tickValue firstOccurrenceIndex
  simp [firstOccurrenceDirectIndex_get?_of_bounded tree hbounded label]

/-- Reference update: record `idx` as `label`'s first occurrence if absent. -/
def setFirstIfNoneList
    (slots : List (Option Nat)) (label idx : Nat) :
    List (Option Nat) :=
  match slots[label]? with
  | none => slots.set label (some idx)
  | some none => slots.set label (some idx)
  | some (some _) => slots

theorem setFirstIfNoneList_length
    (slots : List (Option Nat)) (label idx : Nat) :
    (setFirstIfNoneList slots label idx).length = slots.length := by
  unfold setFirstIfNoneList
  cases h : slots[label]?
  · simp
  case some current =>
    cases current
    · simp
    · rfl

theorem setFirstIfNoneList_get?_ne
    {slots : List (Option Nat)} {label target idx : Nat}
    (hne : label ≠ target) :
    (setFirstIfNoneList slots label idx)[target]? = slots[target]? := by
  unfold setFirstIfNoneList
  cases h : slots[label]?
  · rw [List.getElem?_set]
    simp [hne]
  case some current =>
    cases current
    · rw [List.getElem?_set]
      simp [hne]
    · rfl

theorem setFirstIfNoneList_get?_same_of_none
    {slots : List (Option Nat)} {label idx : Nat}
    (hslot : slots[label]? = some none) :
    (setFirstIfNoneList slots label idx)[label]? = some (some idx) := by
  have hlt : label < slots.length := by
    rcases List.getElem?_eq_some_iff.mp hslot with ⟨h, _⟩
    exact h
  have hvalue : slots[label] = none :=
    (List.getElem?_eq_some_iff.mp hslot).2
  have hset : setFirstIfNoneList slots label idx =
      slots.set label (some idx) := by
    unfold setFirstIfNoneList
    simp [hslot]
  rw [hset]
  simp [hlt]

theorem setFirstIfNoneList_preserves_some
    {slots : List (Option Nat)} {label target idx found : Nat}
    (hslot : slots[target]? = some (some found)) :
    (setFirstIfNoneList slots label idx)[target]? = some (some found) := by
  unfold setFirstIfNoneList
  cases hlabel : slots[label]? with
  | none =>
      by_cases heq : label = target
      · subst label
        rw [hslot] at hlabel
        cases hlabel
      · rw [List.getElem?_set]
        simp [heq, hslot]
  | some current =>
      cases current with
      | none =>
          by_cases heq : label = target
          · subst label
            rw [hslot] at hlabel
            cases hlabel
          · rw [List.getElem?_set]
            simp [heq, hslot]
      | some old =>
          exact hslot

/--
Reference first-occurrence-table builder over an Euler-node suffix.  `idx`
tracks the absolute Euler position of the head of `nodes`.
-/
def firstOccurrenceRowsFromNodes :
    List Nat -> Nat -> List (Option Nat) -> List (Option Nat)
  | [], _idx, slots => slots
  | label :: rest, idx, slots =>
      firstOccurrenceRowsFromNodes rest (idx + 1)
        (setFirstIfNoneList slots label idx)

theorem firstOccurrenceRowsFromNodes_preserves_some
    (nodes : List Nat) (idx : Nat) {slots : List (Option Nat)}
    {target found : Nat}
    (hslot : slots[target]? = some (some found)) :
    (firstOccurrenceRowsFromNodes nodes idx slots)[target]? =
      some (some found) := by
  induction nodes generalizing idx slots with
  | nil =>
      simpa [firstOccurrenceRowsFromNodes] using hslot
  | cons label rest ih =>
      unfold firstOccurrenceRowsFromNodes
      exact ih (idx + 1)
        (setFirstIfNoneList_preserves_some (label := label) hslot)

theorem firstOccurrenceRowsFromNodes_get?_of_none
    (nodes : List Nat) (idx : Nat) {slots : List (Option Nat)}
    {target : Nat}
    (hslot : slots[target]? = some none) :
    (firstOccurrenceRowsFromNodes nodes idx slots)[target]? =
      some ((firstIndexOf? target nodes).map fun offset => idx + offset) := by
  induction nodes generalizing idx slots with
  | nil =>
      simp [firstOccurrenceRowsFromNodes, firstIndexOf?, hslot]
  | cons label rest ih =>
      by_cases hlabel : label = target
      · subst label
        have hset :
            (setFirstIfNoneList slots target idx)[target]? =
              some (some idx) :=
          setFirstIfNoneList_get?_same_of_none hslot
        have hpreserve :=
          firstOccurrenceRowsFromNodes_preserves_some rest (idx + 1) hset
        simpa [firstOccurrenceRowsFromNodes, firstIndexOf?] using hpreserve
      · have hset :
            (setFirstIfNoneList slots label idx)[target]? = some none := by
          rw [setFirstIfNoneList_get?_ne hlabel, hslot]
        have htail := ih (idx + 1) hset
        cases hfirst : firstIndexOf? target rest with
        | none =>
            simpa [firstOccurrenceRowsFromNodes, firstIndexOf?, hlabel,
              hfirst] using htail
        | some offset =>
            simpa [firstOccurrenceRowsFromNodes, firstIndexOf?, hlabel,
              hfirst, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem firstOccurrenceRowsFromNodes_replicate_get?_of_lt
    (nodes : List Nat) {n label : Nat} (hlabel : label < n) :
    (firstOccurrenceRowsFromNodes nodes 0
        (List.replicate n none))[label]? =
      some (firstIndexOf? label nodes) := by
  have hslot :
      (List.replicate n (none : Option Nat))[label]? = some none := by
    simp [hlabel]
  simpa using
    (firstOccurrenceRowsFromNodes_get?_of_none
      nodes 0 (slots := List.replicate n none)
      (target := label) hslot)

theorem firstOccurrenceRowsFromNodes_length
    (nodes : List Nat) (idx : Nat) (slots : List (Option Nat)) :
    (firstOccurrenceRowsFromNodes nodes idx slots).length = slots.length := by
  induction nodes generalizing idx slots with
  | nil =>
      simp [firstOccurrenceRowsFromNodes]
  | cons label rest ih =>
      simp [firstOccurrenceRowsFromNodes, ih,
        setFirstIfNoneList_length]

theorem firstOccurrenceRowsFromNodes_replicate_length
    (nodes : List Nat) (n : Nat) :
    (firstOccurrenceRowsFromNodes nodes 0
      (List.replicate n (none : Option Nat))).length = n := by
  simp [firstOccurrenceRowsFromNodes_length]

private theorem replicate_append_singleton
    (n : Nat) (x : α) :
    List.replicate n x ++ [x] = List.replicate (n + 1) x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp [List.replicate_succ, ih]

/-- Counted initialization of a dense first-occurrence slot array. -/
def initFirstOccurrenceSlots : Nat -> RAM.Exec (Array (Option Nat))
  | 0 => RAM.allocArray #[]
  | n + 1 =>
      RAM.Exec.bind (initFirstOccurrenceSlots n) fun slots =>
        RAM.pushArray slots none

theorem initFirstOccurrenceSlots_value_toList (n : Nat) :
    (initFirstOccurrenceSlots n).value.toList =
      List.replicate n none := by
  induction n with
  | zero =>
      simp [initFirstOccurrenceSlots, RAM.allocArray]
  | succ n ih =>
      simp [initFirstOccurrenceSlots, RAM.Exec.bind, ih,
        replicate_append_singleton]

theorem initFirstOccurrenceSlots_steps (n : Nat) :
    (initFirstOccurrenceSlots n).steps = n + 1 := by
  induction n with
  | zero =>
      simp [initFirstOccurrenceSlots]
  | succ n ih =>
      simp [initFirstOccurrenceSlots, RAM.Exec.steps_bind, ih]

/-- Counted one-node first-occurrence update. -/
def recordFirstOccurrence
    (slots : Array (Option Nat)) (label idx : Nat) :
    RAM.Exec (Array (Option Nat)) :=
  RAM.Exec.bind (RAM.readArray? slots label) fun current =>
    RAM.Exec.bind (RAM.branch current.isNone) fun _ =>
      match current with
      | none => RAM.writeArray? slots label (some idx)
      | some none => RAM.writeArray? slots label (some idx)
      | some (some _) => RAM.Exec.pure slots

theorem recordFirstOccurrence_value_toList
    (slots : Array (Option Nat)) (label idx : Nat) :
    (recordFirstOccurrence slots label idx).value.toList =
      setFirstIfNoneList slots.toList label idx := by
  unfold recordFirstOccurrence setFirstIfNoneList
  cases hget : slots[label]? with
  | none =>
      have hlist : slots.toList[label]? = none := by
        simpa [Array.getElem?_toList] using hget
      simp [RAM.Exec.bind, hget, hlist, RAM.writeArray?,
        Array.toList_setIfInBounds]
  | some current =>
      have hlist : slots.toList[label]? = some current := by
        simpa [Array.getElem?_toList] using hget
      cases current with
      | none =>
          simp [RAM.Exec.bind, hget, hlist, RAM.writeArray?,
            Array.toList_setIfInBounds]
      | some old =>
          simp [RAM.Exec.bind, hget, hlist]

theorem recordFirstOccurrence_steps_le_three
    (slots : Array (Option Nat)) (label idx : Nat) :
    (recordFirstOccurrence slots label idx).steps <= 3 := by
  unfold recordFirstOccurrence
  cases hget : slots[label]? with
  | none =>
      simp [RAM.Exec.steps_bind, hget]
  | some current =>
      cases current with
      | none =>
          simp [RAM.Exec.steps_bind, hget]
      | some old =>
          simp [RAM.Exec.steps_bind, hget]

/-- Counted scan of Euler nodes into a first-occurrence slot array. -/
def buildFirstOccurrenceSlotsFromNodes :
    List Nat -> Nat -> Array (Option Nat) -> RAM.Exec (Array (Option Nat))
  | [], _idx, slots => RAM.Exec.pure slots
  | label :: rest, idx, slots =>
      RAM.Exec.bind (recordFirstOccurrence slots label idx) fun slots' =>
        buildFirstOccurrenceSlotsFromNodes rest (idx + 1) slots'

theorem buildFirstOccurrenceSlotsFromNodes_value_toList
    (nodes : List Nat) (idx : Nat) (slots : Array (Option Nat)) :
    (buildFirstOccurrenceSlotsFromNodes nodes idx slots).value.toList =
      firstOccurrenceRowsFromNodes nodes idx slots.toList := by
  induction nodes generalizing idx slots with
  | nil =>
      simp [buildFirstOccurrenceSlotsFromNodes, firstOccurrenceRowsFromNodes]
  | cons label rest ih =>
      simp [buildFirstOccurrenceSlotsFromNodes, firstOccurrenceRowsFromNodes,
        RAM.Exec.bind, ih, recordFirstOccurrence_value_toList]

theorem buildFirstOccurrenceSlotsFromNodes_steps_le
    (nodes : List Nat) (idx : Nat) (slots : Array (Option Nat)) :
    (buildFirstOccurrenceSlotsFromNodes nodes idx slots).steps <=
      3 * nodes.length := by
  induction nodes generalizing idx slots with
  | nil =>
      simp [buildFirstOccurrenceSlotsFromNodes]
  | cons label rest ih =>
      unfold buildFirstOccurrenceSlotsFromNodes
      simp [RAM.Exec.steps_bind]
      have hrecord := recordFirstOccurrence_steps_le_three slots label idx
      have htail :=
        ih (idx + 1) (recordFirstOccurrence slots label idx).value
      omega

/-- Counted dense first-occurrence array builder over a generated Euler trace. -/
def buildFirstOccurrenceDirectArray (tree : RoseTree) :
    RAM.Exec (Array (Option Nat)) :=
  RAM.Exec.bind
    (initFirstOccurrenceSlots tree.labelsPreorder.length) fun slots =>
      buildFirstOccurrenceSlotsFromNodes tree.eulerTrace.nodes 0 slots

theorem buildFirstOccurrenceDirectArray_value_toReference
    (tree : RoseTree) :
    (buildFirstOccurrenceDirectArray tree).value.toList =
      firstOccurrenceRowsFromNodes tree.eulerTrace.nodes 0
        (List.replicate tree.labelsPreorder.length none) := by
  unfold buildFirstOccurrenceDirectArray
  simp [RAM.Exec.bind, buildFirstOccurrenceSlotsFromNodes_value_toList,
    initFirstOccurrenceSlots_value_toList]

theorem buildFirstOccurrenceDirectArray_steps_le
    (tree : RoseTree) :
    (buildFirstOccurrenceDirectArray tree).steps <=
      tree.labelsPreorder.length + 1 + 3 * tree.eulerTrace.nodes.length := by
  unfold buildFirstOccurrenceDirectArray
  simp [RAM.Exec.steps_bind]
  have hinit := initFirstOccurrenceSlots_steps tree.labelsPreorder.length
  have hscan :=
    buildFirstOccurrenceSlotsFromNodes_steps_le tree.eulerTrace.nodes 0
      (initFirstOccurrenceSlots tree.labelsPreorder.length).value
  omega

theorem firstOccurrenceRowsFromNodes_replicate_eq_directRows
    (tree : RoseTree) :
    firstOccurrenceRowsFromNodes tree.eulerTrace.nodes 0
        (List.replicate tree.labelsPreorder.length none) =
      firstOccurrenceDirectRows tree := by
  apply List.ext_getElem?
  intro label
  by_cases hlabel : label < tree.labelsPreorder.length
  · have hleft :=
      firstOccurrenceRowsFromNodes_replicate_get?_of_lt
        tree.eulerTrace.nodes hlabel
    have hright :
        (firstOccurrenceDirectRows tree)[label]? =
          some (tree.eulerTrace.firstOccurrence? label) := by
      unfold firstOccurrenceDirectRows
      simp [List.getElem?_map, List.getElem?_range hlabel]
    rw [hleft, hright]
    rfl
  · have hge : tree.labelsPreorder.length <= label :=
      Nat.le_of_not_gt hlabel
    have hleft :
        (firstOccurrenceRowsFromNodes tree.eulerTrace.nodes 0
            (List.replicate tree.labelsPreorder.length none))[label]? =
          none := by
      exact List.getElem?_eq_none (by
        rw [firstOccurrenceRowsFromNodes_replicate_length]
        exact hge)
    have hright : (firstOccurrenceDirectRows tree)[label]? = none := by
      exact List.getElem?_eq_none (by
        rw [firstOccurrenceDirectRows_length]
        exact hge)
    rw [hleft, hright]

theorem buildFirstOccurrenceDirectArray_value_toRows
    (tree : RoseTree) :
    (buildFirstOccurrenceDirectArray tree).value.toList =
      firstOccurrenceDirectRows tree := by
  rw [buildFirstOccurrenceDirectArray_value_toReference,
    firstOccurrenceRowsFromNodes_replicate_eq_directRows]

theorem buildFirstOccurrenceDirectArray_refines_with_steps
    (tree : RoseTree) :
    (buildFirstOccurrenceDirectArray tree).value.toList =
        firstOccurrenceDirectRows tree ∧
      (buildFirstOccurrenceDirectArray tree).steps <=
        tree.labelsPreorder.length + 1 + 3 * tree.eulerTrace.nodes.length := by
  exact ⟨buildFirstOccurrenceDirectArray_value_toRows tree,
    buildFirstOccurrenceDirectArray_steps_le tree⟩

/-- Stored dense first-occurrence table produced by the counted builder. -/
def builtFirstOccurrenceDirectStore (tree : RoseTree) :
    TableModel.StoredSeq (Option Nat) (firstOccurrenceDirectRows tree) where
  repr := (buildFirstOccurrenceDirectArray tree).value
  erases := buildFirstOccurrenceDirectArray_value_toRows tree

@[simp] theorem builtFirstOccurrenceDirectStore_erases
    (tree : RoseTree) :
    (builtFirstOccurrenceDirectStore tree).repr.toList =
      firstOccurrenceDirectRows tree := by
  exact TableModel.StoredSeq.erases_eq (builtFirstOccurrenceDirectStore tree)

theorem builtFirstOccurrenceDirectStore_get?_of_lt
    (tree : RoseTree) {label : Nat}
    (hlabel : label < tree.labelsPreorder.length) :
    Refine.StoredSeq.get? (builtFirstOccurrenceDirectStore tree) label =
      some (tree.eulerTrace.firstOccurrence? label) := by
  rw [TableModel.StoredSeq.get?_eq_absGet?]
  unfold Refine.StoredSeq.absGet?
  unfold firstOccurrenceDirectRows
  simp [List.getElem?_map, List.getElem?_range hlabel]

theorem builtFirstOccurrenceDirectStore_get?_of_ge
    (tree : RoseTree) {label : Nat}
    (hlabel : tree.labelsPreorder.length <= label) :
    Refine.StoredSeq.get? (builtFirstOccurrenceDirectStore tree) label =
      none := by
  rw [TableModel.StoredSeq.get?_eq_absGet?]
  unfold Refine.StoredSeq.absGet?
  exact List.getElem?_eq_none (by
    rw [firstOccurrenceDirectRows_length]
    exact hlabel)

/-- Direct-address first-occurrence indexed access backed by the counted builder. -/
def builtFirstOccurrenceDirectIndex (tree : RoseTree) :
    TableModel.IndexedAccess Nat Nat where
  get? label := (Refine.StoredSeq.get?
    (builtFirstOccurrenceDirectStore tree) label).join

theorem builtFirstOccurrenceDirectIndex_get?_of_bounded
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    (builtFirstOccurrenceDirectIndex tree).get? label =
      tree.eulerTrace.firstOccurrence? label := by
  unfold builtFirstOccurrenceDirectIndex
  change (Refine.StoredSeq.get?
      (builtFirstOccurrenceDirectStore tree) label).join =
    tree.eulerTrace.firstOccurrence? label
  by_cases hlt : label < tree.labelsPreorder.length
  · rw [builtFirstOccurrenceDirectStore_get?_of_lt tree hlt]
    simp
  · have hge : tree.labelsPreorder.length <= label :=
      Nat.le_of_not_gt hlt
    rw [builtFirstOccurrenceDirectStore_get?_of_ge tree hge,
      firstOccurrence?_eq_none_of_ge_labelsPreorder_length
        tree hbounded hge]
    rfl

/-- Costed lookup in the counted-builder-backed direct-address table. -/
def builtFirstOccurrenceDirectCosted (tree : RoseTree) (label : Nat) :
    Costed (Option Nat) :=
  (builtFirstOccurrenceDirectIndex tree).getCosted label

theorem builtFirstOccurrenceDirectCosted_eq_firstOccurrenceCosted_of_bounded
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    builtFirstOccurrenceDirectCosted tree label =
      firstOccurrenceCosted tree.eulerTrace label := by
  unfold builtFirstOccurrenceDirectCosted firstOccurrenceCosted
    TableModel.IndexedAccess.getCosted Costed.tickValue firstOccurrenceIndex
  simp [builtFirstOccurrenceDirectIndex_get?_of_bounded
    tree hbounded label]

/-- Euler-tour node list as a finite modeled indexed sequence. -/
def nodeIndex (trace : EulerTrace) : TableModel.IndexedSeq Nat :=
  TableModel.IndexedSeq.ofList trace.nodes

@[simp] theorem nodeIndex_length (trace : EulerTrace) :
    (nodeIndex trace).length = trace.nodes.length := by
  rfl

@[simp] theorem nodeIndex_get? (trace : EulerTrace) (idx : Nat) :
    (nodeIndex trace).get? idx = trace.nodes[idx]? := by
  rfl

/-- Euler-depth list as a finite modeled indexed sequence. -/
def depthIndex (trace : EulerTrace) : TableModel.IndexedSeq Int :=
  TableModel.IndexedSeq.ofList trace.depths

@[simp] theorem depthIndex_length (trace : EulerTrace) :
    (depthIndex trace).length = trace.depths.length := by
  rfl

@[simp] theorem depthIndex_get? (trace : EulerTrace) (idx : Nat) :
    (depthIndex trace).get? idx = trace.depths[idx]? := by
  rfl

theorem nodeIndex_length_eq_depthIndex_length (trace : EulerTrace) :
    (nodeIndex trace).length = (depthIndex trace).length := by
  exact trace.length_eq

/-- Counted materialization of the Euler-tour node list. -/
def buildNodeArray (trace : EulerTrace) : RAM.Exec (Array Nat) :=
  RAM.arrayOfList trace.nodes

@[simp] theorem buildNodeArray_value_toList (trace : EulerTrace) :
    (buildNodeArray trace).value.toList = trace.nodes := by
  exact RAM.arrayOfList_value_toList trace.nodes

@[simp] theorem buildNodeArray_steps (trace : EulerTrace) :
    (buildNodeArray trace).steps = trace.nodes.length + 1 := by
  exact RAM.arrayOfList_steps trace.nodes

theorem buildNodeArray_refines_with_steps (trace : EulerTrace) :
    (buildNodeArray trace).value.toList = trace.nodes ∧
      (buildNodeArray trace).steps = trace.nodes.length + 1 := by
  exact RAM.arrayOfList_refines_with_steps trace.nodes

/-- Stored Euler-node view produced by the counted builder. -/
def builtNodeStore (trace : EulerTrace) :
    TableModel.StoredSeq Nat trace.nodes where
  repr := (buildNodeArray trace).value
  erases := buildNodeArray_value_toList trace

@[simp] theorem builtNodeStore_erases (trace : EulerTrace) :
    (builtNodeStore trace).repr.toList = trace.nodes := by
  exact TableModel.StoredSeq.erases_eq (builtNodeStore trace)

/-- Euler-tour node indexed sequence backed by the counted node-array builder. -/
def builtNodeIndex (trace : EulerTrace) : TableModel.IndexedSeq Nat where
  length := trace.nodes.length
  get? idx := Refine.StoredSeq.get? (builtNodeStore trace) idx

@[simp] theorem builtNodeIndex_length (trace : EulerTrace) :
    (builtNodeIndex trace).length = trace.nodes.length := by
  rfl

@[simp] theorem builtNodeIndex_get? (trace : EulerTrace) (idx : Nat) :
    (builtNodeIndex trace).get? idx = trace.nodes[idx]? := by
  unfold builtNodeIndex
  change Refine.StoredSeq.get? (builtNodeStore trace) idx = trace.nodes[idx]?
  rw [TableModel.StoredSeq.get?_eq_absGet?]
  rfl

theorem builtNodeIndex_getCosted_eq_nodeIndex
    (trace : EulerTrace) (idx : Nat) :
    (builtNodeIndex trace).getCosted idx =
      (nodeIndex trace).getCosted idx := by
  unfold TableModel.IndexedSeq.getCosted TableModel.IndexedSeq.toAccess
    TableModel.IndexedAccess.getCosted Costed.tickValue
  simp

/-- Counted materialization of the Euler-depth list. -/
def buildDepthArray (trace : EulerTrace) : RAM.Exec (Array Int) :=
  RAM.arrayOfList trace.depths

@[simp] theorem buildDepthArray_value_toList (trace : EulerTrace) :
    (buildDepthArray trace).value.toList = trace.depths := by
  exact RAM.arrayOfList_value_toList trace.depths

@[simp] theorem buildDepthArray_steps (trace : EulerTrace) :
    (buildDepthArray trace).steps = trace.depths.length + 1 := by
  exact RAM.arrayOfList_steps trace.depths

theorem buildDepthArray_refines_with_steps (trace : EulerTrace) :
    (buildDepthArray trace).value.toList = trace.depths ∧
      (buildDepthArray trace).steps = trace.depths.length + 1 := by
  exact RAM.arrayOfList_refines_with_steps trace.depths

/-- Stored Euler-depth view produced by the counted builder. -/
def builtDepthStore (trace : EulerTrace) :
    TableModel.StoredSeq Int trace.depths where
  repr := (buildDepthArray trace).value
  erases := buildDepthArray_value_toList trace

@[simp] theorem builtDepthStore_erases (trace : EulerTrace) :
    (builtDepthStore trace).repr.toList = trace.depths := by
  exact TableModel.StoredSeq.erases_eq (builtDepthStore trace)

/-- Euler-depth indexed sequence backed by the counted depth-array builder. -/
def builtDepthIndex (trace : EulerTrace) : TableModel.IndexedSeq Int where
  length := trace.depths.length
  get? idx := Refine.StoredSeq.get? (builtDepthStore trace) idx

@[simp] theorem builtDepthIndex_length (trace : EulerTrace) :
    (builtDepthIndex trace).length = trace.depths.length := by
  rfl

@[simp] theorem builtDepthIndex_get? (trace : EulerTrace) (idx : Nat) :
    (builtDepthIndex trace).get? idx = trace.depths[idx]? := by
  unfold builtDepthIndex
  change Refine.StoredSeq.get? (builtDepthStore trace) idx = trace.depths[idx]?
  rw [TableModel.StoredSeq.get?_eq_absGet?]
  rfl

theorem builtDepthIndex_getCosted_eq_depthIndex
    (trace : EulerTrace) (idx : Nat) :
    (builtDepthIndex trace).getCosted idx =
      (depthIndex trace).getCosted idx := by
  unfold TableModel.IndexedSeq.getCosted TableModel.IndexedSeq.toAccess
    TableModel.IndexedAccess.getCosted Costed.tickValue
  simp

/-- Costed modeled lookup in the Euler-tour node list. -/
def nodeAtCosted (trace : EulerTrace) (idx : Nat) :
    Costed (Option Nat) :=
  (nodeIndex trace).getCosted idx

@[simp] theorem nodeAtCosted_erase
    (trace : EulerTrace) (idx : Nat) :
    (nodeAtCosted trace idx).erase = trace.nodes[idx]? := by
  rfl

@[simp] theorem nodeAtCosted_value
    (trace : EulerTrace) (idx : Nat) :
    (nodeAtCosted trace idx).value = trace.nodes[idx]? := by
  rfl

theorem nodeAtCosted_cost
    (trace : EulerTrace) (idx : Nat) :
    (nodeAtCosted trace idx).cost =
      TableModel.indexedReadCost := by
  rfl

theorem nodeAtCosted_run
    (trace : EulerTrace) (idx : Nat) :
    (nodeAtCosted trace idx).run =
      (trace.nodes[idx]?, TableModel.indexedReadCost) := by
  rfl

/-- Costed modeled lookup in the Euler-depth list. -/
def depthAtCosted (trace : EulerTrace) (idx : Nat) :
    Costed (Option Int) :=
  (depthIndex trace).getCosted idx

@[simp] theorem depthAtCosted_erase
    (trace : EulerTrace) (idx : Nat) :
    (depthAtCosted trace idx).erase = trace.depths[idx]? := by
  rfl

theorem depthAtCosted_cost
    (trace : EulerTrace) (idx : Nat) :
    (depthAtCosted trace idx).cost =
      TableModel.indexedReadCost := by
  rfl

theorem depthAtCosted_run
    (trace : EulerTrace) (idx : Nat) :
    (depthAtCosted trace idx).run =
      (trace.depths[idx]?, TableModel.indexedReadCost) := by
  rfl

/-- Supplied-backend LCA query cost in the abstract RAM/backend model. -/
def suppliedQueryCost : Nat := 1

/-- Costed query through an already-built exact LCA backend. -/
def queryCosted
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    Costed (Option Nat) :=
  Costed.tickValue suppliedQueryCost
    (LCABackend.queryBuilt backend u v)

theorem queryCosted_erase
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    (queryCosted tree backend u v).erase =
      LCABackend.queryBuilt backend u v := by
  rfl

theorem queryCosted_cost
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    (queryCosted tree backend u v).cost = suppliedQueryCost := by
  rfl

theorem queryCosted_run
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    (queryCosted tree backend u v).run =
      (LCABackend.queryBuilt backend u v, suppliedQueryCost) := by
  rfl

/--
Costed query through the structural Euler reduction from a supplied RMQ backend.
The correctness theorem is inherited from `RoseTree.lcaBackendOfRMQBackend`.
-/
def queryViaRMQCosted
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) : Costed (Option Nat) :=
  queryCosted tree
    (tree.lcaBackendOfRMQBackend rmqBackend hagreement) u v

theorem queryViaRMQCosted_erase
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQCosted tree rmqBackend hagreement u v).erase =
      tree.lcaCandidate rmqBackend u v := by
  rfl

theorem queryViaRMQCosted_cost
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQCosted tree rmqBackend hagreement u v).cost =
      suppliedQueryCost := by
  rfl

/-- Model cost charged to one supplied exact RMQ query. -/
def suppliedRMQQueryCost : Nat := suppliedQueryCost

/-- Costed query through an already-built exact RMQ backend. -/
def rmqQueryCosted
    {xs : List Int} (backend : RMQBackend xs) (left right : Nat) :
    Costed (Option Nat) :=
  Costed.tickValue suppliedRMQQueryCost
    (RMQBackend.queryBuilt backend left right)

@[simp] theorem rmqQueryCosted_erase
    {xs : List Int} (backend : RMQBackend xs) (left right : Nat) :
    (rmqQueryCosted backend left right).erase =
      RMQBackend.queryBuilt backend left right := by
  rfl

theorem rmqQueryCosted_cost
    {xs : List Int} (backend : RMQBackend xs) (left right : Nat) :
    (rmqQueryCosted backend left right).cost =
      suppliedRMQQueryCost := by
  rfl

theorem rmqQueryCosted_run
    {xs : List Int} (backend : RMQBackend xs) (left right : Nat) :
    (rmqQueryCosted backend left right).run =
      (RMQBackend.queryBuilt backend left right, suppliedRMQQueryCost) := by
  rfl

/-- Node-read cost contributed after a supplied RMQ query returns an index. -/
def returnedNodeReadCost (result : Option Nat) : Nat :=
  match result with
  | none => 0
  | some _ => TableModel.indexedReadCost

/-- Exact cost model for a supplied RMQ query followed by an optional node read. -/
def minDepthNodeInWindowIndexedCost
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) : Nat :=
  suppliedRMQQueryCost +
    returnedNodeReadCost (RMQBackend.queryBuilt backend left right)

/--
Costed version of `EulerTrace.minDepthNodeInWindow`: charge the supplied RMQ
query, then charge one modeled node read exactly when the RMQ query returns an
index.
-/
def minDepthNodeInWindowIndexedCosted
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (rmqQueryCosted backend left right) fun
  | none => Costed.pure none
  | some idx => nodeAtCosted trace idx

@[simp] theorem minDepthNodeInWindowIndexedCosted_erase
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) :
    (minDepthNodeInWindowIndexedCosted trace backend left right).erase =
      trace.minDepthNodeInWindow backend left right := by
  unfold minDepthNodeInWindowIndexedCosted EulerTrace.minDepthNodeInWindow
    rmqQueryCosted nodeAtCosted nodeIndex
  cases RMQBackend.queryBuilt backend left right <;> rfl

@[simp] theorem minDepthNodeInWindowIndexedCosted_value
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) :
    (minDepthNodeInWindowIndexedCosted trace backend left right).value =
      trace.minDepthNodeInWindow backend left right :=
  minDepthNodeInWindowIndexedCosted_erase trace backend left right

theorem minDepthNodeInWindowIndexedCosted_cost
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) :
    (minDepthNodeInWindowIndexedCosted trace backend left right).cost =
      minDepthNodeInWindowIndexedCost trace backend left right := by
  unfold minDepthNodeInWindowIndexedCosted minDepthNodeInWindowIndexedCost
    rmqQueryCosted returnedNodeReadCost nodeAtCosted nodeIndex
  cases RMQBackend.queryBuilt backend left right <;> rfl

theorem minDepthNodeInWindowIndexedCost_of_valid
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    {left right : Nat} (hValid : ValidRange trace.depths left right) :
    minDepthNodeInWindowIndexedCost trace backend left right =
      suppliedRMQQueryCost + TableModel.indexedReadCost := by
  let len := right - left
  have hlen : 0 < len := by
    unfold len
    omega
  have hbound : left + len <= trace.depths.length := by
    unfold len
    omega
  have hright : left + len = right := by
    unfold len
    omega
  have hscan :
      LeftmostArgMin trace.depths left right
        (scanWindow trace.depths left len) := by
    simpa [hright] using scanWindow_leftmost trace.depths left len hlen hbound
  have hquery :
      RMQBackend.queryBuilt backend left right =
        some (scanWindow trace.depths left len) :=
    backend.complete hscan
  simp [minDepthNodeInWindowIndexedCost, returnedNodeReadCost, hquery]

theorem minDepthNodeInWindowIndexedCost_le
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) :
    minDepthNodeInWindowIndexedCost trace backend left right <=
      suppliedRMQQueryCost + TableModel.indexedReadCost := by
  unfold minDepthNodeInWindowIndexedCost returnedNodeReadCost
  cases RMQBackend.queryBuilt backend left right <;>
    simp [suppliedRMQQueryCost, suppliedQueryCost,
      TableModel.indexedReadCost]

theorem minDepthNodeInWindowIndexedCosted_run
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (left right : Nat) :
    (minDepthNodeInWindowIndexedCosted trace backend left right).run =
      (trace.minDepthNodeInWindow backend left right,
        minDepthNodeInWindowIndexedCost trace backend left right) := by
  simp [Costed.run, minDepthNodeInWindowIndexedCosted_cost]

/-- Exact cost model for the explicit indexed-access LCA-via-RMQ query path. -/
def traceQueryViaRMQIndexedCost
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) : Nat :=
  TableModel.indexedReadCost +
    (TableModel.indexedReadCost +
      match trace.firstOccurrence? u, trace.firstOccurrence? v with
      | some i, some j =>
          let window := EulerTrace.occurrenceWindow i j
          minDepthNodeInWindowIndexedCost trace backend window.1 window.2
      | _, _ => 0)

/--
Costed trace-level LCA-via-RMQ query using explicit modeled access:
two first-occurrence reads, then a supplied RMQ query and one node read when
the RMQ query returns an index.
-/
def traceQueryViaRMQIndexedCosted
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) : Costed (Option Nat) :=
  Costed.bind (firstOccurrenceCosted trace u) fun
  | none =>
      Costed.bind (firstOccurrenceCosted trace v) fun _ =>
        Costed.pure none
  | some i =>
      Costed.bind (firstOccurrenceCosted trace v) fun
      | none => Costed.pure none
      | some j =>
          let window := EulerTrace.occurrenceWindow i j
          minDepthNodeInWindowIndexedCosted trace backend window.1 window.2

@[simp] theorem traceQueryViaRMQIndexedCosted_erase
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) :
    (traceQueryViaRMQIndexedCosted trace backend u v).erase =
      trace.lcaCandidate backend u v := by
  unfold traceQueryViaRMQIndexedCosted EulerTrace.lcaCandidate
    firstOccurrenceCosted firstOccurrenceIndex
  cases hu : trace.firstOccurrence? u <;>
    cases hv : trace.firstOccurrence? v <;>
    simp [hu, hv, Costed.bind, Costed.pure]

@[simp] theorem traceQueryViaRMQIndexedCosted_value
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) :
    (traceQueryViaRMQIndexedCosted trace backend u v).value =
      trace.lcaCandidate backend u v :=
  traceQueryViaRMQIndexedCosted_erase trace backend u v

theorem traceQueryViaRMQIndexedCosted_cost
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) :
    (traceQueryViaRMQIndexedCosted trace backend u v).cost =
      traceQueryViaRMQIndexedCost trace backend u v := by
  unfold traceQueryViaRMQIndexedCosted traceQueryViaRMQIndexedCost
    firstOccurrenceCosted firstOccurrenceIndex
  cases hu : trace.firstOccurrence? u <;>
    cases hv : trace.firstOccurrence? v <;>
    simp [hu, hv, Costed.bind, Costed.pure,
      TableModel.IndexedAccess.getCosted,
      minDepthNodeInWindowIndexedCosted_cost]

theorem traceQueryViaRMQIndexedCosted_cost_of_firstOccurrences
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    {u v i j : Nat}
    (hu : trace.firstOccurrence? u = some i)
    (hv : trace.firstOccurrence? v = some j) :
    (traceQueryViaRMQIndexedCosted trace backend u v).cost =
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  have hValid :
      ValidRange trace.depths
        (EulerTrace.occurrenceWindow i j).1
        (EulerTrace.occurrenceWindow i j).2 := by
    exact trace.occurrenceWindow_valid hu hv
  rw [traceQueryViaRMQIndexedCosted_cost]
  simp [traceQueryViaRMQIndexedCost, hu, hv,
    minDepthNodeInWindowIndexedCost_of_valid trace backend hValid]

theorem traceQueryViaRMQIndexedCost_le
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) :
    traceQueryViaRMQIndexedCost trace backend u v <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  unfold traceQueryViaRMQIndexedCost
  cases hu : trace.firstOccurrence? u with
  | none =>
      cases hv : trace.firstOccurrence? v with
      | none =>
          simp [suppliedRMQQueryCost, suppliedQueryCost,
            TableModel.indexedReadCost]
      | some j =>
          simp [suppliedRMQQueryCost, suppliedQueryCost,
            TableModel.indexedReadCost]
  | some i =>
      cases hv : trace.firstOccurrence? v with
      | none =>
          simp [suppliedRMQQueryCost, suppliedQueryCost,
            TableModel.indexedReadCost]
      | some j =>
          simp
          exact minDepthNodeInWindowIndexedCost_le trace backend
            (EulerTrace.occurrenceWindow i j).1
            (EulerTrace.occurrenceWindow i j).2

theorem traceQueryViaRMQIndexedCosted_cost_le
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) :
    (traceQueryViaRMQIndexedCosted trace backend u v).cost <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  rw [traceQueryViaRMQIndexedCosted_cost]
  exact traceQueryViaRMQIndexedCost_le trace backend u v

theorem traceQueryViaRMQIndexedCosted_run
    (trace : EulerTrace) (backend : RMQBackend trace.depths)
    (u v : Nat) :
    (traceQueryViaRMQIndexedCosted trace backend u v).run =
      (trace.lcaCandidate backend u v,
        traceQueryViaRMQIndexedCost trace backend u v) := by
  simp [Costed.run, traceQueryViaRMQIndexedCosted_cost]

/-- Tree-level cost model for the explicit indexed-access LCA-via-RMQ path. -/
def queryViaRMQIndexedCost
    (tree : RoseTree) (backend : RMQBackend tree.eulerTrace.depths)
    (u v : Nat) : Nat :=
  traceQueryViaRMQIndexedCost tree.eulerTrace backend u v

/--
Costed query through the structural Euler reduction, with first-occurrence and
node-list accesses charged explicitly.  The agreement proof is accepted to
match `queryViaRMQCosted`; the cost/value path itself is trace-level.
-/
def queryViaRMQIndexedCosted
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (_hagreement : tree.TracePathAgreement)
    (u v : Nat) : Costed (Option Nat) :=
  traceQueryViaRMQIndexedCosted tree.eulerTrace rmqBackend u v

@[simp] theorem queryViaRMQIndexedCosted_erase
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQIndexedCosted tree rmqBackend hagreement u v).erase =
      tree.lcaCandidate rmqBackend u v := by
  unfold queryViaRMQIndexedCosted RoseTree.lcaCandidate
  exact traceQueryViaRMQIndexedCosted_erase tree.eulerTrace rmqBackend u v

theorem queryViaRMQIndexedCosted_cost
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQIndexedCosted tree rmqBackend hagreement u v).cost =
      queryViaRMQIndexedCost tree rmqBackend u v := by
  unfold queryViaRMQIndexedCosted queryViaRMQIndexedCost
  exact traceQueryViaRMQIndexedCosted_cost tree.eulerTrace rmqBackend u v

theorem queryViaRMQIndexedCosted_cost_of_firstOccurrences
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    {u v i j : Nat}
    (hu : tree.eulerTrace.firstOccurrence? u = some i)
    (hv : tree.eulerTrace.firstOccurrence? v = some j) :
    (queryViaRMQIndexedCosted tree rmqBackend hagreement u v).cost =
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  unfold queryViaRMQIndexedCosted
  exact traceQueryViaRMQIndexedCosted_cost_of_firstOccurrences
    tree.eulerTrace rmqBackend hu hv

theorem queryViaRMQIndexedCost_le
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (u v : Nat) :
    queryViaRMQIndexedCost tree rmqBackend u v <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  unfold queryViaRMQIndexedCost
  exact traceQueryViaRMQIndexedCost_le tree.eulerTrace rmqBackend u v

theorem queryViaRMQIndexedCosted_cost_le
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQIndexedCosted tree rmqBackend hagreement u v).cost <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  rw [queryViaRMQIndexedCosted_cost]
  exact queryViaRMQIndexedCost_le tree rmqBackend u v

theorem queryViaRMQIndexedCosted_run
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQIndexedCosted tree rmqBackend hagreement u v).run =
      (tree.lcaCandidate rmqBackend u v,
        queryViaRMQIndexedCost tree rmqBackend u v) := by
  unfold queryViaRMQIndexedCosted queryViaRMQIndexedCost RoseTree.lcaCandidate
  exact traceQueryViaRMQIndexedCosted_run tree.eulerTrace rmqBackend u v

/--
Tree-level indexed-cost query through a plus-minus-one backend over generated
Euler-tour parentheses.
-/
def queryViaEulerParensRMQIndexedCosted
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (Succinct.plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) : Costed (Option Nat) :=
  queryViaRMQIndexedCosted tree
    (Succinct.rmqBackendOfEulerParensBackend tree backend) hagreement u v

/-- Cost model for `queryViaEulerParensRMQIndexedCosted`. -/
def queryViaEulerParensRMQIndexedCost
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (Succinct.plusMinusOneInputOfEulerParens tree))
    (u v : Nat) : Nat :=
  queryViaRMQIndexedCost tree
    (Succinct.rmqBackendOfEulerParensBackend tree backend) u v

@[simp] theorem queryViaEulerParensRMQIndexedCosted_erase
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (Succinct.plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaEulerParensRMQIndexedCosted tree backend hagreement u v).erase =
      Succinct.lcaCandidateOfEulerParensBackend tree backend u v := by
  unfold queryViaEulerParensRMQIndexedCosted
    Succinct.lcaCandidateOfEulerParensBackend
  exact queryViaRMQIndexedCosted_erase tree
    (Succinct.rmqBackendOfEulerParensBackend tree backend)
    hagreement u v

theorem queryViaEulerParensRMQIndexedCosted_cost
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (Succinct.plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaEulerParensRMQIndexedCosted tree backend hagreement u v).cost =
      queryViaEulerParensRMQIndexedCost tree backend u v := by
  unfold queryViaEulerParensRMQIndexedCosted queryViaEulerParensRMQIndexedCost
  exact queryViaRMQIndexedCosted_cost tree
    (Succinct.rmqBackendOfEulerParensBackend tree backend)
    hagreement u v

theorem queryViaEulerParensRMQIndexedCosted_cost_of_firstOccurrences
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (Succinct.plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement)
    {u v i j : Nat}
    (hu : tree.eulerTrace.firstOccurrence? u = some i)
    (hv : tree.eulerTrace.firstOccurrence? v = some j) :
    (queryViaEulerParensRMQIndexedCosted tree backend hagreement u v).cost =
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  exact queryViaRMQIndexedCosted_cost_of_firstOccurrences tree
    (Succinct.rmqBackendOfEulerParensBackend tree backend)
    hagreement hu hv

theorem queryViaEulerParensRMQIndexedCosted_run
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (Succinct.plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaEulerParensRMQIndexedCosted tree backend hagreement u v).run =
      (Succinct.lcaCandidateOfEulerParensBackend tree backend u v,
        queryViaEulerParensRMQIndexedCost tree backend u v) := by
  unfold queryViaEulerParensRMQIndexedCosted queryViaEulerParensRMQIndexedCost
    Succinct.lcaCandidateOfEulerParensBackend
  exact queryViaRMQIndexedCosted_run tree
    (Succinct.rmqBackendOfEulerParensBackend tree backend)
    hagreement u v

/-- Concrete indexed-cost LCA query through the packed Euler-parentheses PM1 RMQ. -/
def queryViaPackedEulerParensRMQIndexedCosted
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) : Costed (Option Nat) :=
  queryViaEulerParensRMQIndexedCosted tree
    (Succinct.packedEulerParensBackend tree) hagreement u v

/-- Cost model for `queryViaPackedEulerParensRMQIndexedCosted`. -/
def queryViaPackedEulerParensRMQIndexedCost
    (tree : RoseTree) (u v : Nat) : Nat :=
  queryViaEulerParensRMQIndexedCost tree
    (Succinct.packedEulerParensBackend tree) u v

@[simp] theorem queryViaPackedEulerParensRMQIndexedCosted_erase
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).erase =
      Succinct.packedEulerParensLCACandidate tree u v := by
  exact queryViaEulerParensRMQIndexedCosted_erase
    tree (Succinct.packedEulerParensBackend tree) hagreement u v

@[simp] theorem queryViaPackedEulerParensRMQIndexedCosted_value
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).value =
      Succinct.packedEulerParensLCACandidate tree u v := by
  exact queryViaPackedEulerParensRMQIndexedCosted_erase
    tree hagreement u v

theorem queryViaPackedEulerParensRMQIndexedCosted_cost
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).cost =
      queryViaPackedEulerParensRMQIndexedCost tree u v := by
  exact queryViaEulerParensRMQIndexedCosted_cost
    tree (Succinct.packedEulerParensBackend tree) hagreement u v

theorem queryViaPackedEulerParensRMQIndexedCosted_cost_of_firstOccurrences
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    {u v i j : Nat}
    (hu : tree.eulerTrace.firstOccurrence? u = some i)
    (hv : tree.eulerTrace.firstOccurrence? v = some j) :
    (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).cost =
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  exact queryViaEulerParensRMQIndexedCosted_cost_of_firstOccurrences
    tree (Succinct.packedEulerParensBackend tree) hagreement hu hv

theorem queryViaPackedEulerParensRMQIndexedCost_le
    (tree : RoseTree) (u v : Nat) :
    queryViaPackedEulerParensRMQIndexedCost tree u v <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  unfold queryViaPackedEulerParensRMQIndexedCost
  exact queryViaRMQIndexedCost_le tree
    (Succinct.rmqBackendOfEulerParensBackend tree
      (Succinct.packedEulerParensBackend tree)) u v

theorem queryViaPackedEulerParensRMQIndexedCosted_cost_le
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).cost <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  rw [queryViaPackedEulerParensRMQIndexedCosted_cost]
  exact queryViaPackedEulerParensRMQIndexedCost_le tree u v

theorem queryViaPackedEulerParensRMQIndexedCosted_cost_le_four
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).cost <=
      4 := by
  have hle :=
    queryViaPackedEulerParensRMQIndexedCosted_cost_le
      tree hagreement u v
  simpa [TableModel.indexedReadCost, suppliedRMQQueryCost,
    suppliedQueryCost] using hle

theorem queryViaPackedEulerParensRMQIndexedCosted_run
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).run =
      (Succinct.packedEulerParensLCACandidate tree u v,
        queryViaPackedEulerParensRMQIndexedCost tree u v) := by
  exact queryViaEulerParensRMQIndexedCosted_run
    tree (Succinct.packedEulerParensBackend tree) hagreement u v

theorem queryViaPackedEulerParensRMQIndexedCosted_refines_with_steps_of_tracePathAgreement
    (tree : RoseTree)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (forall {node : Nat},
      (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).value =
          some node ->
        tree.IsPathLCA u v node) /\
      (queryViaPackedEulerParensRMQIndexedCosted tree hagreement u v).cost <=
        4 := by
  constructor
  · intro node hquery
    have hcandidate :
        Succinct.packedEulerParensLCACandidate tree u v = some node := by
      simpa using hquery
    exact
      Succinct.packedEulerParensLCACandidate_isPathLCA_of_tracePathAgreement
        tree hagreement hcandidate
  · exact queryViaPackedEulerParensRMQIndexedCosted_cost_le_four
      tree hagreement u v

theorem queryViaPackedEulerParensRMQIndexedCosted_refines_with_steps_of_labelsUnique
    (tree : RoseTree)
    (hunique : tree.LabelsUnique)
    (u v : Nat) :
    (forall {node : Nat},
      (queryViaPackedEulerParensRMQIndexedCosted tree
          (tree.tracePathAgreement_of_labelsUnique hunique) u v).value =
          some node ->
        tree.IsPathLCA u v node) /\
      (queryViaPackedEulerParensRMQIndexedCosted tree
          (tree.tracePathAgreement_of_labelsUnique hunique) u v).cost <=
        4 := by
  exact
    queryViaPackedEulerParensRMQIndexedCosted_refines_with_steps_of_tracePathAgreement
      tree (tree.tracePathAgreement_of_labelsUnique hunique) u v

end LCACost

end RMQ
