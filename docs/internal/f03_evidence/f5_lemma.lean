import RMQ.Core.SuccinctFinalStoreParam

/-!
F5 linchpin, CHECKED.

The only channel by which a `FixedWidthNatTable`'s content-dependent `entries`
list can influence the controller's EXECUTED read is `entries.length`.
Everything else (the payload, the stored words, the `read_exact` codec proof) is
invisible to `machineReadComputationAt`, whose table argument is literally
named `_table` and never used.
-/

open RMQ
open RMQ.SuccinctSpace

namespace F5Lemma

/-- Two tables of the same width whose entry lists merely have the same LENGTH
produce the *same* flat-store computation: same addresses, same reads, same
decoded value, for every store. Contents of `entries` are irrelevant. -/
theorem machineReadComputationAt_depends_on_entries_only_through_length
    {e1 e2 : List Nat} {width : Nat}
    (t1 : FixedWidthNatTable e1 width)
    (t2 : FixedWidthNatTable e2 width)
    (hlen : e1.length = e2.length)
    (wordSize base deadAddress i : Nat) :
    t1.machineReadComputationAt wordSize base deadAddress i =
      t2.machineReadComputationAt wordSize base deadAddress i := by
  unfold FixedWidthNatTable.machineReadComputationAt
  rw [hlen]

/-- Consequence: same footprint (the executed address list) for every store. -/
theorem machineReadComputationAt_footprint_eq_of_length_eq
    {e1 e2 : List Nat} {width : Nat}
    (t1 : FixedWidthNatTable e1 width)
    (t2 : FixedWidthNatTable e2 width)
    (hlen : e1.length = e2.length)
    (wordSize base deadAddress i : Nat) (store : FlatWordStore) :
    ((t1.machineReadComputationAt wordSize base deadAddress i).run
        store).footprint =
      ((t2.machineReadComputationAt wordSize base deadAddress i).run
        store).footprint := by
  rw [machineReadComputationAt_depends_on_entries_only_through_length
    t1 t2 hlen wordSize base deadAddress i]

/-- And the same decoded value for every store: the reply comes from the store,
not from `entries`. -/
theorem machineReadComputationAt_value_eq_of_length_eq
    {e1 e2 : List Nat} {width : Nat}
    (t1 : FixedWidthNatTable e1 width)
    (t2 : FixedWidthNatTable e2 width)
    (hlen : e1.length = e2.length)
    (wordSize base deadAddress i : Nat) (store : FlatWordStore) :
    ((t1.machineReadComputationAt wordSize base deadAddress i).run store).value =
      ((t2.machineReadComputationAt wordSize base deadAddress i).run
        store).value := by
  rw [machineReadComputationAt_depends_on_entries_only_through_length
    t1 t2 hlen wordSize base deadAddress i]

/-- The controller-level wrapper inherits it verbatim. -/
theorem canonicalRelativeRmmMachineReadNatComputation_entries_irrelevant
    {e1 e2 : List Nat} {width : Nat}
    (shape : Cartesian.CartesianShape)
    (t1 : FixedWidthNatTable e1 width)
    (t2 : FixedWidthNatTable e2 width)
    (hlen : e1.length = e2.length)
    (base i : Nat) :
    SuccinctClose.canonicalRelativeRmmMachineReadNatComputation shape t1 base i =
      SuccinctClose.canonicalRelativeRmmMachineReadNatComputation shape t2 base
        i := by
  unfold SuccinctClose.canonicalRelativeRmmMachineReadNatComputation
  exact machineReadComputationAt_depends_on_entries_only_through_length
    t1 t2 hlen _ _ _ _

/-- The six `entries` families that carry `bpExcessAt` values all have
shape-free lengths.  Stated together so the F03 row can cite one fact. -/
theorem summary_entry_lengths_are_size_only
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      macroSize macroCount levelCount : Nat) :
    (SuccinctClose.bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount).length = superCount
    /\ (SuccinctClose.bpBlockRelativeMinExcessEntries shape blockSize
        blocksPerSuper blockCount).length = blockCount
    /\ (SuccinctClose.bpBlockRelativeMaxExcessEntries shape blockSize
        blocksPerSuper blockCount).length = blockCount
    /\ (SuccinctClose.bpBlockArgMinLocalOffsetEntries shape blockSize
        blockCount).length = blockCount
    /\ (SuccinctClose.bpLocalSparseOffsetEntries shape blockSize blockCount
        macroSize macroCount levelCount).length =
          macroCount * (levelCount * macroSize)
    /\ (SuccinctClose.bpGlobalSparseBlockEntries shape blockSize blockCount
        macroSize macroCount levelCount).length = levelCount * macroCount :=
  ⟨SuccinctClose.bpSuperblockBaselineEntries_length _ _ _ _,
   SuccinctClose.bpBlockRelativeMinExcessEntries_length _ _ _ _,
   SuccinctClose.bpBlockRelativeMaxExcessEntries_length _ _ _ _,
   SuccinctClose.bpBlockArgMinLocalOffsetEntries_length _ _ _,
   SuccinctClose.bpLocalSparseOffsetEntries_length _ _ _ _ _ _,
   SuccinctClose.bpGlobalSparseBlockEntries_length _ _ _ _ _ _⟩

#print axioms machineReadComputationAt_depends_on_entries_only_through_length
#print axioms canonicalRelativeRmmMachineReadNatComputation_entries_irrelevant
#print axioms summary_entry_lengths_are_size_only

end F5Lemma
