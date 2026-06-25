import RMQ.Core.SuccinctSelectProposal

/-!
Archived select-side obstruction witnesses.

These declarations are intentionally retained even though the live succinct RMQ
capstone no longer uses the old BP-specialized sparse/dense route. They record
why tempting packed-pointer layouts were not acceptable compact witnesses.
-/

namespace RMQ.Archive.SelectObstructions

abbrev sparseDense_locator_fullMachineField_not_word_bounded :=
  RMQ.SuccinctSelectProposal.sparseDenseFalseSelectLocatorEntry_fullMachineField_not_word_bounded

abbrev short_super_local_pointer_capacity_obstruction
    {shape : Cartesian.CartesianShape} :=
  @RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.short_super_local_pointer_capacity_obstruction
    shape

abbrev dense_branch_packed_local_pointer_capacity_obstruction
    {shape : Cartesian.CartesianShape} :=
  @RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.dense_branch_packed_local_pointer_capacity_obstruction
    shape

abbrev super_locator_full_machine_field_impossible
    {shape : Cartesian.CartesianShape} :=
  @RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.super_locator_full_machine_field_impossible
    shape

abbrev local_locator_full_machine_field_impossible
    {shape : Cartesian.CartesianShape} :=
  @RMQ.SuccinctSelectProposal.SparseDenseFalseSelectCloseData.local_locator_full_machine_field_impossible
    shape

end RMQ.Archive.SelectObstructions
