import Lean
import RMQ.Core.WordRAM.Packed.Capstone

/-! Check the elaborated certificate inventory. Text matching in the replay
runner is an early diagnostic only: Lean admits escaped names, default fields,
and indentation that a line-oriented inventory can overlook. This validation
script uses Lean's actual structure metadata and adds no theorem assumptions. -/

namespace PQ1InventoryCheck

def expected : Array Lean.Name := #[
  `allocationResidualLittleO, `completeResidualLittleO, `widthBounds,
  `dataCapacity, `completeCapacity, `memoryWordsFit, `allocationAddressesFit,
  `programFieldsFit, `budgetExact, `programLength, `encodedProgramBound,
  `registerCount, `scratchCount, `unusedRegisters, `validInputs, `natContract,
  `leftmost, `result, `halt, `invalidGuard, `stepBound, `categoryPartition,
  `finalStateFit, `transitionSafety, `prefixSafety, `readWidth,
  `positionalReadBacking, `orderedLogicalRefinement, `logicalReadOnly,
  `suppliedMemoryAgreement, `specResult, `noFailedLoads, `invalidGuardSteps]

def hasInventory (env : Lean.Environment) (name : Lean.Name)
    (fields : Array Lean.Name) : Bool :=
  match Lean.getStructureInfo? env name with
  | none => false
  | some info => info.parentInfo.isEmpty && info.fieldNames == fields

structure Unchanged : Prop where
  registered : True

structure Underscore : Prop where
  registered : True
    /-- A defaulted member at greater indentation is still a real field. -/
    unregistered_field : True := True.intro

structure Apostrophe : Prop where
  registered : True
  unregisteredField' : True := True.intro

structure Unicode : Prop where
  registered : True
  α : True := True.intro

structure Escaped : Prop where
  registered : True
  «extra field» : True := True.intro

end PQ1InventoryCheck

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← Lean.getEnv
  unless PQ1InventoryCheck.expected.size == 33 do
    throwError "PQ1-FIELDS: frozen inventory count changed"
  unless PQ1InventoryCheck.hasInventory env
      `RMQ.SuccinctFinal.PackedWordRAM.FullyChargedPackedQueryCapstone
      PQ1InventoryCheck.expected do
    throwError "PQ1-FIELDS: elaborated certificate differs from the frozen 33 fields"
  unless PQ1InventoryCheck.hasInventory env `PQ1InventoryCheck.Unchanged #[`registered] do
    throwError "PQ1-FIELDS: unchanged control rejected"
  for name in #[`PQ1InventoryCheck.Underscore, `PQ1InventoryCheck.Apostrophe,
      `PQ1InventoryCheck.Unicode, `PQ1InventoryCheck.Escaped,
      `PQ1InventoryCheck.Absent] do
    if PQ1InventoryCheck.hasInventory env name #[`registered] then
      throwError "PQ1-FIELDS: extra-field or missing-structure control accepted: {name}"
  Lean.logInfo "PQ1-FIELDS PASS actual=33 unchanged accepted; defaulted/indented, underscore, apostrophe, Unicode, escaped and absent controls rejected"
