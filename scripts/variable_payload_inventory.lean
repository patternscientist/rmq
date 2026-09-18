import Lean
import RMQ.Core.WordRAM.Packed.AllocationLowerBound

/-! Check the actual elaborated LB-1 structures against literal ordered field
inventories. The expected names are frozen check data, never extracted from the
producer source or generated from its current metadata. Defaulted fields, unusual
names, indentation, missing structures and parent structures pass through the
same production predicate as the three real certificates. This diagnostic script
adds no theorem assumptions and does not replace the exact-type consumers. -/

namespace LB1InventoryCheck

def expectedEncoding : Array Lean.Name := #[
  `encode, `query, `length_le, `query_exact]

def expectedOptimality : Array Lean.Name := #[
  `wordRoundTrip, `wordSerializationInjective, `serializedLength, `memoryRecovery,
  `decoderExact, `decoderLeftmost, `sameShapeMemory, `shapeInjectivity,
  `uniformBudgetCount, `uniformBudgetLower, `canonicalCount, `canonicalLower,
  `upperCapacity, `allocationResidualLittleO, `runIdentity, `machine]

def expectedMachine : Array Lean.Name := #[
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

structure Defaulted : Prop where
  registered : True
  unregistered : True := True.intro

structure Indented : Prop where
  registered : True
    /-- Greater indentation does not remove a defaulted member from metadata. -/
    unregistered : True := True.intro

structure Underscore : Prop where
  registered : True
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

structure Missing : Prop where
  replacement : True

structure WithParent : Prop extends Unchanged where
  added : True

structure Ordered : Prop where
  first : True
  second : True

end LB1InventoryCheck

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← Lean.getEnv
  unless LB1InventoryCheck.expectedEncoding.size == 4 &&
      LB1InventoryCheck.expectedOptimality.size == 16 &&
      LB1InventoryCheck.expectedMachine.size == 33 do
    throwError "LB1-FIELDS: frozen inventory counts changed"
  unless LB1InventoryCheck.hasInventory env `RMQ.ExactRMQBoundedEncoding
      LB1InventoryCheck.expectedEncoding do
    throwError "LB1-FIELDS: bounded encoding differs from the frozen 4 fields or has a parent"
  unless LB1InventoryCheck.hasInventory env
      `RMQ.SuccinctFinal.PackedWordRAM.PackedAllocationOptimality
      LB1InventoryCheck.expectedOptimality do
    throwError "LB1-FIELDS: allocation optimality differs from the frozen 16 fields or has a parent"
  unless LB1InventoryCheck.hasInventory env
      `RMQ.SuccinctFinal.PackedWordRAM.ReconstructedPackedQueryCapstone
      LB1InventoryCheck.expectedMachine do
    throwError "LB1-FIELDS: reconstructed machine differs from the frozen 33 fields or has a parent"
  unless LB1InventoryCheck.hasInventory env `LB1InventoryCheck.Unchanged #[`registered] do
    throwError "LB1-FIELDS: unchanged control rejected"
  unless LB1InventoryCheck.hasInventory env `LB1InventoryCheck.Ordered #[`first, `second] do
    throwError "LB1-FIELDS: ordered positive control rejected"
  for name in #[`LB1InventoryCheck.Defaulted, `LB1InventoryCheck.Indented,
      `LB1InventoryCheck.Underscore, `LB1InventoryCheck.Apostrophe,
      `LB1InventoryCheck.Unicode, `LB1InventoryCheck.Escaped,
      `LB1InventoryCheck.Missing, `LB1InventoryCheck.Absent] do
    if LB1InventoryCheck.hasInventory env name #[`registered] then
      throwError "LB1-FIELDS: extra-field or missing control accepted: {name}"
  if LB1InventoryCheck.hasInventory env `LB1InventoryCheck.Unchanged #[`registered, `missing] then
    throwError "LB1-FIELDS: missing expected field accepted"
  if LB1InventoryCheck.hasInventory env `LB1InventoryCheck.Ordered #[`second, `first] then
    throwError "LB1-FIELDS: reversed field order accepted"
  match Lean.getStructureInfo? env `LB1InventoryCheck.WithParent with
  | none => throwError "LB1-FIELDS: parent control metadata absent"
  | some info =>
      unless info.fieldNames == #[`toUnchanged, `added] && !info.parentInfo.isEmpty do
        throwError "LB1-FIELDS: parent control does not isolate parent rejection"
  if LB1InventoryCheck.hasInventory env `LB1InventoryCheck.WithParent #[`toUnchanged, `added] then
    throwError "LB1-FIELDS: parent structure accepted"
  Lean.logInfo "LB1-FIELDS PASS actual=4,16,33; unchanged and ordered controls accepted; defaulted, indented, underscore, apostrophe, Unicode, escaped, absent, missing, reversed and parent controls rejected"
