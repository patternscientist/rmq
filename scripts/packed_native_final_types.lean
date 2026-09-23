import RMQ.Core.WordRAM.Native.AxiomChecks
import RMQ.Core.WordRAM.Native.WitnessExport

-- AxiomChecks imports all five leaf check modules and the literal public
-- consumers. WitnessExport adds the two operational-witness modules.
#check RMQ.SuccinctFinal.PackedNative.nativeExecutionCapstone_holds
#check RMQ.SuccinctFinal.PackedNative.ContractChecks.publicContract
#check RMQ.SuccinctFinal.PackedNative.ContractChecks.checkN01
#check RMQ.SuccinctFinal.PackedNative.ContractChecks.checkN42
