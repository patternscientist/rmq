import RMQ.Validation.PackedNative

-- Keep this import separate from WitnessExport: both executable roots define
-- a global main. Their source checks and runtime campaigns are independent.
#check RMQ.SuccinctFinal.PackedNative.nativeExecutionCapstone_holds
#check RMQ.SuccinctFinal.PackedNative.ContractChecks.publicContract
