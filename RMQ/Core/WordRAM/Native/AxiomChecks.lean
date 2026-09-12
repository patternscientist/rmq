import RMQ.Core.WordRAM.Native.Contract
import RMQ.Core.WordRAM.Native.Limbs.Checks
import RMQ.Core.WordRAM.Native.Machine.Checks
import RMQ.Core.WordRAM.Native.Machine.CodeFactsChecks
import RMQ.Core.WordRAM.Native.Binary.Checks
import RMQ.Core.WordRAM.Native.Binary.Cursor.Checks

/-! # Final native-source trust inventory

Frozen before implementation: AX-LEAVES imports every limb/machine/code/binary/
cursor consumer module; AX-CAPSTONE prints the public capstone and all 42
independently stated Contract consumers; AX-SOURCE prints the actual exported
entry, host, canonical execution and full representation/refinement producers.
The printed inventory is trust evidence. Contract's exact proposition consumers
supply dependency evidence separately; an inventory alone does not replace them.
-/

namespace RMQ.SuccinctFinal.PackedNative

#print axioms nativeExecutionCapstone_holds
#print axioms ContractChecks.publicContract
#print axioms ContractChecks.checkN01
#print axioms ContractChecks.checkN02
#print axioms ContractChecks.checkN03
#print axioms ContractChecks.checkN04
#print axioms ContractChecks.checkN05
#print axioms ContractChecks.checkN06
#print axioms ContractChecks.checkN07
#print axioms ContractChecks.checkN08
#print axioms ContractChecks.checkN09
#print axioms ContractChecks.checkN10
#print axioms ContractChecks.checkN11
#print axioms ContractChecks.checkN12
#print axioms ContractChecks.checkN13
#print axioms ContractChecks.checkN14
#print axioms ContractChecks.checkN15
#print axioms ContractChecks.checkN16
#print axioms ContractChecks.checkN17
#print axioms ContractChecks.checkN18
#print axioms ContractChecks.checkN19
#print axioms ContractChecks.checkN20
#print axioms ContractChecks.checkN21
#print axioms ContractChecks.checkN22
#print axioms ContractChecks.checkN23
#print axioms ContractChecks.checkN24
#print axioms ContractChecks.checkN25
#print axioms ContractChecks.checkN26
#print axioms ContractChecks.checkN27
#print axioms ContractChecks.checkN28
#print axioms ContractChecks.checkN29
#print axioms ContractChecks.checkN30
#print axioms ContractChecks.checkN31
#print axioms ContractChecks.checkN32
#print axioms ContractChecks.checkN33
#print axioms ContractChecks.checkN34
#print axioms ContractChecks.checkN35
#print axioms ContractChecks.checkN36
#print axioms ContractChecks.checkN37
#print axioms ContractChecks.checkN38
#print axioms ContractChecks.checkN39
#print axioms ContractChecks.checkN40
#print axioms ContractChecks.checkN41
#print axioms ContractChecks.checkN42
#print axioms nativeLoadEntry_source
#print axioms nativeQueryEntry_source
#print axioms nativeWordBytes_exact
#print axioms nativeCore_source
#print axioms nativeCore_no_reads
#print axioms nativeLoadEntry_success
#print axioms nativeHostBounds
#print axioms nativeLoadedProgram
#print axioms nativeMemoryLookup
#print axioms nativeCodeLookup
#print axioms canonicalExecution_decode
#print axioms canonicalObservation_reference
#print axioms canonicalExecution_spec
#print axioms canonicalExecution_leftmost
#print axioms canonical_supplied_memory
#print axioms nativeLoadEntry_canonical
#print axioms nativeQueryEntry_canonical
#print axioms LimbWord.decode_encode
#print axioms LimbWord.encode_decode
#print axioms LimbWord.encode_injective
#print axioms LimbWord.checkedArithmetic_success
#print axioms LimbWord.checkedArithmetic_accepts_iff
#print axioms LimbWord.checkedComparison_success
#print axioms LimbWord.checkedAddress_success
#print axioms LimbWord.checkedInt_success
#print axioms LimbMachine.run_reference
#print axioms LimbMachine.runThin_reference
#print axioms LimbMachine.run_loaded_reference
#print axioms LimbMachine.runThin_loaded_reference
#print axioms LimbMachine.runThin_projection
#print axioms LimbMachine.runThin_no_reads
#print axioms LimbMachine.run_final_canonical
#print axioms LimbMachine.decodeInstruction_success
#print axioms LimbMachine.code_exists_program
#print axioms StorageImage.decode_encode
#print axioms StorageImage.raw_encode_injective
#print axioms StorageImage.decodeSupported_iff
#print axioms StorageImage.encoded_bit_accounting
#print axioms BinaryCursor.decodeSupported_eq
#print axioms BinaryCursor.decodeSupported_iff
#print axioms BinaryCursor.readScalarDigits_reject_count
#print axioms BinaryCursor.readScalarLimit_reject_count

end RMQ.SuccinctFinal.PackedNative
