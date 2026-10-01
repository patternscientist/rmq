
# LIFE-1-R3 injected test double appended to a disposable copy of
# scripts/packed_native_lifecycle_integrity_check.ps1. It wraps the real
# Complete-LNIntegrity and, once, reports an ordinary failed fixture check.
# R3-FAULT-FUNCTION
${function:R3RealCompleteLNIntegrity}=${function:Complete-LNIntegrity}
function Complete-LNIntegrity([object]$State) {
  $result=R3RealCompleteLNIntegrity $State
  if(Invoke-R3Fault){
    $result.success=$false
    $result.errors=@($result.errors)+@('R3-DOUBLE: injected ordinary stage failure')
  }
  return $result
}
