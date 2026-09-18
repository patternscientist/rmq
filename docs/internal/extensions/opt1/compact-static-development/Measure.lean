import RMQ.Core.WordRAM.Optimization.Query

open RMQ.SuccinctFinal.PackedWordRAM
open RMQ.SuccinctFinal.PackedWordRAM.Optimization

set_option maxRecDepth 30000

-- This diagnostic evaluates the literal emitted list independently of the
-- size and encoding recurrences. Kernel equalities are checked separately.
#eval do
  let program := compactQueryProgram
  IO.println s!"literalInstructions={program.length}"
  IO.println s!"literalEncodingWords={(program.map Instruction.encoding).flatten.length}"
  IO.println s!"recurrenceInstructions={compactSize compactQuerySource}"
  IO.println s!"recurrenceEncodingWords={compactEncodingWords compactQuerySource}"
  IO.println s!"chargedBound={compactQueryBudget}"
  IO.println s!"depth={compactDepth compactQuerySource}"
  IO.println s!"maximumCount={compactMaxCount compactQuerySource}"
  IO.println s!"registerBank={compactQueryRegisterCount}"
  IO.println s!"scratchWords={compactQueryScratchWords}"
