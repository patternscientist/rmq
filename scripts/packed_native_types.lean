import RMQ.Core.WordRAM.Native.Route

open RMQ.SuccinctFinal
open PackedWordRAM PackedNative

-- Expected types are written independently of the current declaration types.
example (memory : Array Nat) (program : Array Instruction) (fuel : Nat)
    (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    (runFinite memory program fuel s).decode =
      run memory.toList program.toList fuel s.decode :=
  runFinite_decode memory program fuel s hwrites

example (observeReads : Bool) (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    decodeThin (routeCore observeReads memory program fuel s) =
      observeRun observeReads (run memory.toList program.toList fuel s.decode) {} :=
  routeCore_reference observeReads memory program fuel s hwrites

example (observeReads : Bool) (memory : Memory) (program : Program)
    (capacity fuel : Nat) (s : State)
    (hwrites : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    decodeThin (routeCore observeReads memory.toArray program.toArray fuel
      (FiniteState.ofState capacity s)) =
        observeRun observeReads (run memory program fuel s) {} :=
  routeCore_ofState observeReads memory program capacity fuel s hwrites hzero

example (i : Instruction) : parseInstruction i.encoding = .ok i :=
  parseInstruction_encoding i

example (n left right : Nat) :
    (routeInitialState n left right).decode =
      ⟨Registers.write (Registers.write (Registers.write (fun _ => 0) 0 left) 1 right) 2 n,
        0, .running⟩ :=
  routeInitialState_decode n left right

example (i j : Instruction) (h : i.encoding = j.encoding) : i = j :=
  instruction_encoding_injective i j h

example (memory : Array Nat) (program : Array Instruction)
    (fuel : Nat) (s : FiniteState) :
    (runThin false memory program fuel s {}).2.readsRev = [] :=
  runThin_no_reads memory program fuel s {}

#print axioms executeFinite_decode
#print axioms runFinite_decode
#print axioms runFinite_ofState
#print axioms runThin_projection
#print axioms runThin_no_reads
#print axioms runThin_reference
#print axioms parseInstruction_encoding
#print axioms instruction_encoding_injective
#print axioms routeCore_source
#print axioms routeCore_reference
#print axioms routeCore_ofState
#print axioms routeInitialState_decode
#print axioms routeDestinationFits_iff
