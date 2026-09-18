import RMQ.Core.WordRAM.Native.Thin

/-! # Source-path experiment

This textual experiment is not the versioned binary loader or the final API.
The exported declaration calls the actual proved finite runner, never a second
Rust interpreter. The source-to-machine translation remains a compiler/runtime
assumption. Limits below bound this experiment only.
-/

namespace RMQ.SuccinctFinal.PackedNative
open PackedWordRAM

def parseNumbers (s : String) : Except String (List Nat) :=
  (s.splitOn " ").mapM fun token =>
    match token.toNat? with
    | some n => .ok n
    | none => .error "invalid natural"

def decodeArithmetic : Nat → Option Arithmetic
  | 0 => some .add | 1 => some .sub | 2 => some .mul | 3 => some .div
  | 4 => some .mod | 5 => some .shl | 6 => some .shr | 7 => some .band
  | 8 => some .bor | 9 => some .bxor | _ => none

def decodeComparison : Nat → Option Comparison
  | 0 => some .lt | 1 => some .le | 2 => some .eq | _ => none

def parseInstruction : List Nat → Except String Instruction
  | [0, dst, address] => .ok (.load dst address)
  | [1, dst, value] => .ok (.constant dst value)
  | [2, dst, src] => .ok (.move dst src)
  | [3, op, dst, lhs, rhs] =>
      match decodeArithmetic op with
      | some op => .ok (.arithmetic op dst lhs rhs)
      | none => .error "arithmetic tag"
  | [4, op, dst, lhs, rhs] =>
      match decodeComparison op with
      | some op => .ok (.comparison op dst lhs rhs)
      | none => .error "comparison tag"
  | [5, target] => .ok (.jump target)
  | [6, src] => .ok (.jumpRegister src)
  | [7, condition, target] => .ok (.branchZero condition target)
  | [8, src] => .ok (.halt src)
  | _ => .error "instruction shape"

/-- Every primitive encoding decodes to the identical instruction, including
all numeric fields and operation tags. -/
theorem parseInstruction_encoding (i : Instruction) :
    parseInstruction i.encoding = .ok i := by
  cases i with
  | arithmetic op dst lhs rhs => cases op <;> rfl
  | comparison op dst lhs rhs => cases op <;> rfl
  | _ => rfl

theorem instruction_encoding_injective (i j : Instruction)
    (h : i.encoding = j.encoding) : i = j := by
  have hd := congrArg parseInstruction h
  simpa only [parseInstruction_encoding, Except.ok.injEq] using hd

def routeLines (s : String) : List String :=
  (s.splitOn "\n").filter (fun line => !line.isEmpty)

def countsText (c : Counts) : String :=
  String.intercalate " "
    ([c.memoryRead, c.registerWrite, c.arithmetic, c.comparison, c.branch, c.control].map toString)

def observationText (out : FiniteState × Stats) : String :=
  let packet := match out.1.status with
    | .halted n => toString n
    | _ => "none"
  let reads := out.2.readsRev.reverse.map fun r =>
    toString r.address ++ " " ++ match r.reply with
      | none => "none" | some n => toString n
  packet ++ " " ++ toString out.2.steps ++ "\n" ++ countsText out.2.counts ++ "\n" ++
    String.intercalate "\n" reads ++ "\n"

def routeCore (observeReads : Bool) (memory : Array Nat)
    (program : Array Instruction) (fuel : Nat) (s : FiniteState) : FiniteState × Stats :=
  runThin observeReads memory program fuel s {}

/-- Register order is left, right, n, matching Packed/Guard.lean. The slim
experiment quotes that initial-state body; canonical instantiation remains a
separate consumer that imports the accepted PQ1 construction. -/
def routeInitialState (n left right : Nat) : FiniteState :=
  FiniteState.ofState 8271
    ⟨Registers.write (Registers.write (Registers.write (fun _ => 0) 0 left) 1 right) 2 n,
      0, .running⟩

theorem routeInitialState_decode (n left right : Nat) :
    (routeInitialState n left right).decode =
      ⟨Registers.write (Registers.write (Registers.write (fun _ => 0) 0 left) 1 right) 2 n,
        0, .running⟩ := by
  apply FiniteState.decode_ofState
  intro r hr
  simp [Registers.write, show r ≠ 2 by omega, show r ≠ 1 by omega, show r ≠ 0 by omega]

def routeDestinationFits (i : Instruction) : Bool :=
  match i with
  | .load dst _ | .constant dst _ | .move dst _ |
      .arithmetic _ dst _ _ | .comparison _ dst _ _ => dst < 8271
  | _ => true

theorem routeDestinationFits_iff (i : Instruction) :
    routeDestinationFits i = true ↔ i.WritesOnly (fun r => r < 8271) := by
  cases i <;> simp [routeDestinationFits, Instruction.WritesOnly]

/-- This is the actual computational entry called by the exported parser. -/
theorem routeCore_source (observeReads : Bool) (memory : Array Nat)
    (program : Array Instruction) (fuel : Nat) (s : FiniteState) :
    routeCore observeReads memory program fuel s =
      ((runFinite memory program fuel s).final,
        (runFinite memory program fuel s).transitions.foldl
          (recordTransition observeReads) {}) :=
  runThin_projection observeReads memory program fuel s {}

/-- Independently anchors the exported core to the original PQ1 interpreter;
the full native capstone must additionally instantiate the canonical objects,
finite limbs, binary loading and the frontend marshaling boundary. -/
theorem routeCore_reference (observeReads : Bool) (memory : Array Nat)
    (program : Array Instruction) (fuel : Nat) (s : FiniteState)
    (hwrites : ∀ i ∈ program.toList, i.WritesOnly (fun r => r < s.regs.size)) :
    decodeThin (routeCore observeReads memory program fuel s) =
      observeRun observeReads (run memory.toList program.toList fuel s.decode) {} :=
  runThin_reference observeReads memory program fuel s {} hwrites

theorem routeCore_ofState (observeReads : Bool) (memory : Memory) (program : Program)
    (capacity fuel : Nat) (s : State)
    (hwrites : ∀ i ∈ program, i.WritesOnly (fun r => r < capacity))
    (hzero : ∀ r, capacity ≤ r → s.regs r = 0) :
    decodeThin (routeCore observeReads memory.toArray program.toArray fuel
      (FiniteState.ofState capacity s)) =
      observeRun observeReads (run memory program fuel s) {} := by
  simpa only [List.toList_toArray, FiniteState.decode_ofState capacity s hzero] using
    routeCore_reference observeReads memory.toArray program.toArray fuel
      (FiniteState.ofState capacity s)
      (by simpa only [List.toList_toArray, FiniteState.ofState_size] using hwrites)

def routeEvaluate (programText fixtureText : String) (observeReads : Bool) :
    Except String String := do
  if programText.utf8ByteSize > 50000000 || fixtureText.utf8ByteSize > 1000000 then
    throw "text size limit"
  let code ← (routeLines programText).mapM fun line => do
    let ns ← parseNumbers line
    parseInstruction ns
  if code.any (fun i => !routeDestinationFits i) then throw "destination limit"
  let fixture := routeLines fixtureText
  let header ← parseNumbers (fixture.headD "")
  let [n, left, right, width, fuel] := header | throw "fixture header"
  if width > 4096 || width == 0 || fuel > 1000000 || code.length > 1000000 then
    throw "experiment domain"
  let cells ← fixture.tail.mapM fun line =>
    match line.toNat? with | some n => .ok n | none => .error "cell"
  if cells.any (fun n => n >= 2 ^ width) then throw "cell width"
  let s := routeInitialState n left right
  pure (observationText (routeCore observeReads cells.toArray code.toArray fuel s))

@[export rmq_native_route]
def routeEntry (programText fixtureText : String) (observeReads : Bool) : String :=
  match routeEvaluate programText fixtureText observeReads with
  | .ok output => output
  | .error reason => "ERROR " ++ reason ++ "\n"

end RMQ.SuccinctFinal.PackedNative
