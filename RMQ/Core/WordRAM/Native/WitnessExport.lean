import RMQ.Core.WordRAM.Native.Witnesses

/-! Operational reference exporter. Numeric expectations come only from the
canonical raw query evaluator, its semantic trace and scanWindow. -/

namespace RMQ.SuccinctFinal.PackedNative.WitnessExport

open PackedWordRAM Cartesian SuccinctSpace PackedCellProbe Witnesses

def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError ("NATIVE-WITNESS " ++ message))

-- All serialized strings here are fixed schema/enum literals or decimal
-- numerals. No arbitrary path, selector or external text enters this encoder.
def quoted (text : String) : String := "\"" ++ text ++ "\""
def number (value : Nat) : String := toString value
def decimal (value : Nat) : String := quoted (toString value)
def nullable (value : Option Nat) : String := value.map decimal |>.getD "null"
def jsonArray (values : List String) : String := "[" ++ String.intercalate "," values ++ "]"
def jsonObject (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map fun (key, value) => quoted key ++ ":" ++ value) ++ "}"

def receiptJSON (receipt : Receipt) : String :=
  jsonObject [("address", decimal receipt.address), ("reply", nullable receipt.reply)]

structure Physical where
  ordinal : Nat
  transitionIndex : Nat
  pc : Nat
  destination : Nat
  addressRegister : Nat
  addressValue : Nat
  destinationBefore : Nat
  receipt : Receipt

def Physical.json (value : Physical) : String :=
  jsonObject [("physicalOrdinal", number value.ordinal),
    ("transitionIndex", number value.transitionIndex), ("pc", decimal value.pc),
    ("loadRegisters", jsonObject [("destination", number value.destination),
      ("address", number value.addressRegister)]),
    ("prestate", jsonObject [("pc", decimal value.pc), ("status", quoted "running"),
      ("addressValue", decimal value.addressValue),
      ("destinationValue", decimal value.destinationBefore)]),
    ("address", decimal value.receipt.address), ("reply", nullable value.receipt.reply)]

structure Logical where
  stage : Stage
  ordinal : Nat
  inStage : Nat
  physicalOrdinal : Nat
  segment : Nat
  index : Nat
  word : Option WordRAM.Word
  span : Option NumericSpan
  physical : List Physical
  width : Nat

def Logical.crosses (value : Logical) : Bool :=
  match value.span, value.physical with
  | some span, [first, second] =>
      decide (0 < span.length ∧
        value.width < (174 * value.width + span.position) % value.width + span.length ∧
        second.receipt.address = first.receipt.address + 1) &&
        first.receipt.reply.isSome && second.receipt.reply.isSome
  | _, _ => false

def Logical.json (value : Logical) : String :=
  let span := match value.span with
    | none => "null"
    | some span => jsonObject [("position", decimal span.position),
        ("absolutePosition", decimal (174 * value.width + span.position)),
        ("length", decimal span.length), ("width", number value.width),
        ("offset", number ((174 * value.width + span.position) % value.width))]
  let word := match value.word with
    | none => "null"
    | some bits => jsonObject [("bitLength", number bits.length), ("value", decimal (bitsToNatLE bits))]
  jsonObject [("stage", quoted value.stage.name), ("logicalOrdinal", number value.ordinal),
    ("logicalInStage", number value.inStage), ("physicalOrdinal", number value.physicalOrdinal),
    ("segment", number value.segment), ("index", decimal value.index),
    ("logicalReply", word), ("span", span),
    ("crossCell", if value.crosses then "true" else "false"),
    ("physical", jsonArray (value.physical.map Physical.json))]

structure Candidate where
  sourceID : String
  xs : List Int
  left : Nat
  right : Nat
  expected : Nat

def crossBlockInput : List Int := [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

def candidates : List Candidate := [
  ⟨"cross-block", crossBlockInput, 1, 11, 5⟩,
  ⟨"same-block", crossBlockInput, 6, 10, 9⟩,
  ⟨"adjacent-blocks", crossBlockInput, 4, 8, 5⟩,
  ⟨"monotone-24", (List.range 24).map Int.ofNat, 0, 24, 0⟩]

structure Snapshot where
  candidate : Candidate
  memory : Memory
  expectedJSON : String
  logical : Array Logical

def inspect (program : Array Instruction) (memory : Memory) (candidate : Candidate) : IO Snapshot := do
  let xs := candidate.xs
  let shape := SuccinctClassic.cartesianShape xs
  let actual := runArray memory program queryBudget (initialState xs.length candidate.left candidate.right)
  let reference := SuccinctClassic.queryTraceResult xs candidate.left candidate.right
  let semantic := stages xs candidate.left candidate.right
  check (decide (ValidRange xs candidate.left candidate.right)) "candidate range is invalid"
  check (reference.value == some candidate.expected) "reference/literal answer mismatch"
  check (RMQ.scanWindow xs candidate.left (candidate.right - candidate.left) == candidate.expected)
    "scanWindow/literal answer mismatch"
  check (actual.result == some (candidate.expected + 1)) "primitive/literal answer mismatch"
  check (actual.final.status == .halted (candidate.expected + 1)) "primitive did not halt"
  check (actual.steps ≤ queryBudget) "primitive budget exceeded"
  check (flatten semantic == reference.trace) "semantic call-site trace mismatch"
  check (reference.trace.all (fun event => match event with
    | .readWord _ _ _ => true
    | _ => false)) "non-read reference event"
  let raw := actual.reads.toArray
  let metadataReads := (List.range 174).map fun index =>
    Receipt.mk index (metadata shape)[index]?
  let expanded := metadataReads ++ logicalTraceReads shape memory reference.trace
  check (actual.reads == expanded) "canonical physical expansion mismatch"
  check (actual.reads.all fun receipt => receipt.reply == memory[receipt.address]? && receipt.reply.isSome)
    "primitive memory reply mismatch"

  let mut physical : Array Physical := #[]
  for (transition, index) in actual.transitions.zipIdx do
    match transition.receipt with
    | none => pure ()
    | some receipt =>
        match transition.instruction with
        | .load dst address =>
            check (transition.before.status == .running) "receipt prestate is stopped"
            check (program[transition.before.pc]? == some transition.instruction) "receipt source PC mismatch"
            check (receipt.address == transition.before.regs address) "receipt address-register mismatch"
            check (receipt.reply == memory[receipt.address]?) "receipt loaded-value mismatch"
            physical := physical.push ⟨physical.size, index, transition.before.pc, dst, address,
              transition.before.regs address, transition.before.regs dst, receipt⟩
        | _ => throw (IO.userError "NATIVE-WITNESS receipt attached to non-load")
  check (physical.toList.map (·.receipt) == actual.reads) "transition occurrence projection mismatch"

  let width := wordWidth xs.length
  let mut logical : Array Logical := #[]
  let mut ordinal := 0
  let mut physicalOrdinal := 174
  for stage in semantic do
    for (event, inStage) in stage.trace.zipIdx do
      match event with
      | .readWord segment index word =>
          let receipts := readerReceipts shape memory segment index
          let selected := (physical.toList.drop physicalOrdinal).take receipts.length
          check (selected.map (·.receipt) == receipts) "logical/physical occurrence offset mismatch"
          check ((raw.toList.drop physicalOrdinal).take receipts.length == receipts)
            "raw receipt ordinal mismatch"
          let span := reviewerLogicalSpan shape.size (longCount shape)
            (packedReviewerSparseCount shape) segment index
          logical := logical.push ⟨stage.stage, ordinal, inStage, physicalOrdinal,
            segment, index, word, span, selected, width⟩
          ordinal := ordinal + 1
          physicalOrdinal := physicalOrdinal + receipts.length
      | _ => throw (IO.userError "NATIVE-WITNESS non-read stage event")
  check (ordinal == reference.trace.length && physicalOrdinal == physical.size)
    "unconsumed semantic or physical occurrences"
  let categories : List Category := [.memoryRead, .registerWrite, .arithmetic, .comparison, .branch, .control]
  let counts := categories.map actual.categoryCount
  check (counts.sum == actual.steps) "category partition mismatch"
  let expectedJSON := jsonObject [("status", quoted ("halted " ++ toString (candidate.expected + 1))),
    ("steps", number actual.steps), ("categories", jsonArray (counts.map number)),
    ("reads", jsonArray (actual.reads.map receiptJSON))]
  pure ⟨candidate, memory, expectedJSON, logical⟩

inductive Kind where
  | selectLeft | selectRight | leftFringe | rightFringe | interior | finalRank | crossCell
deriving DecidableEq, BEq

def Kind.id : Kind → String
  | .selectLeft => "canonical-select-left"
  | .selectRight => "canonical-select-right"
  | .leftFringe => "canonical-left-fringe"
  | .rightFringe => "canonical-right-fringe"
  | .interior => "canonical-interior"
  | .finalRank => "canonical-rank-final"
  | .crossCell => "canonical-cross-cell"

def Kind.matches (kind : Kind) (value : Logical) : Bool :=
  !value.physical.isEmpty && match kind with
  | .selectLeft => value.stage == .selectLeft
  | .selectRight => value.stage == .selectRight
  | .leftFringe => value.stage == .leftFringeWindow
  | .rightFringe => value.stage == .rightFringeWindow
  | .interior => value.stage == .interior
  | .finalRank => value.stage == .finalRank
  | .crossCell => value.crosses

def kinds : List Kind := [.selectLeft, .selectRight, .leftFringe, .rightFringe, .interior, .finalRank, .crossCell]

/-- Independent literal roster: an empty, omitted, duplicated or reordered kind
list must fail before preprocessing or creating output files. -/
def checkKinds (selection : List Kind) : IO Unit :=
  check (selection.map Kind.id == ["canonical-select-left", "canonical-select-right",
    "canonical-left-fringe", "canonical-right-fringe", "canonical-interior",
    "canonical-rank-final", "canonical-cross-cell"]) "exact required-kind roster mismatch"

def programSha256 : String := "2D978D9D81CC3326F623F3A21AFCDA9FE3329E6F1DB60B2000425C4EF0A0D875"

def fixtureJSON (kind : Kind) (snapshot : Snapshot) (value : Logical) : String :=
  let c := snapshot.candidate
  jsonObject [("schema", quoted "native1-canonical-witness-v1"), ("id", quoted kind.id),
    ("width", number (wordWidth c.xs.length)), ("inputLength", decimal c.xs.length),
    ("registerCount", number queryRegisterCount), ("left", decimal c.left), ("right", decimal c.right),
    ("fuel", number queryBudget), ("memory", jsonArray (snapshot.memory.map decimal)),
    ("program", jsonObject [("path", quoted "program.txt.gz"), ("uncompressedSha256", quoted programSha256)]),
    ("expected", snapshot.expectedJSON),
    ("witnessEvidence", jsonObject [("candidate", quoted c.sourceID),
      ("input", jsonArray (c.xs.map (fun value => quoted (toString value)))),
      ("expectedLeftmost", decimal c.expected), ("occurrence", value.json)])]

/-- The lookup key is the entire input list; each entry is produced by the
canonical builder in this function, once per distinct input. -/
def memoryFor (cache : IO.Ref (List (List Int × Memory))) (xs : List Int) : IO Memory := do
  match (← cache.get).find? (·.1 == xs) with
  | some (_, memory) => pure memory
  | none =>
      let memory := buildMemory xs
      cache.modify ((xs, memory) :: ·)
      pure memory

def mainImpl (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "NATIVE-WITNESS expects one output directory")
  checkKinds kinds
  let output := System.FilePath.mk directory
  let program := queryProgram.toArray
  let cache ← IO.mkRef ([] : List (List Int × Memory))
  let mut snapshots : Array Snapshot := #[]
  for candidate in candidates do
    let memory ← memoryFor cache candidate.xs
    let snapshot ← inspect program memory candidate
    snapshots := snapshots.push snapshot
    IO.println ("NATIVE-WITNESS inspected " ++ candidate.sourceID ++
      " logical=" ++ toString snapshot.logical.size)
    if kinds.all (fun kind => snapshots.any (fun snapshot => snapshot.logical.any kind.matches)) then
      break
  let mut selected : Array (Kind × Snapshot × Logical) := #[]
  for kind in kinds do
    let choice := snapshots.toList.findSome? fun snapshot =>
      (snapshot.logical.toList.find? kind.matches).map fun value => (snapshot, value)
    let some (snapshot, value) := choice |
      throw (IO.userError ("NATIVE-WITNESS missing actual occurrence: " ++ kind.id))
    selected := selected.push (kind, snapshot, value)
  IO.FS.createDirAll output
  -- The consumer hashes this actual canonical export and requires exact equality
  -- with programSha256 before using the shared, separately pinned gzip program.
  let stream ← IO.FS.Handle.mk (output / "canonical-program.txt") .write
  for instruction in program do
    stream.putStrLn (String.intercalate " " (instruction.encoding.map toString))
  stream.flush
  for (kind, snapshot, value) in selected do
    IO.FS.writeFile (output / (kind.id ++ ".fixture")) (fixtureJSON kind snapshot value ++ "\n")
    IO.println ("NATIVE-WITNESS exported " ++ kind.id ++ " stage=" ++ value.stage.name ++
      " logical=" ++ toString value.ordinal ++ " physical=" ++ toString value.physicalOrdinal)
  IO.println ("NATIVE-WITNESS PASS fixtures=" ++ toString selected.size)

end RMQ.SuccinctFinal.PackedNative.WitnessExport

def main (args : List String) : IO Unit := RMQ.SuccinctFinal.PackedNative.WitnessExport.mainImpl args
