import Lean
import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerController
import RMQ.Core.SuccinctRMQClassic

/- Reference fixture exporter only. JSON traces and answers are expected-output
   data for the checker, never inputs to the charged instruction VM. The
   geometry object depends on n alone; dynamic counts are recovered by the VM. -/
namespace WholePathFixture

open Lean RMQ RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedCellProbe

def jn (n : Nat) : Json := toJson n
def js (s : String) : Json := .str s
def ja (xs : List Json) : Json := .arr xs.toArray
def jo (xs : List (String × Json)) : Json := Json.mkObj xs
def natString (n : Nat) : Json := js (toString n)

def instructionName : PackedReviewerInstructionSite → String
  | .leftSelect => "leftSelect"
  | .rightSelect => "rightSelect"
  | .lcaClose => "lcaClose"
  | .finalRank => "finalRank"

def requestJson (r : PackedReviewerLogicalRequest) : Json := jo
  [("instruction", js (instructionName r.invocation.instruction)),
   ("argument", jn r.invocation.argument), ("argument2", jn r.invocation.argument2),
   ("site", js (reprStr r.site)), ("segment", jn r.segment), ("index", jn r.index)]

def wordJson : Option (List Bool) → Json
  | none => .null
  | some bits => jo [("width", jn bits.length),
      ("value", natString (SuccinctSpace.bitsToNatLE bits))]

def terminalJson : Option (Option Nat) → Json
  | none => jo [("complete", toJson false), ("answer", .null)]
  | some none => jo [("complete", toJson true), ("answer", .null)]
  | some (some n) => jo [("complete", toJson true), ("answer", jn n)]

def phaseName : PackedReviewerWholeState → String
  | .leftSelect .. => "leftSelect"
  | .rightSelect .. => "rightSelect"
  | .finalRank .. => "finalRank"
  | .done .. => "done"
  | .lcaClose _ _ _ _ _ lca =>
    match lca with
    | .sameSeed .. => "sameSeed"
    | .sameWindow .. => "sameWindow"
    | .sameFringe .. => "sameFringe"
    | .leftSeed .. => "leftSeed"
    | .leftWindow .. => "leftWindow"
    | .leftFringe .. => "leftFringe"
    | .middle .. => "middle"
    | .rightSeed .. => "rightSeed"
    | .rightWindow .. => "rightWindow"
    | .rightFringe .. => "rightFringe"
    | .done .. => "lcaDone"

structure LogicalDumpEvent where
  phase : String
  request : PackedReviewerLogicalRequest
  reply : Option (List Bool)
  plan : List Nat

-- The exported logical replay invokes the real protocol and the real packed
-- read on the same canonical memory. It creates no second semantic store.
def logicalDump (n lc sc : Nat) (memory : List (List Bool)) :
    Nat → PackedReviewerWholeState → List LogicalDumpEvent × Option (Option Nat)
  | 0, state => ([], packedReviewerWholeResult state)
  | fuel + 1, state =>
    match packedReviewerWholeResult state with
    | some answer => ([], some answer)
    | none =>
      match packedReviewerWholeNextRequest state with
      | none => ([], none)
      | some request =>
        let reply := packedReviewerLogicalRead n lc sc memory request
        let tail := logicalDump n lc sc memory fuel
          (packedReviewerWholeConsumeReply state reply)
        ({phase := phaseName state, request, reply,
          plan := packedReviewerLogicalPlan n lc sc request} :: tail.1, tail.2)

def logicalJson (e : LogicalDumpEvent) : Json := jo
  [("phase", js e.phase), ("request", requestJson e.request),
   ("reply", wordJson e.reply), ("physicalPlan", ja (e.plan.map jn))]

def physicalJson (n : Nat) (e : PackedReviewerPhysicalEvent) : Json :=
  let origin := match e.request.origin with
    | .header => jo [("kind", js "header")]
    | .sparsePrelude req => jo [("kind", js "sparsePrelude"),
        ("request", js (reprStr req)),
        ("segment", jn (match req with
          | .rankSuper => 13 | .rankBlock => 14 | .flagWord => 15)),
        ("index", jn (req.index n))]
    | .wholeQuery req => jo [("kind", js "wholeQuery"),
        ("request", requestJson req)]
  jo [("address", jn e.request.address), ("ordinal", jn e.request.ordinal),
      ("cellCount", jn e.request.cellCount), ("origin", origin),
      ("reply", wordJson e.reply)]

def sources : List (Nat × ConcreteBPNativeSuccinctRMQFlatPayloadSource) :=
  [(17, .finalRankSuperFalse), (18, .finalRankBlockFalse),
   (1, .selectSuperBaseOccurrence), (2, .selectSuperBaseWordIndex),
   (3, .selectSuperRankBefore), (4, .selectSuperFirstOffset),
   (5, .selectLocalBaseOccurrence), (6, .selectLocalBaseWordIndex),
   (7, .selectLocalRankBefore), (8, .selectLocalFirstOffset),
   (9, .selectLongFlagRankSuperTrue), (10, .selectLongFlagRankBlockTrue),
   (11, .selectLongFlagBits), (12, .selectLongRelative),
   (13, .selectSparseRankSuperTrue), (14, .selectSparseRankBlockTrue),
   (15, .selectSparseFlagBits), (16, .selectSparseRelative)]

def descriptorJson (n : Nat)
    (pair : Nat × ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Json :=
  let s := pair.2
  let bits0 := packedReviewerSourceBitLength n 0 0 s
  let count0 := packedReviewerSourceWordCount n 0 0 s
  jo [("segment", jn pair.1),
      ("stride", jn (packedSourceStride n s)),
      ("bits0", jn bits0),
      ("bitsLong1", jn (packedReviewerSourceBitLength n 1 0 s - bits0)),
      ("bitsSparse1", jn (packedReviewerSourceBitLength n 0 1 s - bits0)),
      ("count0", jn count0),
      ("countLong1", jn (packedReviewerSourceWordCount n 1 0 s - count0)),
      ("countSparse1", jn (packedReviewerSourceWordCount n 0 1 s - count0))]

def descriptorsFit (n lc sc : Nat) : Bool := sources.all fun pair =>
  let s := pair.2
  let b := packedReviewerSourceBitLength n 0 0 s
  let c := packedReviewerSourceWordCount n 0 0 s
  decide (packedReviewerSourceBitLength n lc sc s =
      b + lc * (packedReviewerSourceBitLength n 1 0 s - b) +
        sc * (packedReviewerSourceBitLength n 0 1 s - b)) &&
    decide (packedReviewerSourceWordCount n lc sc s =
      c + lc * (packedReviewerSourceWordCount n 1 0 s - c) +
        sc * (packedReviewerSourceWordCount n 0 1 s - c))

def interiorComponents : List PackedReviewerInteriorComponentTag :=
  [.baseline, .minRel, .maxRel, .argOffset, .localOffset, .globalBlock,
    .localLevel, .globalLevel]

def interiorJson (n : Nat) (c : PackedReviewerInteriorComponentTag) : Json := jo
  [("component", js (reprStr c)), ("entries", jn (packedReviewerInteriorEntryCount n c)),
   ("width", jn (packedReviewerInteriorEntryWidth n c)),
   ("wordPrefix", jn (packedReviewerInteriorComponentWordPrefix n c)),
   ("bitPrefix", jn (packedReviewerInteriorComponentBitPrefix n c)),
   ("wordCount", jn (packedReviewerInteriorComponentWordCount n c))]

def geometryJson (n : Nat) : Json :=
  let l := packedInteriorLayout n
  let off := packedInteriorOffsets n
  let ld := SuccinctClose.bpSparseLevelDomain l.macroSize
  let gd := SuccinctClose.bpSparseLevelDomain l.macroSampleCount
  jo [("sourceDescriptors", ja (sources.map (descriptorJson n))),
      ("interiorComponents", ja (interiorComponents.map (interiorJson n))),
      ("vmGlobals", jo [("BPW", jn (packedBpCodeWordWidth n)),
        ("B", jn l.blockSize), ("C", jn (packedFringeChunkBits n)),
        ("S", jn l.blocksPerSuper), ("NB", jn l.blockCount),
        ("NS", jn l.superSampleCount), ("M", jn l.macroSize),
        ("MC", jn l.macroSampleCount), ("LC", jn l.levelCount),
        ("GC", jn l.globalLevelCount), ("RW", jn l.relativeWidth),
        ("OW", jn l.offsetWidth), ("BAW", jn l.blockAddressWidth),
        ("LD", jn ld), ("GD", jn gd),
        ("LW", jn (SuccinctClose.bpSparseLevelWidth ld)),
        ("GW", jn (SuccinctClose.bpSparseLevelWidth gd)),
        ("OFF_BASELINE", jn off.baseline), ("OFF_MIN", jn off.minRel),
        ("OFF_MAX", jn off.maxRel), ("OFF_ARG", jn off.argOffset),
        ("OFF_LOCAL", jn off.localOffset), ("OFF_GLOBAL", jn off.globalBlock),
        ("OFF_LOCAL_LEVEL", jn off.localLevel),
        ("OFF_GLOBAL_LEVEL", jn off.globalLevel),
        ("OFF_DEAD", jn (packedInteriorComponentWords n))]),
      ("layout", jo [("blockSize", jn l.blockSize),
        ("blocksPerSuper", jn l.blocksPerSuper), ("blockCount", jn l.blockCount),
        ("relativeWidth", jn l.relativeWidth), ("superSampleCount", jn l.superSampleCount),
        ("superWidth", jn (packedBpCodeWordWidth n)), ("macroSize", jn l.macroSize),
        ("macroSampleCount", jn l.macroSampleCount), ("offsetWidth", jn l.offsetWidth),
        ("levelCount", jn l.levelCount), ("globalLevelCount", jn l.globalLevelCount),
        ("blockAddressWidth", jn l.blockAddressWidth)]),
      ("packedFringeWidth", jn (packedReviewerFringeWidth n)),
      ("packedSelectChunkWidth", jn (packedReviewerSelectChunkWidth n)),
      ("packedFringeCount", jn (packedReviewerFringeCount n)),
      ("packedSelectChunkCount", jn (packedReviewerSelectChunkCount n)),
      ("interiorOverhead", jn (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n)),
      ("fringeOverhead", jn (SuccinctClose.bpFringeTableOverhead n)),
      ("packedSuperSlots", jn (packedSuperSlots n)),
      ("packedSparseSlots", jn (packedSparseSlots n)),
      ("packedLongFlagWordSize", jn (packedLongFlagWordSize n)),
      ("packedSparseWordSize", jn (packedSparseWordSize n)),
      ("packedBpCodeWordWidth", jn (packedBpCodeWordWidth n)),
      ("packedFringeChunkBits", jn (packedFringeChunkBits n)),
      ("packedSelectWordSize", jn (packedSelectWordSize n)),
      ("packedSelectSuperStride", jn (packedSelectSuperStride n)),
      ("packedSelectLocalStride", jn (packedSelectLocalStride n)),
      ("packedSelectLocalSlotsPerSuper", jn (packedSelectLocalSlotsPerSuper n)),
      ("preludeWordIndex", jn (packedReviewerSparsePreludeWordIndex n)),
      ("preludeWordOffset", jn (packedReviewerSparsePreludeWordOffset n))]

def referenceAnswer (xs : List Int) (left right : Nat) : Option Nat :=
  if left < right ∧ right ≤ xs.length then
    let best := xs.zipIdx.foldl (fun best pair =>
      if left ≤ pair.2 ∧ pair.2 < right then
        match best with
        | none => some pair
        | some old => if pair.1 < old.1 then some pair else best
      else best) (none : Option (Int × Nat))
    best.map Prod.snd
  else none

def input (n : Nat) (pattern : String) : List Int :=
  (List.range n).map fun i =>
    if pattern == "ascending" then Int.ofNat i
    else if pattern == "descending" then Int.ofNat (n - i)
    else if pattern == "ties" then 3
    else if pattern == "comb" then
      if i == 0 then 0 else Int.ofNat (n - i)
    else if pattern == "zigzag" then
      if i % 2 == 0 then Int.ofNat (n - i / 2) else -(Int.ofNat (i / 2 + 1))
    else (([3, 2, 3, 1, 3, 2, 3, 0] : List Int)[i % 8]?).getD 0

def hasPhase (es : List LogicalDumpEvent) (phase : String) : Bool :=
  es.any (fun e => e.phase == phase)

def buildFixture (n : Nat) (pattern : String) (left right : Nat) : IO (Json × Bool) := do
  let xs := input n pattern
  let valid := decide (left < right ∧ right ≤ n)
  let shape := SuccinctClassic.cartesianShape xs
  let memory := packedReviewerMemory shape
  let width := packedReviewerCellWidth n
  let lc := longCount shape
  let sc := packedReviewerSparseCount shape
  let physical := packedReviewerRunAgainstMemory memory n left right
  let logical := if valid then
    logicalDump n lc sc memory 210 (packedReviewerWholeStart n left right)
    else ([], some none)
  let expected := referenceAnswer xs left right
  let wholePhysicalAddresses := physical.trace.filterMap fun e =>
    match e.request.origin with
    | .wholeQuery _ => some e.request.address
    | _ => none
  let planAddresses := logical.1.flatMap (fun e => e.plan)
  let lcaEvent := logical.1.find? fun e =>
    e.request.invocation.instruction == .lcaClose
  let leftClose := (lcaEvent.map (fun e => e.request.invocation.argument)).getD 0
  let rightClose := (lcaEvent.map (fun e => e.request.invocation.argument2)).getD 0
  let blockSize := packedSummaryBlockSizeRaw n
  let leftBlock := SuccinctClose.blockOfClose blockSize leftClose
  let rightBlock := SuccinctClose.blockOfClose blockSize rightClose
  let interior := logical.1.any (fun e => e.request.segment == 20)
  let crossing := physical.trace.any (fun e => e.request.cellCount == 2)
  let allPhases := hasPhase logical.1 "leftSelect" && hasPhase logical.1 "rightSelect" &&
    hasPhase logical.1 "leftFringe" && hasPhase logical.1 "rightFringe" &&
    hasPhase logical.1 "finalRank" && interior && crossing
  let sameTerminal := decide (physical.terminal = logical.2)
  let answerMatches := decide (physical.terminal = some expected)
  let receiptsMatch := decide (wholePhysicalAddresses = planAddresses)
  let repliesMatch := physical.trace.all fun e =>
    decide (memory[e.request.address]? = e.reply)
  let coefficientsMatch := descriptorsFit n lc sc &&
    ([0, 1, 2, 7] : List Nat).all (fun a =>
      ([0, 1, 2, 7] : List Nat).all (fun b => descriptorsFit n a b))
  let wholePathCovered := valid && allPhases && decide (leftBlock + 1 < rightBlock)
  let acceptable := sameTerminal && answerMatches && receiptsMatch &&
    repliesMatch && coefficientsMatch && !physical.failed
  let coverage := jo [("validQuery", toJson valid),
    ("wholePathCovered", toJson wholePathCovered),
    ("leftSelect", toJson (hasPhase logical.1 "leftSelect")),
    ("rightSelect", toJson (hasPhase logical.1 "rightSelect")),
    ("leftFringe", toJson (hasPhase logical.1 "leftFringe")),
    ("rightFringe", toJson (hasPhase logical.1 "rightFringe")),
    ("interiorSegment20", toJson interior),
    ("finalRank", toJson (hasPhase logical.1 "finalRank")),
    ("crossingPhysicalRead", toJson crossing),
    ("sameTerminal", toJson sameTerminal), ("answerMatches", toJson answerMatches),
    ("wholePhysicalReceiptsMatch", toJson receiptsMatch),
    ("physicalRepliesMatchMemory", toJson repliesMatch),
    ("affineDescriptorsMatch", toJson coefficientsMatch),
    ("accepted", toJson acceptable)]
  IO.println s!"Fixture n={n} pattern={pattern} query=[{left},{right}) cells={memory.length} w={width} physical={physical.trace.length} logical={logical.1.length} closes={leftClose},{rightClose} blocks={leftBlock},{rightBlock} answer={expected}"
  IO.println coverage.compress
  pure (jo [("schema", js "rc6-packed-whole-path-v1"),
    ("sourceCommit", js "4639223bc8130b0ef752270b5cbdd74325abcd60"),
    ("input", ja (xs.map (fun v => js (toString v)))), ("pattern", js pattern),
    ("n", jn n), ("left", jn left), ("right", jn right), ("cellWidth", jn width),
    ("cells", ja (memory.map (fun bs => natString (SuccinctSpace.bitsToNatLE bs)))),
    ("allocatedBits", jn (memory.length * width)),
    ("geometry", geometryJson n),
    ("reference", jo [("answer", match expected with | none => .null | some i => jn i),
      ("longCount", jn lc), ("sparseCount", jn sc), ("leftClose", jn leftClose),
      ("rightClose", jn rightClose), ("leftBlock", jn leftBlock), ("rightBlock", jn rightBlock),
      ("terminal", terminalJson physical.terminal), ("failed", toJson physical.failed),
      ("physicalTrace", ja (physical.trace.map (physicalJson n))),
      ("logicalTrace", ja (logical.1.map logicalJson))]),
    ("coverage", coverage)], acceptable)

end WholePathFixture

def main (args : List String) : IO UInt32 := do
  let output := args[0]?.getD "fixture.json"
  let n := ((args[1]?).bind String.toNat?).getD 9
  let pattern := args[2]?.getD "balanced"
  let left := ((args[3]?).bind String.toNat?).getD 0
  let right := ((args[4]?).bind String.toNat?).getD n
  unless (["balanced", "ascending", "descending", "ties", "zigzag", "comb"] : List String).contains pattern do
    throw (IO.userError s!"Unknown pattern: {pattern}")
  let (json, accepted) ← WholePathFixture.buildFixture n pattern left right
  IO.FS.writeFile output (json.pretty ++ "\n")
  IO.println s!"Wrote reference fixture to {output}"
  pure (if accepted then 0 else 2)
