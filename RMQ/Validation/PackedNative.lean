import RMQ.Core.WordRAM.Native.Contract

/-! # Executable checks of the actual binary native source boundary

Frozen acceptance before implementation (native1-lean-validator-v1): VN-ENTRY
runs nativeLoadEntry on bytes, then nativeQueryEntry and nativeCore on that
loaded image; VN-ORACLE uses literal independent status/count/ordered-receipt
expectations; VN-REGISTRY pins the nonempty default roster separately and rejects
empty, malformed, unknown and duplicate selector channels; VN-COMPARE compares
the same source entry with an independently supplied exact UTF-8 expectation,
under explicit byte/hex/fuel bounds. VN-QUIET checks the real quiet projection;
VN-REPEAT reuses one loaded image across distinct queries. No reference run or
native result is used to manufacture an expected observation.

CLI: no arguments runs all cases; --case ID runs exactly one. The optional
NATIVE1_LEAN_SELECTOR environment variable carries id:ID, including an explicit
empty value on hosts whose process launcher otherwise drops empty arguments.
compare IMAGE LEFT_HEX RIGHT_HEX FUEL 0|1 EXPECTED_FILE uses little-endian byte
hex, strict decimal fuel, exact UTF-8 bytes and LF endings (no normalization).
All failures return exit 1 and a NATIVE1-LEAN ERROR diagnostic on stderr.
-/

namespace RMQ.Validation.PackedNative

open RMQ.SuccinctFinal.PackedNative RMQ.SuccinctFinal.PackedWordRAM

def registryVersion : String := "native1-lean-validator-v1"
def selectorVariable : String := "NATIVE1_LEAN_SELECTOR"

def bytes (values : List UInt8) : ByteArray := ⟨values.toArray⟩
def endpoint (width value : Nat) : ByteArray := ⟨LimbWord.encode width value⟩

structure Attempt where
  left : ByteArray
  right : ByteArray
  fuel : Nat := 16
  reads : Bool := true
  expected : Except String String

structure Fixture where
  id : String
  input : ByteArray
  rejectLoad : Bool := false
  attempts : List Attempt := []

def query (width left right : Nat) (expected : String) (reads : Bool := true)
    (fuel : Nat := 16) : Attempt :=
  ⟨endpoint width left, endpoint width right, fuel, reads, .ok expected⟩

/-- Three actual loads, including a repeated address, then sum the first two values. -/
def readImage : StorageImage := StorageImage.fromReference 8 2 8
  [.constant 3 0, .load 4 3, .constant 3 1, .load 5 3,
   .constant 3 0, .load 6 3, .arithmetic .add 7 4 5, .halt 7] [23, 7]

def arithmeticImage (width : Nat) (op : Arithmetic) : StorageImage :=
  StorageImage.fromReference width 0 4 [.arithmetic op 3 0 1, .halt 3] []

def echoImage (width : Nat) : StorageImage :=
  StorageImage.fromReference width 0 3 [.halt 0] []

/-- 2^175+37 and 2^174+19, written as 22 literal little-endian bytes. -/
def wideLeft : ByteArray := bytes
  [37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,128]
def wideRight : ByteArray := bytes
  [19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64]

def fixtures : List Fixture := [
  { id := "load-query-ordered", input := readImage.encode, attempts := [
    query 8 0 2 "halted 30\n8\n3 3 1 0 0 1\n0 23\n1 7\n0 23\n"] },
  { id := "endpoint-order-176", input := (arithmeticImage 176 .sub).encode, attempts := [
    { left := wideLeft, right := wideRight,
      expected := .ok "halted 23945242826029513411849172299223580994042798784118802\n2\n0 0 1 0 0 1\n\n" }] },
  { id := "arithmetic-zero-divisor", input := (arithmeticImage 8 .div).encode, attempts := [
    query 8 17 0 "fault\n1\n0 0 1 0 0 0\n\n"] },
  { id := "arithmetic-overflow", input := (arithmeticImage 8 .add).encode, attempts := [
    query 8 255 1 "fault\n1\n0 0 1 0 0 0\n\n"] },
  { id := "arithmetic-overshift", input := (arithmeticImage 8 .shl).encode, attempts := [
    query 8 1 8 "fault\n1\n0 0 1 0 0 0\n\n"] },
  { id := "missing-memory", input :=
      (StorageImage.fromReference 8 1 4 [.load 3 0, .halt 3] [23]).encode,
    attempts := [query 8 1 0 "fault\n1\n1 0 0 0 0 0\n1 none\n"] },
  { id := "missing-fetch", input := (StorageImage.fromReference 8 0 3 [] []).encode,
    attempts := [query 8 0 0 "running\n0\n0 0 0 0 0 0\n\n"] },
  { id := "invalid-endpoint-padding", input := (echoImage 9).encode, attempts := [
    { left := bytes [0,2], right := bytes [0,0],
      expected := .error "noncanonical query word" }] },
  { id := "invalid-endpoint-length", input := (echoImage 176).encode, attempts := [
    { left := bytes [0], right := endpoint 176 0,
      expected := .error "noncanonical query word" }] },
  { id := "malformed-padding", input :=
      (StorageImage.mk 9 0 3 (LimbMachine.encodeCode 9 [.halt 0]) #[#[0,2]]).encode,
    rejectLoad := true },
  { id := "malformed-length", input :=
      (StorageImage.mk 9 0 3 (LimbMachine.encodeCode 9 [.halt 0]) #[#[0]]).encode,
    rejectLoad := true },
  { id := "malformed-version", input := bytes [82,77,81,78,2], rejectLoad := true },
  { id := "truncated-image", input := readImage.encode.extract 0 (readImage.encode.size - 1),
    rejectLoad := true },
  { id := "repeated-loaded-image", input := (echoImage 8).encode, attempts := [
    query 8 7 0 "halted 7\n1\n0 0 0 0 0 1\n\n",
    query 8 19 0 "halted 19\n1\n0 0 0 0 0 1\n\n",
    query 8 7 0 "halted 7\n1\n0 0 0 0 0 1\n\n"] },
  { id := "reads-false-projection", input := readImage.encode, attempts := [
    query 8 0 2 "halted 30\n8\n3 3 1 0 0 1\n\n" false] },
  { id := "fuel-exhaustion", input := readImage.encode, attempts := [
    query 8 0 2 "running\n2\n1 1 0 0 0 0\n0 23\n" true 2] }
]

/-- Independent roster: deleting, renaming, duplicating or reordering a case fails. -/
def requiredIDs : List String := [
  "load-query-ordered", "endpoint-order-176", "arithmetic-zero-divisor",
  "arithmetic-overflow", "arithmetic-overshift", "missing-memory", "missing-fetch",
  "invalid-endpoint-padding", "invalid-endpoint-length", "malformed-padding",
  "malformed-length", "malformed-version", "truncated-image", "repeated-loaded-image",
  "reads-false-projection", "fuel-exhaustion"]

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def checkAttempt (id : String) (image : StorageImage) (attempt : Attempt) : IO Unit := do
  let actual := nativeQueryEntry image attempt.left attempt.right attempt.fuel attempt.reads
  match actual, attempt.expected with
  | .ok text, .ok expected =>
    check (text.toUTF8.data == expected.toUTF8.data) (id ++ ": observation mismatch")
    let core := nativeCore image attempt.left.data attempt.right.data attempt.fuel attempt.reads
    check (nativeObservationText core == text) (id ++ ": actual core/entry mismatch")
    if !attempt.reads then
      let logged := nativeCore image attempt.left.data attempt.right.data attempt.fuel true
      check (core.2.readsRev.isEmpty && core.1.regs == logged.1.regs &&
        core.1.pc == logged.1.pc && core.1.status.decode == logged.1.status.decode &&
        core.2.steps == logged.2.steps && decide (core.2.counts = logged.2.counts))
        (id ++ ": quiet projection mismatch")
  | .error error, .error expected => check (error == expected) (id ++ ": error mismatch")
  | .error error, .ok _ => throw (IO.userError (id ++ ": unexpected query rejection: " ++ error))
  | .ok _, .error _ => throw (IO.userError (id ++ ": expected query rejection"))

def runFixture (fixture : Fixture) : IO Unit := do
  check (fixture.rejectLoad == fixture.attempts.isEmpty)
    (fixture.id ++ ": malformed case contract")
  match nativeLoadEntry fixture.input with
  | .error error =>
    check (fixture.rejectLoad && error == "invalid or unsupported binary image")
      (fixture.id ++ ": unexpected load rejection")
  | .ok image =>
    check (!fixture.rejectLoad) (fixture.id ++ ": expected load rejection")
    check (image.encode.data == fixture.input.data) (fixture.id ++ ": loaded byte identity mismatch")
    for attempt in fixture.attempts do checkAttempt fixture.id image attempt
  IO.println ("NATIVE1-LEAN CASE " ++ fixture.id ++ " PASS")

def findFixture (id : String) : IO Fixture := do
  check (!id.trim.isEmpty) "explicitly empty selector"
  check (id.toList.all fun c => "abcdefghijklmnopqrstuvwxyz0123456789-".contains c)
    "malformed selector"
  match fixtures.find? (fun fixture => fixture.id == id) with
  | some fixture => return fixture
  | none => throw (IO.userError ("unknown selector: " ++ id))

def selection (args : List String) : IO (Option Fixture) := do
  let channel ← IO.getEnv selectorVariable
  match args, channel with
  | [], none => return none
  | ["--case", id], none => return some (← findFixture id)
  | [], some encoded =>
    check (encoded.startsWith "id:") "malformed selector channel"
    return some (← findFixture (encoded.drop 3))
  | _ :: _, some _ => throw (IO.userError "selector given twice")
  | _, _ => throw (IO.userError "expected no arguments, --case ID, or compare mode")

/-- Read only bounded chunks. File growth cannot bypass the byte limit. -/
def readBoundedAux (handle : IO.FS.Handle) (remaining : Nat) (out : ByteArray) : IO ByteArray := do
  if remaining = 0 then return out
  let chunk ← handle.read ((min remaining 65536).toUSize)
  if _hz : chunk.size = 0 then return out
  else
    if _hb : chunk.size ≤ remaining then
      readBoundedAux handle (remaining - chunk.size) (out ++ chunk)
    else throw (IO.userError "file reader exceeded requested bound")
termination_by remaining
decreasing_by omega

def readBounded (path : System.FilePath) (limit : Nat) : IO ByteArray := do
  let metadata ← path.metadata
  check (metadata.type == .file) "input path is not a regular file"
  check (metadata.byteSize.toNat ≤ limit) "file exceeds byte limit"
  let data ← IO.FS.withFile path .read fun handle => readBoundedAux handle (limit + 1) .empty
  check (data.size ≤ limit) "file grew beyond byte limit"
  return data

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def parseHexAux : List Char → ByteArray → Option ByteArray
  | [], out => some out
  | high :: low :: rest, out => do
      let hi ← hexDigit high
      let lo ← hexDigit low
      parseHexAux rest (out.push (UInt8.ofNat (16 * hi + lo)))
  | _, _ => none

def parseEndpoint (input : String) (width : Nat) : IO ByteArray := do
  check (input.utf8ByteSize ≤ 1024) "endpoint hex exceeds byte limit"
  check (input.utf8ByteSize = 2 * LimbWord.limbCount width) "endpoint hex length mismatch"
  match parseHexAux input.toList .empty with
  | some value => return value
  | none => throw (IO.userError "malformed endpoint hex")

def parseFuel (input : String) : IO Nat := do
  check (!input.isEmpty && input.utf8ByteSize ≤ 7 && input.toList.all Char.isDigit)
    "malformed or oversized fuel"
  match input.toNat? with
  | some fuel =>
    check (fuel ≤ nativeFuelLimit) "fuel exceeds native limit"
    return fuel
  | none => throw (IO.userError "malformed fuel")

def compareFiles (imagePath leftHex rightHex fuelText readsText expectedPath : String) : IO Unit := do
  check ((← IO.getEnv selectorVariable).isNone) "selector is incompatible with compare mode"
  let fuel ← parseFuel fuelText
  let reads ← match readsText with
    | "0" => pure false
    | "1" => pure true
    | _ => throw (IO.userError "READS must be exactly 0 or 1")
  check (leftHex.utf8ByteSize ≤ 1024 && rightHex.utf8ByteSize ≤ 1024)
    "endpoint hex exceeds byte limit"
  let input ← readBounded ⟨imagePath⟩ nativeLimits.maxFileBytes
  let expected ← readBounded ⟨expectedPath⟩ nativeLimits.maxFileBytes
  check (String.fromUTF8? expected).isSome "expected observation is not UTF-8"
  let image ← match nativeLoadEntry input with
    | .ok image => pure image
    | .error error => throw (IO.userError ("load rejected: " ++ error))
  let left ← parseEndpoint leftHex image.width
  let right ← parseEndpoint rightHex image.width
  let actual ← match nativeQueryEntry image left right fuel reads with
    | .ok text => pure text
    | .error error => throw (IO.userError ("query rejected: " ++ error))
  check (actual.toUTF8.data == expected.data) "comparison observation mismatch"
  IO.println ("NATIVE1-LEAN COMPARE PASS bytes=" ++ toString input.size ++
    " fuel=" ++ toString fuel ++ " reads=" ++ readsText)

def mainImpl (args : List String) : IO Unit := do
  check (!requiredIDs.isEmpty && fixtures.map (·.id) == requiredIDs)
    "registry mismatch, missing, reordered or duplicate case"
  match args with
  | ["compare", image, left, right, fuel, reads, expected] =>
    compareFiles image left right fuel reads expected
  | _ =>
    let chosen ← selection args
    let selected := match chosen with | none => fixtures | some fixture => [fixture]
    check (!selected.isEmpty) "zero-case selection"
    let mut executed : List String := []
    for fixture in selected do
      runFixture fixture
      executed := fixture.id :: executed
    check (executed.reverse == selected.map (·.id)) "executed/expected case registry mismatch"
    let mode := if chosen.isNone then "full" else "selected"
    IO.println ("NATIVE1-LEAN PASS registry=" ++ registryVersion ++
      " executed=" ++ toString executed.length ++ " expected=" ++ toString selected.length ++
      " mode=" ++ mode)

end RMQ.Validation.PackedNative

def main (args : List String) : IO UInt32 := do
  try
    RMQ.Validation.PackedNative.mainImpl args
    return 0
  catch error =>
    (← IO.getStderr).putStrLn ("NATIVE1-LEAN ERROR " ++ error.toString)
    return 1
