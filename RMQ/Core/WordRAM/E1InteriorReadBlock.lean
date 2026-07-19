import RMQ.Core.WordRAM.E1CrossBlockArm

/-!
# E1 amended machine: the interior's ATOMIC TABLE READ (M3d-11)

Every memory read the interior leg performs is one instance of a single
route-side primitive:

    FixedWidthNatTable.machineReadComputationAt wordSize base dead i
      (`MachineChunkedTableProgram.lean:343`)

wrapped as `canonicalRelativeRmmMachineReadNatComputation`
(`InteriorDirectory.lean:2132`).  The interior's maximising branch makes
exactly ELEVEN such calls per two-span and THIRTY-THREE in total
(`canonicalRelativeRmmMachineCrossMacroCandidateCosted_cost_le_thirty_three_of_macro_crossing`,
`InteriorDirectory.lean:5412`), so this one block is the atom that the whole
interior simulation is built from.  It is landed and certified on its own,
before any composite, because a defect here multiplies by thirty-three.

## Why the primitive is single-read, and where that is conditional

The route's adapter reads `fixedWidthNatTableMachineChunkCount width wordSize`
consecutive words (`MachineChunkedTable.lean:12`), which is
`width / wordSize + (if width % wordSize = 0 then 0 else 1)`.  That is a
VARIABLE count in general, and a machine block for the general case would be
an uncapped loop -- the very defect that blocked this rung before B7.

It is not variable here, and the reason is checked rather than assumed:
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:4060`) derives `chunkCount <= 1` from
`width <= machineWordBits`.  This module carries the matching hypotheses
`0 < width` and `width <= wordSize` EXPLICITLY on the bridge theorem
(`interiorReadNat_reads_eq_route`), so the single-read shape is a stated
obligation of every consumer rather than a silent property of the current
tables.  `0 < width` is the half the cost bound does not need: at `width = 0`
the route reads NOTHING and this block would over-read by one.  That
asymmetry is recorded here because it is exactly the kind of off-by-one an
`<= 1` cost bound hides.

## The block

Seven instructions, ONE branch, exactly ONE `readMem`.  The dead-address
path is the fall-through and the live path is the taken branch, so the
route's `if i < entries.length` is decided by a machine comparison on the
machine's own index register -- not by a Lean-level `if` outside the machine.

    Q+0  const  iT entriesLen
    Q+1  natLt  iT iIdx iT        -- iT := (i < entriesLen)
    Q+2  const  iA base
    Q+3  add    iA iA iIdx        -- iA := base + i        (live address)
    Q+4  brNZ   iT (Q+6)          -- valid: skip the override
    Q+5  const  iA deadAddress    -- invalid: dead address
    Q+6  readMem iVal segment iA
    Q+7                            -- exit

The category log is a FUNCTION of the route-side condition
(`interiorReadNatCats`), never a numeral: the live path charges six steps
and the dead path seven, and which one is charged is determined by the same
`i < entriesLen` the route branches on.

## Option encoding

The route decodes with `fixedWidthNatTableMachineDecode`
(`MachineChunkedTable.lean:215`), which at one chunk is
`word?.map bitsToNatLE`.  The machine decodes with `decodeRead`
(`E1Machine.lean:139`), which is `bitsToNatLE word + 1` on a hit and `0` on
a miss.  So the machine register carries the route's `Option Nat` in the
development's standing option-shift convention, and read success is testable
by one comparison against `0`.  `interiorReadNat_value_eq_route` states that
correspondence.
-/

namespace RMQ
namespace WordRAM
namespace E1InteriorReadBlock

open E1Machine
open RMQ.SuccinctSpace

/-! ## Register bank extension (interior, `85 .. 88`)

The bank below `85` is fully allocated: `40 .. 62` fold, `63 .. 68` arm,
`69 .. 71` same-block, `72 .. 74` dispatch, `75 .. 84` three-way merge
(`E1CandMerge3.lean:97`).  The interior opens a fresh bank at `85` so that
none of its scratch overlaps the merge slots `mLV`/`mLP`/`mMV`/`mMP` the
cross-block composition requires it to preserve. -/

/-- Table index to read (input). -/
abbrev iIdx : Nat := 85
/-- Decoded cell, option-shifted (`0` = `none`, `v + 1` = `some v`). -/
abbrev iVal : Nat := 86
/-- Physical address scratch. -/
abbrev iA : Nat := 87
/-- Comparison scratch. -/
abbrev iT : Nat := 88

/-! ## The block -/

/--
The atomic table read at base `Q` (seven instructions, exit `Q + 7`).

`segment` is the interior's canonical component segment, `base` the table's
offset inside it, `deadAddress` the shared dead word, and `entriesLen` the
table's logical entry count -- all per-shape program constants.  The index
comes from the machine register `iIdx`.
-/
def interiorReadNat (segment base deadAddress entriesLen Q : Nat) :
    List Instr :=
  [ .const iT entriesLen        -- Q+0
  , .natLt iT iIdx iT           -- Q+1
  , .const iA base              -- Q+2
  , .add iA iA iIdx             -- Q+3
  , .brNZ iT (Q + 6)            -- Q+4
  , .const iA deadAddress       -- Q+5
  , .readMem iVal segment iA ]  -- Q+6

@[simp] theorem interiorReadNat_length
    (segment base deadAddress entriesLen Q : Nat) :
    (interiorReadNat segment base deadAddress entriesLen Q).length = 7 := rfl

/-- The physical address the block reads: the route's own case split
(`machineReadComputationAt`, `MachineChunkedTableProgram.lean:343`) at one
chunk, where `fixedWidthNatTableMachineFootprintAt base width wordSize i`
is the singleton `[base + i]`. -/
def interiorReadAddr (base deadAddress entriesLen i : Nat) : Nat :=
  if i < entriesLen then base + i else deadAddress

/--
Category log, indexed by the route-side validity condition the block
dispatches on.  Never a numeral: the live path is six steps, the dead path
seven, and the index is the same predicate the route branches on.
-/
def interiorReadNatCats (valid : Bool) : List Category :=
  if valid then
    [.registerWrite, .comparison, .registerWrite, .arithmetic, .branch,
      .memoryRead]
  else
    [.registerWrite, .comparison, .registerWrite, .arithmetic, .branch,
      .registerWrite, .memoryRead]

@[simp] theorem interiorReadNatCats_live :
    (interiorReadNatCats true).length = 6 := rfl

@[simp] theorem interiorReadNatCats_dead :
    (interiorReadNatCats false).length = 7 := rfl

/-- Exactly one charged memory read on EITHER path.  This is the block's
central accounting fact: the dead path costs one more controller step but
not one more read, matching the route's `machineReadCostedWithStore_cost`
(`MachineChunkedTable.lean:240`), which charges `1` for an invalid index. -/
theorem interiorReadNatCats_memoryRead_count (valid : Bool) :
    ((interiorReadNatCats valid).filter (· == Category.memoryRead)).length
      = 1 := by
  cases valid <;> rfl

/-- The block writes only its two scratch registers and its output; the
index register `iIdx` is read-only, so a caller may keep an index live
across the read. -/
abbrev InteriorReadNatUntouched (r : Nat) : Prop :=
  r ≠ iVal ∧ r ≠ iA ∧ r ≠ iT

/-! ## Width certificate -/

/--
Constructor-exhaustive width certificate for the atomic read.  No wildcard
arm: each of the seven instructions discharges its own constructor's field
conjunction from `Instr.FieldsFit` (`E1Machine.lean:501`).  The block carries
no divisor, so no positivity arm arises.

The three per-shape constants (`base`, `deadAddress`, `entriesLen`) and the
segment are hypotheses rather than assumptions about the current tables: a
shape whose component store outgrew the modeled width fails this certificate
instead of silently producing an oversized immediate.
-/
theorem interiorReadNat_fits (w segment base deadAddress entriesLen Q : Nat)
    (hw : 88 < 2 ^ w) (hQ : Q + 6 < 2 ^ w) (hseg : segment < 2 ^ w)
    (hbase : base < 2 ^ w) (hdead : deadAddress < 2 ^ w)
    (hlen : entriesLen < 2 ^ w) :
    ∀ instr ∈ interiorReadNat segment base deadAddress entriesLen Q,
      Instr.FieldsFit w instr := by
  intro instr hinstr
  have h85 : (85 : Nat) < 2 ^ w := by omega
  have h86 : (86 : Nat) < 2 ^ w := by omega
  have h87 : (87 : Nat) < 2 ^ w := by omega
  have h88 : (88 : Nat) < 2 ^ w := hw
  simp only [interiorReadNat, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h | h | h | h | h | h <;> subst h
  · exact ⟨h88, hlen⟩
  · exact ⟨h88, h85, h88⟩
  · exact ⟨h87, hbase⟩
  · exact ⟨h87, h87, h85⟩
  · exact ⟨h88, hQ⟩
  · exact ⟨h87, hdead⟩
  · exact ⟨h86, hseg, h87⟩

/-! ## Exact simulation -/

/--
EXACT SIMULATION OF THE ATOMIC TABLE READ.

The receipt is a POSITIONAL singleton at the address the route's adapter
issues; the category log is indexed by the route's own validity condition;
the output register carries the route's decoded cell in the option-shift
convention; and every register outside the block's three-register write set
is preserved.

The validity test is performed BY THE MACHINE (`natLt` at `Q + 1` on the
machine's index register, branched on at `Q + 4`), not by a Lean-level `if`
around the block -- which is what REQ-E1-05's anti-vacuity challenge demands
of a guard and what makes the dead-address path a charged path rather than a
meta-level fallback.
-/
theorem interiorReadNat_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {segment base deadAddress entriesLen Q : Nat}
    (hHost : HostedAt program Q
      (interiorReadNat segment base deadAddress entriesLen Q))
    (regs : RegFile) (i : Nat) (hIdx : regs iIdx = i) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 7, false⟩
        [.readWord segment (interiorReadAddr base deadAddress entriesLen i)
          (store.readWord? segment
            (interiorReadAddr base deadAddress entriesLen i))]
        (interiorReadNatCats (decide (i < entriesLen))) ∧
      regs' iVal =
        decodeRead (store.readWord? segment
          (interiorReadAddr base deadAddress entriesLen i)) ∧
      (∀ r, InteriorReadNatUntouched r → regs' r = regs r) := by
  have hf : ∀ (k m : Nat) (instr : Instr), k < 7 ->
      (interiorReadNat segment base deadAddress entriesLen Q)[k]? =
        some instr -> Q + k = m -> program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [<- hm, hHost k hk, hget]
  have h0 : program[Q]? = some (.const iT entriesLen) :=
    hf 0 Q _ (by omega) rfl (by omega)
  have h1 : program[Q + 1]? = some (.natLt iT iIdx iT) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[Q + 2]? = some (.const iA base) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[Q + 3]? = some (.add iA iA iIdx) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[Q + 4]? = some (.brNZ iT (Q + 6)) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[Q + 5]? = some (.const iA deadAddress) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[Q + 6]? = some (.readMem iVal segment iA) :=
    hf 6 _ _ (by omega) rfl (by omega)
  -- Q+0: pin the entry count
  have r0 : RunsTo store program ⟨regs, Q, false⟩
      ⟨regs.write iT entriesLen, Q + 1, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨regs, Q, false⟩ : State)) rfl h0
    simpa using h
  -- Q+1: the validity comparison, on the machine's own index register
  have r1 : RunsTo store program ⟨regs.write iT entriesLen, Q + 1, false⟩
      ⟨(regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0), Q + 2, false⟩ []
      [Category.comparison] := by
    have h := RunsTo.natLt (store := store)
      (s := (⟨regs.write iT entriesLen, Q + 1, false⟩ : State)) rfl h1
    simpa [RegFile.write, iIdx, iT, hIdx] using h
  -- abbreviation for the register file after the comparison
  have r2 : RunsTo store program
      ⟨(regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0), Q + 2, false⟩
      ⟨((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base,
        Q + 3, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨(regs.write iT entriesLen).write iT
        (if i < entriesLen then 1 else 0), Q + 2, false⟩ : State)) rfl h2
    simpa using h
  have r3 : RunsTo store program
      ⟨((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base, Q + 3, false⟩
      ⟨(((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base).write iA
            (base + i), Q + 4, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.add (store := store)
      (s := (⟨((regs.write iT entriesLen).write iT
        (if i < entriesLen then 1 else 0)).write iA base,
        Q + 3, false⟩ : State)) rfl h3
    simpa [RegFile.write, iA, iIdx, hIdx] using h
  have hpre := (r0.trans r1).trans (r2.trans r3)
  by_cases hvalid : i < entriesLen
  · -- LIVE path: the branch is taken and the dead override is skipped
    have rbr : RunsTo store program
        ⟨(((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i), Q + 4, false⟩
        ⟨(((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i), Q + 6, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken (store := store)
        (s := (⟨(((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base).write iA
            (base + i), Q + 4, false⟩ : State)) rfl h4
        (by simp [RegFile.write, iA, iT, hvalid])
      simpa using h
    have rread : RunsTo store program
        ⟨(((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i), Q + 6, false⟩
        ⟨((((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i)).write iVal
                (decodeRead (store.readWord? segment (base + i))),
          Q + 7, false⟩
        [.readWord segment (base + i)
          (store.readWord? segment (base + i))] [Category.memoryRead] := by
      have h := RunsTo.readMem (store := store)
        (s := (⟨(((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base).write iA
            (base + i), Q + 6, false⟩ : State)) rfl h6
      simpa [RegFile.write, iA] using h
    refine ⟨((((regs.write iT entriesLen).write iT
      (if i < entriesLen then 1 else 0)).write iA base).write iA
        (base + i)).write iVal
          (decodeRead (store.readWord? segment (base + i))), ?_, ?_, ?_⟩
    · have hrun := hpre.trans (rbr.trans rread)
      simpa [interiorReadNatCats, interiorReadAddr, hvalid] using hrun
    · simp [RegFile.write, interiorReadAddr, hvalid]
    · intro r hr
      obtain ⟨hV, hA, hT⟩ := hr
      simp [RegFile.write, hV, hA, hT]
  · -- DEAD path: the branch falls through into the dead-address override
    have rbr : RunsTo store program
        ⟨(((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i), Q + 4, false⟩
        ⟨(((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i), Q + 5, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_not_taken (store := store)
        (s := (⟨(((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base).write iA
            (base + i), Q + 4, false⟩ : State)) rfl h4
        (by simp [RegFile.write, iA, iT, hvalid])
      simpa using h
    have rdead : RunsTo store program
        ⟨(((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i), Q + 5, false⟩
        ⟨((((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i)).write iA deadAddress, Q + 6, false⟩ []
        [Category.registerWrite] := by
      have h := RunsTo.const (store := store)
        (s := (⟨(((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base).write iA
            (base + i), Q + 5, false⟩ : State)) rfl h5
      simpa using h
    have rread : RunsTo store program
        ⟨((((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i)).write iA deadAddress, Q + 6, false⟩
        ⟨(((((regs.write iT entriesLen).write iT
            (if i < entriesLen then 1 else 0)).write iA base).write iA
              (base + i)).write iA deadAddress).write iVal
                (decodeRead (store.readWord? segment deadAddress)),
          Q + 7, false⟩
        [.readWord segment deadAddress
          (store.readWord? segment deadAddress)] [Category.memoryRead] := by
      have h := RunsTo.readMem (store := store)
        (s := (⟨((((regs.write iT entriesLen).write iT
          (if i < entriesLen then 1 else 0)).write iA base).write iA
            (base + i)).write iA deadAddress, Q + 6, false⟩ : State)) rfl h6
      simpa [RegFile.write, iA] using h
    refine ⟨(((((regs.write iT entriesLen).write iT
      (if i < entriesLen then 1 else 0)).write iA base).write iA
        (base + i)).write iA deadAddress).write iVal
          (decodeRead (store.readWord? segment deadAddress)), ?_, ?_, ?_⟩
    · have hrun := hpre.trans (rbr.trans (rdead.trans rread))
      simpa [interiorReadNatCats, interiorReadAddr, hvalid] using hrun
    · simp [RegFile.write, interiorReadAddr, hvalid]
    · intro r hr
      obtain ⟨hV, hA, hT⟩ := hr
      simp [RegFile.write, hV, hA, hT]

/-! ## Bridge to the route's adapter

The three theorems below are what make this block a statement about the
ROUTE rather than about itself: the route's own adapter, at one chunk,
issues exactly the address this block computes, emits exactly the receipt
this block emits, and decodes to exactly the value this block leaves in
`iVal` under the option-shift convention.
-/

/--
THE SINGLE-CHUNK OBLIGATION, STATED NOT ASSUMED.

`0 < width` and `width <= wordSize` together force the route's chunk count
to be exactly one.  The upper bound alone gives only `<= 1`
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`,
`InteriorDirectory.lean:4060`); the missing half is `0 < width`, and without
it a zero-width table reads NOTHING while this block still reads once.  That
is why both hypotheses travel together on every consumer below.
-/
theorem chunkCount_eq_one {width wordSize : Nat}
    (hwidth0 : 0 < width) (hwidth : width ≤ wordSize) :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount width wordSize = 1 := by
  unfold SuccinctSpace.fixedWidthNatTableMachineChunkCount
  rcases Nat.lt_or_ge width wordSize with hlt | hge
  · rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]
    simp [Nat.ne_of_gt hwidth0]
  · have heq : width = wordSize := by omega
    subst heq
    rw [Nat.div_self hwidth0, Nat.mod_self]
    simp

/-- At one chunk the route's shifted footprint is the singleton this block
addresses.  This is the positional fact behind the receipt equality: not
"the same set of addresses", but the same one-element list. -/
theorem footprintAt_eq_singleton {width wordSize : Nat}
    (hwidth0 : 0 < width) (hwidth : width ≤ wordSize) (base i : Nat) :
    SuccinctSpace.fixedWidthNatTableMachineFootprintAt base width wordSize i
      = [base + i] := by
  unfold SuccinctSpace.fixedWidthNatTableMachineFootprintAt
    SuccinctSpace.fixedWidthNatTableMachineFootprint
  rw [chunkCount_eq_one hwidth0 hwidth]
  simp [SuccinctSpace.consecutiveWordIndices]

/-- Collecting a one-word payload list is the identity on the option. -/
theorem collectPayloadWords_singleton (word? : Option (List Bool)) :
    SuccinctSpace.collectPayloadWords [word?] = word? := by
  cases word? with
  | none => rfl
  | some word => simp [SuccinctSpace.collectPayloadWords]

/--
THE ATOM'S ROUTE CORRESPONDENCE.

The route's adapter, run against the interior's canonical component segment,
produces a ONE-EVENT trace at `interiorReadAddr` -- the same address, in the
same position, carrying the same word -- and its value is the decoded cell.

`interiorReadNat_runsTo`'s receipt is syntactically this trace, so composing
the two gives positional receipt equality for one interior read; the interior
simulation then gets its receipt by concatenation, thirty-three times over,
with no per-site reasoning about addresses.
-/
theorem interiorReadNat_route_atom
    {entries : List Nat} {width wordSize : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth0 : 0 < width) (hwidth : width ≤ wordSize)
    (store : ReadStore) (segment base deadAddress i : Nat) :
    RMQ.SuccinctClose.flatStoreExecutionTraceResultAtSegment segment
        ((table.machineReadComputationAt wordSize base deadAddress i).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore store segment)) =
      { value :=
          (store.readWord? segment
            (interiorReadAddr base deadAddress entries.length i)).map
              SuccinctSpace.bitsToNatLE
      , trace :=
          [.readWord segment
            (interiorReadAddr base deadAddress entries.length i)
            (store.readWord? segment
              (interiorReadAddr base deadAddress entries.length i))] } := by
  unfold RMQ.SuccinctClose.flatStoreExecutionTraceResultAtSegment
    SuccinctSpace.FixedWidthNatTable.machineReadComputationAt
    interiorReadAddr
  by_cases hvalid : i < entries.length
  · rw [if_pos hvalid]
    rw [footprintAt_eq_singleton hwidth0 hwidth]
    simp [SuccinctSpace.FlatStoreComputation.readMany,
      SuccinctSpace.FlatStoreComputation.map,
      SuccinctSpace.FlatStoreComputation.bind,
      SuccinctSpace.FlatStoreExecution.append,
      SuccinctSpace.fixedWidthNatTableMachineDecode,
      collectPayloadWords_singleton,
      RMQ.SuccinctClose.flatWordStoreOfReadStore, hvalid]
  · rw [if_neg hvalid]
    simp [SuccinctSpace.FlatStoreComputation.readMany,
      SuccinctSpace.FlatStoreComputation.map,
      SuccinctSpace.FlatStoreComputation.bind,
      SuccinctSpace.FlatStoreExecution.append,
      SuccinctSpace.fixedWidthNatTableMachineDecode,
      collectPayloadWords_singleton,
      RMQ.SuccinctClose.flatWordStoreOfReadStore, hvalid]

end E1InteriorReadBlock
end WordRAM
end RMQ
