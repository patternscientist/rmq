import RMQ.Core.WordRAM.E1InteriorReadBlock

/-!
# E1 amended machine: the interior's EIGHT-CAPPED CHUNK FOLD (M3d-12)

`E1InteriorReadBlock.interiorReadNat` simulates the interior's atomic table
read in the SINGLE-CHUNK regime only, and says so: it carries `0 < width`
and `width <= wordSize` as explicit hypotheses on its bridge
(`interiorReadNat_route_atom`, `E1InteriorReadBlock.lean:443`).  Those
hypotheses are discharged for the macro-crossing branch
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`,
`InteriorDirectory.lean:4060`, from `width <= machineWordBits`) and NOT for
the within-macro branch, where the route has only
`width <= 7 * machineWordBits`
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`,
`InteriorDirectory.lean:4511`, consumed by the explicitly
`26 = 8 + 9 + 9` arithmetic at `:5196`).

AT SMALL SHAPES ONE LOGICAL INTERIOR READ EMITS UP TO EIGHT PHYSICAL READ
EVENTS.  This module is the block that covers that regime.

## This is not a return to the pre-B7 obstruction

The pre-B7 obstruction was an UNCAPPED loop: an iteration count that grew
with the shape, so no all-size literal step total existed.  `8` is a
LITERAL cap, fixed for every shape, and it is enforced BY THE MACHINE
rather than assumed of the supplied constant: `interiorChunkInit` derives
the iteration count with the truncated-subtraction cap chain
`x - (x - 8)`, which is the same chain `fringeArmInit`
(`E1FringeArmBlock.lean:118`) uses for the fringe's `33`.  A shape whose
chunk count exceeded `8` would run a SHORT fold here, not an unbounded
one; `interiorChunkCount_le_eight` then proves that no reachable shape
does, so the cap is never actually binding and the fold is exact.

## Why the fold has two loops, and why only one of them reads

The route's value is `bitsToNatLE` of the CONCATENATION of the chunks in
ascending address order (`collectPayloadWords`,
`MachineChunkedTable.lean:201`), so with every chunk `wordSize` bits wide
the value is `sum_j 2 ^ (j * wordSize) * chunk j` -- LITTLE-endian in the
chunk index.  The machine's arithmetic vocabulary has `mulConst` and
`divConst` (multiply/divide a register by a program CONSTANT) but no
register-by-register multiply (`Instr`, `E1Machine.lean:76`), so the
running `2 ^ (j * wordSize) * chunk j` term cannot be formed directly.

What CAN be formed with `mulConst` alone is the Horner step
`acc := acc * 2 ^ wordSize + chunk j`, which accumulates BIG-endian.  So
the block reads ascending -- the order the receipt must match -- into a
big-endian accumulator, then reverses the base-`2 ^ wordSize` digits with
a second capped loop.  THE SECOND LOOP PERFORMS NO READS: its receipt
contribution is `[]` at every iteration, so the block's whole receipt is
the read loop's receipt, and the digit reversal costs only `arithmetic`
and `branch` charges.  `interiorChunkFoldCats_memoryRead_count` is the
accounting statement of exactly that.

## The dead path is a one-chunk fold, not a separate shape

`FixedWidthNatTable.machineReadComputationAt`
(`MachineChunkedTableProgram.lean:343`) applies the SAME decode to both
arms of its `i < entries.length` split; the invalid arm just reads the
singleton `[deadAddress]`.  So the invalid path is the valid path at one
chunk and a different start address, and the machine realises it by
overriding `cAddr` and `cCnt` before the loop rather than by branching
around a second read block.  One loop covers both, and the receipt
equality is uniform in the validity condition.

## Register bank extension (interior chunk fold, `89 .. 99`)

The bank below `89` is fully allocated: `40 .. 62` fringe fold, `63 .. 68`
arm, `69 .. 71` same-block, `72 .. 74` dispatch, `75 .. 84` three-way
merge, `85 .. 88` the interior atom (`E1InteriorReadBlock.lean:89`).  This
block opens at `89`, so its scratch is disjoint from the merge slots the
cross-block composition requires the interior to preserve, and from the
atom's own bank -- the fold READS `iIdx` (`85`) and writes nothing below
`89`.
-/

namespace RMQ
namespace WordRAM
namespace E1InteriorChunkFold

open E1Machine
open RMQ.SuccinctSpace
open E1InteriorReadBlock (iIdx)

/-! ## Registers -/

/-- Constant `1`. -/
abbrev cOne : Nat := 89
/-- Remaining chunk counter (the read loop's descending counter). -/
abbrev cCnt : Nat := 90
/-- Running physical address. -/
abbrev cAddr : Nat := 91
/-- Big-endian chunk accumulator. -/
abbrev cAcc : Nat := 92
/-- Count of missing chunks read so far (`0` iff every chunk was present). -/
abbrev cBad : Nat := 93
/-- The chunk just read, option-shifted. -/
abbrev cW : Nat := 94
/-- Scratch. -/
abbrev cT : Nat := 95
/-- Scratch. -/
abbrev cU : Nat := 96
/-- Little-endian accumulator built by the digit-reversal loop. -/
abbrev cRev : Nat := 97
/-- Saved iteration count (the reversal loop's descending counter). -/
abbrev cN : Nat := 98
/-- Decoded cell, option-shifted (`0` = `none`, `v + 1` = `some v`). -/
abbrev cOut : Nat := 99

/-! ## Route-side shape of one chunked read

`chunkAddrs` is the route's own address list: `machineReadComputationAt`'s
`if i < entries.length` split, with the valid arm expanded through
`fixedWidthNatTableMachineFootprintAt` (`MachineChunkedTableProgram.lean:332`)
and `fixedWidthNatTableMachineFootprint` (`MachineChunkedTable.lean:196`).
`chunkStart` and `chunkIters` are what the MACHINE computes; the bridge
lemma `chunkAddrs_eq_consecutive` says they generate exactly that list.
-/

/-- The ascending physical addresses the route's adapter issues for
logical cell `i`. -/
def chunkAddrs (base deadAddress entriesLen chunkCount i : Nat) : List Nat :=
  if i < entriesLen then
    (consecutiveWordIndices (i * chunkCount) chunkCount).map (fun a => base + a)
  else
    [deadAddress]

/-- The first physical address the machine's fold reads. -/
def chunkStart (base deadAddress entriesLen chunkCount i : Nat) : Nat :=
  if i < entriesLen then base + i * chunkCount else deadAddress

/-- The number of iterations the machine's read loop performs: the
eight-capped chunk count on the valid path, one on the dead path. -/
def chunkIters (entriesLen chunkCount i : Nat) : Nat :=
  if i < entriesLen then Nat.min chunkCount 8 else 1

/-- Shifting a consecutive index block is the consecutive index block at
the shifted start. -/
theorem consecutiveWordIndices_map_add (b start count : Nat) :
    (consecutiveWordIndices start count).map (fun a => b + a) =
      consecutiveWordIndices (b + start) count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      have hshift : b + (start + 1) = b + start + 1 := by omega
      simp only [consecutiveWordIndices, List.map_cons, ih, hshift]

/--
THE MACHINE'S FOLD READS EXACTLY THE ROUTE'S ADDRESS LIST.

Both arms of the route's validity split are one consecutive index block:
the valid arm is `chunkCount` words from `base + i * chunkCount`, the dead
arm is one word at `deadAddress`.  The cap is not binding here -- it is
`chunkCount <= 8` that makes `chunkIters` equal `chunkCount` -- so the
hypothesis is exactly the route's within-macro width bound, discharged by
`interiorChunkCount_le_eight`.
-/
theorem chunkAddrs_eq_consecutive
    {base deadAddress entriesLen chunkCount i : Nat}
    (hcap : chunkCount ≤ 8) :
    chunkAddrs base deadAddress entriesLen chunkCount i =
      consecutiveWordIndices
        (chunkStart base deadAddress entriesLen chunkCount i)
        (chunkIters entriesLen chunkCount i) := by
  unfold chunkAddrs chunkStart chunkIters
  by_cases hvalid : i < entriesLen
  · rw [if_pos hvalid, if_pos hvalid, if_pos hvalid]
    rw [consecutiveWordIndices_map_add]
    have hmin : chunkCount.min 8 = chunkCount := by simp [hcap]
    rw [hmin]
  · rw [if_neg hvalid, if_neg hvalid, if_neg hvalid]
    rfl

/--
THE EIGHT-CHUNK CAP, DERIVED FROM THE ROUTE'S WITHIN-MACRO WIDTH BOUND.

`width <= 7 * wordSize` is the bound the route actually has inside a macro
(`canonicalRelativeRmmMachineReadNatCosted_cost_le_eight`,
`InteriorDirectory.lean:4511`); it yields at most `7` full chunks plus the
partial-chunk indicator, hence `8`.

`0 < wordSize` is deliberately NOT a hypothesis: it is not needed.  At
`wordSize = 0` the route's own definition gives `width / 0 = 0` and
`width % 0 = width`, so the chunk count is at most the indicator `1`.
Stating the bound without a positivity side condition keeps the cap
UNCONDITIONAL, which is what the all-size claim needs.
-/
theorem interiorChunkCount_le_eight {width wordSize : Nat}
    (hwidth : width ≤ 7 * wordSize) :
    fixedWidthNatTableMachineChunkCount width wordSize ≤ 8 := by
  unfold fixedWidthNatTableMachineChunkCount
  have hdiv : width / wordSize ≤ 7 := by
    apply Nat.div_le_of_le_mul
    omega
  cases hmod : width % wordSize with
  | zero => simp; omega
  | succ m => simp; omega

/-- A positive width reads at least one chunk.  This is the half the
route's `<= 8` cost bound does not supply, and without it a zero-width
table reads NOTHING while this block still reads once -- the same
asymmetry `E1InteriorReadBlock` records for the single-chunk atom. -/
theorem interiorChunkCount_pos {width wordSize : Nat}
    (hwidth : 0 < width) :
    0 < fixedWidthNatTableMachineChunkCount width wordSize := by
  unfold fixedWidthNatTableMachineChunkCount
  rcases Nat.eq_zero_or_pos (width % wordSize) with hm | hm
  · rcases Nat.eq_zero_or_pos (width / wordSize) with hq | hq
    · exfalso
      have hdm := Nat.div_add_mod width wordSize
      simp only [hq, hm, Nat.mul_zero, Nat.add_zero] at hdm
      omega
    · omega
  · simp [Nat.ne_of_gt hm]

/-! ## The block

Thirty-seven instructions in four segments.  Exactly ONE `readMem`, and it
is inside the read loop, so the block's memory traffic is exactly its
iteration count -- `interiorChunkFoldCats_memoryRead_count` states this and
`interiorChunkFoldCats_memoryRead_le_eight` caps it.
-/

/--
Fold init at base `Q` (seventeen instructions, exit `Q + 17`).

Computes the route's validity condition BY MACHINE COMPARISON on the
machine's own index register (`natLt` at `Q + 1`, branched at `Q + 9`),
the start address `base + i * chunkCount`, and the iteration count.

The count is `chunkCount - (chunkCount - 8)` -- the truncated-subtraction
cap chain, machine-executed.  The cap is therefore a property of the
MACHINE, not of the supplied constant: a shape presenting a chunk count
above `8` would run a short fold, never an unbounded one.
`interiorChunkCount_le_eight` separately shows no reachable shape does, so
the cap is exact rather than lossy.

The dead path overrides both the address and the count, making it a
one-chunk instance of the same fold rather than a separate code path.
-/
def interiorChunkInit
    (base deadAddress entriesLen chunkCount Q : Nat) : List Instr :=
  [ .const cT entriesLen           -- Q+0
  , .natLt cT iIdx cT              -- Q+1   cT := (i < entriesLen)
  , .mulConst cAddr iIdx chunkCount -- Q+2  cAddr := i * chunkCount
  , .const cU base                 -- Q+3
  , .add cAddr cU cAddr            -- Q+4   cAddr := base + i * chunkCount
  , .const cCnt chunkCount         -- Q+5
  , .const cU 8                    -- Q+6
  , .sub cU cCnt cU                -- Q+7   cU := chunkCount - 8
  , .sub cCnt cCnt cU              -- Q+8   cCnt := min chunkCount 8
  , .brNZ cT (Q + 12)              -- Q+9   valid: skip the dead override
  , .const cAddr deadAddress       -- Q+10
  , .const cCnt 1                  -- Q+11
  , .const cOne 1                  -- Q+12
  , .const cAcc 0                  -- Q+13
  , .const cBad 0                  -- Q+14
  , .const cRev 0                  -- Q+15
  , .move cN cCnt ]                -- Q+16  save the count for the reversal

@[simp] theorem interiorChunkInit_length
    (base deadAddress entriesLen chunkCount Q : Nat) :
    (interiorChunkInit base deadAddress entriesLen chunkCount Q).length
      = 17 := rfl

/--
The read loop body plus back edge at base `LB` (nine instructions).

One `readMem`, at the running address, then the ascending address bump,
the miss test (`cW = 0` is the option-shift's `none`), the big-endian
Horner step, and the counter decrement with the `brNZ` back edge.

The Horner step accumulates BIG-endian because `mulConst` can scale the
ACCUMULATOR but no instruction can scale the freshly read chunk by a
running power -- see the module header.  `interiorChunkCombine` puts the
digits back in the route's little-endian order.
-/
def interiorChunkReadBody (segment wordScale LB : Nat) : List Instr :=
  [ .readMem cW segment cAddr      -- LB+0  THE read
  , .add cAddr cAddr cOne          -- LB+1  ascend
  , .natLt cT cW cOne              -- LB+2  cT := (cW = 0), i.e. a miss
  , .add cBad cBad cT              -- LB+3  accumulate misses
  , .sub cW cW cOne                -- LB+4  unshift the option
  , .mulConst cAcc cAcc wordScale  -- LB+5  Horner shift
  , .add cAcc cAcc cW              -- LB+6  Horner add
  , .sub cCnt cCnt cOne            -- LB+7  decrement
  , .brNZ cCnt LB ]                -- LB+8  back edge

@[simp] theorem interiorChunkReadBody_length (segment wordScale LB : Nat) :
    (interiorChunkReadBody segment wordScale LB).length = 9 := rfl

/--
The digit-reversal loop body plus back edge at base `MB` (eight
instructions).

READ-FREE BY CONSTRUCTION: no `readMem` appears, so every iteration
contributes the empty receipt and the block's whole trace is the read
loop's trace.  It converts the big-endian accumulator to the route's
little-endian value by moving one base-`wordScale` digit per iteration,
under the same iteration count the read loop used.
-/
def interiorChunkCombine (wordScale MB : Nat) : List Instr :=
  [ .divConst cT cAcc wordScale    -- MB+0  cT := acc / scale
  , .mulConst cU cT wordScale      -- MB+1
  , .sub cU cAcc cU                -- MB+2  cU := acc % scale, the low digit
  , .mulConst cRev cRev wordScale  -- MB+3
  , .add cRev cRev cU              -- MB+4  emit the digit, reversed
  , .move cAcc cT                  -- MB+5  acc := acc / scale
  , .sub cN cN cOne                -- MB+6  decrement
  , .brNZ cN MB ]                  -- MB+7  back edge

@[simp] theorem interiorChunkCombine_length (wordScale MB : Nat) :
    (interiorChunkCombine wordScale MB).length = 8 := rfl

/--
The epilogue at base `E` (three instructions, exit `E + 3`).

Re-imposes the option shift: the cell is `some` exactly when no chunk was
missing, and `cBad` counts the missing chunks, so the `none` verdict is a
machine branch on a machine-accumulated count -- not a Lean-level `if`.
-/
def interiorChunkEpilogue (E : Nat) : List Instr :=
  [ .const cOut 0                  -- E+0   default: none
  , .brNZ cBad (E + 3)             -- E+1   some chunk missing: keep none
  , .add cOut cRev cOne ]          -- E+2   all present: some (rev)

@[simp] theorem interiorChunkEpilogue_length (E : Nat) :
    (interiorChunkEpilogue E).length = 3 := rfl

/-- The whole eight-capped chunk fold at base `Q` (thirty-seven
instructions, exit `Q + 37`). -/
def interiorChunkFold
    (segment base deadAddress entriesLen chunkCount wordScale Q : Nat) :
    List Instr :=
  interiorChunkInit base deadAddress entriesLen chunkCount Q
    ++ interiorChunkReadBody segment wordScale (Q + 17)
    ++ interiorChunkCombine wordScale (Q + 26)
    ++ interiorChunkEpilogue (Q + 34)

@[simp] theorem interiorChunkFold_length
    (segment base deadAddress entriesLen chunkCount wordScale Q : Nat) :
    (interiorChunkFold segment base deadAddress entriesLen chunkCount
      wordScale Q).length = 37 := rfl

/-! ## Category logs

Every log below is a FUNCTION of a route-side condition or of the
machine-computed iteration count.  No numeral is asserted anywhere; the
literal `8` enters only through `interiorChunkFoldCats_memoryRead_le_eight`,
as a CONSEQUENCE of the cap chain.
-/

/-- Init charges, indexed by the route's validity condition: the valid
path skips the two-instruction dead override. -/
def interiorChunkInitCats (valid : Bool) : List Category :=
  if valid then
    [.registerWrite, .comparison, .arithmetic, .registerWrite, .arithmetic,
      .registerWrite, .registerWrite, .arithmetic, .arithmetic, .branch,
      .registerWrite, .registerWrite, .registerWrite, .registerWrite,
      .registerWrite]
  else
    [.registerWrite, .comparison, .arithmetic, .registerWrite, .arithmetic,
      .registerWrite, .registerWrite, .arithmetic, .arithmetic, .branch,
      .registerWrite, .registerWrite, .registerWrite, .registerWrite,
      .registerWrite, .registerWrite, .registerWrite]

@[simp] theorem interiorChunkInitCats_valid :
    (interiorChunkInitCats true).length = 15 := rfl

@[simp] theorem interiorChunkInitCats_dead :
    (interiorChunkInitCats false).length = 17 := rfl

/-- One read-loop iteration's charges.  Identical on every iteration --
the back edge is charged whether or not it is taken -- so the loop's total
is a function of the iteration count alone. -/
def interiorChunkReadBodyCats : List Category :=
  (interiorChunkReadBody 0 0 0).map Instr.category

@[simp] theorem interiorChunkReadBodyCats_length :
    interiorChunkReadBodyCats.length = 9 := rfl

/-- One reversal iteration's charges. -/
def interiorChunkCombineCats : List Category :=
  (interiorChunkCombine 0 0).map Instr.category

@[simp] theorem interiorChunkCombineCats_length :
    interiorChunkCombineCats.length = 8 := rfl

/-- Epilogue charges, indexed by whether every chunk was present. -/
def interiorChunkEpilogueCats (allPresent : Bool) : List Category :=
  if allPresent then [.registerWrite, .branch, .arithmetic]
  else [.registerWrite, .branch]

/-- Whole-fold charges: the init's validity-indexed log, then the read
loop's per-iteration log repeated by the machine-computed count, then the
reversal loop's, then the epilogue's presence-indexed log. -/
def interiorChunkFoldCats (valid allPresent : Bool) (iters : Nat) :
    List Category :=
  interiorChunkInitCats valid
    ++ iterLog (fun _ => interiorChunkReadBodyCats) iters
    ++ iterLog (fun _ => interiorChunkCombineCats) iters
    ++ interiorChunkEpilogueCats allPresent

/-- Exactly one charged memory read per read-loop iteration. -/
theorem interiorChunkReadBodyCats_memoryRead_count :
    (interiorChunkReadBodyCats.filter (· == Category.memoryRead)).length
      = 1 := rfl

/-- The reversal loop is READ-FREE: its per-iteration log charges no
memory read at all.  This is what makes the block's whole receipt equal to
the read loop's receipt. -/
theorem interiorChunkCombineCats_memoryRead_count :
    (interiorChunkCombineCats.filter (· == Category.memoryRead)).length
      = 0 := rfl

/-- The init charges no memory read: its only memory contact is the index
register it compares. -/
theorem interiorChunkInitCats_memoryRead_count (valid : Bool) :
    ((interiorChunkInitCats valid).filter
        (· == Category.memoryRead)).length = 0 := by
  cases valid <;> rfl

/-- The epilogue charges no memory read. -/
theorem interiorChunkEpilogueCats_memoryRead_count (allPresent : Bool) :
    ((interiorChunkEpilogueCats allPresent).filter
        (· == Category.memoryRead)).length = 0 := by
  cases allPresent <;> rfl

/-- Counting memory reads through an iterated constant log. -/
theorem iterLog_const_filter_length
    (cats : List Category) (iters : Nat) :
    ((iterLog (fun _ => cats) iters).filter
        (· == Category.memoryRead)).length
      = iters * (cats.filter (· == Category.memoryRead)).length := by
  induction iters with
  | zero => simp
  | succ n ih =>
      rw [iterLog_succ, List.filter_append, List.length_append, ih,
        Nat.succ_mul]
      omega

/--
THE BLOCK'S DERIVED MEMORY-READ COUNT.

The fold charges exactly `iters` memory reads: one per read-loop
iteration, none from the init, none from the read-free reversal loop, none
from the epilogue.  DERIVED from the category algebra, not asserted.
-/
theorem interiorChunkFoldCats_memoryRead_count
    (valid allPresent : Bool) (iters : Nat) :
    ((interiorChunkFoldCats valid allPresent iters).filter
        (· == Category.memoryRead)).length
      = iters := by
  unfold interiorChunkFoldCats
  rw [List.filter_append, List.filter_append, List.filter_append,
    List.length_append, List.length_append, List.length_append,
    iterLog_const_filter_length, iterLog_const_filter_length,
    interiorChunkReadBodyCats_memoryRead_count,
    interiorChunkCombineCats_memoryRead_count,
    interiorChunkInitCats_memoryRead_count,
    interiorChunkEpilogueCats_memoryRead_count]
  omega

/--
THE LITERAL CAP, ON THE MACHINE'S OWN COUNT.

`chunkIters` is what the cap chain computes, so the fold's memory traffic
is at most `8` FOR EVERY SHAPE, with no size hypothesis.  This is the
statement that makes "every loop is a chunk fold under a literal cap" true
of the interior.
-/
theorem interiorChunkFoldCats_memoryRead_le_eight
    (valid allPresent : Bool) (entriesLen chunkCount i : Nat) :
    ((interiorChunkFoldCats valid allPresent
        (chunkIters entriesLen chunkCount i)).filter
        (· == Category.memoryRead)).length
      ≤ 8 := by
  rw [interiorChunkFoldCats_memoryRead_count]
  unfold chunkIters
  split
  · exact Nat.min_le_right _ _
  · omega

/-! ## Width certificate (REQ-E1-02 consumption for this block)

Constructor-exhaustive, per segment and then combined.  No wildcard arm:
each instruction discharges its own constructor's field conjunction from
`Instr.FieldsFit` (`E1Machine.lean:501`).

Unlike the single-chunk atom, this block DOES carry a divisor, so a
positivity arm arises and is discharged from `0 < wordScale` -- which
holds because `wordScale` is `2 ^ wordSize`.  The per-shape constants
(`base`, `deadAddress`, `entriesLen`, `chunkCount`, `wordScale`) are
hypotheses rather than assumptions about the current tables: a shape whose
component store or word scale outgrew the modeled width fails this
certificate instead of silently emitting an oversized immediate.
-/

theorem interiorChunkInit_fits
    {w base deadAddress entriesLen chunkCount Q : Nat}
    (hw : 99 < 2 ^ w) (hQ : Q + 12 < 2 ^ w)
    (hbase : base < 2 ^ w) (hdead : deadAddress < 2 ^ w)
    (hlen : entriesLen < 2 ^ w) (hcc : chunkCount < 2 ^ w) :
    ∀ instr ∈ interiorChunkInit base deadAddress entriesLen chunkCount Q,
      Instr.FieldsFit w instr := by
  intro instr hinstr
  have h85 : (85 : Nat) < 2 ^ w := by omega
  have h89 : (89 : Nat) < 2 ^ w := by omega
  have h90 : (90 : Nat) < 2 ^ w := by omega
  have h91 : (91 : Nat) < 2 ^ w := by omega
  have h92 : (92 : Nat) < 2 ^ w := by omega
  have h93 : (93 : Nat) < 2 ^ w := by omega
  have h95 : (95 : Nat) < 2 ^ w := by omega
  have h96 : (96 : Nat) < 2 ^ w := by omega
  have h97 : (97 : Nat) < 2 ^ w := by omega
  have h98 : (98 : Nat) < 2 ^ w := by omega
  have h8 : (8 : Nat) < 2 ^ w := by omega
  have h1 : (1 : Nat) < 2 ^ w := by omega
  have h0 : (0 : Nat) < 2 ^ w := by omega
  simp only [interiorChunkInit, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    | h | h | h <;> subst h
  · exact ⟨h95, hlen⟩
  · exact ⟨h95, h85, h95⟩
  · exact ⟨h91, h85, hcc⟩
  · exact ⟨h96, hbase⟩
  · exact ⟨h91, h96, h91⟩
  · exact ⟨h90, hcc⟩
  · exact ⟨h96, h8⟩
  · exact ⟨h96, h90, h96⟩
  · exact ⟨h90, h90, h96⟩
  · exact ⟨h95, hQ⟩
  · exact ⟨h91, hdead⟩
  · exact ⟨h90, h1⟩
  · exact ⟨h89, h1⟩
  · exact ⟨h92, h0⟩
  · exact ⟨h93, h0⟩
  · exact ⟨h97, h0⟩
  · exact ⟨h98, h90⟩

theorem interiorChunkReadBody_fits {w segment wordScale LB : Nat}
    (hw : 99 < 2 ^ w) (hLB : LB < 2 ^ w) (hseg : segment < 2 ^ w)
    (hscale : wordScale < 2 ^ w) :
    ∀ instr ∈ interiorChunkReadBody segment wordScale LB,
      Instr.FieldsFit w instr := by
  intro instr hinstr
  have h89 : (89 : Nat) < 2 ^ w := by omega
  have h90 : (90 : Nat) < 2 ^ w := by omega
  have h91 : (91 : Nat) < 2 ^ w := by omega
  have h92 : (92 : Nat) < 2 ^ w := by omega
  have h93 : (93 : Nat) < 2 ^ w := by omega
  have h94 : (94 : Nat) < 2 ^ w := by omega
  have h95 : (95 : Nat) < 2 ^ w := by omega
  simp only [interiorChunkReadBody, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨h94, hseg, h91⟩
  · exact ⟨h91, h91, h89⟩
  · exact ⟨h95, h94, h89⟩
  · exact ⟨h93, h93, h95⟩
  · exact ⟨h94, h94, h89⟩
  · exact ⟨h92, h92, hscale⟩
  · exact ⟨h92, h92, h94⟩
  · exact ⟨h90, h90, h89⟩
  · exact ⟨h90, hLB⟩

theorem interiorChunkCombine_fits {w wordScale MB : Nat}
    (hw : 99 < 2 ^ w) (hMB : MB < 2 ^ w)
    (hscale0 : 0 < wordScale) (hscale : wordScale < 2 ^ w) :
    ∀ instr ∈ interiorChunkCombine wordScale MB,
      Instr.FieldsFit w instr := by
  intro instr hinstr
  have h89 : (89 : Nat) < 2 ^ w := by omega
  have h92 : (92 : Nat) < 2 ^ w := by omega
  have h95 : (95 : Nat) < 2 ^ w := by omega
  have h96 : (96 : Nat) < 2 ^ w := by omega
  have h97 : (97 : Nat) < 2 ^ w := by omega
  have h98 : (98 : Nat) < 2 ^ w := by omega
  simp only [interiorChunkCombine, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨h95, h92, hscale0, hscale⟩
  · exact ⟨h96, h95, hscale⟩
  · exact ⟨h96, h92, h96⟩
  · exact ⟨h97, h97, hscale⟩
  · exact ⟨h97, h97, h96⟩
  · exact ⟨h92, h95⟩
  · exact ⟨h98, h98, h89⟩
  · exact ⟨h98, hMB⟩

theorem interiorChunkEpilogue_fits {w E : Nat}
    (hw : 99 < 2 ^ w) (hE : E + 3 < 2 ^ w) :
    ∀ instr ∈ interiorChunkEpilogue E, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h89 : (89 : Nat) < 2 ^ w := by omega
  have h93 : (93 : Nat) < 2 ^ w := by omega
  have h97 : (97 : Nat) < 2 ^ w := by omega
  have h99 : (99 : Nat) < 2 ^ w := hw
  have h0 : (0 : Nat) < 2 ^ w := by omega
  simp only [interiorChunkEpilogue, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with h | h | h <;> subst h
  · exact ⟨h99, h0⟩
  · exact ⟨h93, hE⟩
  · exact ⟨h99, h97, h89⟩

/-- Constructor-exhaustive width certificate for the whole fold. -/
theorem interiorChunkFold_fits
    {w segment base deadAddress entriesLen chunkCount wordScale Q : Nat}
    (hw : 99 < 2 ^ w) (hQ : Q + 37 < 2 ^ w) (hseg : segment < 2 ^ w)
    (hbase : base < 2 ^ w) (hdead : deadAddress < 2 ^ w)
    (hlen : entriesLen < 2 ^ w) (hcc : chunkCount < 2 ^ w)
    (hscale0 : 0 < wordScale) (hscale : wordScale < 2 ^ w) :
    ∀ instr ∈ interiorChunkFold segment base deadAddress entriesLen
        chunkCount wordScale Q,
      Instr.FieldsFit w instr := by
  intro instr hinstr
  rw [interiorChunkFold, List.mem_append, List.mem_append,
    List.mem_append] at hinstr
  rcases hinstr with ((hi | hi) | hi) | hi
  · exact interiorChunkInit_fits hw (by omega) hbase hdead hlen hcc instr hi
  · exact interiorChunkReadBody_fits hw (by omega) hseg hscale instr hi
  · exact interiorChunkCombine_fits hw (by omega) hscale0 hscale instr hi
  · exact interiorChunkEpilogue_fits hw (by omega) instr hi

end E1InteriorChunkFold
end WordRAM
end RMQ
