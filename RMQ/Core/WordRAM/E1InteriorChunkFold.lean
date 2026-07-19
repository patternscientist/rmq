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
def interiorChunkInitHead
    (base entriesLen chunkCount : Nat) : List Instr :=
  [ .const cT entriesLen            -- Q+0
  , .natLt cT iIdx cT               -- Q+1   cT := (i < entriesLen)
  , .mulConst cAddr iIdx chunkCount -- Q+2   cAddr := i * chunkCount
  , .const cU base                  -- Q+3
  , .add cAddr cU cAddr             -- Q+4   cAddr := base + i * chunkCount
  , .const cCnt chunkCount          -- Q+5
  , .const cU 8                     -- Q+6
  , .sub cU cCnt cU                 -- Q+7   cU := chunkCount - 8
  , .sub cCnt cCnt cU ]             -- Q+8   cCnt := min chunkCount 8

/-- The dead-address override: taken only when the route's validity test
fails, making the dead path a ONE-CHUNK instance of the same fold. -/
def interiorChunkInitDead (deadAddress : Nat) : List Instr :=
  [ .const cAddr deadAddress        -- Q+10
  , .const cCnt 1 ]                 -- Q+11

/-- The fold's zeroing tail, common to both paths. -/
def interiorChunkInitTail : List Instr :=
  [ .const cOne 1                   -- Q+12
  , .const cAcc 0                   -- Q+13
  , .const cBad 0                   -- Q+14
  , .const cRev 0                   -- Q+15
  , .move cN cCnt ]                 -- Q+16  save the count for the reversal

def interiorChunkInit
    (base deadAddress entriesLen chunkCount Q : Nat) : List Instr :=
  interiorChunkInitHead base entriesLen chunkCount
    ++ [.brNZ cT (Q + 12)]          -- Q+9   valid: skip the dead override
    ++ interiorChunkInitDead deadAddress
    ++ interiorChunkInitTail

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
  (interiorChunkInitHead 0 0 0).map Instr.category
    ++ [Category.branch]
    ++ (if valid then [] else (interiorChunkInitDead 0).map Instr.category)
    ++ interiorChunkInitTail.map Instr.category

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
  simp only [interiorChunkInit, interiorChunkInitHead,
    interiorChunkInitDead, interiorChunkInitTail, List.append_assoc,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
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

/-! ## Spec side of the fold

The three functions below describe what the read loop is accumulating, as
functions of the store and the ascending chunk index -- never numerals.
`chunkAcc` is BIG-endian by construction (see DD-20260719-004); the
reversal loop is what restores the route's little-endian value.
-/

/-- The ascending trace the fold must emit: one `readWord` per chunk, at
the route's addresses, in the route's order. -/
def chunkEventsAt (store : ReadStore) (segment start n : Nat) :
    List TraceEvent :=
  (consecutiveWordIndices start n).map
    (fun a => TraceEvent.readWord segment a (store.readWord? segment a))

/-- The big-endian accumulator after `j` chunks, in the option-shift
convention: a missing chunk contributes the truncated `0 - 1 = 0` and is
recorded separately by `chunkBad`, so the accumulator is never consulted
when a chunk was missing. -/
def chunkAcc (store : ReadStore) (segment scale start : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      chunkAcc store segment scale start j * scale
        + (decodeRead (store.readWord? segment (start + j)) - 1)

/-- The number of missing chunks among the first `j`.  `0` exactly when
every chunk was present, which is the route's `some`/`none` verdict. -/
def chunkBad (store : ReadStore) (segment start : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 =>
      chunkBad store segment start j
        + (if decodeRead (store.readWord? segment (start + j)) = 0 then 1
           else 0)

/-- Registers the read-loop body writes. -/
abbrev ChunkReadBodyUntouched (r : Nat) : Prop :=
  r ≠ cW ∧ r ≠ cAddr ∧ r ≠ cT ∧ r ≠ cBad ∧ r ≠ cAcc ∧ r ≠ cCnt

/-- Local congruence for iterated logs (a copy of the combinator used by
the rank and fringe bridges, kept module-local to avoid depending on their
import order). -/
theorem iterLog_congr_local {α : Type} {f g : Nat → List α} :
    ∀ (n : Nat), (∀ k, k < n → f k = g k) → iterLog f n = iterLog g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      show f n ++ iterLog f n = g n ++ iterLog g n
      rw [h n (by omega), ih (fun k hk => h k (by omega))]

/-! ## One read-loop iteration

The eight intermediate register files are named rather than written as
nested `write` towers, so that each simulation step states the value it
writes in already-normalised form.  They are definitions, not tactic-local
abbreviations, because this development is Mathlib-free and `set` is not
available.
-/

/-- After `LB+0`: the chunk lands in `cW`, option-shifted. -/
def rbR1 (regs : RegFile) (dw : Nat) : RegFile := regs.write cW dw

/-- After `LB+1`: the address ascends. -/
def rbR2 (regs : RegFile) (dw addr : Nat) : RegFile :=
  (rbR1 regs dw).write cAddr (addr + 1)

/-- After `LB+2`: the miss verdict, `cW = 0` in the option shift. -/
def rbR3 (regs : RegFile) (dw addr : Nat) : RegFile :=
  (rbR2 regs dw addr).write cT (if dw < 1 then 1 else 0)

/-- After `LB+3`: the miss counter accumulates. -/
def rbR4 (regs : RegFile) (dw addr bad : Nat) : RegFile :=
  (rbR3 regs dw addr).write cBad (bad + (if dw < 1 then 1 else 0))

/-- After `LB+4`: the option shift is removed. -/
def rbR5 (regs : RegFile) (dw addr bad : Nat) : RegFile :=
  (rbR4 regs dw addr bad).write cW (dw - 1)

/-- After `LB+5`: the Horner shift. -/
def rbR6 (regs : RegFile) (dw addr bad acc wordScale : Nat) : RegFile :=
  (rbR5 regs dw addr bad).write cAcc (acc * wordScale)

/-- After `LB+6`: the Horner add. -/
def rbR7 (regs : RegFile) (dw addr bad acc wordScale : Nat) : RegFile :=
  (rbR6 regs dw addr bad acc wordScale).write cAcc
    (acc * wordScale + (dw - 1))

/-- After `LB+7`: the counter decrements. -/
def rbR8 (regs : RegFile) (dw addr bad acc wordScale cnt : Nat) : RegFile :=
  (rbR7 regs dw addr bad acc wordScale).write cCnt cnt

/-- Every unfolding needed to evaluate the iteration's register tower. -/
theorem rbR8_apply
    (regs : RegFile) (dw addr bad acc wordScale cnt r : Nat) :
    rbR8 regs dw addr bad acc wordScale cnt r =
      if r = cCnt then cnt
      else if r = cAcc then acc * wordScale + (dw - 1)
      else if r = cW then dw - 1
      else if r = cBad then bad + (if dw < 1 then 1 else 0)
      else if r = cT then (if dw < 1 then 1 else 0)
      else if r = cAddr then addr + 1
      else regs r := by
  unfold rbR8 rbR7 rbR6 rbR5 rbR4 rbR3 rbR2 rbR1 RegFile.write
  simp only [cCnt, cAcc, cW, cBad, cT, cAddr]
  by_cases h1 : r = 90
  · simp [h1]
  · by_cases h2 : r = 92
    · simp [h2]
    · by_cases h3 : r = 94
      · simp [h3]
      · by_cases h4 : r = 93
        · simp [h4]
        · by_cases h5 : r = 95
          · simp [h5]
          · by_cases h6 : r = 91
            · simp [h6]
            · simp [h1, h2, h3, h4, h5, h6]

/-! ## One read-loop iteration -/

/--
ONE ITERATION OF THE READ LOOP.

Exactly one `readWord`, at the running address; the address ascends by
one; the miss counter takes the option-shift's `cW = 0` verdict; the
accumulator takes one Horner step; the counter decrements; and the back
edge is taken exactly when iterations remain.

`cN` is stated preserved explicitly because it lives INSIDE the fold's own
bank (`98`), so the outside-the-bank preservation clause does not cover
it, and the reversal loop depends on it surviving the read loop intact.
-/
theorem interiorChunkReadBody_step
    (store : ReadStore) {program : E1Machine.Program}
    {segment wordScale LB : Nat}
    (hHost : HostedAt program LB (interiorChunkReadBody segment wordScale LB))
    (regs : RegFile) (addr cnt acc bad : Nat)
    (hOne : regs cOne = 1) (hAddr : regs cAddr = addr)
    (hCnt : regs cCnt = cnt + 1) (hAcc : regs cAcc = acc)
    (hBad : regs cBad = bad) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, LB, false⟩
          ⟨regs', if cnt = 0 then LB + 9 else LB, false⟩
          [.readWord segment addr (store.readWord? segment addr)]
          interiorChunkReadBodyCats ∧
        regs' cOne = 1 ∧
        regs' cAddr = addr + 1 ∧
        regs' cCnt = cnt ∧
        regs' cAcc =
          acc * wordScale
            + (decodeRead (store.readWord? segment addr) - 1) ∧
        regs' cBad =
          bad
            + (if decodeRead (store.readWord? segment addr) = 0 then 1
               else 0) ∧
        regs' cN = regs cN ∧
        (∀ r, ChunkReadBodyUntouched r → regs' r = regs r) := by
  have hf : ∀ (k m : Nat) (instr : Instr), k < 9 →
      (interiorChunkReadBody segment wordScale LB)[k]? = some instr →
      LB + k = m → program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[LB]? = some (.readMem cW segment cAddr) :=
    hf 0 LB _ (by omega) rfl (by omega)
  have h1 : program[LB + 1]? = some (.add cAddr cAddr cOne) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[LB + 2]? = some (.natLt cT cW cOne) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[LB + 3]? = some (.add cBad cBad cT) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[LB + 4]? = some (.sub cW cW cOne) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[LB + 5]? = some (.mulConst cAcc cAcc wordScale) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[LB + 6]? = some (.add cAcc cAcc cW) :=
    hf 6 _ _ (by omega) rfl (by omega)
  have h7 : program[LB + 7]? = some (.sub cCnt cCnt cOne) :=
    hf 7 _ _ (by omega) rfl (by omega)
  have h8 : program[LB + 8]? = some (.brNZ cCnt LB) :=
    hf 8 _ _ (by omega) rfl (by omega)
  have s0 : RunsTo store program ⟨regs, LB, false⟩
      ⟨rbR1 regs (decodeRead (store.readWord? segment addr)), LB + 1,
        false⟩
      [.readWord segment addr (store.readWord? segment addr)]
      [Category.memoryRead] := by
    have h := RunsTo.readMem (store := store)
      (s := (⟨regs, LB, false⟩ : State)) rfl h0
    simpa [rbR1, hAddr] using h
  have s1 : RunsTo store program
      ⟨rbR1 regs (decodeRead (store.readWord? segment addr)), LB + 1,
        false⟩
      ⟨rbR2 regs (decodeRead (store.readWord? segment addr)) addr, LB + 2,
        false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.add (store := store)
      (s := (⟨rbR1 regs (decodeRead (store.readWord? segment addr)),
        LB + 1, false⟩ : State)) rfl h1
    simpa [rbR2, rbR1, RegFile.write, cAddr, cW, cOne, hAddr, hOne] using h
  have s2 : RunsTo store program
      ⟨rbR2 regs (decodeRead (store.readWord? segment addr)) addr, LB + 2,
        false⟩
      ⟨rbR3 regs (decodeRead (store.readWord? segment addr)) addr, LB + 3,
        false⟩ [] [Category.comparison] := by
    have h := RunsTo.natLt (store := store)
      (s := (⟨rbR2 regs (decodeRead (store.readWord? segment addr)) addr,
        LB + 2, false⟩ : State)) rfl h2
    simpa [rbR3, rbR2, rbR1, RegFile.write, cAddr, cW, cOne, hOne] using h
  have s3 : RunsTo store program
      ⟨rbR3 regs (decodeRead (store.readWord? segment addr)) addr, LB + 3,
        false⟩
      ⟨rbR4 regs (decodeRead (store.readWord? segment addr)) addr bad,
        LB + 4, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.add (store := store)
      (s := (⟨rbR3 regs (decodeRead (store.readWord? segment addr)) addr,
        LB + 3, false⟩ : State)) rfl h3
    simpa [rbR4, rbR3, rbR2, rbR1, RegFile.write, cAddr, cW, cT, cBad,
      hBad] using h
  have s4 : RunsTo store program
      ⟨rbR4 regs (decodeRead (store.readWord? segment addr)) addr bad,
        LB + 4, false⟩
      ⟨rbR5 regs (decodeRead (store.readWord? segment addr)) addr bad,
        LB + 5, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨rbR4 regs (decodeRead (store.readWord? segment addr)) addr
        bad, LB + 4, false⟩ : State)) rfl h4
    simpa [rbR5, rbR4, rbR3, rbR2, rbR1, RegFile.write, cAddr, cW, cT,
      cBad, cOne, hOne] using h
  have s5 : RunsTo store program
      ⟨rbR5 regs (decodeRead (store.readWord? segment addr)) addr bad,
        LB + 5, false⟩
      ⟨rbR6 regs (decodeRead (store.readWord? segment addr)) addr bad acc
        wordScale, LB + 6, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.mulConst (store := store)
      (s := (⟨rbR5 regs (decodeRead (store.readWord? segment addr)) addr
        bad, LB + 5, false⟩ : State)) rfl h5
    simpa [rbR6, rbR5, rbR4, rbR3, rbR2, rbR1, RegFile.write, cAddr, cW,
      cT, cBad, cAcc, hAcc] using h
  have s6 : RunsTo store program
      ⟨rbR6 regs (decodeRead (store.readWord? segment addr)) addr bad acc
        wordScale, LB + 6, false⟩
      ⟨rbR7 regs (decodeRead (store.readWord? segment addr)) addr bad acc
        wordScale, LB + 7, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.add (store := store)
      (s := (⟨rbR6 regs (decodeRead (store.readWord? segment addr)) addr
        bad acc wordScale, LB + 6, false⟩ : State)) rfl h6
    simpa [rbR7, rbR6, rbR5, rbR4, rbR3, rbR2, rbR1, RegFile.write, cAcc,
      cW] using h
  have s7 : RunsTo store program
      ⟨rbR7 regs (decodeRead (store.readWord? segment addr)) addr bad acc
        wordScale, LB + 7, false⟩
      ⟨rbR8 regs (decodeRead (store.readWord? segment addr)) addr bad acc
        wordScale cnt, LB + 8, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨rbR7 regs (decodeRead (store.readWord? segment addr)) addr
        bad acc wordScale, LB + 7, false⟩ : State)) rfl h7
    simpa [rbR8, rbR7, rbR6, rbR5, rbR4, rbR3, rbR2, rbR1, RegFile.write,
      cCnt, cAcc, cW, cAddr, cT, cBad, cOne, hCnt, hOne] using h
  have s8 : RunsTo store program
      ⟨rbR8 regs (decodeRead (store.readWord? segment addr)) addr bad acc
        wordScale cnt, LB + 8, false⟩
      ⟨rbR8 regs (decodeRead (store.readWord? segment addr)) addr bad acc
        wordScale cnt, if cnt = 0 then LB + 9 else LB, false⟩ []
      [Category.branch] := by
    have h := RunsTo.brNZ (store := store)
      (s := (⟨rbR8 regs (decodeRead (store.readWord? segment addr)) addr
        bad acc wordScale cnt, LB + 8, false⟩ : State)) rfl h8
    have hcnt8 :
        rbR8 regs (decodeRead (store.readWord? segment addr)) addr bad acc
          wordScale cnt cCnt = cnt := by
      rw [rbR8_apply]; simp
    simpa [hcnt8] using h
  refine ⟨rbR8 regs (decodeRead (store.readWord? segment addr)) addr bad
    acc wordScale cnt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hrun :=
      ((((s0.trans s1).trans (s2.trans s3)).trans
        ((s4.trans s5).trans (s6.trans s7))).trans s8)
    simpa [interiorChunkReadBodyCats, interiorChunkReadBody] using hrun
  · rw [rbR8_apply]; simp [cOne, cCnt, cAcc, cW, cBad, cT, cAddr, hOne]
  · rw [rbR8_apply]; simp [cAddr, cCnt, cAcc, cW, cBad, cT]
  · rw [rbR8_apply]; simp
  · rw [rbR8_apply]; simp [cAcc, cCnt]
  · rw [rbR8_apply]; simp [cBad, cCnt, cAcc, cW]
  · rw [rbR8_apply]; simp [cN, cCnt, cAcc, cW, cBad, cT, cAddr]
  · intro r hr
    obtain ⟨hW, hAd, hT, hB, hAc, hC⟩ := hr
    rw [rbR8_apply]
    simp [hW, hAd, hT, hB, hAc, hC]

/-! ## The read loop -/

/-- Registers outside the interior chunk-fold bank. -/
abbrev ChunkFoldUntouched (r : Nat) : Prop := r < 89 ∨ 99 < r

/-- A register outside the bank is outside the read body's write set. -/
theorem chunkReadBodyUntouched_of_fold {r : Nat}
    (h : ChunkFoldUntouched r) : ChunkReadBodyUntouched r := by
  simp only [ChunkFoldUntouched] at h
  simp only [ChunkReadBodyUntouched, cW, cAddr, cT, cBad, cAcc, cCnt]
  omega

/--
The descending loop counter reads ASCENDING addresses: the iteration
executed with remaining counter `k + 1` reads position `n - (k + 1)`, so
concatenating the per-iteration receipts in execution order yields exactly
the route's ascending address list.  This is the positional statement that
makes the receipt equality survive loop composition.
-/
theorem iterLog_chunkReads_eq (store : ReadStore) (segment : Nat) :
    ∀ (n start : Nat),
      iterLog (fun k =>
        [TraceEvent.readWord segment (start + (n - (k + 1)))
          (store.readWord? segment (start + (n - (k + 1))))]) n
        = chunkEventsAt store segment start n := by
  intro n
  induction n with
  | zero => intro start; rfl
  | succ n ih =>
      intro start
      have hhead : start + (n + 1 - (n + 1)) = start := by omega
      have hcongr :
          iterLog (fun k =>
            [TraceEvent.readWord segment (start + (n + 1 - (k + 1)))
              (store.readWord? segment (start + (n + 1 - (k + 1))))]) n
            = iterLog (fun k =>
              [TraceEvent.readWord segment (start + 1 + (n - (k + 1)))
                (store.readWord? segment
                  (start + 1 + (n - (k + 1))))]) n := by
        apply iterLog_congr_local
        intro k hk
        have harg : start + (n + 1 - (k + 1)) = start + 1 + (n - (k + 1)) := by
          omega
        rw [harg]
      show [TraceEvent.readWord segment (start + (n + 1 - (n + 1)))
          (store.readWord? segment (start + (n + 1 - (n + 1))))]
          ++ iterLog _ n = _
      rw [hhead, hcongr, ih (start + 1)]
      rfl

/--
EXACT SIMULATION OF THE INTERIOR'S CHUNK READ LOOP.

From the loop entry with the pinned constants, the start address, the
machine-computed iteration count, a zeroed accumulator and a zeroed miss
counter, the hosted body plus back edge run to the loop exit at `LB + 9`,
emitting exactly the route's ascending chunk reads -- POSITIONALLY equal
to `chunkEventsAt` -- charging one per-iteration log per chunk, and
leaving the big-endian accumulation in `cAcc` with the missing-chunk count
in `cBad`.

`0 < n` is required and is not decoration: the back edge makes this a
do-while, so at `n = 0` the machine would still read once while the route
reads nothing.  That is the same off-by-one `E1InteriorReadBlock` records
for the single-chunk atom, surfacing here as an explicit hypothesis rather
than as a silent assumption about the shape.
-/
theorem interiorChunkReadLoop_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {segment wordScale LB : Nat}
    (hHost : HostedAt program LB
      (interiorChunkReadBody segment wordScale LB))
    (regsL : RegFile) (start n : Nat) (hn : 0 < n)
    (hOne : regsL cOne = 1) (hAddr : regsL cAddr = start)
    (hCnt : regsL cCnt = n) (hAcc : regsL cAcc = 0)
    (hBad : regsL cBad = 0) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regsL, LB, false⟩ ⟨regsF, LB + 9, false⟩
          (chunkEventsAt store segment start n)
          (iterLog (fun _ => interiorChunkReadBodyCats) n) ∧
        regsF cOne = 1 ∧
        regsF cCnt = 0 ∧
        regsF cAcc = chunkAcc store segment wordScale start n ∧
        regsF cBad = chunkBad store segment start n ∧
        regsF cN = regsL cN ∧
        regsF cRev = regsL cRev ∧
        (∀ r, ChunkFoldUntouched r → regsF r = regsL r) := by
  let P : Nat → State → Prop := fun k s =>
    k ≤ n ∧ s.halted = false ∧
    s.pc = (if k = 0 then LB + 9 else LB) ∧
    s.regs cOne = 1 ∧
    s.regs cAddr = start + (n - k) ∧
    s.regs cCnt = k ∧
    s.regs cAcc = chunkAcc store segment wordScale start (n - k) ∧
    s.regs cBad = chunkBad store segment start (n - k) ∧
    s.regs cN = regsL cN ∧
    s.regs cRev = regsL cRev ∧
    (∀ r, ChunkFoldUntouched r → s.regs r = regsL r)
  have hstep : ∀ k s, P (k + 1) s →
      ∃ s', RunsTo store program s s'
          [TraceEvent.readWord segment (start + (n - (k + 1)))
            (store.readWord? segment (start + (n - (k + 1))))]
          interiorChunkReadBodyCats ∧ P k s' := by
    intro k s hP
    obtain ⟨regs, pc, halted⟩ := s
    obtain ⟨hkle, hhalt, hpc, hone, haddr, hcnt, hacc, hbad, hcn, hcrev,
      hpres⟩ := hP
    simp only at hhalt hpc hone haddr hcnt hacc hbad hcn hcrev hpres
    subst hhalt
    rw [if_neg (Nat.succ_ne_zero k)] at hpc
    subst pc
    have hik : n - k = (n - (k + 1)) + 1 := by omega
    obtain ⟨regs', hrun, hone', haddr', hcnt', hacc', hbad', hcn', hpres'⟩ :=
      interiorChunkReadBody_step store hHost regs
        (start + (n - (k + 1))) k
        (chunkAcc store segment wordScale start (n - (k + 1)))
        (chunkBad store segment start (n - (k + 1)))
        hone haddr hcnt hacc hbad
    refine ⟨⟨regs', if k = 0 then LB + 9 else LB, false⟩, hrun, ?_⟩
    refine ⟨by omega, rfl, rfl, hone', ?_, hcnt', ?_, ?_, ?_, ?_, ?_⟩
    · show regs' cAddr = start + (n - k)
      rw [haddr', hik]
      omega
    · show regs' cAcc = chunkAcc store segment wordScale start (n - k)
      rw [hacc', hik]
      rfl
    · show regs' cBad = chunkBad store segment start (n - k)
      rw [hbad', hik]
      rfl
    · show regs' cN = regsL cN
      rw [hcn', hcn]
    · show regs' cRev = regsL cRev
      have hrev : ChunkReadBodyUntouched cRev := by decide
      rw [hpres' cRev hrev, hcrev]
    · intro r hr
      show regs' r = regsL r
      rw [hpres' r (chunkReadBodyUntouched_of_fold hr), hpres r hr]
  have hP0 : P n ⟨regsL, LB, false⟩ := by
    refine ⟨Nat.le_refl n, rfl, ?_, hOne, ?_, hCnt, ?_, ?_, rfl, rfl,
      fun r _ => rfl⟩
    · show LB = if n = 0 then LB + 9 else LB
      rw [if_neg (by omega)]
    · show regsL cAddr = start + (n - n)
      rw [hAddr]; omega
    · show regsL cAcc = chunkAcc store segment wordScale start (n - n)
      rw [hAcc, Nat.sub_self]; rfl
    · show regsL cBad = chunkBad store segment start (n - n)
      rw [hBad, Nat.sub_self]; rfl
  obtain ⟨sF, hrunF, hPF⟩ :=
    RunsTo.iterate (store := store) (program := program) P
      (fun k =>
        [TraceEvent.readWord segment (start + (n - (k + 1)))
          (store.readWord? segment (start + (n - (k + 1))))])
      (fun _ => interiorChunkReadBodyCats) hstep n ⟨regsL, LB, false⟩ hP0
  obtain ⟨regsF, pcF, haltedF⟩ := sF
  obtain ⟨_, hhaltF, hpcF, honeF, _, hcntF, haccF, hbadF, hcnF, hcrevF,
    hpresF⟩ := hPF
  simp only at hhaltF hpcF honeF hcntF haccF hbadF hcnF hcrevF hpresF
  subst hhaltF
  subst pcF
  refine ⟨regsF, ?_, honeF, hcntF, ?_, ?_, hcnF, hcrevF, hpresF⟩
  · rwa [iterLog_chunkReads_eq store segment n start] at hrunF
  · rw [haccF, Nat.sub_zero]
  · rw [hbadF, Nat.sub_zero]

/-! ## The digit-reversal loop

Read-free.  Its whole contribution to the receipt is `[]` at every
iteration, so the fold's trace is the read loop's trace; what it costs is
`arithmetic` and `branch` charges under the same literal cap.
-/

/-- The reversal state after `j` steps: one base-`scale` digit moves from
the big-endian accumulator to the little-endian result per step. -/
def chunkRevAt (scale acc0 : Nat) : Nat → Nat × Nat
  | 0 => (acc0, 0)
  | j + 1 =>
      ((chunkRevAt scale acc0 j).1 / scale,
        (chunkRevAt scale acc0 j).2 * scale
          + (chunkRevAt scale acc0 j).1 % scale)

/-- `a - a / k * k` is `a % k`; the machine forms the remainder this way
because it has no modulus instruction. -/
theorem sub_div_mul_eq_mod (a k : Nat) : a - a / k * k = a % k := by
  have h := Nat.div_add_mod a k
  have hcomm : a / k * k = k * (a / k) := Nat.mul_comm _ _
  omega

/-- An iterated empty receipt is empty. -/
theorem iterLog_nil_reads (n : Nat) :
    iterLog (fun _ => ([] : List TraceEvent)) n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterLog_succ, ih]; rfl

/-- After `MB+0`: the quotient. -/
def rvR1 (regs : RegFile) (acc scale : Nat) : RegFile :=
  regs.write cT (acc / scale)

/-- After `MB+1`: the quotient scaled back up. -/
def rvR2 (regs : RegFile) (acc scale : Nat) : RegFile :=
  (rvR1 regs acc scale).write cU (acc / scale * scale)

/-- After `MB+2`: the low digit, formed as a difference. -/
def rvR3 (regs : RegFile) (acc scale : Nat) : RegFile :=
  (rvR2 regs acc scale).write cU (acc % scale)

/-- After `MB+3`: the result shifts up. -/
def rvR4 (regs : RegFile) (acc scale rev : Nat) : RegFile :=
  (rvR3 regs acc scale).write cRev (rev * scale)

/-- After `MB+4`: the digit is emitted, reversed. -/
def rvR5 (regs : RegFile) (acc scale rev : Nat) : RegFile :=
  (rvR4 regs acc scale rev).write cRev (rev * scale + acc % scale)

/-- After `MB+5`: the accumulator drops its low digit. -/
def rvR6 (regs : RegFile) (acc scale rev : Nat) : RegFile :=
  (rvR5 regs acc scale rev).write cAcc (acc / scale)

/-- After `MB+6`: the counter decrements. -/
def rvR7 (regs : RegFile) (acc scale rev cnt : Nat) : RegFile :=
  (rvR6 regs acc scale rev).write cN cnt

theorem rvR7_apply (regs : RegFile) (acc scale rev cnt r : Nat) :
    rvR7 regs acc scale rev cnt r =
      if r = cN then cnt
      else if r = cAcc then acc / scale
      else if r = cRev then rev * scale + acc % scale
      else if r = cU then acc % scale
      else if r = cT then acc / scale
      else regs r := by
  unfold rvR7 rvR6 rvR5 rvR4 rvR3 rvR2 rvR1 RegFile.write
  simp only [cN, cAcc, cRev, cU, cT]
  by_cases h1 : r = 98
  · simp [h1]
  · by_cases h2 : r = 92
    · simp [h2]
    · by_cases h3 : r = 97
      · simp [h3]
      · by_cases h4 : r = 96
        · simp [h4]
        · by_cases h5 : r = 95
          · simp [h5]
          · simp [h1, h2, h3, h4, h5]

/-- Registers the reversal body writes. -/
abbrev ChunkCombineUntouched (r : Nat) : Prop :=
  r ≠ cT ∧ r ≠ cU ∧ r ≠ cRev ∧ r ≠ cAcc ∧ r ≠ cN

/-- A register outside the bank is outside the reversal body's write
set. -/
theorem chunkCombineUntouched_of_fold {r : Nat}
    (h : ChunkFoldUntouched r) : ChunkCombineUntouched r := by
  simp only [ChunkFoldUntouched] at h
  simp only [ChunkCombineUntouched, cT, cU, cRev, cAcc, cN]
  omega

/--
ONE ITERATION OF THE REVERSAL LOOP.

No `readWord`: the receipt is empty.  One base-`scale` digit moves from
`cAcc` to `cRev`, the counter decrements, and the back edge is taken
exactly when iterations remain.

`cBad` is stated preserved because the epilogue's `some`/`none` verdict
reads it after this loop has run.
-/
theorem interiorChunkCombine_step
    (store : ReadStore) {program : E1Machine.Program} {wordScale MB : Nat}
    (hHost : HostedAt program MB (interiorChunkCombine wordScale MB))
    (regs : RegFile) (acc rev cnt : Nat)
    (hOne : regs cOne = 1) (hAcc : regs cAcc = acc)
    (hRev : regs cRev = rev) (hN : regs cN = cnt + 1) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, MB, false⟩
          ⟨regs', if cnt = 0 then MB + 8 else MB, false⟩ []
          interiorChunkCombineCats ∧
        regs' cOne = 1 ∧
        regs' cAcc = acc / wordScale ∧
        regs' cRev = rev * wordScale + acc % wordScale ∧
        regs' cN = cnt ∧
        regs' cBad = regs cBad ∧
        (∀ r, ChunkCombineUntouched r → regs' r = regs r) := by
  have hf : ∀ (k m : Nat) (instr : Instr), k < 8 →
      (interiorChunkCombine wordScale MB)[k]? = some instr →
      MB + k = m → program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[MB]? = some (.divConst cT cAcc wordScale) :=
    hf 0 MB _ (by omega) rfl (by omega)
  have h1 : program[MB + 1]? = some (.mulConst cU cT wordScale) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[MB + 2]? = some (.sub cU cAcc cU) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[MB + 3]? = some (.mulConst cRev cRev wordScale) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[MB + 4]? = some (.add cRev cRev cU) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[MB + 5]? = some (.move cAcc cT) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[MB + 6]? = some (.sub cN cN cOne) :=
    hf 6 _ _ (by omega) rfl (by omega)
  have h7 : program[MB + 7]? = some (.brNZ cN MB) :=
    hf 7 _ _ (by omega) rfl (by omega)
  have s0 : RunsTo store program ⟨regs, MB, false⟩
      ⟨rvR1 regs acc wordScale, MB + 1, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.divConst (store := store)
      (s := (⟨regs, MB, false⟩ : State)) rfl h0
    simpa [rvR1, hAcc] using h
  have s1 : RunsTo store program ⟨rvR1 regs acc wordScale, MB + 1, false⟩
      ⟨rvR2 regs acc wordScale, MB + 2, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.mulConst (store := store)
      (s := (⟨rvR1 regs acc wordScale, MB + 1, false⟩ : State)) rfl h1
    simpa [rvR2, rvR1, RegFile.write, cT, cU] using h
  have s2 : RunsTo store program ⟨rvR2 regs acc wordScale, MB + 2, false⟩
      ⟨rvR3 regs acc wordScale, MB + 3, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨rvR2 regs acc wordScale, MB + 2, false⟩ : State)) rfl h2
    simpa [rvR3, rvR2, rvR1, RegFile.write, cT, cU, cAcc, hAcc,
      sub_div_mul_eq_mod] using h
  have s3 : RunsTo store program ⟨rvR3 regs acc wordScale, MB + 3, false⟩
      ⟨rvR4 regs acc wordScale rev, MB + 4, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.mulConst (store := store)
      (s := (⟨rvR3 regs acc wordScale, MB + 3, false⟩ : State)) rfl h3
    simpa [rvR4, rvR3, rvR2, rvR1, RegFile.write, cT, cU, cRev, hRev]
      using h
  have s4 : RunsTo store program
      ⟨rvR4 regs acc wordScale rev, MB + 4, false⟩
      ⟨rvR5 regs acc wordScale rev, MB + 5, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.add (store := store)
      (s := (⟨rvR4 regs acc wordScale rev, MB + 4, false⟩ : State)) rfl h4
    simpa [rvR5, rvR4, rvR3, rvR2, rvR1, RegFile.write, cU, cRev] using h
  have s5 : RunsTo store program
      ⟨rvR5 regs acc wordScale rev, MB + 5, false⟩
      ⟨rvR6 regs acc wordScale rev, MB + 6, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move (store := store)
      (s := (⟨rvR5 regs acc wordScale rev, MB + 5, false⟩ : State)) rfl h5
    simpa [rvR6, rvR5, rvR4, rvR3, rvR2, rvR1, RegFile.write, cT, cU,
      cRev, cAcc] using h
  have s6 : RunsTo store program
      ⟨rvR6 regs acc wordScale rev, MB + 6, false⟩
      ⟨rvR7 regs acc wordScale rev cnt, MB + 7, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨rvR6 regs acc wordScale rev, MB + 6, false⟩ : State)) rfl h6
    simpa [rvR7, rvR6, rvR5, rvR4, rvR3, rvR2, rvR1, RegFile.write, cT,
      cU, cRev, cAcc, cN, cOne, hN, hOne] using h
  have s7 : RunsTo store program
      ⟨rvR7 regs acc wordScale rev cnt, MB + 7, false⟩
      ⟨rvR7 regs acc wordScale rev cnt, if cnt = 0 then MB + 8 else MB,
        false⟩ [] [Category.branch] := by
    have h := RunsTo.brNZ (store := store)
      (s := (⟨rvR7 regs acc wordScale rev cnt, MB + 7, false⟩ : State))
      rfl h7
    have hn7 : rvR7 regs acc wordScale rev cnt cN = cnt := by
      rw [rvR7_apply]; simp
    simpa [hn7] using h
  refine ⟨rvR7 regs acc wordScale rev cnt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hrun :=
      (((s0.trans s1).trans (s2.trans s3)).trans
        ((s4.trans s5).trans (s6.trans s7)))
    simpa [interiorChunkCombineCats, interiorChunkCombine] using hrun
  · rw [rvR7_apply]; simp [cOne, cN, cAcc, cRev, cU, cT, hOne]
  · rw [rvR7_apply]; simp [cAcc, cN]
  · rw [rvR7_apply]; simp [cRev, cN, cAcc]
  · rw [rvR7_apply]; simp
  · rw [rvR7_apply]; simp [cBad, cN, cAcc, cRev, cU, cT]
  · intro r hr
    obtain ⟨hT, hU, hRv, hAc, hNn⟩ := hr
    rw [rvR7_apply]
    simp [hT, hU, hRv, hAc, hNn]

/--
EXACT SIMULATION OF THE DIGIT-REVERSAL LOOP.

Emits NOTHING -- the receipt is `[]` -- and converts the read loop's
big-endian accumulation into the route's little-endian digit order under
the same iteration count, leaving the result in `cRev`.

`0 < n` is required for the same do-while reason as the read loop.
-/
theorem interiorChunkCombineLoop_runsTo
    (store : ReadStore) {program : E1Machine.Program} {wordScale MB : Nat}
    (hHost : HostedAt program MB (interiorChunkCombine wordScale MB))
    (regsL : RegFile) (acc0 n : Nat) (hn : 0 < n)
    (hOne : regsL cOne = 1) (hAcc : regsL cAcc = acc0)
    (hRev : regsL cRev = 0) (hN : regsL cN = n) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regsL, MB, false⟩ ⟨regsF, MB + 8, false⟩ []
          (iterLog (fun _ => interiorChunkCombineCats) n) ∧
        regsF cOne = 1 ∧
        regsF cRev = (chunkRevAt wordScale acc0 n).2 ∧
        regsF cN = 0 ∧
        regsF cBad = regsL cBad ∧
        (∀ r, ChunkFoldUntouched r → regsF r = regsL r) := by
  let P : Nat → State → Prop := fun k s =>
    k ≤ n ∧ s.halted = false ∧
    s.pc = (if k = 0 then MB + 8 else MB) ∧
    s.regs cOne = 1 ∧
    s.regs cAcc = (chunkRevAt wordScale acc0 (n - k)).1 ∧
    s.regs cRev = (chunkRevAt wordScale acc0 (n - k)).2 ∧
    s.regs cN = k ∧
    s.regs cBad = regsL cBad ∧
    (∀ r, ChunkFoldUntouched r → s.regs r = regsL r)
  have hstep : ∀ k s, P (k + 1) s →
      ∃ s', RunsTo store program s s' [] interiorChunkCombineCats ∧ P k s' := by
    intro k s hP
    obtain ⟨regs, pc, halted⟩ := s
    obtain ⟨hkle, hhalt, hpc, hone, hacc, hrev, hcn, hbad, hpres⟩ := hP
    simp only at hhalt hpc hone hacc hrev hcn hbad hpres
    subst hhalt
    rw [if_neg (Nat.succ_ne_zero k)] at hpc
    subst pc
    have hik : n - k = (n - (k + 1)) + 1 := by omega
    obtain ⟨regs', hrun, hone', hacc', hrev', hcn', hbad', hpres'⟩ :=
      interiorChunkCombine_step store hHost regs
        (chunkRevAt wordScale acc0 (n - (k + 1))).1
        (chunkRevAt wordScale acc0 (n - (k + 1))).2
        k hone hacc hrev hcn
    refine ⟨⟨regs', if k = 0 then MB + 8 else MB, false⟩, hrun, ?_⟩
    refine ⟨by omega, rfl, rfl, hone', ?_, ?_, hcn', ?_, ?_⟩
    · show regs' cAcc = (chunkRevAt wordScale acc0 (n - k)).1
      rw [hacc', hik]
      rfl
    · show regs' cRev = (chunkRevAt wordScale acc0 (n - k)).2
      rw [hrev', hik]
      rfl
    · show regs' cBad = regsL cBad
      rw [hbad', hbad]
    · intro r hr
      show regs' r = regsL r
      rw [hpres' r (chunkCombineUntouched_of_fold hr), hpres r hr]
  have hP0 : P n ⟨regsL, MB, false⟩ := by
    refine ⟨Nat.le_refl n, rfl, ?_, hOne, ?_, ?_, hN, rfl, fun r _ => rfl⟩
    · show MB = if n = 0 then MB + 8 else MB
      rw [if_neg (by omega)]
    · show regsL cAcc = (chunkRevAt wordScale acc0 (n - n)).1
      rw [hAcc, Nat.sub_self]; rfl
    · show regsL cRev = (chunkRevAt wordScale acc0 (n - n)).2
      rw [hRev, Nat.sub_self]; rfl
  obtain ⟨sF, hrunF, hPF⟩ :=
    RunsTo.iterate (store := store) (program := program) P
      (fun _ => []) (fun _ => interiorChunkCombineCats) hstep n
      ⟨regsL, MB, false⟩ hP0
  obtain ⟨regsF, pcF, haltedF⟩ := sF
  obtain ⟨_, hhaltF, hpcF, honeF, _, hrevF, hcnF, hbadF, hpresF⟩ := hPF
  simp only at hhaltF hpcF honeF hrevF hcnF hbadF hpresF
  subst hhaltF
  subst pcF
  refine ⟨regsF, ?_, honeF, ?_, hcnF, hbadF, hpresF⟩
  · rwa [iterLog_nil_reads n] at hrunF
  · rw [hrevF, Nat.sub_zero]

/-! ## The init -/

@[simp] theorem interiorChunkInitHead_length
    (base entriesLen chunkCount : Nat) :
    (interiorChunkInitHead base entriesLen chunkCount).length = 9 := rfl

@[simp] theorem interiorChunkInitDead_length (deadAddress : Nat) :
    (interiorChunkInitDead deadAddress).length = 2 := rfl

@[simp] theorem interiorChunkInitTail_length :
    interiorChunkInitTail.length = 5 := rfl

theorem interiorChunkInitHead_straight (base entriesLen chunkCount : Nat) :
    ∀ instr ∈ interiorChunkInitHead base entriesLen chunkCount,
      instr.isStraight = true := by
  intro instr hi
  simp only [interiorChunkInitHead, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem interiorChunkInitDead_straight (deadAddress : Nat) :
    ∀ instr ∈ interiorChunkInitDead deadAddress,
      instr.isStraight = true := by
  intro instr hi
  simp only [interiorChunkInitDead, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl <;> rfl

theorem interiorChunkInitTail_straight :
    ∀ instr ∈ interiorChunkInitTail, instr.isStraight = true := by
  intro instr hi
  simp only [interiorChunkInitTail, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;> rfl

/-! Preservation for the init's three straight segments, via
`straightRegs_preserves`: a register outside the fold's bank is never a
write target of any of the seventeen instructions. -/

theorem initHead_preserves (store : ReadStore)
    (base entriesLen chunkCount : Nat) (regs : RegFile) {r : Nat}
    (hr : ChunkFoldUntouched r) :
    straightRegs store (interiorChunkInitHead base entriesLen chunkCount)
      regs r = regs r := by
  simp only [ChunkFoldUntouched] at hr
  apply straightRegs_preserves
  intro instr hi
  simp only [interiorChunkInitHead, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Instr.writesTo, cT, cU, cAddr, cCnt, ne_eq,
      Option.some.injEq]; omega)

theorem initDead_preserves (store : ReadStore) (deadAddress : Nat)
    (regs : RegFile) {r : Nat} (hr : ChunkFoldUntouched r) :
    straightRegs store (interiorChunkInitDead deadAddress) regs r
      = regs r := by
  simp only [ChunkFoldUntouched] at hr
  apply straightRegs_preserves
  intro instr hi
  simp only [interiorChunkInitDead, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl <;>
    (simp only [Instr.writesTo, cAddr, cCnt, ne_eq, Option.some.injEq];
      omega)

theorem initTail_preserves (store : ReadStore) (regs : RegFile) {r : Nat}
    (hr : ChunkFoldUntouched r) :
    straightRegs store interiorChunkInitTail regs r = regs r := by
  simp only [ChunkFoldUntouched] at hr
  apply straightRegs_preserves
  intro instr hi
  simp only [interiorChunkInitTail, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl <;>
    (simp only [Instr.writesTo, cOne, cAcc, cBad, cRev, cN, ne_eq,
      Option.some.injEq]; omega)

/-- The cap chain computes the minimum.  This is the arithmetic content of
DD-20260719-005: the machine's two truncated subtractions ARE `min`. -/
theorem cap_chain_eq_min (chunkCount : Nat) :
    chunkCount - (chunkCount - 8) = Nat.min chunkCount 8 := by
  by_cases h : chunkCount ≤ 8
  · have hmin : Nat.min chunkCount 8 = chunkCount := Nat.min_eq_left h
    rw [hmin]; omega
  · have h8 : 8 ≤ chunkCount := by omega
    have hmin : Nat.min chunkCount 8 = 8 := Nat.min_eq_right h8
    rw [hmin]; omega

/--
EXACT SIMULATION OF THE FOLD INIT.

Emits NOTHING (no `readMem` in any of the three segments), charges the
validity-indexed log, and leaves the machine with the route's start
address in `cAddr` and the eight-capped iteration count in both `cCnt` and
its saved copy `cN`, with the accumulators zeroed.

The validity test is performed BY THE MACHINE -- `natLt` at `Q+1` against
the machine's own index register, branched at `Q+9` -- not by a Lean-level
`if` around the block, which is what REQ-E1-05's anti-vacuity challenge
demands of a guard.
-/
theorem interiorChunkInit_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {base deadAddress entriesLen chunkCount Q : Nat}
    (hHost : HostedAt program Q
      (interiorChunkInit base deadAddress entriesLen chunkCount Q))
    (regs : RegFile) (i : Nat) (hIdx : regs iIdx = i) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 17, false⟩ []
          (interiorChunkInitCats (decide (i < entriesLen))) ∧
        regs' cOne = 1 ∧
        regs' cAddr =
          chunkStart base deadAddress entriesLen chunkCount i ∧
        regs' cCnt = chunkIters entriesLen chunkCount i ∧
        regs' cN = chunkIters entriesLen chunkCount i ∧
        regs' cAcc = 0 ∧ regs' cBad = 0 ∧ regs' cRev = 0 ∧
        (∀ r, ChunkFoldUntouched r → regs' r = regs r) := by
  have hHead : HostedAt program Q
      (interiorChunkInitHead base entriesLen chunkCount) :=
    hHost.append_left.append_left.append_left
  have hBr : program[Q + 9]? = some (.brNZ cT (Q + 12)) := by
    have h := hHost.append_left.append_left.append_right
    simpa using h.head
  have hDead : HostedAt program (Q + 10)
      (interiorChunkInitDead deadAddress) := by
    have h := hHost.append_left.append_right
    simpa using h
  have hTail : HostedAt program (Q + 12) interiorChunkInitTail := by
    have h := hHost.append_right
    simpa using h
  have rHead := RunsTo.straight store
    (interiorChunkInitHead base entriesLen chunkCount)
    (interiorChunkInitHead_straight base entriesLen chunkCount) Q hHead regs
  have rTail : ∀ rr : RegFile,
      RunsTo store program ⟨rr, Q + 12, false⟩
        ⟨straightRegs store interiorChunkInitTail rr, Q + 17, false⟩
        (straightReads store interiorChunkInitTail rr)
        (interiorChunkInitTail.map Instr.category) := by
    intro rr
    have h := RunsTo.straight store interiorChunkInitTail
      interiorChunkInitTail_straight (Q + 12) hTail rr
    simpa using h
  by_cases hvalid : i < entriesLen
  · -- LIVE path: the branch is taken and the dead override is skipped
    have hcond :
        straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs cT ≠ 0 := by
      straight_eval [interiorChunkInitHead, cT, cU, cAddr, cCnt, iIdx]
      simp [hIdx, hvalid]
    have rBr : RunsTo store program
        ⟨straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs,
          Q + 9, false⟩
        ⟨straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs,
          Q + 12, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken (store := store)
        (s := (⟨straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs, Q + 9,
          false⟩ : State)) rfl (by simpa using hBr) hcond
      simpa using h
    refine ⟨straightRegs store interiorChunkInitTail
      (straightRegs store
        (interiorChunkInitHead base entriesLen chunkCount) regs),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hrun := (rHead.trans rBr).trans (rTail _)
      have hreads : straightReads store
          (interiorChunkInitHead base entriesLen chunkCount) regs = [] := by
        straight_eval [interiorChunkInitHead]
      have hreadsT : straightReads store interiorChunkInitTail
          (straightRegs store
            (interiorChunkInitHead base entriesLen chunkCount) regs)
          = [] := by
        straight_eval [interiorChunkInitTail]
      rw [hreads, hreadsT] at hrun
      simpa [interiorChunkInitCats, hvalid] using hrun
    · straight_eval [interiorChunkInitTail, interiorChunkInitHead, cOne,
        cAcc, cBad, cRev, cN, cCnt, cT, cU, cAddr, iIdx]
    · straight_eval [interiorChunkInitTail, interiorChunkInitHead, cOne,
        cAcc, cBad, cRev, cN, cCnt, cT, cU, cAddr, iIdx]
      simp [chunkStart, hvalid, hIdx]
    · straight_eval [interiorChunkInitTail, interiorChunkInitHead, cOne,
        cAcc, cBad, cRev, cN, cCnt, cT, cU, cAddr, iIdx]
      simp [chunkIters, hvalid, cap_chain_eq_min]
    · straight_eval [interiorChunkInitTail, interiorChunkInitHead, cOne,
        cAcc, cBad, cRev, cN, cCnt, cT, cU, cAddr, iIdx]
      simp [chunkIters, hvalid, cap_chain_eq_min]
    · straight_eval [interiorChunkInitTail, interiorChunkInitHead, cOne,
        cAcc, cBad, cRev, cN, cCnt, cT, cU, cAddr, iIdx]
    · straight_eval [interiorChunkInitTail, interiorChunkInitHead, cOne,
        cAcc, cBad, cRev, cN, cCnt, cT, cU, cAddr, iIdx]
    · straight_eval [interiorChunkInitTail, interiorChunkInitHead, cOne,
        cAcc, cBad, cRev, cN, cCnt, cT, cU, cAddr, iIdx]
    · intro r hr
      rw [initTail_preserves store _ hr, initHead_preserves store _ _ _ _ hr]
  · -- DEAD path: the branch falls through into the override
    have hcond :
        straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs cT = 0 := by
      straight_eval [interiorChunkInitHead, cT, cU, cAddr, cCnt, iIdx,
        hIdx, hvalid]
    have rBr : RunsTo store program
        ⟨straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs,
          Q + 9, false⟩
        ⟨straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs,
          Q + 10, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_not_taken (store := store)
        (s := (⟨straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs, Q + 9,
          false⟩ : State)) rfl (by simpa using hBr) hcond
      simpa using h
    have rDead : RunsTo store program
        ⟨straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs,
          Q + 10, false⟩
        ⟨straightRegs store (interiorChunkInitDead deadAddress)
          (straightRegs store
            (interiorChunkInitHead base entriesLen chunkCount) regs),
          Q + 12, false⟩
        (straightReads store (interiorChunkInitDead deadAddress)
          (straightRegs store
            (interiorChunkInitHead base entriesLen chunkCount) regs))
        ((interiorChunkInitDead deadAddress).map Instr.category) := by
      have h := RunsTo.straight store (interiorChunkInitDead deadAddress)
        (interiorChunkInitDead_straight deadAddress) (Q + 10) hDead
        (straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs)
      simpa using h
    refine ⟨straightRegs store interiorChunkInitTail
      (straightRegs store (interiorChunkInitDead deadAddress)
        (straightRegs store
          (interiorChunkInitHead base entriesLen chunkCount) regs)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hrun := ((rHead.trans rBr).trans rDead).trans (rTail _)
      have hreads : straightReads store
          (interiorChunkInitHead base entriesLen chunkCount) regs = [] := by
        straight_eval [interiorChunkInitHead]
      have hreadsD : straightReads store (interiorChunkInitDead deadAddress)
          (straightRegs store
            (interiorChunkInitHead base entriesLen chunkCount) regs)
          = [] := by
        straight_eval [interiorChunkInitDead]
      have hreadsT : straightReads store interiorChunkInitTail
          (straightRegs store (interiorChunkInitDead deadAddress)
            (straightRegs store
              (interiorChunkInitHead base entriesLen chunkCount) regs))
          = [] := by
        straight_eval [interiorChunkInitTail]
      rw [hreads, hreadsD, hreadsT] at hrun
      simpa [interiorChunkInitCats, hvalid] using hrun
    · straight_eval [interiorChunkInitTail, interiorChunkInitDead,
        interiorChunkInitHead, cOne, cAcc, cBad, cRev, cN, cCnt, cT, cU,
        cAddr, iIdx]
    · straight_eval [interiorChunkInitTail, interiorChunkInitDead,
        interiorChunkInitHead, cOne, cAcc, cBad, cRev, cN, cCnt, cT, cU,
        cAddr, iIdx]
      simp [chunkStart, hvalid]
    · straight_eval [interiorChunkInitTail, interiorChunkInitDead,
        interiorChunkInitHead, cOne, cAcc, cBad, cRev, cN, cCnt, cT, cU,
        cAddr, iIdx]
      simp [chunkIters, hvalid]
    · straight_eval [interiorChunkInitTail, interiorChunkInitDead,
        interiorChunkInitHead, cOne, cAcc, cBad, cRev, cN, cCnt, cT, cU,
        cAddr, iIdx]
      simp [chunkIters, hvalid]
    · straight_eval [interiorChunkInitTail, interiorChunkInitDead,
        interiorChunkInitHead, cOne, cAcc, cBad, cRev, cN, cCnt, cT, cU,
        cAddr, iIdx]
    · straight_eval [interiorChunkInitTail, interiorChunkInitDead,
        interiorChunkInitHead, cOne, cAcc, cBad, cRev, cN, cCnt, cT, cU,
        cAddr, iIdx]
    · straight_eval [interiorChunkInitTail, interiorChunkInitDead,
        interiorChunkInitHead, cOne, cAcc, cBad, cRev, cN, cCnt, cT, cU,
        cAddr, iIdx]
    · intro r hr
      rw [initTail_preserves store _ hr, initDead_preserves store _ _ hr,
        initHead_preserves store _ _ _ _ hr]

/-! ## The epilogue -/

/--
EXACT SIMULATION OF THE EPILOGUE.

Re-imposes the option shift.  The `none` verdict is a MACHINE BRANCH on a
MACHINE-ACCUMULATED count: `cBad` was incremented once per missing chunk
by the read loop, and the epilogue branches on it.  Nothing here consults
a Lean-level `if` about the store.
-/
theorem interiorChunkEpilogue_runsTo
    (store : ReadStore) {program : E1Machine.Program} {E : Nat}
    (hHost : HostedAt program E (interiorChunkEpilogue E))
    (regs : RegFile) (rev bad : Nat)
    (hOne : regs cOne = 1) (hRev : regs cRev = rev)
    (hBad : regs cBad = bad) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, E, false⟩ ⟨regs', E + 3, false⟩ []
          (interiorChunkEpilogueCats (decide (bad = 0))) ∧
        regs' cOut = (if bad = 0 then rev + 1 else 0) ∧
        (∀ r, ChunkFoldUntouched r → regs' r = regs r) := by
  have h0 : program[E]? = some (.const cOut 0) := by
    simpa using hHost.head
  have h1 : program[E + 1]? = some (.brNZ cBad (E + 3)) := by
    have h := hHost 1 (by simp)
    simpa using h
  have h2 : program[E + 2]? = some (.add cOut cRev cOne) := by
    have h := hHost 2 (by simp)
    simpa using h
  have s0 : RunsTo store program ⟨regs, E, false⟩
      ⟨regs.write cOut 0, E + 1, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨regs, E, false⟩ : State)) rfl h0
    simpa using h
  have hbadv : (regs.write cOut 0) cBad = bad := by
    simp [RegFile.write, cOut, cBad, hBad]
  by_cases hzero : bad = 0
  · -- every chunk present: fall through and shift the value
    have sbr : RunsTo store program ⟨regs.write cOut 0, E + 1, false⟩
        ⟨regs.write cOut 0, E + 2, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_not_taken (store := store)
        (s := (⟨regs.write cOut 0, E + 1, false⟩ : State)) rfl h1
        (by show regs.write cOut 0 cBad = 0; rw [hbadv]; exact hzero)
      simpa using h
    have sadd : RunsTo store program ⟨regs.write cOut 0, E + 2, false⟩
        ⟨(regs.write cOut 0).write cOut (rev + 1), E + 3, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.add (store := store)
        (s := (⟨regs.write cOut 0, E + 2, false⟩ : State)) rfl h2
      simpa [RegFile.write, cOut, cRev, cOne, hRev, hOne] using h
    refine ⟨(regs.write cOut 0).write cOut (rev + 1), ?_, ?_, ?_⟩
    · have hrun := (s0.trans sbr).trans sadd
      simpa [interiorChunkEpilogueCats, hzero] using hrun
    · simp [RegFile.write, hzero]
    · intro r hr
      simp only [ChunkFoldUntouched] at hr
      have hne : r ≠ cOut := by simp only [cOut]; omega
      simp [RegFile.write, hne]
  · -- some chunk missing: the branch keeps the `none` default
    have sbr : RunsTo store program ⟨regs.write cOut 0, E + 1, false⟩
        ⟨regs.write cOut 0, E + 3, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken (store := store)
        (s := (⟨regs.write cOut 0, E + 1, false⟩ : State)) rfl h1
        (by show regs.write cOut 0 cBad ≠ 0; rw [hbadv]; exact hzero)
      simpa using h
    refine ⟨regs.write cOut 0, ?_, ?_, ?_⟩
    · have hrun := s0.trans sbr
      simpa [interiorChunkEpilogueCats, hzero] using hrun
    · simp [RegFile.write, hzero]
    · intro r hr
      simp only [ChunkFoldUntouched] at hr
      have hne : r ≠ cOut := by simp only [cOut]; omega
      simp [RegFile.write, hne]

/-! ## The whole fold -/

/-- The route's trace for one chunked read: its own address list, each
address paired with the word the store holds there. -/
def chunkRouteEvents (store : ReadStore)
    (segment base deadAddress entriesLen chunkCount i : Nat) :
    List TraceEvent :=
  (chunkAddrs base deadAddress entriesLen chunkCount i).map
    (fun a => TraceEvent.readWord segment a (store.readWord? segment a))

/--
THE POSITIONAL RECEIPT IDENTITY.

What the machine's fold emits (`chunkEventsAt` at the machine-computed
start and count) is what the route's adapter issues
(`chunkRouteEvents`) -- the same addresses, in the same positions,
carrying the same words -- for BOTH arms of the validity split at once.
-/
theorem chunkEventsAt_eq_route (store : ReadStore)
    {segment base deadAddress entriesLen chunkCount i : Nat}
    (hcap : chunkCount ≤ 8) :
    chunkEventsAt store segment
        (chunkStart base deadAddress entriesLen chunkCount i)
        (chunkIters entriesLen chunkCount i)
      = chunkRouteEvents store segment base deadAddress entriesLen
          chunkCount i := by
  unfold chunkRouteEvents chunkEventsAt
  rw [chunkAddrs_eq_consecutive hcap]

/-- The fold's iteration count is positive exactly when the table has a
chunk to read. -/
theorem chunkIters_pos {entriesLen chunkCount i : Nat}
    (hcc : 0 < chunkCount) : 0 < chunkIters entriesLen chunkCount i := by
  unfold chunkIters
  split
  · rcases Nat.le_total chunkCount 8 with h | h
    · have e : Nat.min chunkCount 8 = chunkCount := Nat.min_eq_left h
      rw [e]; omega
    · have e : Nat.min chunkCount 8 = 8 := Nat.min_eq_right h
      rw [e]; omega
  · omega

/--
EXACT SIMULATION OF THE INTERIOR'S EIGHT-CAPPED CHUNK FOLD.

From the block entry with the logical table index in `iIdx`, the
thirty-seven hosted instructions run to the block exit at `Q + 37`,
emitting EXACTLY THE ROUTE'S TRACE for that chunked read -- positionally,
address for address, word for word, on both arms of the validity split --
charging the fold's category log, and leaving the decoded cell in `cOut`
in the option-shift convention.

The two hypotheses are the ones DD-20260719-003 identified and refused to
hide.  `0 < chunkCount` is the half the route's `<= 8` cost bound does not
supply: at zero chunks the route reads nothing while this do-while block
still reads once.  `chunkCount <= 8` is the within-macro cap, discharged
for every reachable shape by `interiorChunkCount_le_eight`.
-/
theorem interiorChunkFold_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {segment base deadAddress entriesLen chunkCount wordScale Q : Nat}
    (hHost : HostedAt program Q
      (interiorChunkFold segment base deadAddress entriesLen chunkCount
        wordScale Q))
    (hccPos : 0 < chunkCount) (hccCap : chunkCount ≤ 8)
    (regs : RegFile) (i : Nat) (hIdx : regs iIdx = i) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 37, false⟩
          (chunkRouteEvents store segment base deadAddress entriesLen
            chunkCount i)
          (interiorChunkFoldCats (decide (i < entriesLen))
            (decide (chunkBad store segment
              (chunkStart base deadAddress entriesLen chunkCount i)
              (chunkIters entriesLen chunkCount i) = 0))
            (chunkIters entriesLen chunkCount i)) ∧
        regs' cOut =
          (if chunkBad store segment
                (chunkStart base deadAddress entriesLen chunkCount i)
                (chunkIters entriesLen chunkCount i) = 0 then
            (chunkRevAt wordScale
              (chunkAcc store segment wordScale
                (chunkStart base deadAddress entriesLen chunkCount i)
                (chunkIters entriesLen chunkCount i))
              (chunkIters entriesLen chunkCount i)).2 + 1
          else 0) ∧
        (∀ r, ChunkFoldUntouched r → regs' r = regs r) := by
  have hIters : 0 < chunkIters entriesLen chunkCount i :=
    chunkIters_pos hccPos
  -- hosting decomposition
  have hInit : HostedAt program Q
      (interiorChunkInit base deadAddress entriesLen chunkCount Q) :=
    hHost.append_left.append_left.append_left
  have hRead : HostedAt program (Q + 17)
      (interiorChunkReadBody segment wordScale (Q + 17)) := by
    have h := hHost.append_left.append_left.append_right
    simpa using h
  have hComb : HostedAt program (Q + 26)
      (interiorChunkCombine wordScale (Q + 26)) := by
    have h := hHost.append_left.append_right
    simpa using h
  have hEpi : HostedAt program (Q + 34)
      (interiorChunkEpilogue (Q + 34)) := by
    have h := hHost.append_right
    simpa using h
  -- the four segments
  obtain ⟨r1, rInit, h1One, h1Addr, h1Cnt, h1N, h1Acc, h1Bad, h1Rev,
    h1Pres⟩ := interiorChunkInit_runsTo store hInit regs i hIdx
  obtain ⟨r2, rRead, h2One, _h2Cnt, h2Acc, h2Bad, h2N, h2Rev, h2Pres⟩ :=
    interiorChunkReadLoop_runsTo store hRead r1
      (chunkStart base deadAddress entriesLen chunkCount i)
      (chunkIters entriesLen chunkCount i) hIters h1One h1Addr h1Cnt
      h1Acc h1Bad
  have h2Nv : r2 cN = chunkIters entriesLen chunkCount i := by
    rw [h2N, h1N]
  have h2Revv : r2 cRev = 0 := by rw [h2Rev, h1Rev]
  obtain ⟨r3, rComb, h3One, h3Rev, _h3N, h3Bad, h3Pres⟩ :=
    interiorChunkCombineLoop_runsTo store hComb r2
      (chunkAcc store segment wordScale
        (chunkStart base deadAddress entriesLen chunkCount i)
        (chunkIters entriesLen chunkCount i))
      (chunkIters entriesLen chunkCount i) hIters h2One h2Acc h2Revv h2Nv
  have h3Badv : r3 cBad =
      chunkBad store segment
        (chunkStart base deadAddress entriesLen chunkCount i)
        (chunkIters entriesLen chunkCount i) := by
    rw [h3Bad, h2Bad]
  obtain ⟨r4, rEpi, h4Out, h4Pres⟩ :=
    interiorChunkEpilogue_runsTo store hEpi r3 _ _ h3One h3Rev h3Badv
  refine ⟨r4, ?_, h4Out, ?_⟩
  · have hrun := ((rInit.trans rRead).trans rComb).trans rEpi
    rw [chunkEventsAt_eq_route store hccCap] at hrun
    simpa [interiorChunkFoldCats] using hrun
  · -- OUTSIDE THE BANK `89 .. 99` NOTHING MOVES: chain the four segments'
    -- own preservation clauses.  This is what makes the fold composable
    -- more than once in a single program (M3d-13 item 2).
    intro r hr
    rw [h4Pres r hr, h3Pres r hr, h2Pres r hr, h1Pres r hr]

/-! ## Hosting witness: the paths EXECUTE, onto distinguishable halts

`interiorChunkFold_runsTo` is a statement about every store and every
index.  A theorem of that shape can be true because its paths are
unreachable, so the block is also RUN here, on a concrete store, and the
outcomes are checked to differ.

The witness shape: one segment, table base `10`, dead address `99`,
three logical entries, TWO chunks per entry, word scale `2` (one-bit
chunks).  The store holds words at `10`, `11`, `12` and at the dead
address `99`, and holds nothing at `13`, `14`, `15` -- so the witness
exercises a fully present multi-chunk read, a partially missing one, a
wholly missing one, and the dead path.
-/

/-- Witness store: present at `10`, `11`, `12`, `99`; absent elsewhere. -/
def witnessStore : ReadStore :=
  ⟨fun segment address =>
    if segment = 0 then
      if address = 10 then some [true]
      else if address = 11 then some [false]
      else if address = 12 then some [true]
      else if address = 99 then some [true]
      else none
    else none⟩

/-- Witness program: the fold at base `0`, then `halt`. -/
def chunkFoldWitness : E1Machine.Program :=
  interiorChunkFold 0 10 99 3 2 2 0 ++ [.halt]

/-- The witness program hosts the fold at base `0`. -/
theorem chunkFoldWitness_hosts :
    HostedAt chunkFoldWitness 0 (interiorChunkFold 0 10 99 3 2 2 0) :=
  HostedAt.append_left (hostedAt_self chunkFoldWitness)

/-- Register file for one path: only the logical index is supplied. -/
def witnessRegs (i : Nat) : RegFile := RegFile.write (fun _ => 0) iIdx i

/-- The observable outcome of running the witness at one index: exit pc,
halted flag, modeled steps, option-shifted cell, read log. -/
def witnessOutcome (i : Nat) :
    Nat × Bool × Nat × Nat × List TraceEvent :=
  let r := run witnessStore chunkFoldWitness 128 ⟨witnessRegs i, 0, false⟩
  (r.final.pc, r.final.halted, r.steps, r.final.regs cOut, r.readLog)

/-- PATH 1: a valid index whose TWO chunks are both present.  The block
reads `10` then `11` -- ASCENDING, the route's order -- and returns the
option-shifted `bitsToNatLE ([true] ++ [false]) = 1`, i.e. `2`.  This is
the executed check that the big-endian read loop and the read-free
reversal loop compose back to the route's LITTLE-endian value. -/
theorem chunkFoldWitness_path_bothPresent :
    witnessOutcome 0 =
      (37, true, 53, 2,
        [.readWord 0 10 (some [true]), .readWord 0 11 (some [false])]) :=
  rfl

/-- PATH 2: a valid index whose SECOND chunk is missing.  Both chunks are
still read -- the fold does not short-circuit -- and the missing chunk
drives `cOut` to the option-shift's `none`. -/
theorem chunkFoldWitness_path_partiallyMissing :
    witnessOutcome 1 =
      (37, true, 52, 0,
        [.readWord 0 12 (some [true]), .readWord 0 13 none]) := rfl

/-- PATH 3: a valid index whose chunks are BOTH missing. -/
theorem chunkFoldWitness_path_whollyMissing :
    witnessOutcome 2 =
      (37, true, 52, 0,
        [.readWord 0 14 none, .readWord 0 15 none]) := rfl

/-- PATH 4: an index past the table.  The dead path reads the dead address
ONCE -- it is a one-chunk instance of the same fold (DD-20260719-006) --
and costs two more init steps and one fewer loop pass. -/
theorem chunkFoldWitness_path_dead :
    witnessOutcome 5 =
      (37, true, 38, 2, [.readWord 0 99 (some [true])]) := rfl

/-- Every path HALTS, at the same exit, having actually run. -/
theorem chunkFoldWitness_all_halt :
    [ (witnessOutcome 0).2.1, (witnessOutcome 1).2.1
    , (witnessOutcome 2).2.1, (witnessOutcome 5).2.1 ]
      = [true, true, true, true] := rfl

/--
THE FOUR EXECUTED PATHS ARE PAIRWISE DISTINGUISHABLE on the
`(modeled steps, option-shifted cell, read log)` triple.  This is the
statement that would fail if any two control paths collapsed.

WORTH RECORDING FOR THE VALIDATOR'S DISCRIMINATOR CHOICE (M6): paths 2 and
3 agree on BOTH the modeled step count (`52`) and the returned cell (`0`).
They are separated ONLY by the read log.  So on this block a value check
has no power over a receipt-only difference, and step counting has none
either -- a mutation that redirected a chunk read to a different address
of the same multiplicity would pass both and be caught only by
event-by-event receipt diffing.
-/
theorem chunkFoldWitness_paths_distinguishable :
    let obs := fun (o : Nat × Bool × Nat × Nat × List TraceEvent) =>
      (o.2.2.1, o.2.2.2.1, o.2.2.2.2)
    [ obs (witnessOutcome 0), obs (witnessOutcome 1)
    , obs (witnessOutcome 2), obs (witnessOutcome 5) ].Nodup := by decide

/-- Executed form of the cap: no path reads more than the literal `8`
chunks, and the multi-chunk paths genuinely read more than one -- so the
fold is exercised as a FOLD, not merely as the single-chunk atom the
predecessor block already covered. -/
theorem chunkFoldWitness_readCounts :
    [ (witnessOutcome 0).2.2.2.2.length, (witnessOutcome 1).2.2.2.2.length
    , (witnessOutcome 2).2.2.2.2.length
    , (witnessOutcome 5).2.2.2.2.length ]
      = [2, 2, 2, 1] := rfl

end E1InteriorChunkFold
end WordRAM
end RMQ
