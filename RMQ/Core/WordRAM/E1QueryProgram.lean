import RMQ.Core.WordRAM.E1MachineCalculus

/-!
# E1 amended machine: whole-query program skeleton and validity guard

First route-facing layer over the E1 machine (frozen matrix
`docs/internal/E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`, REQ-E1-05 plus the
program-representation half of REQ-E1-03): the frozen query register map, the
option-shift output packet convention, the per-shape program skeleton, and the
charged validity guard with its checked invalid-rejection theorems.

Design (DD-20260718-006):

* the machine receives the query operands in fixed input registers
  (`regLeft`, `regRight`) and reports its answer packet in `regOut` using the
  same option-shift encoding as `decodeRead`: `0` decodes to `none`,
  `v + 1` decodes to `some v` (`decodePacket`);
* a concrete program is `programSkeleton n validPath`: the eight-instruction
  charged guard prologue at base `0`, then the valid-path block at base `8`,
  then the two-instruction invalid exit at base `8 + validPath.length`.  The
  invalid exit is reachable only through the guard's two conditional
  branches; the valid path terminates by writing `regOut` and halting, so it
  never falls through into the exit block;
* the guard is computed BY MACHINE INSTRUCTIONS on the input registers -
  `natLt`/`natLe` comparisons, `natEq` negations against the pinned zero
  register, and `brNZ` branches - so rejection charges machine steps in the
  frozen categories, unlike the accepted route's Lean-level
  `withValidRange` boundary which charges nothing.  The rejection theorems
  record the exact category logs (`guardRejectRangeCats`,
  `guardRejectBoundsCats`), an empty receipt log, and a zero memory-read
  count, matching `SuccinctClassic.queryCosted_invalid` semantics (the
  bridge statement lives in `RMQ.Core.WordRAM.E1QueryBridge`).

The guard theorems are stated against ANY program hosting the guard block at
base `0` and the invalid exit at its branch target (via `HostedAt`), so they
are stable while the valid-path component blocks land.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine

/-! ## Frozen query register map (DD-20260718-006) -/

/-- Input register: query left endpoint. -/
abbrev regLeft : Nat := 0

/-- Input register: query right endpoint (half-open). -/
abbrev regRight : Nat := 1

/-- Output packet register (option-shift encoding: `0` decodes to `none`,
`v + 1` decodes to `some v`). -/
abbrev regOut : Nat := 2

/-- Pinned zero constant, written by the guard prologue. -/
abbrev regZero : Nat := 3

/-- Per-shape input-size constant `n`, written by the guard prologue. -/
abbrev regN : Nat := 4

/-- Guard scratch: result of the `left < right` comparison. -/
abbrev regT1 : Nat := 5

/-- Guard scratch: result of the `right <= n` comparison. -/
abbrev regT2 : Nat := 6

/-- Guard scratch: negation flag feeding the invalid branch. -/
abbrev regG : Nat := 7

/-- First register index reserved for valid-path component blocks. -/
abbrev firstComponentReg : Nat := 8

/-! ## Machine-level query conventions -/

/-- Query-input register file: the two input registers carry the query
operands; every other register starts at zero. -/
def initialRegs (left right : Nat) : RegFile := fun r =>
  if r = regLeft then left else if r = regRight then right else 0

/-- Machine start state for one query: input registers loaded, program
counter at the guard prologue, not halted. -/
def initialState (left right : Nat) : State :=
  ⟨initialRegs left right, 0, false⟩

/-- Output packet decode, mirroring `decodeRead`'s option shift: `0` is the
guarded `none` packet, `v + 1` carries answer `v`. -/
def decodePacket (v : Nat) : Option Nat :=
  if v = 0 then none else some (v - 1)

@[simp] theorem decodePacket_zero : decodePacket 0 = none := rfl

@[simp] theorem decodePacket_succ (v : Nat) :
    decodePacket (v + 1) = some v := by
  simp [decodePacket]

/-! ## Guard prologue, invalid exit, and the program skeleton -/

/--
Charged validity guard: pin `0`, load the per-shape size constant `n`,
compare `left < right` and `right <= n` on the input registers, and branch
to `invalidBase` when either test fails.  Every check is an executed
machine instruction, so rejection is charged in the frozen categories.
-/
def guardBlock (n invalidBase : Nat) : List Instr :=
  [ .const regZero 0
  , .const regN n
  , .natLt regT1 regLeft regRight
  , .natLe regT2 regRight regN
  , .natEq regG regT1 regZero
  , .brNZ regG invalidBase
  , .natEq regG regT2 regZero
  , .brNZ regG invalidBase ]

@[simp] theorem guardBlock_length (n invalidBase : Nat) :
    (guardBlock n invalidBase).length = 8 := rfl

/-- Invalid exit: write the `none` packet and halt. -/
def invalidExitBlock : List Instr :=
  [ .const regOut 0
  , .halt ]

@[simp] theorem invalidExitBlock_length : invalidExitBlock.length = 2 := rfl

/--
Per-shape program skeleton: guard prologue at base `0`, the valid-path block
at base `8`, the invalid exit at base `8 + validPath.length`.  The exit block
is reachable only through the guard branches: the valid path ends by writing
`regOut` and halting.
-/
def programSkeleton (n : Nat) (validPath : List Instr) : E1Machine.Program :=
  guardBlock n (8 + validPath.length) ++ (validPath ++ invalidExitBlock)

theorem programSkeleton_def (n : Nat) (validPath : List Instr) :
    programSkeleton n validPath =
      guardBlock n (8 + validPath.length) ++
        (validPath ++ invalidExitBlock) := rfl

@[simp] theorem programSkeleton_length (n : Nat) (validPath : List Instr) :
    (programSkeleton n validPath).length = 10 + validPath.length := by
  simp [programSkeleton, Nat.add_comm]

/-- The skeleton hosts the guard prologue at base `0`. -/
theorem programSkeleton_hosts_guardBlock (n : Nat) (validPath : List Instr) :
    HostedAt (programSkeleton n validPath) 0
      (guardBlock n (8 + validPath.length)) :=
  HostedAt.append_left (hostedAt_self (programSkeleton n validPath))

/-- The skeleton hosts the valid-path block at base `8`. -/
theorem programSkeleton_hosts_validPath (n : Nat) (validPath : List Instr) :
    HostedAt (programSkeleton n validPath) 8 validPath := by
  have h :=
    HostedAt.append_left
      (HostedAt.append_right (hostedAt_self (programSkeleton n validPath)))
  simpa using h

/-- The skeleton hosts the invalid exit at the guard branch target. -/
theorem programSkeleton_hosts_invalidExit (n : Nat) (validPath : List Instr) :
    HostedAt (programSkeleton n validPath) (8 + validPath.length)
      invalidExitBlock := by
  have h :=
    HostedAt.append_right
      (HostedAt.append_right (hostedAt_self (programSkeleton n validPath)))
  simpa using h

/-! ## Constructor-exhaustive width accounting for the skeleton -/

/-- Every guard-prologue field fits any width whose word can hold `n`, the
branch target, and the eight-register map. -/
theorem guardBlock_fits {w n invalidBase : Nat}
    (hn : n < 2 ^ w) (hbase : invalidBase < 2 ^ w) (hw : 8 ≤ 2 ^ w) :
    ∀ instr ∈ guardBlock n invalidBase, instr.FieldsFit w := by
  intro instr hmem
  simp only [guardBlock, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h <;> subst h <;>
    simp only [Instr.FieldsFit, regLeft, regRight, regZero, regN,
      regT1, regT2, regG] <;> omega

/-- Every invalid-exit field fits any width that can hold the register map. -/
theorem invalidExitBlock_fits {w : Nat} (hw : 8 ≤ 2 ^ w) :
    ∀ instr ∈ invalidExitBlock, instr.FieldsFit w := by
  intro instr hmem
  simp only [invalidExitBlock, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h <;> subst h <;>
    simp only [Instr.FieldsFit, regOut] <;> omega

/-- Skeleton width certificate: the whole program fits once `n`, the branch
target, and every valid-path field fit. -/
theorem programSkeleton_fits {w n : Nat} {validPath : List Instr}
    (hn : n < 2 ^ w) (hbase : 8 + validPath.length < 2 ^ w) (hw : 8 ≤ 2 ^ w)
    (hvalid : ∀ instr ∈ validPath, instr.FieldsFit w) :
    ProgramFits w (programSkeleton n validPath) := by
  intro instr hmem
  simp only [programSkeleton, List.mem_append] at hmem
  rcases hmem with h | h | h
  · exact guardBlock_fits hn hbase hw instr h
  · exact hvalid instr h
  · exact invalidExitBlock_fits hw instr h

/-! ## Charged invalid rejection -/

/-- Exact category log charged when the guard rejects an empty or reversed
range (`¬ left < right`): two constant loads, the two range comparisons, one
negation, the taken branch, the `none`-packet write, halt. -/
def guardRejectRangeCats : List Category :=
  [ .registerWrite, .registerWrite, .comparison, .comparison, .comparison
  , .branch, .registerWrite, .control ]

/-- Exact category log charged when the guard rejects an out-of-bounds range
(`left < right` but `¬ right ≤ n`): both negations and both branches
execute before the `none`-packet write and halt. -/
def guardRejectBoundsCats : List Category :=
  [ .registerWrite, .registerWrite, .comparison, .comparison, .comparison
  , .branch, .comparison, .branch, .registerWrite, .control ]

/--
Guard rejection, empty/reversed ranges: from the query start state, any
program hosting the guard block at base `0` and the invalid exit at
`invalidBase` runs - with exact fuel - to a halted state carrying the
`none` output packet, an EMPTY receipt log, and exactly the frozen
`guardRejectRangeCats` category log.
-/
theorem guard_reject_of_not_lt
    (store : ReadStore) {program : E1Machine.Program} {n invalidBase : Nat}
    (hguard : HostedAt program 0 (guardBlock n invalidBase))
    (hexit : HostedAt program invalidBase invalidExitBlock)
    {left right : Nat} (hnot : ¬ left < right) :
    ∃ final : State,
      RunsTo store program (initialState left right) final []
          guardRejectRangeCats ∧
        final.halted = true ∧ final.regs regOut = 0 := by
  have hf0 : program[0]? = some (.const regZero 0) := by
    have h := hguard 0 (by simp)
    simpa [guardBlock] using h
  have hf1 : program[1]? = some (.const regN n) := by
    have h := hguard 1 (by simp)
    simpa [guardBlock] using h
  have hf2 : program[2]? = some (.natLt regT1 regLeft regRight) := by
    have h := hguard 2 (by simp)
    simpa [guardBlock] using h
  have hf3 : program[3]? = some (.natLe regT2 regRight regN) := by
    have h := hguard 3 (by simp)
    simpa [guardBlock] using h
  have hf4 : program[4]? = some (.natEq regG regT1 regZero) := by
    have h := hguard 4 (by simp)
    simpa [guardBlock] using h
  have hf5 : program[5]? = some (.brNZ regG invalidBase) := by
    have h := hguard 5 (by simp)
    simpa [guardBlock] using h
  have he0 : program[invalidBase]? = some (.const regOut 0) := by
    have h := hexit 0 (by simp)
    simpa [invalidExitBlock] using h
  have he1 : program[invalidBase + 1]? = some .halt := by
    have h := hexit 1 (by simp)
    simpa [invalidExitBlock] using h
  have h0 : RunsTo store program (initialState left right)
      ⟨(initialRegs left right).write regZero 0, 1, false⟩
      [] [.registerWrite] :=
    RunsTo.const rfl hf0
  have h1 : RunsTo store program
      ⟨(initialRegs left right).write regZero 0, 1, false⟩
      ⟨((initialRegs left right).write regZero 0).write regN n, 2, false⟩
      [] [.registerWrite] :=
    RunsTo.const rfl hf1
  have h2 : RunsTo store program
      ⟨((initialRegs left right).write regZero 0).write regN n, 2, false⟩
      ⟨(((initialRegs left right).write regZero 0).write regN n).write regT1
          (if left < right then 1 else 0), 3, false⟩
      [] [.comparison] :=
    RunsTo.natLt (dst := regT1) (src₁ := regLeft) (src₂ := regRight) rfl hf2
  rw [if_neg hnot] at h2
  have h3 : RunsTo store program
      ⟨(((initialRegs left right).write regZero 0).write regN n).write regT1
          0, 3, false⟩
      ⟨((((initialRegs left right).write regZero 0).write regN n).write regT1
          0).write regT2 (if right ≤ n then 1 else 0), 4, false⟩
      [] [.comparison] :=
    RunsTo.natLe (dst := regT2) (src₁ := regRight) (src₂ := regN) rfl hf3
  have h4 : RunsTo store program
      ⟨((((initialRegs left right).write regZero 0).write regN n).write regT1
          0).write regT2 (if right ≤ n then 1 else 0), 4, false⟩
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 0).write regT2 (if right ≤ n then 1 else 0)).write regG 1,
        5, false⟩
      [] [.comparison] :=
    RunsTo.natEq (dst := regG) (src₁ := regT1) (src₂ := regZero) rfl hf4
  have h5 : RunsTo store program
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 0).write regT2 (if right ≤ n then 1 else 0)).write regG 1,
        5, false⟩
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 0).write regT2 (if right ≤ n then 1 else 0)).write regG 1,
        invalidBase, false⟩
      [] [.branch] :=
    RunsTo.brNZ (cond := regG) (target := invalidBase) rfl hf5
  have h6 : RunsTo store program
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 0).write regT2 (if right ≤ n then 1 else 0)).write regG 1,
        invalidBase, false⟩
      ⟨((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 0).write regT2 (if right ≤ n then 1 else 0)).write regG
          1).write regOut 0,
        invalidBase + 1, false⟩
      [] [.registerWrite] :=
    RunsTo.const rfl he0
  have h7 : RunsTo store program
      ⟨((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 0).write regT2 (if right ≤ n then 1 else 0)).write regG
          1).write regOut 0,
        invalidBase + 1, false⟩
      ⟨((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 0).write regT2 (if right ≤ n then 1 else 0)).write regG
          1).write regOut 0,
        invalidBase + 1, true⟩
      [] [.control] :=
    RunsTo.halt rfl he1
  have hall := ((((((h0.trans h1).trans h2).trans h3).trans h4).trans
    h5).trans h6).trans h7
  exact ⟨_, hall, rfl, rfl⟩

/--
Guard rejection, out-of-bounds ranges: `left < right` but `right` exceeds
the size constant `n`.  Both guard branches execute; the receipt log is
empty and the category log is exactly `guardRejectBoundsCats`.
-/
theorem guard_reject_of_out_of_bounds
    (store : ReadStore) {program : E1Machine.Program} {n invalidBase : Nat}
    (hguard : HostedAt program 0 (guardBlock n invalidBase))
    (hexit : HostedAt program invalidBase invalidExitBlock)
    {left right : Nat} (hlt : left < right) (hbound : ¬ right ≤ n) :
    ∃ final : State,
      RunsTo store program (initialState left right) final []
          guardRejectBoundsCats ∧
        final.halted = true ∧ final.regs regOut = 0 := by
  have hf0 : program[0]? = some (.const regZero 0) := by
    have h := hguard 0 (by simp)
    simpa [guardBlock] using h
  have hf1 : program[1]? = some (.const regN n) := by
    have h := hguard 1 (by simp)
    simpa [guardBlock] using h
  have hf2 : program[2]? = some (.natLt regT1 regLeft regRight) := by
    have h := hguard 2 (by simp)
    simpa [guardBlock] using h
  have hf3 : program[3]? = some (.natLe regT2 regRight regN) := by
    have h := hguard 3 (by simp)
    simpa [guardBlock] using h
  have hf4 : program[4]? = some (.natEq regG regT1 regZero) := by
    have h := hguard 4 (by simp)
    simpa [guardBlock] using h
  have hf5 : program[5]? = some (.brNZ regG invalidBase) := by
    have h := hguard 5 (by simp)
    simpa [guardBlock] using h
  have hf6 : program[6]? = some (.natEq regG regT2 regZero) := by
    have h := hguard 6 (by simp)
    simpa [guardBlock] using h
  have hf7 : program[7]? = some (.brNZ regG invalidBase) := by
    have h := hguard 7 (by simp)
    simpa [guardBlock] using h
  have he0 : program[invalidBase]? = some (.const regOut 0) := by
    have h := hexit 0 (by simp)
    simpa [invalidExitBlock] using h
  have he1 : program[invalidBase + 1]? = some .halt := by
    have h := hexit 1 (by simp)
    simpa [invalidExitBlock] using h
  have h0 : RunsTo store program (initialState left right)
      ⟨(initialRegs left right).write regZero 0, 1, false⟩
      [] [.registerWrite] :=
    RunsTo.const rfl hf0
  have h1 : RunsTo store program
      ⟨(initialRegs left right).write regZero 0, 1, false⟩
      ⟨((initialRegs left right).write regZero 0).write regN n, 2, false⟩
      [] [.registerWrite] :=
    RunsTo.const rfl hf1
  have h2 : RunsTo store program
      ⟨((initialRegs left right).write regZero 0).write regN n, 2, false⟩
      ⟨(((initialRegs left right).write regZero 0).write regN n).write regT1
          (if left < right then 1 else 0), 3, false⟩
      [] [.comparison] :=
    RunsTo.natLt (dst := regT1) (src₁ := regLeft) (src₂ := regRight) rfl hf2
  rw [if_pos hlt] at h2
  have h3 : RunsTo store program
      ⟨(((initialRegs left right).write regZero 0).write regN n).write regT1
          1, 3, false⟩
      ⟨((((initialRegs left right).write regZero 0).write regN n).write regT1
          1).write regT2 (if right ≤ n then 1 else 0), 4, false⟩
      [] [.comparison] :=
    RunsTo.natLe (dst := regT2) (src₁ := regRight) (src₂ := regN) rfl hf3
  rw [if_neg hbound] at h3
  have h4 : RunsTo store program
      ⟨((((initialRegs left right).write regZero 0).write regN n).write regT1
          1).write regT2 0, 4, false⟩
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0, 5, false⟩
      [] [.comparison] :=
    RunsTo.natEq (dst := regG) (src₁ := regT1) (src₂ := regZero) rfl hf4
  have h5 : RunsTo store program
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0, 5, false⟩
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0, 6, false⟩
      [] [.branch] :=
    RunsTo.brNZ (cond := regG) (target := invalidBase) rfl hf5
  have h6 : RunsTo store program
      ⟨(((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0, 6, false⟩
      ⟨((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0).write regG 1, 7, false⟩
      [] [.comparison] :=
    RunsTo.natEq (dst := regG) (src₁ := regT2) (src₂ := regZero) rfl hf6
  have h7 : RunsTo store program
      ⟨((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0).write regG 1, 7, false⟩
      ⟨((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0).write regG 1,
        invalidBase, false⟩
      [] [.branch] :=
    RunsTo.brNZ (cond := regG) (target := invalidBase) rfl hf7
  have h8 : RunsTo store program
      ⟨((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0).write regG 1,
        invalidBase, false⟩
      ⟨(((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0).write regG 1).write regOut 0,
        invalidBase + 1, false⟩
      [] [.registerWrite] :=
    RunsTo.const rfl he0
  have h9 : RunsTo store program
      ⟨(((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0).write regG 1).write regOut 0,
        invalidBase + 1, false⟩
      ⟨(((((((initialRegs left right).write regZero 0).write regN n).write
          regT1 1).write regT2 0).write regG 0).write regG 1).write regOut 0,
        invalidBase + 1, true⟩
      [] [.control] :=
    RunsTo.halt rfl he1
  have hall := ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans
    h5).trans h6).trans h7).trans h8).trans h9
  exact ⟨_, hall, rfl, rfl⟩

/--
Combined charged invalid rejection: whenever the query range fails the
route's validity test against the size constant `n`, the hosted guard runs
the machine to a halted `none`-packet state with an EMPTY receipt log, a
zero memory-read category count, and at most ten charged bookkeeping steps.
-/
theorem guard_reject_of_invalid
    (store : ReadStore) {program : E1Machine.Program} {n invalidBase : Nat}
    (hguard : HostedAt program 0 (guardBlock n invalidBase))
    (hexit : HostedAt program invalidBase invalidExitBlock)
    {left right : Nat} (hbad : ¬ (left < right ∧ right ≤ n)) :
    ∃ (final : State) (cats : List Category),
      RunsTo store program (initialState left right) final [] cats ∧
        final.halted = true ∧ final.regs regOut = 0 ∧
        catCount cats .memoryRead = 0 ∧ cats.length ≤ 10 := by
  by_cases hlt : left < right
  · have hbound : ¬ right ≤ n := fun h => hbad ⟨hlt, h⟩
    obtain ⟨final, hrun, hhalted, hout⟩ :=
      guard_reject_of_out_of_bounds store hguard hexit hlt hbound
    exact ⟨final, guardRejectBoundsCats, hrun, hhalted, hout, rfl,
      by decide⟩
  · obtain ⟨final, hrun, hhalted, hout⟩ :=
      guard_reject_of_not_lt store hguard hexit hlt
    exact ⟨final, guardRejectRangeCats, hrun, hhalted, hout, rfl,
      by decide⟩

/-- Invalid rejection specialized to the concrete program skeleton. -/
theorem programSkeleton_reject_of_invalid
    (store : ReadStore) (n : Nat) (validPath : List Instr)
    {left right : Nat} (hbad : ¬ (left < right ∧ right ≤ n)) :
    ∃ (final : State) (cats : List Category),
      RunsTo store (programSkeleton n validPath)
          (initialState left right) final [] cats ∧
        final.halted = true ∧ final.regs regOut = 0 ∧
        catCount cats .memoryRead = 0 ∧ cats.length ≤ 10 :=
  guard_reject_of_invalid store
    (programSkeleton_hosts_guardBlock n validPath)
    (programSkeleton_hosts_invalidExit n validPath) hbad

/-! ## Invalid-guard fixtures (kernel-checked machine executions)

Deterministic guarded runs of the concrete skeleton (with an empty valid
path) on the empty-, reversed-, and out-of-bounds fixtures the matrix
names: the machine halts with the `none` packet, performs no read, and
charges exactly the frozen guard step counts.
-/

/-- Fixture store with no payload words: the guard never reads, so no
fixture below can be satisfied by store contents. -/
def emptyFixtureStore : ReadStore := ⟨fun _ _ => none⟩

/- Empty input, empty range `[0, 0)`. -/
example :
    (run emptyFixtureStore (programSkeleton 0 []) 10
        (initialState 0 0)).final.regs regOut = 0 := rfl

example :
    (run emptyFixtureStore (programSkeleton 0 []) 10
        (initialState 0 0)).final.halted = true := rfl

example :
    (run emptyFixtureStore (programSkeleton 0 []) 10
        (initialState 0 0)).readLog = [] := rfl

example :
    (run emptyFixtureStore (programSkeleton 0 []) 10
        (initialState 0 0)).steps = 8 := rfl

/- Reversed range `[3, 2)` on a size-5 skeleton. -/
example :
    (run emptyFixtureStore (programSkeleton 5 []) 10
        (initialState 3 2)).final.regs regOut = 0 := rfl

example :
    (run emptyFixtureStore (programSkeleton 5 []) 10
        (initialState 3 2)).readLog = [] := rfl

example :
    (run emptyFixtureStore (programSkeleton 5 []) 10
        (initialState 3 2)).catLog = guardRejectRangeCats := rfl

/- Out-of-bounds range `[0, 9)` on a size-5 skeleton: both guard branches
execute. -/
example :
    (run emptyFixtureStore (programSkeleton 5 []) 12
        (initialState 0 9)).final.regs regOut = 0 := rfl

example :
    (run emptyFixtureStore (programSkeleton 5 []) 12
        (initialState 0 9)).readLog = [] := rfl

example :
    (run emptyFixtureStore (programSkeleton 5 []) 12
        (initialState 0 9)).steps = 10 := rfl

example :
    (run emptyFixtureStore (programSkeleton 5 []) 12
        (initialState 0 9)).catLog = guardRejectBoundsCats := rfl

end E1Query
end WordRAM
end RMQ
