import RMQ.Core.WordRAM.E1FringeFoldBlock

/-!
# E1 amended machine: the fringe arm prologue (M3d-2, steps 1 and 2)

The two pieces that stand between `E1FringeFoldBlock`'s fold simulation and
a whole fringe arm:

* the WINDOW-READ sub-block — four charged payload reads at global segment
  `0` producing the four window registers `fW0..fW3` in exactly the
  `windowRegsValue` Horner form the fold consumes, positionally matching
  `localBPBlockWordsTraceResultWithStore`
  (`ConcreteDirectoryRAMStoreParam.lean:4071`);
* the 33-CAP INIT — the fold's iteration count is literally
  `Nat.min (relHi / c + 1) 33` (`ChargedFringeTrace.lean:722`/`:743`), and
  the machine derives it by the same truncated-subtraction cap chain
  `rankAtInit` uses for its 8-cap (`E1RankAtBlock.lean:56-62`), never by an
  asserted numeral.

Both are straight-line, so both are single `RunsTo.straight` applications;
the work is in the receipt and value bridges to the route objects.

The prologue's exit registers are exactly the fold's entry hypotheses, so
`fringeArmPrologue_runsTo` composes directly with
`fringeFoldLoop_runsTo_accepted` (`E1FringeFoldBlock.lean:1301`).
-/

namespace RMQ
namespace WordRAM
namespace E1FringeArmBlock

open E1Machine
open E1FringeFoldBlock
open RMQ.SuccinctClose
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-! ## Register bank extension (fringe arm, `63`) -/

/-- Window base word index (the first of the four payload words). -/
abbrev fBase : Nat := 63

/-! ## Store-side window bits

The bits the four charged reads actually deliver, as a function of the
store alone.  `readBits` is the machine's view of one payload word: a
missing word contributes no bits, exactly as `readStorePayloadWordValue`
contributes no list element.
-/

/-- Bits of one payload word at global segment `0`, `[]` when absent. -/
def readBits (store : ReadStore) (index : Nat) : List Bool :=
  (store.readWord? 0 index).getD []

/-- The four-word window the machine reads, as a function of the store. -/
def windowBitsOfStore (store : ReadStore) (base : Nat) : List Bool :=
  readBits store base ++ readBits store (base + 1) ++
    readBits store (base + 2) ++ readBits store (base + 3)

/-- The machine's decoded window register value at one word. -/
theorem readBits_decode (store : ReadStore) (index : Nat) :
    ((store.readWord? 0 index).map SuccinctSpace.bitsToNatLE).getD 0 =
      SuccinctSpace.bitsToNatLE (readBits store index) := by
  unfold readBits
  cases h : store.readWord? 0 index
  · rfl
  · rfl

/-- Flattening one payload-word read value gives that word's bits. -/
theorem flatten_readStorePayloadWordValue (store : ReadStore) (index : Nat) :
    SuccinctSpace.flattenPayloadWords
        (readStorePayloadWordValue store 0 index) =
      readBits store index := by
  unfold readStorePayloadWordValue readBits
  cases h : store.readWord? 0 index
  · rfl
  · rename_i w
    show SuccinctSpace.flattenPayloadWords [w] = w
    simp [SuccinctSpace.flattenPayloadWords]

/-! ## The window-read sub-block -/

/--
The window-read sub-block: four charged payload reads at global segment
`0`, indices `base .. base + 3`, each decoded out of the option-shift
convention (`decodeRead - 1`) into its window register.

Eleven instructions, exactly FOUR memory reads — one per payload word, no
multi-read composite.
-/
def fringeWindowRead : List Instr :=
  [ .readMem fW0 0 fBase
  , .sub fW0 fW0 fOne
  , .add fT fBase fOne
  , .readMem fW1 0 fT
  , .sub fW1 fW1 fOne
  , .add fT fT fOne
  , .readMem fW2 0 fT
  , .sub fW2 fW2 fOne
  , .add fT fT fOne
  , .readMem fW3 0 fT
  , .sub fW3 fW3 fOne ]

@[simp] theorem fringeWindowRead_length :
    fringeWindowRead.length = 11 := rfl

/-! ## The 33-cap fold init

`fCnt := Nat.min (relHi / c + 1) 33`, derived by the truncated-subtraction
cap chain `x - (x - 33)`.  The cap `33` is the route's literal
(`ChargedFringeTrace.lean:722`/`:743`); the machine never asserts the
resulting count, it computes it.
-/

/--
Fold init at chunk width `c`: pin the constants, zero the chunk cursor and
the option-shifted best pair, and derive the 33-capped chunk count from
the relative high endpoint already in `fHi`.
-/
def fringeArmInit (c : Nat) : List Instr :=
  [ .const fOne 1
  , .const fC c
  , .const fJC 0
  , .const fBV 0
  , .const fBP 0
  , .divConst fT fHi c
  , .add fCnt fT fOne
  , .const fU 33
  , .sub fT fCnt fU
  , .sub fCnt fCnt fT ]

@[simp] theorem fringeArmInit_length (c : Nat) :
    (fringeArmInit c).length = 10 := rfl

/-- The full 21-instruction fringe arm prologue. -/
def fringeArmPrologue (c : Nat) : List Instr :=
  fringeArmInit c ++ fringeWindowRead

@[simp] theorem fringeArmPrologue_length (c : Nat) :
    (fringeArmPrologue c).length = 21 := rfl

/-! ## Frozen category logs -/

/-- Categories charged by the fold init. -/
def fringeArmInitCats : List Category :=
  (fringeArmInit 0).map Instr.category

@[simp] theorem fringeArmInitCats_length :
    fringeArmInitCats.length = 10 := rfl

/-- Categories charged by the window-read sub-block. -/
def fringeWindowReadCats : List Category :=
  fringeWindowRead.map Instr.category

@[simp] theorem fringeWindowReadCats_length :
    fringeWindowReadCats.length = 11 := rfl

/-- Categories charged by the whole prologue. -/
def fringeArmPrologueCats : List Category :=
  fringeArmInitCats ++ fringeWindowReadCats

@[simp] theorem fringeArmPrologueCats_length :
    fringeArmPrologueCats.length = 21 := rfl

/-- The init's category log does not depend on the chunk width. -/
theorem fringeArmInit_cats (c : Nat) :
    (fringeArmInit c).map Instr.category = fringeArmInitCats := rfl

theorem fringeWindowRead_cats :
    fringeWindowRead.map Instr.category = fringeWindowReadCats := rfl

/-- Exactly four of the prologue's charged steps are memory reads. -/
theorem fringeArmPrologueCats_memoryRead_count :
    (fringeArmPrologueCats.filter (· == Category.memoryRead)).length = 4 :=
  rfl

/-! ## Straightness certificates -/

theorem fringeWindowRead_straight :
    forall instr, instr ∈ fringeWindowRead -> instr.isStraight = true := by
  intro instr hi
  simp only [fringeWindowRead, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl <;> rfl

theorem fringeArmInit_straight (c : Nat) :
    forall instr, instr ∈ fringeArmInit c -> instr.isStraight = true := by
  intro instr hi
  simp only [fringeArmInit, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl <;> rfl

theorem fringeArmPrologue_straight (c : Nat) :
    forall instr, instr ∈ fringeArmPrologue c ->
      instr.isStraight = true := by
  intro instr hi
  rw [fringeArmPrologue, List.mem_append] at hi
  rcases hi with hi | hi
  · exact fringeArmInit_straight c instr hi
  · exact fringeWindowRead_straight instr hi

/-! ## Width certificate -/

/--
Constructor-exhaustive width certificate for the prologue: every encoded
field of every one of the 21 instructions fits the modeled word width.
No wildcard arm — `Instr.FieldsFit` matches on every constructor.
-/
theorem fringeArmPrologue_fits {c w : Nat}
    (hreg : 64 ≤ 2 ^ w) (hcpos : 0 < c) (hc : c < 2 ^ w) :
    ∀ instr ∈ fringeArmPrologue c, instr.FieldsFit w := by
  intro instr hmem
  simp only [fringeArmPrologue, fringeArmInit, fringeWindowRead,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl <;>
    simp only [Instr.FieldsFit, fOne, fC, fW0, fW1, fW2, fW3, fBV, fBP,
      fJC, fHi, fCnt, fT, fU, fBase] <;>
    omega

/-! ## Shared symbolic-evaluation macros (module-local instances) -/

local macro "arm_eval" : tactic =>
  `(tactic| straight_eval [fringeArmInit, fringeWindowRead,
      fOne, fC, fW0, fW1, fW2, fW3, fAcc, fBV, fBP, fJC, fLo, fHi, fCnt,
      fV, fA, fB, fSlot, fE, fCV, fCP, fT, fU, fX, fBase])

local macro "arm_writes" : tactic =>
  `(tactic| straight_writes [fOne, fC, fW0, fW1, fW2, fW3, fAcc, fBV, fBP,
      fJC, fLo, fHi, fCnt, fV, fA, fB, fSlot, fE, fCV, fCP, fT, fU, fX,
      fBase])

/-! ## The cap identity -/

/-- The truncated-subtraction cap chain computes `Nat.min`. -/
theorem cap_chain_eq_min (x k : Nat) : x - (x - k) = Nat.min x k := by
  show x - (x - k) = min x k
  omega

/-- The 33-capped chunk count is always positive, so the fold always runs
at least one pass (this is the fold block's `hcount` hypothesis). -/
theorem cap_count_pos (relHi c : Nat) :
    0 < Nat.min (relHi / c + 1) 33 := by
  show 0 < min (relHi / c + 1) 33
  generalize relHi / c = q
  omega

/-! ## Window-read simulation -/

/-- The window read writes only the four window registers and `fT`. -/
abbrev FringeWindowReadUntouched (r : Nat) : Prop :=
  r ≠ 42 ∧ r ≠ 43 ∧ r ≠ 44 ∧ r ≠ 45 ∧ r ≠ 60

/-- The literal four-event receipt of the window read at base `base`. -/
def windowReadEvents (store : ReadStore) (base : Nat) : List TraceEvent :=
  [ TraceEvent.readWord 0 base (store.readWord? 0 base)
  , TraceEvent.readWord 0 (base + 1) (store.readWord? 0 (base + 1))
  , TraceEvent.readWord 0 (base + 2) (store.readWord? 0 (base + 2))
  , TraceEvent.readWord 0 (base + 3) (store.readWord? 0 (base + 3)) ]

/--
Exact simulation of the window-read sub-block: from a register file with
the pinned `fOne` and the window base in `fBase`, the hosted sub-block runs
to `A + 11` emitting exactly the four ascending payload reads and leaving
the four decoded window words in `fW0..fW3`.
-/
theorem fringeWindowRead_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A : Nat}
    (hHost : HostedAt program A fringeWindowRead)
    (base : Nat) (regs : RegFile)
    (hOne : regs fOne = 1) (hBase : regs fBase = base) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, A, false⟩ ⟨regs', A + 11, false⟩
        (windowReadEvents store base) fringeWindowReadCats ∧
      regs' fW0 = SuccinctSpace.bitsToNatLE (readBits store base) ∧
      regs' fW1 = SuccinctSpace.bitsToNatLE (readBits store (base + 1)) ∧
      regs' fW2 = SuccinctSpace.bitsToNatLE (readBits store (base + 2)) ∧
      regs' fW3 = SuccinctSpace.bitsToNatLE (readBits store (base + 3)) ∧
      (∀ r, FringeWindowReadUntouched r -> regs' r = regs r) := by
  have hrun := RunsTo.straight store fringeWindowRead
    fringeWindowRead_straight A hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store fringeWindowRead regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store fringeWindowRead regs =
      windowReadEvents store base := by
    arm_eval <;> simp [hOne, hBase, windowReadEvents]
  rw [hreads, fringeWindowRead_cats] at hrun
  refine ⟨regsW, hrun, ?_, ?_, ?_, ?_, ?_⟩
  · rw [<- hregsW, <- readBits_decode]
    arm_eval <;> simp [hOne, hBase, decodeRead_pred_eq_map_getD]
  · rw [<- hregsW, <- readBits_decode]
    arm_eval <;> simp [hOne, hBase, decodeRead_pred_eq_map_getD]
  · rw [<- hregsW, <- readBits_decode]
    arm_eval <;> simp [hOne, hBase, decodeRead_pred_eq_map_getD]
  · rw [<- hregsW, <- readBits_decode]
    arm_eval <;> simp [hOne, hBase, decodeRead_pred_eq_map_getD]
  · intro r hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [fringeWindowRead, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl <;>
      arm_writes <;> omega

/-! ## Init simulation -/

/-- The init writes only the pinned constants, the zeroed fold registers,
the counter and the scratch registers. -/
abbrev FringeArmInitUntouched (r : Nat) : Prop :=
  r ≠ 40 ∧ r ≠ 41 ∧ r ≠ 47 ∧ r ≠ 48 ∧ r ≠ 49 ∧ r ≠ 52 ∧ r ≠ 60 ∧ r ≠ 61

/--
Exact simulation of the 33-cap fold init: from a register file holding the
relative high endpoint in `fHi`, the hosted init runs to `A + 10` with no
memory reads, pinning the constants, zeroing the cursor and the
option-shifted best pair, and leaving the DERIVED 33-capped chunk count
`Nat.min (relHi / c + 1) 33` in `fCnt`.
-/
theorem fringeArmInit_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A c : Nat}
    (hHost : HostedAt program A (fringeArmInit c))
    (relHi : Nat) (regs : RegFile) (hHi : regs fHi = relHi) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, A, false⟩ ⟨regs', A + 10, false⟩
        [] fringeArmInitCats ∧
      regs' fOne = 1 ∧ regs' fC = c ∧ regs' fJC = 0 ∧
      regs' fBV = 0 ∧ regs' fBP = 0 ∧
      regs' fCnt = Nat.min (relHi / c + 1) 33 ∧
      (∀ r, FringeArmInitUntouched r -> regs' r = regs r) := by
  have hrun := RunsTo.straight store (fringeArmInit c)
    (fringeArmInit_straight c) A hHost regs
  obtain ⟨regsI, hregsI⟩ :
      ∃ x, straightRegs store (fringeArmInit c) regs = x := ⟨_, rfl⟩
  rw [hregsI] at hrun
  have hreads : straightReads store (fringeArmInit c) regs = [] := by
    arm_eval <;> simp
  rw [hreads, fringeArmInit_cats] at hrun
  refine ⟨regsI, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [<- hregsI]; arm_eval <;> simp
  · rw [<- hregsI]; arm_eval <;> simp
  · rw [<- hregsI]; arm_eval <;> simp
  · rw [<- hregsI]; arm_eval <;> simp
  · rw [<- hregsI]; arm_eval <;> simp
  · rw [<- hregsI, <- cap_chain_eq_min]
    arm_eval <;> simp [hHi]
  · intro r hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
    rw [<- hregsI]
    apply straightRegs_preserves
    intro i hi
    simp only [fringeArmInit, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl <;>
      arm_writes <;> omega

end E1FringeArmBlock
end WordRAM
end RMQ
