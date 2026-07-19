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


/-! ## Bridges to the accepted route objects

The machine's window base is a WORD index; the route's `localBPWindowBase`
(`LocalBPDecoder.lean:205`) is the corresponding BIT base, i.e. this word
index times the word width.
-/

/-- The first of the four payload words covering a local BP block. -/
def bpWindowFirstWord (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Nat :=
  blockStartOf blockSize (blockOfClose blockSize close) /
    SuccinctRank.machineWordBits shape.bpCode.length

/-- The route's bit-level window base is the machine's word index scaled
by the word width. -/
theorem localBPWindowBase_eq (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    localBPWindowBase shape blockSize close =
      bpWindowFirstWord shape blockSize close *
        SuccinctRank.machineWordBits shape.bpCode.length := rfl

/--
RECEIPT BRIDGE.  The window-read sub-block's four-event log is
POSITIONALLY equal — a `List` equality, not a multiset or membership
claim — to the accepted store-parameterized four-word BP block read
`localBPBlockWordsTraceResultWithStore`
(`ConcreteDirectoryRAMStoreParam.lean:4071`).
-/
theorem windowReadEvents_eq_route
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (blockSize close : Nat) :
    windowReadEvents store (bpWindowFirstWord shape blockSize close) =
      (localBPBlockWordsTraceResultWithStore shape store blockSize
        close).trace := by
  unfold windowReadEvents localBPBlockWordsTraceResultWithStore
    bpCodeWordReadTraceResultWithStore bpWindowFirstWord
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]

/-- The same receipt bridge against the flattened window-bits object. -/
theorem windowReadEvents_eq_route_windowBits
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (blockSize close : Nat) :
    windowReadEvents store (bpWindowFirstWord shape blockSize close) =
      (localBPWindowBitsTraceResultWithStore shape store blockSize
        close).trace := by
  rw [windowReadEvents_eq_route shape store blockSize close]
  unfold localBPWindowBitsTraceResultWithStore
  simp [WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.pure]

/--
VALUE BRIDGE.  The window bits the accepted route object delivers are
exactly the concatenation of the four payload words the machine's four
charged reads return — so the fold's `window` argument is recovered from
the machine's own reads, not copied from the spec.
-/
theorem route_windowBits_eq_windowBitsOfStore
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (blockSize close : Nat) :
    (localBPWindowBitsTraceResultWithStore shape store blockSize
        close).value =
      windowBitsOfStore store (bpWindowFirstWord shape blockSize close) := by
  unfold localBPWindowBitsTraceResultWithStore
    localBPBlockWordsTraceResultWithStore bpCodeWordReadTraceResultWithStore
    windowBitsOfStore bpWindowFirstWord
  simp only [WordRAM.TraceResult.map, WordRAM.TraceResult.bind,
    WordRAM.TraceResult.pure, SuccinctSpace.flattenPayloadWords_append,
    flatten_readStorePayloadWordValue]

/--
HORNER BRIDGE.  Given the route-side fact that the first three window
words are full width, the machine's four window registers represent
exactly the window the fold consumes.  This is the hypothesis
`fringeFoldLoop_runsTo_accepted` takes as `hW`, and the discipline is the
one the dense select leg uses for `hlen`: the length facts are route-side
properties of `chunkPayloadWords`, discharged at canonical instantiation.
-/
theorem windowRegsValue_of_readBits {L : Nat} (store : ReadStore)
    (base : Nat)
    (h0 : (readBits store base).length = L)
    (h1 : (readBits store (base + 1)).length = L)
    (h2 : (readBits store (base + 2)).length = L) :
    windowRegsValue L
        (SuccinctSpace.bitsToNatLE (readBits store base))
        (SuccinctSpace.bitsToNatLE (readBits store (base + 1)))
        (SuccinctSpace.bitsToNatLE (readBits store (base + 2)))
        (SuccinctSpace.bitsToNatLE (readBits store (base + 3))) =
      SuccinctSpace.bitsToNatLE (windowBitsOfStore store base) := by
  unfold windowBitsOfStore
  exact (windowRegsValue_eq_bitsToNatLE h0 h1 h2).symm

/-! ## Prologue composition -/

/-- The prologue writes only the pinned constants, the window registers,
the zeroed fold registers, the counter and the scratch registers.  In
particular it preserves `fLo`, `fHi`, `fAcc` and `fBase`. -/
abbrev FringeArmPrologueUntouched (r : Nat) : Prop :=
  r ≠ 40 ∧ r ≠ 41 ∧ r ≠ 42 ∧ r ≠ 43 ∧ r ≠ 44 ∧ r ≠ 45 ∧ r ≠ 47 ∧
    r ≠ 48 ∧ r ≠ 49 ∧ r ≠ 52 ∧ r ≠ 60 ∧ r ≠ 61

/--
Exact simulation of the whole 21-instruction fringe arm prologue: the
33-cap init followed by the window read.  The exit register file is
precisely the fold's entry configuration — pinned constants, zeroed cursor
and best pair, the DERIVED capped count, and the four window registers —
and the receipt is exactly the four window reads.
-/
theorem fringeArmPrologue_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A c : Nat}
    (hHost : HostedAt program A (fringeArmPrologue c))
    (base relHi : Nat) (regs : RegFile)
    (hBase : regs fBase = base) (hHi : regs fHi = relHi) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, A, false⟩ ⟨regs', A + 21, false⟩
        (windowReadEvents store base) fringeArmPrologueCats ∧
      regs' fOne = 1 ∧ regs' fC = c ∧ regs' fJC = 0 ∧
      regs' fBV = 0 ∧ regs' fBP = 0 ∧
      regs' fCnt = Nat.min (relHi / c + 1) 33 ∧
      regs' fW0 = SuccinctSpace.bitsToNatLE (readBits store base) ∧
      regs' fW1 = SuccinctSpace.bitsToNatLE (readBits store (base + 1)) ∧
      regs' fW2 = SuccinctSpace.bitsToNatLE (readBits store (base + 2)) ∧
      regs' fW3 = SuccinctSpace.bitsToNatLE (readBits store (base + 3)) ∧
      (∀ r, FringeArmPrologueUntouched r -> regs' r = regs r) := by
  have hInitHost : HostedAt program A (fringeArmInit c) :=
    HostedAt.append_left hHost
  have hReadHost : HostedAt program (A + 10) fringeWindowRead := by
    have := HostedAt.append_right (code₁ := fringeArmInit c)
      (code₂ := fringeWindowRead) hHost
    simpa using this
  obtain ⟨regsI, hrunI, hOne, hC, hJC, hBV, hBP, hCnt, hpresI⟩ :=
    fringeArmInit_runsTo store hInitHost relHi regs hHi
  have hBaseI : regsI fBase = base := by
    rw [hpresI fBase (by decide), hBase]
  obtain ⟨regsW, hrunW, hW0, hW1, hW2, hW3, hpresW⟩ :=
    fringeWindowRead_runsTo store hReadHost base regsI hOne hBaseI
  have htrans := RunsTo.trans hrunI hrunW
  have hpc : A + 10 + 11 = A + 21 := by omega
  rw [hpc] at htrans
  have hev : ([] : List TraceEvent) ++ windowReadEvents store base =
      windowReadEvents store base := by simp
  rw [hev] at htrans
  refine ⟨regsW, htrans, ?_, ?_, ?_, ?_, ?_, ?_, hW0, hW1, hW2, hW3, ?_⟩
  · rw [hpresW fOne (by decide), hOne]
  · rw [hpresW fC (by decide), hC]
  · rw [hpresW fJC (by decide), hJC]
  · rw [hpresW fBV (by decide), hBV]
  · rw [hpresW fBP (by decide), hBP]
  · rw [hpresW fCnt (by decide), hCnt]
  · intro r hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hr
    rw [hpresW r ⟨h3, h4, h5, h6, h11⟩,
      hpresI r ⟨h1, h2, h7, h8, h9, h10, h11, h12⟩]


/-! ## The fringe leg: prologue then fold

Composing `fringeArmPrologue_runsTo` with
`fringeFoldLoop_runsTo_accepted` (`E1FringeFoldBlock.lean:1301`) gives the
whole read-performing part of a fringe arm.  The remaining route step,
`bpFringeCandGlobal`, is a PURE two-arm option rebase that performs no
memory read, so this theorem's receipt is already the arm's complete
receipt.

Layout: prologue at `A .. A+20`, fold loop base `LB = A + 21`, loop exit
at `A + 88`.
-/

/-- Category log of the whole fringe leg at the derived capped count. -/
def fringeLegCats (store : ReadStore) (S c : Nat) (window : List Bool)
    (relLo relHi seed count : Nat) : List Category :=
  fringeArmPrologueCats ++
    fringeFoldCats store S c window relLo relHi seed count

/--
Exact simulation of a whole fringe leg: the 21-instruction prologue (four
charged window reads plus the derived 33-cap) followed by the charged
chunk fold.

The receipt is the four window reads followed POSITIONALLY by the accepted
fold object's own trace; the fold's value is recovered from the machine's
registers `fAcc` and the option-shifted pair `fBV`/`fBP`.  The iteration
count is the DERIVED `Nat.min (relHi / c + 1) 33`, never an asserted
numeral.
-/
theorem fringeLeg_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A S c L : Nat}
    (hc : c ≤ L)
    (hPro : HostedAt program A (fringeArmPrologue c))
    (hPre : HostedAt program (A + 21) (fringePrefix S c))
    (hMrg : HostedAt program (A + 21 + 32) (fringeMerge (A + 21)))
    (hTail : HostedAt program (A + 21 + 45)
      (fringeShift c L ++ fringeAdvance))
    (hbr : program[A + 21 + 66]? = some (.brNZ fCnt (A + 21)))
    (base relLo relHi seed : Nat)
    (h0 : (readBits store base).length = L)
    (h1 : (readBits store (base + 1)).length = L)
    (h2 : (readBits store (base + 2)).length = L)
    (regs : RegFile)
    (hBase : regs fBase = base) (hLo : regs fLo = relLo)
    (hHi : regs fHi = relHi) (hAcc : regs fAcc = seed) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs, A, false⟩ ⟨regsF, A + 88, false⟩
        (windowReadEvents store base ++
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
            (windowBitsOfStore store base) seed relLo relHi
            (Nat.min (relHi / c + 1) 33)).trace)
        (fringeLegCats store S c (windowBitsOfStore store base)
          relLo relHi seed (Nat.min (relHi / c + 1) 33)) ∧
      (regsF fAcc, bestOfRegs (regsF fBV) (regsF fBP)) =
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
          (windowBitsOfStore store base) seed relLo relHi
          (Nat.min (relHi / c + 1) 33)).value ∧
      (∀ r, FringeFoldUntouched r -> regsF r = regs r) := by
  obtain ⟨regsP, hrunP, hOne, hC, hJC, hBV, hBP, hCnt,
      hW0, hW1, hW2, hW3, hpresP⟩ :=
    fringeArmPrologue_runsTo store hPro base relHi regs hBase hHi
  have hLoP : regsP fLo = relLo := by
    rw [hpresP fLo (by decide), hLo]
  have hHiP : regsP fHi = relHi := by
    rw [hpresP fHi (by decide), hHi]
  have hAccP : regsP fAcc = seed := by
    rw [hpresP fAcc (by decide), hAcc]
  have hWin : windowRegsValue L (regsP fW0) (regsP fW1) (regsP fW2)
      (regsP fW3) =
      SuccinctSpace.bitsToNatLE (windowBitsOfStore store base) := by
    rw [hW0, hW1, hW2, hW3]
    exact windowRegsValue_of_readBits store base h0 h1 h2
  obtain ⟨regsF, hrunF, hval, hpresF⟩ :=
    fringeFoldLoop_runsTo_accepted store hc hPre hMrg hTail hbr
      (windowBitsOfStore store base) relLo relHi seed
      (Nat.min (relHi / c + 1) 33) (cap_count_pos relHi c)
      regsP hOne hC hLoP hHiP hJC hCnt hAccP hBV hWin
  have htrans := RunsTo.trans hrunP hrunF
  have hpc : A + 21 + 67 = A + 88 := by omega
  rw [hpc] at htrans
  refine ⟨regsF, htrans, hval, ?_⟩
  intro r hr
  have hpro : FringeArmPrologueUntouched r := by
    simp only [FringeFoldUntouched] at hr
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega
  rw [hpresF r hr, hpresP r hpro]

/-! ## Receipt bridge to the accepted fringe arm objects

The left and right charged chunked fringe arms
(`ChargedFringeTrace.lean:707`/`:730`) are each a `bind` of the window
read into the fold, followed by a PURE `bpFringeCandGlobal` map.  The
machine's leg receipt is therefore positionally equal to the whole arm's
receipt.
-/

/-- The accepted LEFT fringe arm's receipt is the machine leg's receipt. -/
theorem fringeLeg_trace_eq_leftArm
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize leftClose seed : Nat) :
    (bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose seed).trace =
      windowReadEvents store (bpWindowFirstWord shape blockSize leftClose) ++
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store fringeSegment
          (bpFringeChunkBits shape.bpCode.length)
          (windowBitsOfStore store
            (bpWindowFirstWord shape blockSize leftClose))
          seed
          (leftClose + 1 - localBPWindowBase shape blockSize leftClose)
          (leftClose + 1 +
            (blockStartOf blockSize (blockOfClose blockSize leftClose) +
              blockSize - leftClose) - 1 -
            localBPWindowBase shape blockSize leftClose)
          (Nat.min
            ((leftClose + 1 +
              (blockStartOf blockSize (blockOfClose blockSize leftClose) +
                blockSize - leftClose) - 1 -
              localBPWindowBase shape blockSize leftClose) /
              bpFringeChunkBits shape.bpCode.length + 1) 33)).trace := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [windowReadEvents_eq_route_windowBits shape store blockSize leftClose,
    <- route_windowBits_eq_windowBitsOfStore shape store blockSize leftClose]
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]

/-- The accepted RIGHT fringe arm's receipt is the machine leg's receipt. -/
theorem fringeLeg_trace_eq_rightArm
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize rightClose seed : Nat) :
    (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize rightClose seed).trace =
      windowReadEvents store
          (bpWindowFirstWord shape blockSize rightClose) ++
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store fringeSegment
          (bpFringeChunkBits shape.bpCode.length)
          (windowBitsOfStore store
            (bpWindowFirstWord shape blockSize rightClose))
          seed
          (blockStartOf blockSize (blockOfClose blockSize rightClose) -
            localBPWindowBase shape blockSize rightClose)
          (blockStartOf blockSize (blockOfClose blockSize rightClose) +
            (rightClose -
              blockStartOf blockSize (blockOfClose blockSize rightClose) + 2)
            - 1 - localBPWindowBase shape blockSize rightClose)
          (Nat.min
            ((blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) + 2)
              - 1 - localBPWindowBase shape blockSize rightClose) /
              bpFringeChunkBits shape.bpCode.length + 1) 33)).trace := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [windowReadEvents_eq_route_windowBits shape store blockSize rightClose,
    <- route_windowBits_eq_windowBitsOfStore shape store blockSize rightClose]
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]


/-! ## The `bpFringeCandGlobal` epilogue

The last route step of each fringe arm (`ChargedFringeChunks.lean:1617`)
is a PURE two-arm option rebase: an occupied best is rebased to global
coordinates, an empty best falls back to the seed pair.  It performs no
memory read, so the epilogue emits no receipt — but it still costs branch
and arithmetic ticks, which the arm-indexed category log records.

Since `bpFringeCandGlobal` always returns `some`, the machine carries the
result UNSHIFTED in `fRV`/`fRP`.

The epilogue PINS ITS OWN unit constant in the scratch register `fT`
rather than reading `fOne`.  That is deliberate: the fold block's
preservation predicate `FringeFoldUntouched` (`r < 40 ∨ 63 ≤ r`) is
conservative and does not certify `fOne`, so an epilogue depending on
`fOne` would not compose with the fold without strengthening the fold's
certificate.  Pinning locally costs one register write and keeps the
epilogue composable as written.
-/

/-- Window bit base (the route's `localBPWindowBase`). -/
abbrev fBB : Nat := 64
/-- Fallback candidate value (the seed). -/
abbrev fSeed : Nat := 65
/-- Fallback candidate position. -/
abbrev fStart : Nat := 66
/-- Result value. -/
abbrev fRV : Nat := 67
/-- Result position. -/
abbrev fRP : Nat := 68

/--
The global-rebase epilogue at base `E` (seven instructions, exit
`E + 7`): if the fold left an occupied best, unshift it and rebase its
position by the window bit base; otherwise fall back to the seed pair.
-/
def fringeCandGlobal (E : Nat) : List Instr :=
  [ .const fT 1            -- E+0
  , .brNZ fBV (E + 5)      -- E+1
  , .move fRV fSeed        -- E+2
  , .move fRP fStart       -- E+3
  , .brNZ fT (E + 7)       -- E+4
  , .sub fRV fBV fT        -- E+5
  , .add fRP fBB fBP ]     -- E+6

@[simp] theorem fringeCandGlobal_length (E : Nat) :
    (fringeCandGlobal E).length = 7 := rfl

/-- Constructor-exhaustive width certificate for the global-rebase
epilogue.  No wildcard arm: each of the seven instructions discharges its
own constructor's field conjunction from `Instr.FieldsFit`.  The epilogue
carries no divisor, so no positivity arm arises.  Both branch targets are
`E`-relative and so are bounded by the single hypothesis `hE`.

This was the one segment of the same-block leg with no width certificate;
`rankCloseBlock_fits` (`E1RankBlock.lean:1003`), `fringeLoopBody_fits`
(`E1FringeFoldBlock.lean:376`), `fringeArmPrologue_fits` (`:210`),
`windowAddr_fits`, `windowRange_fits`, `sameBlockClose_fits`,
`rankSeedPos_fits` and `rankSeedFinish_fits` already covered the rest. -/
theorem fringeCandGlobal_fits (w E : Nat) (hw : 68 < 2 ^ w)
    (hE : E + 7 < 2 ^ w) :
    ∀ instr ∈ fringeCandGlobal E, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  have h47 : (47 : Nat) < 2 ^ w := by omega
  have h48 : (48 : Nat) < 2 ^ w := by omega
  have h60 : (60 : Nat) < 2 ^ w := by omega
  have h64 : (64 : Nat) < 2 ^ w := by omega
  have h65 : (65 : Nat) < 2 ^ w := by omega
  have h66 : (66 : Nat) < 2 ^ w := by omega
  have h67 : (67 : Nat) < 2 ^ w := by omega
  have h68 : (68 : Nat) < 2 ^ w := hw
  have h5 : E + 5 < 2 ^ w := by omega
  simp only [fringeCandGlobal, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h | h | h | h | h | h <;> subst h
  · exact ⟨h60, h1⟩
  · exact ⟨h47, h5⟩
  · exact ⟨h67, h65⟩
  · exact ⟨h68, h66⟩
  · exact ⟨h60, hE⟩
  · exact ⟨h67, h47, h60⟩
  · exact ⟨h68, h64, h48⟩

/--
Category log of the epilogue, indexed by the route-side condition it
dispatches on (whether the fold left an occupied best).  Never a numeral.
-/
def fringeCandGlobalArmCats (occupied : Bool) : List Category :=
  if occupied then
    [.registerWrite, .branch, .arithmetic, .arithmetic]
  else
    [.registerWrite, .branch, .registerWrite, .registerWrite, .branch]

/-- The epilogue writes only its scratch register and the two result
registers. -/
abbrev FringeCandGlobalUntouched (r : Nat) : Prop :=
  r ≠ 60 ∧ r ≠ 67 ∧ r ≠ 68

/--
Exact simulation of the global-rebase epilogue: no receipt, an
arm-indexed category log, and `some (fRV, fRP)` equal to the route's
`bpFringeCandGlobal` applied to the machine's own option-shifted best.
-/
theorem fringeCandGlobal_runsTo
    (store : ReadStore) {program : E1Machine.Program} {E : Nat}
    (hHost : HostedAt program E (fringeCandGlobal E))
    (regs : RegFile) (bb seed start : Nat)
    (hBB : regs fBB = bb)
    (hSeed : regs fSeed = seed) (hStart : regs fStart = start) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, E, false⟩ ⟨regs', E + 7, false⟩ []
        (fringeCandGlobalArmCats (!(regs fBV == 0))) ∧
      some (regs' fRV, regs' fRP) =
        bpFringeCandGlobal bb seed start
          (bestOfRegs (regs fBV) (regs fBP)) ∧
      (∀ r, FringeCandGlobalUntouched r -> regs' r = regs r) := by
  have hf : forall (k m : Nat) (instr : Instr), k < 7 ->
      (fringeCandGlobal E)[k]? = some instr -> E + k = m ->
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [<- hm, hHost k hk, hget]
  have h0 : program[E]? = some (.const fT 1) :=
    hf 0 E (.const fT 1) (by omega) rfl (by omega)
  have h1 : program[E + 1]? = some (.brNZ fBV (E + 5)) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[E + 2]? = some (.move fRV fSeed) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[E + 3]? = some (.move fRP fStart) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[E + 4]? = some (.brNZ fT (E + 7)) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[E + 5]? = some (.sub fRV fBV fT) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[E + 6]? = some (.add fRP fBB fBP) :=
    hf 6 _ _ (by omega) rfl (by omega)
  -- pin the local unit constant, common to both arms
  have hpin : RunsTo store program ⟨regs, E, false⟩
      ⟨regs.write fT 1, E + 1, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨regs, E, false⟩ : State)) rfl h0
    simpa using h
  by_cases hbv : regs fBV = 0
  · -- empty best: fall back to the seed pair
    have hbr1 : RunsTo store program ⟨regs.write fT 1, E + 1, false⟩
        ⟨regs.write fT 1, E + 2, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_not_taken (store := store)
        (s := (⟨regs.write fT 1, E + 1, false⟩ : State)) rfl h1
        (by simpa [RegFile.write, fT, fBV] using hbv)
      simpa using h
    have hm2 : RunsTo store program ⟨regs.write fT 1, E + 2, false⟩
        ⟨(regs.write fT 1).write fRV seed, E + 3, false⟩ []
        [Category.registerWrite] := by
      have h := RunsTo.move (store := store)
        (s := (⟨regs.write fT 1, E + 2, false⟩ : State)) rfl h2
      simpa [RegFile.write, fT, fSeed, hSeed] using h
    have hm3 : RunsTo store program
        ⟨(regs.write fT 1).write fRV seed, E + 3, false⟩
        ⟨((regs.write fT 1).write fRV seed).write fRP start,
          E + 4, false⟩ [] [Category.registerWrite] := by
      have h := RunsTo.move (store := store)
        (s := (⟨(regs.write fT 1).write fRV seed, E + 3,
          false⟩ : State)) rfl h3
      simpa [RegFile.write, fT, fRV, fStart, hStart] using h
    have hbr4 : RunsTo store program
        ⟨((regs.write fT 1).write fRV seed).write fRP start,
          E + 4, false⟩
        ⟨((regs.write fT 1).write fRV seed).write fRP start,
          E + 7, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken (store := store)
        (s := (⟨((regs.write fT 1).write fRV seed).write fRP start,
          E + 4, false⟩ : State)) rfl h4
        (by simp [RegFile.write, fT, fRV, fRP])
      simpa using h
    refine ⟨((regs.write fT 1).write fRV seed).write fRP start,
      ?_, ?_, ?_⟩
    · have hrun := (((hpin.trans hbr1).trans hm2).trans hm3).trans hbr4
      simpa [fringeCandGlobalArmCats, hbv] using hrun
    · have e1 : (((regs.write fT 1).write fRV seed).write fRP start)
          fRV = seed := by simp [RegFile.write, fRV, fRP]
      have e2 : (((regs.write fT 1).write fRV seed).write fRP start)
          fRP = start := by simp [RegFile.write]
      rw [e1, e2, hbv, bestOfRegs_zero]
      rfl
    · intro r hr
      obtain ⟨hT, hRV, hRP⟩ := hr
      simp [RegFile.write, hT, hRV, hRP]
  · -- occupied best: unshift and rebase
    have hbr1 : RunsTo store program ⟨regs.write fT 1, E + 1, false⟩
        ⟨regs.write fT 1, E + 5, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken (store := store)
        (s := (⟨regs.write fT 1, E + 1, false⟩ : State)) rfl h1
        (by simpa [RegFile.write, fT, fBV] using hbv)
      simpa using h
    have hs5 : RunsTo store program ⟨regs.write fT 1, E + 5, false⟩
        ⟨(regs.write fT 1).write fRV (regs fBV - 1), E + 6, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.sub (store := store)
        (s := (⟨regs.write fT 1, E + 5, false⟩ : State)) rfl h5
      simpa [RegFile.write, fT, fBV] using h
    have ha6 : RunsTo store program
        ⟨(regs.write fT 1).write fRV (regs fBV - 1), E + 6, false⟩
        ⟨((regs.write fT 1).write fRV (regs fBV - 1)).write fRP
          (bb + regs fBP), E + 7, false⟩ [] [Category.arithmetic] := by
      have h := RunsTo.add (store := store)
        (s := (⟨(regs.write fT 1).write fRV (regs fBV - 1), E + 6,
          false⟩ : State)) rfl h6
      simpa [RegFile.write, fT, fRV, fBB, fBP, hBB] using h
    refine ⟨((regs.write fT 1).write fRV (regs fBV - 1)).write fRP
      (bb + regs fBP), ?_, ?_, ?_⟩
    · have hrun := ((hpin.trans hbr1).trans hs5).trans ha6
      simpa [fringeCandGlobalArmCats, hbv] using hrun
    · have e1 : (((regs.write fT 1).write fRV (regs fBV - 1)).write fRP
          (bb + regs fBP)) fRV = regs fBV - 1 := by
        simp [RegFile.write, fRV, fRP]
      have e2 : (((regs.write fT 1).write fRV (regs fBV - 1)).write fRP
          (bb + regs fBP)) fRP = bb + regs fBP := by
        simp [RegFile.write]
      rw [e1, e2]
      obtain ⟨v, hv⟩ : ∃ v, regs fBV = v + 1 := ⟨regs fBV - 1, by omega⟩
      rw [hv, bestOfRegs_succ]
      simp [bpFringeCandGlobal]
    · intro r hr
      obtain ⟨hT, hRV, hRP⟩ := hr
      simp [RegFile.write, hT, hRV, hRP]

/-! ## The whole fringe arm: prologue, fold, epilogue

Composing `fringeLeg_runsTo` with `fringeCandGlobal_runsTo` gives a whole
fringe arm.  Layout: prologue `A .. A+20`, fold loop base `A+21` (exit
`A+88`), epilogue `A+88 .. A+94`, arm exit `A+95`.

The epilogue's category log is indexed by the ROUTE-side condition — the
`isSome` of the accepted fold object's best candidate — not by the
machine's register, and not by a numeral.
-/

/-- The option-shift convention agrees with `Option.isSome`. -/
theorem bestOfRegs_isSome (bv bp : Nat) :
    (bestOfRegs bv bp).isSome = !(bv == 0) := by
  unfold bestOfRegs
  by_cases h : bv = 0 <;> simp [h]

/-- Category log of a whole fringe arm, indexed by the route-side
occupancy of the fold's best candidate. -/
def fringeArmCats (store : ReadStore) (S c : Nat) (window : List Bool)
    (relLo relHi seed count : Nat) : List Category :=
  fringeLegCats store S c window relLo relHi seed count ++
    fringeCandGlobalArmCats
      ((bpFringeChunkFoldTraceResultAtSegmentWithStore store S c window
        seed relLo relHi count).value.2).isSome

/--
Exact simulation of a whole charged fringe arm: four charged window
reads, the capped charged chunk fold, and the pure global rebase.

The receipt is exactly the four window reads followed positionally by the
accepted fold object's trace — the epilogue adds none — and the result
pair in `fRV`/`fRP` is the route's `bpFringeCandGlobal` applied to the
accepted fold object's own best candidate.
-/
theorem fringeArm_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A S c L : Nat}
    (hc : c ≤ L)
    (hPro : HostedAt program A (fringeArmPrologue c))
    (hPre : HostedAt program (A + 21) (fringePrefix S c))
    (hMrg : HostedAt program (A + 21 + 32) (fringeMerge (A + 21)))
    (hTail : HostedAt program (A + 21 + 45)
      (fringeShift c L ++ fringeAdvance))
    (hbr : program[A + 21 + 66]? = some (.brNZ fCnt (A + 21)))
    (hEpi : HostedAt program (A + 88) (fringeCandGlobal (A + 88)))
    (base bb relLo relHi seed start : Nat)
    (h0 : (readBits store base).length = L)
    (h1 : (readBits store (base + 1)).length = L)
    (h2 : (readBits store (base + 2)).length = L)
    (regs : RegFile)
    (hBase : regs fBase = base) (hLo : regs fLo = relLo)
    (hHi : regs fHi = relHi) (hAcc : regs fAcc = seed)
    (hBB : regs fBB = bb) (hSeed : regs fSeed = seed)
    (hStart : regs fStart = start) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs, A, false⟩ ⟨regsF, A + 95, false⟩
        (windowReadEvents store base ++
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
            (windowBitsOfStore store base) seed relLo relHi
            (Nat.min (relHi / c + 1) 33)).trace)
        (fringeArmCats store S c (windowBitsOfStore store base)
          relLo relHi seed (Nat.min (relHi / c + 1) 33)) ∧
      some (regsF fRV, regsF fRP) =
        bpFringeCandGlobal bb seed start
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
            (windowBitsOfStore store base) seed relLo relHi
            (Nat.min (relHi / c + 1) 33)).value.2 := by
  obtain ⟨regsL, hrunL, hvalL, hpresL⟩ :=
    fringeLeg_runsTo store hc hPro hPre hMrg hTail hbr base relLo relHi
      seed h0 h1 h2 regs hBase hLo hHi hAcc
  have hbest : bestOfRegs (regsL fBV) (regsL fBP) =
      (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
        (windowBitsOfStore store base) seed relLo relHi
        (Nat.min (relHi / c + 1) 33)).value.2 :=
    congrArg Prod.snd hvalL
  have hBBL : regsL fBB = bb := by
    rw [hpresL fBB (by decide), hBB]
  have hSeedL : regsL fSeed = seed := by
    rw [hpresL fSeed (by decide), hSeed]
  have hStartL : regsL fStart = start := by
    rw [hpresL fStart (by decide), hStart]
  obtain ⟨regsF, hrunE, hvalE, _hpresE⟩ :=
    fringeCandGlobal_runsTo store hEpi regsL bb seed start
      hBBL hSeedL hStartL
  -- the epilogue's arm index is the route-side occupancy of the best
  have hidx : (!(regsL fBV == 0)) =
      ((bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
        (windowBitsOfStore store base) seed relLo relHi
        (Nat.min (relHi / c + 1) 33)).value.2).isSome := by
    rw [<- hbest, bestOfRegs_isSome]
  rw [hidx] at hrunE
  have htrans := RunsTo.trans hrunL hrunE
  have hpc : A + 88 + 7 = A + 95 := by omega
  rw [hpc] at htrans
  have hev : (windowReadEvents store base ++
      (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
        (windowBitsOfStore store base) seed relLo relHi
        (Nat.min (relHi / c + 1) 33)).trace) ++ ([] : List TraceEvent) =
      windowReadEvents store base ++
      (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
        (windowBitsOfStore store base) seed relLo relHi
        (Nat.min (relHi / c + 1) 33)).trace := by simp
  rw [hev] at htrans
  refine ⟨regsF, htrans, ?_⟩
  rw [hvalE, hbest]

/-! ## Value bridges to the named accepted fringe arm objects

`fringeArm_runsTo` delivers the result pair against the fold object and
`bpFringeCandGlobal`.  These two lemmas identify that with the `.value` of
the NAMED accepted arm objects
`bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore` and its
right counterpart (`ChargedFringeTrace.lean:707`/`:730`), at the route's
own instantiation of base, start, `relLo` and `relHi`.
-/

/-- The accepted LEFT fringe arm's value, in the form the machine
delivers it. -/
theorem leftArm_value_eq
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize leftClose seed : Nat) :
    (bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize leftClose seed).value =
      bpFringeCandGlobal (localBPWindowBase shape blockSize leftClose)
        seed (leftClose + 1)
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store fringeSegment
          (bpFringeChunkBits shape.bpCode.length)
          (windowBitsOfStore store
            (bpWindowFirstWord shape blockSize leftClose))
          seed
          (leftClose + 1 - localBPWindowBase shape blockSize leftClose)
          (leftClose + 1 +
            (blockStartOf blockSize (blockOfClose blockSize leftClose) +
              blockSize - leftClose) - 1 -
            localBPWindowBase shape blockSize leftClose)
          (Nat.min
            ((leftClose + 1 +
              (blockStartOf blockSize (blockOfClose blockSize leftClose) +
                blockSize - leftClose) - 1 -
              localBPWindowBase shape blockSize leftClose) /
              bpFringeChunkBits shape.bpCode.length + 1) 33)).value.2 := by
  unfold bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [<- route_windowBits_eq_windowBitsOfStore shape store blockSize
    leftClose]
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]

/-- The accepted RIGHT fringe arm's value, in the form the machine
delivers it. -/
theorem rightArm_value_eq
    (shape : Cartesian.CartesianShape) (store : ReadStore)
    (fringeSegment blockSize rightClose seed : Nat) :
    (bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
        shape store fringeSegment blockSize rightClose seed).value =
      bpFringeCandGlobal (localBPWindowBase shape blockSize rightClose)
        seed (blockStartOf blockSize (blockOfClose blockSize rightClose))
        (bpFringeChunkFoldTraceResultAtSegmentWithStore store fringeSegment
          (bpFringeChunkBits shape.bpCode.length)
          (windowBitsOfStore store
            (bpWindowFirstWord shape blockSize rightClose))
          seed
          (blockStartOf blockSize (blockOfClose blockSize rightClose) -
            localBPWindowBase shape blockSize rightClose)
          (blockStartOf blockSize (blockOfClose blockSize rightClose) +
            (rightClose -
              blockStartOf blockSize (blockOfClose blockSize rightClose) + 2)
            - 1 - localBPWindowBase shape blockSize rightClose)
          (Nat.min
            ((blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) + 2)
              - 1 - localBPWindowBase shape blockSize rightClose) /
              bpFringeChunkBits shape.bpCode.length + 1) 33)).value.2 := by
  unfold bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
  rw [<- route_windowBits_eq_windowBitsOfStore shape store blockSize
    rightClose]
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map,
    WordRAM.TraceResult.pure]

end E1FringeArmBlock
end WordRAM
end RMQ
