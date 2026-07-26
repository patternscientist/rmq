import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION ATTEMPT against verdict S for
`RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore` (F1).

Goal: find two shapes of the SAME size whose F1 TraceResult (value AND trace)
differs, for SOME store / base / position.

Novel attack surface vs the original agent's sweep:
  * PARTIAL stores (readWord? = none) that drive the `| _,_,_ => pure 0` branch
    at ChargedRankSelectLeafTrace.lean:181 -- never exercised by their 3 total stores.
  * VARIABLE-LENGTH reply words (word.length feeds `bpWordRankEffLimit`, hence
    the chunk count and the chunk-table addresses).
  * larger sizes (7, 8) and boundary positions around `wordSize` multiples.
  * more bases, incl. base 0 and huge base.
  * full (value, trace) equality, i.e. every field of `TraceResult`.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace AdvF1

/-- Memoized exhaustive shape enumeration (no exponential recomputation). -/
def shapesUpTo : Nat -> Array (List CartesianShape)
  | 0 => #[[CartesianShape.empty]]
  | Nat.succ n =>
      let prev := shapesUpTo n
      let next : List CartesianShape :=
        (List.range (n + 1)).flatMap fun k =>
          (prev[k]!).flatMap fun l =>
            (prev[n - k]!).map fun r => CartesianShape.node l r
      prev.push next

def shapesOfSize (n : Nat) : List CartesianShape := (shapesUpTo n)[n]!

def spine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (spine n)

def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore shape store base pos

/-! ### Adversarial stores -/

/-- Everything missing: forces the `_,_,_ => pure 0` fallback. -/
def noneStore : WordRAM.ReadStore where
  readWord? := fun _ _ => none

/-- A hole at exactly one segment; everything else present. -/
def holeStore (hole : Nat) : WordRAM.ReadStore where
  readWord? := fun s i =>
    if s == hole then none
    else some ((List.range 12).map (fun k => (s * 5 + i * 7 + k * 3) % 4 < 2))

/-- Reply words of WILDLY VARYING LENGTH (0..19): word.length feeds
`bpWordRankEffLimit`, so this moves the chunk count and the chunk addresses. -/
def varLenStore : WordRAM.ReadStore where
  readWord? := fun s i =>
    some ((List.range ((s * 3 + i * 5) % 20)).map (fun k => (k * 7 + s + i) % 3 == 0))

/-- Wide 64-bit replies. -/
def bigStore : WordRAM.ReadStore where
  readWord? := fun s i =>
    some ((List.range 64).map (fun k => (s * 31 + i * 17 + k * 11) % 5 < 2))

/-- Sometimes-none, index dependent (holes interleaved with data). -/
def sparseStore : WordRAM.ReadStore where
  readWord? := fun s i =>
    if (s + i) % 3 == 0 then none
    else some ((List.range ((i % 9) + 1)).map (fun k => (k + s * i) % 2 == 0))

def stores : List (String × WordRAM.ReadStore) :=
  [("none", noneStore), ("hole+0", holeStore 6), ("hole+2", holeStore 8),
   ("hole+4", holeStore 10), ("varLen", varLenStore), ("big", bigStore),
   ("sparse", sparseStore)]

def bases : List Nat := [0, 1, 6, 17, 1000]

def poss : List Nat :=
  (List.range 20) ++ [20, 21, 31, 32, 33, 1000, 1000000]

/-- FULL TraceResult content: value and the entire event list. -/
def sig (s : CartesianShape) : List (Nat × List WordRAM.TraceEvent) :=
  stores.flatMap fun st =>
    bases.flatMap fun b =>
      poss.map fun p => let r := F1 s st.2 b p; (r.value, r.trace)

/-! ### ATTACK 1: exhaustive same-size counterexample hunt, sizes 1..7. -/

#eval show IO Unit from do
  for n in [1, 2, 3, 4, 5, 6, 7] do
    let shapes := shapesOfSize n
    let b := shapes.headD CartesianShape.empty
    let bsig := sig b
    let mut bad : List CartesianShape := []
    for s in shapes do
      if sig s != bsig then bad := s :: bad
    IO.println s!"ATTACK1 n={n} shapes={shapes.length} bpLen={b.bpCode.length} \
combosPerShape={bsig.length} COUNTEREXAMPLES={bad.length}"
    match bad with
    | [] => pure ()
    | c :: _ => IO.println s!"  witness bp={c.bpCode} vs bp={b.bpCode}"

/-! ### ATTACK 2: size 8 (1430 shapes), trimmed matrix but still exhaustive in shape. -/

def sigSmall (s : CartesianShape) : List (Nat × List WordRAM.TraceEvent) :=
  [("varLen", varLenStore), ("sparse", sparseStore), ("none", noneStore)].flatMap
    fun st =>
      ([6, 17] : List Nat).flatMap fun b =>
        ([0, 1, 3, 4, 7, 8, 15, 16, 17, 500] : List Nat).map fun p =>
          let r := F1 s st.2 b p; (r.value, r.trace)

#eval show IO Unit from do
  for n in [8] do
    let shapes := shapesOfSize n
    let b := shapes.headD CartesianShape.empty
    let bsig := sigSmall b
    let mut bad := 0
    for s in shapes do
      if sigSmall s != bsig then bad := bad + 1
    IO.println s!"ATTACK2 n={n} shapes={shapes.length} bpLen={b.bpCode.length} \
COUNTEREXAMPLES={bad}"

/-! ### ATTACK 3: is the congruence VACUOUS?  Does the built data actually
differ across same-size shapes?  If the sample tables/packed words were equal
for all same-size shapes, the S verdict would be trivially true and uninformative. -/

#eval show IO Unit from do
  for n in [3, 5, 7] do
    let shapes := shapesOfSize n
    let b := shapes.headD CartesianShape.empty
    let db := builtRelativeSplitBPCloseRankData b
    let mut diffSuper := 0
    let mut diffBlock := 0
    let mut diffWords := 0
    let mut diffWordSize := 0
    let mut diffOverhead := 0
    for s in shapes do
      let d := builtRelativeSplitBPCloseRankData s
      if d.superFalseEntries != db.superFalseEntries then diffSuper := diffSuper + 1
      if d.blockFalseEntries != db.blockFalseEntries then diffBlock := diffBlock + 1
      if d.bitWords.store.words.toList != db.bitWords.store.words.toList then
        diffWords := diffWords + 1
      if d.wordSize != db.wordSize then diffWordSize := diffWordSize + 1
      if (builtRelativeSplitBPCloseRankSuperOverhead s
            + builtRelativeSplitBPCloseRankBlockOverhead s)
          != (builtRelativeSplitBPCloseRankSuperOverhead b
            + builtRelativeSplitBPCloseRankBlockOverhead b) then
        diffOverhead := diffOverhead + 1
    IO.println s!"ATTACK3 n={n} shapes={shapes.length} \
dataDiffersInSuperEntries={diffSuper} blockEntries={diffBlock} packedWords={diffWords} \
wordSize={diffWordSize} overheadSum={diffOverhead}"

/-! ### ATTACK 4: does the fallback branch actually fire, and is the leaf still
non-dead there?  (Otherwise ATTACK1's `none`/`sparse` rows prove nothing.) -/

#eval show IO Unit from do
  let s := spine 7
  for st in stores do
    let r := F1 s st.2 6 7
    IO.println s!"ATTACK4 store={st.1} value={r.value} steps={r.trace.length} \
reads={r.trace.filterMap fun e => match e with
  | WordRAM.TraceEvent.readWord sg i _ => some (sg, i) | _ => none}"

/-! ### ATTACK 5: the size-only bridge itself.  Verify `bpCode.length = 2*size`
by execution on every enumerated shape (if this failed, "same size" would not
imply "same length" and the whole S argument would collapse). -/

#eval show IO Unit from do
  let mut bad := 0
  let mut total := 0
  for n in [0, 1, 2, 3, 4, 5, 6, 7] do
    for s in shapesOfSize n do
      total := total + 1
      if s.bpCode.length != 2 * s.size then bad := bad + 1
      if s.size != n then bad := bad + 1
  IO.println s!"ATTACK5 shapesChecked={total} lengthOrSizeViolations={bad}"

/-! ### ATTACK 6: cross-SIZE control.  If F1 were shape-blind for a stupid
reason (e.g. all our stores drive it to a constant), differing n would also give
the same answer.  It must NOT. -/

#eval show IO Unit from do
  for st in [("varLen", varLenStore), ("big", bigStore), ("sparse", sparseStore)] do
    let vals := ([1, 2, 3, 5, 8, 13, 21, 34, 100] : List Nat).map fun n =>
      let r := F1 (spine n) st.2 6 9
      (n, r.value, r.trace.length,
        r.trace.filterMap fun e => match e with
          | WordRAM.TraceEvent.readWord sg i _ => some (sg, i) | _ => none)
    IO.println s!"ATTACK6 store={st.1} {vals}"

end AdvF1
