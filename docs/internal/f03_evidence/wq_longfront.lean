import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
THE LIVE QUERY-PATH REGIME FRONTIER.

The closure comparison (wq_regimemember.lean) shows the summary/interior regime
switches (`canonicalBPRelativeMinMaxArgSummaryTableActive` and friends) are in
the STORE closure only, NOT in the controller closure.  The regime predicates
that ARE live on the query path are, all inside the select leaf L1:

    superIsLong, localIsSparseException, compactLocalEntryIsLive
    (via sparseExceptionSelectData shape.bpCode false)

They are the only content-reading BRANCHES the controller can take.  This file
maps their true firing frontier by evaluation.

Structure of the bound.  `superIsLong bits false s` is
`superLongSpan m < superSpan bits false s` with `m = bits.length = 2n`.
A super slot covers `superStride m` consecutive closes, so its span is
(#closes in window) + (#opens in window).  Opens in the window are either
matched inside (at most superStride of them) or still on the stack at the
window end (at most the tree depth <= n).  Hence

    superSpan <= 2 * superStride m + n            (STRUCTURAL BOUND)

so `superIsLong` is IDENTICALLY FALSE, for every shape whatsoever, whenever

    2 * superStride (2n) + n <= superLongSpan (2n).

We (1) scan that arithmetic to find the exact first n where the bound stops
excluding firing, and (2) EXECUTE max superSpan on shape families chosen to
maximise it, to check the bound is not fantasy.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.GenericSelect

namespace WQLong

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

/-- `deep a b`: bp = T (TF)^a F T^b F^b.  A run of widely spaced closes, then a
    maximal descending chain of `b` opens, then `b` packed closes.  This is the
    span-maximising family: the window straddling the chain picks up `b` opens
    that are not matched inside it. -/
def deep (a b : Nat) : CartesianShape := .node (rightSpine a) (leftSpine b)

/-- Mirror: the descending chain comes first. -/
def deepL (a b : Nat) : CartesianShape := .node (leftSpine b) (rightSpine a)

/-- Chain in the middle of a right spine. -/
def midChain (a b c : Nat) : CartesianShape :=
  .node (rightSpine a) (.node (leftSpine b) (rightSpine c))

def logPath : String :=
  "C:/Users/poin/AppData/Local/Temp/claude/C--Users-poin-Documents-RMQ--claude-worktrees-recursing-cerf-300c92/09e21f10-b494-4393-9fb6-2f4ad4dedb1c/scratchpad/wq_longfront_log.txt"

/-- max over all super slots of superSpan, for one shape and target. -/
def maxSuperSpan (s : CartesianShape) (tgt : Bool) : Nat :=
  let bits := s.bpCode
  let k := superSlotCount bits tgt
  (List.range k).foldl (fun acc i => max acc (superSpan bits tgt i)) 0

def anyLong (s : CartesianShape) (tgt : Bool) : Bool :=
  let bits := s.bpCode
  (List.range (superSlotCount bits tgt)).any (fun i => superIsLong bits tgt i)

def anyExc (s : CartesianShape) (tgt : Bool) : Bool :=
  let bits := s.bpCode
  (List.range (localSlotCount bits tgt)).any (fun i => localIsSparseException bits tgt i)

def liveCount (s : CartesianShape) (tgt : Bool) : Nat :=
  let bits := s.bpCode
  ((List.range (localSlotCount bits tgt)).filter
    (fun i => compactLocalEntryIsLive bits tgt i)).length

#eval show IO Unit from do
  let h <- IO.FS.Handle.mk logPath IO.FS.Mode.write
  let say (s : String) : IO Unit := do h.putStrLn s; h.flush; IO.println s

  say "=== PART 1: arithmetic frontier of the live select regimes ==="
  say "n | m=2n | wordBits | ell | superStride | superLongSpan | structuralMaxSpan=2*superStride+n | CAN-FIRE?"
  let mut firstNaive : Option Nat := none
  let mut firstStruct : Option Nat := none
  -- exact scan over n at powers of two and at the band edges
  for e in List.range 26 do
    let n := 2 ^ e
    let m := 2 * n
    let sl := superLongSpan m
    let ss := superStride m
    let bound := 2 * ss + n
    let naive := decide (sl < m)
    let struc := decide (sl < bound)
    if naive && firstNaive.isNone then firstNaive := some n
    if struc && firstStruct.isNone then firstStruct := some n
    say s!"n=2^{e}={n} m={m} w={wordBits m} ell={ell m} superStride={ss} superLongSpan={sl} structMax={bound} naiveCanFire={naive} structCanFire={struc}"
  say s!"first n (powers of 2) where the NAIVE bound (span<=m) stops excluding firing: {firstNaive}"
  say s!"first n (powers of 2) where the STRUCTURAL bound stops excluding firing: {firstStruct}"

  -- exact linear localisation of the structural frontier
  say "-- exact structural frontier by linear scan --"
  let mut exact : Option Nat := none
  for i in List.range 40000 do
    let n := i + 1
    let m := 2 * n
    if decide (superLongSpan m < 2 * superStride m + n) then
      if exact.isNone then
        exact := some n
        say s!"EXACT smallest n with superLongSpan(2n) < 2*superStride(2n)+n : n={n} (m={m}, superLongSpan={superLongSpan m}, bound={2 * superStride m + n})"
  say s!"structural frontier over n=1..40000 : {exact}"
  say "  => for EVERY n strictly below that value, and EVERY shape of that size,"
  say "     superIsLong is identically false and localIsSparseException is identically false."

  say "=== PART 2: localStride, which gates the sparse-local regime ==="
  let mut firstStride : Option Nat := none
  for e in List.range 130 do
    let m := 2 ^ e
    if decide (2 <= localStride m) then
      if firstStride.isNone then
        firstStride := some e
        say s!"first exponent e with localStride(2^e) >= 2 : e={e} localStride={localStride m} wordBits={wordBits m} ell={ell m}"
  say s!"localStride>=2 first at 2^{firstStride} (none up to 2^129 means the sparse-local arm is unreachable)"

  say "=== PART 3: EXECUTED max superSpan on span-maximising families ==="
  say "n | family | maxSuperSpan(false) | superLongSpan(2n) | margin | anyLong | anyExc"
  for n in [64, 128, 256, 512, 1024, 2048] do
    let m := 2 * n
    let sl := superLongSpan m
    let fams : List (String × CartesianShape) :=
      [ ("leftSpine", leftSpine n), ("rightSpine", rightSpine n)
      , ("balanced", balanced n)
      , ("deep(n/4,3n/4)", deep (n / 4) (n - 1 - n / 4))
      , ("deep(1,n-2)", deep 1 (n - 2))
      , ("deepL(n/4,3n/4)", deepL (n / 4) (n - 1 - n / 4))
      , ("midChain", midChain (n / 4) (n / 2) (n - 1 - n / 4 - n / 2)) ]
    for (nm, s) in fams do
      if s.size != n then
        say s!"  GENBUG n={n} {nm} size={s.size}"
      else
        let ms := maxSuperSpan s false
        say s!"  n={n} {nm} maxSuperSpan={ms} superLongSpan={sl} margin={sl - ms} anyLong={anyLong s false} anyExc={anyExc s false} liveLocals={liveCount s false}"
  say "DONE"
  h.flush

end WQLong
