import Lean
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION ATTEMPT on the F1 = S verdict, QUANTIFIER LENS.
Independent of the claimant's files.
-/

open Lean Lean.Meta Lean.Elab

namespace AdvQF1

partial def headName (e : Expr) : String :=
  match Lean.Expr.getAppFn e with
  | Expr.const n _ => n.toString
  | Expr.fvar _ => "<fvar>"
  | Expr.bvar i => s!"<bvar {i}>"
  | _ => "<other>"

/-- Walk `body`, reporting for each occurrence of fvar `target` the chain of
enclosing application heads (innermost first). -/
partial def occs (target : FVarId) (parents : List String) (e : Expr) :
    Array String -> Array String :=
  fun acc =>
  match e with
  | Expr.fvar id =>
      if id == target then acc.push (String.intercalate " < " parents) else acc
  | Expr.app _ _ =>
      let f := Lean.Expr.getAppFn e
      let args := Lean.Expr.getAppArgs e
      let h := headName e
      let acc := occs target parents f acc
      args.foldl (fun a x => occs target (h :: parents) x a) acc
  | Expr.lam _ t b _ => occs target ("<lam>" :: parents) b (occs target parents t acc)
  | Expr.forallE _ t b _ => occs target ("<pi>" :: parents) b (occs target parents t acc)
  | Expr.letE _ t v b _ =>
      occs target ("<let>" :: parents) b
        (occs target parents v (occs target parents t acc))
  | Expr.mdata _ b => occs target parents b acc
  | Expr.proj s i b => occs target (s!"<proj {s}.{i}>" :: parents) b acc
  | _ => acc

def scanConsumer (nm : Name) : MetaM Unit := do
  let env <- getEnv
  let some ci := env.find? nm | throwError "no {nm}"
  let some val := ci.value? | throwError "no value for {nm}"
  lambdaTelescope val fun xs body => do
    IO.println s!"CONSUMER {nm}"
    for x in xs do
      let fv := x.fvarId!
      let ld <- fv.getDecl
      let found := occs fv [] body #[]
      IO.println s!"  binder {ld.userName} : occurrences={found.size}"
      for f in found do
        IO.println s!"      ctx: {f}"

end AdvQF1

open Lean.Elab.Command in
run_cmd liftTermElabM do
  AdvQF1.scanConsumer
    ``RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore

open RMQ RMQ.Cartesian RMQ.SuccinctFinal RMQ.SuccinctRank

namespace AdvQF1

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

/-- Right spine of size n, STRUCTURAL (needed for a real factorization). -/
def rspine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rspine n)

theorem rspine_size (n : Nat) : (rspine n).size = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [rspine, CartesianShape.size, ih]
      omega

/-- Independent restatement of the congruence, proved by me. The closing `rfl`
inside `rw` is what certifies `data` is consumed ONLY through those three
projections: if `data` leaked anywhere else this would not close. -/
theorem my_congr
    {b1 b2 : List Bool} {s1 o1 q1 s2 o2 q2 : Nat}
    (d1 : TwoLevelPayloadLiveStoredWordRankData b1 s1 o1 q1)
    (d2 : TwoLevelPayloadLiveStoredWordRankData b2 s2 o2 q2)
    (hlen : b1.length = b2.length)
    (hws : d1.wordSize = d2.wordSize)
    (hbps : d1.blocksPerSuper = d2.blocksPerSuper)
    (store : WordRAM.ReadStore) (ss bs ws cs c : Nat)
    (target : Bool) (pos : Nat) :
    d1.bpChunkedRankTraceResultWithStore store ss bs ws cs c target pos
      = d2.bpChunkedRankTraceResultWithStore store ss bs ws cs c target pos := by
  have hq : d1.queryPos pos = d2.queryPos pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.queryPos, hlen]
  have hwi : d1.wordIndex pos = d2.wordIndex pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.wordIndex, hq, hws]
  have hsi : d1.superIndex pos = d2.superIndex pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.superIndex, hwi, hbps]
  have hwo : d1.wordOffset pos = d2.wordOffset pos := by
    simp [TwoLevelPayloadLiveStoredWordRankData.wordOffset, hq, hwi, hws]
  unfold TwoLevelPayloadLiveStoredWordRankData.bpChunkedRankTraceResultWithStore
  rw [hsi, hwi, hwo]

/-- THE STATEMENT THE `S` LABEL ACTUALLY NEEDS: the controller may replace the
semantic shape by a shape it FABRICATES FROM n ALONE, with no change to value or
trace. Strictly stronger than "same-size shapes agree". -/
theorem F1_factors_through_n
    (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        shape store base pos
      = RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
        (rspine shape.size) store base pos := by
  have hlen : shape.bpCode.length = (rspine shape.size).bpCode.length := by
    rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, rspine_size]
  unfold RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
  rw [show SuccinctClose.bpFringeChunkBits shape.bpCode.length
        = SuccinctClose.bpFringeChunkBits (rspine shape.size).bpCode.length from
      by rw [hlen]]
  exact
    my_congr
      (builtRelativeSplitBPCloseRankData shape)
      (builtRelativeSplitBPCloseRankData (rspine shape.size))
      hlen
      (by
        show SuccinctRank.machineWordBits shape.bpCode.length
          = SuccinctRank.machineWordBits (rspine shape.size).bpCode.length
        rw [hlen])
      (by
        show SuccinctRank.machineWordBits shape.bpCode.length
          = SuccinctRank.machineWordBits (rspine shape.size).bpCode.length
        rw [hlen])
      store base (base + 1) (base + 2) (base + 4) _ false pos

theorem F1_exists_G :
    exists G : Nat -> WordRAM.ReadStore -> Nat -> Nat -> WordRAM.TraceResult Nat,
      forall (shape : CartesianShape) store base pos,
        RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
            shape store base pos
          = G shape.size store base pos := by
  refine ⟨fun n store base pos =>
    RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
      (rspine n) store base pos, ?_⟩
  intro shape store base pos
  exact F1_factors_through_n shape store base pos

#print axioms F1_factors_through_n
#print axioms F1_exists_G

def F1 (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    WordRAM.TraceResult Nat :=
  RMQ.SuccinctFinal.concreteBPNativeRankCloseWordTraceResultAtSegmentWithStore
    shape store base pos

def reads (shape : CartesianShape) (store : WordRAM.ReadStore) (base pos : Nat) :
    List (Nat × Nat) :=
  (F1 shape store base pos).trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

def lspine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (lspine n) CartesianShape.empty

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

partial def zig : Nat -> Bool -> CartesianShape
  | 0, _ => CartesianShape.empty
  | Nat.succ n, b =>
      if b then CartesianShape.node CartesianShape.empty (zig n false)
      else CartesianShape.node (zig n true) CartesianShape.empty

partial def prand : Nat -> Nat -> CartesianShape
  | 0, _ => CartesianShape.empty
  | Nat.succ n, seed =>
      let k := (seed * 1103515 + 12345) % (n + 1)
      CartesianShape.node (prand k (seed * 31 + 7)) (prand (n - k) (seed * 17 + 3))

def families (n : Nat) : List (String × CartesianShape) :=
  [("rspine", rspine n), ("lspine", lspine n), ("balanced", balanced n),
   ("zig", zig n true), ("rand1", prand n 1), ("rand2", prand n 12345),
   ("rand3", prand n 777777)]

def stNone : WordRAM.ReadStore where readWord? := fun _ _ => none

def stFlat (w : List Bool) : WordRAM.ReadStore where readWord? := fun _ _ => some w

-- none exactly on the packed-word segment (base+2 with base=6 => 8)
def stHoleWord : WordRAM.ReadStore where
  readWord? := fun seg _ => if seg == 8 then none else some [true, false, true]

def stHoleSuper : WordRAM.ReadStore where
  readWord? := fun seg _ => if seg == 6 then none else some [true, false, true]

-- ragged widths: returned word length swings wildly with the index
def stRagged : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range ((seg * 13 + i * 29) % 71)).map (fun k => (k * 7 + i) % 3 == 0))

def stHash : WordRAM.ReadStore where
  readWord? := fun seg i =>
    some ((List.range 64).map (fun k => (seg * 7 + i * 13 + k * 5) % 3 == 0))

def storeList : List (String × WordRAM.ReadStore) :=
  [("none", stNone), ("flat0", stFlat [true, false, true, false]),
   ("flatEmpty", stFlat []), ("holeWord", stHoleWord), ("holeSuper", stHoleSuper),
   ("ragged", stRagged), ("hash", stHash)]

def posesFor (n : Nat) : List Nat :=
  [0, 1, n - 1, n, n + 1, 2 * n - 1, 2 * n, 2 * n + 1, 4 * n, 1000000]

def basesList : List Nat := [0, 6, 17, 999]

def sigOf (s : CartesianShape) (store : WordRAM.ReadStore) (n : Nat) :
    List (Nat × List WordRAM.TraceEvent) :=
  basesList.flatMap fun b =>
    (posesFor n).map fun p => let r := F1 s store b p; (r.value, r.trace)

-- A: cross-family differential at LARGE n. Any nonzero violation refutes S.
#eval show IO Unit from do
  for n in [7, 8, 15, 16, 31, 32, 63, 64, 100, 127, 128, 200, 255, 256, 400] do
    let fams := families n
    let base := fams.head!
    let mut bad : List String := []
    for (nm, st) in storeList do
      let bsig := sigOf base.2 st n
      for (fnm, s) in fams do
        if s.size != n then bad := bad ++ [s!"SIZEBUG {fnm}={s.size}"]
        if sigOf s st n != bsig then bad := bad ++ [s!"DIFFER store={nm} fam={fnm}"]
    IO.println s!"LARGE-N n={n} bpLen={base.2.bpCode.length} families={fams.length} stores={storeList.length} violations={bad.length} {bad.take 4}"

-- B: probe-count bound at large n
#eval show IO Unit from do
  let mut worst := 0
  let mut worstAt := ""
  for n in [1, 2, 4, 8, 16, 32, 64, 128, 256, 400] do
    for (nm, st) in storeList do
      for p in posesFor n do
        let k := (reads (rspine n) st 6 p).length
        if k > worst then
          worst := k
          worstAt := s!"n={n} store={nm} pos={p}"
  IO.println s!"MAX-PROBES worst={worst} at {worstAt}"

-- C: anti-vacuity
#eval show IO Unit from do
  for n in [8, 64, 256, 400] do
    IO.println s!"ANTIVAC-N n={n} ragged reads={reads (rspine n) stRagged 6 n} value={(F1 (rspine n) stRagged 6 n).value}"
  for (nm, st) in storeList do
    IO.println s!"ANTIVAC-STORE store={nm} reads={reads (rspine 100) st 6 100} value={(F1 (rspine 100) st 6 100).value}"

-- D: geometry knobs at large n
#eval show IO Unit from do
  for n in [7, 63, 100, 255, 400] do
    let d := builtRelativeSplitBPCloseRankData (rspine n)
    IO.println s!"KNOBS n={n} bpLen={(rspine n).bpCode.length} wordSize={d.wordSize} blocksPerSuper={d.blocksPerSuper} c={RMQ.SuccinctClose.bpFringeChunkBits (rspine n).bpCode.length} qp={d.queryPos n} si={d.superIndex n} wi={d.wordIndex n} wo={d.wordOffset n}"

-- E: the shape families really are distinct trees (guard against a vacuous sweep)
#eval show IO Unit from do
  for n in [7, 16, 63, 100] do
    let fams := families n
    IO.println s!"DISTINCT n={n} distinctBpCodes={((fams.map (fun p => p.2.bpCode)).eraseDups).length} of {fams.length}"

end AdvQF1
