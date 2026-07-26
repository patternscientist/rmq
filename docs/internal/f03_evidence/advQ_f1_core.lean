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


end AdvQF1
