import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL REFUTATION, attack #4: close the two things the defender left open.

(1) The defender left 36 of 74 divisor slots "UNRESOLVED, arrives as a lambda-bound
    parameter", explicitly listing `macroSize`, `macroCount`, `localStride`,
    `stride`, `superStride`, `layout.macroSize`, `layout.blocksPerSuper`.  All of
    those are fields/derivations of `RelativeRmm.canonicalLayout shape`
    (RMQ/Core/SuccinctClose/RelativeSummary.lean:1276-1281), which is IN the
    917-constant core.  If `canonicalLayout` is size-congruent, that whole family
    collapses to S in one step.

(2) The F5 residual.  `canonicalRelativeRmmInteriorComponentOffsets`
    (InteriorDirectory.lean:1614-1627) is the hop that carries `bpExcessAt` into
    the controller (defender's BFS hop 9 -> 10 -> 11).  But it consumes the
    content-built tables ONLY through `(... .machineStore hword).store.words.size`
    -- i.e. through their WORD COUNT.  If the offsets record is size-congruent
    while the table ENTRIES genuinely differ, then `bpExcessAt` is computed and
    DISCARDED: build-only (B), not a free input (X).  That is the exact
    anti-vacuity pair the defender never produced.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctClose

namespace AdvRxOffBig

/-! ## Part 1: CHECKED size-congruence of the whole canonical layout. -/

theorem base_congr {a b : CartesianShape} (h : a.size = b.size) :
    canonicalBPRelativeSummaryBase a = canonicalBPRelativeSummaryBase b := by
  unfold canonicalBPRelativeSummaryBase; rw [h]

theorem layout_congr {a b : CartesianShape} (h : a.size = b.size) :
    RelativeRmm.canonicalLayout a = RelativeRmm.canonicalLayout b := by
  unfold RelativeRmm.canonicalLayout
  unfold canonicalBPRelativeSummaryBlockSizeRaw
    canonicalBPRelativeSummaryBlocksPerSuperRaw
    canonicalBPRelativeSummaryBlockCountRaw
    canonicalBPRelativeSummaryRelativeWidthRaw
  rw [base_congr h, h]

/-- every layout-derived divisor the defender left UNRESOLVED is therefore
    size-only.  Stated for the ones named in their divisor dump. -/
theorem macroSize_congr {a b : CartesianShape} (h : a.size = b.size) :
    (RelativeRmm.canonicalLayout a).macroSize =
      (RelativeRmm.canonicalLayout b).macroSize := by
  rw [layout_congr h]

theorem macroSampleCount_congr {a b : CartesianShape} (h : a.size = b.size) :
    (RelativeRmm.canonicalLayout a).macroSampleCount =
      (RelativeRmm.canonicalLayout b).macroSampleCount := by
  rw [layout_congr h]

theorem superSampleCount_congr {a b : CartesianShape} (h : a.size = b.size) :
    (RelativeRmm.canonicalLayout a).superSampleCount =
      (RelativeRmm.canonicalLayout b).superSampleCount := by
  rw [layout_congr h]

/-- `superWidth` also only touches `bpCode.length`, which `bpCode_length`
    (RMQ/Core/Shape.lean:51) makes `2 * size`. -/
theorem superWidth_congr {a b : CartesianShape} (h : a.size = b.size) :
    (RelativeRmm.canonicalLayout a).superWidth a =
      (RelativeRmm.canonicalLayout b).superWidth b := by
  unfold RelativeRmm.Layout.superWidth
  rw [CartesianShape.bpCode_length, CartesianShape.bpCode_length, h]

/-! ## Part 2: executed offsets-vs-entries anti-vacuity pair. -/

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

partial def leftSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (leftSpine n) CartesianShape.empty

partial def rightSpine : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node CartesianShape.empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n => CartesianShape.node (balanced (n / 2)) (balanced (n - n / 2))

partial def zigzag (goLeft : Bool) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      if goLeft then CartesianShape.node (zigzag false n) CartesianShape.empty
      else CartesianShape.node CartesianShape.empty (zigzag true n)

partial def pseudo (seed : Nat) : Nat -> CartesianShape
  | 0 => CartesianShape.empty
  | Nat.succ n =>
      let k := (seed * 1103515245 + 12345) % (n + 1)
      CartesianShape.node (pseudo (seed + 7) k) (pseudo (seed + 13) (n - k))

def family (n : Nat) : List (String × CartesianShape) :=
  [("leftSpine", leftSpine n), ("rightSpine", rightSpine n),
   ("balanced", balanced n), ("zigzagL", zigzag true n),
   ("pseudo3", pseudo 3 n), ("pseudo11", pseudo 11 n)]

def offs (s : CartesianShape) : CanonicalRelativeRmmInteriorComponentOffsets :=
  canonicalRelativeRmmInteriorComponentOffsets s

def layoutTuple (s : CartesianShape) : Nat × Nat × Nat × Nat :=
  let l := RelativeRmm.canonicalLayout s
  (l.blockSize, l.blocksPerSuper, l.blockCount, l.relativeWidth)

/-- content probes: these MUST differ across the family, or Part 2 is vacuous. -/
def contentProbe (s : CartesianShape) : List Nat :=
  let l := RelativeRmm.canonicalLayout s
  let bs := l.blockSize
  let bps := l.blocksPerSuper
  let sc := canonicalBPRelativeSummarySuperCountRaw s
  (List.range 6).map (fun p => bpExcessAt s (p * 3))
    ++ (List.range 4).map (fun b => bpBlockArgMinPrefixPos s bs b)
    ++ bpSuperblockBaselineEntries s bs bps sc
    ++ bpBlockArgMinLocalOffsetEntries s bs l.blockCount

#eval show IO Unit from do
  for n in [256, 512, 600, 1024] do
    let fam := family n
    match fam with
    | [] => pure ()
    | (lbl0, s0) :: _ =>
      let o0 := offs s0
      let lt0 := layoutTuple s0
      let c0 := contentProbe s0
      let mut offD := 0
      let mut layD := 0
      let mut conD := 0
      for (_, s) in fam do
        if offs s != o0 then offD := offD + 1
        if layoutTuple s != lt0 then layD := layD + 1
        if contentProbe s != c0 then conD := conD + 1
      IO.println s!"n={n} base={lbl0} layout={lt0}"
      IO.println s!"   offsets = {repr o0}"
      IO.println s!"   ACROSS {fam.length} equal-size shapes:  layoutDiffers={layD}  offsetsDiffers={offD}   ||  ANTI-VACUITY contentProbeDiffers={conD}"
      IO.println s!"   contentProbe(base)   = {c0.take 12}"
      match fam.drop 1 with
      | (lbl1, s1) :: _ => IO.println s!"   contentProbe({lbl1}) = {(contentProbe s1).take 12}"
      | _ => pure ()

end AdvRxOffBig
