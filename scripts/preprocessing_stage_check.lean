import RMQ.Core.WordRAM.Construction.Proof.Buffer
import RMQ.Core.WordRAM.Construction.Proof.Tail
import RMQ.Core.WordRAM.Construction.Proof.Leaves
import RMQ.Core.WordRAM.Construction.Proof.Exact
import RMQ.Core.WordRAM.Construction.Proof.AccessHalf
import RMQ.Core.WordRAM.Construction.Proof.InteriorClose
import RMQ.Core.WordRAM.Construction.ArrayRun
import Lean

/-! Independent exact-type consumers of the PRE-1 builder stage S2 (emission
calculus, counted loops, zero-initialized arrays, the size-only geometry
prelude, sparse-level tables): the builder source blocks of
`Builder/{Registers,Emit,Geometry,Interior}.lean` (inside the builder firewall)
and their safe-evaluation specifications in
`Proof/{Base,Emit,Interior,Geometry,Stage2,RegSpec,Loops,GeometryBank}.lean`
(outside it). Every exit theorem is restated at a fully written type. The
fixture checks (`stageGuard*`, evaluated once by the verdict command at the
end) run the executable structured evaluator `evalF` (sound for
`Eval`, never the charged interpreter and never kernel evaluation) on the actual
source fragments: the sparse-level tables for `n ∈ {0, 5, 24}` against the
reference table payloads computed from `Cartesian.shape (List.replicate n 0)`,
and the geometry prelude for `n ∈ {0, 1, 7, 24, 1000}` against the reference
values `geoVal n i` of all 39 bank registers. -/

namespace PRE1StageConsumer

open RMQ RMQ.Cartesian RMQ.SuccinctSpace RMQ.SuccinctClose
open RMQ.SuccinctFinal.PackedConstruction
open RMQ.SuccinctFinal.PackedConstruction.Structured
open RMQ.SuccinctFinal.PackedConstruction.Builder
open RMQ.SuccinctFinal.PackedConstruction.Proof

/-! ## Source pins -/

theorem emitBits_def : ∀ (w v : Operand), emitBits w v =
    .seq (.seq (.action (.move 12 w)) (.action (.move 13 v)))
      (.loop 12 (.seq (.action (.arithmetic .mod 11 13 9)) (.seq (.action (.reserve 10))
        (.seq (.action (.store 10 11)) (.seq (.action (.arithmetic .div 13 13 9))
          (.action (.arithmetic .sub 12 12 2))))))) := fun _ _ => rfl

theorem levelEntryBlock_def : ∀ (dom : Operand), levelEntryBlock dom =
    .seq (log2Block 22 14)
      (.seq (.action (.arithmetic .shl 23 2 22)) (.seq (.action (.arithmetic .mul 24 dom 22))
        (.action (.arithmetic .add 16 23 24)))) := fun _ => rfl

/-! ## Emission specifications -/

theorem spec_emitBits : ∀ {W : Nat}, 32 ≤ W → ∀ (w v : Operand), (v : Nat) ≠ 12 →
    ∀ (s : State), s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 →
    s.regs v < 2 ^ W → s.regs w < 2 ^ W → s.extent + s.regs w < 2 ^ W →
    ∃ s' k, SafeEval W (emitBits w v) s s' k ∧ k ≤ 7 * s.regs w + 3 ∧ s'.status = .running ∧
      Emits s s' ((natToBitsLE (s.regs w) (s.regs v)).map bitToNat) ∧
      (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @emitBits_spec

theorem spec_emitTable : ∀ {W : Nat}, 32 ≤ W → ∀ (count w : Operand) (entry : Block)
    (f : Nat → Nat) (J : Nat) (writes : Nat → Prop),
    ¬ (10 ≤ (count : Nat) ∧ (count : Nat) ≤ 16) → ¬ (10 ≤ (w : Nat) ∧ (w : Nat) ≤ 16) →
    ¬ writes count → ¬ writes w → ¬ writes 2 → ¬ writes 9 → ¬ writes 14 →
    ∀ (s : State), s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 →
    s.regs count + 1 < 2 ^ W → s.regs w < 2 ^ W →
    s.extent + s.regs count * s.regs w < 2 ^ W →
    (∀ u, u.status = .running →
      (∀ r, ¬ writes r → ¬ (10 ≤ r ∧ r ≤ 16) → u.regs r = s.regs r) →
      (∀ a, a < s.extent → u.memory a = s.memory a) → s.extent ≤ u.extent → u.keys = s.keys →
      u.keyRegs = s.keyRegs → u.regs 14 < s.regs count →
      ∃ u' j, SafeEval W entry u u' j ∧ j ≤ J ∧ u'.status = .running ∧
        u'.regs 16 = f (u.regs 14) ∧ u'.regs 16 < 2 ^ W ∧ u'.memory = u.memory ∧
        u'.extent = u.extent ∧ (∀ r, ¬ writes r → r ≠ 16 → u'.regs r = u.regs r) ∧
        u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys) →
    ∃ s' k, SafeEval W (emitTable count w entry) s s' k ∧
      k ≤ s.regs count * (J + 7 * s.regs w + 7) + 3 ∧ s'.status = .running ∧
      Emits s s' ((flattenPayloadWords (((List.range (s.regs count)).map f).map
        (natToBitsLE (s.regs w)))).map bitToNat) ∧
      (∀ r, ¬ writes r → ¬ (10 ≤ r ∧ r ≤ 16) → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @emitTable_spec

theorem spec_log2Block : ∀ {W : Nat}, 32 ≤ W → ∀ (dst src : Operand),
    (dst : Nat) ≠ 2 → (dst : Nat) ≠ 9 → (dst : Nat) ≠ 20 → (dst : Nat) ≠ 21 →
    ∀ (s : State), s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs src < 2 ^ W →
    ∃ s' k, SafeEval W (log2Block dst src) s s' k ∧ k ≤ 5 * Nat.log2 (s.regs src) + 4 ∧
      s'.status = .running ∧ s'.regs dst = Nat.log2 (s.regs src) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧
      (∀ r : Nat, r ≠ (dst : Nat) → r ≠ 20 → r ≠ 21 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @log2Block_spec

theorem spec_Emits_def : ∀ (s₀ s : State) (vals : List Nat), Emits s₀ s vals ↔
    (s.extent = s₀.extent + vals.length ∧
      ∀ a, s.memory a = if s₀.extent ≤ a ∧ a < s₀.extent + vals.length
        then vals[a - s₀.extent]? else s₀.memory a) := fun _ _ _ => Iff.rfl

/-! ## Interior geometry subset and sparse-level tables -/

theorem spec_interiorGeometry : ∀ {W : Nat}, 32 ≤ W → ∀ (s : State) (n : Nat),
    s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = n →
    (n + 2) * (n + 2) * ((n + 2) * (n + 2)) < 2 ^ W →
    ∃ s' k, SafeEval W interiorGeometryBlock s s' k ∧ k ≤ 25 * W + 40 ∧ s'.status = .running ∧
      s'.regs 30 = Nat.log2 n + 1 ∧
      s'.regs 31 = (Nat.log2 n + 1) * (Nat.log2 n + 1) ∧
      s'.regs 32 = n / (Nat.log2 n + 1) ∧
      s'.regs 33 = n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1 ∧
      s'.regs 34 = bpSparseLevelDomain ((Nat.log2 n + 1) * (Nat.log2 n + 1)) ∧
      s'.regs 35 = bpSparseLevelDomain
        (n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1) ∧
      s'.regs 36 = bpSparseLevelWidth
        (bpSparseLevelDomain ((Nat.log2 n + 1) * (Nat.log2 n + 1))) ∧
      s'.regs 37 = bpSparseLevelWidth (bpSparseLevelDomain
        (n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1)) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧
      (∀ r : Nat, ¬ (20 ≤ r ∧ r ≤ 25) → ¬ (30 ≤ r ∧ r ≤ 37) → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @interiorGeometry_spec

theorem spec_localLevelTable_emits_payload : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape)
    (s : State), s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = shape.size →
    (shape.size + 2) * (shape.size + 2) * ((shape.size + 2) * (shape.size + 2)) < 2 ^ W →
    s.extent + bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize *
      bpSparseLevelWidth (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <
        2 ^ W →
    ∃ s' k, SafeEval W (.seq interiorGeometryBlock (levelTableBlock 34 36)) s s' k ∧
      s'.status = .running ∧
      Emits s s' ((canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload.map
        bitToNat) :=
  @localLevelTable_emits_payload

theorem spec_globalLevelTable_emits_payload : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape)
    (s : State), s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = shape.size →
    (shape.size + 2) * (shape.size + 2) * ((shape.size + 2) * (shape.size + 2)) < 2 ^ W →
    s.extent + bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount *
      bpSparseLevelWidth (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount) <
        2 ^ W →
    ∃ s' k, SafeEval W (.seq interiorGeometryBlock (levelTableBlock 35 37)) s s' k ∧
      s'.status = .running ∧
      Emits s s' ((canonicalRelativeRmmInteriorGlobalLevelTable shape).table.payload.map
        bitToNat) :=
  @globalLevelTable_emits_payload

/-! ## Executable smoke checks (structured evaluator, not kernel evaluation) -/

def smokeState (n : Nat) : State :=
  { regs := fun r => if r = 1 then n else 0, memory := fun _ => none, extent := 0,
    keys := fun _ => none, keyRegs := fun _ => 0, pc := 0, status := .running }

def smokeCells (b : Block) (n : Nat) : Option (List Nat) :=
  (evalF 100000 (.seq constantsBlock b) (smokeState n)).map fun r =>
    (List.range r.1.extent).map fun a => (r.1.memory a).getD 7

def stageGuard1 : Bool := smokeCells (.seq interiorGeometryBlock (levelTableBlock 34 36)) 0 ==
  some ((canonicalRelativeRmmInteriorLocalLevelTable (Cartesian.shape (List.replicate 0 0))).table.payload.map bitToNat)
def stageGuard2 : Bool := smokeCells (.seq interiorGeometryBlock (levelTableBlock 34 36)) 5 ==
  some ((canonicalRelativeRmmInteriorLocalLevelTable (Cartesian.shape (List.replicate 5 0))).table.payload.map bitToNat)
def stageGuard3 : Bool := smokeCells (.seq interiorGeometryBlock (levelTableBlock 34 36)) 24 ==
  some ((canonicalRelativeRmmInteriorLocalLevelTable (Cartesian.shape (List.replicate 24 0))).table.payload.map bitToNat)
def stageGuard4 : Bool := smokeCells (.seq interiorGeometryBlock (levelTableBlock 35 37)) 24 ==
  some ((canonicalRelativeRmmInteriorGlobalLevelTable (Cartesian.shape (List.replicate 24 0))).table.payload.map bitToNat)

/-! ## Register-only specifications, counted loops, arrays (S2 continuation) -/

theorem spec_RegSpec_def : ∀ (W : Nat) (b : Block) (pre : Registers → Prop)
    (F : Registers → Registers) (cost : Registers → Nat), RegSpec W b pre F cost ↔
    (∀ s : State, s.status = .running → pre s.regs →
      ∃ s' k, SafeEval W b s s' k ∧ k ≤ cost s.regs ∧ s'.status = .running ∧
        s'.regs = F s.regs ∧ s'.memory = s.memory ∧ s'.extent = s.extent ∧
        s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs) := fun _ _ _ _ _ => Iff.rfl

theorem spec_RegSpec_pure : ∀ {W : Nat}, 32 ≤ W → ∀ (ops : List Action),
    RegSpec W (acts ops) (pureOKs W ops) (pureRegs ops) (fun _ => ops.length) :=
  @RegSpec.pure

theorem spec_RegSpec_log2 : ∀ {W : Nat}, 32 ≤ W → ∀ (dst src : Operand),
    (dst : Nat) ≠ 2 → (dst : Nat) ≠ 9 → (dst : Nat) ≠ 20 → (dst : Nat) ≠ 21 →
    RegSpec W (log2Block dst src) (fun r => r 2 = 1 ∧ r 9 = 2 ∧ r src < 2 ^ W)
      (fun r => put (put (put r 20 (r src / 2 ^ Nat.log2 (r src))) 21 0) dst
        (Nat.log2 (r src)))
      (fun r => 5 * Nat.log2 (r src) + 4) :=
  @RegSpec.log2

theorem spec_forSlots : ∀ {W : Nat}, 32 ≤ W → ∀ (i go cnt : Operand) (body : Block) (J : Nat),
    (i : Nat) ≠ go → (i : Nat) ≠ cnt → (go : Nat) ≠ cnt → (i : Nat) ≠ 2 → (go : Nat) ≠ 2 →
    ∀ (Inv : Nat → State → Prop) (s : State), s.status = .running → s.regs 2 = 1 →
    s.regs cnt < 2 ^ W →
    (∀ u : State, u.status = .running → (∀ r : Nat, r ≠ i → r ≠ go → u.regs r = s.regs r) →
      u.memory = s.memory → u.extent = s.extent → u.keys = s.keys → u.keyRegs = s.keyRegs →
      Inv 0 u) →
    (∀ k (u : State), k < s.regs cnt → Inv k u → u.status = .running → u.regs i = k →
      u.regs cnt = s.regs cnt → u.regs 2 = 1 →
      ∃ u' j, SafeEval W body u u' j ∧ j ≤ J ∧ u'.status = .running ∧ u'.regs i = k ∧
        u'.regs cnt = s.regs cnt ∧ u'.regs 2 = 1 ∧
        ∀ v : State, v.status = .running →
          (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u'.regs r) →
          v.memory = u'.memory → v.extent = u'.extent → v.keys = u'.keys →
          v.keyRegs = u'.keyRegs → Inv (k + 1) v) →
    ∃ s' k, SafeEval W (forSlots i go cnt body) s s' k ∧ k ≤ s.regs cnt * (J + 4) + 3 ∧
      s'.status = .running ∧ Inv (s.regs cnt) s' ∧ s'.regs i = s.regs cnt ∧
      s'.regs cnt = s.regs cnt :=
  @forSlots_spec

theorem spec_reserveArray : ∀ {W : Nat}, 32 ≤ W → ∀ (base cnt : Operand),
    (base : Nat) ≠ 0 → (base : Nat) ≠ 2 → (base : Nat) ≠ 10 → (base : Nat) ≠ 12 →
    (cnt : Nat) ≠ base →
    ∀ (s : State), s.status = .running → s.regs 0 = 0 → s.regs 2 = 1 →
    s.extent + s.regs cnt + 1 < 2 ^ W →
    ∃ s' k, SafeEval W (reserveArray base cnt) s s' k ∧ k ≤ 5 * s.regs cnt + 4 ∧
      s'.status = .running ∧ Emits s s' (List.replicate (s.regs cnt + 1) 0) ∧
      s'.regs base = s.extent ∧
      (∀ r : Nat, r ≠ base → r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @reserveArray_spec

theorem spec_emitFlatMap : ∀ {W : Nat}, 32 ≤ W → ∀ (i go cnt : Operand) (body : Block) (J : Nat)
    (g : Nat → List Nat) (Keep : State → Prop),
    (i : Nat) ≠ go → (i : Nat) ≠ cnt → (go : Nat) ≠ cnt → (i : Nat) ≠ 2 → (go : Nat) ≠ 2 →
    ∀ (s : State), s.status = .running → s.regs 2 = 1 → s.regs cnt < 2 ^ W →
    (∀ u : State, u.status = .running → (∀ r : Nat, r ≠ i → r ≠ go → u.regs r = s.regs r) →
      u.memory = s.memory → u.extent = s.extent → u.keys = s.keys → u.keyRegs = s.keyRegs →
      Keep u) →
    (∀ u v : State, Keep u → (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u.regs r) →
      v.memory = u.memory → v.extent = u.extent → v.keys = u.keys → v.keyRegs = u.keyRegs →
      Keep v) →
    (∀ k (u : State), k < s.regs cnt → Keep u → u.status = .running → u.regs i = k →
      u.regs cnt = s.regs cnt → u.regs 2 = 1 →
      ∃ u' j, SafeEval W body u u' j ∧ j ≤ J ∧ u'.status = .running ∧ u'.regs i = k ∧
        u'.regs cnt = s.regs cnt ∧ u'.regs 2 = 1 ∧ Emits u u' (g k) ∧ Keep u') →
    ∃ s' k, SafeEval W (forSlots i go cnt body) s s' k ∧ k ≤ s.regs cnt * (J + 4) + 3 ∧
      s'.status = .running ∧ Emits s s' ((List.range (s.regs cnt)).flatMap g) ∧ Keep s' :=
  @emitFlatMap_spec

/-! ## The geometry bank -/

/-- Independently written identity of every bank register. -/
theorem spec_geoVal_pins : ∀ n : Nat,
    geoVal n 0 = 2 * n ∧ geoVal n 1 = SuccinctFinal.PackedCellProbe.packedRankWordSize n ∧
    geoVal n 2 = GenericSelect.superStride (2 * n) ∧ geoVal n 3 = GenericSelect.ell (2 * n) ∧
    geoVal n 4 = GenericSelect.localStride (2 * n) ∧
    geoVal n 5 = GenericSelect.localSlotsPerSuper (2 * n) ∧
    geoVal n 6 = GenericSelect.superLongSpan (2 * n) ∧
    geoVal n 7 = SuccinctFinal.PackedCellProbe.packedSuperSlots n ∧
    geoVal n 8 = SuccinctFinal.PackedCellProbe.packedLocalSlots n ∧
    geoVal n 9 = SuccinctFinal.PackedCellProbe.packedSparseSlots n ∧
    geoVal n 10 = SuccinctFinal.PackedCellProbe.packedRankBlockWidth n ∧
    geoVal n 11 = SuccinctFinal.PackedCellProbe.packedLocalWidth n ∧
    geoVal n 12 = SuccinctFinal.PackedCellProbe.packedLongFlagWordSize n ∧
    geoVal n 13 = SuccinctFinal.PackedCellProbe.packedSparseWordSize n ∧
    geoVal n 14 = SuccinctFinal.PackedCellProbe.packedRankSuperSlots n ∧
    geoVal n 15 = SuccinctFinal.PackedCellProbe.packedRankBlockSlots n ∧
    geoVal n 16 = SuccinctFinal.PackedCellProbe.packedLongFlagRankSlots n ∧
    geoVal n 17 = SuccinctFinal.PackedCellProbe.packedSparseRankSlots n ∧
    geoVal n 18 = 2 * (Nat.log2 n + 1) ∧
    geoVal n 19 = n / (Nat.log2 n + 1) / (Nat.log2 n + 1) + 1 ∧
    geoVal n 20 = SuccinctRank.machineWordBits ((Nat.log2 n + 1) * (Nat.log2 n + 1)) ∧
    geoVal n 21 = SuccinctRank.machineWordBits
      (n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1) ∧
    geoVal n 22 = SuccinctRank.machineWordBits (n / (Nat.log2 n + 1)) ∧
    geoVal n 23 = 2 * (Nat.log2 (Nat.log2 n + 1) + 1) + 3 ∧
    geoVal n 26 = bpFringeChunkBits (2 * n) ∧
    geoVal n 27 = bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) ∧
    geoVal n 28 = bpFringeChunkEntryWidth (bpFringeChunkBits (2 * n)) ∧
    geoVal n 29 = bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) ∧
    geoVal n 30 = bpChunkSelectEntryWidth (bpFringeChunkBits (2 * n)) ∧
    geoVal n 31 = canonicalRelativeRmmInteriorRawPayloadOverhead n ∧
    geoVal n 32 = bpFringeTableOverhead n ∧ geoVal n 33 = bpChunkSelectTableOverhead n ∧
    geoVal n 36 = SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead n ∧
    geoVal n 37 = SuccinctFinal.PackedCellProbe.packedReviewerCellWidth n ∧
    geoVal n 38 = SuccinctFinal.PackedWordRAM.wordWidth n := fun _ =>
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem spec_GeoUpTo_def : ∀ (n k : Nat) (r : Registers),
    GeoUpTo n k r ↔ ∀ i, i < k → r (38 + i) = geoVal n i := fun _ _ _ => Iff.rfl

theorem spec_GeoBase_def : ∀ (n : Nat) (r : Registers), GeoBase n r ↔
    (r 1 = n ∧ r 2 = 1 ∧ r 9 = 2 ∧ r 30 = Nat.log2 n + 1 ∧
      r 31 = (Nat.log2 n + 1) * (Nat.log2 n + 1) ∧ r 32 = n / (Nat.log2 n + 1) ∧
      r 33 = n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1 ∧
      r 34 = bpSparseLevelDomain ((Nat.log2 n + 1) * (Nat.log2 n + 1)) ∧
      r 35 = bpSparseLevelDomain
        (n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1) ∧
      r 36 = bpSparseLevelWidth (bpSparseLevelDomain ((Nat.log2 n + 1) * (Nat.log2 n + 1))) ∧
      r 37 = bpSparseLevelWidth (bpSparseLevelDomain
        (n / (Nat.log2 n + 1) / ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1))) :=
  fun _ _ => Iff.rfl

theorem geometryPrelude_def :
    geometryPrelude = .seq interiorGeometryBlock (geoChain 39) := rfl

theorem geoStepBlock_36_def : geoStepBlock 36 =
    .seq (.action (.constant 26 1180)) (.seq (.action (.arithmetic .mul 26 26 72))
      (.seq (.action (.constant 27 513)) (.seq (.action (.arithmetic .mul 27 27 73))
        (.seq (.action (.arithmetic .add 26 26 27)) (.seq (.action (.constant 27 561))
          (.action (.arithmetic .add 74 26 27))))))) := rfl

theorem spec_geometryPrelude : ∀ {W n : Nat}, 32 ≤ W → 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W →
    ∀ (s : State), s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = n →
    ∃ s' k, SafeEval W geometryPrelude s s' k ∧ k ≤ 25 * W + 40 + 39 * (5 * W + 20) ∧
      s'.status = .running ∧ GeoBase n s'.regs ∧ GeoUpTo n 39 s'.regs ∧
      (∀ x : Nat, ¬ (20 ≤ x ∧ x ≤ 28) → ¬ (30 ≤ x ∧ x ≤ 76) → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧
      s'.keyRegs = s.keyRegs :=
  @geometryPrelude_spec

theorem spec_geoChain : ∀ {W n : Nat}, 32 ≤ W → 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W →
    ∀ k, k ≤ 39 → ∀ s : State, s.status = .running → GeoBase n s.regs →
    ∃ s' j, SafeEval W (geoChain k) s s' j ∧ j ≤ k * (5 * W + 20) ∧ s'.status = .running ∧
      GeoBase n s'.regs ∧ GeoUpTo n k s'.regs ∧
      (∀ x : Nat, ¬ (20 ≤ x ∧ x ≤ 28) → ¬ (38 ≤ x ∧ x < 38 + k) → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs :=
  @geoChain_spec

/-! ## Executable smoke checks of the geometry prelude (structured evaluator) -/

def geoSmoke (n : Nat) : Bool :=
  match evalF 1000000 (.seq constantsBlock geometryPrelude) (smokeState n) with
  | none => false
  | some (u, _) =>
      (List.range 39).all (fun i => u.regs (38 + i) == geoVal n i) &&
      u.regs 30 == Nat.log2 n + 1 && u.regs 33 == n / (Nat.log2 n + 1) /
        ((Nat.log2 n + 1) * (Nat.log2 n + 1)) + 1

def stageGuard5 : Bool := geoSmoke 0
def stageGuard6 : Bool := geoSmoke 1
def stageGuard7 : Bool := geoSmoke 7
def stageGuard8 : Bool := geoSmoke 24
def stageGuard9 : Bool := geoSmoke 1000

/-! ## Stage S3: leaves, spine laws, stack pass and BP emission -/

theorem keyLeaf_def : keyLeaf =
    .seq (.action (.loadKey 0 4)) (.seq (.action (.loadKey 1 5))
      (.seq (.action (.compareKey 6 0 1)) (.seq (.action (.move 6 6))
        (.action (.move 6 6))))) := rfl

theorem wordLeaf_def : wordLeaf =
    .seq (.action (.arithmetic .add 7 4 2)) (.seq (.action (.load 7 7))
      (.seq (.action (.arithmetic .add 8 5 2)) (.seq (.action (.load 8 8))
        (.action (.comparison .lt 6 7 8))))) := rfl

theorem spec_KeySpec_def : ∀ (W : Nat) (xs : List Int) (Inp : State → Prop) (leaf : Block),
    KeySpec W xs Inp leaf ↔
    (∀ u : State, u.status = .running → Inp u → u.regs 2 = 1 →
      u.regs 4 < xs.length → u.regs 5 < xs.length →
      ∃ u', SafeEval W leaf u u' 5 ∧ u'.status = .running ∧
        u'.regs 6 = (if xs.getD (u.regs 4) 0 < xs.getD (u.regs 5) 0 then 1 else 0) ∧
        (∀ r : Nat, r ≠ 6 → r ≠ 7 → r ≠ 8 → u'.regs r = u.regs r) ∧
        u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys) :=
  fun _ _ _ _ => Iff.rfl

theorem spec_OracleInput_def : ∀ (xs : List Int) (u : State),
    OracleInput xs u ↔ u.keys = fun i => xs[i]? := fun _ _ => Iff.rfl

theorem spec_WordInput_def : ∀ (W : Nat) (xs : List Int) (u : State),
    WordInput W xs u ↔ (InputFits W xs ∧ xs.length + 1 ≤ u.extent ∧
      ∀ k, k < xs.length → u.memory (k + 1) = some (encodeInt W (xs.getD k 0))) :=
  fun _ _ _ => Iff.rfl

theorem spec_keyLeaf : ∀ {W : Nat}, 32 ≤ W → ∀ (xs : List Int),
    KeySpec W xs (OracleInput xs) keyLeaf := @keyLeaf_spec

theorem spec_wordLeaf : ∀ {W : Nat}, 32 ≤ W → ∀ (xs : List Int),
    KeySpec W xs (WordInput W xs) wordLeaf := @wordLeaf_spec

open Spec Spec.StackCartesianTreeSpec in
theorem spec_spineFrom_insertRight : ∀ (t : StackCartesianTree) (v : Int) (o : Nat),
    spineFrom (t.insertRight v) o =
      (spineFrom t o).takeWhile (fun e => !popsFor v e) ++
        [(o + t.shape.size, ((spineFrom t o).find? (popsFor v)).elim (o + t.shape.size) (·.2.1),
          v)] := spineFrom_insertRight

open Spec Spec.StackCartesianTreeSpec in
theorem spec_insertPoint_eq_find : ∀ (t : StackCartesianTree) (v : Int) (o : Nat),
    (insertPoint t v).map (o + ·) = ((spineFrom t o).find? (popsFor v)).map (·.2.1) :=
  insertPoint_eq_find

open Spec Spec.StackCartesianTreeSpec in
theorem spec_spineFrom_sorted : ∀ {t : StackCartesianTree}, t.Valid → ∀ (o : Nat),
    (spineFrom t o).Pairwise (fun a b => a.2.2 ≤ b.2.2) := @spineFrom_sorted

open Spec Spec.StackCartesianTreeSpec in
theorem spec_openCounts_sum : ∀ (T : CartesianShape), (openCounts T).sum = T.size :=
  openCounts_sum

theorem spec_cartesianBP_key : ∀ {W : Nat}, 32 ≤ W → ∀ (xs : List Int) (s : State),
    s.status = .running → s.regs 0 = 0 → s.regs 2 = 1 → s.regs 1 = xs.length →
    s.keys = (fun i => xs[i]?) →
    s.extent + 3 * (xs.length + 1) + 2 * xs.length + 2 < 2 ^ W →
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock keyLeaf) bpEmitBlock)) s s' k ∧
      k ≤ 79 * xs.length + 19 ∧ s'.status = .running ∧
      s'.extent = s.extent + 3 * (xs.length + 1) + 2 * xs.length ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧
      (∀ a, a < 2 * xs.length → s'.memory (s.extent + 3 * (xs.length + 1) + a) =
        some (((Cartesian.shape xs).bpCode.map bitToNat).getD a 0)) ∧
      (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 10 → r ≠ 12 → ¬ (100 ≤ r ∧ r ≤ 114) →
        s'.regs r = s.regs r) ∧
      s'.keys = s.keys :=
  @cartesianBP_key

theorem spec_cartesianBP_word : ∀ {W : Nat}, 32 ≤ W → ∀ (xs : List Int) (s : State),
    s.status = .running → s.regs 0 = 0 → s.regs 2 = 1 → s.regs 1 = xs.length →
    WordInput W xs s →
    s.extent + 3 * (xs.length + 1) + 2 * xs.length + 2 < 2 ^ W →
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock wordLeaf) bpEmitBlock)) s s' k ∧
      k ≤ 79 * xs.length + 19 ∧ s'.status = .running ∧
      s'.extent = s.extent + 3 * (xs.length + 1) + 2 * xs.length ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧
      (∀ a, a < 2 * xs.length → s'.memory (s.extent + 3 * (xs.length + 1) + a) =
        some (((Cartesian.shape xs).bpCode.map bitToNat).getD a 0)) ∧
      (∀ r : Nat, ¬ (4 ≤ r ∧ r ≤ 8) → r ≠ 10 → r ≠ 12 → ¬ (100 ≤ r ∧ r ≤ 114) →
        s'.regs r = s.regs r) ∧
      s'.keys = s.keys :=
  @cartesianBP_word

/-! ## Executable S3 fixtures (array-backed interpreter on the compiled source) -/

def s3Program (leaf : Block) : Array BInstr :=
  ((Block.seq (.action (.load 1 0)) (.seq constantsBlock (.seq stackArraysBlock
    (.seq (stackPassBlock leaf) bpEmitBlock)))).compileAt 0 ++ [(⟨.halt 3⟩ : BInstr)]).toArray

def s3Cells (r : ArrayRun) (base : Nat) : List Nat :=
  (List.range (r.final.memory.size - base)).map fun k => (r.final.memory.getD (base + k) none).getD 7

def s3Key (xs : List Int) : Bool :=
  let r := runArray (s3Program keyLeaf) 1000000 (ExecState.ofComparisonInput 200 xs)
  r.final.status == .halted 0 &&
    s3Cells r (1 + 3 * (xs.length + 1)) == (Cartesian.shape xs).bpCode.map bitToNat

def s3Word (xs : List Int) : Bool :=
  let r := runArray (s3Program wordLeaf) 1000000 (ExecState.ofWordInput 200 64 xs)
  r.final.status == .halted 0 &&
    s3Cells r (xs.length + 1 + 3 * (xs.length + 1)) == (Cartesian.shape xs).bpCode.map bitToNat

def stageGuard10 : Bool := s3Key [] && s3Word []
def stageGuard11 : Bool := s3Key [7] && s3Word [7]
def stageGuard12 : Bool := s3Key [4, -3, -3, 8] && s3Word [4, -3, -3, 8]
def stageGuard13 : Bool := s3Key [1, 1, 1, 1] && s3Word [1, 1, 1, 1]
def stageGuard14 : Bool := s3Key [1, 2, 3, 4, 5] && s3Word [5, 4, 3, 2, 1]
def stageGuard15 : Bool := s3Key [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] && s3Word [2, 2, 1, 1, 3, 3, 0, 0]
-- `crossBlockInput` of `RMQ.Validation.PackedQueryRuntime`, restated literally
def stageGuard16 : Bool := s3Key [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9] && s3Word [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

/-! ## Stage S4 checkpoint: block statistics and the four summary tables -/

theorem maxActs_def : ∀ (dst a b : Operand), maxActs dst a b =
    [.comparison .lt 26 a b, .arithmetic .sub 27 2 26, .arithmetic .mul 28 26 b,
      .arithmetic .mul 27 27 a, .arithmetic .add dst 28 27] := fun _ _ _ => rfl

theorem blockStatsBlock_def : blockStatsBlock =
    .seq (acts [.constant 120 0, .arithmetic .add 134 56 2])
      (.seq (forSlots 121 122 32 blockBodyBlock)
        (acts [.arithmetic .add 108 115 32, .store 108 120])) := rfl

theorem summaryTablesBlock_def : summaryTablesBlock =
    .seq (acts [.arithmetic .mul 133 30 56])
      (.seq (emitTable 57 39 baselineEntryBlock)
      (.seq (emitTable 32 61 (relativeEntryBlock 116))
      (.seq (emitTable 32 61 (relativeEntryBlock 117))
        (emitTable 32 61 argOffsetEntryBlock)))) := rfl

theorem relativeEntryBlock_def : ∀ (statBase : Operand), relativeEntryBlock statBase =
    acts [.arithmetic .div 131 14 30, .arithmetic .mul 131 131 30,
      .arithmetic .add 108 115 131, .load 132 108,
      .arithmetic .add 108 statBase 14, .load 16 108,
      .arithmetic .add 16 16 133, .arithmetic .sub 16 16 132] := fun _ => rfl

theorem spec_argStep_def : ∀ (shape : CartesianShape) (p best : Nat),
    Spec.argStep shape p best =
      if bpExcessAt shape (Nat.min p shape.bpCode.length) < bpExcessAt shape best then
        Nat.min p shape.bpCode.length else best := fun _ _ _ => rfl

theorem spec_bpBlockArgMinPrefixPosFrom_eq_argAcc : ∀ (shape : CartesianShape)
    (steps pos best : Nat),
    bpBlockArgMinPrefixPosFrom shape pos steps best = Spec.argAcc shape pos steps best :=
  Spec.bpBlockArgMinPrefixPosFrom_eq_argAcc

theorem spec_natListMinFrom_append_singleton : ∀ (seed : Nat) (L : List Nat) (x : Nat),
    natListMinFrom seed (L ++ [x]) = Nat.min (natListMinFrom seed L) x :=
  Spec.natListMinFrom_append_singleton

theorem spec_natListMax_append_singleton : ∀ (L : List Nat) (x : Nat),
    natListMax (L ++ [x]) = Nat.max (natListMax L) x :=
  Spec.natListMax_append_singleton

theorem spec_argAcc_ge : ∀ (shape : CartesianShape) (start : Nat),
    start ≤ shape.bpCode.length → ∀ (k : Nat), start ≤ Spec.argAcc shape start k start :=
  Spec.argAcc_ge

theorem spec_bpCell_def : ∀ (shape : CartesianShape) (k : Nat),
    bpCell shape k = (shape.bpCode.map bitToNat).getD k 0 := fun _ _ => rfl

theorem spec_SampleFrame_def : ∀ r : Nat, SampleFrame r ↔
    (¬ (26 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ r ≠ 120 ∧ r ≠ 123 ∧ r ≠ 124 ∧ ¬ (125 ≤ r ∧ r ≤ 131)) :=
  fun _ => Iff.rfl

theorem spec_StatsFrame_def : ∀ r : Nat, StatsFrame r ↔
    (SampleFrame r ∧ r ≠ 121 ∧ r ≠ 122 ∧ r ≠ 134) := fun _ => Iff.rfl

theorem spec_SummaryFrame_def : ∀ r : Nat, SummaryFrame r ↔
    (¬ (10 ≤ r ∧ r ≤ 16) ∧ r ≠ 108 ∧ r ≠ 131 ∧ r ≠ 132 ∧ r ≠ 133) := fun _ => Iff.rfl

theorem spec_Region_def : ∀ (u : State) (e0 len : Nat) (M : Nat → Nat),
    Region u e0 len M ↔ ∀ a, a < len → u.memory (e0 + a) = some (M a) := fun _ _ _ _ => Iff.rfl

theorem spec_sampleLoop : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape) (s : State),
    s.status = .running → s.regs 2 = 1 → ∀ (B : Nat), s.regs 119 = B →
    Region s B shape.bpCode.length (bpCell shape) →
    B + shape.bpCode.length ≤ s.extent → B + 4 * shape.bpCode.length + 4 < 2 ^ W →
    ∀ (bs blk : Nat), s.regs 56 = bs → s.regs 134 = bs + 1 →
    blk * bs + bs ≤ shape.bpCode.length →
    s.regs 129 = blk * bs → s.regs 120 = bpExcessAt shape (blk * bs) →
    s.regs 125 = shape.bpCode.length → s.regs 126 = 0 →
    s.regs 127 = blk * bs → s.regs 128 = bpExcessAt shape (blk * bs) →
    ∃ s' j, SafeEval W (forSlots 123 124 134 sampleBodyBlock) s s' j ∧
      j ≤ (bs + 1) * 28 + 3 ∧ s'.status = .running ∧
      s'.regs 125 = bpBlockMinExcess shape bs blk ∧
      s'.regs 126 = bpBlockMaxExcess shape bs blk ∧
      s'.regs 127 = bpBlockArgMinPrefixPos shape bs blk ∧
      s'.regs 120 = bpExcessAt shape (blk * bs + bs) ∧
      (∀ r : Nat, SampleFrame r → s'.regs r = s.regs r) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys :=
  @sampleLoop_spec

theorem spec_blockBody : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape) (u : State),
    u.status = .running → u.regs 2 = 1 →
    ∀ (A0 A1 A2 A3 B bs bc blk : Nat), u.regs 115 = A0 → u.regs 116 = A1 →
    u.regs 117 = A2 → u.regs 118 = A3 → u.regs 119 = B →
    u.regs 121 = blk → u.regs 56 = bs → u.regs 134 = bs + 1 →
    u.regs 38 = shape.bpCode.length → u.regs 120 = bpExcessAt shape (blk * bs) →
    Region u B shape.bpCode.length (bpCell shape) →
    B + shape.bpCode.length ≤ u.extent → B + 4 * shape.bpCode.length + 4 < 2 ^ W →
    u.extent < 2 ^ W → blk < bc → bc * bs ≤ shape.bpCode.length →
    A0 + bc + 1 ≤ A1 → A1 + bc ≤ A2 → A2 + bc ≤ A3 → A3 + bc ≤ B →
    ∃ u' j, SafeEval W blockBodyBlock u u' j ∧ j ≤ (bs + 1) * 28 + 16 ∧ u'.status = .running ∧
      u'.memory = put (put (put (put u.memory (A0 + blk) (some (bpExcessAt shape (blk * bs))))
        (A1 + blk) (some (bpBlockMinExcess shape bs blk)))
        (A2 + blk) (some (bpBlockMaxExcess shape bs blk)))
        (A3 + blk) (some (bpBlockArgMinPrefixPos shape bs blk)) ∧
      u'.regs 120 = bpExcessAt shape (blk * bs + bs) ∧
      (∀ r : Nat, SampleFrame r → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys :=
  @blockBody_spec

theorem spec_blockStats : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape) (s : State),
    s.status = .running → s.regs 2 = 1 →
    ∀ (A0 A1 A2 A3 B bs bc : Nat), s.regs 115 = A0 → s.regs 116 = A1 →
    s.regs 117 = A2 → s.regs 118 = A3 → s.regs 119 = B →
    s.regs 56 = bs → s.regs 32 = bc → s.regs 38 = shape.bpCode.length →
    Region s B shape.bpCode.length (bpCell shape) →
    B + shape.bpCode.length ≤ s.extent → B + 4 * shape.bpCode.length + 4 < 2 ^ W →
    s.extent < 2 ^ W → bs + 1 < 2 ^ W → bc * bs ≤ shape.bpCode.length →
    A0 + bc + 1 ≤ A1 → A1 + bc ≤ A2 → A2 + bc ≤ A3 → A3 + bc ≤ B →
    ∃ s' j, SafeEval W blockStatsBlock s s' j ∧ j ≤ bc * ((bs + 1) * 28 + 20) + 7 ∧
      s'.status = .running ∧
      (∀ b, b ≤ bc → s'.memory (A0 + b) = some (bpExcessAt shape (b * bs))) ∧
      (∀ b, b < bc → s'.memory (A1 + b) = some (bpBlockMinExcess shape bs b)) ∧
      (∀ b, b < bc → s'.memory (A2 + b) = some (bpBlockMaxExcess shape bs b)) ∧
      (∀ b, b < bc → s'.memory (A3 + b) = some (bpBlockArgMinPrefixPos shape bs b)) ∧
      (∀ a, (a < A0 ∨ A3 + bc ≤ a) → s'.memory a = s.memory a) ∧
      (∀ r : Nat, StatsFrame r → r ≠ 108 → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys :=
  @blockStats_spec

theorem spec_baselineEntry : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape) (u : State),
    u.status = .running → ∀ (bps bs A0 bc slot : Nat),
    u.regs 14 = slot → u.regs 30 = bps → u.regs 115 = A0 →
    slot * bps ≤ bc → A0 + bc < u.extent → A0 + bc < 2 ^ W →
    shape.bpCode.length < 2 ^ W →
    u.memory (A0 + slot * bps) = some (bpExcessAt shape (slot * bps * bs)) →
    ∃ u' j, SafeEval W baselineEntryBlock u u' j ∧ j ≤ 3 ∧ u'.status = .running ∧
      u'.regs 16 = bpExcessAt shape (blockStartOf bs (slot * bps)) ∧ u'.regs 16 < 2 ^ W ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 131 → r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @baselineEntry_spec

theorem spec_relativeEntry : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape) (statBase : Operand),
    (statBase : Nat) ≠ 131 → (statBase : Nat) ≠ 132 → (statBase : Nat) ≠ 108 →
    ∀ (u : State), u.status = .running → ∀ (bps bs A0 S bc slot value : Nat),
    u.regs 14 = slot → u.regs 30 = bps → u.regs 115 = A0 →
    u.regs statBase = S → u.regs 133 = bps * bs → 0 < bps →
    slot < bc → A0 + bc < u.extent → S + bc ≤ u.extent →
    A0 + bc < 2 ^ W → S + bc < 2 ^ W → shape.bpCode.length + bps * bs < 2 ^ W →
    value ≤ shape.bpCode.length →
    u.memory (A0 + slot / bps * bps) = some (bpExcessAt shape (slot / bps * bps * bs)) →
    u.memory (S + slot) = some value →
    bpExcessAt shape (bpSuperblockStartPos bs bps slot) ≤ value + bpSuperblockSpan bs bps →
    ∃ u' j, SafeEval W (relativeEntryBlock statBase) u u' j ∧ j ≤ 8 ∧ u'.status = .running ∧
      u'.regs 16 = bpRelativeExcessEntry shape bs bps slot value ∧ u'.regs 16 < 2 ^ W ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 131 → r ≠ 132 → r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @relativeEntry_spec

theorem spec_argOffsetEntry : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape) (u : State),
    u.status = .running → ∀ (bs A3 bc slot : Nat),
    u.regs 14 = slot → u.regs 56 = bs → u.regs 118 = A3 →
    slot < bc → A3 + bc ≤ u.extent → A3 + bc < 2 ^ W →
    bc * bs ≤ shape.bpCode.length → shape.bpCode.length < 2 ^ W →
    u.memory (A3 + slot) = some (bpBlockArgMinPrefixPos shape bs slot) →
    ∃ u' j, SafeEval W argOffsetEntryBlock u u' j ∧ j ≤ 4 ∧ u'.status = .running ∧
      u'.regs 16 = bpBlockArgMinLocalOffset shape bs slot ∧ u'.regs 16 < 2 ^ W ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 131 → r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @argOffsetEntry_spec

theorem spec_summaryTables : ∀ {W : Nat}, 32 ≤ W → ∀ (shape : CartesianShape) (s : State),
    s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 →
    ∀ (A0 A1 A2 A3 bps bs bc ssc sw rw : Nat),
    s.regs 115 = A0 → s.regs 116 = A1 → s.regs 117 = A2 → s.regs 118 = A3 →
    s.regs 30 = bps → s.regs 56 = bs → s.regs 32 = bc → s.regs 57 = ssc →
    s.regs 39 = sw → s.regs 61 = rw →
    0 < bps → ssc = bc / bps + 1 → bc * bs ≤ shape.bpCode.length →
    A0 + bc + 1 ≤ A1 → A1 + bc ≤ A2 → A2 + bc ≤ A3 → A3 + bc ≤ s.extent →
    bc + 2 < 2 ^ W → shape.bpCode.length + bps * bs < 2 ^ W →
    s.extent + ssc * sw + bc * rw + bc * rw + bc * rw < 2 ^ W →
    sw < 2 ^ W → rw < 2 ^ W →
    (∀ b, b ≤ bc → s.memory (A0 + b) = some (bpExcessAt shape (b * bs))) →
    (∀ b, b < bc → s.memory (A1 + b) = some (bpBlockMinExcess shape bs b)) →
    (∀ b, b < bc → s.memory (A2 + b) = some (bpBlockMaxExcess shape bs b)) →
    (∀ b, b < bc → s.memory (A3 + b) = some (bpBlockArgMinPrefixPos shape bs b)) →
    ∃ s' j, SafeEval W summaryTablesBlock s s' j ∧
      j ≤ ssc * (7 * sw + 10) + bc * (21 * rw + 41) + 13 ∧ s'.status = .running ∧
      Emits s s' ((Spec.tableBits (bpSuperblockBaselineEntries shape bs bps ssc) sw ++
        Spec.tableBits (bpBlockRelativeMinExcessEntries shape bs bps bc) rw ++
        Spec.tableBits (bpBlockRelativeMaxExcessEntries shape bs bps bc) rw ++
        Spec.tableBits (bpBlockArgMinLocalOffsetEntries shape bs bc) rw).map bitToNat) ∧
      (∀ r : Nat, SummaryFrame r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @summaryTables_spec

theorem spec_tableBits_def : ∀ (entries : List Nat) (width : Nat),
    Spec.tableBits entries width = flattenPayloadWords (entries.map (natToBitsLE width)) :=
  fun _ _ => rfl

/-! ## Executable S4 fixtures (array-backed interpreter on the compiled source)

The harness reserves the four statistics arrays with `reserveArray` (one cell
more than `blockCount` each) before the stack pass, records the BP base in
register 119 and a marker in register 199 after the BP segment, and then runs
`blockStatsBlock; summaryTablesBlock`. The cells after the marker are compared
with the first four interior segments of the emission plan. -/

def s4ArraysHarness : Block :=
  .seq (reserveArray 115 32) (.seq (reserveArray 116 32)
    (.seq (reserveArray 117 32) (reserveArray 118 32)))

def s4Program : Array BInstr :=
  ((Block.seq (.action (.load 1 0)) (.seq constantsBlock (.seq geometryPrelude
    (.seq stackArraysBlock (.seq s4ArraysHarness
    (.seq (stackPassBlock keyLeaf)
    (.seq (acts [.reserve 131, .arithmetic .add 119 131 2])
    (.seq bpEmitBlock
    (.seq (acts [.reserve 199, .arithmetic .add 199 199 2])
    (.seq blockStatsBlock summaryTablesBlock)))))))))).compileAt 0 ++
    [(⟨.halt 3⟩ : BInstr)]).toArray

def s4Summary (xs : List Int) : Bool :=
  let r := runArray s4Program 10000000 (ExecState.ofComparisonInput 200 xs)
  r.final.status == .halted 0 &&
    s3Cells r (r.final.regs.getD 199 0) ==
      (((Spec.interiorSegments (Cartesian.shape xs)).take 4).flatten).map bitToNat

def s4Input (n : Nat) : List Int :=
  (List.range n).map (fun i => ((i * 37 + 11) % 13 : Nat) - (6 : Int))

def stageGuard17 : Bool := [0, 1, 2, 3, 12, 24].all (fun n => s4Summary (s4Input n))
def stageGuard18 : Bool := [7, 9, 15, 17, 31, 33, 63, 65].all (fun n => s4Summary (s4Input n))
def stageGuard19 : Bool := s4Summary [1, 1, 1, 1] && s4Summary [4, -3, -3, 8]
-- `crossBlockInput` of `RMQ.Validation.PackedQueryRuntime`, restated literally
def stageGuard20 : Bool := s4Summary [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

/-! ## Stage S4 completion: sparse memos, sparse tables and the close segment -/

theorem betterActs_def : ∀ (dst x y : Operand), betterActs dst x y =
    [.arithmetic .add 108 116 x, .load 144 108, .arithmetic .add 108 116 y, .load 145 108,
      .comparison .lt 146 145 144, .arithmetic .sub 147 2 146, .arithmetic .mul 146 146 y,
      .arithmetic .mul 147 147 x, .arithmetic .add dst 146 147] := fun _ _ _ => rfl

theorem memoLevelsBlock_def : ∀ (base count scale levels : Operand),
    memoLevelsBlock base count scale levels =
      .seq (acts [.arithmetic .sub 148 levels 2])
        (forSlots 137 138 148
          (.seq (acts [.arithmetic .shl 141 2 137, .arithmetic .mul 146 137 count,
              .arithmetic .add 149 base 146, .arithmetic .add 150 149 count])
            (forSlots 139 140 count (memoCellBlock scale)))) := fun _ _ _ _ => rfl

theorem localMemoBlock_def : localMemoBlock =
    .seq (forSlots 139 140 32 (acts [.arithmetic .add 108 135 139, .store 108 139]))
      (memoLevelsBlock 135 32 2 58) := rfl

theorem globalMemoBlock_def : globalMemoBlock =
    .seq (forSlots 139 140 33 macroScanBlock) (memoLevelsBlock 136 33 31 59) := rfl

theorem interiorCloseBlock_def : interiorCloseBlock =
    .seq blockStatsBlock (.seq localMemoBlock (.seq globalMemoBlock
      (.seq summaryTablesBlock
      (.seq (emitTable 62 58 localEntryBlock)
      (.seq (emitTable 63 60 globalEntryBlock)
      (.seq (levelTableBlock 34 36) (levelTableBlock 35 37))))))) := rfl

theorem spec_CloseFrame_def : ∀ r : Nat, CloseFrame r ↔
    (¬ (10 ≤ r ∧ r ≤ 16) ∧ ¬ (20 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ ¬ (120 ≤ r ∧ r ≤ 134) ∧
      ¬ (137 ≤ r ∧ r ≤ 158)) := fun _ => Iff.rfl

theorem spec_interiorPayload_eq_segments : ∀ (shape : CartesianShape),
    (canonicalRelativeRmmInteriorDirectory shape).payload = (Spec.interiorSegments shape).flatten :=
  Spec.interiorPayload_eq_segments

section S4Completion

open RMQ.SuccinctFinal.PackedConstruction.Spec

theorem spec_argPos_excess_eq_min : ∀ (shape : CartesianShape) (bs b : Nat)
    (_ : b * bs + bs ≤ shape.bpCode.length),
    bpExcessAt shape (bpBlockArgMinPrefixPos shape bs b) = bpBlockMinExcess shape bs b :=
  @Spec.argPos_excess_eq_min

theorem spec_better_eq_min : ∀ (shape : CartesianShape) (bs x y : Nat)
    (_ : x * bs + bs ≤ shape.bpCode.length) (_ : y * bs + bs ≤ shape.bpCode.length),
    bpBetterArgMinBlock shape bs x y =
      if bpBlockMinExcess shape bs y < bpBlockMinExcess shape bs x then y else x :=
  @Spec.better_eq_min

theorem spec_rangeArgMin_snoc : ∀ (shape : CartesianShape) (bs st k : Nat),
    bpRangeArgMinBlock shape bs st (k + 2) =
      bpBetterArgMinBlock shape bs (bpRangeArgMinBlock shape bs st (k + 1)) (st + 1 + k) :=
  @Spec.rangeArgMin_snoc

theorem spec_globalMemo_double : ∀ (shape : CartesianShape) (bs M m l : Nat),
    bpRangeArgMinBlock shape bs (m * M) (2 ^ (l + 1) * M) =
      bpBetterArgMinBlock shape bs
        (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))
        (bpRangeArgMinBlock shape bs ((m + 2 ^ l) * M) (2 ^ l * M)) :=
  @Spec.globalMemo_double

theorem spec_memoCell : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (scale : Operand)
    (_ : (scale : Nat) ≠ 146)
    (u : State) (_ : u.status = .running) (_ : u.regs 2 = 1)
    (A1 bs bc S i h P C VX VY : Nat) (_ : u.regs 116 = A1) (_ : u.regs 32 = bc)
    (_ : u.regs scale = S) (_ : 1 ≤ S) (_ : u.regs 139 = i) (_ : u.regs 141 = h)
    (_ : u.regs 149 = P) (_ : u.regs 150 = C)
    (_ : (i + h + h) * S < 2 ^ W)
    (_ : A1 + bc ≤ u.extent) (_ : A1 + bc < 2 ^ W)
    (_ : bc * bs ≤ shape.bpCode.length) (_ : shape.bpCode.length < 2 ^ W)
    (_ : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b))
    (_ : (i + h + h) * S ≤ bc →
      u.memory (P + i) = some VX ∧ u.memory (P + (i + h)) = some VY ∧ VX < bc ∧ VY < bc ∧
        P + (i + h) < u.extent ∧ C + i < u.extent ∧ C + i < 2 ^ W ∧ P + (i + h) < 2 ^ W),
    ∃ u' j, SafeEval W (memoCellBlock scale) u u' j ∧ j ≤ 22 ∧ u'.status = .running ∧
      u'.memory = (if (i + h + h) * S ≤ bc then
        put u.memory (C + i) (some (bpBetterArgMinBlock shape bs VX VY)) else u.memory) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (142 ≤ r ∧ r ≤ 147) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @memoCell_spec

theorem spec_memoLevels : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape)
    (base count scale levels : Operand)
    (_ : (base : Nat) ≠ 108 ∧ ¬ (137 ≤ (base : Nat) ∧ (base : Nat) ≤ 150))
    (_ : (count : Nat) ≠ 108 ∧ ¬ (137 ≤ (count : Nat) ∧ (count : Nat) ≤ 150) ∧ (count : Nat) ≠ 2)
    (_ : (scale : Nat) ≠ 108 ∧ ¬ (137 ≤ (scale : Nat) ∧ (scale : Nat) ≤ 150))
    (u : State) (_ : u.status = .running) (_ : u.regs 2 = 1)
    (A1 bs bc Bm N S Lv : Nat) (V : Nat → Nat → Nat)
    (_ : u.regs 116 = A1) (_ : u.regs 32 = bc) (_ : u.regs base = Bm)
    (_ : u.regs count = N) (_ : u.regs scale = S) (_ : u.regs levels = Lv)
    (_ : 1 ≤ S) (_ : 1 ≤ Lv) (_ : Lv < W)
    (_ : Bm + Lv * N + (N + 2 ^ Lv) * S < 2 ^ W)
    (_ : Bm + Lv * N ≤ u.extent) (_ : A1 + bc ≤ Bm)
    (_ : bc * bs ≤ shape.bpCode.length) (_ : shape.bpCode.length < 2 ^ W)
    (_ : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b))
    (_ : ∀ l i, (i + 2 ^ (l + 1)) * S ≤ bc →
      V (l + 1) i = bpBetterArgMinBlock shape bs (V l i) (V l (i + 2 ^ l)))
    (_ : ∀ l i, (i + 2 ^ l) * S ≤ bc → V l i < bc)
    (_ : ∀ l i, (i + 2 ^ l) * S ≤ bc → i < N)
    (_ : ∀ i, (i + 1) * S ≤ bc → u.memory (Bm + i) = some (V 0 i)),
    ∃ u' j, SafeEval W (memoLevelsBlock base count scale levels) u u' j ∧
      j ≤ Lv * (26 * N + 11) + 4 ∧ u'.status = .running ∧
      (∀ l i, l < Lv → (i + 2 ^ l) * S ≤ bc → u'.memory (Bm + l * N + i) = some (V l i)) ∧
      (∀ a, (a < Bm + N ∨ Bm + Lv * N ≤ a) → u'.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 150) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @memoLevels_spec

theorem spec_localMemo : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1)
    (A1 bs bc Bm LC : Nat) (_ : u.regs 116 = A1) (_ : u.regs 32 = bc)
    (_ : u.regs 135 = Bm) (_ : u.regs 58 = LC) (_ : 1 ≤ LC) (_ : LC < W)
    (_ : Bm + LC * bc + (bc + 2 ^ LC) * 1 < 2 ^ W)
    (_ : Bm + LC * bc ≤ u.extent) (_ : u.extent < 2 ^ W) (_ : A1 + bc ≤ Bm)
    (_ : bc * bs ≤ shape.bpCode.length) (_ : shape.bpCode.length < 2 ^ W)
    (_ : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b)),
    ∃ u' j, SafeEval W localMemoBlock u u' j ∧ j ≤ bc * 6 + 3 + (LC * (26 * bc + 11) + 4) ∧
      u'.status = .running ∧
      (∀ l b, l < LC → b + 2 ^ l ≤ bc →
        u'.memory (Bm + l * bc + b) = some (bpRangeArgMinBlock shape bs b (2 ^ l))) ∧
      (∀ a, (a < Bm ∨ Bm + LC * bc ≤ a) → u'.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 150) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @localMemo_spec

theorem spec_macroScan : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1)
    (A1 bs bc M Gb m : Nat) (_ : u.regs 116 = A1) (_ : u.regs 32 = bc)
    (_ : u.regs 31 = M) (_ : u.regs 136 = Gb) (_ : u.regs 139 = m)
    (_ : 1 ≤ M) (_ : (m + 1) * M < 2 ^ W) (_ : A1 + bc ≤ u.extent) (_ : A1 + bc < 2 ^ W)
    (_ : u.extent < 2 ^ W)
    (_ : bc * bs ≤ shape.bpCode.length) (_ : shape.bpCode.length < 2 ^ W)
    (_ : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b))
    (_ : (m + 1) * M ≤ bc → Gb + m < u.extent ∧ Gb + m < 2 ^ W),
    ∃ u' j, SafeEval W macroScanBlock u u' j ∧ j ≤ 15 * M + 12 ∧ u'.status = .running ∧
      u'.memory = (if (m + 1) * M ≤ bc then
        put u.memory (Gb + m) (some (bpRangeArgMinBlock shape bs (m * M) M)) else u.memory) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (142 ≤ r ∧ r ≤ 147) → ¬ (151 ≤ r ∧ r ≤ 154) →
        u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @macroScan_spec

theorem spec_globalMemo : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1)
    (A1 bs bc Gb M mc GLC : Nat) (_ : u.regs 116 = A1) (_ : u.regs 32 = bc)
    (_ : u.regs 31 = M) (_ : u.regs 33 = mc) (_ : u.regs 136 = Gb) (_ : u.regs 59 = GLC)
    (_ : 1 ≤ M) (_ : mc = bc / M + 1) (_ : 1 ≤ GLC) (_ : GLC < W)
    (_ : Gb + GLC * mc + (mc + 2 ^ GLC) * M < 2 ^ W)
    (_ : Gb + GLC * mc ≤ u.extent) (_ : u.extent < 2 ^ W) (_ : A1 + bc ≤ Gb)
    (_ : bc * bs ≤ shape.bpCode.length) (_ : shape.bpCode.length < 2 ^ W)
    (_ : ∀ b, b < bc → u.memory (A1 + b) = some (bpBlockMinExcess shape bs b)),
    ∃ u' j, SafeEval W globalMemoBlock u u' j ∧
      j ≤ mc * (15 * M + 16) + 3 + (GLC * (26 * mc + 11) + 4) ∧ u'.status = .running ∧
      (∀ l m, l < GLC → (m + 2 ^ l) * M ≤ bc →
        u'.memory (Gb + l * mc + m) = some (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))) ∧
      (∀ a, (a < Gb ∨ Gb + GLC * mc ≤ a) → u'.memory a = u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (137 ≤ r ∧ r ≤ 154) → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @globalMemo_spec

theorem spec_localEntry : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1)
    (bs bc Bm M mc LC slot : Nat) (_ : u.regs 14 = slot) (_ : u.regs 58 = LC)
    (_ : u.regs 31 = M) (_ : u.regs 32 = bc) (_ : u.regs 135 = Bm)
    (_ : 1 ≤ M) (_ : 1 ≤ LC) (_ : LC < W) (_ : slot < mc * (LC * M))
    (_ : slot + LC * M + (mc + 1) * M + 2 ^ LC < 2 ^ W)
    (_ : Bm + LC * bc ≤ u.extent) (_ : Bm + LC * bc < 2 ^ W)
    (_ : ∀ l b, l < LC → b + 2 ^ l ≤ bc →
      u.memory (Bm + l * bc + b) = some (bpRangeArgMinBlock shape bs b (2 ^ l))),
    ∃ u' j, SafeEval W localEntryBlock u u' j ∧ j ≤ 21 ∧ u'.status = .running ∧
      u'.regs 16 = bpLocalSparseCellOffset shape bs bc M (slot / (LC * M))
        ((slot % (LC * M)) % M) ((slot % (LC * M)) / M) ∧
      u'.regs 16 < 2 ^ W ∧ u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 141 → r ≠ 146 → r ≠ 147 → r ≠ 151 → ¬ (155 ≤ r ∧ r ≤ 158) →
        r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @localEntry_spec

theorem spec_globalEntry : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1)
    (bs bc Gb M mc GLC slot : Nat) (_ : u.regs 14 = slot) (_ : u.regs 33 = mc)
    (_ : u.regs 31 = M) (_ : u.regs 32 = bc) (_ : u.regs 136 = Gb)
    (_ : 1 ≤ mc) (_ : 1 ≤ M) (_ : GLC < W) (_ : slot < GLC * mc)
    (_ : slot + (mc + 2 ^ GLC) * M < 2 ^ W) (_ : bc < 2 ^ W)
    (_ : Gb + GLC * mc ≤ u.extent) (_ : Gb + GLC * mc < 2 ^ W)
    (_ : ∀ l m, l < GLC → (m + 2 ^ l) * M ≤ bc →
      u.memory (Gb + l * mc + m) = some (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))),
    ∃ u' j, SafeEval W globalEntryBlock u u' j ∧ j ≤ 17 ∧ u'.status = .running ∧
      u'.regs 16 = bpGlobalSparseCellBlock shape bs bc M mc (slot % mc) (slot / mc) ∧
      u'.regs 16 < 2 ^ W ∧ u'.memory = u.memory ∧ u'.extent = u.extent ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 141 → r ≠ 146 → r ≠ 147 → r ≠ 155 → r ≠ 156 → r ≠ 158 →
        r ≠ 16 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @globalEntry_spec

theorem spec_localSparseTable : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (_ : s.regs 9 = 2)
    (bs bc Bm M mc LC : Nat) (_ : s.regs 58 = LC) (_ : s.regs 31 = M)
    (_ : s.regs 32 = bc) (_ : s.regs 135 = Bm) (_ : s.regs 62 = mc * (LC * M))
    (_ : 1 ≤ M) (_ : 1 ≤ LC) (_ : LC < W)
    (_ : mc * (LC * M) + LC * M + (mc + 1) * M + 2 ^ LC < 2 ^ W)
    (_ : s.extent + mc * (LC * M) * LC < 2 ^ W)
    (_ : Bm + LC * bc ≤ s.extent) (_ : Bm + LC * bc < 2 ^ W)
    (_ : ∀ l b, l < LC → b + 2 ^ l ≤ bc →
      s.memory (Bm + l * bc + b) = some (bpRangeArgMinBlock shape bs b (2 ^ l))),
    ∃ s' k, SafeEval W (emitTable rLSCNT rOW localEntryBlock) s s' k ∧
      k ≤ mc * (LC * M) * (21 + 7 * LC + 7) + 3 ∧ s'.status = .running ∧
      Emits s s' ((tableBits (bpLocalSparseOffsetEntries shape bs bc M mc LC) LC).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ LocalEntryWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @localSparseTable_spec

theorem spec_globalSparseTable : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (_ : s.regs 9 = 2)
    (bs bc Gb M mc GLC BAW : Nat) (_ : s.regs 33 = mc) (_ : s.regs 31 = M)
    (_ : s.regs 32 = bc) (_ : s.regs 136 = Gb) (_ : s.regs 63 = GLC * mc)
    (_ : s.regs 60 = BAW)
    (_ : mc = bc / M + 1) (_ : 1 ≤ mc) (_ : 1 ≤ M) (_ : GLC < W)
    (_ : GLC * mc + (mc + 2 ^ GLC) * M < 2 ^ W) (_ : bc < 2 ^ W) (_ : BAW < 2 ^ W)
    (_ : s.extent + GLC * mc * BAW < 2 ^ W)
    (_ : Gb + GLC * mc ≤ s.extent) (_ : Gb + GLC * mc < 2 ^ W)
    (_ : ∀ l m, l < GLC → (m + 2 ^ l) * M ≤ bc →
      s.memory (Gb + l * mc + m) = some (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))),
    ∃ s' k, SafeEval W (emitTable rGSCNT rBAW globalEntryBlock) s s' k ∧
      k ≤ GLC * mc * (17 + 7 * BAW + 7) + 3 ∧ s'.status = .running ∧
      Emits s s' ((tableBits (bpGlobalSparseBlockEntries shape bs bc M mc GLC) BAW).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ GlobalEntryWrites r → ¬ (10 ≤ r ∧ r ≤ 16) → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @globalSparseTable_spec

theorem spec_interiorCloseLayout : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (_ : s.regs 9 = 2)
    (A0 A1 A2 A3 B Bm Gb bs bps bc ssc sw rw M mc LC GLC BAW ldom lwid gdom gwid : Nat)
    (_ : s.regs 115 = A0) (_ : s.regs 116 = A1) (_ : s.regs 117 = A2)
    (_ : s.regs 118 = A3) (_ : s.regs 119 = B) (_ : s.regs 135 = Bm)
    (_ : s.regs 136 = Gb) (_ : s.regs 56 = bs) (_ : s.regs 32 = bc)
    (_ : s.regs 38 = shape.bpCode.length) (_ : s.regs 30 = bps) (_ : s.regs 57 = ssc)
    (_ : s.regs 39 = sw) (_ : s.regs 61 = rw) (_ : s.regs 31 = M) (_ : s.regs 33 = mc)
    (_ : s.regs 58 = LC) (_ : s.regs 59 = GLC) (_ : s.regs 60 = BAW)
    (_ : s.regs 62 = mc * (LC * M)) (_ : s.regs 63 = GLC * mc)
    (_ : s.regs 34 = ldom) (_ : s.regs 36 = lwid) (_ : s.regs 35 = gdom)
    (_ : s.regs 37 = gwid)
    (_ : Region s B shape.bpCode.length (bpCell shape))
    (_ : B + shape.bpCode.length ≤ s.extent)
    (_ : A0 + bc + 1 ≤ A1) (_ : A1 + bc ≤ A2) (_ : A2 + bc ≤ A3) (_ : A3 + bc ≤ Bm)
    (_ : Bm + LC * bc ≤ Gb) (_ : Gb + GLC * mc ≤ B)
    (_ : 0 < bps) (_ : ssc = bc / bps + 1) (_ : bc * bs ≤ shape.bpCode.length)
    (_ : 1 ≤ M) (_ : mc = bc / M + 1) (_ : 1 ≤ LC) (_ : 1 ≤ GLC)
    (_ : LC < W) (_ : GLC < W) (_ : 2 ≤ ldom) (_ : 2 ≤ gdom)
    (_ : s.extent < 2 ^ W) (_ : B + 4 * shape.bpCode.length + 4 < 2 ^ W)
    (_ : bs + 1 < 2 ^ W) (_ : bc + 2 < 2 ^ W) (_ : shape.bpCode.length + bps * bs < 2 ^ W)
    (_ : sw < 2 ^ W) (_ : rw < 2 ^ W) (_ : BAW < 2 ^ W)
    (_ : Bm + LC * bc + (bc + 2 ^ LC) * 1 < 2 ^ W)
    (_ : Gb + GLC * mc + (mc + 2 ^ GLC) * M < 2 ^ W)
    (_ : mc * (LC * M) + LC * M + (mc + 1) * M + 2 ^ LC < 2 ^ W)
    (_ : ldom * (Nat.log2 ldom + 1) < 2 ^ W ∧ gdom * (Nat.log2 gdom + 1) < 2 ^ W ∧
      lwid < 2 ^ W ∧ gwid < 2 ^ W)
    (_ : s.extent + ssc * sw + bc * rw + bc * rw + bc * rw + mc * (LC * M) * LC +
      GLC * mc * BAW + ldom * lwid + gdom * gwid < 2 ^ W),
    ∃ t s' k, SafeEval W interiorCloseBlock s s' k ∧
      k ≤ bc * ((bs + 1) * 28 + 20) + 7 + (bc * 6 + 3 + (LC * (26 * bc + 11) + 4)) +
        (mc * (15 * M + 16) + 3 + (GLC * (26 * mc + 11) + 4)) +
        (ssc * (7 * sw + 10) + bc * (21 * rw + 41) + 13) +
        (mc * (LC * M) * (21 + 7 * LC + 7) + 3) + (GLC * mc * (17 + 7 * BAW + 7) + 3) +
        (ldom * (5 * Nat.log2 ldom + 7 + 7 * lwid + 7) + 3) +
        (gdom * (5 * Nat.log2 gdom + 7 + 7 * gwid + 7) + 3) ∧
      s'.status = .running ∧ t.extent = s.extent ∧
      (∀ a, (a < A0 ∨ Gb + GLC * mc ≤ a) → t.memory a = s.memory a) ∧
      Emits t s' ((tableBits (bpSuperblockBaselineEntries shape bs bps ssc) sw ++
        tableBits (bpBlockRelativeMinExcessEntries shape bs bps bc) rw ++
        tableBits (bpBlockRelativeMaxExcessEntries shape bs bps bc) rw ++
        tableBits (bpBlockArgMinLocalOffsetEntries shape bs bc) rw ++
        tableBits (bpLocalSparseOffsetEntries shape bs bc M mc LC) LC ++
        tableBits (bpGlobalSparseBlockEntries shape bs bc M mc GLC) BAW ++
        tableBits (bpSparseLevelEntries ldom) lwid ++
        tableBits (bpSparseLevelEntries gdom) gwid).map SuccinctSpace.bitToNat) ∧
      (∀ r : Nat, CloseFrame r → s'.regs r = s.regs r) ∧
      s'.keys = s.keys :=
  @interiorCloseLayout_spec

theorem spec_closeSegment : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : GeoBase shape.size s.regs)
    (_ : GeoUpTo shape.size 39 s.regs)
    (A0 A1 A2 A3 B Bm Gb : Nat) (_ : s.regs 115 = A0) (_ : s.regs 116 = A1)
    (_ : s.regs 117 = A2) (_ : s.regs 118 = A3) (_ : s.regs 119 = B)
    (_ : s.regs 135 = Bm) (_ : s.regs 136 = Gb)
    (_ : Region s B shape.bpCode.length (bpCell shape))
    (_ : B + shape.bpCode.length ≤ s.extent)
    (_ : A0 + geoBlocks shape.size + 1 ≤ A1) (_ : A1 + geoBlocks shape.size ≤ A2)
    (_ : A2 + geoBlocks shape.size ≤ A3) (_ : A3 + geoBlocks shape.size ≤ Bm)
    (_ : Bm + SuccinctRank.machineWordBits (geoMacro shape.size) * geoBlocks shape.size ≤ Gb)
    (_ : Gb + SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size ≤ B)
    (_ : s.extent + 16 * (400000 * (shape.size + 1)) < 2 ^ W),
    ∃ t s' k, SafeEval W interiorCloseBlock s s' k ∧ k ≤ 1600 * (400000 * (shape.size + 1)) ∧
      s'.status = .running ∧ t.extent = s.extent ∧
      (∀ a, (a < A0 ∨
          Gb + SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size ≤ a) →
        t.memory a = s.memory a) ∧
      Emits t s' ((canonicalRelativeRmmInteriorDirectory shape).payload.map SuccinctSpace.bitToNat) ∧
      (∀ r : Nat, CloseFrame r → s'.regs r = s.regs r) ∧ s'.keys = s.keys :=
  @closeSegment_spec

end S4Completion

/-! ## Executable S4 completion fixtures (array-backed interpreter on the compiled source)

The harness additionally reserves the local memo (`levelCount * blockCount + 1`
cells, register 135) and the global memo (`globalLevelCount * macroSampleCount +
1` cells, register 136) after the statistics arrays, and runs
`interiorCloseBlock`. The cells after the marker are compared with all eight
interior segments. -/

def s4CloseProgram : Array BInstr :=
  ((Block.seq (.action (.load 1 0)) (.seq constantsBlock (.seq geometryPrelude
    (.seq stackArraysBlock (.seq s4ArraysHarness
    (.seq (acts [.arithmetic .mul 198 58 32]) (.seq (reserveArray 135 198)
    (.seq (acts [.arithmetic .mul 198 59 33]) (.seq (reserveArray 136 198)
    (.seq (stackPassBlock keyLeaf)
    (.seq (acts [.reserve 131, .arithmetic .add 119 131 2])
    (.seq bpEmitBlock
    (.seq (acts [.reserve 199, .arithmetic .add 199 199 2])
      interiorCloseBlock))))))))))))).compileAt 0 ++
    [(⟨.halt 3⟩ : BInstr)]).toArray

def s4Close (xs : List Int) : Bool :=
  let r := runArray s4CloseProgram 10000000 (ExecState.ofComparisonInput 200 xs)
  r.final.status == .halted 0 &&
    s3Cells r (r.final.regs.getD 199 0) ==
      ((Spec.interiorSegments (Cartesian.shape xs)).flatten).map bitToNat

def stageGuard21 : Bool := [0, 1, 2, 3, 4, 5, 6, 8, 12, 16, 24].all (fun n => s4Close (s4Input n))
def stageGuard22 : Bool := [7, 9, 15, 17, 31, 33, 63, 65].all (fun n => s4Close (s4Input n))
def stageGuard23 : Bool := s4Close (s4Input 127) && s4Close (s4Input 129)
def stageGuard24 : Bool := s4Close [1, 1, 1, 1] && s4Close [4, -3, -3, 8]
-- `crossBlockInput` of `RMQ.Validation.PackedQueryRuntime`, restated literally
def stageGuard25 : Bool := s4Close [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

/-! ## Stage S5: the access half -/

theorem posActs_def : ∀ (dst occ : Operand), posActs dst occ =
    minActs 188 occ 1 ++ [.arithmetic .add 108 159 188, .load dst 108] := fun _ _ => rfl

theorem monusActs_def : ∀ (dst a b : Operand), monusActs dst a b =
    maxActs 189 a b ++ [.arithmetic .sub dst 189 b] := fun _ _ _ => rfl

theorem posStepBlock_def : posStepBlock =
    .seq (acts [.arithmetic .mod 169 165 39])
    (.seq (.ifZero 169
        (acts [.arithmetic .div 170 165 39, .arithmetic .add 108 160 170, .store 108 168])
        .skip)
    (.seq (acts [.comparison .lt 169 165 38])
      (.ifZero 169 .skip
        (.seq (acts [.arithmetic .add 108 119 165, .load 130 108])
          (.ifZero 130
            (acts [.arithmetic .add 108 159 168, .store 108 165,
              .arithmetic .add 168 168 2])
            .skip))))) := rfl

theorem posPassBlock_def : posPassBlock =
    .seq (acts [.constant 168 0, .arithmetic .add 167 38 2])
    (.seq (forSlots 165 166 167 posStepBlock)
      (acts [.arithmetic .add 108 159 168, .store 108 38])) := rfl

theorem longFlagBlock_def : longFlagBlock =
    acts ([.arithmetic .mul 179 173 40, .arithmetic .add 169 179 40] ++
      minActs 180 169 1 ++
      [.arithmetic .sub 169 180 2] ++ posActs 182 169 ++ posActs 181 179 ++
      [.arithmetic .add 182 182 2] ++ monusActs 183 182 181 ++
      [.comparison .lt 184 44 183,
        .arithmetic .add 108 161 173, .store 108 184,
        .arithmetic .add 108 162 173, .store 108 177,
        .arithmetic .add 177 177 184]) := rfl

theorem longFlagsBlock_def : longFlagsBlock =
    .seq (acts [.constant 177 0])
    (.seq (forSlots 173 174 45 longFlagBlock)
      (acts [.arithmetic .add 108 162 45, .store 108 177])) := rfl

theorem sparseFlagBlock_def : sparseFlagBlock =
    acts ([.arithmetic .div 185 175 43, .arithmetic .mod 169 175 43,
      .arithmetic .mul 169 169 42, .arithmetic .mul 179 185 40,
      .arithmetic .add 170 179 40] ++ minActs 186 170 1 ++
      [.arithmetic .add 179 179 169, .arithmetic .add 170 179 42] ++
      minActs 180 170 186 ++
      monusActs 169 180 2 ++ posActs 182 169 ++ posActs 181 179 ++
      [.arithmetic .add 182 182 2] ++ monusActs 183 182 181 ++
      [.comparison .lt 171 39 183,
        .arithmetic .add 108 161 185, .load 172 108,
        .arithmetic .sub 172 2 172, .arithmetic .mul 184 171 172,
        .arithmetic .add 108 163 175, .store 108 184,
        .arithmetic .add 108 164 175, .store 108 178,
        .arithmetic .add 178 178 184]) := rfl

theorem sparseFlagsBlock_def : sparseFlagsBlock =
    .seq (acts [.constant 178 0])
    (.seq (forSlots 175 176 46 sparseFlagBlock)
      (acts [.arithmetic .add 108 164 46, .store 108 178])) := rfl

theorem rankSuperEntryBlock_def : rankSuperEntryBlock =
    acts [.arithmetic .mul 169 14 39, .arithmetic .add 108 160 169, .load 16 108] := rfl

theorem rankBlockEntryBlock_def : rankBlockEntryBlock =
    acts [.arithmetic .add 108 160 14, .load 16 108,
      .arithmetic .div 169 14 39, .arithmetic .mul 169 169 39,
      .arithmetic .add 108 160 169, .load 170 108, .arithmetic .sub 16 16 170] := rfl

theorem superOccEntryBlock_def : superOccEntryBlock =
    acts [.arithmetic .mul 16 14 40] := rfl

theorem superWordEntryBlock_def : superWordEntryBlock =
    acts ([.arithmetic .mul 179 14 40] ++ posActs 181 179 ++
      [.arithmetic .div 16 181 39]) := rfl

theorem superFlagEntryBlock_def : superFlagEntryBlock =
    acts [.arithmetic .add 108 161 14, .load 16 108] := rfl

theorem superOffsetEntryBlock_def : superOffsetEntryBlock =
    acts ([.arithmetic .mul 179 14 40] ++ posActs 181 179 ++
      [.arithmetic .mod 16 181 39]) := rfl

theorem localDecodeActs_def : localDecodeActs =
    [.arithmetic .div 185 14 43, .arithmetic .mod 169 14 43,
      .arithmetic .mul 169 169 42, .arithmetic .mul 170 185 40,
      .arithmetic .add 179 170 169,
      .arithmetic .add 108 161 185, .load 171 108, .arithmetic .sub 171 2 171,
      .comparison .lt 172 179 1, .arithmetic .mul 187 171 172] := rfl

theorem localOccEntryBlock_def : localOccEntryBlock =
    acts (localDecodeActs ++ [.arithmetic .mul 16 187 169]) := rfl

theorem localWordEntryBlock_def : localWordEntryBlock =
    acts (localDecodeActs ++ posActs 181 179 ++ posActs 182 170 ++
      [.arithmetic .div 181 181 39, .arithmetic .div 182 182 39,
        .arithmetic .sub 16 181 182, .arithmetic .mul 16 187 16]) := rfl

theorem localFlagEntryBlock_def : localFlagEntryBlock =
    acts (localDecodeActs ++ [.arithmetic .add 108 163 14, .load 16 108,
      .arithmetic .mul 16 187 16]) := rfl

theorem localOffsetEntryBlock_def : localOffsetEntryBlock =
    acts (localDecodeActs ++ posActs 181 179 ++
      [.arithmetic .mod 16 181 39, .arithmetic .mul 16 187 16]) := rfl

theorem flagRankEntryBlock_def : ∀ (base w : Operand), flagRankEntryBlock base w =
    acts [.arithmetic .mul 169 14 w, .arithmetic .add 108 base 169, .load 16 108] := fun _ _ => rfl

theorem zeroEntryBlock_def : zeroEntryBlock =
    acts [.constant 16 0] := rfl

theorem flagEntryBlock_def : ∀ (base : Operand), flagEntryBlock base =
    acts [.arithmetic .add 108 base 14, .load 16 108] := fun _ => rfl

theorem relativeOffsetEntryBlock_def : relativeOffsetEntryBlock =
    acts ([.arithmetic .add 169 179 14, .comparison .lt 170 169 180] ++
      posActs 171 169 ++ monusActs 171 171 181 ++ [.arithmetic .mul 16 170 171]) := rfl

theorem longRelativeBodyBlock_def : longRelativeBodyBlock =
    .seq (acts [.arithmetic .add 108 161 173, .load 184 108])
      (.ifZero 184 .skip
        (.seq (acts ([.arithmetic .mul 179 173 40, .arithmetic .add 172 179 40] ++
            minActs 180 172 1 ++ posActs 181 179))
          (emitTable 40 39 relativeOffsetEntryBlock))) := rfl

theorem sparseRelativeBodyBlock_def : sparseRelativeBodyBlock =
    .seq (acts [.arithmetic .add 108 163 175, .load 184 108])
      (.ifZero 184 .skip
        (.seq (acts ([.arithmetic .div 185 175 43, .arithmetic .mod 169 175 43,
            .arithmetic .mul 169 169 42, .arithmetic .mul 179 185 40,
            .arithmetic .add 172 179 40] ++ minActs 180 172 1 ++
            [.arithmetic .add 179 179 169] ++ posActs 181 179))
          (emitTable 42 49 relativeOffsetEntryBlock))) := rfl

theorem accessHalfBlock_def : accessHalfBlock =
    .seq posPassBlock (.seq longFlagsBlock (.seq sparseFlagsBlock
    (.seq (emitTable 52 39 rankSuperEntryBlock)
    (.seq (emitTable 53 48 rankBlockEntryBlock)
    (.seq (emitTable 45 39 superOccEntryBlock)
    (.seq (emitTable 45 39 superWordEntryBlock)
    (.seq (emitTable 45 39 superFlagEntryBlock)
    (.seq (emitTable 45 39 superOffsetEntryBlock)
    (.seq (emitTable 46 49 localOccEntryBlock)
    (.seq (emitTable 46 49 localWordEntryBlock)
    (.seq (emitTable 46 49 localFlagEntryBlock)
    (.seq (emitTable 46 49 localOffsetEntryBlock)
    (.seq (emitTable 54 50 (flagRankEntryBlock 162 50))
    (.seq (emitTable 54 50 zeroEntryBlock)
    (.seq (emitTable 45 2 (flagEntryBlock 161))
    (.seq (forSlots 173 174 45 longRelativeBodyBlock)
    (.seq (emitTable 55 51 (flagRankEntryBlock 164 51))
    (.seq (emitTable 55 51 zeroEntryBlock)
    (.seq (emitTable 47 2 (flagEntryBlock 163))
      (forSlots 175 176 46 sparseRelativeBodyBlock)))))))))))))))))))) := rfl

theorem spec_AccessWrites_def : ∀ r : Nat, AccessWrites r ↔
    (r = 108 ∨ (26 ≤ r ∧ r ≤ 28) ∨ (169 ≤ r ∧ r ≤ 172) ∨ (179 ≤ r ∧ r ≤ 189)) := fun _ => Iff.rfl

theorem spec_RelWrites_def : ∀ r : Nat, RelWrites r ↔
    (r = 108 ∨ (26 ≤ r ∧ r ≤ 28) ∨ (169 ≤ r ∧ r ≤ 171) ∨ r = 188 ∨ r = 189) := fun _ => Iff.rfl

theorem spec_BodyWrites_def : ∀ r : Nat, BodyWrites r ↔
    ((10 ≤ r ∧ r ≤ 16) ∨ r = 108 ∨ (26 ≤ r ∧ r ≤ 28) ∨ (169 ≤ r ∧ r ≤ 172) ∨ (179 ≤ r ∧ r ≤ 189)) :=
  fun _ => Iff.rfl

theorem spec_AccessFrame_def : ∀ r : Nat, AccessFrame r ↔
    (¬ (10 ≤ r ∧ r ≤ 16) ∧ ¬ (26 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ ¬ (169 ≤ r ∧ r ≤ 176) ∧
      ¬ (179 ≤ r ∧ r ≤ 189)) := fun _ => Iff.rfl

theorem spec_AccessHalfFrame_def : ∀ r : Nat, AccessHalfFrame r ↔
    (¬ (10 ≤ r ∧ r ≤ 16) ∧ ¬ (26 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ r ≠ 130 ∧ ¬ (165 ≤ r ∧ r ≤ 189)) :=
  fun _ => Iff.rfl

theorem spec_flagNat_def : ∀ b : Bool, flagNat b = if b then 1 else 0 := fun _ => rfl

theorem spec_liveAccessPayload_eq_segments : ∀ (shape : CartesianShape),
    SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape =
      (Spec.accessSegments shape).flatten :=
  Spec.liveAccessPayload_eq_segments

section S5Access

open RMQ.SuccinctFinal.PackedConstruction.Spec RMQ.GenericSelect

theorem spec_select_at_close : ∀ (b : List Bool) {p : Nat} (_ : b[p]? = some false),
    RMQ.Succinct.select false b (RMQ.Succinct.rankPrefix false b p) = some p :=
  @Spec.select_at_close

theorem spec_position_at_close : ∀ (b : List Bool) {p : Nat} (_ : b[p]? = some false),
    position b false (RMQ.Succinct.rankPrefix false b p) = p :=
  @Spec.position_at_close

theorem spec_rankPrefix_false_succ : ∀ (b : List Bool) {p : Nat} (_ : p < b.length),
    RMQ.Succinct.rankPrefix false b (p + 1) =
      RMQ.Succinct.rankPrefix false b p + (if b[p] then 0 else 1) :=
  @Spec.rankPrefix_false_succ

theorem spec_bp_occurrenceCount : ∀ (shape : CartesianShape),
    occurrenceCount shape.bpCode false = shape.size :=
  @Spec.bp_occurrenceCount

theorem spec_bp_rank_end : ∀ (shape : CartesianShape) {q : Nat} (_ : shape.bpCode.length ≤ q),
    RMQ.Succinct.rankPrefix false shape.bpCode q = shape.size :=
  @Spec.bp_rank_end

theorem spec_bp_position_size : ∀ (shape : CartesianShape),
    position shape.bpCode false shape.size = shape.bpCode.length :=
  @Spec.bp_position_size

theorem spec_position_min_size : ∀ (shape : CartesianShape) (k : Nat),
    position shape.bpCode false (min k shape.size) = position shape.bpCode false k :=
  @Spec.position_min_size

theorem spec_posStep_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (B P0 R0 ws p : Nat) (_ : u.regs 119 = B)
    (_ : u.regs 159 = P0) (_ : u.regs 160 = R0) (_ : u.regs 39 = ws)
    (_ : u.regs 38 = shape.bpCode.length) (_ : u.regs 165 = p)
    (_ : u.regs 168 = RMQ.Succinct.rankPrefix false shape.bpCode p) (_ : 1 ≤ ws)
    (_ : p ≤ shape.bpCode.length) (_ : Region u B shape.bpCode.length (bpCell shape))
    (_ : P0 + shape.size + 1 ≤ R0) (_ : R0 + shape.bpCode.length / ws + 1 ≤ B)
    (_ : B + shape.bpCode.length ≤ u.extent) (_ : u.extent < 2 ^ W),
    ∃ u' j, SafeEval W posStepBlock u u' j ∧ j ≤ 16 ∧ u'.status = .running ∧
      u'.regs 168 = RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) ∧
      (∀ a, (a < P0 ∨ R0 + shape.bpCode.length / ws + 1 ≤ a) → u'.memory a = u.memory a) ∧
      (∀ k, k < RMQ.Succinct.rankPrefix false shape.bpCode p →
        u'.memory (P0 + k) = u.memory (P0 + k)) ∧
      (RMQ.Succinct.rankPrefix false shape.bpCode p < RMQ.Succinct.rankPrefix false shape.bpCode (p + 1) →
        u'.memory (P0 + RMQ.Succinct.rankPrefix false shape.bpCode p) =
          some (position shape.bpCode false (RMQ.Succinct.rankPrefix false shape.bpCode p))) ∧
      (∀ j, j * ws = p → u'.memory (R0 + j) = some (RMQ.Succinct.rankPrefix false shape.bpCode p)) ∧
      (∀ j, j * ws ≠ p → u'.memory (R0 + j) = u.memory (R0 + j)) ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 130 → r ≠ 168 → r ≠ 169 → r ≠ 170 → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys :=
  @posStep_spec

theorem spec_posPass_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (B P0 R0 ws : Nat) (_ : s.regs 119 = B)
    (_ : s.regs 159 = P0) (_ : s.regs 160 = R0) (_ : s.regs 39 = ws)
    (_ : s.regs 38 = shape.bpCode.length) (_ : 1 ≤ ws)
    (_ : Region s B shape.bpCode.length (bpCell shape)) (_ : P0 + shape.size + 1 ≤ R0)
    (_ : R0 + shape.bpCode.length / ws + 1 ≤ B) (_ : B + shape.bpCode.length ≤ s.extent)
    (_ : s.extent < 2 ^ W),
    ∃ s' j, SafeEval W posPassBlock s s' j ∧ j ≤ (shape.bpCode.length + 1) * 20 + 7 ∧
      s'.status = .running ∧
      (∀ k, k ≤ shape.size → s'.memory (P0 + k) = some (position shape.bpCode false k)) ∧
      (∀ j, j ≤ shape.bpCode.length / ws →
        s'.memory (R0 + j) = some (RMQ.Succinct.rankPrefix false shape.bpCode (j * ws))) ∧
      (∀ a, (a < P0 ∨ R0 + shape.bpCode.length / ws + 1 ≤ a) → s'.memory a = s.memory a) ∧
      (∀ r : Nat, r ≠ 108 → r ≠ 130 → ¬ (165 ≤ r ∧ r ≤ 170) → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys :=
  @posPass_spec

theorem spec_posActs_prefix : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (dst occ : Operand)
    (_ : (occ : Nat) ≠ 26 ∧ (occ : Nat) ≠ 27) (u : State) (_ : u.status = .running)
    (_ : u.regs 2 = 1) (P0 K : Nat) (_ : u.regs 1 = shape.size) (_ : u.regs 159 = P0)
    (_ : u.regs occ = K) (_ : K < 2 ^ W)
    (_ : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (_ : P0 + shape.size < u.extent) (_ : P0 + shape.size < 2 ^ W) (_ : shape.bpCode.length < 2 ^ W),
    ∃ u', ActsPrefix W (posActs dst occ) u u' 7 ∧
      u'.regs dst = position shape.bpCode false K ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 188 → r ≠ dst → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @posActs_prefix

theorem spec_monusActs_prefix : ∀ {W : Nat} (_ : 32 ≤ W) (dst a b : Operand)
    (_ : (a : Nat) ≠ 26 ∧ (a : Nat) ≠ 27 ∧ (a : Nat) ≠ 28)
    (_ : (b : Nat) ≠ 26 ∧ (b : Nat) ≠ 27 ∧ (b : Nat) ≠ 28 ∧ (b : Nat) ≠ 189) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (A Bv : Nat) (_ : u.regs a = A) (_ : u.regs b = Bv)
    (_ : A < 2 ^ W) (_ : Bv < 2 ^ W),
    ∃ u', ActsPrefix W (monusActs dst a b) u u' 6 ∧ u'.regs dst = A - Bv ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 189 → r ≠ dst → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @monusActs_prefix

theorem spec_longFlag_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (P0 L0 C0 k cnt : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 159 = P0) (_ : u.regs 161 = L0) (_ : u.regs 162 = C0) (_ : u.regs 173 = k)
    (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 44 = superLongSpan shape.bpCode.length) (_ : u.regs 177 = cnt)
    (_ : k < superSlotCount shape.bpCode false) (_ : cnt ≤ k)
    (_ : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : P0 + shape.size < L0) (_ : L0 + superSlotCount shape.bpCode false ≤ C0)
    (_ : C0 + superSlotCount shape.bpCode false < u.extent) (_ : u.extent < 2 ^ W)
    (_ : shape.bpCode.length + 1 < 2 ^ W) (_ : (k + 1) * superStride shape.bpCode.length < 2 ^ W),
    ∃ u' j, SafeEval W longFlagBlock u u' j ∧ j ≤ 35 ∧ u'.status = .running ∧
      u'.memory = put (put u.memory (L0 + k) (some (flagNat (superIsLong shape.bpCode false k))))
        (C0 + k) (some cnt) ∧
      u'.regs 177 = cnt + flagNat (superIsLong shape.bpCode false k) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → ¬ (177 ≤ r ∧ r ≤ 184) → r ≠ 188 →
        r ≠ 189 → u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @longFlag_spec

theorem spec_longFlags_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (P0 L0 C0 : Nat) (_ : s.regs 1 = shape.size)
    (_ : s.regs 159 = P0) (_ : s.regs 161 = L0) (_ : s.regs 162 = C0)
    (_ : s.regs 40 = superStride shape.bpCode.length)
    (_ : s.regs 44 = superLongSpan shape.bpCode.length)
    (_ : s.regs 45 = superSlotCount shape.bpCode false)
    (_ : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : P0 + shape.size < L0) (_ : L0 + superSlotCount shape.bpCode false ≤ C0)
    (_ : C0 + superSlotCount shape.bpCode false < s.extent) (_ : s.extent < 2 ^ W)
    (_ : shape.bpCode.length + 1 < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length < 2 ^ W),
    ∃ s' j, SafeEval W longFlagsBlock s s' j ∧
      j ≤ superSlotCount shape.bpCode false * 39 + 6 ∧ s'.status = .running ∧
      (∀ k, k < superSlotCount shape.bpCode false →
        s'.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k))) ∧
      (∀ k, k ≤ superSlotCount shape.bpCode false →
        s'.memory (C0 + k) = some (RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) k)) ∧
      (∀ a, (a < L0 ∨ C0 + superSlotCount shape.bpCode false + 1 ≤ a) → s'.memory a = s.memory a) ∧
      s'.regs 177 = RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false)
        (superSlotCount shape.bpCode false) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → r ≠ 169 → ¬ (173 ≤ r ∧ r ≤ 184) → r ≠ 188 →
        r ≠ 189 → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys :=
  @longFlags_spec

theorem spec_sparseFlag_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (P0 L0 F0 G0 g cnt : Nat)
    (_ : u.regs 1 = shape.size) (_ : u.regs 159 = P0) (_ : u.regs 161 = L0) (_ : u.regs 163 = F0)
    (_ : u.regs 164 = G0) (_ : u.regs 175 = g) (_ : u.regs 178 = cnt)
    (_ : u.regs 39 = wordBits shape.bpCode.length) (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 42 = localStride shape.bpCode.length)
    (_ : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : g < localSlotCount shape.bpCode false) (_ : cnt ≤ g)
    (_ : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : P0 + shape.size < L0) (_ : L0 + superSlotCount shape.bpCode false ≤ F0)
    (_ : F0 + localSlotCount shape.bpCode false ≤ G0)
    (_ : G0 + localSlotCount shape.bpCode false < u.extent) (_ : u.extent < 2 ^ W)
    (_ : shape.bpCode.length + 1 < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W),
    ∃ u' j, SafeEval W sparseFlagBlock u u' j ∧ j ≤ 60 ∧ u'.status = .running ∧
      u'.memory = put (put u.memory (F0 + g) (some (flagNat (localIsSparseException shape.bpCode false g))))
        (G0 + g) (some cnt) ∧
      u'.regs 178 = cnt + flagNat (localIsSparseException shape.bpCode false g) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → ¬ (178 ≤ r ∧ r ≤ 189) →
        u'.regs r = u.regs r) ∧
      u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @sparseFlag_spec

theorem spec_sparseFlags_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (P0 L0 F0 G0 : Nat) (_ : s.regs 1 = shape.size)
    (_ : s.regs 159 = P0) (_ : s.regs 161 = L0) (_ : s.regs 163 = F0) (_ : s.regs 164 = G0)
    (_ : s.regs 39 = wordBits shape.bpCode.length) (_ : s.regs 40 = superStride shape.bpCode.length)
    (_ : s.regs 42 = localStride shape.bpCode.length)
    (_ : s.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : s.regs 46 = localSlotCount shape.bpCode false)
    (_ : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      s.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : P0 + shape.size < L0) (_ : L0 + superSlotCount shape.bpCode false ≤ F0)
    (_ : F0 + localSlotCount shape.bpCode false ≤ G0)
    (_ : G0 + localSlotCount shape.bpCode false < s.extent) (_ : s.extent < 2 ^ W)
    (_ : shape.bpCode.length + 1 < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W),
    ∃ s' j, SafeEval W sparseFlagsBlock s s' j ∧
      j ≤ localSlotCount shape.bpCode false * 64 + 6 ∧ s'.status = .running ∧
      (∀ g, g < localSlotCount shape.bpCode false →
        s'.memory (F0 + g) = some (flagNat (localIsSparseException shape.bpCode false g))) ∧
      (∀ g, g ≤ localSlotCount shape.bpCode false →
        s'.memory (G0 + g) = some (RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) g)) ∧
      (∀ a, (a < F0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) → s'.memory a = s.memory a) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r : Nat, ¬ (26 ≤ r ∧ r ≤ 28) → r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → r ≠ 175 → r ≠ 176 →
        ¬ (178 ≤ r ∧ r ≤ 189) → s'.regs r = s.regs r) ∧
      s'.extent = s.extent ∧ s'.keys = s.keys :=
  @sparseFlags_spec

theorem spec_flagEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (base : Operand) (u : State)
    (_ : u.status = .running) (F0 N slot : Nat) (val : Nat → Nat) (_ : u.regs 14 = slot)
    (_ : u.regs base = F0) (_ : slot < N) (_ : ∀ k, k < N → u.memory (F0 + k) = some (val k))
    (_ : F0 + N ≤ u.extent) (_ : F0 + N < 2 ^ W) (_ : ∀ k, k < N → val k < 2 ^ W),
    EntryOK W (flagEntryBlock base) AccessWrites u (val slot) 2 :=
  @flagEntry_spec

theorem spec_flagRankEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (base w : Operand)
    (_ : (base : Nat) ≠ 169) (u : State) (_ : u.status = .running) (C0 N ws slot : Nat)
    (val : Nat → Nat) (_ : u.regs 14 = slot) (_ : u.regs w = ws) (_ : u.regs base = C0)
    (_ : slot * ws ≤ N) (_ : ∀ k, k ≤ N → u.memory (C0 + k) = some (val k)) (_ : C0 + N < u.extent)
    (_ : C0 + N < 2 ^ W) (_ : ∀ k, k ≤ N → val k < 2 ^ W),
    EntryOK W (flagRankEntryBlock base w) AccessWrites u (val (slot * ws)) 3 :=
  @flagRankEntry_spec

theorem spec_rankBlockEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (R0 N ws slot : Nat) (val : Nat → Nat) (_ : u.regs 14 = slot) (_ : u.regs 39 = ws)
    (_ : u.regs 160 = R0) (_ : 1 ≤ ws) (_ : slot ≤ N)
    (_ : ∀ k, k ≤ N → u.memory (R0 + k) = some (val k)) (_ : ∀ i j, i ≤ j → j ≤ N → val i ≤ val j)
    (_ : R0 + N < u.extent) (_ : R0 + N < 2 ^ W) (_ : ∀ k, k ≤ N → val k < 2 ^ W),
    EntryOK W rankBlockEntryBlock AccessWrites u (val slot - val (slot / ws * ws)) 7 :=
  @rankBlockEntry_spec

theorem spec_zeroEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running),
    EntryOK W zeroEntryBlock AccessWrites u 0 1 :=
  @zeroEntry_spec

theorem spec_superOccEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (S slot : Nat) (_ : u.regs 14 = slot) (_ : u.regs 40 = S) (_ : slot * S < 2 ^ W),
    EntryOK W superOccEntryBlock AccessWrites u (slot * S) 1 :=
  @superOccEntry_spec

theorem spec_relOffsetEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (P0 base e bpos slot : Nat)
    (_ : u.regs 1 = shape.size) (_ : u.regs 159 = P0) (_ : u.regs 14 = slot) (_ : u.regs 179 = base)
    (_ : u.regs 180 = e) (_ : u.regs 181 = bpos) (_ : base + slot < 2 ^ W) (_ : bpos < 2 ^ W)
    (_ : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (_ : P0 + shape.size < u.extent) (_ : P0 + shape.size < 2 ^ W) (_ : shape.bpCode.length < 2 ^ W),
    EntryOK W relativeOffsetEntryBlock RelWrites u
      (if base + slot < e then position shape.bpCode false (base + slot) - bpos else 0) 20 :=
  @relOffsetEntry_spec

theorem spec_superWordEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (P0 S ws slot : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 159 = P0) (_ : u.regs 14 = slot) (_ : u.regs 40 = S) (_ : u.regs 39 = ws)
    (_ : 1 ≤ ws) (_ : slot * S < 2 ^ W)
    (_ : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (_ : P0 + shape.size < u.extent) (_ : P0 + shape.size < 2 ^ W) (_ : shape.bpCode.length < 2 ^ W),
    EntryOK W superWordEntryBlock AccessWrites u (position shape.bpCode false (slot * S) / ws) 9 :=
  @superWordEntry_spec

theorem spec_superOffsetEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (P0 S ws slot : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 159 = P0) (_ : u.regs 14 = slot) (_ : u.regs 40 = S) (_ : u.regs 39 = ws)
    (_ : 1 ≤ ws) (_ : slot * S < 2 ^ W)
    (_ : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (_ : P0 + shape.size < u.extent) (_ : P0 + shape.size < 2 ^ W) (_ : shape.bpCode.length < 2 ^ W),
    EntryOK W superOffsetEntryBlock AccessWrites u (position shape.bpCode false (slot * S) % ws) 9 :=
  @superOffsetEntry_spec

theorem spec_localDecode_prefix : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (L0 g : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 161 = L0) (_ : u.regs 14 = g) (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 42 = localStride shape.bpCode.length)
    (_ : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : g < localSlotCount shape.bpCode false)
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (_ : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W),
    ∃ v, ActsPrefix W localDecodeActs u v 10 ∧
      v.regs 170 = localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length ∧
      v.regs 169 = localBaseOccurrence shape.bpCode.length g -
        localSuperSlot shape.bpCode.length g * superStride shape.bpCode.length ∧
      v.regs 179 = localBaseOccurrence shape.bpCode.length g ∧
      v.regs 187 = flagNat (compactLocalEntryIsLive shape.bpCode false g) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (169 ≤ r ∧ r ≤ 172) → r ≠ 179 → r ≠ 185 → r ≠ 187 →
        v.regs r = u.regs r) ∧
      v.memory = u.memory ∧ v.extent = u.extent ∧ v.keys = u.keys ∧ v.keyRegs = u.keyRegs :=
  @localDecode_prefix

theorem spec_localOccEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (L0 g : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 161 = L0) (_ : u.regs 14 = g) (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 42 = localStride shape.bpCode.length)
    (_ : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : g < localSlotCount shape.bpCode false)
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (_ : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W),
    EntryOK W localOccEntryBlock AccessWrites u (localEntry shape.bpCode false g).baseOccurrence 11 :=
  @localOccEntry_spec

theorem spec_localWordEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (P0 L0 g : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 159 = P0) (_ : u.regs 161 = L0) (_ : u.regs 14 = g)
    (_ : u.regs 39 = wordBits shape.bpCode.length) (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 42 = localStride shape.bpCode.length)
    (_ : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : g < localSlotCount shape.bpCode false)
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (_ : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (_ : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (_ : P0 + shape.size < u.extent) (_ : P0 + shape.size < 2 ^ W) (_ : shape.bpCode.length < 2 ^ W),
    EntryOK W localWordEntryBlock AccessWrites u (localEntry shape.bpCode false g).baseWordIndex 28 :=
  @localWordEntry_spec

theorem spec_localFlagEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (L0 F0 g : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 161 = L0) (_ : u.regs 163 = F0) (_ : u.regs 14 = g)
    (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 42 = localStride shape.bpCode.length)
    (_ : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : g < localSlotCount shape.bpCode false)
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (_ : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (_ : ∀ k, k < localSlotCount shape.bpCode false →
      u.memory (F0 + k) = some (flagNat (localIsSparseException shape.bpCode false k)))
    (_ : F0 + localSlotCount shape.bpCode false ≤ u.extent)
    (_ : F0 + localSlotCount shape.bpCode false < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W),
    EntryOK W localFlagEntryBlock AccessWrites u (localEntry shape.bpCode false g).rankBefore 13 :=
  @localFlagEntry_spec

theorem spec_localOffsetEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (P0 L0 g : Nat) (_ : u.regs 1 = shape.size)
    (_ : u.regs 159 = P0) (_ : u.regs 161 = L0) (_ : u.regs 14 = g)
    (_ : u.regs 39 = wordBits shape.bpCode.length) (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 42 = localStride shape.bpCode.length)
    (_ : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : g < localSlotCount shape.bpCode false)
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (_ : L0 + superSlotCount shape.bpCode false < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (_ : ∀ k, k ≤ shape.size → u.memory (P0 + k) = some (position shape.bpCode false k))
    (_ : P0 + shape.size < u.extent) (_ : P0 + shape.size < 2 ^ W) (_ : shape.bpCode.length < 2 ^ W),
    EntryOK W localOffsetEntryBlock AccessWrites u (localEntry shape.bpCode false g).firstOffset 19 :=
  @localOffsetEntry_spec

theorem spec_relativeOffsetsOrZero_eq_positions : ∀ (b : List Bool) (base cnt e bpos : Nat)
    (_ : e ≤ occurrenceCount b false),
    relativeOffsetsOrZero false b base cnt e bpos =
      (List.range cnt).map (fun o => if base + o < e then position b false (base + o) - bpos else 0) :=
  @relativeOffsetsOrZero_eq_positions

theorem spec_longRelativeBody_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (_ : u.regs 9 = 2) (P0 L0 k : Nat)
    (_ : u.regs 1 = shape.size) (_ : u.regs 159 = P0) (_ : u.regs 161 = L0) (_ : u.regs 173 = k)
    (_ : u.regs 39 = wordBits shape.bpCode.length) (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : k < superSlotCount shape.bpCode false)
    (_ : ∀ k', k' < superSlotCount shape.bpCode false →
      u.memory (L0 + k') = some (flagNat (superIsLong shape.bpCode false k')))
    (_ : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : P0 + shape.size < L0) (_ : L0 + superSlotCount shape.bpCode false ≤ u.extent)
    (_ : u.extent + (longSuperRelativeEntriesForSlot shape.bpCode false k).length *
      wordBits shape.bpCode.length < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length < 2 ^ W)
    (_ : shape.bpCode.length < 2 ^ W),
    ∃ u' j, SafeEval W longRelativeBodyBlock u u' j ∧
      j ≤ 21 + 34 * ((longSuperRelativeEntriesForSlot shape.bpCode false k).length *
        wordBits shape.bpCode.length) ∧ u'.status = .running ∧
      Emits u u' ((flattenPayloadWords ((longSuperRelativeEntriesForSlot shape.bpCode false k).map
        (natToBitsLE (wordBits shape.bpCode.length)))).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → u'.regs r = u.regs r) ∧ u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @longRelativeBody_spec

theorem spec_sparseRelativeBody_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (u : State)
    (_ : u.status = .running) (_ : u.regs 2 = 1) (_ : u.regs 9 = 2) (P0 F0 g : Nat)
    (_ : u.regs 1 = shape.size) (_ : u.regs 159 = P0) (_ : u.regs 163 = F0) (_ : u.regs 175 = g)
    (_ : u.regs 40 = superStride shape.bpCode.length)
    (_ : u.regs 42 = localStride shape.bpCode.length)
    (_ : u.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : u.regs 49 = sparseExceptionRelativeWidth shape.bpCode)
    (_ : g < localSlotCount shape.bpCode false)
    (_ : ∀ g', g' < localSlotCount shape.bpCode false →
      u.memory (F0 + g') = some (flagNat (localIsSparseException shape.bpCode false g')))
    (_ : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : P0 + shape.size < F0) (_ : F0 + localSlotCount shape.bpCode false ≤ u.extent)
    (_ : u.extent + (sparseExceptionRelativeEntriesForSlot shape.bpCode false g).length *
      sparseExceptionRelativeWidth shape.bpCode < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (_ : shape.bpCode.length < 2 ^ W),
    ∃ u' j, SafeEval W sparseRelativeBodyBlock u u' j ∧
      j ≤ 25 + 34 * ((sparseExceptionRelativeEntriesForSlot shape.bpCode false g).length *
        sparseExceptionRelativeWidth shape.bpCode) ∧ u'.status = .running ∧
      Emits u u' ((flattenPayloadWords ((sparseExceptionRelativeEntriesForSlot shape.bpCode false g).map
        (natToBitsLE (sparseExceptionRelativeWidth shape.bpCode)))).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → u'.regs r = u.regs r) ∧ u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @sparseRelativeBody_spec

theorem spec_relLoop_spec : ∀ {W : Nat} (_ : 32 ≤ W) (i go cnt : Operand) (body : Block) (J w : Nat)
    (E : Nat → List Nat) (Keep : State → Prop) (_ : (i : Nat) ≠ go) (_ : (i : Nat) ≠ cnt)
    (_ : (go : Nat) ≠ cnt) (_ : (i : Nat) ≠ 2) (_ : (go : Nat) ≠ 2) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (_ : s.regs cnt < 2 ^ W)
    (_ : s.extent + ((List.range (s.regs cnt)).flatMap E).length * w < 2 ^ W)
    (_ : ∀ u : State, u.status = .running → (∀ r : Nat, r ≠ i → r ≠ go → u.regs r = s.regs r) →
      u.memory = s.memory → u.extent = s.extent → u.keys = s.keys → u.keyRegs = s.keyRegs → Keep u)
    (_ : ∀ u v : State, Keep u → (∀ r : Nat, r ≠ i → r ≠ go → v.regs r = u.regs r) →
      v.memory = u.memory → v.extent = u.extent → v.keys = u.keys → v.keyRegs = u.keyRegs → Keep v)
    (_ : ∀ k (u : State), k < s.regs cnt → Keep u → u.status = .running →
      u.regs i = k → u.regs cnt = s.regs cnt → u.regs 2 = 1 →
      Emits s u ((List.range k).flatMap
        (fun x => (flattenPayloadWords ((E x).map (natToBitsLE w))).map SuccinctSpace.bitToNat)) →
      u.extent + (E k).length * w < 2 ^ W →
      ∃ u' j, SafeEval W body u u' j ∧ j ≤ J + 34 * ((E k).length * w) ∧ u'.status = .running ∧
        u'.regs i = k ∧ u'.regs cnt = s.regs cnt ∧ u'.regs 2 = 1 ∧
        Emits u u' ((flattenPayloadWords ((E k).map (natToBitsLE w))).map SuccinctSpace.bitToNat) ∧
        Keep u'),
    ∃ s' j, SafeEval W (forSlots i go cnt body) s s' j ∧
      j ≤ s.regs cnt * (J + 4) + 3 + 34 * (((List.range (s.regs cnt)).flatMap E).length * w) ∧
      s'.status = .running ∧
      Emits s s' ((flattenPayloadWords (((List.range (s.regs cnt)).flatMap E).map
        (natToBitsLE w))).map SuccinctSpace.bitToNat) ∧ Keep s' :=
  @relLoop_spec

theorem spec_longRelative_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (_ : s.regs 9 = 2) (P0 L0 : Nat)
    (_ : s.regs 1 = shape.size) (_ : s.regs 159 = P0) (_ : s.regs 161 = L0)
    (_ : s.regs 39 = wordBits shape.bpCode.length) (_ : s.regs 40 = superStride shape.bpCode.length)
    (_ : s.regs 45 = superSlotCount shape.bpCode false)
    (_ : ∀ k, k < superSlotCount shape.bpCode false →
      s.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k)))
    (_ : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : P0 + shape.size < L0) (_ : L0 + superSlotCount shape.bpCode false ≤ s.extent)
    (_ : s.extent + (tableBits (longSuperRelativeEntries shape.bpCode false)
      (wordBits shape.bpCode.length)).length < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length < 2 ^ W)
    (_ : shape.bpCode.length < 2 ^ W),
    ∃ s' j, SafeEval W (forSlots rK rKGO rSUP longRelativeBodyBlock) s s' j ∧
      j ≤ superSlotCount shape.bpCode false * 25 + 3 +
        34 * (tableBits (longSuperRelativeEntries shape.bpCode false) (wordBits shape.bpCode.length)).length ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (longSuperRelativeEntries shape.bpCode false)
        (wordBits shape.bpCode.length)).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → r ≠ 173 → r ≠ 174 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @longRelative_spec

theorem spec_sparseRelative_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : s.regs 2 = 1) (_ : s.regs 9 = 2) (P0 F0 : Nat)
    (_ : s.regs 1 = shape.size) (_ : s.regs 159 = P0) (_ : s.regs 163 = F0)
    (_ : s.regs 40 = superStride shape.bpCode.length)
    (_ : s.regs 42 = localStride shape.bpCode.length)
    (_ : s.regs 43 = localSlotsPerSuper shape.bpCode.length)
    (_ : s.regs 46 = localSlotCount shape.bpCode false)
    (_ : s.regs 49 = sparseExceptionRelativeWidth shape.bpCode)
    (_ : ∀ g, g < localSlotCount shape.bpCode false →
      s.memory (F0 + g) = some (flagNat (localIsSparseException shape.bpCode false g)))
    (_ : ∀ q, q ≤ shape.size → s.memory (P0 + q) = some (position shape.bpCode false q))
    (_ : P0 + shape.size < F0) (_ : F0 + localSlotCount shape.bpCode false ≤ s.extent)
    (_ : s.extent + (tableBits (sparseExceptionRelativeEntries shape.bpCode false)
      (sparseExceptionRelativeWidth shape.bpCode)).length < 2 ^ W)
    (_ : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W)
    (_ : shape.bpCode.length < 2 ^ W),
    ∃ s' j, SafeEval W (forSlots rG rGGO rLOC sparseRelativeBodyBlock) s s' j ∧
      j ≤ localSlotCount shape.bpCode false * 29 + 3 +
        34 * (tableBits (sparseExceptionRelativeEntries shape.bpCode false)
          (sparseExceptionRelativeWidth shape.bpCode)).length ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (sparseExceptionRelativeEntries shape.bpCode false)
        (sparseExceptionRelativeWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ BodyWrites r → r ≠ 175 → r ≠ 176 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @sparseRelative_spec

theorem spec_accessTable_generic : ∀ {W : Nat} (_ : 32 ≤ W) {shape : CartesianShape}
    {P0 R0 L0 C0 F0 G0 : Nat} (count w : Operand) (entry : Block) (J : Nat) (writes : Nat → Prop)
    (_ : ¬ TableScratch count) (_ : ¬ TableScratch w) (_ : ¬ writes count) (_ : ¬ writes w)
    (_ : ¬ writes 2) (_ : ¬ writes 9) (_ : ¬ writes 14) (_ : ∀ r, AccessFrame r → ¬ writes r)
    (N wv : Nat) (es : List Nat) (f : Nat → Nat) (u : State)
    (_ : AccessReady W shape P0 R0 L0 C0 F0 G0 u) (_ : u.regs count = N) (_ : u.regs w = wv)
    (_ : 1 ≤ wv) (_ : wv < 2 ^ W) (_ : (List.range N).map f = es)
    (_ : u.extent + (tableBits es wv).length < 2 ^ W)
    (_ : ∀ x : State, AccessReady W shape P0 R0 L0 C0 F0 G0 x → x.status = .running →
      (∀ r, ¬ writes r → ¬ TableScratch r → x.regs r = u.regs r) → x.regs 14 < N →
      EntryOK W entry writes x (f (x.regs 14)) J),
    ∃ v k, SafeEval W (emitTable count w entry) u v k ∧ k ≤ (J + 14) * (tableBits es wv).length + 3 ∧
      v.status = .running ∧ Emits u v ((tableBits es wv).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  @accessTable_generic

theorem spec_accessRegs_of_bank : ∀ (shape : CartesianShape) {r : Registers}
    (_ : GeoUpTo shape.size 39 r),
    r 38 = shape.bpCode.length ∧ r 39 = wordBits shape.bpCode.length ∧
    r 40 = superStride shape.bpCode.length ∧ r 42 = localStride shape.bpCode.length ∧
    r 43 = localSlotsPerSuper shape.bpCode.length ∧ r 44 = superLongSpan shape.bpCode.length ∧
    r 45 = superSlotCount shape.bpCode false ∧ r 46 = localSlotCount shape.bpCode false ∧
    r 47 = (sparseExceptionEffectiveFlagBits shape.bpCode false).length ∧
    r 48 = SuccinctRank.machineWordBits
      (SuccinctRank.machineWordBits shape.bpCode.length * SuccinctRank.machineWordBits shape.bpCode.length) ∧
    r 49 = sparseExceptionRelativeWidth shape.bpCode ∧
    r 50 = SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length ∧
    r 51 = SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length ∧
    r 52 = shape.bpCode.length / SuccinctRank.machineWordBits shape.bpCode.length /
      SuccinctRank.machineWordBits shape.bpCode.length + 1 ∧
    r 53 = shape.bpCode.length / SuccinctRank.machineWordBits shape.bpCode.length + 1 ∧
    r 54 = (longSuperFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length + 1 ∧
    r 55 = (sparseExceptionEffectiveFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length + 1 :=
  @accessRegs_of_bank

theorem spec_access_caps : ∀ {W : Nat} (shape : CartesianShape)
    (_ : 2 ^ 32 * (2 * shape.size + 4) ^ 8 < 2 ^ W),
    (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
      localStride shape.bpCode.length < 2 ^ W ∧ shape.bpCode.length + 1 < 2 ^ W :=
  @access_caps

theorem spec_accessPasses_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : GeoBase shape.size s.regs) (_ : GeoUpTo shape.size 39 s.regs)
    (_ : 2 ^ 32 * (2 * shape.size + 4) ^ 8 < 2 ^ W) (P0 R0 L0 C0 F0 G0 B : Nat) (_ : s.regs 119 = B)
    (_ : s.regs 159 = P0) (_ : s.regs 160 = R0) (_ : s.regs 161 = L0) (_ : s.regs 162 = C0)
    (_ : s.regs 163 = F0) (_ : s.regs 164 = G0) (_ : Region s B shape.bpCode.length (bpCell shape))
    (_ : B + shape.bpCode.length ≤ s.extent) (_ : P0 + shape.size + 1 ≤ R0)
    (_ : R0 + shape.bpCode.length / wordBits shape.bpCode.length + 1 ≤ L0)
    (_ : L0 + superSlotCount shape.bpCode false ≤ C0)
    (_ : C0 + superSlotCount shape.bpCode false + 1 ≤ F0)
    (_ : F0 + localSlotCount shape.bpCode false ≤ G0)
    (_ : G0 + localSlotCount shape.bpCode false + 1 ≤ B) (_ : s.extent < 2 ^ W),
    ∃ t k, (∀ (rest : Block) (t' : State) (k' : Nat), SafeEval W rest t t' k' →
        SafeEval W (.seq posPassBlock (.seq longFlagsBlock (.seq sparseFlagsBlock rest))) s t' (k + k')) ∧
      k ≤ (shape.bpCode.length + 1) * 20 + 7 + (superSlotCount shape.bpCode false * 39 + 6) +
        (localSlotCount shape.bpCode false * 64 + 6) ∧
      AccessReady W shape P0 R0 L0 C0 F0 G0 t ∧ t.extent = s.extent ∧
      (∀ a, (a < P0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) → t.memory a = s.memory a) ∧
      t.regs 177 = RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false)
        (superSlotCount shape.bpCode false) ∧
      t.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r, AccessHalfFrame r → t.regs r = s.regs r) ∧ t.keys = s.keys :=
  @accessPasses_spec

theorem spec_accessSegments_eq : ∀ (shape : CartesianShape),
    accessSegments shape =
      [ tableBits (SuccinctRank.canonicalSuperRankEntries false shape.bpCode
          (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
          (SuccinctRank.machineWordBits shape.bpCode.length),
        tableBits (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
          (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
          (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
            SuccinctRank.machineWordBits shape.bpCode.length)),
        tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets (superEntries shape.bpCode false))
          (superFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets (localEntries shape.bpCode false))
          (localFieldWidth shape.bpCode),
        tableBits (SuccinctRank.canonicalSuperRankEntries true (longSuperFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length),
        tableBits (SuccinctRank.canonicalBlockRankEntries true (longSuperFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length),
        longSuperFlagBits shape.bpCode false,
        tableBits (longSuperRelativeEntries shape.bpCode false) (longSuperRelativeWidth shape.bpCode),
        tableBits (SuccinctRank.canonicalSuperRankEntries true (sparseExceptionEffectiveFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length),
        tableBits (SuccinctRank.canonicalBlockRankEntries true (sparseExceptionEffectiveFlagBits shape.bpCode false)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
          (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length),
        sparseExceptionEffectiveFlagBits shape.bpCode false,
        tableBits (sparseExceptionRelativeEntries shape.bpCode false) (sparseExceptionRelativeWidth shape.bpCode) ] :=
  @accessSegments_eq

theorem spec_accessHalf_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (s : State)
    (_ : s.status = .running) (_ : GeoBase shape.size s.regs) (_ : GeoUpTo shape.size 39 s.regs)
    (_ : 2 ^ 32 * (2 * shape.size + 4) ^ 8 < 2 ^ W) (P0 R0 L0 C0 F0 G0 B : Nat) (_ : s.regs 119 = B)
    (_ : s.regs 159 = P0) (_ : s.regs 160 = R0) (_ : s.regs 161 = L0) (_ : s.regs 162 = C0)
    (_ : s.regs 163 = F0) (_ : s.regs 164 = G0) (_ : Region s B shape.bpCode.length (bpCell shape))
    (_ : B + shape.bpCode.length ≤ s.extent) (_ : P0 + shape.size + 1 ≤ R0)
    (_ : R0 + shape.bpCode.length / wordBits shape.bpCode.length + 1 ≤ L0)
    (_ : L0 + superSlotCount shape.bpCode false ≤ C0)
    (_ : C0 + superSlotCount shape.bpCode false + 1 ≤ F0)
    (_ : F0 + localSlotCount shape.bpCode false ≤ G0)
    (_ : G0 + localSlotCount shape.bpCode false + 1 ≤ B)
    (_ : s.extent + 16 * (400000 * (shape.size + 1)) < 2 ^ W),
    ∃ t s' k, SafeEval W accessHalfBlock s s' k ∧ k ≤ 200 * (400000 * (shape.size + 1)) ∧
      s'.status = .running ∧ t.extent = s.extent ∧
      (∀ a, (a < P0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) → t.memory a = s.memory a) ∧
      Emits t s' ((SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).map
        SuccinctSpace.bitToNat) ∧
      s'.regs 177 = RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false)
        (superSlotCount shape.bpCode false) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r, AccessHalfFrame r → s'.regs r = s.regs r) ∧ s'.keys = s.keys :=
  @accessHalf_spec

theorem spec_lc_eq_longCount : ∀ (shape : CartesianShape),
    RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) (superSlotCount shape.bpCode false) =
      RMQ.SuccinctFinal.PackedCellProbe.longCount shape :=
  @lc_eq_longCount

theorem spec_sc_eq_sparseCount : ∀ (shape : CartesianShape),
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) (localSlotCount shape.bpCode false) *
      localStride shape.bpCode.length = RMQ.SuccinctFinal.PackedCellProbe.packedReviewerSparseCount shape :=
  @sc_eq_sparseCount

end S5Access

/-! ## Executable S5 fixtures (array-backed interpreter on the compiled source)

The harness reserves the six access arrays (positions `n + 1` cells, word
boundary counts `2n / ws + 2`, long flags and their counts `sup + 1` each,
sparse-exception flags and their counts `loc + 1` each) in the layout order of
`accessHalf_spec`, then runs the Cartesian pass, the BP emission and
`accessHalfBlock`. The cells after the marker are compared with all eighteen
access segments. -/

def s5ArraysHarness : Block :=
  .seq (reserveArray 159 1) (.seq (reserveArray 160 53)
    (.seq (reserveArray 161 45) (.seq (reserveArray 162 45)
    (.seq (reserveArray 163 46) (reserveArray 164 46)))))

def s5Program : Array BInstr :=
  ((Block.seq (.action (.load 1 0)) (.seq constantsBlock (.seq geometryPrelude
    (.seq stackArraysBlock (.seq s5ArraysHarness
    (.seq (stackPassBlock keyLeaf)
    (.seq (acts [.reserve 131, .arithmetic .add 119 131 2])
    (.seq bpEmitBlock
    (.seq (acts [.reserve 199, .arithmetic .add 199 199 2])
      accessHalfBlock))))))))).compileAt 0 ++
    [(⟨.halt 3⟩ : BInstr)]).toArray

def s5Access (xs : List Int) : Bool :=
  let r := runArray s5Program 100000000 (ExecState.ofComparisonInput 200 xs)
  r.final.status == .halted 0 &&
    s3Cells r (r.final.regs.getD 199 0) ==
      ((Spec.accessSegments (Cartesian.shape xs)).flatten).map bitToNat

def stageGuard26 : Bool := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].all (fun n => s5Access (s4Input n))
def stageGuard27 : Bool := [12, 15, 16, 17, 24, 31, 33].all (fun n => s5Access (s4Input n))
def stageGuard28 : Bool := s5Access [1, 1, 1, 1] && s5Access [4, -3, -3, 8]
-- `crossBlockInput` of `RMQ.Validation.PackedQueryRuntime`, restated literally
def stageGuard29 : Bool := s5Access [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

/-! ## Stage S6: microtables, header patch, paddings and the bit buffer -/

theorem fringeDecodeActs_def : fringeDecodeActs =
    [.arithmetic .add 200 64 2, .arithmetic .mul 201 200 200,
      .arithmetic .div 202 14 201, .arithmetic .div 203 14 200,
      .arithmetic .mod 203 203 200, .arithmetic .mod 204 14 200,
      .move 205 64, .constant 206 0, .constant 207 0] := rfl

theorem fringeStepBlock_def : fringeStepBlock =
    acts [.comparison .eq 210 208 203, .comparison .lt 211 203 208,
      .comparison .lt 212 208 204, .arithmetic .mul 211 211 212,
      .comparison .lt 212 205 207, .arithmetic .mul 211 211 212,
      .arithmetic .add 210 210 211, .arithmetic .sub 211 2 210,
      .arithmetic .mul 212 210 205, .arithmetic .mul 213 211 207, .arithmetic .add 207 212 213,
      .arithmetic .mul 212 210 208, .arithmetic .mul 213 211 206, .arithmetic .add 206 212 213,
      .comparison .lt 210 208 64, .arithmetic .mod 211 202 9,
      .arithmetic .div 202 202 9, .arithmetic .mul 211 211 9,
      .arithmetic .mul 211 211 210, .arithmetic .add 205 205 211,
      .arithmetic .sub 205 205 210] := rfl

theorem fringeEntryBlock_def : fringeEntryBlock =
    .seq (acts fringeDecodeActs)
    (.seq (forSlots 208 209 200 fringeStepBlock)
      (acts [.arithmetic .add 210 200 200, .arithmetic .mul 210 205 210,
        .arithmetic .add 210 210 207, .arithmetic .mul 210 210 200,
        .arithmetic .add 16 210 206])) := rfl

theorem selectDecodeActs_def : selectDecodeActs =
    [.arithmetic .add 200 64 2, .arithmetic .div 214 14 200,
      .arithmetic .mod 215 14 200, .constant 216 0, .move 217 64] := rfl

theorem selectStepBlock_def : selectStepBlock =
    acts [.arithmetic .mod 210 214 9, .arithmetic .div 214 214 9,
      .arithmetic .sub 210 2 210, .comparison .eq 211 216 215,
      .arithmetic .mul 211 211 210, .arithmetic .sub 212 2 211,
      .arithmetic .mul 213 211 208, .arithmetic .mul 212 212 217,
      .arithmetic .add 217 213 212, .arithmetic .add 216 216 210] := rfl

theorem selectEntryBlock_def : selectEntryBlock =
    .seq (acts selectDecodeActs)
    (.seq (forSlots 208 209 64 selectStepBlock)
      (acts [.move 16 217])) := rfl

theorem microtablesBlock_def : microtablesBlock =
    .seq (emitTable 65 66 fringeEntryBlock) (emitTable 67 68 selectEntryBlock) := rfl

theorem headerReserveBlock_def : headerReserveBlock =
    .seq (acts [.arithmetic .sub 226 75 2])
      (.seq (reserveArray 220 226) (acts [.arithmetic .add 119 220 75])) := rfl

theorem headerPatchStepBlock_def : headerPatchStepBlock =
    acts [.arithmetic .add 108 220 222, .arithmetic .mod 226 221 9, .store 108 226,
      .arithmetic .div 221 221 9] := rfl

theorem headerPatchBlock_def : headerPatchBlock =
    .seq (acts [.move 221 177]) (forSlots 222 223 75 headerPatchStepBlock) := rfl

theorem zerosBlock_def : ∀ (cnt : Operand), zerosBlock cnt =
    .seq (acts [.move 12 cnt])
      (.loop 12 (.seq (emitBit 0) (.action (.arithmetic .sub 12 12 2)))) := fun _ => rfl

theorem padBlock_def : padBlock =
    .seq (acts [.reserve 224, .store 224 0,
      .arithmetic .sub 226 224 220,
      .arithmetic .sub 227 226 75, .arithmetic .add 227 227 75,
      .arithmetic .sub 227 227 2, .arithmetic .div 227 227 75,
      .arithmetic .add 227 227 2, .arithmetic .mul 227 227 75,
      .arithmetic .add 228 227 76, .arithmetic .sub 228 228 2,
      .arithmetic .div 228 228 76, .arithmetic .mul 228 228 76,
      .arithmetic .sub 225 228 226, .comparison .lt 227 226 228,
      .arithmetic .sub 225 225 227])
      (zerosBlock 225) := rfl

theorem bufferBlock_def : bufferBlock =
    .seq headerReserveBlock (.seq bpEmitBlock (.seq accessHalfBlock (.seq interiorCloseBlock
      (.seq microtablesBlock (.seq headerPatchBlock padBlock))))) := rfl

theorem spec_MicroWrites_def : ∀ r : Nat, MicroWrites r ↔ (200 ≤ r ∧ r ≤ 219) := fun _ => Iff.rfl

theorem spec_BufferKept_def : ∀ r : Nat, BufferKept r ↔
    (r ≤ 3 ∨ r = 9 ∨ (29 ≤ r ∧ r ≤ 99) ∨ (115 ≤ r ∧ r ≤ 118) ∨ r = 135 ∨ r = 136 ∨
      (159 ≤ r ∧ r ≤ 164) ∨ 229 ≤ r) := fun _ => Iff.rfl

theorem spec_BufferFrame_def : ∀ r : Nat, BufferFrame r ↔
    (¬ (4 ≤ r ∧ r ≤ 28) ∧ ¬ (100 ≤ r ∧ r ≤ 228)) := fun _ => Iff.rfl

theorem spec_EmitsFrom_def : ∀ (base : Nat) (s₀ s : State) (vals : List Nat),
    EmitsFrom base s₀ s vals ↔ (s.extent = s₀.extent + vals.length ∧
      ∀ a, base ≤ a → s.memory a =
        if s₀.extent ≤ a ∧ a < s₀.extent + vals.length then vals[a - s₀.extent]? else s₀.memory a) :=
  fun _ _ _ _ => Iff.rfl

theorem spec_denseBitsOf_def : ∀ oldW WW L : Nat,
    denseBitsOf oldW WW L = (((L - 1) / oldW + 1) * oldW + WW - 1) / WW * WW := fun _ _ _ => rfl

section S6Buffer

open RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedConstruction.Spec RMQ.GenericSelect

theorem spec_natToBitsLE_getElem :
    ∀ (c v t : Nat), t < c →
    (SuccinctSpace.natToBitsLE c v)[t]? = some (decide (v / 2 ^ t % 2 = 1)) :=
  @Spec.natToBitsLE_getElem?

theorem spec_pattern_getElem : ∀ {c t : Nat} (v : Nat) (_ : t < c),
    (bpFringeChunkPattern c v)[t]? = some (decide (v / 2 ^ t % 2 = 1)) :=
  @Spec.pattern_getElem?

theorem spec_pattern_rank_true_succ : ∀ {c t : Nat} (v : Nat) (_ : t < c),
    RMQ.Succinct.rankPrefix true (bpFringeChunkPattern c v) (t + 1) =
      RMQ.Succinct.rankPrefix true (bpFringeChunkPattern c v) t + v / 2 ^ t % 2 :=
  @Spec.pattern_rank_true_succ

theorem spec_pattern_rank_false_succ : ∀ {c t : Nat} (v : Nat) (_ : t < c),
    RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1) =
      RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t + (1 - v / 2 ^ t % 2) :=
  @Spec.pattern_rank_false_succ

theorem spec_excessOffset_succ : ∀ {c t : Nat} (v : Nat) (_ : t < c),
    bpFringeChunkExcessOffsetAt c v (t + 1) + 1 =
      bpFringeChunkExcessOffsetAt c v t + 2 * (v / 2 ^ t % 2) ∧
      1 ≤ bpFringeChunkExcessOffsetAt c v t :=
  @Spec.excessOffset_succ

theorem spec_scanArgMin_snoc : ∀ (f : Nat → Nat) (a m : Nat) (_ : 1 ≤ m),
    bpFringeScanArgMin f a (m + 1) = bpFringeScanBetter f (bpFringeScanArgMin f a m) (a + m) :=
  @Spec.scanArgMin_snoc

theorem spec_selectPos_step : ∀ {c t k : Nat} (v : Nat) (_ : t < c) (pos : Nat)
    (_ : pos = if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t
      then bpChunkSelectPos c false v k else c),
    (if RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t = k then 1 else 0) *
        (1 - v / 2 ^ t % 2) * t +
      (1 - (if RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t = k then 1 else 0) *
        (1 - v / 2 ^ t % 2)) * pos =
    if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1)
      then bpChunkSelectPos c false v k else c :=
  @Spec.selectPos_step

theorem spec_selectPos_final : ∀ (c v k : Nat),
    (if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) c
      then bpChunkSelectPos c false v k else c) = bpChunkSelectPos c false v k :=
  @Spec.selectPos_final

theorem spec_fringeBest_step : ∀ (f : Nat → Nat) (a b t bp bv : Nat)
    (_ : a < t → bp = bpFringeScanArgMin f a (min t b - a) ∧ bv = f bp) (_ : a ≤ t),
    ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0)) * t +
      (1 - ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0))) * bp =
        bpFringeScanArgMin f a (min (t + 1) b - a) ∧
    ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0)) * f t +
      (1 - ((if t = a then 1 else 0) +
        (if a < t then 1 else 0) * (if t < b then 1 else 0) * (if f t < bv then 1 else 0))) * bv =
        f (bpFringeScanArgMin f a (min (t + 1) b - a)) :=
  @Spec.fringeBest_step

theorem spec_selectStep_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (_ : u.regs 2 = 1) (_ : u.regs 9 = 2) (c v k t : Nat) (_ : t < c) (_ : c + 1 < 2 ^ W)
    (_ : v < 2 ^ W) (_ : u.regs 208 = t) (_ : u.regs 214 = v / 2 ^ t) (_ : u.regs 215 = k)
    (_ : u.regs 216 = RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t)
    (_ : u.regs 217 = if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) t
      then bpChunkSelectPos c false v k else c),
    ∃ u' j, SafeEval W selectStepBlock u u' j ∧ j ≤ 10 ∧ u'.status = .running ∧
      u'.regs 214 = v / 2 ^ (t + 1) ∧
      u'.regs 216 = RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1) ∧
      u'.regs 217 = (if k < RMQ.Succinct.rankPrefix false (bpFringeChunkPattern c v) (t + 1)
        then bpChunkSelectPos c false v k else c) ∧
      (∀ r, ¬ (210 ≤ r ∧ r ≤ 214) → r ≠ 216 → r ≠ 217 → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @selectStep_spec

theorem spec_selectEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (_ : u.regs 2 = 1) (_ : u.regs 9 = 2) (c slot : Nat) (_ : u.regs 64 = c) (_ : u.regs 14 = slot)
    (_ : slot < bpChunkSelectRowCount c) (_ : bpChunkSelectRowCount c + c + 1 < 2 ^ W),
    EntryOK W selectEntryBlock MicroWrites u
      (bpChunkSelectPos c false (slot / (c + 1)) (slot % (c + 1))) (14 * c + 9) :=
  @selectEntry_spec

theorem spec_selectTable_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running)
    (_ : s.regs 2 = 1) (_ : s.regs 9 = 2) (c : Nat) (_ : s.regs 64 = c)
    (_ : s.regs 67 = bpChunkSelectRowCount c) (_ : s.regs 68 = bpChunkSelectEntryWidth c)
    (_ : bpChunkSelectRowCount c + c + 1 < 2 ^ W)
    (_ : s.extent + bpChunkSelectRowCount c * bpChunkSelectEntryWidth c < 2 ^ W),
    ∃ s' k, SafeEval W (emitTable rSROWS rSWID selectEntryBlock) s s' k ∧
      k ≤ bpChunkSelectRowCount c * (14 * c + 9 + 7 * bpChunkSelectEntryWidth c + 7) + 3 ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ MicroWrites r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @selectTable_spec

theorem spec_fringeStep_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (_ : u.regs 2 = 1) (_ : u.regs 9 = 2) (c v a b t bp bv : Nat) (_ : t ≤ c) (_ : a ≤ c)
    (_ : b ≤ c) (_ : 4 * c + 4 < 2 ^ W) (_ : v < 2 ^ W) (_ : u.regs 64 = c)
    (_ : u.regs 202 = v / 2 ^ t) (_ : u.regs 203 = a) (_ : u.regs 204 = b)
    (_ : u.regs 205 = bpFringeChunkExcessOffsetAt c v t) (_ : u.regs 206 = bp) (_ : u.regs 207 = bv)
    (_ : u.regs 208 = t) (_ : bp ≤ c) (_ : bv ≤ 2 * c)
    (_ : a < t → bp = bpFringeScanArgMin (bpFringeChunkExcessOffsetAt c v) a (min t b - a) ∧
      bv = bpFringeChunkExcessOffsetAt c v bp),
    ∃ u' j, SafeEval W fringeStepBlock u u' j ∧ j ≤ 21 ∧ u'.status = .running ∧
      u'.regs 202 = v / 2 ^ (t + 1) ∧
      u'.regs 205 = bpFringeChunkExcessOffsetAt c v (min (t + 1) c) ∧
      u'.regs 206 ≤ c ∧ u'.regs 207 ≤ 2 * c ∧
      (a < t + 1 → u'.regs 206 =
          bpFringeScanArgMin (bpFringeChunkExcessOffsetAt c v) a (min (t + 1) b - a) ∧
        u'.regs 207 = bpFringeChunkExcessOffsetAt c v (u'.regs 206)) ∧
      (∀ r, r ≠ 202 → ¬ (205 ≤ r ∧ r ≤ 207) → ¬ (210 ≤ r ∧ r ≤ 213) → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @fringeStep_spec

theorem spec_fringeEntry_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (_ : u.regs 2 = 1) (_ : u.regs 9 = 2) (c slot : Nat) (_ : u.regs 64 = c) (_ : u.regs 14 = slot)
    (_ : slot < bpFringeChunkRowCount c)
    (_ : bpFringeChunkRowCount c + 16 * ((c + 1) * (c + 1) * (c + 1)) < 2 ^ W),
    EntryOK W fringeEntryBlock MicroWrites u
      (bpFringeChunkPacked c (slot / ((c + 1) * (c + 1))) (slot / (c + 1) % (c + 1)) (slot % (c + 1)))
      (25 * c + 42) :=
  @fringeEntry_spec

theorem spec_fringeTable_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running)
    (_ : s.regs 2 = 1) (_ : s.regs 9 = 2) (c : Nat) (_ : s.regs 64 = c)
    (_ : s.regs 65 = bpFringeChunkRowCount c) (_ : s.regs 66 = bpFringeChunkEntryWidth c)
    (_ : bpFringeChunkRowCount c + 16 * ((c + 1) * (c + 1) * (c + 1)) < 2 ^ W)
    (_ : s.extent + bpFringeChunkRowCount c * bpFringeChunkEntryWidth c < 2 ^ W),
    ∃ s' k, SafeEval W (emitTable rFROWS rFWID fringeEntryBlock) s s' k ∧
      k ≤ bpFringeChunkRowCount c * (25 * c + 42 + 7 * bpFringeChunkEntryWidth c + 7) + 3 ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).map
        SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ MicroWrites r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @fringeTable_spec

theorem spec_microtables_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running)
    (_ : s.regs 2 = 1) (_ : s.regs 9 = 2) (c : Nat) (_ : s.regs 64 = c)
    (_ : s.regs 65 = bpFringeChunkRowCount c) (_ : s.regs 66 = bpFringeChunkEntryWidth c)
    (_ : s.regs 67 = bpChunkSelectRowCount c) (_ : s.regs 68 = bpChunkSelectEntryWidth c)
    (_ : bpFringeChunkRowCount c + bpChunkSelectRowCount c + 16 * ((c + 1) * (c + 1) * (c + 1)) <
      2 ^ W)
    (_ : s.extent + (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).length +
      (tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).length < 2 ^ W),
    ∃ s' k, SafeEval W microtablesBlock s s' k ∧
      k ≤ bpFringeChunkRowCount c * (25 * c + 42 + 7 * bpFringeChunkEntryWidth c + 7) + 3 +
        (bpChunkSelectRowCount c * (14 * c + 9 + 7 * bpChunkSelectEntryWidth c + 7) + 3) ∧
      s'.status = .running ∧
      Emits s s' ((tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c) ++
        tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map SuccinctSpace.bitToNat) ∧
      (∀ r, ¬ MicroWrites r → ¬ TableScratch r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @microtables_spec

theorem spec_zeroLoop_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running)
    (_ : s.regs 0 = 0) (_ : s.regs 2 = 1) (N : Nat) (_ : s.regs 12 = N)
    (_ : s.extent + N + 1 < 2 ^ W),
    ∃ s' k, SafeEval W (.loop rECNT (.seq (emitBit rZERO) (.action (.arithmetic .sub rECNT rECNT rONE))))
        s s' k ∧ k ≤ 5 * N + 1 ∧ s'.status = .running ∧ Emits s s' (List.replicate N 0) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @zeroLoop_spec

theorem spec_zeros_spec : ∀ {W : Nat} (_ : 32 ≤ W) (cnt : Operand) (s : State)
    (_ : s.status = .running) (_ : s.regs 0 = 0) (_ : s.regs 2 = 1)
    (_ : s.extent + s.regs cnt + 1 < 2 ^ W),
    ∃ s' k, SafeEval W (zerosBlock cnt) s s' k ∧ k ≤ 5 * s.regs cnt + 2 ∧ s'.status = .running ∧
      Emits s s' (List.replicate (s.regs cnt) 0) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @zeros_spec

theorem spec_headerReserve_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running)
    (_ : s.regs 0 = 0) (_ : s.regs 2 = 1) (oldW : Nat) (_ : s.regs 75 = oldW) (_ : 1 ≤ oldW)
    (_ : s.extent + oldW + 1 < 2 ^ W),
    ∃ s' k, SafeEval W headerReserveBlock s s' k ∧ k ≤ 5 * oldW + 2 ∧ s'.status = .running ∧
      Emits s s' (List.replicate oldW 0) ∧ s'.regs 220 = s.extent ∧
      s'.regs 119 = s.extent + oldW ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → r ≠ 119 → r ≠ 220 → r ≠ 226 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @headerReserve_spec

theorem spec_headerPatch_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (_ : u.regs 2 = 1) (_ : u.regs 9 = 2) (buf oldW lc : Nat) (_ : u.regs 220 = buf)
    (_ : u.regs 75 = oldW) (_ : u.regs 177 = lc) (_ : lc < 2 ^ W) (_ : buf + oldW ≤ u.extent)
    (_ : u.extent < 2 ^ W),
    ∃ u' k, SafeEval W headerPatchBlock u u' k ∧ k ≤ 8 * oldW + 4 ∧ u'.status = .running ∧
      u'.extent = u.extent ∧
      (∀ a, u'.memory a =
        if buf ≤ a ∧ a < buf + oldW then some (lc / 2 ^ (a - buf) % 2) else u.memory a) ∧
      (∀ r : Nat, r ≠ 108 → ¬ (221 ≤ r ∧ r ≤ 223) → r ≠ 226 → u'.regs r = u.regs r) ∧
      u'.keyRegs = u.keyRegs ∧ u'.keys = u.keys :=
  @headerPatch_spec

theorem spec_prefix_reserve : ∀ {W : Nat} (_ : 32 ≤ W) (d : Operand) (v : State)
    (_ : v.status = .running) (_ : v.extent + 1 < 2 ^ W),
    ∃ v', ActsPrefix W [.reserve d] v v' 1 ∧ v'.regs = put v.regs d v.extent ∧
      v'.memory = v.memory ∧ v'.extent = v.extent + 1 ∧ v'.keys = v.keys ∧
      v'.keyRegs = v.keyRegs :=
  @prefix_reserve

theorem spec_pad_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running)
    (_ : u.regs 0 = 0) (_ : u.regs 2 = 1) (buf L oldW WW : Nat) (_ : u.regs 220 = buf)
    (_ : u.extent = buf + L) (_ : u.regs 75 = oldW) (_ : u.regs 76 = WW) (_ : 1 ≤ oldW) (_ : 1 ≤ WW)
    (_ : oldW ≤ L) (_ : buf + L + oldW + WW + 2 < 2 ^ W),
    ∃ s' k, SafeEval W padBlock u s' k ∧ k ≤ 5 * (denseBitsOf oldW WW L - L) + 18 ∧
      s'.status = .running ∧ L ≤ denseBitsOf oldW WW L ∧ denseBitsOf oldW WW L ≤ L + oldW + WW ∧
      Emits u s' (List.replicate (denseBitsOf oldW WW L - L -
        (if L < denseBitsOf oldW WW L then 1 else 0) + 1) 0) ∧
      (∀ r : Nat, r ≠ 10 → r ≠ 12 → ¬ (224 ≤ r ∧ r ≤ 228) → s'.regs r = u.regs r) ∧
      s'.keyRegs = u.keyRegs ∧ s'.keys = u.keys :=
  @pad_spec

theorem spec_GeoBase_congr : ∀ {n : Nat} {r r' : Registers} (_ : GeoBase n r)
    (_ : ∀ x : Nat, (x = 1 ∨ x = 2 ∨ x = 9 ∨ (30 ≤ x ∧ x ≤ 37)) → r' x = r x),
    GeoBase n r' :=
  @GeoBase.congr

theorem spec_GeoUpTo_congr : ∀ {n k : Nat} {r r' : Registers} (_ : GeoUpTo n k r)
    (_ : ∀ x : Nat, 38 ≤ x → x < 38 + k → r' x = r x),
    GeoUpTo n k r' :=
  @GeoUpTo.congr

theorem spec_Emits_shiftFrom : ∀ {base : Nat} {u t s : State} {vals : List Nat} (_ : Emits t s vals)
    (_ : t.extent = u.extent) (_ : ∀ a, base ≤ a → t.memory a = u.memory a),
    EmitsFrom base u s vals :=
  @Emits.shiftFrom

theorem spec_EmitsFrom_trans : ∀ {base : Nat} {s₀ s₁ s₂ : State} {v w : List Nat}
    (_ : EmitsFrom base s₀ s₁ v) (_ : EmitsFrom base s₁ s₂ w),
    EmitsFrom base s₀ s₂ (v ++ w) :=
  @EmitsFrom.trans

theorem spec_EmitsFrom_memory_at : ∀ {base : Nat} {s₀ s : State} {vals : List Nat}
    (_ : EmitsFrom base s₀ s vals) (_ : base ≤ s₀.extent) {i : Nat} (_ : i < vals.length),
    s.memory (s₀.extent + i) = some vals[i] :=
  @EmitsFrom.memory_at

theorem spec_bufferCells_getD : ∀ (shape : CartesianShape) (i : Nat),
    ((PackedWordRAM.densePad (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerPaddedBits shape)).map bitToNat).getD i 0 =
      if i < PackedCellProbe.packedReviewerCellWidth shape.size then
        PackedCellProbe.longCount shape / 2 ^ i % 2
      else ((PackedCellProbe.packedReviewerPayloadBits shape).map bitToNat).getD
        (i - PackedCellProbe.packedReviewerCellWidth shape.size) 0 :=
  @bufferCells_getD

theorem spec_bufferCells_length : ∀ (shape : CartesianShape),
    ((PackedWordRAM.densePad (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerPaddedBits shape)).map bitToNat).length =
      denseBitsOf (PackedCellProbe.packedReviewerCellWidth shape.size)
        (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerCellWidth shape.size +
          PackedCellProbe.packedReviewerPayloadLength shape.size (PackedCellProbe.longCount shape)
            (PackedCellProbe.packedReviewerSparseCount shape)) :=
  @bufferCells_length

theorem spec_bufferTail_spec : ∀ {W : Nat} (_ : 32 ≤ W) (n c oldW WW buf lc : Nat)
    (_ : bpFringeChunkBits (2 * n) = c) (_ : PackedCellProbe.packedReviewerCellWidth n = oldW)
    (_ : PackedWordRAM.wordWidth n = WW) (sC u0 : State) (_ : sC.status = .running)
    (_ : GeoUpTo n 39 sC.regs) (_ : sC.regs 0 = 0) (_ : sC.regs 2 = 1) (_ : sC.regs 9 = 2)
    (_ : sC.regs 220 = buf) (_ : sC.regs 177 = lc) (_ : lc ≤ n) (Q : List Nat) (_ : u0.extent = buf)
    (_ : EmitsFrom buf u0 sC (List.replicate oldW 0 ++ Q))
    (_ : Q.length + (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).length +
      (tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).length + 2 ≤
        400000 * (n + 1))
    (_ : buf + 8 * (400000 * (n + 1)) < 2 ^ W),
    ∃ s' k, SafeEval W (.seq microtablesBlock (.seq headerPatchBlock padBlock)) sC s' k ∧
      k ≤ 100 * (400000 * (n + 1)) ∧ s'.status = .running ∧
      buf + denseBitsOf oldW WW (oldW + (Q ++ (tableBits (bpFringeChunkEntries c)
          (bpFringeChunkEntryWidth c) ++ tableBits (bpChunkSelectEntries c false)
          (bpChunkSelectEntryWidth c)).map bitToNat).length) ≤ s'.extent ∧
      s'.extent ≤ buf + denseBitsOf oldW WW (oldW + (Q ++ (tableBits (bpFringeChunkEntries c)
          (bpFringeChunkEntryWidth c) ++ tableBits (bpChunkSelectEntries c false)
          (bpChunkSelectEntryWidth c)).map bitToNat).length) + 1 ∧
      (∀ i, i < denseBitsOf oldW WW (oldW + (Q ++ (tableBits (bpFringeChunkEntries c)
          (bpFringeChunkEntryWidth c) ++ tableBits (bpChunkSelectEntries c false)
          (bpChunkSelectEntryWidth c)).map bitToNat).length) →
        s'.memory (buf + i) = some (if i < oldW then lc / 2 ^ i % 2 else
          (Q ++ (tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c) ++
            tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map bitToNat).getD
            (i - oldW) 0)) ∧
      (∀ a, a < buf → s'.memory a = sC.memory a) ∧
      (∀ r, BufferKept r → s'.regs r = sC.regs r) ∧
      s'.regs 220 = buf ∧ s'.regs 177 = lc ∧ s'.regs 178 = sC.regs 178 ∧ s'.keys = sC.keys :=
  @bufferTail_spec

theorem spec_bufferAccessClose_spec : ∀ {W : Nat} (_ : 32 ≤ W) (shape : CartesianShape) (n : Nat)
    (_ : shape.size = n) (sB : State) (_ : sB.status = .running) (_ : GeoBase n sB.regs)
    (_ : GeoUpTo n 39 sB.regs) (_ : 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W)
    (P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb buf B : Nat) (_ : sB.regs 119 = B) (_ : sB.regs 159 = P0)
    (_ : sB.regs 160 = R0) (_ : sB.regs 161 = L0) (_ : sB.regs 162 = C0) (_ : sB.regs 163 = F0)
    (_ : sB.regs 164 = G0) (_ : sB.regs 115 = A0) (_ : sB.regs 116 = A1) (_ : sB.regs 117 = A2)
    (_ : sB.regs 118 = A3) (_ : sB.regs 135 = Bm) (_ : sB.regs 136 = Gb)
    (_ : Region sB B shape.bpCode.length (bpCell shape)) (_ : sB.extent = B + shape.bpCode.length)
    (_ : P0 + n + 1 ≤ R0) (_ : R0 + shape.bpCode.length / wordBits shape.bpCode.length + 1 ≤ L0)
    (_ : L0 + superSlotCount shape.bpCode false ≤ C0)
    (_ : C0 + superSlotCount shape.bpCode false + 1 ≤ F0)
    (_ : F0 + localSlotCount shape.bpCode false ≤ G0)
    (_ : G0 + localSlotCount shape.bpCode false + 1 ≤ buf) (_ : A0 + geoBlocks n + 1 ≤ A1)
    (_ : A1 + geoBlocks n ≤ A2) (_ : A2 + geoBlocks n ≤ A3) (_ : A3 + geoBlocks n ≤ Bm)
    (_ : Bm + SuccinctRank.machineWordBits (geoMacro n) * geoBlocks n ≤ Gb)
    (_ : Gb + SuccinctRank.machineWordBits (geoMacros n) * geoMacros n ≤ buf) (_ : buf ≤ B)
    (_ : sB.extent + 17 * (400000 * (n + 1)) < 2 ^ W),
    ∃ sX sC kA kC, SafeEval W accessHalfBlock sB sX kA ∧ SafeEval W interiorCloseBlock sX sC kC ∧
      kA + kC ≤ 1800 * (400000 * (n + 1)) ∧ sC.status = .running ∧
      EmitsFrom buf sB sC
        ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).map bitToNat ++
          (canonicalRelativeRmmInteriorDirectory shape).payload.map bitToNat) ∧
      (∀ a, a < buf → (a < P0 ∨ G0 + localSlotCount shape.bpCode false + 1 ≤ a) →
        (a < A0 ∨ Gb + SuccinctRank.machineWordBits (geoMacros n) * geoMacros n ≤ a) →
        sC.memory a = sB.memory a) ∧
      sC.regs 177 = PackedCellProbe.longCount shape ∧
      sC.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
        (localSlotCount shape.bpCode false) ∧
      (∀ r, BufferKept r → sC.regs r = sB.regs r) ∧ sC.regs 220 = sB.regs 220 ∧
      sC.keys = sB.keys :=
  @bufferAccessClose_spec

theorem spec_bufferHead_spec : ∀ {W : Nat} (_ : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (_ : KeySpec W xs Inp leaf) (s : State) (_ : s.status = .running)
    (_ : s.regs 0 = 0) (_ : s.regs 2 = 1) (_ : s.regs 1 = xs.length) (_ : Inp s)
    (_ : InpBelow Inp s.extent) (oldW : Nat) (_ : s.regs 75 = oldW) (_ : 1 ≤ oldW)
    (_ : s.extent + 3 * (xs.length + 1) + oldW + 2 * xs.length + 2 < 2 ^ W),
    ∃ sA sP sH sB k1 k2 kH kE, SafeEval W stackArraysBlock s sA k1 ∧
      SafeEval W (stackPassBlock leaf) sA sP k2 ∧ SafeEval W headerReserveBlock sP sH kH ∧
      SafeEval W bpEmitBlock sH sB kE ∧ k1 + k2 + kH + kE ≤ 79 * xs.length + 21 + 5 * oldW ∧
      sB.status = .running ∧ sP.extent = s.extent + 3 * (xs.length + 1) ∧
      EmitsFrom (s.extent + 3 * (xs.length + 1)) sP sB
        (List.replicate oldW 0 ++ (shape xs).bpCode.map bitToNat) ∧
      sB.extent = s.extent + 3 * (xs.length + 1) + oldW + (shape xs).bpCode.length ∧
      Region sB (s.extent + 3 * (xs.length + 1) + oldW) (shape xs).bpCode.length (bpCell (shape xs)) ∧
      (∀ a, a < s.extent → sB.memory a = s.memory a) ∧
      sB.regs 119 = s.extent + 3 * (xs.length + 1) + oldW ∧
      sB.regs 220 = s.extent + 3 * (xs.length + 1) ∧
      (∀ r, BufferKept r → sB.regs r = s.regs r) ∧ sB.keys = s.keys :=
  @bufferHead_spec

theorem spec_bufferStage_spec : ∀ {W : Nat} (_ : 32 ≤ W) (xs : List Int) (Inp : State → Prop)
    (leaf : Block) (_ : KeySpec W xs Inp leaf) (s : State) (_ : s.status = .running)
    (_ : s.regs 0 = 0) (_ : GeoBase xs.length s.regs) (_ : GeoUpTo xs.length 39 s.regs)
    (_ : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W) (_ : Inp s) (_ : InpBelow Inp s.extent)
    (P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb : Nat) (_ : s.regs 159 = P0) (_ : s.regs 160 = R0)
    (_ : s.regs 161 = L0) (_ : s.regs 162 = C0) (_ : s.regs 163 = F0) (_ : s.regs 164 = G0)
    (_ : s.regs 115 = A0) (_ : s.regs 116 = A1) (_ : s.regs 117 = A2) (_ : s.regs 118 = A3)
    (_ : s.regs 135 = Bm) (_ : s.regs 136 = Gb) (_ : P0 + xs.length + 1 ≤ R0)
    (_ : R0 + (shape xs).bpCode.length / wordBits (shape xs).bpCode.length + 1 ≤ L0)
    (_ : L0 + superSlotCount (shape xs).bpCode false ≤ C0)
    (_ : C0 + superSlotCount (shape xs).bpCode false + 1 ≤ F0)
    (_ : F0 + localSlotCount (shape xs).bpCode false ≤ G0)
    (_ : G0 + localSlotCount (shape xs).bpCode false + 1 ≤ s.extent)
    (_ : A0 + geoBlocks xs.length + 1 ≤ A1) (_ : A1 + geoBlocks xs.length ≤ A2)
    (_ : A2 + geoBlocks xs.length ≤ A3) (_ : A3 + geoBlocks xs.length ≤ Bm)
    (_ : Bm + SuccinctRank.machineWordBits (geoMacro xs.length) * geoBlocks xs.length ≤ Gb)
    (_ : Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ s.extent)
    (_ : s.extent + 32 * (400000 * (xs.length + 1)) < 2 ^ W),
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock leaf) bufferBlock)) s s' k ∧
      k ≤ 2000 * (400000 * (xs.length + 1)) ∧ s'.status = .running ∧
      s'.regs 220 = s.extent + 3 * (xs.length + 1) ∧
      ArrayAt s' (s.extent + 3 * (xs.length + 1))
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length
        (fun i => ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).getD i 0) ∧
      s'.extent ≤ s.extent + 3 * (xs.length + 1) +
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length + 1 ∧
      (∀ a, a < s.extent → (a < P0 ∨ G0 + localSlotCount (shape xs).bpCode false + 1 ≤ a) →
        (a < A0 ∨ Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ a) →
        s'.memory a = s.memory a) ∧
      s'.regs 177 = PackedCellProbe.longCount (shape xs) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits (shape xs).bpCode false)
        (localSlotCount (shape xs).bpCode false) ∧
      (∀ r, BufferFrame r → s'.regs r = s.regs r) ∧ s'.keys = s.keys :=
  @bufferStage_spec

end S6Buffer

/-! ## Executable S6 fixtures (array-backed interpreter on the compiled source)

The microtable harness runs the geometry prelude and `microtablesBlock` after a
marker cell and compares every cell after the marker with the fringe and
select-chunk tables at `c = bpFringeChunkBits (2n)` (`c = 1` for `n < 128`,
`c = 2` at `n = 128`). The buffer harness reserves the access arrays and the
interior statistics and memo arrays in the layout order of `bufferStage_spec`,
then runs the stack arrays, the Cartesian pass and `bufferBlock`: the first
`denseCount * W` cells at register 220 must be the dense buffer of the
reference, and the extent may exceed them by at most the probe cell. -/

def s6MicroProgram : Array BInstr :=
  ((Block.seq (.action (.load 1 0)) (.seq constantsBlock (.seq geometryPrelude
    (.seq (acts [.reserve 199, .arithmetic .add 199 199 2])
      microtablesBlock)))).compileAt 0 ++
    [(⟨.halt 3⟩ : BInstr)]).toArray

def s6Micro (n : Nat) : Bool :=
  let r := runArray s6MicroProgram 100000000 (ExecState.ofComparisonInput 260 (List.replicate n 0))
  let c := bpFringeChunkBits (2 * n)
  r.final.status == .halted 0 &&
    s3Cells r (r.final.regs.getD 199 0) ==
      (Spec.tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c) ++
        Spec.tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map bitToNat

def stageGuard30 : Bool := [0, 1, 5, 127, 128].all s6Micro

def s6ArraysHarness : Block :=
  .seq (reserveArray 159 1) (.seq (reserveArray 160 53)
    (.seq (reserveArray 161 45) (.seq (reserveArray 162 45)
    (.seq (reserveArray 163 46) (.seq (reserveArray 164 46)
    (.seq (reserveArray 115 32) (.seq (reserveArray 116 32)
    (.seq (reserveArray 117 32) (.seq (reserveArray 118 32)
    (.seq (acts [.arithmetic .mul 198 58 32]) (.seq (reserveArray 135 198)
    (.seq (acts [.arithmetic .mul 198 59 33]) (reserveArray 136 198)))))))))))))

def s6BufferProgram : Array BInstr :=
  ((Block.seq (.action (.load 1 0)) (.seq constantsBlock (.seq geometryPrelude
    (.seq s6ArraysHarness
    (.seq stackArraysBlock (.seq (stackPassBlock keyLeaf) bufferBlock)))))).compileAt 0 ++
    [(⟨.halt 3⟩ : BInstr)]).toArray

def s6Buffer (xs : List Int) : Bool :=
  let r := runArray s6BufferProgram 100000000 (ExecState.ofComparisonInput 260 xs)
  let e := (SuccinctFinal.PackedWordRAM.densePad (SuccinctFinal.PackedWordRAM.wordWidth xs.length)
    (SuccinctFinal.PackedCellProbe.packedReviewerPaddedBits (Cartesian.shape xs))).map bitToNat
  let cells := s3Cells r (r.final.regs.getD 220 0)
  r.final.status == .halted 0 && cells.take e.length == e &&
    e.length ≤ cells.length && cells.length ≤ e.length + 1

def stageGuard31 : Bool := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9].all (fun n => s6Buffer (s4Input n))
def stageGuard32 : Bool := [12, 15, 16, 17, 24, 31, 33].all (fun n => s6Buffer (s4Input n))
def stageGuard33 : Bool := s6Buffer [1, 1, 1, 1] && s6Buffer [4, -3, -3, 8]
-- `crossBlockInput` of `RMQ.Validation.PackedQueryRuntime`, restated literally
def stageGuard34 : Bool := s6Buffer [9, 7, 8, 6, 5, 2, 8, 7, 6, 2, 4, 9]

/-! ## Stage S7 (arrays, metadata bank, metadata words, dense words, tail)

Exact-type restatements of the S7 exit theorems (`Spec/Metadata.lean`,
`Proof/{MetaBounds,MetaSteps,MetaChain,Output,Tail}.lean`, the strengthened
frame `bufferStage_kept` of `Proof/Buffer.lean`) and a harness fixture: the
header, the constants, the geometry prelude, `arraysBlock`, the buffer phase and
`outputBlock`, then `halt 3`, run by the array-backed interpreter; the cells from
the halt value to the extent must be `buildMemory xs`. -/

section S7Output

open RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedConstruction.Spec RMQ.GenericSelect
open RMQ.SuccinctFinal.PackedCellProbe
open RMQ.SuccinctFinal.PackedWordRAM hiding State Registers Transition Memory Status Run run Instruction execute

theorem spec_metaChain_spec : ∀ {W n lc c : Nat} (_ : 32 ≤ W)
    (_ : 32 * (400000 * (n + 1)) < 2 ^ W) (_ : mv_pay n lc c + 2 ≤ 400000 * (n + 1)),
    ∀ k, k ≤ 108 → ∀ s : State, s.status = .running → MetaBase n lc c s.regs →
    ∃ s' j, SafeEval W (metaChain k) s s' j ∧ j ≤ 6 * k ∧ s'.status = .running ∧
      MetaBase n lc c s'.regs ∧ MetaUpTo n lc c k s'.regs ∧
      (∀ x : Nat, ¬ (229 ≤ x ∧ x < 229 + k) → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs :=
  @metaChain_spec

theorem spec_MetaBase_def : ∀ (n lc c : Nat) (r : Registers), MetaBase n lc c r ↔
    (GeoBase n r ∧ GeoUpTo n 39 r ∧ r 177 = lc ∧ r 178 = c ∧ r 0 = 0) := fun _ _ _ _ => Iff.rfl

theorem spec_MetaUpTo_def : ∀ (n lc c k : Nat) (r : Registers), MetaUpTo n lc c k r ↔
    (∀ i, i < k → r (229 + i) = metaVal n lc c i) := fun _ _ _ _ _ => Iff.rfl

theorem outputBlock_def : outputBlock = .seq (metaChain 108) (.seq metaEmitBlock repackBlock) := rfl

theorem repackBlock_def : repackBlock = forSlots 337 338 277 repackWordBlock := rfl

theorem metaEmitBlock_def :
    metaEmitBlock = .seq (acts [.reserve 3, .store 3 1]) (emitRegs metaWordRegs) := rfl

theorem spec_SafeEval_regs_fit : ∀ {W : Nat} (_ : 32 ≤ W) {b : Block} {s s' : State} {k : Nat} (_ : SafeEval W b s s' k) (_ : ∀ r, s.regs r < 2 ^ W),
    ∀ r, s'.regs r < 2 ^ W :=
  @SafeEval.regs_fit

theorem spec_emitRegs_spec : ∀ {W : Nat} (_ : 32 ≤ W),
    ∀ (rs : List Operand) (s : State),
    s.status = .running → (∀ r ∈ rs, (r : Nat) ≠ 10) → (∀ r, s.regs r < 2 ^ W) →
    s.extent + rs.length < 2 ^ W →
    ∃ s', SafeEval W (emitRegs rs) s s' (2 * rs.length) ∧ s'.status = .running ∧
      Emits s s' (rs.map (fun r : Operand => s.regs r)) ∧ (∀ r : Nat, r ≠ 10 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @emitRegs_spec

theorem spec_metaHead_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running) (_ : ∀ r, s.regs r < 2 ^ W) (_ : s.extent + 1 < 2 ^ W),
    ∃ s', SafeEval W (acts [.reserve rOUT, .store rOUT 1]) s s' 2 ∧ s'.status = .running ∧
      Emits s s' [s.regs 1] ∧ s'.regs 3 = s.extent ∧
      (∀ r : Nat, r ≠ 3 → s'.regs r = s.regs r) ∧ s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @metaHead_spec

theorem spec_metaEmit_spec : ∀ {W n lc c : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running) (_ : ∀ r, s.regs r < 2 ^ W) (_ : s.extent + 174 < 2 ^ W) (_ : GeoBase n s.regs) (_ : GeoUpTo n 39 s.regs) (_ : s.regs 177 = lc) (_ : s.regs 0 = 0) (_ : MetaUpTo n lc c 108 s.regs),
    ∃ s', SafeEval W metaEmitBlock s s' 348 ∧ s'.status = .running ∧
      Emits s s' (metaWords n lc c) ∧ s'.regs 3 = s.extent ∧
      (∀ r : Nat, r ≠ 3 → r ≠ 10 → s'.regs r = s.regs r) ∧ s'.keyRegs = s.keyRegs ∧
      s'.keys = s.keys :=
  @metaEmit_spec

theorem spec_cellsLE_lt : ∀ (f : Nat → Nat),
    ∀ (lo len : Nat), (∀ i, i < len → f (lo + i) ≤ 1) →
    cellsLE f lo len < 2 ^ len :=
  @cellsLE_lt

theorem spec_cellsLE_eq_bitsToNatLE :
    ∀ (l : List Bool) (lo len : Nat), lo + len ≤ l.length →
    cellsLE (fun j => (l.map SuccinctSpace.bitToNat).getD j 0) lo len =
      SuccinctSpace.bitsToNatLE ((l.drop lo).take len) :=
  @cellsLE_eq_bitsToNatLE

theorem spec_hornerStep_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running) (_ : u.regs 2 = 1) (j a acc x : Nat) (_ : u.regs 341 = j + 1) (_ : u.regs 339 = a + 1) (_ : u.regs 340 = acc) (_ : a < u.extent) (_ : u.memory a = some x) (_ : x ≤ 1) (_ : acc + acc + x < 2 ^ W) (_ : j < 2 ^ W) (_ : u.extent < 2 ^ W),
    ∃ u', SafeEval W hornerStepBlock u u' 5 ∧ u'.status = .running ∧
      u'.regs 339 = a ∧ u'.regs 340 = acc + acc + x ∧ u'.regs 341 = j ∧
      (∀ r : Nat, ¬ (339 ≤ r ∧ r ≤ 342) → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧
      u'.keyRegs = u.keyRegs :=
  @hornerStep_spec

theorem spec_hornerLoop_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running) (_ : u.regs 2 = 1) (g : Nat → Nat) (base lo L : Nat) (_ : u.regs 341 = L) (_ : u.regs 339 = base + lo + L) (_ : u.regs 340 = 0) (_ : L ≤ W) (_ : ∀ i, i < L → u.memory (base + lo + i) = some (g (lo + i))) (_ : ∀ i, i < L → g (lo + i) ≤ 1) (_ : base + lo + L ≤ u.extent) (_ : u.extent < 2 ^ W),
    ∃ u' k, SafeEval W (.loop rRJ hornerStepBlock) u u' k ∧ k ≤ L * 7 + 1 ∧
      u'.status = .running ∧ u'.regs 340 = cellsLE g lo L ∧
      (∀ r : Nat, ¬ (339 ≤ r ∧ r ≤ 342) → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧
      u'.keyRegs = u.keyRegs :=
  @hornerLoop_spec

theorem spec_repackWord_spec : ∀ {W : Nat} (_ : 32 ≤ W) (u : State) (_ : u.status = .running) (_ : u.regs 2 = 1) (g : Nat → Nat) (buf W0 i : Nat) (_ : u.regs 337 = i) (_ : u.regs 76 = W0) (_ : u.regs 220 = buf) (_ : 1 ≤ W0) (_ : W0 ≤ W) (_ : ∀ j, j < W0 → u.memory (buf + i * W0 + j) = some (g (i * W0 + j))) (_ : ∀ j, j < W0 → g (i * W0 + j) ≤ 1) (_ : buf + (i + 1) * W0 ≤ u.extent) (_ : u.extent + 1 < 2 ^ W),
    ∃ u' k, SafeEval W repackWordBlock u u' k ∧ k ≤ 7 * W0 + 8 ∧ u'.status = .running ∧
      Emits u u' [cellsLE g (i * W0) W0] ∧
      (∀ r : Nat, r ≠ 10 → ¬ (339 ≤ r ∧ r ≤ 342) → u'.regs r = u.regs r) ∧
      u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs :=
  @repackWord_spec

theorem spec_repack_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running) (_ : s.regs 2 = 1) (g : Nat → Nat) (buf W0 N : Nat) (_ : s.regs 220 = buf) (_ : s.regs 76 = W0) (_ : s.regs 277 = N) (_ : 1 ≤ W0) (_ : W0 ≤ W) (_ : ∀ j, j < N * W0 → s.memory (buf + j) = some (g j)) (_ : ∀ j, j < N * W0 → g j ≤ 1) (_ : buf + N * W0 ≤ s.extent) (_ : s.extent + N + 1 < 2 ^ W),
    ∃ s' k, SafeEval W repackBlock s s' k ∧ k ≤ N * (7 * W0 + 12) + 3 ∧ s'.status = .running ∧
      Emits s s' (hornerWords g W0 N) ∧
      (∀ r : Nat, r ≠ 10 → ¬ (337 ≤ r ∧ r ≤ 342) → s'.regs r = s.regs r) ∧
      s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs :=
  @repack_spec

theorem spec_dcount_eq_denseCount : ∀ (shape : CartesianShape),
    mv_dcount shape.size (PackedCellProbe.longCount shape)
        (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
          (GenericSelect.localSlotCount shape.bpCode false)) =
      PackedWordRAM.denseCount (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerPaddedBits shape) :=
  @dcount_eq_denseCount

theorem spec_outputWords_eq_buildMemory : ∀ (xs : List Int),
    metaWords xs.length (PackedCellProbe.longCount (shape xs))
        (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
          (GenericSelect.localSlotCount (shape xs).bpCode false)) ++
      hornerWords (fun j => ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map SuccinctSpace.bitToNat).getD j 0)
        (PackedWordRAM.wordWidth xs.length)
        (mv_dcount xs.length (PackedCellProbe.longCount (shape xs))
          (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
            (GenericSelect.localSlotCount (shape xs).bpCode false))) =
      PackedWordRAM.buildMemory xs :=
  @outputWords_eq_buildMemory

theorem spec_outputStage_spec : ∀ {W n lc c : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running) (_ : ∀ r, s.regs r < 2 ^ W) (_ : GeoBase n s.regs) (_ : GeoUpTo n 39 s.regs) (_ : s.regs 177 = lc) (_ : s.regs 178 = c) (_ : s.regs 0 = 0) (g : Nat → Nat) (buf : Nat) (_ : s.regs 220 = buf) (_ : ∀ j, j < mv_dcount n lc c * PackedWordRAM.wordWidth n → s.memory (buf + j) = some (g j)) (_ : ∀ j, j < mv_dcount n lc c * PackedWordRAM.wordWidth n → g j ≤ 1) (_ : buf + mv_dcount n lc c * PackedWordRAM.wordWidth n ≤ s.extent) (_ : mv_pay n lc c + 2 ≤ 400000 * (n + 1)) (_ : s.extent + 32 * (400000 * (n + 1)) < 2 ^ W) (_ : PackedWordRAM.wordWidth n ≤ W),
    ∃ s' k, SafeEval W outputBlock s s' k ∧
      k ≤ 1000 + mv_dcount n lc c * (7 * PackedWordRAM.wordWidth n + 12) ∧
      s'.status = .running ∧ s'.regs 3 = s.extent ∧
      Emits s s' (metaWords n lc c ++ hornerWords g (PackedWordRAM.wordWidth n) (mv_dcount n lc c)) ∧
      s'.keys = s.keys :=
  @outputStage_spec

theorem spec_arraysBlock_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running) (_ : s.regs 0 = 0) (_ : s.regs 2 = 1) (N1 N2 N3 N4 NB OW GLC MS : Nat) (_ : s.regs 1 = N1) (_ : s.regs 53 = N2) (_ : s.regs 45 = N3) (_ : s.regs 46 = N4) (_ : s.regs 32 = NB) (_ : s.regs 58 = OW) (_ : s.regs 59 = GLC) (_ : s.regs 33 = MS) (_ : s.extent + (N1 + 1) + (N2 + 1) + 2 * (N3 + 1) + 2 * (N4 + 1) + 4 * (NB + 1) +
      (OW * NB + 1) + (GLC * MS + 1) + OW * NB + GLC * MS + 1 < 2 ^ W),
    ∃ s' k, SafeEval W arraysBlock s s' k ∧
      k ≤ 5 * ((N1 + 1) + (N2 + 1) + 2 * (N3 + 1) + 2 * (N4 + 1) + 4 * (NB + 1) +
        (OW * NB + 1) + (GLC * MS + 1)) + 2 ∧ s'.status = .running ∧
      Emits s s' (List.replicate ((N1 + 1) + (N2 + 1) + 2 * (N3 + 1) + 2 * (N4 + 1) + 4 * (NB + 1) +
        (OW * NB + 1) + (GLC * MS + 1)) 0) ∧
      s'.regs 159 = s.extent ∧ s'.regs 160 = s'.regs 159 + (N1 + 1) ∧
      s'.regs 161 = s'.regs 160 + (N2 + 1) ∧ s'.regs 162 = s'.regs 161 + (N3 + 1) ∧
      s'.regs 163 = s'.regs 162 + (N3 + 1) ∧ s'.regs 164 = s'.regs 163 + (N4 + 1) ∧
      s'.regs 115 = s'.regs 164 + (N4 + 1) ∧ s'.regs 116 = s'.regs 115 + (NB + 1) ∧
      s'.regs 117 = s'.regs 116 + (NB + 1) ∧ s'.regs 118 = s'.regs 117 + (NB + 1) ∧
      s'.regs 135 = s'.regs 118 + (NB + 1) ∧ s'.regs 136 = s'.regs 135 + (OW * NB + 1) ∧
      s'.extent = s'.regs 136 + (GLC * MS + 1) ∧
      (∀ r : Nat, ¬ ArraysWritten r → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys :=
  @arraysBlock_spec

theorem spec_bufferStage_kept : ∀ {W : Nat} (_ : 32 ≤ W) (xs : List Int) (Inp : State → Prop) (leaf : Block) (_ : KeySpec W xs Inp leaf) (s : State) (_ : s.status = .running) (_ : s.regs 0 = 0) (_ : GeoBase xs.length s.regs) (_ : GeoUpTo xs.length 39 s.regs) (_ : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W) (_ : Inp s) (_ : InpBelow Inp s.extent) (P0 R0 L0 C0 F0 G0 A0 A1 A2 A3 Bm Gb : Nat) (_ : s.regs 159 = P0) (_ : s.regs 160 = R0) (_ : s.regs 161 = L0) (_ : s.regs 162 = C0) (_ : s.regs 163 = F0) (_ : s.regs 164 = G0) (_ : s.regs 115 = A0) (_ : s.regs 116 = A1) (_ : s.regs 117 = A2) (_ : s.regs 118 = A3) (_ : s.regs 135 = Bm) (_ : s.regs 136 = Gb) (_ : P0 + xs.length + 1 ≤ R0) (_ : R0 + (shape xs).bpCode.length / wordBits (shape xs).bpCode.length + 1 ≤ L0) (_ : L0 + superSlotCount (shape xs).bpCode false ≤ C0) (_ : C0 + superSlotCount (shape xs).bpCode false + 1 ≤ F0) (_ : F0 + localSlotCount (shape xs).bpCode false ≤ G0) (_ : G0 + localSlotCount (shape xs).bpCode false + 1 ≤ s.extent) (_ : A0 + geoBlocks xs.length + 1 ≤ A1) (_ : A1 + geoBlocks xs.length ≤ A2) (_ : A2 + geoBlocks xs.length ≤ A3) (_ : A3 + geoBlocks xs.length ≤ Bm) (_ : Bm + SuccinctRank.machineWordBits (geoMacro xs.length) * geoBlocks xs.length ≤ Gb) (_ : Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ s.extent) (_ : s.extent + 32 * (400000 * (xs.length + 1)) < 2 ^ W),
    ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock leaf) bufferBlock)) s s' k ∧
      k ≤ 2000 * (400000 * (xs.length + 1)) ∧ s'.status = .running ∧
      s'.regs 220 = s.extent + 3 * (xs.length + 1) ∧
      ArrayAt s' (s.extent + 3 * (xs.length + 1))
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length
        (fun i => ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).getD i 0) ∧
      s'.extent ≤ s.extent + 3 * (xs.length + 1) +
        ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map bitToNat).length + 1 ∧
      (∀ a, a < s.extent → (a < P0 ∨ G0 + localSlotCount (shape xs).bpCode false + 1 ≤ a) →
        (a < A0 ∨ Gb + SuccinctRank.machineWordBits (geoMacros xs.length) * geoMacros xs.length ≤ a) →
        s'.memory a = s.memory a) ∧
      s'.regs 177 = PackedCellProbe.longCount (shape xs) ∧
      s'.regs 178 = RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits (shape xs).bpCode false)
        (localSlotCount (shape xs).bpCode false) ∧
      (∀ r, BufferKept r → s'.regs r = s.regs r) ∧ s'.keys = s.keys :=
  @bufferStage_kept

theorem spec_pay_le_of_shape : ∀ (xs : List Int),
    mv_pay xs.length (longCount (shape xs))
        (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
          (GenericSelect.localSlotCount (shape xs).bpCode false)) + 2 ≤
      400000 * (xs.length + 1) :=
  @pay_le_of_shape

theorem spec_arrays_le_of_pay : ∀ (n lc c : Nat) (_ : mv_pay n lc c + 2 ≤ 400000 * (n + 1)),
    packedLocalSlots n ≤ mv_pay n lc c ∧
      (packedInteriorLayout n).offsetWidth * (packedInteriorLayout n).blockCount ≤ mv_pay n lc c ∧
      (packedInteriorLayout n).globalLevelCount * (packedInteriorLayout n).macroSampleCount ≤
        mv_pay n lc c ∧
      packedRankBlockSlots n ≤ 2 * n + 1 ∧ packedSuperSlots n ≤ n :=
  @arrays_le_of_pay

theorem spec_tailStage_spec : ∀ {W : Nat} (_ : 32 ≤ W) (xs : List Int) (Inp : State → Prop) (leaf : Block) (_ : KeySpec W xs Inp leaf) (s : State) (_ : s.status = .running) (_ : ∀ r, s.regs r < 2 ^ W) (_ : s.regs 0 = 0) (_ : GeoBase xs.length s.regs) (_ : GeoUpTo xs.length 39 s.regs) (_ : Inp s) (_ : InpBelow Inp s.extent) (_ : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W) (_ : s.extent + 64 * (400000 * (xs.length + 1)) < 2 ^ W) (_ : wordWidth xs.length ≤ W),
    ∃ s' k, SafeEval W (.seq arraysBlock (.seq (.seq stackArraysBlock (.seq (stackPassBlock leaf)
        bufferBlock)) outputBlock)) s s' k ∧
      k ≤ 2100 * (400000 * (xs.length + 1)) ∧ s'.status = .running ∧
      s.extent ≤ s'.regs 3 ∧ s'.regs 3 ≤ s.extent + 8 * (400000 * (xs.length + 1)) ∧
      s'.extent = s'.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        s'.memory (s'.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧ s'.keys = s.keys :=
  @tailStage_spec

theorem spec_metaVal_le : ∀ (n lc c : Nat), mv_pay n lc c + 2 ≤ 400000 * (n + 1) →
    ∀ i, i < 108 → metaVal n lc c i ≤ 3 * (400000 * (n + 1)) :=
  @metaVal_le

theorem spec_metaWords_eq : ∀ (n lc c : Nat),
    metaWords n lc c = metadataOf n lc (c * GenericSelect.localStride (2 * n)) :=
  @metaWords_eq

theorem spec_pay_eq : ∀ (n lc c : Nat),
    packedReviewerPayloadLength n lc (c * GenericSelect.localStride (2 * n)) = mv_pay n lc c :=
  @pay_eq

theorem spec_cellCount_eq : ∀ (n lc c : Nat),
    packedReviewerCellCount n lc (c * GenericSelect.localStride (2 * n)) = mv_oldCount n lc c :=
  @cellCount_eq

end S7Output

def s7HarnessProgram : Array BInstr :=
  ((Block.seq (.action (.load 1 0)) (.seq constantsBlock (.seq geometryPrelude (.seq arraysBlock
    (.seq (.seq stackArraysBlock (.seq (stackPassBlock keyLeaf) bufferBlock)) outputBlock))))).compileAt 0 ++
    [(⟨.halt 3⟩ : BInstr)]).toArray

def s7Output (xs : List Int) : Bool :=
  let r := runArray s7HarnessProgram 1000000000 (ExecState.ofComparisonInput 350 xs)
  match r.final.status with
  | .halted b =>
      (List.range (r.final.memory.size - b)).map (fun k => (r.final.memory.getD (b + k) none).getD 0) ==
        SuccinctFinal.PackedWordRAM.buildMemory xs
  | _ => false

def stageGuard35 : Bool := s7Output [] && s7Output [4, -3, -3, 8]

/-! ## Stage S7 completion: the program constants, their runs and exactness

Exact-type restatements of `Proof/Constants.lean` (the affine reading of the
amended fuel body, V3-6a) and `Proof/Exact.lean` (capacity at the word width, the
whole source, the run, fuel sufficiency and both V3-6 equality theorems), and a
fixture on the production constants themselves: `builderProgram` and
`builderProgramWord` run by the array-backed interpreter at fuel `builderBudget n`;
the cells from the halt value to the extent must be `buildMemory xs`. -/

section S7Constants

open RMQ.SuccinctFinal RMQ.SuccinctFinal.PackedConstruction.Spec
open RMQ.SuccinctFinal.PackedCellProbe
open RMQ.SuccinctFinal.PackedWordRAM hiding State Registers Transition Memory Status Run run Instruction execute

theorem spec_builderBudget_eq_mul_add :
    ∀ n : Nat, builderBudget n = 1000000000 * n + 1000000000 :=
  @builderBudget_eq_mul_add

theorem spec_fringeOverhead_ge_two : ∀ (n : Nat),
    2 ≤ bpFringeTableOverhead n :=
  @fringeOverhead_ge_two

theorem spec_two_n_four_lt_cellPow : ∀ (n : Nat),
    2 * n + 4 < 2 ^ packedReviewerCellWidth n :=
  @two_n_four_lt_cellPow

theorem spec_bankcap_wordWidth : ∀ (n : Nat),
    2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ wordWidth n :=
  @bankcap_wordWidth

theorem spec_cap_wordWidth : ∀ (n : Nat),
    n + 1 + 64 * (400000 * (n + 1)) < 2 ^ wordWidth n :=
  @cap_wordWidth

theorem spec_header_spec : ∀ {W : Nat} (_ : 32 ≤ W) (s : State) (_ : s.status = .running) (_ : s.regs 0 = 0) (_ : 0 < s.extent) {n : Nat} (_ : s.memory 0 = some n) (_ : n < 2 ^ W),
    ∃ s', SafeEval W (.action (.load 1 0)) s s' 1 ∧ s'.status = .running ∧
      s'.regs = put s.regs 1 n ∧ s'.memory = s.memory ∧ s'.extent = s.extent ∧
      s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs :=
  @header_spec

theorem spec_builderSource_spec : ∀ {W : Nat} (_ : 32 ≤ W) (xs : List Int) (Inp : State → Prop) (leaf : Block) (_ : KeySpec W xs Inp leaf) (s : State) (_ : s.status = .running) (_ : ∀ r, s.regs r = 0) (_ : 0 < s.extent) (_ : s.memory 0 = some xs.length) (_ : Inp s) (_ : InpBelow Inp s.extent) (_ : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W) (_ : s.extent + 64 * (400000 * (xs.length + 1)) < 2 ^ W) (_ : wordWidth xs.length ≤ W),
    ∃ s' k, SafeEval W (builderSource leaf) s s' k ∧
      k ≤ 3 + (25 * W + 40 + 39 * (5 * W + 20)) + 2100 * (400000 * (xs.length + 1)) ∧
      s'.status = .running ∧ s.extent ≤ s'.regs 3 ∧
      s'.regs 3 ≤ s.extent + 8 * (400000 * (xs.length + 1)) ∧
      s'.extent = s'.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        s'.memory (s'.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < s.extent → s'.memory a = s.memory a) ∧ s'.keys = s.keys :=
  @builderSource_spec

theorem spec_builderRun_spec : ∀ {W : Nat} (_ : 32 ≤ W) (xs : List Int) (Inp : State → Prop) (leaf : Block) (_ : KeySpec W xs Inp leaf) (_ : (builderSource leaf).size < 2 ^ 32) (s : State) (_ : s.pc = 0) (_ : s.status = .running) (_ : ∀ r, s.regs r = 0) (_ : 0 < s.extent) (_ : s.memory 0 = some xs.length) (_ : Inp s) (_ : InpBelow Inp s.extent) (_ : 2 ^ 32 * (2 * xs.length + 4) ^ 8 < 2 ^ W) (_ : s.extent + 64 * (400000 * (xs.length + 1)) < 2 ^ W) (_ : wordWidth xs.length ≤ W),
    ∃ sF ts, RunsTo ((builderSource leaf).compileAt 0 ++ [⟨.halt 3⟩]) s sF ts ∧
      ts.length ≤ 4 + (25 * W + 40 + 39 * (5 * W + 20)) + 2100 * (400000 * (xs.length + 1)) ∧
      sF.status = .halted (sF.regs 3) ∧ s.extent ≤ sF.regs 3 ∧
      sF.regs 3 ≤ s.extent + 8 * (400000 * (xs.length + 1)) ∧
      sF.extent = sF.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        sF.memory (sF.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < s.extent → sF.memory a = s.memory a) ∧ sF.keys = s.keys :=
  @builderRun_spec

theorem spec_emitted_eq_of_stored : ∀ (s : State) (base : Nat) (l : List Nat) (_ : ∀ i, i < l.length → s.memory (base + i) = some (l.getD i 0)),
    emitted s base l.length = l :=
  @emitted_eq_of_stored

theorem spec_run_of_halting : ∀ (prog : List BInstr) (fuel : Nat) (s sF : State) (ts : List Transition) (_ : RunsTo prog s sF ts) (_ : ts.length ≤ fuel) (_ : sF.status ≠ .running),
    run prog fuel s = ⟨sF, ts⟩ :=
  @run_of_halting

theorem spec_wordWidth_ge_32 : ∀ (n : Nat),
    32 ≤ wordWidth n :=
  @wordWidth_ge_32

theorem spec_budget_ge : ∀ (n : Nat),
    4 + (25 * wordWidth n + 40 + 39 * (5 * wordWidth n + 20)) + 2100 * (400000 * (n + 1)) ≤
      builderBudget n :=
  @budget_ge

theorem spec_builder_run_comparison : ∀ (xs : List Int),
    ∃ sF ts, run builderProgram (builderBudget xs.length) (comparisonInputState xs) = ⟨sF, ts⟩ ∧
      RunsTo builderProgram (comparisonInputState xs) sF ts ∧
      ts.length ≤ 4 + (25 * wordWidth xs.length + 40 + 39 * (5 * wordWidth xs.length + 20)) +
        2100 * (400000 * (xs.length + 1)) ∧
      sF.status = .halted (sF.regs 3) ∧ 1 ≤ sF.regs 3 ∧
      sF.regs 3 ≤ 1 + 8 * (400000 * (xs.length + 1)) ∧
      sF.extent = sF.regs 3 + (buildMemory xs).length ∧
      (∀ i, i < (buildMemory xs).length →
        sF.memory (sF.regs 3 + i) = some ((buildMemory xs).getD i 0)) ∧
      (∀ a, a < 1 → sF.memory a = (comparisonInputState xs).memory a) ∧
      sF.keys = (comparisonInputState xs).keys :=
  @builder_run_comparison

theorem spec_efficientBuild_eq_buildMemory :
    ∀ xs : List Int, efficientBuild xs = buildMemory xs :=
  @efficientBuild_eq_buildMemory

theorem spec_efficientBuildWord_eq_buildMemory :
    ∀ xs : List Int, InputFits (wordWidth xs.length) xs →
    efficientBuildWord (wordWidth xs.length) xs = buildMemory xs :=
  @efficientBuildWord_eq_buildMemory

end S7Constants

def s7Production (xs : List Int) : Bool :=
  let r := runArray builderProgram.toArray (builderBudget xs.length) (ExecState.ofComparisonInput 350 xs)
  match r.final.status with
  | .halted b =>
      (List.range (r.final.memory.size - b)).map (fun k => (r.final.memory.getD (b + k) none).getD 0) ==
        SuccinctFinal.PackedWordRAM.buildMemory xs
  | _ => false

def s7ProductionWord (xs : List Int) : Bool :=
  let r := runArray builderProgramWord.toArray (builderBudget xs.length)
    (ExecState.ofWordInput 350 (SuccinctFinal.PackedWordRAM.wordWidth xs.length) xs)
  match r.final.status with
  | .halted b =>
      (List.range (r.final.memory.size - b)).map (fun k => (r.final.memory.getD (b + k) none).getD 0) ==
        SuccinctFinal.PackedWordRAM.buildMemory xs
  | _ => false

def stageGuard36 : Bool :=
  s7Production [] && s7Production [4, -3, -3, 8] && s7ProductionWord [] && s7ProductionWord [4, -3, -3, 8]



/-! ## Axiom inventory (every new S2 declaration) -/

#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rZERO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rN
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rONE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rOUT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLEAF_I
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLEAF_J
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLEAF_RES
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLEAF_T1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLEAF_T2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rTWO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCUR
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBIT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rECNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rEVAL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSLOT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rENT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLX
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLM
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBASE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMACRO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBLOCKS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMACROS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLDOM
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rGDOM
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLWID
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rGWID
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.acts
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.emitBit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.emitBitsBody
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.emitBits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.emitTableBody
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.emitTable
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.log2Body
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.log2Block
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.constantsBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.levelWidthBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.interiorGeometryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.levelEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.levelTableBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_21
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_22
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_23
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_24
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_25
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_26
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_27
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_28
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_29
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_30
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_31
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_33
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_34
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_35
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_36
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_37
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_38
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_39
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_40
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.put_same
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.put_ne
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_constant
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_move
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_arithmetic
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_comparison
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_reserve
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_store
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_load
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.execActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ActsOK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.acts_evalG
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.execActs_running
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.execActs_append
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EvalG.regs_frame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EvalG.keys_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.refl
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.trans
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.memory_below
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.memory_at
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_move
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_constant
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_comparison
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_reserve
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_store
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_add
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_sub
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_mul
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_div
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_mod
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_shl
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.two_le_two_pow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitBit_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.natToBitsLE_succ_right
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bitToNat_decide_mod_two
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitBitsBody_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitBits_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.TableScratch
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flatten_bits_length
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flatten_range_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.of_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitTable_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.div_pow_ge_two_of_log2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.div_pow_log2_lt_two
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2Block_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_lt_width
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_mono
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.LevelEntryWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.levelEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.levelTable_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.constantsBlock_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.levelWidthBlock_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_succ_le_self
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.level_cap_of_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoBase
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoMacro
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoBlocks
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoMacros
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.interiorGeometry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoMacro_layout
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoMacros_layout
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoBase_layout
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoBlocks_layout
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.level_domain_facts
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localLevelTable_emits_payload
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.globalLevelTable_emits_payload
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RegSpec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RegSpec.seq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RegSpec.weaken
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pureReg
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pureOK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pureRegs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pureOKs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pure_exec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pure_safe
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pure_acts_exec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RegSpec.pure
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RegSpec.log2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_41
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_42
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_43
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_44
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_45
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_46
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_47
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_48
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_49
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_50
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_51
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_52
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_53
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_54
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_55
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_56
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_57
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_58
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_59
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_60
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_61
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_62
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_63
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_64
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_65
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_66
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_67
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_68
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_69
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_70
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_71
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_72
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_73
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_74
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_75
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_76
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_77
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_78
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_79
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_80
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_81
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_82
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_83
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_84
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_85
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_86
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_87
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_88
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_89
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_90
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_91
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_92
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_93
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_94
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_95
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_96
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_97
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_98
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_99
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_100
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_101
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_102
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_103
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_104
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_105
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_106
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_107
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_108
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_109
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_110
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_111
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_112
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_113
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_114
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_115
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_116
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_117
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_118
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_119
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_120
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_121
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_122
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_123
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_124
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_125
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_126
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_127
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_128
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_129
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_130
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_131
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_132
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_133
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_134
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_135
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_136
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_137
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_138
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_139
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_140
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_141
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_142
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_143
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_144
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_145
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_146
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_147
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_148
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_149
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_150
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_151
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_152
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_153
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_154
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_155
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_156
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_157
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_158
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_159
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_160
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_161
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_162
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_163
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_164
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_165
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_166
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_167
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_168
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_169
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_170
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_171
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_172
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_173
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_174
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_175
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_176
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_177
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_178
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_179
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_180
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_181
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_182
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_183
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_184
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_185
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_186
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_187
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_188
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_189
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_190
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_191
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_192
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_193
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_194
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_195
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_196
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_197
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_198
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_199
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_513
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_561
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_1180
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.forSlots_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.reserveArray_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ArrayAt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.arrayAt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_succ_lt_pow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RegSpec.wordBits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pureDst
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pureReg_frame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pureRegs_frame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoVal
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.GeoBase
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.GeoUpTo
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.GeoStepOK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.GeoStepOK.of_regSpec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordBits_cost_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordBitsF_frame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cap_of_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.powB_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.mulB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_succ_le_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.powB_facts
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordBitsF
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2F
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordBits_cost_le5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.scratch_of_all
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep_pure
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep_wordBits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep_pure_wordBits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep_wordBits_pure
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep_log2_pure
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_ws
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_S
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_e
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_ls
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_lps
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_LS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_sup
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_loc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_sp
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_mul_self_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_succ_le_of_pos
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_base
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_macro
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_blocks
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_macros
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_ow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_wb_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wb_pos
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_levelWidth
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_c
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_pow_c
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.c_lt_width
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.shiftLeft_one
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.mulC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.eight_w_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ao_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_q
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_AO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_I
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_F
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bnd_C
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.capB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep21
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep22
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep23
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep24
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep25
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep26
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep27
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep28
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep29
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep30
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep31
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep33
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep34
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep35
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep36
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cellArg_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep37
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep38
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoStep_all
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geoChain_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.interior_cap_of_bank
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.geometryPrelude_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rM2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rWS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rEL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLSTR
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLPS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLSPAN
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSUP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLOC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRBW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLFW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSFW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRSUP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRBLK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLFR
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSFR
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBS2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSSC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rOW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rGLC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBAW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLSCNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rGSCNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFROWS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFWID
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSROWS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSWID
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rIBITS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFBITS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCBITS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rQ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rR
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rAO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rOLDW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rWW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.forSlots
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.reserveArray
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.wordBitsBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.minActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.geoStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.geoChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.geometryPrelude
#print axioms PRE1StageConsumer.spec_RegSpec_def
#print axioms PRE1StageConsumer.spec_RegSpec_pure
#print axioms PRE1StageConsumer.spec_RegSpec_log2
#print axioms PRE1StageConsumer.spec_forSlots
#print axioms PRE1StageConsumer.spec_reserveArray
#print axioms PRE1StageConsumer.spec_geoVal_pins
#print axioms PRE1StageConsumer.spec_GeoUpTo_def
#print axioms PRE1StageConsumer.spec_GeoBase_def
#print axioms PRE1StageConsumer.geometryPrelude_def
#print axioms PRE1StageConsumer.geoStepBlock_36_def
#print axioms PRE1StageConsumer.spec_geometryPrelude
#print axioms PRE1StageConsumer.spec_geoChain
#print axioms PRE1StageConsumer.geoSmoke
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.congr_right
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flatMap_range_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitFlatMap_spec
#print axioms PRE1StageConsumer.spec_emitFlatMap
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSTK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLDB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCNTB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSTKH
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rI
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rIGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLAST
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rPOP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rADDR
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rTOP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rWG
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rTMP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rJ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rJGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.stackArraysBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.popGuardBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.popBodyBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.linkBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.pushBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.stackStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.stackPassBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.bpUnitBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.bpEmitBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.keyLeaf
#print axioms RMQ.SuccinctFinal.PackedConstruction.wordLeaf
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.spineFrom
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.popsFor
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.values_length
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.spineFrom_insertRight
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.insertPoint_eq_find
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.spineFrom_mem
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.spineFrom_sorted
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.takeWhile_find_of_split
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.sum_append_nat
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.openCounts_sum
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.le_sum_of_mem
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.getD_of_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.getD_of_ge
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.openCounts_getD_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.getD_append_singleton
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.getD_modify_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.take_succ_getD
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.buildTree_take_size
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.StackCartesianTreeSpec.spine_entry_facts
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.forSlots_spec_pot
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EvalG.loop_measure_pot
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.KeySpec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.OracleInput
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.WordInput
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_loadKey
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.exec_compareKey
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.getD_eq_of_getElem?
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.keyLeaf_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordLeaf_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Region
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.store_region
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.load_region
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.safe_load_region
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.stackArrays_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.region_zero
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Region.mono
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.InpStable
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.popGuard_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.guardVal
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.popLoop_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.linkPushM
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.linkPush_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.InpBelow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.InpBelow.stable
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.spineAt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.countsAt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.StackInv
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.PassStart
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.spine_length_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.stackStep_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.stackPass_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.unitCells
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.unitCells_length
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flatMap_unitCells_length
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bpUnit_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sum_take_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sum_take_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flatMap_take_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bpEmit_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bitToNat_map_bpUnit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bpCells_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cartesianBP_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.oracleInput_below
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordInput_below
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cartesianBP_key
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cartesianBP_word
#print axioms PRE1StageConsumer.keyLeaf_def
#print axioms PRE1StageConsumer.wordLeaf_def
#print axioms PRE1StageConsumer.spec_KeySpec_def
#print axioms PRE1StageConsumer.spec_OracleInput_def
#print axioms PRE1StageConsumer.spec_WordInput_def
#print axioms PRE1StageConsumer.spec_keyLeaf
#print axioms PRE1StageConsumer.spec_wordLeaf
#print axioms PRE1StageConsumer.spec_spineFrom_insertRight
#print axioms PRE1StageConsumer.spec_insertPoint_eq_find
#print axioms PRE1StageConsumer.spec_spineFrom_sorted
#print axioms PRE1StageConsumer.spec_openCounts_sum
#print axioms PRE1StageConsumer.spec_cartesianBP_key
#print axioms PRE1StageConsumer.spec_cartesianBP_word
#print axioms PRE1StageConsumer.s3Program
#print axioms PRE1StageConsumer.s3Cells
#print axioms PRE1StageConsumer.s3Key
#print axioms PRE1StageConsumer.s3Word
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rESB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMINB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMAXB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rARGB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBPB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rEX
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBLK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rOFF
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rOGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMN
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMX
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBEST
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBESTE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rPOS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCELL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSPAN
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBS1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.maxActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.sampleBodyBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.blockBodyBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.blockStatsBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.baselineEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.relativeEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.argOffsetEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.summaryTablesBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.natListMinFrom_append_singleton
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.natListMax_append_singleton
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.samples_take
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.range_map_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.argStep
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.argAcc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.argAcc_shift
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.bpBlockArgMinPrefixPosFrom_eq_argAcc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.excess_step
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.argAcc_ge
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bpCell
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bpCell_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bpCell_excess
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sampleBody_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.SampleFrame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sampleLoop_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.addStoreState
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.addStore_exec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.addStore_seq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.addStore_pair
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.blockBody_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.StatsFrame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.put4_ne
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bpExcessAt_zero
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.blockStats_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.step_pure
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.step_load
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.baselineEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.relativeEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.argOffsetEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.BaselineWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RelativeWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.SummaryFrame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.summaryTables_spec
#print axioms PRE1StageConsumer.maxActs_def
#print axioms PRE1StageConsumer.blockStatsBlock_def
#print axioms PRE1StageConsumer.summaryTablesBlock_def
#print axioms PRE1StageConsumer.relativeEntryBlock_def
#print axioms PRE1StageConsumer.spec_argStep_def
#print axioms PRE1StageConsumer.spec_bpBlockArgMinPrefixPosFrom_eq_argAcc
#print axioms PRE1StageConsumer.spec_natListMinFrom_append_singleton
#print axioms PRE1StageConsumer.spec_natListMax_append_singleton
#print axioms PRE1StageConsumer.spec_argAcc_ge
#print axioms PRE1StageConsumer.spec_bpCell_def
#print axioms PRE1StageConsumer.spec_SampleFrame_def
#print axioms PRE1StageConsumer.spec_StatsFrame_def
#print axioms PRE1StageConsumer.spec_SummaryFrame_def
#print axioms PRE1StageConsumer.spec_Region_def
#print axioms PRE1StageConsumer.spec_sampleLoop
#print axioms PRE1StageConsumer.spec_blockBody
#print axioms PRE1StageConsumer.spec_blockStats
#print axioms PRE1StageConsumer.spec_baselineEntry
#print axioms PRE1StageConsumer.spec_relativeEntry
#print axioms PRE1StageConsumer.spec_argOffsetEntry
#print axioms PRE1StageConsumer.spec_summaryTables
#print axioms PRE1StageConsumer.spec_tableBits_def
#print axioms PRE1StageConsumer.s4ArraysHarness
#print axioms PRE1StageConsumer.s4Program
#print axioms PRE1StageConsumer.s4Summary
#print axioms PRE1StageConsumer.s4Input
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rAMB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rGMB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLVL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLVGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMBGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSPN
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCX
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCY
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rKX
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rKY
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rT7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLVCNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rROWP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rROWC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMST
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMM1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rJS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rJSGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rMI
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLV
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSTB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.betterActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.memoCellBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.memoLevelsBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.localMemoBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.macroScanBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.globalMemoBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.localEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.globalEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.interiorCloseBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.argAcc_excess_eq_min
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.argPos_excess_eq_min
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.better_eq_min
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.rangeArgMin_snoc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.globalMemo_double
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.localMemo_double
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ActsPrefix
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.acts_cons_safe
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ActsPrefix.cons
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ActsPrefix.append
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ActsPrefix.close
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.prefix_pure
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.prefix_load
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.prefix_store
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.covered_block
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.betterActs_prefix
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.memoCell_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.row_addr_ne
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.row_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.row_ge
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.memoLevels_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localMemo_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.macroScan_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.globalMemo_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.globalEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.LocalEntryWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.GlobalEntryWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localSparseTable_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.globalSparseTable_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.CloseFrame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.interiorCloseLayout_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.two_pow_mwb_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.mwb_lt_of_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.mul_lin
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.mul_lin2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.mwb_le_self
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.closeSegment_spec
#print axioms PRE1StageConsumer.betterActs_def
#print axioms PRE1StageConsumer.memoLevelsBlock_def
#print axioms PRE1StageConsumer.localMemoBlock_def
#print axioms PRE1StageConsumer.globalMemoBlock_def
#print axioms PRE1StageConsumer.interiorCloseBlock_def
#print axioms PRE1StageConsumer.spec_CloseFrame_def
#print axioms PRE1StageConsumer.spec_interiorPayload_eq_segments
#print axioms PRE1StageConsumer.spec_argPos_excess_eq_min
#print axioms PRE1StageConsumer.spec_better_eq_min
#print axioms PRE1StageConsumer.spec_rangeArgMin_snoc
#print axioms PRE1StageConsumer.spec_globalMemo_double
#print axioms PRE1StageConsumer.spec_memoCell
#print axioms PRE1StageConsumer.spec_memoLevels
#print axioms PRE1StageConsumer.spec_localMemo
#print axioms PRE1StageConsumer.spec_macroScan
#print axioms PRE1StageConsumer.spec_globalMemo
#print axioms PRE1StageConsumer.spec_localEntry
#print axioms PRE1StageConsumer.spec_globalEntry
#print axioms PRE1StageConsumer.spec_localSparseTable
#print axioms PRE1StageConsumer.spec_globalSparseTable
#print axioms PRE1StageConsumer.spec_interiorCloseLayout
#print axioms PRE1StageConsumer.spec_closeSegment
#print axioms PRE1StageConsumer.s4CloseProgram
#print axioms PRE1StageConsumer.s4Close
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rPOSB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRWB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLFB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLFCB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSFB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSFCB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rPGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rM2P1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rA1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rA2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rA3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rA4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rKGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rG
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rGGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLCNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSCNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBOCC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rEOCC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBPOS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rEPOS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSPANA
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFLAG
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSSL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSEND
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rLIVE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rA5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rA6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.posActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.monusActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.posStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.posPassBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.longFlagBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.longFlagsBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.sparseFlagBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.sparseFlagsBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rankSuperEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rankBlockEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.superOccEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.superWordEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.superFlagEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.superOffsetEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.localDecodeActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.localOccEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.localWordEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.localFlagEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.localOffsetEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.flagRankEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.zeroEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.flagEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.relativeOffsetEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.longRelativeBodyBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.sparseRelativeBodyBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.accessHalfBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.select_at_close
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.position_at_close
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.rankPrefix_false_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.bp_occurrenceCount
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.bp_rank_end
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.bp_position_size
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.position_min_size
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.posStep_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.posPass_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ActsPrefix.nil'
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.prefix_pureList
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.posActs_prefix
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.monusActs_prefix
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flagNat
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flagNat_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.longFlag_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rank_flags_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.longFlags_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localOffset_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sparseFlag_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sparseFlags_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EntryOK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.RelWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flagEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flagRankEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rankBlockEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.zeroEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.superOccEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.relOffsetEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.superPos_prefix
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.superWordEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.superOffsetEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localBase_bound
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localSlotsPerSuper_le_superStride
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localSlot_lt_cap
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flagNat_not_and
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localDecode_prefix
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.not_accessWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localEntry_baseOccurrence_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localEntry_baseWordIndex_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localEntry_rankBefore_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localEntry_firstOffset_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localOccEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localWordEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localFlagEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.localOffsetEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.relativeOffsetsOrZero_eq_positions
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flatten_map_flatMap
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.BodyWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.not_bodyWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.longRelativeBody_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sparseRelativeBody_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.entryBits_length
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flatMap_range_length_mono
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.relLoop_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.longRelative_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sparseRelative_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessFrame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady.mono
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady.step
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessFrame_of_table
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessFrame_of_body
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.machineWordBits_le_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.table_cost_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady.lenW'
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady.entry
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable_generic
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessWrites_frame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable1_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady.wsW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady.supS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rankBlock_mono
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable2_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable3_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessReady.posBounds
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable4_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable5_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable6_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sparseExceptionRelativeWidth_W
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable7_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable8_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable9_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable10_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flags_tableBits_one
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.flagTable_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.longFlagBits_length'
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable11_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable12_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable13_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.rank_flags_take
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sparseEff_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sparseEff_rank
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable15_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable16_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable17_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessRegs_of_bank
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.access_caps
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.AccessHalfFrame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessPasses_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable14_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessTable18_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessSegments_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.accessHalf_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.lc_eq_longCount
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.sc_eq_sparseCount
#print axioms PRE1StageConsumer.posActs_def
#print axioms PRE1StageConsumer.monusActs_def
#print axioms PRE1StageConsumer.posStepBlock_def
#print axioms PRE1StageConsumer.posPassBlock_def
#print axioms PRE1StageConsumer.longFlagBlock_def
#print axioms PRE1StageConsumer.longFlagsBlock_def
#print axioms PRE1StageConsumer.sparseFlagBlock_def
#print axioms PRE1StageConsumer.sparseFlagsBlock_def
#print axioms PRE1StageConsumer.rankSuperEntryBlock_def
#print axioms PRE1StageConsumer.rankBlockEntryBlock_def
#print axioms PRE1StageConsumer.superOccEntryBlock_def
#print axioms PRE1StageConsumer.superWordEntryBlock_def
#print axioms PRE1StageConsumer.superFlagEntryBlock_def
#print axioms PRE1StageConsumer.superOffsetEntryBlock_def
#print axioms PRE1StageConsumer.localDecodeActs_def
#print axioms PRE1StageConsumer.localOccEntryBlock_def
#print axioms PRE1StageConsumer.localWordEntryBlock_def
#print axioms PRE1StageConsumer.localFlagEntryBlock_def
#print axioms PRE1StageConsumer.localOffsetEntryBlock_def
#print axioms PRE1StageConsumer.flagRankEntryBlock_def
#print axioms PRE1StageConsumer.zeroEntryBlock_def
#print axioms PRE1StageConsumer.flagEntryBlock_def
#print axioms PRE1StageConsumer.relativeOffsetEntryBlock_def
#print axioms PRE1StageConsumer.longRelativeBodyBlock_def
#print axioms PRE1StageConsumer.sparseRelativeBodyBlock_def
#print axioms PRE1StageConsumer.accessHalfBlock_def
#print axioms PRE1StageConsumer.spec_AccessWrites_def
#print axioms PRE1StageConsumer.spec_RelWrites_def
#print axioms PRE1StageConsumer.spec_BodyWrites_def
#print axioms PRE1StageConsumer.spec_AccessFrame_def
#print axioms PRE1StageConsumer.spec_AccessHalfFrame_def
#print axioms PRE1StageConsumer.spec_flagNat_def
#print axioms PRE1StageConsumer.spec_liveAccessPayload_eq_segments
#print axioms PRE1StageConsumer.spec_select_at_close
#print axioms PRE1StageConsumer.spec_position_at_close
#print axioms PRE1StageConsumer.spec_rankPrefix_false_succ
#print axioms PRE1StageConsumer.spec_bp_occurrenceCount
#print axioms PRE1StageConsumer.spec_bp_rank_end
#print axioms PRE1StageConsumer.spec_bp_position_size
#print axioms PRE1StageConsumer.spec_position_min_size
#print axioms PRE1StageConsumer.spec_posStep_spec
#print axioms PRE1StageConsumer.spec_posPass_spec
#print axioms PRE1StageConsumer.spec_posActs_prefix
#print axioms PRE1StageConsumer.spec_monusActs_prefix
#print axioms PRE1StageConsumer.spec_longFlag_spec
#print axioms PRE1StageConsumer.spec_longFlags_spec
#print axioms PRE1StageConsumer.spec_sparseFlag_spec
#print axioms PRE1StageConsumer.spec_sparseFlags_spec
#print axioms PRE1StageConsumer.spec_flagEntry_spec
#print axioms PRE1StageConsumer.spec_flagRankEntry_spec
#print axioms PRE1StageConsumer.spec_rankBlockEntry_spec
#print axioms PRE1StageConsumer.spec_zeroEntry_spec
#print axioms PRE1StageConsumer.spec_superOccEntry_spec
#print axioms PRE1StageConsumer.spec_relOffsetEntry_spec
#print axioms PRE1StageConsumer.spec_superWordEntry_spec
#print axioms PRE1StageConsumer.spec_superOffsetEntry_spec
#print axioms PRE1StageConsumer.spec_localDecode_prefix
#print axioms PRE1StageConsumer.spec_localOccEntry_spec
#print axioms PRE1StageConsumer.spec_localWordEntry_spec
#print axioms PRE1StageConsumer.spec_localFlagEntry_spec
#print axioms PRE1StageConsumer.spec_localOffsetEntry_spec
#print axioms PRE1StageConsumer.spec_relativeOffsetsOrZero_eq_positions
#print axioms PRE1StageConsumer.spec_longRelativeBody_spec
#print axioms PRE1StageConsumer.spec_sparseRelativeBody_spec
#print axioms PRE1StageConsumer.spec_relLoop_spec
#print axioms PRE1StageConsumer.spec_longRelative_spec
#print axioms PRE1StageConsumer.spec_sparseRelative_spec
#print axioms PRE1StageConsumer.spec_accessTable_generic
#print axioms PRE1StageConsumer.spec_accessRegs_of_bank
#print axioms PRE1StageConsumer.spec_access_caps
#print axioms PRE1StageConsumer.spec_accessPasses_spec
#print axioms PRE1StageConsumer.spec_accessSegments_eq
#print axioms PRE1StageConsumer.spec_accessHalf_spec
#print axioms PRE1StageConsumer.spec_lc_eq_longCount
#print axioms PRE1StageConsumer.spec_sc_eq_sparseCount
#print axioms PRE1StageConsumer.s5ArraysHarness
#print axioms PRE1StageConsumer.s5Program
#print axioms PRE1StageConsumer.s5Access
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rCP1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSQ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFV
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFA
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFBP
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFBV
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rFTGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rF1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rF2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rF3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rF4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSX
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rSPOS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.fringeDecodeActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.fringeStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.fringeEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.selectDecodeActs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.selectStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.selectEntryBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.microtablesBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rBUF
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rHX
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rHI
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rHIGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rPROBE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rPAD
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rH1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rH2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rDB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.headerReserveBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.headerPatchStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.headerPatchBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.zerosBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.padBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.bufferBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.natToBitsLE_getElem?
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.pattern_getElem?
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.pattern_rank_true_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.pattern_rank_false_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.excessOffset_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.scanArgMin_snoc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.scanArgMin_zero
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.scanArgMin_one
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.selectPos_step
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.selectPos_final
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.fringeBest_step
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_200
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_201
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_202
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_203
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_204
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_205
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_206
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_207
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_208
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_209
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_210
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_211
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_212
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_213
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_214
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_215
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_216
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_217
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_218
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_219
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.MicroWrites
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.div_two_pow_succ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.selectStep_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.selectEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.selectTable_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.take_le_one
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.mul_le_of_le_one
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.fringeStep_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.fringeEntry_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.fringeTable_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.microtables_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_220
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_221
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_222
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_223
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_224
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_225
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_226
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_227
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_228
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.zeroLoop_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.zeros_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.headerReserve_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.headerPatch_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.prefix_reserve
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.denseBitsOf
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pad_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.GeoBase.congr
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.GeoUpTo.congr
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.BufferKept
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.BufferFrame
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EmitsFrom
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.emitsFrom
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.shiftFrom
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EmitsFrom.trans
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.EmitsFrom.memory_at
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.getD_map_append_replicate_false
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bufferCells_getD
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bufferCells_length
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bufferTail_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bufferAccessClose_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bufferHead_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bufferStage_spec
#print axioms PRE1StageConsumer.fringeDecodeActs_def
#print axioms PRE1StageConsumer.fringeStepBlock_def
#print axioms PRE1StageConsumer.fringeEntryBlock_def
#print axioms PRE1StageConsumer.selectDecodeActs_def
#print axioms PRE1StageConsumer.selectStepBlock_def
#print axioms PRE1StageConsumer.selectEntryBlock_def
#print axioms PRE1StageConsumer.microtablesBlock_def
#print axioms PRE1StageConsumer.headerReserveBlock_def
#print axioms PRE1StageConsumer.headerPatchStepBlock_def
#print axioms PRE1StageConsumer.headerPatchBlock_def
#print axioms PRE1StageConsumer.zerosBlock_def
#print axioms PRE1StageConsumer.padBlock_def
#print axioms PRE1StageConsumer.bufferBlock_def
#print axioms PRE1StageConsumer.spec_MicroWrites_def
#print axioms PRE1StageConsumer.spec_BufferKept_def
#print axioms PRE1StageConsumer.spec_BufferFrame_def
#print axioms PRE1StageConsumer.spec_EmitsFrom_def
#print axioms PRE1StageConsumer.spec_denseBitsOf_def
#print axioms PRE1StageConsumer.spec_natToBitsLE_getElem
#print axioms PRE1StageConsumer.spec_pattern_getElem
#print axioms PRE1StageConsumer.spec_pattern_rank_true_succ
#print axioms PRE1StageConsumer.spec_pattern_rank_false_succ
#print axioms PRE1StageConsumer.spec_excessOffset_succ
#print axioms PRE1StageConsumer.spec_scanArgMin_snoc
#print axioms PRE1StageConsumer.spec_selectPos_step
#print axioms PRE1StageConsumer.spec_selectPos_final
#print axioms PRE1StageConsumer.spec_fringeBest_step
#print axioms PRE1StageConsumer.spec_selectStep_spec
#print axioms PRE1StageConsumer.spec_selectEntry_spec
#print axioms PRE1StageConsumer.spec_selectTable_spec
#print axioms PRE1StageConsumer.spec_fringeStep_spec
#print axioms PRE1StageConsumer.spec_fringeEntry_spec
#print axioms PRE1StageConsumer.spec_fringeTable_spec
#print axioms PRE1StageConsumer.spec_microtables_spec
#print axioms PRE1StageConsumer.spec_zeroLoop_spec
#print axioms PRE1StageConsumer.spec_zeros_spec
#print axioms PRE1StageConsumer.spec_headerReserve_spec
#print axioms PRE1StageConsumer.spec_headerPatch_spec
#print axioms PRE1StageConsumer.spec_prefix_reserve
#print axioms PRE1StageConsumer.spec_pad_spec
#print axioms PRE1StageConsumer.spec_GeoBase_congr
#print axioms PRE1StageConsumer.spec_GeoUpTo_congr
#print axioms PRE1StageConsumer.spec_Emits_shiftFrom
#print axioms PRE1StageConsumer.spec_EmitsFrom_trans
#print axioms PRE1StageConsumer.spec_EmitsFrom_memory_at
#print axioms PRE1StageConsumer.spec_bufferCells_getD
#print axioms PRE1StageConsumer.spec_bufferCells_length
#print axioms PRE1StageConsumer.spec_bufferTail_spec
#print axioms PRE1StageConsumer.spec_bufferAccessClose_spec
#print axioms PRE1StageConsumer.spec_bufferHead_spec
#print axioms PRE1StageConsumer.spec_bufferStage_spec
#print axioms PRE1StageConsumer.s6MicroProgram
#print axioms PRE1StageConsumer.s6Micro
#print axioms PRE1StageConsumer.s6ArraysHarness
#print axioms PRE1StageConsumer.s6BufferProgram
#print axioms PRE1StageConsumer.s6Buffer
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_sc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_lcS
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_len18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_o18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_acc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_a
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_b18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_pay
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_oldCount
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_oldBits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_dcount
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_wc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ioff
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_foff
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_soff
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_fbase
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_sbase
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q2n
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cc2n
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_aliasWc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_qsup
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_lfwc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_qsp
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_sfwc
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_fbits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_sbits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q_39
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cc_39
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q_61
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cc_61
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q_58
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cc_58
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q_60
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cc_60
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q_36
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cc_36
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q_37
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cc_37
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cd_39
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cd_61
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cd_58
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cd_60
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cd_36
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_cd_37
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_BW
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_MR
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_LT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_GT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_LL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_GL
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_p2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_p3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_p4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_p5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_p6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_p7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ptot
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q1bits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q2bits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q5bits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q6bits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_q7bits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.mv_ib7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVals
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_21
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_22
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_23
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_24
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_25
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_26
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_27
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_28
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_29
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_30
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_31
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_33
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_34
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_35
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_36
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_37
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_38
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_39
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_40
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_41
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_42
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_43
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_44
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_45
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_46
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_47
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_48
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_49
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_50
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_51
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_52
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_53
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_54
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_55
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_56
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_57
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_58
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_59
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_60
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_61
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_62
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_63
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_64
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_65
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_66
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_67
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_68
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_69
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_70
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_71
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_72
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_73
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_74
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_75
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_76
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_77
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_78
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_79
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_80
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_81
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_82
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_83
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_84
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_85
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_86
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_87
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_88
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_89
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_90
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_91
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_92
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_93
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_94
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_95
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_96
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_97
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_98
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_99
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_100
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_101
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_102
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_103
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_104
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_105
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_106
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaVal_107
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaWords
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_finalRankSuperFalse
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_finalRankBlockFalse
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectSuperBaseOccurrence
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectSuperBaseWordIndex
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectSuperRankBefore
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectSuperFirstOffset
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLocalBaseOccurrence
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLocalBaseWordIndex
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLocalRankBefore
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLocalFirstOffset
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLongFlagRankSuperTrue
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLongFlagRankBlockTrue
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLongFlagBits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectLongRelative
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectSparseRankSuperTrue
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectSparseRankBlockTrue
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.srcLen_selectSparseFlagBits
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.ws_pos
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.tableWords_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.pay_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.cellCount_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_21
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.regDesc_22
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_baseline
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_minRel
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_maxRel
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_argOffset
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_localOffset
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_globalBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_localLevel
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.intDesc_globalLevel
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.scalar_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Spec.metaWords_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rASZ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rDCNT
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRI
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRIGO
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRA
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rACC
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRJ
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.rRB
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.arraysBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.metaStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.metaChain
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.emitRegs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.metaWordRegs
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.metaEmitBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.hornerStepBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.repackWordBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.repackBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Builder.outputBlock
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ceilDiv_le_self'
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.lt0_le_one
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.log2_add_one_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaAtoms
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaVal_le
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.lt0_eq
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.MetaBase
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.MetaUpTo
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.MetaStepOK
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep_pure
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep0
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep1
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep2
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep3
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep4
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep5
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep6
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep7
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep8
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep9
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep10
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep11
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep12
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep13
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep14
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep15
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep16
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep17
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep18
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep19
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep20
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep21
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep22
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep23
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep24
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep25
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep26
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep27
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep28
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep29
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep30
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep31
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep33
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep34
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep35
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep36
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep37
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep38
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep39
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep40
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep41
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep42
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep43
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep44
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep45
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep46
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep47
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep48
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep49
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep50
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep51
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep52
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep53
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep54
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep55
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep56
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep57
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep58
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep59
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep60
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep61
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep62
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep63
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep64
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep65
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep66
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep67
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep68
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep69
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep70
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep71
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep72
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep73
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep74
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep75
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep76
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep77
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep78
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep79
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep80
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep81
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep82
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep83
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep84
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep85
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep86
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep87
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep88
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep89
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep90
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep91
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep92
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep93
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep94
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep95
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep96
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep97
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep98
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep99
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep100
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep101
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep102
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep103
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep104
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep105
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep106
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep107
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaStep_all
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaChain_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.put_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Action.Safe.regs_fit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.SafeEval.regs_fit
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitRegs_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaHead_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaWordRegs_ne_ten
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaWordRegs_length
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaWordRegs_map
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaWordRegs_ne_three
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.metaEmit_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cellsLE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cellsLE_lt
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cellsLE_eq_bitsToNatLE
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.hornerWords
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.hornerStep_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.hornerLoop_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.repackWord_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.repack_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.dcount_eq_denseCount
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.outputWords_eq_buildMemory
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.outputStage_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.ArraysWritten
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.Emits.replicate_congr
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.arrayStep
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.arraysBlock_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.pay_le_of_shape
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.arrays_le_of_pay
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.tailStage_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bufferStage_kept
#print axioms PRE1StageConsumer.spec_metaChain_spec
#print axioms PRE1StageConsumer.spec_MetaBase_def
#print axioms PRE1StageConsumer.spec_MetaUpTo_def
#print axioms PRE1StageConsumer.outputBlock_def
#print axioms PRE1StageConsumer.repackBlock_def
#print axioms PRE1StageConsumer.metaEmitBlock_def
#print axioms PRE1StageConsumer.spec_SafeEval_regs_fit
#print axioms PRE1StageConsumer.spec_emitRegs_spec
#print axioms PRE1StageConsumer.spec_metaHead_spec
#print axioms PRE1StageConsumer.spec_metaEmit_spec
#print axioms PRE1StageConsumer.spec_cellsLE_lt
#print axioms PRE1StageConsumer.spec_cellsLE_eq_bitsToNatLE
#print axioms PRE1StageConsumer.spec_hornerStep_spec
#print axioms PRE1StageConsumer.spec_hornerLoop_spec
#print axioms PRE1StageConsumer.spec_repackWord_spec
#print axioms PRE1StageConsumer.spec_repack_spec
#print axioms PRE1StageConsumer.spec_dcount_eq_denseCount
#print axioms PRE1StageConsumer.spec_outputWords_eq_buildMemory
#print axioms PRE1StageConsumer.spec_outputStage_spec
#print axioms PRE1StageConsumer.spec_arraysBlock_spec
#print axioms PRE1StageConsumer.spec_bufferStage_kept
#print axioms PRE1StageConsumer.spec_pay_le_of_shape
#print axioms PRE1StageConsumer.spec_arrays_le_of_pay
#print axioms PRE1StageConsumer.spec_tailStage_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderBudget_eq_mul_add
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.fringeOverhead_ge_two
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.two_n_four_lt_cellPow
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.bankcap_wordWidth
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.cap_wordWidth
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.header_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderSource_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderRun_spec
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.emitted_eq_of_stored
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.run_of_halting
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.wordWidth_ge_32
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.budget_ge
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builder_run_comparison
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.efficientBuild_eq_buildMemory
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.efficientBuildWord_eq_buildMemory
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builder_leaf_difference
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgram_contract
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.builderProgramWord_contract
#print axioms PRE1StageConsumer.spec_metaVal_le
#print axioms PRE1StageConsumer.spec_metaWords_eq
#print axioms PRE1StageConsumer.spec_pay_eq
#print axioms PRE1StageConsumer.spec_cellCount_eq
#print axioms PRE1StageConsumer.s7HarnessProgram
#print axioms PRE1StageConsumer.s7Output
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_229
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_230
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_231
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_232
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_233
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_234
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_235
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_236
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_237
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_238
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_239
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_240
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_241
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_242
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_243
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_244
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_245
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_246
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_247
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_248
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_249
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_250
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_251
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_252
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_253
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_254
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_255
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_256
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_257
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_258
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_259
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_260
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_261
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_262
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_263
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_264
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_265
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_266
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_267
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_268
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_269
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_270
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_271
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_272
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_273
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_274
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_275
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_276
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_277
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_278
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_279
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_280
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_281
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_282
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_283
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_284
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_285
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_286
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_287
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_288
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_289
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_290
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_291
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_292
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_293
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_294
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_295
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_296
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_297
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_298
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_299
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_300
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_301
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_302
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_303
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_304
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_305
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_306
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_307
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_308
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_309
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_310
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_311
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_312
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_313
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_314
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_315
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_316
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_317
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_318
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_319
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_320
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_321
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_322
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_323
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_324
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_325
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_326
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_327
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_328
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_329
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_330
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_331
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_332
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_333
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_334
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_335
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_336
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_337
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_338
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_339
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_340
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_341
#print axioms RMQ.SuccinctFinal.PackedConstruction.Proof.operand_val_342
/-! ## Verdict marker (coordinator item before the S8 freeze, DD-20260913-PRE1-013; repair PRE-1-R2 of audit PRE-1-A2 P2-1)

The exit code is the verdict. The marker is printed if and only if (1) the whole
file elaborates with no error-severity message, (2) `consumerWitness`, which
refers to each declaration above, exists and collects no `sorryAx`, and (3)
every fixture check holds (`stageGuards`, evaluated here once); a missing or
`sorryAx`-dependent witnessed declaration or a failing fixture check logs one
error here instead of the marker, as before, and a failure of (1) alone prints
nothing. Lean 4.22 resets the command state's message log before every command
(`Lean.Language.Lean.process.doElab` sets `messages := .empty`), so this command
cannot read an earlier command's errors from its own state. For the whole-file
condition it elaborates the file a second time in this process from the source
text of its own input context, with only this command blanked (line breaks
kept), through `Lean.Parser.parseHeader`, `Lean.Elab.processHeader` and
`Lean.Elab.IO.processCommands`, which collects the message logs of every command
snapshot, and requires `MessageLog.hasErrors` to be false for the header and for
those messages: the predicate by which the frontend decides the exit code. An
error in any command kind (a declaration, an anonymous example, a `#guard` or
`run_cmd` check, a missing declaration after a maximum-recursion-depth failure,
or a command after this one) therefore suppresses the marker. -/

def consumerWitness : Unit :=
  let _ := @PRE1StageConsumer.emitBits_def
  let _ := @PRE1StageConsumer.levelEntryBlock_def
  let _ := @PRE1StageConsumer.spec_emitBits
  let _ := @PRE1StageConsumer.spec_emitTable
  let _ := @PRE1StageConsumer.spec_log2Block
  let _ := @PRE1StageConsumer.spec_Emits_def
  let _ := @PRE1StageConsumer.spec_interiorGeometry
  let _ := @PRE1StageConsumer.spec_localLevelTable_emits_payload
  let _ := @PRE1StageConsumer.spec_globalLevelTable_emits_payload
  let _ := @PRE1StageConsumer.smokeState
  let _ := @PRE1StageConsumer.smokeCells
  let _ := @PRE1StageConsumer.stageGuard1
  let _ := @PRE1StageConsumer.stageGuard2
  let _ := @PRE1StageConsumer.stageGuard3
  let _ := @PRE1StageConsumer.stageGuard4
  let _ := @PRE1StageConsumer.spec_RegSpec_def
  let _ := @PRE1StageConsumer.spec_RegSpec_pure
  let _ := @PRE1StageConsumer.spec_RegSpec_log2
  let _ := @PRE1StageConsumer.spec_forSlots
  let _ := @PRE1StageConsumer.spec_reserveArray
  let _ := @PRE1StageConsumer.spec_emitFlatMap
  let _ := @PRE1StageConsumer.spec_geoVal_pins
  let _ := @PRE1StageConsumer.spec_GeoUpTo_def
  let _ := @PRE1StageConsumer.spec_GeoBase_def
  let _ := @PRE1StageConsumer.geometryPrelude_def
  let _ := @PRE1StageConsumer.geoStepBlock_36_def
  let _ := @PRE1StageConsumer.spec_geometryPrelude
  let _ := @PRE1StageConsumer.spec_geoChain
  let _ := @PRE1StageConsumer.geoSmoke
  let _ := @PRE1StageConsumer.stageGuard5
  let _ := @PRE1StageConsumer.stageGuard6
  let _ := @PRE1StageConsumer.stageGuard7
  let _ := @PRE1StageConsumer.stageGuard8
  let _ := @PRE1StageConsumer.stageGuard9
  let _ := @PRE1StageConsumer.keyLeaf_def
  let _ := @PRE1StageConsumer.wordLeaf_def
  let _ := @PRE1StageConsumer.spec_KeySpec_def
  let _ := @PRE1StageConsumer.spec_OracleInput_def
  let _ := @PRE1StageConsumer.spec_WordInput_def
  let _ := @PRE1StageConsumer.spec_keyLeaf
  let _ := @PRE1StageConsumer.spec_wordLeaf
  let _ := @PRE1StageConsumer.spec_spineFrom_insertRight
  let _ := @PRE1StageConsumer.spec_insertPoint_eq_find
  let _ := @PRE1StageConsumer.spec_spineFrom_sorted
  let _ := @PRE1StageConsumer.spec_openCounts_sum
  let _ := @PRE1StageConsumer.spec_cartesianBP_key
  let _ := @PRE1StageConsumer.spec_cartesianBP_word
  let _ := @PRE1StageConsumer.s3Program
  let _ := @PRE1StageConsumer.s3Cells
  let _ := @PRE1StageConsumer.s3Key
  let _ := @PRE1StageConsumer.s3Word
  let _ := @PRE1StageConsumer.stageGuard10
  let _ := @PRE1StageConsumer.stageGuard11
  let _ := @PRE1StageConsumer.stageGuard12
  let _ := @PRE1StageConsumer.stageGuard13
  let _ := @PRE1StageConsumer.stageGuard14
  let _ := @PRE1StageConsumer.stageGuard15
  let _ := @PRE1StageConsumer.stageGuard16
  let _ := @PRE1StageConsumer.maxActs_def
  let _ := @PRE1StageConsumer.blockStatsBlock_def
  let _ := @PRE1StageConsumer.summaryTablesBlock_def
  let _ := @PRE1StageConsumer.relativeEntryBlock_def
  let _ := @PRE1StageConsumer.spec_argStep_def
  let _ := @PRE1StageConsumer.spec_bpBlockArgMinPrefixPosFrom_eq_argAcc
  let _ := @PRE1StageConsumer.spec_natListMinFrom_append_singleton
  let _ := @PRE1StageConsumer.spec_natListMax_append_singleton
  let _ := @PRE1StageConsumer.spec_argAcc_ge
  let _ := @PRE1StageConsumer.spec_bpCell_def
  let _ := @PRE1StageConsumer.spec_SampleFrame_def
  let _ := @PRE1StageConsumer.spec_StatsFrame_def
  let _ := @PRE1StageConsumer.spec_SummaryFrame_def
  let _ := @PRE1StageConsumer.spec_Region_def
  let _ := @PRE1StageConsumer.spec_sampleLoop
  let _ := @PRE1StageConsumer.spec_blockBody
  let _ := @PRE1StageConsumer.spec_blockStats
  let _ := @PRE1StageConsumer.spec_baselineEntry
  let _ := @PRE1StageConsumer.spec_relativeEntry
  let _ := @PRE1StageConsumer.spec_argOffsetEntry
  let _ := @PRE1StageConsumer.spec_summaryTables
  let _ := @PRE1StageConsumer.spec_tableBits_def
  let _ := @PRE1StageConsumer.s4ArraysHarness
  let _ := @PRE1StageConsumer.s4Program
  let _ := @PRE1StageConsumer.s4Summary
  let _ := @PRE1StageConsumer.s4Input
  let _ := @PRE1StageConsumer.stageGuard17
  let _ := @PRE1StageConsumer.stageGuard18
  let _ := @PRE1StageConsumer.stageGuard19
  let _ := @PRE1StageConsumer.stageGuard20
  let _ := @PRE1StageConsumer.betterActs_def
  let _ := @PRE1StageConsumer.memoLevelsBlock_def
  let _ := @PRE1StageConsumer.localMemoBlock_def
  let _ := @PRE1StageConsumer.globalMemoBlock_def
  let _ := @PRE1StageConsumer.interiorCloseBlock_def
  let _ := @PRE1StageConsumer.spec_CloseFrame_def
  let _ := @PRE1StageConsumer.spec_interiorPayload_eq_segments
  let _ := @PRE1StageConsumer.spec_argPos_excess_eq_min
  let _ := @PRE1StageConsumer.spec_better_eq_min
  let _ := @PRE1StageConsumer.spec_rangeArgMin_snoc
  let _ := @PRE1StageConsumer.spec_globalMemo_double
  let _ := @PRE1StageConsumer.spec_memoCell
  let _ := @PRE1StageConsumer.spec_memoLevels
  let _ := @PRE1StageConsumer.spec_localMemo
  let _ := @PRE1StageConsumer.spec_macroScan
  let _ := @PRE1StageConsumer.spec_globalMemo
  let _ := @PRE1StageConsumer.spec_localEntry
  let _ := @PRE1StageConsumer.spec_globalEntry
  let _ := @PRE1StageConsumer.spec_localSparseTable
  let _ := @PRE1StageConsumer.spec_globalSparseTable
  let _ := @PRE1StageConsumer.spec_interiorCloseLayout
  let _ := @PRE1StageConsumer.spec_closeSegment
  let _ := @PRE1StageConsumer.s4CloseProgram
  let _ := @PRE1StageConsumer.s4Close
  let _ := @PRE1StageConsumer.stageGuard21
  let _ := @PRE1StageConsumer.stageGuard22
  let _ := @PRE1StageConsumer.stageGuard23
  let _ := @PRE1StageConsumer.stageGuard24
  let _ := @PRE1StageConsumer.stageGuard25
  let _ := @PRE1StageConsumer.posActs_def
  let _ := @PRE1StageConsumer.monusActs_def
  let _ := @PRE1StageConsumer.posStepBlock_def
  let _ := @PRE1StageConsumer.posPassBlock_def
  let _ := @PRE1StageConsumer.longFlagBlock_def
  let _ := @PRE1StageConsumer.longFlagsBlock_def
  let _ := @PRE1StageConsumer.sparseFlagBlock_def
  let _ := @PRE1StageConsumer.sparseFlagsBlock_def
  let _ := @PRE1StageConsumer.rankSuperEntryBlock_def
  let _ := @PRE1StageConsumer.rankBlockEntryBlock_def
  let _ := @PRE1StageConsumer.superOccEntryBlock_def
  let _ := @PRE1StageConsumer.superWordEntryBlock_def
  let _ := @PRE1StageConsumer.superFlagEntryBlock_def
  let _ := @PRE1StageConsumer.superOffsetEntryBlock_def
  let _ := @PRE1StageConsumer.localDecodeActs_def
  let _ := @PRE1StageConsumer.localOccEntryBlock_def
  let _ := @PRE1StageConsumer.localWordEntryBlock_def
  let _ := @PRE1StageConsumer.localFlagEntryBlock_def
  let _ := @PRE1StageConsumer.localOffsetEntryBlock_def
  let _ := @PRE1StageConsumer.flagRankEntryBlock_def
  let _ := @PRE1StageConsumer.zeroEntryBlock_def
  let _ := @PRE1StageConsumer.flagEntryBlock_def
  let _ := @PRE1StageConsumer.relativeOffsetEntryBlock_def
  let _ := @PRE1StageConsumer.longRelativeBodyBlock_def
  let _ := @PRE1StageConsumer.sparseRelativeBodyBlock_def
  let _ := @PRE1StageConsumer.accessHalfBlock_def
  let _ := @PRE1StageConsumer.spec_AccessWrites_def
  let _ := @PRE1StageConsumer.spec_RelWrites_def
  let _ := @PRE1StageConsumer.spec_BodyWrites_def
  let _ := @PRE1StageConsumer.spec_AccessFrame_def
  let _ := @PRE1StageConsumer.spec_AccessHalfFrame_def
  let _ := @PRE1StageConsumer.spec_flagNat_def
  let _ := @PRE1StageConsumer.spec_liveAccessPayload_eq_segments
  let _ := @PRE1StageConsumer.spec_select_at_close
  let _ := @PRE1StageConsumer.spec_position_at_close
  let _ := @PRE1StageConsumer.spec_rankPrefix_false_succ
  let _ := @PRE1StageConsumer.spec_bp_occurrenceCount
  let _ := @PRE1StageConsumer.spec_bp_rank_end
  let _ := @PRE1StageConsumer.spec_bp_position_size
  let _ := @PRE1StageConsumer.spec_position_min_size
  let _ := @PRE1StageConsumer.spec_posStep_spec
  let _ := @PRE1StageConsumer.spec_posPass_spec
  let _ := @PRE1StageConsumer.spec_posActs_prefix
  let _ := @PRE1StageConsumer.spec_monusActs_prefix
  let _ := @PRE1StageConsumer.spec_longFlag_spec
  let _ := @PRE1StageConsumer.spec_longFlags_spec
  let _ := @PRE1StageConsumer.spec_sparseFlag_spec
  let _ := @PRE1StageConsumer.spec_sparseFlags_spec
  let _ := @PRE1StageConsumer.spec_flagEntry_spec
  let _ := @PRE1StageConsumer.spec_flagRankEntry_spec
  let _ := @PRE1StageConsumer.spec_rankBlockEntry_spec
  let _ := @PRE1StageConsumer.spec_zeroEntry_spec
  let _ := @PRE1StageConsumer.spec_superOccEntry_spec
  let _ := @PRE1StageConsumer.spec_relOffsetEntry_spec
  let _ := @PRE1StageConsumer.spec_superWordEntry_spec
  let _ := @PRE1StageConsumer.spec_superOffsetEntry_spec
  let _ := @PRE1StageConsumer.spec_localDecode_prefix
  let _ := @PRE1StageConsumer.spec_localOccEntry_spec
  let _ := @PRE1StageConsumer.spec_localWordEntry_spec
  let _ := @PRE1StageConsumer.spec_localFlagEntry_spec
  let _ := @PRE1StageConsumer.spec_localOffsetEntry_spec
  let _ := @PRE1StageConsumer.spec_relativeOffsetsOrZero_eq_positions
  let _ := @PRE1StageConsumer.spec_longRelativeBody_spec
  let _ := @PRE1StageConsumer.spec_sparseRelativeBody_spec
  let _ := @PRE1StageConsumer.spec_relLoop_spec
  let _ := @PRE1StageConsumer.spec_longRelative_spec
  let _ := @PRE1StageConsumer.spec_sparseRelative_spec
  let _ := @PRE1StageConsumer.spec_accessTable_generic
  let _ := @PRE1StageConsumer.spec_accessRegs_of_bank
  let _ := @PRE1StageConsumer.spec_access_caps
  let _ := @PRE1StageConsumer.spec_accessPasses_spec
  let _ := @PRE1StageConsumer.spec_accessSegments_eq
  let _ := @PRE1StageConsumer.spec_accessHalf_spec
  let _ := @PRE1StageConsumer.spec_lc_eq_longCount
  let _ := @PRE1StageConsumer.spec_sc_eq_sparseCount
  let _ := @PRE1StageConsumer.s5ArraysHarness
  let _ := @PRE1StageConsumer.s5Program
  let _ := @PRE1StageConsumer.s5Access
  let _ := @PRE1StageConsumer.stageGuard26
  let _ := @PRE1StageConsumer.stageGuard27
  let _ := @PRE1StageConsumer.stageGuard28
  let _ := @PRE1StageConsumer.stageGuard29
  let _ := @PRE1StageConsumer.fringeDecodeActs_def
  let _ := @PRE1StageConsumer.fringeStepBlock_def
  let _ := @PRE1StageConsumer.fringeEntryBlock_def
  let _ := @PRE1StageConsumer.selectDecodeActs_def
  let _ := @PRE1StageConsumer.selectStepBlock_def
  let _ := @PRE1StageConsumer.selectEntryBlock_def
  let _ := @PRE1StageConsumer.microtablesBlock_def
  let _ := @PRE1StageConsumer.headerReserveBlock_def
  let _ := @PRE1StageConsumer.headerPatchStepBlock_def
  let _ := @PRE1StageConsumer.headerPatchBlock_def
  let _ := @PRE1StageConsumer.zerosBlock_def
  let _ := @PRE1StageConsumer.padBlock_def
  let _ := @PRE1StageConsumer.bufferBlock_def
  let _ := @PRE1StageConsumer.spec_MicroWrites_def
  let _ := @PRE1StageConsumer.spec_BufferKept_def
  let _ := @PRE1StageConsumer.spec_BufferFrame_def
  let _ := @PRE1StageConsumer.spec_EmitsFrom_def
  let _ := @PRE1StageConsumer.spec_denseBitsOf_def
  let _ := @PRE1StageConsumer.spec_natToBitsLE_getElem
  let _ := @PRE1StageConsumer.spec_pattern_getElem
  let _ := @PRE1StageConsumer.spec_pattern_rank_true_succ
  let _ := @PRE1StageConsumer.spec_pattern_rank_false_succ
  let _ := @PRE1StageConsumer.spec_excessOffset_succ
  let _ := @PRE1StageConsumer.spec_scanArgMin_snoc
  let _ := @PRE1StageConsumer.spec_selectPos_step
  let _ := @PRE1StageConsumer.spec_selectPos_final
  let _ := @PRE1StageConsumer.spec_fringeBest_step
  let _ := @PRE1StageConsumer.spec_selectStep_spec
  let _ := @PRE1StageConsumer.spec_selectEntry_spec
  let _ := @PRE1StageConsumer.spec_selectTable_spec
  let _ := @PRE1StageConsumer.spec_fringeStep_spec
  let _ := @PRE1StageConsumer.spec_fringeEntry_spec
  let _ := @PRE1StageConsumer.spec_fringeTable_spec
  let _ := @PRE1StageConsumer.spec_microtables_spec
  let _ := @PRE1StageConsumer.spec_zeroLoop_spec
  let _ := @PRE1StageConsumer.spec_zeros_spec
  let _ := @PRE1StageConsumer.spec_headerReserve_spec
  let _ := @PRE1StageConsumer.spec_headerPatch_spec
  let _ := @PRE1StageConsumer.spec_prefix_reserve
  let _ := @PRE1StageConsumer.spec_pad_spec
  let _ := @PRE1StageConsumer.spec_GeoBase_congr
  let _ := @PRE1StageConsumer.spec_GeoUpTo_congr
  let _ := @PRE1StageConsumer.spec_Emits_shiftFrom
  let _ := @PRE1StageConsumer.spec_EmitsFrom_trans
  let _ := @PRE1StageConsumer.spec_EmitsFrom_memory_at
  let _ := @PRE1StageConsumer.spec_bufferCells_getD
  let _ := @PRE1StageConsumer.spec_bufferCells_length
  let _ := @PRE1StageConsumer.spec_bufferTail_spec
  let _ := @PRE1StageConsumer.spec_bufferAccessClose_spec
  let _ := @PRE1StageConsumer.spec_bufferHead_spec
  let _ := @PRE1StageConsumer.spec_bufferStage_spec
  let _ := @PRE1StageConsumer.s6MicroProgram
  let _ := @PRE1StageConsumer.s6Micro
  let _ := @PRE1StageConsumer.stageGuard30
  let _ := @PRE1StageConsumer.s6ArraysHarness
  let _ := @PRE1StageConsumer.s6BufferProgram
  let _ := @PRE1StageConsumer.s6Buffer
  let _ := @PRE1StageConsumer.stageGuard31
  let _ := @PRE1StageConsumer.stageGuard32
  let _ := @PRE1StageConsumer.stageGuard33
  let _ := @PRE1StageConsumer.stageGuard34
  let _ := @PRE1StageConsumer.spec_metaChain_spec
  let _ := @PRE1StageConsumer.spec_MetaBase_def
  let _ := @PRE1StageConsumer.spec_MetaUpTo_def
  let _ := @PRE1StageConsumer.outputBlock_def
  let _ := @PRE1StageConsumer.repackBlock_def
  let _ := @PRE1StageConsumer.metaEmitBlock_def
  let _ := @PRE1StageConsumer.spec_SafeEval_regs_fit
  let _ := @PRE1StageConsumer.spec_emitRegs_spec
  let _ := @PRE1StageConsumer.spec_metaHead_spec
  let _ := @PRE1StageConsumer.spec_metaEmit_spec
  let _ := @PRE1StageConsumer.spec_cellsLE_lt
  let _ := @PRE1StageConsumer.spec_cellsLE_eq_bitsToNatLE
  let _ := @PRE1StageConsumer.spec_hornerStep_spec
  let _ := @PRE1StageConsumer.spec_hornerLoop_spec
  let _ := @PRE1StageConsumer.spec_repackWord_spec
  let _ := @PRE1StageConsumer.spec_repack_spec
  let _ := @PRE1StageConsumer.spec_dcount_eq_denseCount
  let _ := @PRE1StageConsumer.spec_outputWords_eq_buildMemory
  let _ := @PRE1StageConsumer.spec_outputStage_spec
  let _ := @PRE1StageConsumer.spec_arraysBlock_spec
  let _ := @PRE1StageConsumer.spec_bufferStage_kept
  let _ := @PRE1StageConsumer.spec_pay_le_of_shape
  let _ := @PRE1StageConsumer.spec_arrays_le_of_pay
  let _ := @PRE1StageConsumer.spec_tailStage_spec
  let _ := @PRE1StageConsumer.spec_metaVal_le
  let _ := @PRE1StageConsumer.spec_metaWords_eq
  let _ := @PRE1StageConsumer.spec_pay_eq
  let _ := @PRE1StageConsumer.spec_cellCount_eq
  let _ := @PRE1StageConsumer.s7HarnessProgram
  let _ := @PRE1StageConsumer.s7Output
  let _ := @PRE1StageConsumer.stageGuard35
  let _ := @PRE1StageConsumer.spec_builderBudget_eq_mul_add
  let _ := @PRE1StageConsumer.spec_fringeOverhead_ge_two
  let _ := @PRE1StageConsumer.spec_two_n_four_lt_cellPow
  let _ := @PRE1StageConsumer.spec_bankcap_wordWidth
  let _ := @PRE1StageConsumer.spec_cap_wordWidth
  let _ := @PRE1StageConsumer.spec_header_spec
  let _ := @PRE1StageConsumer.spec_builderSource_spec
  let _ := @PRE1StageConsumer.spec_builderRun_spec
  let _ := @PRE1StageConsumer.spec_emitted_eq_of_stored
  let _ := @PRE1StageConsumer.spec_run_of_halting
  let _ := @PRE1StageConsumer.spec_wordWidth_ge_32
  let _ := @PRE1StageConsumer.spec_budget_ge
  let _ := @PRE1StageConsumer.spec_builder_run_comparison
  let _ := @PRE1StageConsumer.spec_efficientBuild_eq_buildMemory
  let _ := @PRE1StageConsumer.spec_efficientBuildWord_eq_buildMemory
  let _ := @PRE1StageConsumer.s7Production
  let _ := @PRE1StageConsumer.s7ProductionWord
  let _ := @PRE1StageConsumer.stageGuard36
  ()

def stageGuards : Bool :=
  stageGuard1 &&
  stageGuard2 &&
  stageGuard3 &&
  stageGuard4 &&
  stageGuard5 &&
  stageGuard6 &&
  stageGuard7 &&
  stageGuard8 &&
  stageGuard9 &&
  stageGuard10 &&
  stageGuard11 &&
  stageGuard12 &&
  stageGuard13 &&
  stageGuard14 &&
  stageGuard15 &&
  stageGuard16 &&
  stageGuard17 &&
  stageGuard18 &&
  stageGuard19 &&
  stageGuard20 &&
  stageGuard21 &&
  stageGuard22 &&
  stageGuard23 &&
  stageGuard24 &&
  stageGuard25 &&
  stageGuard26 &&
  stageGuard27 &&
  stageGuard28 &&
  stageGuard29 &&
  stageGuard30 &&
  stageGuard31 &&
  stageGuard32 &&
  stageGuard33 &&
  stageGuard34 &&
  stageGuard35 &&
  stageGuard36

open Lean Elab Command in
#eval show CommandElabM Unit from do
  -- (1) Whole file: elaborate this file again in this process from its own
  -- source text, with only this command blanked (line breaks kept), and read
  -- the message log of the header and of every command.
  let context ← read
  let source := context.fileMap.source
  let scope ← getScope
  let markerStop := (Parser.parseCommand (Parser.mkInputContext source context.fileName)
    { env := ← getEnv, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls } { pos := context.cmdPos } {}).2.1.pos
  let blank := (source.extract context.cmdPos markerStop).map
    fun c => if c == '\n' || c == '\r' then c else ' '
  let input := Parser.mkInputContext
    (source.extract 0 context.cmdPos ++ blank ++ source.extract markerStop source.endPos)
    context.fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader input
  let options := Elab.async.setIfNotSet (internal.cmdlineSnapshots.setIfNotSet {} true) true
  let (headerEnv, headerMessages) ← processHeader header options headerMessages input
    (trustLevel := (← getEnv).header.trustLevel) (leakEnv := true)
    (mainModule := (← getEnv).mainModule)
  let whole ← IO.processCommands input parserState (Command.mkState headerEnv {} options)
  let fileClean := !headerMessages.hasErrors && !whole.commandState.messages.hasErrors
  -- (2) The witness exists and collects no `sorryAx`.
  let witness := `PRE1StageConsumer.consumerWitness
  let witnessClean ← if (← getEnv).contains witness then
      pure !((← collectAxioms witness).contains ``sorryAx)
    else pure false
  -- (3) The fixture checks hold; the two existing failure diagnostics stay.
  if !witnessClean then
    logError "PRE1-STAGE-TYPED-CONSUMERS FAIL: a declaration is missing or depends on sorry"
  else if !stageGuards then
    logError "PRE1-STAGE-TYPED-CONSUMERS FAIL: an executable fixture check is false"
  else if fileClean then
    IO.println "PRE1-STAGE-TYPED-CONSUMERS PASS"
end PRE1StageConsumer