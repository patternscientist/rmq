import RMQ.Core.WordRAM.Construction.Proof.SparseTables
import RMQ.Core.WordRAM.Construction.Spec.Envelope

/-! # PRE-1 builder proofs: the interior close segment (stage S4)

Outside the builder firewall. `interiorCloseBlock` runs the block statistics,
the local and global sparse memos, and then emits the eight interior tables in
payload order. `interiorCloseLayout_spec` states this for any layout meeting
size-only premises: the work touches only the statistics and memo arrays below
the extent, and the emission is exactly the eight `tableBits` segments.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose

/-- Registers the interior close leaves unchanged. -/
def CloseFrame (r : Nat) : Prop :=
  ¬ (10 ≤ r ∧ r ≤ 16) ∧ ¬ (20 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ ¬ (120 ≤ r ∧ r ≤ 134) ∧
    ¬ (137 ≤ r ∧ r ≤ 158)

/-- **Interior close, any layout.** -/
theorem interiorCloseLayout_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hone : s.regs 2 = 1) (htwo : s.regs 9 = 2)
    (A0 A1 A2 A3 B Bm Gb bs bps bc ssc sw rw M mc LC GLC BAW ldom lwid gdom gwid : Nat)
    (h115 : s.regs 115 = A0) (h116 : s.regs 116 = A1) (h117 : s.regs 117 = A2)
    (h118 : s.regs 118 = A3) (h119 : s.regs 119 = B) (h135 : s.regs 135 = Bm)
    (h136 : s.regs 136 = Gb) (h56 : s.regs 56 = bs) (h32 : s.regs 32 = bc)
    (h38 : s.regs 38 = shape.bpCode.length) (h30 : s.regs 30 = bps) (h57 : s.regs 57 = ssc)
    (h39 : s.regs 39 = sw) (h61 : s.regs 61 = rw) (h31 : s.regs 31 = M) (h33 : s.regs 33 = mc)
    (h58 : s.regs 58 = LC) (h59 : s.regs 59 = GLC) (h60 : s.regs 60 = BAW)
    (h62 : s.regs 62 = mc * (LC * M)) (h63 : s.regs 63 = GLC * mc)
    (h34 : s.regs 34 = ldom) (h36 : s.regs 36 = lwid) (h35 : s.regs 35 = gdom)
    (h37 : s.regs 37 = gwid)
    (hR : Region s B shape.bpCode.length (bpCell shape))
    (hBext : B + shape.bpCode.length ≤ s.extent)
    (hA01 : A0 + bc + 1 ≤ A1) (hA12 : A1 + bc ≤ A2) (hA23 : A2 + bc ≤ A3) (hA3m : A3 + bc ≤ Bm)
    (hmG : Bm + LC * bc ≤ Gb) (hGB : Gb + GLC * mc ≤ B)
    (hbps : 0 < bps) (hssc : ssc = bc / bps + 1) (hcover : bc * bs ≤ shape.bpCode.length)
    (hM1 : 1 ≤ M) (hmc : mc = bc / M + 1) (hLC1 : 1 ≤ LC) (hGLC1 : 1 ≤ GLC)
    (hLCW : LC < W) (hGLCW : GLC < W) (hldom : 2 ≤ ldom) (hgdom : 2 ≤ gdom)
    (hextW : s.extent < 2 ^ W) (hBcap : B + 4 * shape.bpCode.length + 4 < 2 ^ W)
    (hbsW : bs + 1 < 2 ^ W) (hbcW : bc + 2 < 2 ^ W) (hspan : shape.bpCode.length + bps * bs < 2 ^ W)
    (hswW : sw < 2 ^ W) (hrwW : rw < 2 ^ W) (hBAWW : BAW < 2 ^ W)
    (hmemoL : Bm + LC * bc + (bc + 2 ^ LC) * 1 < 2 ^ W)
    (hmemoG : Gb + GLC * mc + (mc + 2 ^ GLC) * M < 2 ^ W)
    (hlocE : mc * (LC * M) + LC * M + (mc + 1) * M + 2 ^ LC < 2 ^ W)
    (hlvl : ldom * (Nat.log2 ldom + 1) < 2 ^ W ∧ gdom * (Nat.log2 gdom + 1) < 2 ^ W ∧
      lwid < 2 ^ W ∧ gwid < 2 ^ W)
    (hcapT : s.extent + ssc * sw + bc * rw + bc * rw + bc * rw + mc * (LC * M) * LC +
      GLC * mc * BAW + ldom * lwid + gdom * gwid < 2 ^ W) :
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
      s'.keys = s.keys := by
  have hlenW : shape.bpCode.length < 2 ^ W := by omega
  obtain ⟨hl1, hl2, hl3, hl4⟩ := hlvl
  have hlog1 : 1 ≤ Nat.log2 ldom := (Nat.le_log2 (by omega)).2 (by simpa using hldom)
  have hlog2 : 1 ≤ Nat.log2 gdom := (Nat.le_log2 (by omega)).2 (by simpa using hgdom)
  have hld2 : ldom * 2 ≤ ldom * (Nat.log2 ldom + 1) := Nat.mul_le_mul_left _ (by omega)
  have hgd2 : gdom * 2 ≤ gdom * (Nat.log2 gdom + 1) := Nat.mul_le_mul_left _ (by omega)
  have hmcG : mc ≤ GLC * mc := Nat.le_mul_of_pos_left mc hGLC1
  have hbcL : bc ≤ LC * bc := Nat.le_mul_of_pos_left bc hLC1
  -- block statistics
  obtain ⟨s1, k1, e1, hk1, hr1, E1, N1, X1, R1, M1a, F1, x1, ks1⟩ :=
    blockStats_spec hW shape s hrun hone A0 A1 A2 A3 B bs bc h115 h116 h117 h118 h119 h56 h32 h38
      hR hBext hBcap hextW hbsW hcover hA01 hA12 hA23 (by omega)
  have f1 : ∀ r, CloseFrame r → s1.regs r = s.regs r := fun r ⟨a, b, c, d, e⟩ =>
    F1 r ⟨⟨by omega, c, by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩ c
  -- local memo
  obtain ⟨s2, k2, e2, hk2, hr2, L2, M2, F2, x2, ks2, kr2⟩ :=
    localMemo_spec hW shape s1 hr1 (by rw [f1 2 (by simp [CloseFrame]), hone]) A1 bs bc Bm LC
      (by rw [f1 116 (by simp [CloseFrame]), h116]) (by rw [f1 32 (by simp [CloseFrame]), h32])
      (by rw [f1 135 (by simp [CloseFrame]), h135]) (by rw [f1 58 (by simp [CloseFrame]), h58])
      hLC1 hLCW hmemoL (by rw [x1]; omega) (by rw [x1]; exact hextW) (by omega) hcover hlenW
      (fun b hb => N1 b hb)
  have f2 : ∀ r, CloseFrame r → s2.regs r = s.regs r := fun r hr => by
    rw [F2 r hr.2.2.1 (by have := hr.2.2.2.2; omega), f1 r hr]
  -- global memo
  obtain ⟨s3, k3, e3, hk3, hr3, G3, M3, F3, x3, ks3, kr3⟩ :=
    globalMemo_spec hW shape s2 hr2 (by rw [f2 2 (by simp [CloseFrame]), hone]) A1 bs bc Gb M mc GLC
      (by rw [f2 116 (by simp [CloseFrame]), h116]) (by rw [f2 32 (by simp [CloseFrame]), h32])
      (by rw [f2 31 (by simp [CloseFrame]), h31]) (by rw [f2 33 (by simp [CloseFrame]), h33])
      (by rw [f2 136 (by simp [CloseFrame]), h136]) (by rw [f2 59 (by simp [CloseFrame]), h59])
      hM1 hmc hGLC1 hGLCW hmemoG (by rw [x2, x1]; omega) (by rw [x2, x1]; exact hextW) (by omega)
      hcover hlenW
      (fun b hb => by rw [M2 _ (Or.inl (by omega))]; exact N1 b hb)
  have f3 : ∀ r, CloseFrame r → s3.regs r = s.regs r := fun r hr => by
    rw [F3 r hr.2.2.1 (by have := hr.2.2.2.2; omega), f2 r hr]
  have mem3 : ∀ a, (a < Bm ∨ Gb ≤ a) → a < Gb ∨ Gb + GLC * mc ≤ a → s3.memory a = s1.memory a :=
    fun a h1 h2 => by rw [M3 a h2, M2 a (by omega)]
  have x3' : s3.extent = s.extent := by rw [x3, x2, x1]
  -- summary tables
  obtain ⟨s4, k4, e4, hk4, hr4, E4, F4, kr4, ks4⟩ :=
    summaryTables_spec hW shape s3 hr3 (by rw [f3 2 (by simp [CloseFrame]), hone])
      (by rw [f3 9 (by simp [CloseFrame]), htwo]) A0 A1 A2 A3 bps bs bc ssc sw rw
      (by rw [f3 115 (by simp [CloseFrame]), h115]) (by rw [f3 116 (by simp [CloseFrame]), h116])
      (by rw [f3 117 (by simp [CloseFrame]), h117]) (by rw [f3 118 (by simp [CloseFrame]), h118])
      (by rw [f3 30 (by simp [CloseFrame]), h30]) (by rw [f3 56 (by simp [CloseFrame]), h56])
      (by rw [f3 32 (by simp [CloseFrame]), h32]) (by rw [f3 57 (by simp [CloseFrame]), h57])
      (by rw [f3 39 (by simp [CloseFrame]), h39]) (by rw [f3 61 (by simp [CloseFrame]), h61])
      hbps hssc hcover hA01 hA12 hA23 (by rw [x3']; omega) hbcW hspan (by rw [x3']; omega)
      hswW hrwW
      (fun b hb => by rw [M3 _ (Or.inl (by omega)), M2 _ (Or.inl (by omega))]; exact E1 b hb)
      (fun b hb => by rw [M3 _ (Or.inl (by omega)), M2 _ (Or.inl (by omega))]; exact N1 b hb)
      (fun b hb => by rw [M3 _ (Or.inl (by omega)), M2 _ (Or.inl (by omega))]; exact X1 b hb)
      (fun b hb => by rw [M3 _ (Or.inl (by omega)), M2 _ (Or.inl (by omega))]; exact R1 b hb)
  have f4 : ∀ r, CloseFrame r → s4.regs r = s.regs r := fun r hr => by
    rw [F4 r ⟨hr.1, hr.2.2.1, by have := hr.2.2.2.1; omega, by have := hr.2.2.2.1; omega,
      by have := hr.2.2.2.1; omega⟩, f3 r hr]
  have x4 : s4.extent = s.extent + ssc * sw + bc * rw + bc * rw + bc * rw := by
    rw [E4.1, x3']
    simp only [List.length_map, List.length_append, tableBits, flatten_bits_length,
      bpSuperblockBaselineEntries_length, bpBlockRelativeMinExcessEntries_length,
      bpBlockRelativeMaxExcessEntries_length, bpBlockArgMinLocalOffsetEntries_length]
    omega
  -- local sparse table
  obtain ⟨s5, k5, e5, hk5, hr5, E5, F5, kr5, ks5⟩ :=
    localSparseTable_spec hW shape s4 hr4 (by rw [f4 2 (by simp [CloseFrame]), hone])
      (by rw [f4 9 (by simp [CloseFrame]), htwo]) bs bc Bm M mc LC
      (by rw [f4 58 (by simp [CloseFrame]), h58]) (by rw [f4 31 (by simp [CloseFrame]), h31])
      (by rw [f4 32 (by simp [CloseFrame]), h32]) (by rw [f4 135 (by simp [CloseFrame]), h135])
      (by rw [f4 62 (by simp [CloseFrame]), h62]) hM1 hLC1 hLCW hlocE (by rw [x4]; omega)
      (by rw [x4]; omega) (by omega)
      (fun l b hl hb => by
        have hb' : b < bc := by have := Nat.two_pow_pos l; omega
        have := row_lt (L := LC) hb' hl
        rw [E4.memory_below (by rw [x3']; omega), M3 _ (Or.inl (by omega))]
        exact L2 l b hl hb)
  have f5 : ∀ r, CloseFrame r → s5.regs r = s.regs r := fun r hr => by
    rw [F5 r (by
      intro h
      rcases h with h | h | h | h | h | h
      · exact hr.2.2.1 h
      all_goals have := hr.2.2.2.2; omega) hr.1, f4 r hr]
  have x5 : s5.extent = s.extent + ssc * sw + bc * rw + bc * rw + bc * rw + mc * (LC * M) * LC := by
    rw [E5.1, x4]
    simp only [List.length_map, tableBits, flatten_bits_length, bpLocalSparseOffsetEntries_length]
  -- global sparse table
  obtain ⟨s6, k6, e6, hk6, hr6, E6, F6, kr6, ks6⟩ :=
    globalSparseTable_spec hW shape s5 hr5 (by rw [f5 2 (by simp [CloseFrame]), hone])
      (by rw [f5 9 (by simp [CloseFrame]), htwo]) bs bc Gb M mc GLC BAW
      (by rw [f5 33 (by simp [CloseFrame]), h33]) (by rw [f5 31 (by simp [CloseFrame]), h31])
      (by rw [f5 32 (by simp [CloseFrame]), h32]) (by rw [f5 136 (by simp [CloseFrame]), h136])
      (by rw [f5 63 (by simp [CloseFrame]), h63]) (by rw [f5 60 (by simp [CloseFrame]), h60])
      hmc (by rw [hmc]; exact Nat.le_add_left 1 _) hM1 hGLCW (by omega) (by omega) hBAWW (by rw [x5]; omega)
      (by rw [x5]; omega)
      (by omega)
      (fun l m hl hm => by
        have hmlt : m < mc := by
          have h1 : (m + 1) * M ≤ bc :=
            Nat.le_trans (Nat.mul_le_mul_right M (by have := Nat.two_pow_pos l; omega)) hm
          have h2 : m + 1 ≤ bc / M := (Nat.le_div_iff_mul_le (by omega)).2 h1
          omega
        have := row_lt (L := GLC) hmlt hl
        rw [E5.memory_below (by rw [x4]; omega),
          E4.memory_below (by rw [x3']; omega)]
        exact G3 l m hl hm)
  have f6 : ∀ r, CloseFrame r → s6.regs r = s.regs r := fun r hr => by
    rw [F6 r (by
      intro h
      rcases h with h | h | h | h | h | h | h
      · exact hr.2.2.1 h
      all_goals have := hr.2.2.2.2; omega) hr.1, f5 r hr]
  have x6 : s6.extent = s.extent + ssc * sw + bc * rw + bc * rw + bc * rw + mc * (LC * M) * LC +
      GLC * mc * BAW := by
    rw [E6.1, x5]
    simp only [List.length_map, tableBits, flatten_bits_length, bpGlobalSparseBlockEntries_length]
  -- level tables
  obtain ⟨s7, k7, e7, hk7, hr7, E7, F7, kr7, ks7⟩ :=
    levelTable_spec hW rLDOM rLWID (by decide) (by decide) (by decide) (by decide) s6 hr6
      (by rw [f6 2 (by simp [CloseFrame]), hone]) (by rw [f6 9 (by simp [CloseFrame]), htwo])
      (by show 2 ≤ s6.regs 34; rw [f6 34 (by simp [CloseFrame]), h34]; exact hldom)
      (by show s6.regs 34 + 1 < 2 ^ W; rw [f6 34 (by simp [CloseFrame]), h34]; omega)
      (by show s6.regs 36 < 2 ^ W; rw [f6 36 (by simp [CloseFrame]), h36]; exact hl3)
      (by show s6.extent + s6.regs 34 * s6.regs 36 < 2 ^ W
          rw [f6 34 (by simp [CloseFrame]), f6 36 (by simp [CloseFrame]), h34, h36, x6]; omega)
      (by show s6.regs 34 * (Nat.log2 (s6.regs 34) + 1) < 2 ^ W
          rw [f6 34 (by simp [CloseFrame]), h34]; exact hl1)
  rw [show ((rLDOM : Operand) : Nat) = 34 from rfl, show ((rLWID : Operand) : Nat) = 36 from rfl,
    f6 34 (by simp [CloseFrame]), f6 36 (by simp [CloseFrame]), h34, h36] at hk7 E7
  have f7 : ∀ r, CloseFrame r → s7.regs r = s.regs r := fun r hr => by
    rw [F7 r (by
      intro h
      rcases h with h | h
      · exact hr.1 ⟨by omega, by omega⟩
      · exact hr.2.1 ⟨by omega, by omega⟩) hr.1, f6 r hr]
  have x7 : s7.extent = s.extent + ssc * sw + bc * rw + bc * rw + bc * rw + mc * (LC * M) * LC +
      GLC * mc * BAW + ldom * lwid := by
    rw [E7.1, x6]
    simp only [List.length_map, flatten_bits_length, bpSparseLevelEntries_length]
  obtain ⟨s8, k8, e8, hk8, hr8, E8, F8, kr8, ks8⟩ :=
    levelTable_spec hW rGDOM rGWID (by decide) (by decide) (by decide) (by decide) s7 hr7
      (by rw [f7 2 (by simp [CloseFrame]), hone]) (by rw [f7 9 (by simp [CloseFrame]), htwo])
      (by show 2 ≤ s7.regs 35; rw [f7 35 (by simp [CloseFrame]), h35]; exact hgdom)
      (by show s7.regs 35 + 1 < 2 ^ W; rw [f7 35 (by simp [CloseFrame]), h35]; omega)
      (by show s7.regs 37 < 2 ^ W; rw [f7 37 (by simp [CloseFrame]), h37]; exact hl4)
      (by show s7.extent + s7.regs 35 * s7.regs 37 < 2 ^ W
          rw [f7 35 (by simp [CloseFrame]), f7 37 (by simp [CloseFrame]), h35, h37, x7]; omega)
      (by show s7.regs 35 * (Nat.log2 (s7.regs 35) + 1) < 2 ^ W
          rw [f7 35 (by simp [CloseFrame]), h35]; exact hl2)
  rw [show ((rGDOM : Operand) : Nat) = 35 from rfl, show ((rGWID : Operand) : Nat) = 37 from rfl,
    f7 35 (by simp [CloseFrame]), f7 37 (by simp [CloseFrame]), h35, h37] at hk8 E8
  refine ⟨s3, s8, k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + k8)))))),
    EvalG.seq e1 (EvalG.seq e2 (EvalG.seq e3 (EvalG.seq e4 (EvalG.seq e5 (EvalG.seq e6
      (EvalG.seq e7 e8)))))), by omega, hr8, x3', ?_, ?_, ?_, by rw [ks8, ks7, ks6, ks5, ks4, ks3, ks2, ks1]⟩
  · intro a ha
    rw [M3 a (by omega), M2 a (by omega), M1a a (by omega)]
  · have := ((((E4.trans E5).trans E6).trans E7).trans E8)
    simp only [List.map_append, List.append_assoc] at this ⊢
    exact this
  · intro r hr
    rw [F8 r (by
      intro h
      rcases h with h | h
      · exact hr.1 ⟨by omega, by omega⟩
      · exact hr.2.1 ⟨by omega, by omega⟩) hr.1, f7 r hr]

/-! ## The canonical close segment -/

theorem two_pow_mwb_le (x : Nat) (hx : 1 ≤ x) :
    2 ^ SuccinctRank.machineWordBits x ≤ 2 * x := by
  have := Nat.log2_self_le (show x ≠ 0 by omega)
  show 2 ^ (Nat.log2 x + 1) ≤ 2 * x
  rw [Nat.pow_succ]; omega

theorem mwb_lt_of_lt {x W : Nat} (hx : 1 ≤ x) (hW : 1 ≤ W) (h : 2 * x < 2 ^ W) :
    SuccinctRank.machineWordBits x < W := by
  show Nat.log2 x + 1 < W
  have h1 : x < 2 ^ (W - 1) := by
    have : 2 ^ W = 2 * 2 ^ (W - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    omega
  have := (Nat.log2_lt (show x ≠ 0 by omega)).2 h1
  omega

theorem mul_lin (a x c d : Nat) : a * (c * x + d) = c * (a * x) + d * a := by
  rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm a d]

theorem mul_lin2 (a x y c e d : Nat) : a * (c * x + e * y + d) = c * (a * x) + e * (a * y) + d * a := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_left_comm, Nat.mul_left_comm a e, Nat.mul_comm a d]

theorem mwb_le_self (x : Nat) : SuccinctRank.machineWordBits x ≤ x + 1 := by
  show Nat.log2 x + 1 ≤ x + 1
  have := Nat.log2_le_self x
  omega

/-- **Close segment.** From a state holding the size-only geometry, the BP cells
of `shape` at `B` and the statistics and memo arrays ordered below them, the
interior close appends exactly the stored interior directory payload, in at most
`1600 * (400000 * (n + 1))` transitions; the work touches only the arrays. -/
theorem closeSegment_spec {W : Nat} (hW : 32 ≤ W) (shape : CartesianShape) (s : State)
    (hrun : s.status = .running) (hgeo : GeoBase shape.size s.regs)
    (hbank : GeoUpTo shape.size 39 s.regs)
    (A0 A1 A2 A3 B Bm Gb : Nat) (h115 : s.regs 115 = A0) (h116 : s.regs 116 = A1)
    (h117 : s.regs 117 = A2) (h118 : s.regs 118 = A3) (h119 : s.regs 119 = B)
    (h135 : s.regs 135 = Bm) (h136 : s.regs 136 = Gb)
    (hR : Region s B shape.bpCode.length (bpCell shape))
    (hBext : B + shape.bpCode.length ≤ s.extent)
    (hA01 : A0 + geoBlocks shape.size + 1 ≤ A1) (hA12 : A1 + geoBlocks shape.size ≤ A2)
    (hA23 : A2 + geoBlocks shape.size ≤ A3) (hA3m : A3 + geoBlocks shape.size ≤ Bm)
    (hmG : Bm + SuccinctRank.machineWordBits (geoMacro shape.size) * geoBlocks shape.size ≤ Gb)
    (hGB : Gb + SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size ≤ B)
    (hcap : s.extent + 16 * (400000 * (shape.size + 1)) < 2 ^ W) :
    ∃ t s' k, SafeEval W interiorCloseBlock s s' k ∧ k ≤ 1600 * (400000 * (shape.size + 1)) ∧
      s'.status = .running ∧ t.extent = s.extent ∧
      (∀ a, (a < A0 ∨
          Gb + SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size ≤ a) →
        t.memory a = s.memory a) ∧
      Emits t s' ((canonicalRelativeRmmInteriorDirectory shape).payload.map SuccinctSpace.bitToNat) ∧
      (∀ r : Nat, CloseFrame r → s'.regs r = s.regs r) ∧ s'.keys = s.keys := by
  obtain ⟨g1, g2, g9, g30, g31, g32, g33, g34, g35, g36, g37⟩ := hgeo
  have b38 : s.regs 38 = shape.bpCode.length := by
    rw [Cartesian.CartesianShape.bpCode_length]; exact hbank 0 (by decide)
  have b39 : s.regs 39 = SuccinctRank.machineWordBits shape.bpCode.length := by
    rw [Cartesian.CartesianShape.bpCode_length]; exact hbank 1 (by decide)
  have b56 : s.regs 56 = 2 * geoBase shape.size := hbank 18 (by decide)
  have b57 : s.regs 57 = geoBlocks shape.size / geoBase shape.size + 1 := hbank 19 (by decide)
  have b58 : s.regs 58 = SuccinctRank.machineWordBits (geoMacro shape.size) := hbank 20 (by decide)
  have b59 : s.regs 59 = SuccinctRank.machineWordBits (geoMacros shape.size) := hbank 21 (by decide)
  have b60 : s.regs 60 = SuccinctRank.machineWordBits (geoBlocks shape.size) := hbank 22 (by decide)
  have b61 : s.regs 61 = 2 * (Nat.log2 (geoBase shape.size) + 1) + 3 := hbank 23 (by decide)
  have b62 : s.regs 62 = geoMacros shape.size *
      (SuccinctRank.machineWordBits (geoMacro shape.size) * geoMacro shape.size) := hbank 24 (by decide)
  have b63 : s.regs 63 = SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size :=
    hbank 25 (by decide)
  -- envelopes
  have hseg := interiorSegments_length_add_two_le shape
  have e0 := hseg _ (List.getElem_mem (show 0 < (interiorSegments shape).length by simp))
  have e1 := hseg _ (List.getElem_mem (show 1 < (interiorSegments shape).length by simp))
  have e4 := hseg _ (List.getElem_mem (show 4 < (interiorSegments shape).length by simp))
  have e5 := hseg _ (List.getElem_mem (show 5 < (interiorSegments shape).length by simp))
  have e6 := hseg _ (List.getElem_mem (show 6 < (interiorSegments shape).length by simp))
  have e7 := hseg _ (List.getElem_mem (show 7 < (interiorSegments shape).length by simp))
  simp only [interiorSegments, List.getElem_cons_zero, List.getElem_cons_succ, tableBits_length,
    bpSuperblockBaselineEntries_length, bpBlockRelativeMinExcessEntries_length,
    bpLocalSparseOffsetEntries_length, bpGlobalSparseBlockEntries_length,
    bpSparseLevelEntries_length] at e0 e1 e4 e5 e6 e7
  have c0 := interiorEntryCounts_le shape
  simp only [bpSuperblockBaselineEntries_length, bpBlockRelativeMinExcessEntries_length,
    bpBlockRelativeMaxExcessEntries_length, bpBlockArgMinLocalOffsetEntries_length,
    bpLocalSparseOffsetEntries_length, bpGlobalSparseBlockEntries_length,
    bpSparseLevelEntries_length] at c0
  obtain ⟨cS, cB, -, -, cL, cG, cLd, cGd⟩ := c0
  have hbcn : geoBlocks shape.size ≤ shape.size := canonicalLayout_blockCount_le shape
  have hmcn : geoMacros shape.size ≤ shape.size + 1 := canonicalLayout_macroSampleCount_le shape
  have hLCbc : SuccinctRank.machineWordBits (geoMacro shape.size) * geoBlocks shape.size ≤
      3 * shape.size := canonicalLayout_levelCount_mul_blockCount_le shape
  have hcov : geoBlocks shape.size * (2 * geoBase shape.size) ≤ shape.bpCode.length :=
    SuccinctClose.canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length shape
  have hlen := Cartesian.CartesianShape.bpCode_length shape
  have e0' : (geoBlocks shape.size / geoBase shape.size + 1) *
      SuccinctRank.machineWordBits shape.bpCode.length + 2 ≤ 400000 * (shape.size + 1) := e0
  have e1' : geoBlocks shape.size * (2 * (Nat.log2 (geoBase shape.size) + 1) + 3) + 2 ≤
      400000 * (shape.size + 1) := e1
  have e4' : geoMacros shape.size * (SuccinctRank.machineWordBits (geoMacro shape.size) *
      geoMacro shape.size) * SuccinctRank.machineWordBits (geoMacro shape.size) + 2 ≤
      400000 * (shape.size + 1) := e4
  have e5' : SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size *
      SuccinctRank.machineWordBits (geoBlocks shape.size) + 2 ≤ 400000 * (shape.size + 1) := e5
  have e6' : bpSparseLevelDomain (geoMacro shape.size) *
      bpSparseLevelWidth (bpSparseLevelDomain (geoMacro shape.size)) + 2 ≤
      400000 * (shape.size + 1) := e6
  have e7' : bpSparseLevelDomain (geoMacros shape.size) *
      bpSparseLevelWidth (bpSparseLevelDomain (geoMacros shape.size)) + 2 ≤
      400000 * (shape.size + 1) := e7
  have cS' : geoBlocks shape.size / geoBase shape.size + 1 ≤ 400000 * (shape.size + 1) := cS
  have cL' : geoMacros shape.size * (SuccinctRank.machineWordBits (geoMacro shape.size) *
      geoMacro shape.size) ≤ 400000 * (shape.size + 1) := cL
  have cG' : SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size ≤
      400000 * (shape.size + 1) := cG
  have cLd' : bpSparseLevelDomain (geoMacro shape.size) ≤ 400000 * (shape.size + 1) := cLd
  have cGd' : bpSparseLevelDomain (geoMacros shape.size) ≤ 400000 * (shape.size + 1) := cGd
  clear e0 e1 e4 e5 e6 e7 cS cB cL cG cLd cGd hseg
  have hbps1 : 1 ≤ geoBase shape.size := Nat.le_add_left 1 _
  have hM : geoMacro shape.size = geoBase shape.size * geoBase shape.size := rfl
  have hM1 : 1 ≤ geoMacro shape.size := Nat.mul_pos hbps1 hbps1
  have hmc : geoMacros shape.size = geoBlocks shape.size / geoMacro shape.size + 1 := rfl
  have hmc1 : 1 ≤ geoMacros shape.size := Nat.le_add_left 1 _
  have hLC1 : 1 ≤ SuccinctRank.machineWordBits (geoMacro shape.size) := SuccinctRank.machineWordBits_pos _
  have hGLC1 : 1 ≤ SuccinctRank.machineWordBits (geoMacros shape.size) :=
    SuccinctRank.machineWordBits_pos _
  have hBAW := mwb_le_self (geoBlocks shape.size)
  have h2LC := two_pow_mwb_le (geoMacro shape.size) hM1
  have h2GLC := two_pow_mwb_le (geoMacros shape.size) hmc1
  have hbpsn : geoBase shape.size ≤ shape.size + 1 := by
    have := Nat.log2_le_self shape.size; show Nat.log2 shape.size + 1 ≤ _; omega
  have hlogb : Nat.log2 (geoBase shape.size) ≤ geoBase shape.size := Nat.log2_le_self _
  have hldom2 : 2 ≤ bpSparseLevelDomain (geoMacro shape.size) := two_le_bpSparseLevelDomain _
  have hgdom2 : 2 ≤ bpSparseLevelDomain (geoMacros shape.size) := two_le_bpSparseLevelDomain _
  have hlw1 : 1 ≤ bpSparseLevelWidth (bpSparseLevelDomain (geoMacro shape.size)) := Nat.le_add_left 1 _
  have hgw1 : 1 ≤ bpSparseLevelWidth (bpSparseLevelDomain (geoMacros shape.size)) := Nat.le_add_left 1 _
  have hllog : Nat.log2 (bpSparseLevelDomain (geoMacro shape.size)) + 1 ≤
      bpSparseLevelWidth (bpSparseLevelDomain (geoMacro shape.size)) := by
    show _ ≤ Nat.log2 (_ * (Nat.log2 _ + 1)) + 1
    have := log2_mono (Nat.le_mul_of_pos_right (bpSparseLevelDomain (geoMacro shape.size))
      (show 0 < Nat.log2 (bpSparseLevelDomain (geoMacro shape.size)) + 1 by omega))
    omega
  have hglog : Nat.log2 (bpSparseLevelDomain (geoMacros shape.size)) + 1 ≤
      bpSparseLevelWidth (bpSparseLevelDomain (geoMacros shape.size)) := by
    show _ ≤ Nat.log2 (_ * (Nat.log2 _ + 1)) + 1
    have := log2_mono (Nat.le_mul_of_pos_right (bpSparseLevelDomain (geoMacros shape.size))
      (show 0 < Nat.log2 (bpSparseLevelDomain (geoMacros shape.size)) + 1 by omega))
    omega
  have hMle : geoMacro shape.size ≤ geoMacros shape.size *
      (SuccinctRank.machineWordBits (geoMacro shape.size) * geoMacro shape.size) :=
    Nat.le_trans (Nat.le_mul_of_pos_left _ hLC1) (Nat.le_mul_of_pos_left _ hmc1)
  have hLCW : SuccinctRank.machineWordBits (geoMacro shape.size) < W :=
    mwb_lt_of_lt hM1 (by omega) (by omega)
  have hGLCW : SuccinctRank.machineWordBits (geoMacros shape.size) < W :=
    mwb_lt_of_lt hmc1 (by omega) (by omega)
  -- the goal in explicit segment form
  rw [interiorPayload_eq_segments]
  simp only [interiorSegments, List.flatten_cons, List.flatten_nil, List.append_nil]
  show ∃ t s' k, SafeEval W interiorCloseBlock s s' k ∧ k ≤ 1600 * (400000 * (shape.size + 1)) ∧
      s'.status = .running ∧ t.extent = s.extent ∧
      (∀ a, (a < A0 ∨
          Gb + SuccinctRank.machineWordBits (geoMacros shape.size) * geoMacros shape.size ≤ a) →
        t.memory a = s.memory a) ∧
      Emits t s' ((tableBits (bpSuperblockBaselineEntries shape (2 * geoBase shape.size)
          (geoBase shape.size) (geoBlocks shape.size / geoBase shape.size + 1))
          (SuccinctRank.machineWordBits shape.bpCode.length) ++
        (tableBits (bpBlockRelativeMinExcessEntries shape (2 * geoBase shape.size)
          (geoBase shape.size) (geoBlocks shape.size)) (2 * (Nat.log2 (geoBase shape.size) + 1) + 3) ++
        (tableBits (bpBlockRelativeMaxExcessEntries shape (2 * geoBase shape.size)
          (geoBase shape.size) (geoBlocks shape.size)) (2 * (Nat.log2 (geoBase shape.size) + 1) + 3) ++
        (tableBits (bpBlockArgMinLocalOffsetEntries shape (2 * geoBase shape.size)
          (geoBlocks shape.size)) (2 * (Nat.log2 (geoBase shape.size) + 1) + 3) ++
        (tableBits (bpLocalSparseOffsetEntries shape (2 * geoBase shape.size) (geoBlocks shape.size)
          (geoMacro shape.size) (geoMacros shape.size)
          (SuccinctRank.machineWordBits (geoMacro shape.size)))
          (SuccinctRank.machineWordBits (geoMacro shape.size)) ++
        (tableBits (bpGlobalSparseBlockEntries shape (2 * geoBase shape.size) (geoBlocks shape.size)
          (geoMacro shape.size) (geoMacros shape.size)
          (SuccinctRank.machineWordBits (geoMacros shape.size)))
          (SuccinctRank.machineWordBits (geoBlocks shape.size)) ++
        (tableBits (bpSparseLevelEntries (bpSparseLevelDomain (geoMacro shape.size)))
          (bpSparseLevelWidth (bpSparseLevelDomain (geoMacro shape.size))) ++
        tableBits (bpSparseLevelEntries (bpSparseLevelDomain (geoMacros shape.size)))
          (bpSparseLevelWidth (bpSparseLevelDomain (geoMacros shape.size)))))))))).map
            SuccinctSpace.bitToNat) ∧
      (∀ r : Nat, CloseFrame r → s'.regs r = s.regs r) ∧ s'.keys = s.keys
  -- name the layout
  generalize bpSparseLevelWidth (bpSparseLevelDomain (geoMacro shape.size)) = lwid at *
  generalize bpSparseLevelWidth (bpSparseLevelDomain (geoMacros shape.size)) = gwid at *
  generalize bpSparseLevelDomain (geoMacro shape.size) = ldom at *
  generalize bpSparseLevelDomain (geoMacros shape.size) = gdom at *
  generalize SuccinctRank.machineWordBits (geoMacro shape.size) = LC at *
  generalize SuccinctRank.machineWordBits (geoMacros shape.size) = GLC at *
  generalize SuccinctRank.machineWordBits (geoBlocks shape.size) = BAW at *
  generalize SuccinctRank.machineWordBits shape.bpCode.length = sw at *
  have hssc1 : 1 ≤ geoBlocks shape.size / geoBase shape.size + 1 := Nat.le_add_left 1 _
  generalize hssc : geoBlocks shape.size / geoBase shape.size + 1 = ssc at *
  generalize Nat.log2 (geoBase shape.size) = lb at *
  generalize geoMacros shape.size = mc at *
  generalize geoMacro shape.size = M at *
  generalize geoBlocks shape.size = bc at *
  generalize geoBase shape.size = bps at *
  generalize hLd : Nat.log2 ldom = Ll at *
  generalize hGd : Nat.log2 gdom = Lg at *
  -- derived bounds
  have B1 : 1 ≤ shape.size + 1 := Nat.le_add_left 1 _
  generalize hBp : 400000 * (shape.size + 1) = Bp at *
  have hBpn : shape.size + 1 ≤ Bp := by omega
  have hLM : M ≤ LC * M := Nat.le_mul_of_pos_left M hLC1
  have hcnt : LC * M ≤ mc * (LC * M) := Nat.le_mul_of_pos_left _ hmc1
  have hmcM : mc * M ≤ mc * (LC * M) := Nat.mul_le_mul_left mc hLM
  have hmc1M : (mc + 1) * M = mc * M + M := Nat.succ_mul mc M
  have hsw : sw ≤ ssc * sw := Nat.le_mul_of_pos_left sw hssc1
  have hLCc : LC ≤ mc * (LC * M) * LC := Nat.le_mul_of_pos_left LC (by omega)
  have hGc1 : 1 ≤ GLC * mc := Nat.mul_pos hGLC1 hmc1
  have hGLCle : GLC ≤ GLC * mc := Nat.le_mul_of_pos_right GLC hmc1
  have hBAWc : BAW ≤ GLC * mc * BAW := Nat.le_mul_of_pos_left BAW hGc1
  have hlw : lwid ≤ ldom * lwid := Nat.le_mul_of_pos_left lwid (by omega)
  have hgw : gwid ≤ gdom * gwid := Nat.le_mul_of_pos_left gwid (by omega)
  have hlL : ldom * (Ll + 1) ≤ ldom * lwid := Nat.mul_le_mul_left ldom hllog
  have hgL : gdom * (Lg + 1) ≤ gdom * gwid := Nat.mul_le_mul_left gdom hglog
  have hbb : bps * (2 * bps) = 2 * M := by rw [hM, Nat.mul_left_comm]
  have hcb : bc * (2 * bps) = 2 * (bc * bps) := Nat.mul_left_comm bc 2 bps
  have hGM : (mc + 2 ^ GLC) * M ≤ 3 * (mc * M) := by
    rw [← Nat.mul_assoc]; exact Nat.mul_le_mul_right M (by omega)
  obtain ⟨t, s', k, e, hk, hr, ht, htm, hem, hfr, hks⟩ :=
    interiorCloseLayout_spec hW shape s hrun g2 g9 A0 A1 A2 A3 B Bm Gb (2 * bps) bps bc ssc sw
      (2 * (lb + 1) + 3) M mc LC GLC BAW ldom lwid gdom gwid h115 h116 h117 h118 h119 h135 h136
      b56 g32 b38 g30 b57 b39 b61 g31 g33 b58 b59 b60 b62 b63 g34 g36 g35 g37 hR hBext
      hA01 hA12 hA23 hA3m hmG hGB hbps1 hssc.symm hcov hM1 hmc hLC1 hGLC1 hLCW hGLCW hldom2 hgdom2
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
      ⟨by rw [hLd]; omega, by rw [hGd]; omega, by omega, by omega⟩ (by omega)
  refine ⟨t, s', k, e, ?_, hr, ht, htm, ?_, hfr, hks⟩
  · rw [hLd, hGd] at hk
    have q1 : bc * ((2 * bps + 1) * 28 + 20) = 56 * (bc * bps) + 48 * bc := by
      rw [show (2 * bps + 1) * 28 + 20 = 56 * bps + 48 by omega, mul_lin]
    have q2 : LC * (26 * bc + 11) = 26 * (LC * bc) + 11 * LC := mul_lin _ _ _ _
    have q3 : mc * (15 * M + 16) = 15 * (mc * M) + 16 * mc := mul_lin _ _ _ _
    have q4 : GLC * (26 * mc + 11) = 26 * (GLC * mc) + 11 * GLC := mul_lin _ _ _ _
    have q5 : ssc * (7 * sw + 10) = 7 * (ssc * sw) + 10 * ssc := mul_lin _ _ _ _
    have q6 : bc * (21 * (2 * (lb + 1) + 3) + 41) = 21 * (bc * (2 * (lb + 1) + 3)) + 41 * bc :=
      mul_lin _ _ _ _
    have q7 : mc * (LC * M) * (21 + 7 * LC + 7) = 7 * (mc * (LC * M) * LC) + 28 * (mc * (LC * M)) := by
      rw [show 21 + 7 * LC + 7 = 7 * LC + 28 by omega, mul_lin]
    have q8 : GLC * mc * (17 + 7 * BAW + 7) = 7 * (GLC * mc * BAW) + 24 * (GLC * mc) := by
      rw [show 17 + 7 * BAW + 7 = 7 * BAW + 24 by omega, mul_lin]
    have q9 : ldom * (5 * Ll + 7 + 7 * lwid + 7) = 5 * (ldom * Ll) + 7 * (ldom * lwid) + 14 * ldom := by
      rw [show 5 * Ll + 7 + 7 * lwid + 7 = 5 * Ll + 7 * lwid + 14 by omega, mul_lin2]
    have q10 : gdom * (5 * Lg + 7 + 7 * gwid + 7) = 5 * (gdom * Lg) + 7 * (gdom * gwid) + 14 * gdom := by
      rw [show 5 * Lg + 7 + 7 * gwid + 7 = 5 * Lg + 7 * gwid + 14 by omega, mul_lin2]
    have r1 : ldom * (Ll + 1) = ldom * Ll + ldom := by rw [Nat.mul_add, Nat.mul_one]
    have r2 : gdom * (Lg + 1) = gdom * Lg + gdom := by rw [Nat.mul_add, Nat.mul_one]
    have hbcb : bc * bps ≤ shape.size := by omega
    omega
  · simp only [List.map_append, List.append_assoc] at hem ⊢
    exact hem

end RMQ.SuccinctFinal.PackedConstruction.Proof
