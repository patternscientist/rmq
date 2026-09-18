import RMQ.Core.WordRAM.Construction.Proof.MetaChain
import RMQ.Core.WordRAM.Construction.Proof.Buffer

/-! # PRE-1 builder proofs: arrays, metadata words and dense words (stage S7)

Outside the builder firewall. `SafeEval.regs_fit` keeps every register below
`2 ^ W` along a safe evaluation. `metaEmit_spec` stores `rOUT := extent` and
appends the 174 metadata words read from the geometry bank, the long count and
the metadata bank (`metaWordRegs_map` identifies them with `metaWords`).
`repack_spec` appends one Horner word per `W0` buffer cells, and
`outputWords_eq_buildMemory` identifies the metadata words followed by the dense
words of the reference buffer with `buildMemory xs`. `outputStage_spec` composes
the metadata bank, the metadata words and the dense words; `arraysBlock_spec`
reserves the access and interior arrays in the layout of the buffer stage.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

/-! ## Registers stay within the width -/

theorem put_lt {f : Nat → Nat} {B d v : Nat} (hf : ∀ r, f r < B) (hv : v < B) :
    ∀ r, put f d v r < B := by
  intro r
  simp only [put]
  split
  · exact hv
  · exact hf r

theorem Action.Safe.regs_fit {W : Nat} (hW : 32 ≤ W) {s : State} {op : Action}
    (h : op.Safe W s) (hs : ∀ r, s.regs r < 2 ^ W) :
    ∀ r, (execPrim op.prim s).regs r < 2 ^ W := by
  have h32 : 2 ^ 32 ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hW
  have h1 : 1 < 2 ^ W := one_lt_two_pow hW
  obtain ⟨_, hat⟩ := h
  cases op with
  | load d a =>
    obtain ⟨ha, v, hv, hvw⟩ := hat
    rw [show (Action.load d a).prim = Prim.load d a from rfl, exec_load s d a ha hv]
    exact put_lt hs hvw
  | constant d v => exact put_lt hs (Nat.lt_of_lt_of_le v.isLt h32)
  | move d src => exact put_lt hs (hs _)
  | arithmetic op d l x => exact put_lt hs hat.1
  | comparison op d l x =>
    have : op.eval (s.regs l) (s.regs x) ≤ 1 := by
      cases op <;> simp only [Comparison.eval] <;> split <;> omega
    exact put_lt hs (by omega)
  | store a v =>
    rw [show (Action.store a v).prim = Prim.store a v from rfl, exec_store s a v hat.1]
    exact hs
  | reserve d =>
    have hat' : s.extent + 1 < 2 ^ W := hat
    exact put_lt hs (by omega)
  | loadKey d a =>
    obtain ⟨k, hk⟩ := hat
    simp only [Action.prim, execPrim, hk, State.next]
    exact hs
  | compareKey d a b =>
    exact put_lt hs (by split <;> omega)

/-- Safe evaluation keeps every register below `2 ^ W`. -/
theorem SafeEval.regs_fit {W : Nat} (hW : 32 ≤ W) {b : Block} {s s' : State} {k : Nat}
    (h : SafeEval W b s s' k) (hs : ∀ r, s.regs r < 2 ^ W) : ∀ r, s'.regs r < 2 ^ W := by
  induction h with
  | stopped => exact hs
  | skip => exact hs
  | action op s hrun hp => exact Action.Safe.regs_fit hW hp hs
  | exit => exact hs
  | seq _ _ iha ihb => exact ihb (iha hs)
  | ifZeroTaken _ _ _ ih => exact ih hs
  | ifZeroFallthrough _ _ _ _ ih => exact ih hs
  | ifZeroFallthroughStopped _ _ _ _ ih => exact ih hs
  | loopExit => exact hs
  | loopStep _ _ _ _ _ ihb ihr => exact ihr (ihb hs)
  | loopStopped _ _ _ _ ih => exact ih hs

/-! ## Emitting registers -/

theorem emitRegs_spec {W : Nat} (hW : 32 ≤ W) : ∀ (rs : List Operand) (s : State),
    s.status = .running → (∀ r ∈ rs, (r : Nat) ≠ 10) → (∀ r, s.regs r < 2 ^ W) →
    s.extent + rs.length < 2 ^ W →
    ∃ s', SafeEval W (emitRegs rs) s s' (2 * rs.length) ∧ s'.status = .running ∧
      Emits s s' (rs.map (fun r : Operand => s.regs r)) ∧ (∀ r : Nat, r ≠ 10 → s'.regs r = s.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys
  | [], s, hrun, _, _, _ => ⟨s, EvalG.skip s hrun, hrun, Emits.refl s, fun _ _ => rfl, rfl, rfl⟩
  | r :: rest, s, hrun, h10, hfit, hext => by
      simp only [List.length_cons] at hext
      obtain ⟨s1, e1, hr1, E1, f1, kr1, k1⟩ :=
        emitBit_spec hW r (h10 r List.mem_cons_self) s hrun (hfit r) (by omega)
      have hfit1 := SafeEval.regs_fit hW e1 hfit
      obtain ⟨s2, e2, hr2, E2, f2, kr2, k2⟩ :=
        emitRegs_spec hW rest s1 hr1 (fun x hx => h10 x (List.mem_cons_of_mem _ hx)) hfit1
          (by rw [E1.1]; simp only [List.length_singleton]; omega)
      have hmap : rest.map (fun x : Operand => s1.regs x) = rest.map (fun x : Operand => s.regs x) :=
        List.map_congr_left (fun x hx => f1 x (h10 x (List.mem_cons_of_mem _ hx)))
      have hk : 2 + 2 * rest.length = 2 * (r :: rest).length := by
        simp only [List.length_cons]; omega
      refine ⟨s2, hk ▸ EvalG.seq e1 e2, hr2, ?_, fun x hx => by rw [f2 x hx, f1 x hx],
        by rw [kr2, kr1], by rw [k2, k1]⟩
      have E := Emits.trans E1 E2
      rw [hmap] at E
      exact E

/-- The first metadata cell: `rOUT := extent`, then the length. -/
theorem metaHead_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hfit : ∀ r, s.regs r < 2 ^ W) (hext : s.extent + 1 < 2 ^ W) :
    ∃ s', SafeEval W (acts [.reserve rOUT, .store rOUT 1]) s s' 2 ∧ s'.status = .running ∧
      Emits s s' [s.regs 1] ∧ s'.regs 3 = s.extent ∧
      (∀ r : Nat, r ≠ 3 → s'.regs r = s.regs r) ∧ s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  let s1 := execPrim (.reserve rOUT) s
  have e1 := exec_reserve s rOUT
  have hlt : s1.regs rOUT < s1.extent := by simp [s1, e1]
  have e2 := exec_store s1 rOUT 1 hlt
  have hsafe : ActsOK (Action.Safe W) [.reserve rOUT, .store rOUT 1] s := by
    refine ⟨safe_reserve hW s rOUT hext, by simp [Action.prim, e1, hrun], ?_⟩
    refine ⟨safe_store hW s1 rOUT 1 hlt (by simp [s1, e1]; exact hfit 1), ?_, trivial⟩
    show (execPrim (.store rOUT 1) s1).status = .running
    rw [e2]; simp [s1, e1, hrun]
  have he := acts_evalG (P := Action.Safe W) _ s hrun hsafe
  have hx : execActs [.reserve rOUT, .store rOUT 1] s = execPrim (.store rOUT 1) s1 := rfl
  rw [hx, e2] at he
  refine ⟨_, he, by simp [s1, e1, hrun], ⟨by simp [s1, e1], fun a => ?_⟩, by simp [s1, e1],
    fun r hr => by simp [s1, e1]; exact put_ne _ _ hr, by simp [s1, e1], by simp [s1, e1]⟩
  simp only [s1, e1, operand_val_3, operand_val_1, put_same]
  by_cases ha : a = s.extent
  · subst ha; simp [put]
  · rw [put_ne _ _ ha, if_neg (by simp; omega)]

set_option maxRecDepth 8000 in
theorem metaWordRegs_ne_ten : ∀ r ∈ metaWordRegs, (r : Nat) ≠ 10 := by
  have h : metaWordRegs.all (fun r => r.val != 10) = true := by decide
  intro r hr
  have := List.all_eq_true.mp h r hr
  simpa using this

set_option maxRecDepth 8000 in
theorem metaWordRegs_length : metaWordRegs.length = 173 := by decide

set_option maxRecDepth 8000 in
/-- The registers of metadata words 1-173 hold the reference words. -/
theorem metaWordRegs_map (n lc c : Nat) (r : Registers) (hb : GeoBase n r) (hg : GeoUpTo n 39 r)
    (h177 : r 177 = lc) (h0 : r 0 = 0) (hm : MetaUpTo n lc c 108 r) :
    r 1 :: metaWordRegs.map (fun x : Operand => r x) = metaWords n lc c := by
  have g0 : r 0 = 0 := h0
  have g30 : r 30 = (packedSummaryBase n) := hb.2.2.2.1
  have g31 : r 31 = ((packedInteriorLayout n).macroSize) := hb.2.2.2.2.1
  have g32 : r 32 = ((packedInteriorLayout n).blockCount) := hb.2.2.2.2.2.1
  have g33 : r 33 = ((packedInteriorLayout n).macroSampleCount) := hb.2.2.2.2.2.2.1
  have g34 : r 34 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize) := hb.2.2.2.2.2.2.2.1
  have g35 : r 35 = (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount) := hb.2.2.2.2.2.2.2.2.1
  have g36 : r 36 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSize)) := hb.2.2.2.2.2.2.2.2.2.1
  have g37 : r 37 = (SuccinctClose.bpSparseLevelWidth (SuccinctClose.bpSparseLevelDomain (packedInteriorLayout n).macroSampleCount)) := hb.2.2.2.2.2.2.2.2.2.2
  have g38 : r 38 = (2 * n) := hg 0 (by decide)
  have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
  have g40 : r 40 = (GenericSelect.superStride (2 * n)) := hg 2 (by decide)
  have g42 : r 42 = (GenericSelect.localStride (2 * n)) := hg 4 (by decide)
  have g43 : r 43 = (GenericSelect.localSlotsPerSuper (2 * n)) := hg 5 (by decide)
  have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
  have g46 : r 46 = (packedLocalSlots n) := hg 8 (by decide)
  have g47 : r 47 = (packedSparseSlots n) := hg 9 (by decide)
  have g48 : r 48 = (packedRankBlockWidth n) := hg 10 (by decide)
  have g49 : r 49 = (packedLocalWidth n) := hg 11 (by decide)
  have g50 : r 50 = (packedLongFlagWordSize n) := hg 12 (by decide)
  have g51 : r 51 = (packedSparseWordSize n) := hg 13 (by decide)
  have g52 : r 52 = (packedRankSuperSlots n) := hg 14 (by decide)
  have g53 : r 53 = (packedRankBlockSlots n) := hg 15 (by decide)
  have g54 : r 54 = (packedLongFlagRankSlots n) := hg 16 (by decide)
  have g55 : r 55 = (packedSparseRankSlots n) := hg 17 (by decide)
  have g56 : r 56 = ((packedInteriorLayout n).blockSize) := hg 18 (by decide)
  have g57 : r 57 = ((packedInteriorLayout n).superSampleCount) := hg 19 (by decide)
  have g58 : r 58 = ((packedInteriorLayout n).offsetWidth) := hg 20 (by decide)
  have g59 : r 59 = ((packedInteriorLayout n).globalLevelCount) := hg 21 (by decide)
  have g60 : r 60 = ((packedInteriorLayout n).blockAddressWidth) := hg 22 (by decide)
  have g61 : r 61 = ((packedInteriorLayout n).relativeWidth) := hg 23 (by decide)
  have g64 : r 64 = (packedFringeChunkBits n) := hg 26 (by decide)
  have g65 : r 65 = (packedReviewerFringeCount n) := hg 27 (by decide)
  have g66 : r 66 = (packedReviewerFringeWidth n) := hg 28 (by decide)
  have g67 : r 67 = (packedReviewerSelectChunkCount n) := hg 29 (by decide)
  have g68 : r 68 = (packedReviewerSelectChunkWidth n) := hg 30 (by decide)
  have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
  have g76 : r 76 = (wordWidth n) := hg 38 (by decide)
  have g177 : r 177 = lc := h177
  have m0 : r 229 = mv_sc n lc c := by simpa only [metaVal_0, Nat.reduceAdd] using hm 0 (by decide)
  have m1 : r 230 = mv_len1 n lc c := by simpa only [metaVal_1, Nat.reduceAdd] using hm 1 (by decide)
  have m2 : r 231 = mv_len2 n lc c := by simpa only [metaVal_2, Nat.reduceAdd] using hm 2 (by decide)
  have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
  have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
  have m5 : r 234 = mv_len11 n lc c := by simpa only [metaVal_5, Nat.reduceAdd] using hm 5 (by decide)
  have m6 : r 235 = mv_lcS n lc c := by simpa only [metaVal_6, Nat.reduceAdd] using hm 6 (by decide)
  have m7 : r 236 = mv_len14 n lc c := by simpa only [metaVal_7, Nat.reduceAdd] using hm 7 (by decide)
  have m8 : r 237 = mv_len15 n lc c := by simpa only [metaVal_8, Nat.reduceAdd] using hm 8 (by decide)
  have m9 : r 238 = mv_len18 n lc c := by simpa only [metaVal_9, Nat.reduceAdd] using hm 9 (by decide)
  have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
  have m28 : r 257 = mv_b2 n lc c := by simpa only [metaVal_28, Nat.reduceAdd] using hm 28 (by decide)
  have m29 : r 258 = mv_b3 n lc c := by simpa only [metaVal_29, Nat.reduceAdd] using hm 29 (by decide)
  have m30 : r 259 = mv_b4 n lc c := by simpa only [metaVal_30, Nat.reduceAdd] using hm 30 (by decide)
  have m31 : r 260 = mv_b5 n lc c := by simpa only [metaVal_31, Nat.reduceAdd] using hm 31 (by decide)
  have m32 : r 261 = mv_b6 n lc c := by simpa only [metaVal_32, Nat.reduceAdd] using hm 32 (by decide)
  have m33 : r 262 = mv_b7 n lc c := by simpa only [metaVal_33, Nat.reduceAdd] using hm 33 (by decide)
  have m34 : r 263 = mv_b8 n lc c := by simpa only [metaVal_34, Nat.reduceAdd] using hm 34 (by decide)
  have m35 : r 264 = mv_b9 n lc c := by simpa only [metaVal_35, Nat.reduceAdd] using hm 35 (by decide)
  have m36 : r 265 = mv_b10 n lc c := by simpa only [metaVal_36, Nat.reduceAdd] using hm 36 (by decide)
  have m37 : r 266 = mv_b11 n lc c := by simpa only [metaVal_37, Nat.reduceAdd] using hm 37 (by decide)
  have m38 : r 267 = mv_b12 n lc c := by simpa only [metaVal_38, Nat.reduceAdd] using hm 38 (by decide)
  have m39 : r 268 = mv_b13 n lc c := by simpa only [metaVal_39, Nat.reduceAdd] using hm 39 (by decide)
  have m40 : r 269 = mv_b14 n lc c := by simpa only [metaVal_40, Nat.reduceAdd] using hm 40 (by decide)
  have m41 : r 270 = mv_b15 n lc c := by simpa only [metaVal_41, Nat.reduceAdd] using hm 41 (by decide)
  have m42 : r 271 = mv_b16 n lc c := by simpa only [metaVal_42, Nat.reduceAdd] using hm 42 (by decide)
  have m43 : r 272 = mv_b17 n lc c := by simpa only [metaVal_43, Nat.reduceAdd] using hm 43 (by decide)
  have m44 : r 273 = mv_b18 n lc c := by simpa only [metaVal_44, Nat.reduceAdd] using hm 44 (by decide)
  have m46 : r 275 = mv_oldCount n lc c := by simpa only [metaVal_46, Nat.reduceAdd] using hm 46 (by decide)
  have m47 : r 276 = mv_oldBits n lc c := by simpa only [metaVal_47, Nat.reduceAdd] using hm 47 (by decide)
  have m49 : r 278 = mv_wc n lc c := by simpa only [metaVal_49, Nat.reduceAdd] using hm 49 (by decide)
  have m53 : r 282 = mv_fbase n lc c := by simpa only [metaVal_53, Nat.reduceAdd] using hm 53 (by decide)
  have m54 : r 283 = mv_sbase n lc c := by simpa only [metaVal_54, Nat.reduceAdd] using hm 54 (by decide)
  have m55 : r 284 = mv_ib0 n lc c := by simpa only [metaVal_55, Nat.reduceAdd] using hm 55 (by decide)
  have m57 : r 286 = mv_cc2n n lc c := by simpa only [metaVal_57, Nat.reduceAdd] using hm 57 (by decide)
  have m58 : r 287 = mv_aliasWc n lc c := by simpa only [metaVal_58, Nat.reduceAdd] using hm 58 (by decide)
  have m60 : r 289 = mv_lfwc n lc c := by simpa only [metaVal_60, Nat.reduceAdd] using hm 60 (by decide)
  have m62 : r 291 = mv_sfwc n lc c := by simpa only [metaVal_62, Nat.reduceAdd] using hm 62 (by decide)
  have m63 : r 292 = mv_fbits n lc c := by simpa only [metaVal_63, Nat.reduceAdd] using hm 63 (by decide)
  have m64 : r 293 = mv_sbits n lc c := by simpa only [metaVal_64, Nat.reduceAdd] using hm 64 (by decide)
  have m77 : r 306 = mv_cd_39 n lc c := by simpa only [metaVal_77, Nat.reduceAdd] using hm 77 (by decide)
  have m78 : r 307 = mv_cd_61 n lc c := by simpa only [metaVal_78, Nat.reduceAdd] using hm 78 (by decide)
  have m79 : r 308 = mv_cd_58 n lc c := by simpa only [metaVal_79, Nat.reduceAdd] using hm 79 (by decide)
  have m80 : r 309 = mv_cd_60 n lc c := by simpa only [metaVal_80, Nat.reduceAdd] using hm 80 (by decide)
  have m81 : r 310 = mv_cd_36 n lc c := by simpa only [metaVal_81, Nat.reduceAdd] using hm 81 (by decide)
  have m82 : r 311 = mv_cd_37 n lc c := by simpa only [metaVal_82, Nat.reduceAdd] using hm 82 (by decide)
  have m83 : r 312 = mv_BW n lc c := by simpa only [metaVal_83, Nat.reduceAdd] using hm 83 (by decide)
  have m84 : r 313 = mv_MR n lc c := by simpa only [metaVal_84, Nat.reduceAdd] using hm 84 (by decide)
  have m85 : r 314 = mv_LT n lc c := by simpa only [metaVal_85, Nat.reduceAdd] using hm 85 (by decide)
  have m86 : r 315 = mv_GT n lc c := by simpa only [metaVal_86, Nat.reduceAdd] using hm 86 (by decide)
  have m87 : r 316 = mv_LL n lc c := by simpa only [metaVal_87, Nat.reduceAdd] using hm 87 (by decide)
  have m88 : r 317 = mv_GL n lc c := by simpa only [metaVal_88, Nat.reduceAdd] using hm 88 (by decide)
  have m89 : r 318 = mv_p2 n lc c := by simpa only [metaVal_89, Nat.reduceAdd] using hm 89 (by decide)
  have m90 : r 319 = mv_p3 n lc c := by simpa only [metaVal_90, Nat.reduceAdd] using hm 90 (by decide)
  have m91 : r 320 = mv_p4 n lc c := by simpa only [metaVal_91, Nat.reduceAdd] using hm 91 (by decide)
  have m92 : r 321 = mv_p5 n lc c := by simpa only [metaVal_92, Nat.reduceAdd] using hm 92 (by decide)
  have m93 : r 322 = mv_p6 n lc c := by simpa only [metaVal_93, Nat.reduceAdd] using hm 93 (by decide)
  have m94 : r 323 = mv_p7 n lc c := by simpa only [metaVal_94, Nat.reduceAdd] using hm 94 (by decide)
  have m95 : r 324 = mv_ptot n lc c := by simpa only [metaVal_95, Nat.reduceAdd] using hm 95 (by decide)
  have m101 : r 330 = mv_ib1 n lc c := by simpa only [metaVal_101, Nat.reduceAdd] using hm 101 (by decide)
  have m102 : r 331 = mv_ib2 n lc c := by simpa only [metaVal_102, Nat.reduceAdd] using hm 102 (by decide)
  have m103 : r 332 = mv_ib3 n lc c := by simpa only [metaVal_103, Nat.reduceAdd] using hm 103 (by decide)
  have m104 : r 333 = mv_ib4 n lc c := by simpa only [metaVal_104, Nat.reduceAdd] using hm 104 (by decide)
  have m105 : r 334 = mv_ib5 n lc c := by simpa only [metaVal_105, Nat.reduceAdd] using hm 105 (by decide)
  have m106 : r 335 = mv_ib6 n lc c := by simpa only [metaVal_106, Nat.reduceAdd] using hm 106 (by decide)
  have m107 : r 336 = mv_ib7 n lc c := by simpa only [metaVal_107, Nat.reduceAdd] using hm 107 (by decide)
  have g1 : r 1 = n := hb.1
  simp only [metaWordRegs, List.map_cons, List.map_nil, operand_val_0, operand_val_30, operand_val_31, operand_val_32, operand_val_33, operand_val_34, operand_val_35, operand_val_36, operand_val_37, operand_val_38, operand_val_39, operand_val_40, operand_val_42, operand_val_43, operand_val_45, operand_val_46, operand_val_47, operand_val_48, operand_val_49, operand_val_50, operand_val_51, operand_val_52, operand_val_53, operand_val_54, operand_val_55, operand_val_56, operand_val_57, operand_val_58, operand_val_59, operand_val_60, operand_val_61, operand_val_64, operand_val_65, operand_val_66, operand_val_67, operand_val_68, operand_val_75, operand_val_76, operand_val_177, operand_val_229, operand_val_230, operand_val_231, operand_val_232, operand_val_233, operand_val_234, operand_val_235, operand_val_236, operand_val_237, operand_val_238, operand_val_256, operand_val_257, operand_val_258, operand_val_259, operand_val_260, operand_val_261, operand_val_262, operand_val_263, operand_val_264, operand_val_265, operand_val_266, operand_val_267, operand_val_268, operand_val_269, operand_val_270, operand_val_271, operand_val_272, operand_val_273, operand_val_275, operand_val_276, operand_val_278, operand_val_282, operand_val_283, operand_val_284, operand_val_286, operand_val_287, operand_val_289, operand_val_291, operand_val_292, operand_val_293, operand_val_306, operand_val_307, operand_val_308, operand_val_309, operand_val_310, operand_val_311, operand_val_312, operand_val_313, operand_val_314, operand_val_315, operand_val_316, operand_val_317, operand_val_318, operand_val_319, operand_val_320, operand_val_321, operand_val_322, operand_val_323, operand_val_324, operand_val_330, operand_val_331, operand_val_332, operand_val_333, operand_val_334, operand_val_335, operand_val_336, g1, g0, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g42, g43, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g64, g65, g66, g67, g68, g75, g76, g177, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m46, m47, m49, m53, m54, m55, m57, m58, m60, m62, m63, m64, m77, m78, m79, m80, m81, m82, m83, m84, m85, m86, m87, m88, m89, m90, m91, m92, m93, m94, m95, m101, m102, m103, m104, m105, m106, m107]
  rfl

set_option maxRecDepth 8000 in
theorem metaWordRegs_ne_three : ∀ r ∈ metaWordRegs, (r : Nat) ≠ 3 := by
  have h : metaWordRegs.all (fun r => r.val != 3) = true := by decide
  intro r hr
  have := List.all_eq_true.mp h r hr
  simpa using this

/-- The metadata words: `rOUT := extent`, then the 174 words. -/
theorem metaEmit_spec {W n lc c : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hfit : ∀ r, s.regs r < 2 ^ W) (hext : s.extent + 174 < 2 ^ W)
    (hb : GeoBase n s.regs) (hg : GeoUpTo n 39 s.regs) (h177 : s.regs 177 = lc) (h0 : s.regs 0 = 0)
    (hm : MetaUpTo n lc c 108 s.regs) :
    ∃ s', SafeEval W metaEmitBlock s s' 348 ∧ s'.status = .running ∧
      Emits s s' (metaWords n lc c) ∧ s'.regs 3 = s.extent ∧
      (∀ r : Nat, r ≠ 3 → r ≠ 10 → s'.regs r = s.regs r) ∧ s'.keyRegs = s.keyRegs ∧
      s'.keys = s.keys := by
  obtain ⟨s1, e1, hr1, E1, h3, f1, kr1, k1⟩ := metaHead_spec hW s hrun hfit (by omega)
  have hfit1 := SafeEval.regs_fit hW e1 hfit
  obtain ⟨s2, e2, hr2, E2, f2, kr2, k2⟩ :=
    emitRegs_spec hW metaWordRegs s1 hr1 metaWordRegs_ne_ten hfit1
      (by rw [E1.1, metaWordRegs_length]; simp only [List.length_singleton]; omega)
  have hmap : metaWordRegs.map (fun x : Operand => s1.regs x) =
      metaWordRegs.map (fun x : Operand => s.regs x) :=
    List.map_congr_left (fun x hx => f1 x (metaWordRegs_ne_three x hx))
  have E := Emits.trans E1 E2
  rw [hmap] at E
  rw [metaWordRegs_length] at e2
  refine ⟨s2, EvalG.seq e1 e2, hr2, ?_, by rw [f2 3 (by decide), h3], ?_, by rw [kr2, kr1],
    by rw [k2, k1]⟩
  · have hw := metaWordRegs_map n lc c s.regs hb hg h177 h0 hm
    rw [← hw]
    exact E
  · intro r h3' h10
    rw [f2 r h10, f1 r h3']

/-! ## Dense words -/

/-- Little-endian value of the `len` cells `f lo, ..., f (lo + len - 1)`. -/
def cellsLE (f : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | lo, len + 1 => f lo + 2 * cellsLE f (lo + 1) len

theorem cellsLE_lt (f : Nat → Nat) : ∀ (lo len : Nat), (∀ i, i < len → f (lo + i) ≤ 1) →
    cellsLE f lo len < 2 ^ len
  | _, 0, _ => by simp [cellsLE]
  | lo, len + 1, hf => by
      have h1 := cellsLE_lt f (lo + 1) len (fun i hi => by
        have := hf (i + 1) (by omega)
        rwa [show lo + (i + 1) = lo + 1 + i by omega] at this)
      have h2 := hf 0 (by omega)
      simp only [Nat.add_zero] at h2
      simp only [cellsLE, Nat.pow_succ]
      omega

/-- The dense cells of a bit list are the little-endian cell values. -/
theorem cellsLE_eq_bitsToNatLE : ∀ (l : List Bool) (lo len : Nat), lo + len ≤ l.length →
    cellsLE (fun j => (l.map SuccinctSpace.bitToNat).getD j 0) lo len =
      SuccinctSpace.bitsToNatLE ((l.drop lo).take len)
  | _, _, 0, _ => by simp [cellsLE, SuccinctSpace.bitsToNatLE]
  | l, lo, len + 1, h => by
      have hlo : lo < l.length := by omega
      rw [cellsLE, cellsLE_eq_bitsToNatLE l (lo + 1) len (by omega),
        List.drop_eq_getElem_cons hlo, List.take_succ_cons, SuccinctSpace.bitsToNatLE]
      simp [List.getD, List.getElem?_eq_getElem hlo]

/-- The dense words of the first `k` cells. -/
def hornerWords (f : Nat → Nat) (W0 k : Nat) : List Nat :=
  (List.range k).map fun i => cellsLE f (i * W0) W0

/-- `pre1_finish_simp` extended with the output registers. -/
syntax "pre1_out_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pre1_out_simp [$hs,*]) =>
    `(tactic| pre1_finish_simp [operand_val_277, operand_val_337, operand_val_338, operand_val_339,
      operand_val_340, operand_val_341, operand_val_342, Nat.add_sub_cancel, $hs,*])

/-- **One Horner step.** -/
theorem hornerStep_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (j a acc x : Nat) (hj : u.regs 341 = j + 1) (ha : u.regs 339 = a + 1)
    (hacc : u.regs 340 = acc) (hext : a < u.extent) (hm : u.memory a = some x) (hx : x ≤ 1)
    (hacc2 : acc + acc + x < 2 ^ W) (hjW : j < 2 ^ W) (hextW : u.extent < 2 ^ W) :
    ∃ u', SafeEval W hornerStepBlock u u' 5 ∧ u'.status = .running ∧
      u'.regs 339 = a ∧ u'.regs 340 = acc + acc + x ∧ u'.regs 341 = j ∧
      (∀ r : Nat, ¬ (339 ≤ r ∧ r ≤ 342) → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧
      u'.keyRegs = u.keyRegs := by
  have hW1 : 1 < 2 ^ W := one_lt_two_pow hW
  obtain ⟨v1, p1, r1, m1, x1, k1, kr1⟩ :=
    prefix_pure hW (.arithmetic .sub rRA rRA rONE) u hrun (by pre1_out_simp [ha, hone]; omega)
  have v1r : v1.regs = put u.regs 339 a := by
    rw [r1]; pre1_out_simp [ha, hone]
  obtain ⟨v2, p2, r2, m2, x2, k2, kr2⟩ :=
    prefix_load hW rRB rRA v1 p1.1 (x := x)
      (by rw [v1r, x1]; pre1_out_simp []; exact hext)
      (by rw [v1r, m1]; pre1_out_simp []; exact hm) (by omega)
  have v2r : v2.regs = put (put u.regs 339 a) 342 x := by
    rw [r2, v1r]; rfl
  obtain ⟨v3, p3, r3, m3, x3, k3, kr3⟩ :=
    prefix_pure hW (.arithmetic .add rACC rACC rACC) v2 p2.1 (by
      rw [v2r]; pre1_out_simp [hacc]; omega)
  have v3r : v3.regs = put (put (put u.regs 339 a) 342 x) 340 (acc + acc) := by
    rw [r3, v2r]; pre1_out_simp [hacc]
  obtain ⟨v4, p4, r4, m4, x4, k4, kr4⟩ :=
    prefix_pure hW (.arithmetic .add rACC rACC rRB) v3 p3.1 (by
      rw [v3r]; pre1_out_simp []; omega)
  have v4r : v4.regs = put (put (put u.regs 339 a) 342 x) 340 (acc + acc + x) := by
    rw [r4, v3r]; funext r; pre1_out_simp []; split <;> simp_all
  obtain ⟨v5, p5, r5, m5, x5, k5, kr5⟩ :=
    prefix_pure hW (.arithmetic .sub rRJ rRJ rONE) v4 p4.1 (by
      rw [v4r]; pre1_out_simp [hj, hone]; omega)
  have v5r : v5.regs = put (put (put (put u.regs 339 a) 342 x) 340 (acc + acc + x)) 341 j := by
    rw [r5, v4r]; pre1_out_simp [hj, hone]
  have pall := p1.append (p2.append (p3.append (p4.append p5)))
  refine ⟨v5, pall.close, pall.1, ?_, ?_, ?_, ?_, by rw [m5, m4, m3, m2, m1],
    by rw [x5, x4, x3, x2, x1], by rw [k5, k4, k3, k2, k1], by rw [kr5, kr4, kr3, kr2, kr1]⟩
  · rw [v5r]; simp [put]
  · rw [v5r]; simp [put]
  · rw [v5r]; simp [put]
  · intro r hr
    have h1 : r ≠ 339 := by omega
    have h2 : r ≠ 340 := by omega
    have h3 : r ≠ 341 := by omega
    have h4 : r ≠ 342 := by omega
    rw [v5r]; simp [put, h1, h2, h3, h4]

/-- **Horner loop.** With `L` in register 341, the cursor `base + lo + L` in
register 339 and `0` in register 340, the loop reads the cells from
`base + lo + L - 1` down to `base + lo` and leaves their little-endian value in
register 340. -/
theorem hornerLoop_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (g : Nat → Nat) (base lo L : Nat)
    (hj : u.regs 341 = L) (ha : u.regs 339 = base + lo + L) (hacc : u.regs 340 = 0)
    (hLW : L ≤ W) (hcells : ∀ i, i < L → u.memory (base + lo + i) = some (g (lo + i)))
    (hg : ∀ i, i < L → g (lo + i) ≤ 1) (hext : base + lo + L ≤ u.extent)
    (hextW : u.extent < 2 ^ W) :
    ∃ u' k, SafeEval W (.loop rRJ hornerStepBlock) u u' k ∧ k ≤ L * 7 + 1 ∧
      u'.status = .running ∧ u'.regs 340 = cellsLE g lo L ∧
      (∀ r : Nat, ¬ (339 ≤ r ∧ r ≤ 342) → u'.regs r = u.regs r) ∧
      u'.memory = u.memory ∧ u'.extent = u.extent ∧ u'.keys = u.keys ∧
      u'.keyRegs = u.keyRegs := by
  have hWlt : W < 2 ^ W := Nat.lt_two_pow_self
  have hLpow : 2 ^ L ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) hLW
  let Q : Nat → State → Prop := fun t v =>
    t ≤ L ∧ v.status = .running ∧ v.regs 341 = t ∧ v.regs 339 = base + lo + t ∧
      v.regs 340 = cellsLE g (lo + t) (L - t) ∧
      (∀ r : Nat, ¬ (339 ≤ r ∧ r ≤ 342) → v.regs r = u.regs r) ∧
      v.memory = u.memory ∧ v.extent = u.extent ∧ v.keys = u.keys ∧ v.keyRegs = u.keyRegs
  have hQ : Q L u := by
    refine ⟨Nat.le_refl _, hrun, hj, ha, ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    rw [hacc, Nat.sub_self]; rfl
  have hloop := EvalG.loop_iterate (P := Action.Safe W) Q rRJ hornerStepBlock 5
    (fun _ _ hv => hv.2.1)
    (fun t v hv => by simp only [operand_val_341]; rw [hv.2.2.1]; omega)
    (fun v hv => by simp only [operand_val_341]; exact hv.2.2.1)
    (fun t v ⟨ht, hvr, hvj, hva, hvacc, hvfr, hvm, hve, hvk, hvkr⟩ => by
      have hv2 : v.regs 2 = 1 := by rw [hvfr 2 (by omega), hone]
      have hlt := cellsLE_lt g (lo + t + 1) (L - (t + 1)) (fun i hi => by
        have := hg (t + 1 + i) (by omega)
        rwa [show lo + (t + 1 + i) = lo + t + 1 + i by omega] at this)
      have hxle : g (lo + t) ≤ 1 := hg t (by omega)
      have hpow : 2 ^ (L - (t + 1)) * 2 ≤ 2 ^ L := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
      have hacc' : v.regs 340 = cellsLE g (lo + (t + 1)) (L - (t + 1)) := hvacc
      rw [show lo + (t + 1) = lo + t + 1 by omega] at hacc'
      obtain ⟨v', e, hv'r, hv'a, hv'acc, hv'j, hv'fr, hv'm, hv'e, hv'k, hv'kr⟩ :=
        hornerStep_spec hW v hvr hv2 t (base + lo + t) (cellsLE g (lo + t + 1) (L - (t + 1)))
          (g (lo + t)) hvj (by rw [hva]; omega) hacc' (by rw [hve]; omega)
          (by rw [hvm]; exact hcells t (by omega)) hxle (by omega) (by omega) (by rw [hve]; exact hextW)
      refine ⟨v', 5, e, Nat.le_refl _, by omega, hv'r, hv'j, hv'a, ?_, ?_, by rw [hv'm, hvm],
        by rw [hv'e, hve], by rw [hv'k, hvk], by rw [hv'kr, hvkr]⟩
      · rw [hv'acc, show L - t = L - (t + 1) + 1 by omega, cellsLE]
        omega
      · intro r hr
        rw [hv'fr r hr, hvfr r hr])
  obtain ⟨u', k, e, hk, ⟨_, hr', _, _, hacc', hfr', hm', he', hk', hkr'⟩⟩ := hloop L u hQ
  refine ⟨u', k, e, by omega, hr', ?_, hfr', hm', he', hk', hkr'⟩
  rw [hacc', Nat.add_zero, Nat.sub_zero]

/-- **One dense word.** -/
theorem repackWord_spec {W : Nat} (hW : 32 ≤ W) (u : State) (hrun : u.status = .running)
    (hone : u.regs 2 = 1) (g : Nat → Nat) (buf W0 i : Nat) (hi : u.regs 337 = i)
    (h76 : u.regs 76 = W0) (h220 : u.regs 220 = buf) (hW01 : 1 ≤ W0) (hW0 : W0 ≤ W)
    (hcells : ∀ j, j < W0 → u.memory (buf + i * W0 + j) = some (g (i * W0 + j)))
    (hg : ∀ j, j < W0 → g (i * W0 + j) ≤ 1) (hext : buf + (i + 1) * W0 ≤ u.extent)
    (hextW : u.extent + 1 < 2 ^ W) :
    ∃ u' k, SafeEval W repackWordBlock u u' k ∧ k ≤ 7 * W0 + 8 ∧ u'.status = .running ∧
      Emits u u' [cellsLE g (i * W0) W0] ∧
      (∀ r : Nat, r ≠ 10 → ¬ (339 ≤ r ∧ r ≤ 342) → u'.regs r = u.regs r) ∧
      u'.keys = u.keys ∧ u'.keyRegs = u.keyRegs := by
  have hsucc : (i + 1) * W0 = i * W0 + W0 := Nat.succ_mul i W0
  have hi1 : i + 1 ≤ (i + 1) * W0 := Nat.le_mul_of_pos_right _ hW01
  obtain ⟨t, p, tr, tm, te, tk, tkr⟩ :=
    prefix_pureList hW [.arithmetic .add rRA rRI rONE, .arithmetic .mul rRA rRA rWW,
      .arithmetic .add rRA rRA rBUF, .constant rACC 0, .move rRJ rWW] u hrun (by
      pre1_out_simp [hi, hone, h76, h220]
      omega)
  have t339 : t.regs 339 = buf + i * W0 + W0 := by
    rw [tr]; pre1_out_simp [hi, hone, h76, h220]; omega
  have t340 : t.regs 340 = 0 := by rw [tr]; pre1_out_simp []
  have t341 : t.regs 341 = W0 := by rw [tr]; pre1_out_simp [h76]
  have tfr : ∀ r : Nat, ¬ (339 ≤ r ∧ r ≤ 341) → t.regs r = u.regs r := by
    intro r hr
    have h1 : r ≠ 339 := by omega
    have h2 : r ≠ 340 := by omega
    have h3 : r ≠ 341 := by omega
    rw [tr]; pre1_out_simp [h1, h2, h3]
  obtain ⟨v, kL, eL, hkL, hvr, hv340, hvfr, hvm, hve, hvk, hvkr⟩ :=
    hornerLoop_spec hW t p.1 (by rw [tfr 2 (by omega), hone]) g buf (i * W0) W0 t341 t339 t340
      hW0 (fun j hj => by rw [tm]; exact hcells j hj) hg (by rw [te]; omega) (by rw [te]; omega)
  have hval : cellsLE g (i * W0) W0 < 2 ^ W :=
    Nat.lt_of_lt_of_le (cellsLE_lt g (i * W0) W0 hg) (Nat.pow_le_pow_right (by decide) hW0)
  obtain ⟨w, eE, hwr, hwE, hwfr, hwkr, hwk⟩ :=
    emitBit_spec hW rACC (by decide) v hvr (by simp only [operand_val_340]; rw [hv340]; exact hval)
      (by rw [hve, te]; exact hextW)
  refine ⟨w, 5 + (kL + 2), EvalG.seq p.close (EvalG.seq eL eE), by omega, hwr, ?_, ?_,
    by rw [hwk, hvk, tk], by rw [hwkr, hvkr, tkr]⟩
  · have hE : Emits u v [] := Emits.of_eq (by rw [hve, te]) (by rw [hvm, tm])
    have h := hE.trans hwE
    simp only [operand_val_340, hv340, List.nil_append] at h
    exact h
  · intro r h10 hr
    rw [hwfr r h10, hvfr r hr, tfr r (by omega)]

/-- **The dense words.** -/
theorem repack_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hone : s.regs 2 = 1) (g : Nat → Nat) (buf W0 N : Nat) (h220 : s.regs 220 = buf)
    (h76 : s.regs 76 = W0) (h277 : s.regs 277 = N) (hW01 : 1 ≤ W0) (hW0 : W0 ≤ W)
    (hcells : ∀ j, j < N * W0 → s.memory (buf + j) = some (g j))
    (hg : ∀ j, j < N * W0 → g j ≤ 1) (hbuf : buf + N * W0 ≤ s.extent)
    (hextW : s.extent + N + 1 < 2 ^ W) :
    ∃ s' k, SafeEval W repackBlock s s' k ∧ k ≤ N * (7 * W0 + 12) + 3 ∧ s'.status = .running ∧
      Emits s s' (hornerWords g W0 N) ∧
      (∀ r : Nat, r ≠ 10 → ¬ (337 ≤ r ∧ r ≤ 342) → s'.regs r = s.regs r) ∧
      s'.keys = s.keys ∧ s'.keyRegs = s.keyRegs := by
  let Inv : Nat → State → Prop := fun k v =>
    Emits s v (hornerWords g W0 k) ∧
      (∀ r : Nat, r ≠ 10 → ¬ (337 ≤ r ∧ r ≤ 342) → v.regs r = s.regs r) ∧
      v.keys = s.keys ∧ v.keyRegs = s.keyRegs
  obtain ⟨s', k, e, hk, hr, ⟨hE, hfr, hks, hkrs⟩, _, _⟩ :=
    forSlots_spec hW rRI rRIGO rDCNT repackWordBlock (7 * W0 + 8) (by decide) (by decide)
      (by decide) (by decide) (by decide) Inv s hrun hone
      (by simp only [operand_val_277]; rw [h277]; omega)
      (fun u _ hur hum hue huk hukr => by
        refine ⟨by simpa [hornerWords] using Emits.of_eq hue hum, fun r _ hr => ?_, huk, hukr⟩
        exact hur r (by simp only [operand_val_337]; omega) (by simp only [operand_val_338]; omega))
      (fun kk u hkk ⟨huE, hufr, huks, hukrs⟩ hur hui hucnt huone => by
        simp only [operand_val_277, operand_val_337] at hkk hui hucnt
        rw [h277] at hkk
        have hkW : (kk + 1) * W0 ≤ N * W0 := Nat.mul_le_mul_right _ (by omega)
        have hsucc : (kk + 1) * W0 = kk * W0 + W0 := Nat.succ_mul kk W0
        have hlen : (hornerWords g W0 kk).length = kk := by simp [hornerWords]
        obtain ⟨u', j, eb, hj, hu'r, hu'E, hu'fr, hu'k, hu'kr⟩ :=
          repackWord_spec hW u hur huone g buf W0 kk hui
            (by rw [hufr 76 (by omega) (by omega), h76])
            (by rw [hufr 220 (by omega) (by omega), h220]) hW01 hW0
            (fun jj hjj => by
              rw [huE.memory_below (by omega), Nat.add_assoc]
              exact hcells _ (by omega))
            (fun jj hjj => hg _ (by omega))
            (by rw [huE.1, hlen]; omega) (by rw [huE.1, hlen]; omega)
        refine ⟨u', j, eb, hj, hu'r, ?_, ?_, ?_, fun v _ hvr hvm hve hvk hvkr => ?_⟩
        · simp only [operand_val_337]; rw [hu'fr 337 (by omega) (by omega), hui]
        · simp only [operand_val_277]; rw [hu'fr 277 (by omega) (by omega), hucnt]
        · rw [hu'fr 2 (by omega) (by omega), huone]
        · refine ⟨?_, fun r h10 hr => ?_, by rw [hvk, hu'k, huks], by rw [hvkr, hu'kr, hukrs]⟩
          · have h := (huE.trans hu'E).congr_right hvm hve
            simpa [hornerWords, List.range_succ] using h
          · rw [hvr r (by simp only [operand_val_337]; omega) (by simp only [operand_val_338]; omega),
              hu'fr r h10 (by omega), hufr r h10 hr])
  simp only [operand_val_277] at hk hE
  rw [h277] at hk hE
  exact ⟨s', k, e, hk, hr, hE, hfr, hks, hkrs⟩

/-! ## The emitted words are the reference memory -/

/-- The dense word count computed by the metadata bank is the reference one. -/
theorem dcount_eq_denseCount (shape : CartesianShape) :
    mv_dcount shape.size (PackedCellProbe.longCount shape)
        (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
          (GenericSelect.localSlotCount shape.bpCode false)) =
      PackedWordRAM.denseCount (PackedWordRAM.wordWidth shape.size)
        (PackedCellProbe.packedReviewerPaddedBits shape) := by
  have hsc := sc_eq_sparseCount shape
  rw [CartesianShape.bpCode_length] at hsc
  unfold PackedWordRAM.denseCount GenericSelect.selectCeilDiv
  rw [PackedCellProbe.packedReviewerPaddedBits_length]
  unfold PackedCellProbe.packedReviewerAllocatedBits
  rw [← hsc, cellCount_eq]
  rfl

/-- **Output words.** The 174 metadata words computed from the long count and the
sparse-exception count, followed by the Horner words of the dense buffer, are
`buildMemory xs`. -/
theorem outputWords_eq_buildMemory (xs : List Int) :
    metaWords xs.length (PackedCellProbe.longCount (shape xs))
        (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
          (GenericSelect.localSlotCount (shape xs).bpCode false)) ++
      hornerWords (fun j => ((PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
          (PackedCellProbe.packedReviewerPaddedBits (shape xs))).map SuccinctSpace.bitToNat).getD j 0)
        (PackedWordRAM.wordWidth xs.length)
        (mv_dcount xs.length (PackedCellProbe.longCount (shape xs))
          (RMQ.Succinct.rankPrefix true (GenericSelect.sparseExceptionFlagBits (shape xs).bpCode false)
            (GenericSelect.localSlotCount (shape xs).bpCode false))) =
      PackedWordRAM.buildMemory xs := by
  have hsize : (shape xs).size = xs.length := Cartesian.shape_size xs
  have hsc := sc_eq_sparseCount (shape xs)
  rw [CartesianShape.bpCode_length, hsize] at hsc
  have hdc := dcount_eq_denseCount (shape xs)
  rw [hsize] at hdc
  rw [hdc, metaWords_eq, hsc]
  show _ = PackedWordRAM.shapeMemory (shape xs)
  unfold PackedWordRAM.shapeMemory PackedWordRAM.repackWords
  rw [PackedCellProbe.packedReviewerMemory_flatten, Spec.metadata_eq_metadataOf, hsize]
  congr 1
  unfold hornerWords PackedWordRAM.denseWords PackedWordRAM.denseCells
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have hW := PackedWordRAM.wordWidth_pos xs.length
  have hlen := PackedWordRAM.densePad_length (PackedWordRAM.wordWidth xs.length)
    (PackedCellProbe.packedReviewerPaddedBits (shape xs)) hW
  have hcov : i * PackedWordRAM.wordWidth xs.length + PackedWordRAM.wordWidth xs.length ≤
      (PackedWordRAM.densePad (PackedWordRAM.wordWidth xs.length)
        (PackedCellProbe.packedReviewerPaddedBits (shape xs))).length := by
    rw [hlen, ← Nat.succ_mul]
    exact Nat.mul_le_mul_right _ hi'
  simp only [Function.comp]
  rw [cellsLE_eq_bitsToNatLE _ _ _ hcov]
  rfl

/-! ## The output phase -/

/-- **Output phase.** From a running state holding the geometry bank, the long
count `lc`, the sparse-exception count `c` and the dense buffer of `N * W0`
0/1 cells at `buf` (with `N` the metadata dense count and `W0` the word width
of `n`), `outputBlock` computes the metadata bank, stores `rOUT := extent`, and
appends the 174 metadata words and the `N` Horner words. -/
theorem outputStage_spec {W n lc c : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hfit : ∀ r, s.regs r < 2 ^ W) (hb : GeoBase n s.regs) (hg : GeoUpTo n 39 s.regs)
    (h177 : s.regs 177 = lc) (h178 : s.regs 178 = c) (h0 : s.regs 0 = 0)
    (g : Nat → Nat) (buf : Nat) (h220 : s.regs 220 = buf)
    (hcells : ∀ j, j < mv_dcount n lc c * PackedWordRAM.wordWidth n → s.memory (buf + j) = some (g j))
    (hbits : ∀ j, j < mv_dcount n lc c * PackedWordRAM.wordWidth n → g j ≤ 1)
    (hbuf : buf + mv_dcount n lc c * PackedWordRAM.wordWidth n ≤ s.extent)
    (hpay : mv_pay n lc c + 2 ≤ 400000 * (n + 1))
    (hcap : s.extent + 32 * (400000 * (n + 1)) < 2 ^ W) (hWW : PackedWordRAM.wordWidth n ≤ W) :
    ∃ s' k, SafeEval W outputBlock s s' k ∧
      k ≤ 1000 + mv_dcount n lc c * (7 * PackedWordRAM.wordWidth n + 12) ∧
      s'.status = .running ∧ s'.regs 3 = s.extent ∧
      Emits s s' (metaWords n lc c ++ hornerWords g (PackedWordRAM.wordWidth n) (mv_dcount n lc c)) ∧
      s'.keys = s.keys := by
  have hcap' : 32 * (400000 * (n + 1)) < 2 ^ W := by omega
  obtain ⟨s1, k1, e1, hk1, hr1, hb1, hm1, hf1, hmem1, he1, hks1, hkr1⟩ :=
    metaChain_spec hW hcap' hpay 108 (Nat.le_refl _) s hrun ⟨hb, hg, h177, h178, h0⟩
  have hfit1 := SafeEval.regs_fit hW e1 hfit
  obtain ⟨hb1', hg1, h1771, h1781, h01⟩ := hb1
  obtain ⟨s2, e2, hr2, E2, h32, f2, kr2, ks2⟩ :=
    metaEmit_spec hW s1 hr1 hfit1 (by rw [he1]; omega) hb1' hg1 h1771 h01 hm1
  have hN : mv_dcount n lc c ≤ 3 * (400000 * (n + 1)) := by
    simpa only [metaVal_48] using metaVal_le n lc c hpay 48 (by decide)
  have hfit2 := SafeEval.regs_fit hW e2 hfit1
  have h277 : s2.regs 277 = mv_dcount n lc c := by
    rw [f2 277 (by decide) (by decide)]
    simpa only [metaVal_48, Nat.reduceAdd] using hm1 48 (by decide)
  have h76 : s2.regs 76 = PackedWordRAM.wordWidth n := by
    rw [f2 76 (by decide) (by decide)]; exact hg1 38 (by decide)
  have h2202 : s2.regs 220 = buf := by
    rw [f2 220 (by decide) (by decide), hf1 220 (by omega), h220]
  have h22 : s2.regs 2 = 1 := by rw [f2 2 (by decide) (by decide)]; exact hb1'.2.1
  have hW0pos := PackedWordRAM.wordWidth_pos n
  have hml : (metaWords n lc c).length = 174 := by rw [metaWords_eq, metadataOf_length]
  obtain ⟨s3, k3, e3, hk3, hr3, E3, f3, ks3, kr3⟩ :=
    repack_spec hW s2 hr2 h22 g buf (PackedWordRAM.wordWidth n) (mv_dcount n lc c) h2202 h76 h277
      hW0pos hWW
      (fun j hj => by rw [E2.memory_below (by rw [he1]; omega), hmem1]; exact hcells j hj)
      hbits (by rw [E2.1, he1]; omega) (by rw [E2.1, he1, hml]; omega)
  refine ⟨s3, k1 + (348 + k3), EvalG.seq e1 (EvalG.seq e2 e3), by omega, hr3, ?_, ?_,
    by rw [ks3, ks2, hks1]⟩
  · rw [f3 3 (by decide) (by omega), h32, he1]
  · have hE1 : Emits s s1 [] := Emits.of_eq he1 hmem1
    have h := (hE1.trans E2).trans E3
    simpa only [List.nil_append] using h

/-! ## The arrays -/

/-- Registers `arraysBlock` writes. -/
def ArraysWritten (r : Nat) : Prop :=
  r = 10 ∨ r = 12 ∨ r = 198 ∨ (159 ≤ r ∧ r ≤ 164) ∨ (115 ≤ r ∧ r ≤ 118) ∨ r = 135 ∨ r = 136

theorem Emits.replicate_congr {s s' : State} {a b : Nat} (h : Emits s s' (List.replicate a 0))
    (hab : a = b) : Emits s s' (List.replicate b 0) := hab ▸ h

/-- One array reservation with its count given by value. -/
theorem arrayStep {W : Nat} (hW : 32 ≤ W) (base cnt : Operand) (hb0 : (base : Nat) ≠ 0)
    (hb2 : (base : Nat) ≠ 2) (hb10 : (base : Nat) ≠ 10) (hb12 : (base : Nat) ≠ 12)
    (hcb : (cnt : Nat) ≠ base) (hw : ArraysWritten base) (s₀ : State)
    (s : State) (hrun : s.status = .running) (hzero : s.regs 0 = 0) (hone : s.regs 2 = 1)
    (N : Nat) (hN : s.regs cnt = N) (hext : s.extent + N + 1 < 2 ^ W)
    (hfr : ∀ r : Nat, ¬ ArraysWritten r → s.regs r = s₀.regs r) :
    ∃ s' k, SafeEval W (reserveArray base cnt) s s' k ∧ k ≤ 5 * N + 4 ∧
      s'.status = .running ∧ Emits s s' (List.replicate (N + 1) 0) ∧ s'.regs base = s.extent ∧
      (∀ r : Nat, r ≠ base → r ≠ 10 → r ≠ 12 → s'.regs r = s.regs r) ∧
      (∀ r : Nat, ¬ ArraysWritten r → s'.regs r = s₀.regs r) ∧
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  obtain ⟨s', k, e, hk, hr, E, hbase, hf, hkr, hks⟩ :=
    reserveArray_spec hW base cnt hb0 hb2 hb10 hb12 hcb s hrun hzero hone (by rw [hN]; exact hext)
  rw [hN] at hk E
  refine ⟨s', k, e, hk, hr, E, hbase, hf, fun r hr' => ?_, hkr, hks⟩
  have h1 : r ≠ base := fun h => hr' (h ▸ hw)
  have h2 : r ≠ 10 := fun h => hr' (Or.inl h)
  have h3 : r ≠ 12 := fun h => hr' (Or.inr (Or.inl h))
  rw [hf r h1 h2 h3, hfr r hr']

/-- **Arrays, abstract counts.** `arraysBlock` appends the arrays of the given
counts and leaves their bases in layout order. -/
theorem arraysBlock_spec {W : Nat} (hW : 32 ≤ W) (s : State) (hrun : s.status = .running)
    (hzero : s.regs 0 = 0) (g2 : s.regs 2 = 1)
    (N1 N2 N3 N4 NB OW GLC MS : Nat) (g1 : s.regs 1 = N1) (g53 : s.regs 53 = N2)
    (g45 : s.regs 45 = N3) (g46 : s.regs 46 = N4) (g32 : s.regs 32 = NB) (g58 : s.regs 58 = OW)
    (g59 : s.regs 59 = GLC) (g33 : s.regs 33 = MS)
    (hcap : s.extent + (N1 + 1) + (N2 + 1) + 2 * (N3 + 1) + 2 * (N4 + 1) + 4 * (NB + 1) +
      (OW * NB + 1) + (GLC * MS + 1) + OW * NB + GLC * MS + 1 < 2 ^ W) :
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
      s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys := by
  generalize hPQ : OW * NB = PQ at hcap ⊢
  generalize hGM : GLC * MS = GM at hcap ⊢
  have nw0 : ¬ ArraysWritten 0 := by unfold ArraysWritten; decide
  have nw2 : ¬ ArraysWritten 2 := by unfold ArraysWritten; decide
  have nw : ∀ x, x = 1 ∨ x = 53 ∨ x = 45 ∨ x = 46 ∨ x = 32 ∨ x = 33 ∨ x = 58 ∨ x = 59 →
      ¬ ArraysWritten x := by intro x hx; unfold ArraysWritten; omega
  -- 159
  obtain ⟨t1, k1, e1, hk1, r1, E1, b1, f1, F1, kr1, ks1⟩ :=
    arrayStep hW rPOSB rN (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s s hrun hzero g2 N1 g1 (by omega) (fun _ _ => rfl)
  have x1 := E1.1; simp only [List.length_replicate] at x1
  -- 160
  obtain ⟨t2, k2, e2, hk2, r2, E2, b2, f2, F2, kr2, ks2⟩ :=
    arrayStep hW rRWB rRBLK (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t1 r1 (by rw [F1 0 nw0, hzero]) (by rw [F1 2 nw2, g2])
      _ (by simp only [operand_val_53]; rw [F1 53 (nw 53 (by decide)), g53]) (by omega) F1
  have x2 := E2.1; simp only [List.length_replicate] at x2
  -- 161
  obtain ⟨t3, k3, e3, hk3, r3, E3, b3, f3, F3, kr3, ks3⟩ :=
    arrayStep hW rLFB rSUP (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t2 r2 (by rw [F2 0 nw0, hzero]) (by rw [F2 2 nw2, g2])
      _ (by simp only [operand_val_45]; rw [F2 45 (nw 45 (by decide)), g45]) (by omega) F2
  have x3 := E3.1; simp only [List.length_replicate] at x3
  -- 162
  obtain ⟨t4, k4, e4, hk4, r4, E4, b4, f4, F4, kr4, ks4⟩ :=
    arrayStep hW rLFCB rSUP (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t3 r3 (by rw [F3 0 nw0, hzero]) (by rw [F3 2 nw2, g2])
      _ (by simp only [operand_val_45]; rw [F3 45 (nw 45 (by decide)), g45]) (by omega) F3
  have x4 := E4.1; simp only [List.length_replicate] at x4
  -- 163
  obtain ⟨t5, k5, e5, hk5, r5, E5, b5, f5, F5, kr5, ks5⟩ :=
    arrayStep hW rSFB rLOC (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t4 r4 (by rw [F4 0 nw0, hzero]) (by rw [F4 2 nw2, g2])
      _ (by simp only [operand_val_46]; rw [F4 46 (nw 46 (by decide)), g46]) (by omega) F4
  have x5 := E5.1; simp only [List.length_replicate] at x5
  -- 164
  obtain ⟨t6, k6, e6, hk6, r6, E6, b6, f6, F6, kr6, ks6⟩ :=
    arrayStep hW rSFCB rLOC (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t5 r5 (by rw [F5 0 nw0, hzero]) (by rw [F5 2 nw2, g2])
      _ (by simp only [operand_val_46]; rw [F5 46 (nw 46 (by decide)), g46]) (by omega) F5
  have x6 := E6.1; simp only [List.length_replicate] at x6
  -- 115
  obtain ⟨t7, k7, e7, hk7, r7, E7, b7, f7, F7, kr7, ks7⟩ :=
    arrayStep hW rESB rBLOCKS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t6 r6 (by rw [F6 0 nw0, hzero]) (by rw [F6 2 nw2, g2])
      _ (by simp only [operand_val_32]; rw [F6 32 (nw 32 (by decide)), g32]) (by omega) F6
  have x7 := E7.1; simp only [List.length_replicate] at x7
  -- 116
  obtain ⟨t8, k8, e8, hk8, r8, E8, b8, f8, F8, kr8, ks8⟩ :=
    arrayStep hW rMINB rBLOCKS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t7 r7 (by rw [F7 0 nw0, hzero]) (by rw [F7 2 nw2, g2])
      _ (by simp only [operand_val_32]; rw [F7 32 (nw 32 (by decide)), g32]) (by omega) F7
  have x8 := E8.1; simp only [List.length_replicate] at x8
  -- 117
  obtain ⟨t9, k9, e9, hk9, r9, E9, b9, f9, F9, kr9, ks9⟩ :=
    arrayStep hW rMAXB rBLOCKS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t8 r8 (by rw [F8 0 nw0, hzero]) (by rw [F8 2 nw2, g2])
      _ (by simp only [operand_val_32]; rw [F8 32 (nw 32 (by decide)), g32]) (by omega) F8
  have x9 := E9.1; simp only [List.length_replicate] at x9
  -- 118
  obtain ⟨t10, k10, e10, hk10, r10, E10, b10, f10, F10, kr10, ks10⟩ :=
    arrayStep hW rARGB rBLOCKS (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s t9 r9 (by rw [F9 0 nw0, hzero]) (by rw [F9 2 nw2, g2])
      _ (by simp only [operand_val_32]; rw [F9 32 (nw 32 (by decide)), g32]) (by omega) F9
  have x10 := E10.1; simp only [List.length_replicate] at x10
  -- 198 := offsetWidth * blockCount
  obtain ⟨u1, j1, d1, hj1, q1, R1, M1, X1, K1, KR1⟩ :=
    RegSpec.pure hW [.arithmetic .mul rASZ rOW rBLOCKS] t10 r10 (by
      simp only [pureOKs, pureOK, Arithmetic.eval, operand_val_58, operand_val_32, reduceCtorEq,
        false_implies, false_or, and_true]
      rw [F10 58 (nw 58 (by decide)), F10 32 (nw 32 (by decide)), g58, g32, hPQ]
      omega)
  have u1v : u1.regs 198 = PQ := by
    rw [R1]
    simp only [pureRegs, pureReg, Arithmetic.eval, operand_val_198, operand_val_58, operand_val_32,
      put_same]
    rw [F10 58 (nw 58 (by decide)), F10 32 (nw 32 (by decide)), g58, g32, hPQ]
  have u1fr : ∀ r : Nat, r ≠ 198 → u1.regs r = t10.regs r := by
    intro r hr; rw [R1]; simp only [pureRegs, pureReg, operand_val_198]; exact put_ne _ _ hr
  have U1 : ∀ r : Nat, ¬ ArraysWritten r → u1.regs r = s.regs r := fun r hr => by
    rw [u1fr r (fun h => hr (Or.inr (Or.inr (Or.inl h)))), F10 r hr]
  -- 135
  obtain ⟨t11, k11, e11, hk11, r11, E11, b11, f11, F11, kr11, ks11⟩ :=
    arrayStep hW rAMB rASZ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s u1 q1 (by rw [U1 0 nw0, hzero]) (by rw [U1 2 nw2, g2])
      _ (by simp only [operand_val_198]; exact u1v) (by rw [X1]; omega) U1
  have x11 := E11.1; simp only [List.length_replicate] at x11
  -- 198 := globalLevelCount * macroSampleCount
  obtain ⟨u2, j2, d2, hj2, q2, R2, M2, X2, K2, KR2⟩ :=
    RegSpec.pure hW [.arithmetic .mul rASZ rGLC rMACROS] t11 r11 (by
      simp only [pureOKs, pureOK, Arithmetic.eval, operand_val_59, operand_val_33, reduceCtorEq,
        false_implies, false_or, and_true]
      rw [F11 59 (nw 59 (by decide)), F11 33 (nw 33 (by decide)), g59, g33, hGM]
      omega)
  have u2v : u2.regs 198 = GM := by
    rw [R2]
    simp only [pureRegs, pureReg, Arithmetic.eval, operand_val_198, operand_val_59, operand_val_33,
      put_same]
    rw [F11 59 (nw 59 (by decide)), F11 33 (nw 33 (by decide)), g59, g33, hGM]
  have u2fr : ∀ r : Nat, r ≠ 198 → u2.regs r = t11.regs r := by
    intro r hr; rw [R2]; simp only [pureRegs, pureReg, operand_val_198]; exact put_ne _ _ hr
  have U2 : ∀ r : Nat, ¬ ArraysWritten r → u2.regs r = s.regs r := fun r hr => by
    rw [u2fr r (fun h => hr (Or.inr (Or.inr (Or.inl h)))), F11 r hr]
  -- 136
  obtain ⟨t12, k12, e12, hk12, r12, E12, b12, f12, F12, kr12, ks12⟩ :=
    arrayStep hW rGMB rASZ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by unfold ArraysWritten; decide) s u2 q2 (by rw [U2 0 nw0, hzero]) (by rw [U2 2 nw2, g2])
      _ (by simp only [operand_val_198]; exact u2v) (by rw [X2, x11, X1]; omega) U2
  have x12 := E12.1; simp only [List.length_replicate] at x12
  -- assemble
  have EU1 : Emits t10 u1 [] := Emits.of_eq X1 M1
  have EU2 : Emits t11 u2 [] := Emits.of_eq X2 M2
  have Eall := E1.trans (E2.trans (E3.trans (E4.trans (E5.trans (E6.trans (E7.trans (E8.trans
    (E9.trans (E10.trans (EU1.trans (E11.trans (EU2.trans E12))))))))))))
  simp only [List.nil_append, List.replicate_append_replicate] at Eall
  have Eall' := Emits.replicate_congr Eall (b := (N1 + 1) + (N2 + 1) + 2 * (N3 + 1) +
    2 * (N4 + 1) + 4 * (NB + 1) + (PQ + 1) + (GM + 1)) (by omega)
  have ev := EvalG.seq e1 (EvalG.seq e2 (EvalG.seq e3 (EvalG.seq e4 (EvalG.seq e5 (EvalG.seq e6
    (EvalG.seq e7 (EvalG.seq e8 (EvalG.seq e9 (EvalG.seq e10 (EvalG.seq d1 (EvalG.seq e11
    (EvalG.seq d2 e12))))))))))))
  have p1 : t12.regs 159 = s.extent := by
    rw [f12 159 (by decide) (by decide) (by decide), u2fr 159 (by decide),
      f11 159 (by decide) (by decide) (by decide), u1fr 159 (by decide),
      f10 159 (by decide) (by decide) (by decide), f9 159 (by decide) (by decide) (by decide),
      f8 159 (by decide) (by decide) (by decide), f7 159 (by decide) (by decide) (by decide),
      f6 159 (by decide) (by decide) (by decide), f5 159 (by decide) (by decide) (by decide),
      f4 159 (by decide) (by decide) (by decide), f3 159 (by decide) (by decide) (by decide),
      f2 159 (by decide) (by decide) (by decide)]
    exact b1
  have p2 : t12.regs 160 = t1.extent := by
    rw [f12 160 (by decide) (by decide) (by decide), u2fr 160 (by decide),
      f11 160 (by decide) (by decide) (by decide), u1fr 160 (by decide),
      f10 160 (by decide) (by decide) (by decide), f9 160 (by decide) (by decide) (by decide),
      f8 160 (by decide) (by decide) (by decide), f7 160 (by decide) (by decide) (by decide),
      f6 160 (by decide) (by decide) (by decide), f5 160 (by decide) (by decide) (by decide),
      f4 160 (by decide) (by decide) (by decide), f3 160 (by decide) (by decide) (by decide)]
    exact b2
  have p3 : t12.regs 161 = t2.extent := by
    rw [f12 161 (by decide) (by decide) (by decide), u2fr 161 (by decide),
      f11 161 (by decide) (by decide) (by decide), u1fr 161 (by decide),
      f10 161 (by decide) (by decide) (by decide), f9 161 (by decide) (by decide) (by decide),
      f8 161 (by decide) (by decide) (by decide), f7 161 (by decide) (by decide) (by decide),
      f6 161 (by decide) (by decide) (by decide), f5 161 (by decide) (by decide) (by decide),
      f4 161 (by decide) (by decide) (by decide)]
    exact b3
  have p4 : t12.regs 162 = t3.extent := by
    rw [f12 162 (by decide) (by decide) (by decide), u2fr 162 (by decide),
      f11 162 (by decide) (by decide) (by decide), u1fr 162 (by decide),
      f10 162 (by decide) (by decide) (by decide), f9 162 (by decide) (by decide) (by decide),
      f8 162 (by decide) (by decide) (by decide), f7 162 (by decide) (by decide) (by decide),
      f6 162 (by decide) (by decide) (by decide), f5 162 (by decide) (by decide) (by decide)]
    exact b4
  have p5 : t12.regs 163 = t4.extent := by
    rw [f12 163 (by decide) (by decide) (by decide), u2fr 163 (by decide),
      f11 163 (by decide) (by decide) (by decide), u1fr 163 (by decide),
      f10 163 (by decide) (by decide) (by decide), f9 163 (by decide) (by decide) (by decide),
      f8 163 (by decide) (by decide) (by decide), f7 163 (by decide) (by decide) (by decide),
      f6 163 (by decide) (by decide) (by decide)]
    exact b5
  have p6 : t12.regs 164 = t5.extent := by
    rw [f12 164 (by decide) (by decide) (by decide), u2fr 164 (by decide),
      f11 164 (by decide) (by decide) (by decide), u1fr 164 (by decide),
      f10 164 (by decide) (by decide) (by decide), f9 164 (by decide) (by decide) (by decide),
      f8 164 (by decide) (by decide) (by decide), f7 164 (by decide) (by decide) (by decide)]
    exact b6
  have p7 : t12.regs 115 = t6.extent := by
    rw [f12 115 (by decide) (by decide) (by decide), u2fr 115 (by decide),
      f11 115 (by decide) (by decide) (by decide), u1fr 115 (by decide),
      f10 115 (by decide) (by decide) (by decide), f9 115 (by decide) (by decide) (by decide),
      f8 115 (by decide) (by decide) (by decide)]
    exact b7
  have p8 : t12.regs 116 = t7.extent := by
    rw [f12 116 (by decide) (by decide) (by decide), u2fr 116 (by decide),
      f11 116 (by decide) (by decide) (by decide), u1fr 116 (by decide),
      f10 116 (by decide) (by decide) (by decide), f9 116 (by decide) (by decide) (by decide)]
    exact b8
  have p9 : t12.regs 117 = t8.extent := by
    rw [f12 117 (by decide) (by decide) (by decide), u2fr 117 (by decide),
      f11 117 (by decide) (by decide) (by decide), u1fr 117 (by decide),
      f10 117 (by decide) (by decide) (by decide)]
    exact b9
  have p10 : t12.regs 118 = t9.extent := by
    rw [f12 118 (by decide) (by decide) (by decide), u2fr 118 (by decide),
      f11 118 (by decide) (by decide) (by decide), u1fr 118 (by decide)]
    exact b10
  have p11 : t12.regs 135 = u1.extent := by
    rw [f12 135 (by decide) (by decide) (by decide), u2fr 135 (by decide)]
    exact b11
  have p12 : t12.regs 136 = u2.extent := b12
  refine ⟨t12, k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 + (j1 + (k11 +
    (j2 + k12)))))))))))), ev, ?_, r12, Eall', p1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    F12, by rw [kr12, KR2, kr11, KR1, kr10, kr9, kr8, kr7, kr6, kr5, kr4, kr3, kr2, kr1],
    by rw [ks12, K2, ks11, K1, ks10, ks9, ks8, ks7, ks6, ks5, ks4, ks3, ks2, ks1]⟩
  · simp only [List.length_singleton] at hj1 hj2
    omega
  all_goals (simp only [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12] <;> omega)

end RMQ.SuccinctFinal.PackedConstruction.Proof
