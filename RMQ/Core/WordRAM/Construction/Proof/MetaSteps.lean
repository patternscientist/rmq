import RMQ.Core.WordRAM.Construction.Proof.MetaBounds
import RMQ.Core.WordRAM.Construction.Builder.Output

/-! # PRE-1 builder proofs: metadata bank steps 0-53 (stage S7)

Outside the builder firewall. `MetaStepOK W n lc c i b` is the contract of
metadata bank step `i`: from a running state holding the geometry bank, the
long count `lc` in register 177, the sparse-exception count `c` in register 178
and the first `i` metadata registers, the block safely stores
`metaVal n lc c i` into register `229 + i` in at most six transitions and
changes no other register, memory, extent or keys. `metaStep_pure` reduces a
straight-line step to its register function and safety obligations; every
arithmetic result is below `2 ^ W` by `metaVal_le` and the capacity premise
`32 * (400000 * (n + 1)) < 2 ^ W`, every subtraction is guarded and every
divisor is a positive width. Steps 54-107 and the chain are in `MetaChain`.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose
open RMQ.SuccinctFinal.PackedCellProbe RMQ.SuccinctFinal.PackedWordRAM

@[simp] theorem operand_val_229 : ((229 : Operand) : Nat) = 229 := rfl
@[simp] theorem operand_val_230 : ((230 : Operand) : Nat) = 230 := rfl
@[simp] theorem operand_val_231 : ((231 : Operand) : Nat) = 231 := rfl
@[simp] theorem operand_val_232 : ((232 : Operand) : Nat) = 232 := rfl
@[simp] theorem operand_val_233 : ((233 : Operand) : Nat) = 233 := rfl
@[simp] theorem operand_val_234 : ((234 : Operand) : Nat) = 234 := rfl
@[simp] theorem operand_val_235 : ((235 : Operand) : Nat) = 235 := rfl
@[simp] theorem operand_val_236 : ((236 : Operand) : Nat) = 236 := rfl
@[simp] theorem operand_val_237 : ((237 : Operand) : Nat) = 237 := rfl
@[simp] theorem operand_val_238 : ((238 : Operand) : Nat) = 238 := rfl
@[simp] theorem operand_val_239 : ((239 : Operand) : Nat) = 239 := rfl
@[simp] theorem operand_val_240 : ((240 : Operand) : Nat) = 240 := rfl
@[simp] theorem operand_val_241 : ((241 : Operand) : Nat) = 241 := rfl
@[simp] theorem operand_val_242 : ((242 : Operand) : Nat) = 242 := rfl
@[simp] theorem operand_val_243 : ((243 : Operand) : Nat) = 243 := rfl
@[simp] theorem operand_val_244 : ((244 : Operand) : Nat) = 244 := rfl
@[simp] theorem operand_val_245 : ((245 : Operand) : Nat) = 245 := rfl
@[simp] theorem operand_val_246 : ((246 : Operand) : Nat) = 246 := rfl
@[simp] theorem operand_val_247 : ((247 : Operand) : Nat) = 247 := rfl
@[simp] theorem operand_val_248 : ((248 : Operand) : Nat) = 248 := rfl
@[simp] theorem operand_val_249 : ((249 : Operand) : Nat) = 249 := rfl
@[simp] theorem operand_val_250 : ((250 : Operand) : Nat) = 250 := rfl
@[simp] theorem operand_val_251 : ((251 : Operand) : Nat) = 251 := rfl
@[simp] theorem operand_val_252 : ((252 : Operand) : Nat) = 252 := rfl
@[simp] theorem operand_val_253 : ((253 : Operand) : Nat) = 253 := rfl
@[simp] theorem operand_val_254 : ((254 : Operand) : Nat) = 254 := rfl
@[simp] theorem operand_val_255 : ((255 : Operand) : Nat) = 255 := rfl
@[simp] theorem operand_val_256 : ((256 : Operand) : Nat) = 256 := rfl
@[simp] theorem operand_val_257 : ((257 : Operand) : Nat) = 257 := rfl
@[simp] theorem operand_val_258 : ((258 : Operand) : Nat) = 258 := rfl
@[simp] theorem operand_val_259 : ((259 : Operand) : Nat) = 259 := rfl
@[simp] theorem operand_val_260 : ((260 : Operand) : Nat) = 260 := rfl
@[simp] theorem operand_val_261 : ((261 : Operand) : Nat) = 261 := rfl
@[simp] theorem operand_val_262 : ((262 : Operand) : Nat) = 262 := rfl
@[simp] theorem operand_val_263 : ((263 : Operand) : Nat) = 263 := rfl
@[simp] theorem operand_val_264 : ((264 : Operand) : Nat) = 264 := rfl
@[simp] theorem operand_val_265 : ((265 : Operand) : Nat) = 265 := rfl
@[simp] theorem operand_val_266 : ((266 : Operand) : Nat) = 266 := rfl
@[simp] theorem operand_val_267 : ((267 : Operand) : Nat) = 267 := rfl
@[simp] theorem operand_val_268 : ((268 : Operand) : Nat) = 268 := rfl
@[simp] theorem operand_val_269 : ((269 : Operand) : Nat) = 269 := rfl
@[simp] theorem operand_val_270 : ((270 : Operand) : Nat) = 270 := rfl
@[simp] theorem operand_val_271 : ((271 : Operand) : Nat) = 271 := rfl
@[simp] theorem operand_val_272 : ((272 : Operand) : Nat) = 272 := rfl
@[simp] theorem operand_val_273 : ((273 : Operand) : Nat) = 273 := rfl
@[simp] theorem operand_val_274 : ((274 : Operand) : Nat) = 274 := rfl
@[simp] theorem operand_val_275 : ((275 : Operand) : Nat) = 275 := rfl
@[simp] theorem operand_val_276 : ((276 : Operand) : Nat) = 276 := rfl
@[simp] theorem operand_val_277 : ((277 : Operand) : Nat) = 277 := rfl
@[simp] theorem operand_val_278 : ((278 : Operand) : Nat) = 278 := rfl
@[simp] theorem operand_val_279 : ((279 : Operand) : Nat) = 279 := rfl
@[simp] theorem operand_val_280 : ((280 : Operand) : Nat) = 280 := rfl
@[simp] theorem operand_val_281 : ((281 : Operand) : Nat) = 281 := rfl
@[simp] theorem operand_val_282 : ((282 : Operand) : Nat) = 282 := rfl
@[simp] theorem operand_val_283 : ((283 : Operand) : Nat) = 283 := rfl
@[simp] theorem operand_val_284 : ((284 : Operand) : Nat) = 284 := rfl
@[simp] theorem operand_val_285 : ((285 : Operand) : Nat) = 285 := rfl
@[simp] theorem operand_val_286 : ((286 : Operand) : Nat) = 286 := rfl
@[simp] theorem operand_val_287 : ((287 : Operand) : Nat) = 287 := rfl
@[simp] theorem operand_val_288 : ((288 : Operand) : Nat) = 288 := rfl
@[simp] theorem operand_val_289 : ((289 : Operand) : Nat) = 289 := rfl
@[simp] theorem operand_val_290 : ((290 : Operand) : Nat) = 290 := rfl
@[simp] theorem operand_val_291 : ((291 : Operand) : Nat) = 291 := rfl
@[simp] theorem operand_val_292 : ((292 : Operand) : Nat) = 292 := rfl
@[simp] theorem operand_val_293 : ((293 : Operand) : Nat) = 293 := rfl
@[simp] theorem operand_val_294 : ((294 : Operand) : Nat) = 294 := rfl
@[simp] theorem operand_val_295 : ((295 : Operand) : Nat) = 295 := rfl
@[simp] theorem operand_val_296 : ((296 : Operand) : Nat) = 296 := rfl
@[simp] theorem operand_val_297 : ((297 : Operand) : Nat) = 297 := rfl
@[simp] theorem operand_val_298 : ((298 : Operand) : Nat) = 298 := rfl
@[simp] theorem operand_val_299 : ((299 : Operand) : Nat) = 299 := rfl
@[simp] theorem operand_val_300 : ((300 : Operand) : Nat) = 300 := rfl
@[simp] theorem operand_val_301 : ((301 : Operand) : Nat) = 301 := rfl
@[simp] theorem operand_val_302 : ((302 : Operand) : Nat) = 302 := rfl
@[simp] theorem operand_val_303 : ((303 : Operand) : Nat) = 303 := rfl
@[simp] theorem operand_val_304 : ((304 : Operand) : Nat) = 304 := rfl
@[simp] theorem operand_val_305 : ((305 : Operand) : Nat) = 305 := rfl
@[simp] theorem operand_val_306 : ((306 : Operand) : Nat) = 306 := rfl
@[simp] theorem operand_val_307 : ((307 : Operand) : Nat) = 307 := rfl
@[simp] theorem operand_val_308 : ((308 : Operand) : Nat) = 308 := rfl
@[simp] theorem operand_val_309 : ((309 : Operand) : Nat) = 309 := rfl
@[simp] theorem operand_val_310 : ((310 : Operand) : Nat) = 310 := rfl
@[simp] theorem operand_val_311 : ((311 : Operand) : Nat) = 311 := rfl
@[simp] theorem operand_val_312 : ((312 : Operand) : Nat) = 312 := rfl
@[simp] theorem operand_val_313 : ((313 : Operand) : Nat) = 313 := rfl
@[simp] theorem operand_val_314 : ((314 : Operand) : Nat) = 314 := rfl
@[simp] theorem operand_val_315 : ((315 : Operand) : Nat) = 315 := rfl
@[simp] theorem operand_val_316 : ((316 : Operand) : Nat) = 316 := rfl
@[simp] theorem operand_val_317 : ((317 : Operand) : Nat) = 317 := rfl
@[simp] theorem operand_val_318 : ((318 : Operand) : Nat) = 318 := rfl
@[simp] theorem operand_val_319 : ((319 : Operand) : Nat) = 319 := rfl
@[simp] theorem operand_val_320 : ((320 : Operand) : Nat) = 320 := rfl
@[simp] theorem operand_val_321 : ((321 : Operand) : Nat) = 321 := rfl
@[simp] theorem operand_val_322 : ((322 : Operand) : Nat) = 322 := rfl
@[simp] theorem operand_val_323 : ((323 : Operand) : Nat) = 323 := rfl
@[simp] theorem operand_val_324 : ((324 : Operand) : Nat) = 324 := rfl
@[simp] theorem operand_val_325 : ((325 : Operand) : Nat) = 325 := rfl
@[simp] theorem operand_val_326 : ((326 : Operand) : Nat) = 326 := rfl
@[simp] theorem operand_val_327 : ((327 : Operand) : Nat) = 327 := rfl
@[simp] theorem operand_val_328 : ((328 : Operand) : Nat) = 328 := rfl
@[simp] theorem operand_val_329 : ((329 : Operand) : Nat) = 329 := rfl
@[simp] theorem operand_val_330 : ((330 : Operand) : Nat) = 330 := rfl
@[simp] theorem operand_val_331 : ((331 : Operand) : Nat) = 331 := rfl
@[simp] theorem operand_val_332 : ((332 : Operand) : Nat) = 332 := rfl
@[simp] theorem operand_val_333 : ((333 : Operand) : Nat) = 333 := rfl
@[simp] theorem operand_val_334 : ((334 : Operand) : Nat) = 334 := rfl
@[simp] theorem operand_val_335 : ((335 : Operand) : Nat) = 335 := rfl
@[simp] theorem operand_val_336 : ((336 : Operand) : Nat) = 336 := rfl
@[simp] theorem operand_val_337 : ((337 : Operand) : Nat) = 337 := rfl
@[simp] theorem operand_val_338 : ((338 : Operand) : Nat) = 338 := rfl
@[simp] theorem operand_val_339 : ((339 : Operand) : Nat) = 339 := rfl
@[simp] theorem operand_val_340 : ((340 : Operand) : Nat) = 340 := rfl
@[simp] theorem operand_val_341 : ((341 : Operand) : Nat) = 341 := rfl
@[simp] theorem operand_val_342 : ((342 : Operand) : Nat) = 342 := rfl

/-- `(if 0 < x then 1 else 0)` in the reference's indicator form. -/
theorem lt0_eq (x : Nat) : (if 0 < x then 1 else 0) = (if x = 0 then 0 else 1) := by
  split <;> split <;> omega

/-- Evaluate one metadata step at literal registers. -/
syntax "pre1_meta_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pre1_meta_simp [$hs,*]) => do
    let hs' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar,
      `Lean.Parser.Tactic.simpErase, `Lean.Parser.Tactic.simpLemma] "," := ⟨hs.elemsAndSeps⟩
    `(tactic| simp only [pureOKs, pureOK, pureRegs, pureReg, put,
      Arithmetic.eval, Comparison.eval, reduceCtorEq, false_implies, false_or, or_false,
      true_or, or_true, true_implies, and_true, true_and, implies_true, ite_true, ite_false,
      ↓reduceIte, Nat.reduceEqDiff, Nat.reduceAdd, lt0_eq, operand_val_174, operand_val_0, operand_val_2, operand_val_30, operand_val_31, operand_val_32, operand_val_33, operand_val_34, operand_val_35, operand_val_36, operand_val_37, operand_val_38, operand_val_39, operand_val_40, operand_val_41, operand_val_42, operand_val_43, operand_val_44, operand_val_45, operand_val_46, operand_val_47, operand_val_48, operand_val_49, operand_val_50, operand_val_51, operand_val_52, operand_val_53, operand_val_54, operand_val_55, operand_val_56, operand_val_57, operand_val_58, operand_val_59, operand_val_60, operand_val_61, operand_val_62, operand_val_63, operand_val_64, operand_val_65, operand_val_66, operand_val_67, operand_val_68, operand_val_69, operand_val_70, operand_val_71, operand_val_72, operand_val_73, operand_val_74, operand_val_75, operand_val_76, operand_val_177, operand_val_178, operand_val_229, operand_val_230, operand_val_231, operand_val_232, operand_val_233, operand_val_234, operand_val_235, operand_val_236, operand_val_237, operand_val_238, operand_val_239, operand_val_240, operand_val_241, operand_val_242, operand_val_243, operand_val_244, operand_val_245, operand_val_246, operand_val_247, operand_val_248, operand_val_249, operand_val_250, operand_val_251, operand_val_252, operand_val_253, operand_val_254, operand_val_255, operand_val_256, operand_val_257, operand_val_258, operand_val_259, operand_val_260, operand_val_261, operand_val_262, operand_val_263, operand_val_264, operand_val_265, operand_val_266, operand_val_267, operand_val_268, operand_val_269, operand_val_270, operand_val_271, operand_val_272, operand_val_273, operand_val_274, operand_val_275, operand_val_276, operand_val_277, operand_val_278, operand_val_279, operand_val_280, operand_val_281, operand_val_282, operand_val_283, operand_val_284, operand_val_285, operand_val_286, operand_val_287, operand_val_288, operand_val_289, operand_val_290, operand_val_291, operand_val_292, operand_val_293, operand_val_294, operand_val_295, operand_val_296, operand_val_297, operand_val_298, operand_val_299, operand_val_300, operand_val_301, operand_val_302, operand_val_303, operand_val_304, operand_val_305, operand_val_306, operand_val_307, operand_val_308, operand_val_309, operand_val_310, operand_val_311, operand_val_312, operand_val_313, operand_val_314, operand_val_315, operand_val_316, operand_val_317, operand_val_318, operand_val_319, operand_val_320, operand_val_321, operand_val_322, operand_val_323, operand_val_324, operand_val_325, operand_val_326, operand_val_327, operand_val_328, operand_val_329, operand_val_330, operand_val_331, operand_val_332, operand_val_333, operand_val_334, operand_val_335, operand_val_336, operand_val_337, operand_val_338, operand_val_339, operand_val_340, operand_val_341, operand_val_342, $hs',*])

/-- The registers the metadata bank reads besides its own. -/
def MetaBase (n lc c : Nat) (r : Registers) : Prop :=
  GeoBase n r ∧ GeoUpTo n 39 r ∧ r 177 = lc ∧ r 178 = c ∧ r 0 = 0

/-- The first `k` metadata registers hold their reference values. -/
def MetaUpTo (n lc c k : Nat) (r : Registers) : Prop :=
  ∀ i, i < k → r (229 + i) = metaVal n lc c i

/-- Metadata step `i` from a state with the bank and the first `i` metadata registers. -/
def MetaStepOK (W n lc c i : Nat) (b : Block) : Prop :=
  ∀ s : State, s.status = .running → MetaBase n lc c s.regs → MetaUpTo n lc c i s.regs →
    ∃ s' k, SafeEval W b s s' k ∧ k ≤ 6 ∧ s'.status = .running ∧
      s'.regs (229 + i) = metaVal n lc c i ∧
      (∀ x : Nat, x ≠ 229 + i → s'.regs x = s.regs x) ∧
      s'.memory = s.memory ∧ s'.extent = s.extent ∧ s'.keys = s.keys ∧
      s'.keyRegs = s.keyRegs

theorem metaStep_pure {W n lc c i : Nat} (hW : 32 ≤ W) (ops : List Action) (hlen : ops.length ≤ 6)
    (hdst : (ops.filterMap pureDst).all (fun d => d == 229 + i) = true)
    (hpre : ∀ r, MetaBase n lc c r → MetaUpTo n lc c i r → pureOKs W ops r)
    (hval : ∀ r, MetaBase n lc c r → MetaUpTo n lc c i r →
      pureRegs ops r (229 + i) = metaVal n lc c i) :
    MetaStepOK W n lc c i (acts ops) := by
  intro s hrun hb hm
  obtain ⟨s', k, e, hk, hr, hR, hmem, he, hks, hkr⟩ :=
    RegSpec.pure hW ops s hrun (hpre _ hb hm)
  refine ⟨s', k, e, Nat.le_trans hk hlen, hr, by rw [hR]; exact hval _ hb hm, ?_, hmem, he, hks, hkr⟩
  intro x hx
  rw [hR]
  apply pureRegs_frame
  intro a ha hax
  have := scratch_of_all hdst ha hax
  simp at this
  omega

section Steps

variable {W n lc c : Nat} (hW : 32 ≤ W) (hcap : 32 * (400000 * (n + 1)) < 2 ^ W)
  (hpay : mv_pay n lc c + 2 ≤ 400000 * (n + 1))
include hW hcap hpay

theorem metaStep0 : MetaStepOK W n lc c 0 (metaStepBlock 0) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g178 : r 178 = c := h178
    have g42 : r 42 = (GenericSelect.localStride (2 * n)) := hg 4 (by decide)
    have e : mv_sc n lc c = c * (GenericSelect.localStride (2 * n)) := rfl
    have hv0 : mv_sc n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_0] using metaVal_le n lc c hpay 0 (by decide)
    pre1_meta_simp [g178, g42]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g178 : r 178 = c := h178
    have g42 : r 42 = (GenericSelect.localStride (2 * n)) := hg 4 (by decide)
    pre1_meta_simp [g178, g42, metaVal_0]
    rfl

theorem metaStep1 : MetaStepOK W n lc c 1 (metaStepBlock 1) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g52 : r 52 = (packedRankSuperSlots n) := hg 14 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_len1 n lc c = (packedRankSuperSlots n) * (packedRankWordSize n) := rfl
    have hv1 : mv_len1 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_1] using metaVal_le n lc c hpay 1 (by decide)
    pre1_meta_simp [g52, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g52 : r 52 = (packedRankSuperSlots n) := hg 14 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g52, g39, metaVal_1]
    rfl

theorem metaStep2 : MetaStepOK W n lc c 2 (metaStepBlock 2) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g53 : r 53 = (packedRankBlockSlots n) := hg 15 (by decide)
    have g48 : r 48 = (packedRankBlockWidth n) := hg 10 (by decide)
    have e : mv_len2 n lc c = (packedRankBlockSlots n) * (packedRankBlockWidth n) := rfl
    have hv2 : mv_len2 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_2] using metaVal_le n lc c hpay 2 (by decide)
    pre1_meta_simp [g53, g48]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g53 : r 53 = (packedRankBlockSlots n) := hg 15 (by decide)
    have g48 : r 48 = (packedRankBlockWidth n) := hg 10 (by decide)
    pre1_meta_simp [g53, g48, metaVal_2]
    rfl

theorem metaStep3 : MetaStepOK W n lc c 3 (metaStepBlock 3) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_len3 n lc c = (packedSuperSlots n) * (packedRankWordSize n) := rfl
    have hv3 : mv_len3 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_3] using metaVal_le n lc c hpay 3 (by decide)
    pre1_meta_simp [g45, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [g45, g39, metaVal_3]
    rfl

theorem metaStep4 : MetaStepOK W n lc c 4 (metaStepBlock 4) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g46 : r 46 = (packedLocalSlots n) := hg 8 (by decide)
    have g49 : r 49 = (packedLocalWidth n) := hg 11 (by decide)
    have e : mv_len7 n lc c = (packedLocalSlots n) * (packedLocalWidth n) := rfl
    have hv4 : mv_len7 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_4] using metaVal_le n lc c hpay 4 (by decide)
    pre1_meta_simp [g46, g49]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g46 : r 46 = (packedLocalSlots n) := hg 8 (by decide)
    have g49 : r 49 = (packedLocalWidth n) := hg 11 (by decide)
    pre1_meta_simp [g46, g49, metaVal_4]
    rfl

theorem metaStep5 : MetaStepOK W n lc c 5 (metaStepBlock 5) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g54 : r 54 = (packedLongFlagRankSlots n) := hg 16 (by decide)
    have g50 : r 50 = (packedLongFlagWordSize n) := hg 12 (by decide)
    have e : mv_len11 n lc c = (packedLongFlagRankSlots n) * (packedLongFlagWordSize n) := rfl
    have hv5 : mv_len11 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_5] using metaVal_le n lc c hpay 5 (by decide)
    pre1_meta_simp [g54, g50]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g54 : r 54 = (packedLongFlagRankSlots n) := hg 16 (by decide)
    have g50 : r 50 = (packedLongFlagWordSize n) := hg 12 (by decide)
    pre1_meta_simp [g54, g50, metaVal_5]
    rfl

theorem metaStep6 : MetaStepOK W n lc c 6 (metaStepBlock 6) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g177 : r 177 = lc := h177
    have g40 : r 40 = (GenericSelect.superStride (2 * n)) := hg 2 (by decide)
    have e : mv_lcS n lc c = lc * (GenericSelect.superStride (2 * n)) := rfl
    have hv6 : mv_lcS n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_6] using metaVal_le n lc c hpay 6 (by decide)
    pre1_meta_simp [g177, g40]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g177 : r 177 = lc := h177
    have g40 : r 40 = (GenericSelect.superStride (2 * n)) := hg 2 (by decide)
    pre1_meta_simp [g177, g40, metaVal_6]
    rfl

theorem metaStep7 : MetaStepOK W n lc c 7 (metaStepBlock 7) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m6 : r 235 = mv_lcS n lc c := by simpa only [metaVal_6, Nat.reduceAdd] using hm 6 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    have e : mv_len14 n lc c = (mv_lcS n lc c) * (packedRankWordSize n) := rfl
    have hv7 : mv_len14 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_7] using metaVal_le n lc c hpay 7 (by decide)
    pre1_meta_simp [m6, g39]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m6 : r 235 = mv_lcS n lc c := by simpa only [metaVal_6, Nat.reduceAdd] using hm 6 (by decide)
    have g39 : r 39 = (packedRankWordSize n) := hg 1 (by decide)
    pre1_meta_simp [m6, g39, metaVal_7]
    rfl

theorem metaStep8 : MetaStepOK W n lc c 8 (metaStepBlock 8) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g55 : r 55 = (packedSparseRankSlots n) := hg 17 (by decide)
    have g51 : r 51 = (packedSparseWordSize n) := hg 13 (by decide)
    have e : mv_len15 n lc c = (packedSparseRankSlots n) * (packedSparseWordSize n) := rfl
    have hv8 : mv_len15 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_8] using metaVal_le n lc c hpay 8 (by decide)
    pre1_meta_simp [g55, g51]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g55 : r 55 = (packedSparseRankSlots n) := hg 17 (by decide)
    have g51 : r 51 = (packedSparseWordSize n) := hg 13 (by decide)
    pre1_meta_simp [g55, g51, metaVal_8]
    rfl

theorem metaStep9 : MetaStepOK W n lc c 9 (metaStepBlock 9) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m0 : r 229 = mv_sc n lc c := by simpa only [metaVal_0, Nat.reduceAdd] using hm 0 (by decide)
    have g49 : r 49 = (packedLocalWidth n) := hg 11 (by decide)
    have e : mv_len18 n lc c = (mv_sc n lc c) * (packedLocalWidth n) := rfl
    have hv9 : mv_len18 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_9] using metaVal_le n lc c hpay 9 (by decide)
    pre1_meta_simp [m0, g49]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m0 : r 229 = mv_sc n lc c := by simpa only [metaVal_0, Nat.reduceAdd] using hm 0 (by decide)
    have g49 : r 49 = (packedLocalWidth n) := hg 11 (by decide)
    pre1_meta_simp [m0, g49, metaVal_9]
    rfl

theorem metaStep10 : MetaStepOK W n lc c 10 (metaStepBlock 10) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m1 : r 230 = mv_len1 n lc c := by simpa only [metaVal_1, Nat.reduceAdd] using hm 1 (by decide)
    have m2 : r 231 = mv_len2 n lc c := by simpa only [metaVal_2, Nat.reduceAdd] using hm 2 (by decide)
    have e : mv_o3 n lc c = (mv_len1 n lc c) + (mv_len2 n lc c) := rfl
    have hv10 : mv_o3 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_10] using metaVal_le n lc c hpay 10 (by decide)
    pre1_meta_simp [m1, m2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m1 : r 230 = mv_len1 n lc c := by simpa only [metaVal_1, Nat.reduceAdd] using hm 1 (by decide)
    have m2 : r 231 = mv_len2 n lc c := by simpa only [metaVal_2, Nat.reduceAdd] using hm 2 (by decide)
    pre1_meta_simp [m1, m2, metaVal_10]
    rfl

theorem metaStep11 : MetaStepOK W n lc c 11 (metaStepBlock 11) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m10 : r 239 = mv_o3 n lc c := by simpa only [metaVal_10, Nat.reduceAdd] using hm 10 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    have e : mv_o4 n lc c = (mv_o3 n lc c) + (mv_len3 n lc c) := rfl
    have hv11 : mv_o4 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_11] using metaVal_le n lc c hpay 11 (by decide)
    pre1_meta_simp [m10, m3]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m10 : r 239 = mv_o3 n lc c := by simpa only [metaVal_10, Nat.reduceAdd] using hm 10 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    pre1_meta_simp [m10, m3, metaVal_11]
    rfl

theorem metaStep12 : MetaStepOK W n lc c 12 (metaStepBlock 12) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m11 : r 240 = mv_o4 n lc c := by simpa only [metaVal_11, Nat.reduceAdd] using hm 11 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    have e : mv_o5 n lc c = (mv_o4 n lc c) + (mv_len3 n lc c) := rfl
    have hv12 : mv_o5 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_12] using metaVal_le n lc c hpay 12 (by decide)
    pre1_meta_simp [m11, m3]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m11 : r 240 = mv_o4 n lc c := by simpa only [metaVal_11, Nat.reduceAdd] using hm 11 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    pre1_meta_simp [m11, m3, metaVal_12]
    rfl

theorem metaStep13 : MetaStepOK W n lc c 13 (metaStepBlock 13) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m12 : r 241 = mv_o5 n lc c := by simpa only [metaVal_12, Nat.reduceAdd] using hm 12 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    have e : mv_o6 n lc c = (mv_o5 n lc c) + (mv_len3 n lc c) := rfl
    have hv13 : mv_o6 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_13] using metaVal_le n lc c hpay 13 (by decide)
    pre1_meta_simp [m12, m3]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m12 : r 241 = mv_o5 n lc c := by simpa only [metaVal_12, Nat.reduceAdd] using hm 12 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    pre1_meta_simp [m12, m3, metaVal_13]
    rfl

theorem metaStep14 : MetaStepOK W n lc c 14 (metaStepBlock 14) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m13 : r 242 = mv_o6 n lc c := by simpa only [metaVal_13, Nat.reduceAdd] using hm 13 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    have e : mv_o7 n lc c = (mv_o6 n lc c) + (mv_len3 n lc c) := rfl
    have hv14 : mv_o7 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_14] using metaVal_le n lc c hpay 14 (by decide)
    pre1_meta_simp [m13, m3]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m13 : r 242 = mv_o6 n lc c := by simpa only [metaVal_13, Nat.reduceAdd] using hm 13 (by decide)
    have m3 : r 232 = mv_len3 n lc c := by simpa only [metaVal_3, Nat.reduceAdd] using hm 3 (by decide)
    pre1_meta_simp [m13, m3, metaVal_14]
    rfl

theorem metaStep15 : MetaStepOK W n lc c 15 (metaStepBlock 15) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m14 : r 243 = mv_o7 n lc c := by simpa only [metaVal_14, Nat.reduceAdd] using hm 14 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    have e : mv_o8 n lc c = (mv_o7 n lc c) + (mv_len7 n lc c) := rfl
    have hv15 : mv_o8 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_15] using metaVal_le n lc c hpay 15 (by decide)
    pre1_meta_simp [m14, m4]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m14 : r 243 = mv_o7 n lc c := by simpa only [metaVal_14, Nat.reduceAdd] using hm 14 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    pre1_meta_simp [m14, m4, metaVal_15]
    rfl

theorem metaStep16 : MetaStepOK W n lc c 16 (metaStepBlock 16) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m15 : r 244 = mv_o8 n lc c := by simpa only [metaVal_15, Nat.reduceAdd] using hm 15 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    have e : mv_o9 n lc c = (mv_o8 n lc c) + (mv_len7 n lc c) := rfl
    have hv16 : mv_o9 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_16] using metaVal_le n lc c hpay 16 (by decide)
    pre1_meta_simp [m15, m4]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m15 : r 244 = mv_o8 n lc c := by simpa only [metaVal_15, Nat.reduceAdd] using hm 15 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    pre1_meta_simp [m15, m4, metaVal_16]
    rfl

theorem metaStep17 : MetaStepOK W n lc c 17 (metaStepBlock 17) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m16 : r 245 = mv_o9 n lc c := by simpa only [metaVal_16, Nat.reduceAdd] using hm 16 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    have e : mv_o10 n lc c = (mv_o9 n lc c) + (mv_len7 n lc c) := rfl
    have hv17 : mv_o10 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_17] using metaVal_le n lc c hpay 17 (by decide)
    pre1_meta_simp [m16, m4]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m16 : r 245 = mv_o9 n lc c := by simpa only [metaVal_16, Nat.reduceAdd] using hm 16 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    pre1_meta_simp [m16, m4, metaVal_17]
    rfl

theorem metaStep18 : MetaStepOK W n lc c 18 (metaStepBlock 18) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m17 : r 246 = mv_o10 n lc c := by simpa only [metaVal_17, Nat.reduceAdd] using hm 17 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    have e : mv_o11 n lc c = (mv_o10 n lc c) + (mv_len7 n lc c) := rfl
    have hv18 : mv_o11 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_18] using metaVal_le n lc c hpay 18 (by decide)
    pre1_meta_simp [m17, m4]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m17 : r 246 = mv_o10 n lc c := by simpa only [metaVal_17, Nat.reduceAdd] using hm 17 (by decide)
    have m4 : r 233 = mv_len7 n lc c := by simpa only [metaVal_4, Nat.reduceAdd] using hm 4 (by decide)
    pre1_meta_simp [m17, m4, metaVal_18]
    rfl

theorem metaStep19 : MetaStepOK W n lc c 19 (metaStepBlock 19) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m18 : r 247 = mv_o11 n lc c := by simpa only [metaVal_18, Nat.reduceAdd] using hm 18 (by decide)
    have m5 : r 234 = mv_len11 n lc c := by simpa only [metaVal_5, Nat.reduceAdd] using hm 5 (by decide)
    have e : mv_o12 n lc c = (mv_o11 n lc c) + (mv_len11 n lc c) := rfl
    have hv19 : mv_o12 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_19] using metaVal_le n lc c hpay 19 (by decide)
    pre1_meta_simp [m18, m5]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m18 : r 247 = mv_o11 n lc c := by simpa only [metaVal_18, Nat.reduceAdd] using hm 18 (by decide)
    have m5 : r 234 = mv_len11 n lc c := by simpa only [metaVal_5, Nat.reduceAdd] using hm 5 (by decide)
    pre1_meta_simp [m18, m5, metaVal_19]
    rfl

theorem metaStep20 : MetaStepOK W n lc c 20 (metaStepBlock 20) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m19 : r 248 = mv_o12 n lc c := by simpa only [metaVal_19, Nat.reduceAdd] using hm 19 (by decide)
    have m5 : r 234 = mv_len11 n lc c := by simpa only [metaVal_5, Nat.reduceAdd] using hm 5 (by decide)
    have e : mv_o13 n lc c = (mv_o12 n lc c) + (mv_len11 n lc c) := rfl
    have hv20 : mv_o13 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_20] using metaVal_le n lc c hpay 20 (by decide)
    pre1_meta_simp [m19, m5]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m19 : r 248 = mv_o12 n lc c := by simpa only [metaVal_19, Nat.reduceAdd] using hm 19 (by decide)
    have m5 : r 234 = mv_len11 n lc c := by simpa only [metaVal_5, Nat.reduceAdd] using hm 5 (by decide)
    pre1_meta_simp [m19, m5, metaVal_20]
    rfl

theorem metaStep21 : MetaStepOK W n lc c 21 (metaStepBlock 21) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m20 : r 249 = mv_o13 n lc c := by simpa only [metaVal_20, Nat.reduceAdd] using hm 20 (by decide)
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    have e : mv_o14 n lc c = (mv_o13 n lc c) + (packedSuperSlots n) := rfl
    have hv21 : mv_o14 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_21] using metaVal_le n lc c hpay 21 (by decide)
    pre1_meta_simp [m20, g45]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m20 : r 249 = mv_o13 n lc c := by simpa only [metaVal_20, Nat.reduceAdd] using hm 20 (by decide)
    have g45 : r 45 = (packedSuperSlots n) := hg 7 (by decide)
    pre1_meta_simp [m20, g45, metaVal_21]
    rfl

theorem metaStep22 : MetaStepOK W n lc c 22 (metaStepBlock 22) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m21 : r 250 = mv_o14 n lc c := by simpa only [metaVal_21, Nat.reduceAdd] using hm 21 (by decide)
    have m7 : r 236 = mv_len14 n lc c := by simpa only [metaVal_7, Nat.reduceAdd] using hm 7 (by decide)
    have e : mv_o15 n lc c = (mv_o14 n lc c) + (mv_len14 n lc c) := rfl
    have hv22 : mv_o15 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_22] using metaVal_le n lc c hpay 22 (by decide)
    pre1_meta_simp [m21, m7]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m21 : r 250 = mv_o14 n lc c := by simpa only [metaVal_21, Nat.reduceAdd] using hm 21 (by decide)
    have m7 : r 236 = mv_len14 n lc c := by simpa only [metaVal_7, Nat.reduceAdd] using hm 7 (by decide)
    pre1_meta_simp [m21, m7, metaVal_22]
    rfl

theorem metaStep23 : MetaStepOK W n lc c 23 (metaStepBlock 23) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m22 : r 251 = mv_o15 n lc c := by simpa only [metaVal_22, Nat.reduceAdd] using hm 22 (by decide)
    have m8 : r 237 = mv_len15 n lc c := by simpa only [metaVal_8, Nat.reduceAdd] using hm 8 (by decide)
    have e : mv_o16 n lc c = (mv_o15 n lc c) + (mv_len15 n lc c) := rfl
    have hv23 : mv_o16 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_23] using metaVal_le n lc c hpay 23 (by decide)
    pre1_meta_simp [m22, m8]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m22 : r 251 = mv_o15 n lc c := by simpa only [metaVal_22, Nat.reduceAdd] using hm 22 (by decide)
    have m8 : r 237 = mv_len15 n lc c := by simpa only [metaVal_8, Nat.reduceAdd] using hm 8 (by decide)
    pre1_meta_simp [m22, m8, metaVal_23]
    rfl

theorem metaStep24 : MetaStepOK W n lc c 24 (metaStepBlock 24) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m23 : r 252 = mv_o16 n lc c := by simpa only [metaVal_23, Nat.reduceAdd] using hm 23 (by decide)
    have m8 : r 237 = mv_len15 n lc c := by simpa only [metaVal_8, Nat.reduceAdd] using hm 8 (by decide)
    have e : mv_o17 n lc c = (mv_o16 n lc c) + (mv_len15 n lc c) := rfl
    have hv24 : mv_o17 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_24] using metaVal_le n lc c hpay 24 (by decide)
    pre1_meta_simp [m23, m8]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m23 : r 252 = mv_o16 n lc c := by simpa only [metaVal_23, Nat.reduceAdd] using hm 23 (by decide)
    have m8 : r 237 = mv_len15 n lc c := by simpa only [metaVal_8, Nat.reduceAdd] using hm 8 (by decide)
    pre1_meta_simp [m23, m8, metaVal_24]
    rfl

theorem metaStep25 : MetaStepOK W n lc c 25 (metaStepBlock 25) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m24 : r 253 = mv_o17 n lc c := by simpa only [metaVal_24, Nat.reduceAdd] using hm 24 (by decide)
    have g47 : r 47 = (packedSparseSlots n) := hg 9 (by decide)
    have e : mv_o18 n lc c = (mv_o17 n lc c) + (packedSparseSlots n) := rfl
    have hv25 : mv_o18 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_25] using metaVal_le n lc c hpay 25 (by decide)
    pre1_meta_simp [m24, g47]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m24 : r 253 = mv_o17 n lc c := by simpa only [metaVal_24, Nat.reduceAdd] using hm 24 (by decide)
    have g47 : r 47 = (packedSparseSlots n) := hg 9 (by decide)
    pre1_meta_simp [m24, g47, metaVal_25]
    rfl

theorem metaStep26 : MetaStepOK W n lc c 26 (metaStepBlock 26) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m25 : r 254 = mv_o18 n lc c := by simpa only [metaVal_25, Nat.reduceAdd] using hm 25 (by decide)
    have m9 : r 238 = mv_len18 n lc c := by simpa only [metaVal_9, Nat.reduceAdd] using hm 9 (by decide)
    have e : mv_acc n lc c = (mv_o18 n lc c) + (mv_len18 n lc c) := rfl
    have hv26 : mv_acc n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_26] using metaVal_le n lc c hpay 26 (by decide)
    pre1_meta_simp [m25, m9]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m25 : r 254 = mv_o18 n lc c := by simpa only [metaVal_25, Nat.reduceAdd] using hm 25 (by decide)
    have m9 : r 238 = mv_len18 n lc c := by simpa only [metaVal_9, Nat.reduceAdd] using hm 9 (by decide)
    pre1_meta_simp [m25, m9, metaVal_26]
    rfl

theorem metaStep27 : MetaStepOK W n lc c 27 (metaStepBlock 27) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have e : mv_a n lc c = (packedReviewerCellWidth n) + (2 * n) := rfl
    have hv27 : mv_a n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_27] using metaVal_le n lc c hpay 27 (by decide)
    pre1_meta_simp [g75, g38]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    pre1_meta_simp [g75, g38, metaVal_27]
    rfl

theorem metaStep28 : MetaStepOK W n lc c 28 (metaStepBlock 28) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m1 : r 230 = mv_len1 n lc c := by simpa only [metaVal_1, Nat.reduceAdd] using hm 1 (by decide)
    have e : mv_b2 n lc c = (mv_a n lc c) + (mv_len1 n lc c) := rfl
    have hv28 : mv_b2 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_28] using metaVal_le n lc c hpay 28 (by decide)
    pre1_meta_simp [m27, m1]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m1 : r 230 = mv_len1 n lc c := by simpa only [metaVal_1, Nat.reduceAdd] using hm 1 (by decide)
    pre1_meta_simp [m27, m1, metaVal_28]
    rfl

theorem metaStep29 : MetaStepOK W n lc c 29 (metaStepBlock 29) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m10 : r 239 = mv_o3 n lc c := by simpa only [metaVal_10, Nat.reduceAdd] using hm 10 (by decide)
    have e : mv_b3 n lc c = (mv_a n lc c) + (mv_o3 n lc c) := rfl
    have hv29 : mv_b3 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_29] using metaVal_le n lc c hpay 29 (by decide)
    pre1_meta_simp [m27, m10]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m10 : r 239 = mv_o3 n lc c := by simpa only [metaVal_10, Nat.reduceAdd] using hm 10 (by decide)
    pre1_meta_simp [m27, m10, metaVal_29]
    rfl

theorem metaStep30 : MetaStepOK W n lc c 30 (metaStepBlock 30) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m11 : r 240 = mv_o4 n lc c := by simpa only [metaVal_11, Nat.reduceAdd] using hm 11 (by decide)
    have e : mv_b4 n lc c = (mv_a n lc c) + (mv_o4 n lc c) := rfl
    have hv30 : mv_b4 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_30] using metaVal_le n lc c hpay 30 (by decide)
    pre1_meta_simp [m27, m11]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m11 : r 240 = mv_o4 n lc c := by simpa only [metaVal_11, Nat.reduceAdd] using hm 11 (by decide)
    pre1_meta_simp [m27, m11, metaVal_30]
    rfl

theorem metaStep31 : MetaStepOK W n lc c 31 (metaStepBlock 31) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m12 : r 241 = mv_o5 n lc c := by simpa only [metaVal_12, Nat.reduceAdd] using hm 12 (by decide)
    have e : mv_b5 n lc c = (mv_a n lc c) + (mv_o5 n lc c) := rfl
    have hv31 : mv_b5 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_31] using metaVal_le n lc c hpay 31 (by decide)
    pre1_meta_simp [m27, m12]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m12 : r 241 = mv_o5 n lc c := by simpa only [metaVal_12, Nat.reduceAdd] using hm 12 (by decide)
    pre1_meta_simp [m27, m12, metaVal_31]
    rfl

theorem metaStep32 : MetaStepOK W n lc c 32 (metaStepBlock 32) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m13 : r 242 = mv_o6 n lc c := by simpa only [metaVal_13, Nat.reduceAdd] using hm 13 (by decide)
    have e : mv_b6 n lc c = (mv_a n lc c) + (mv_o6 n lc c) := rfl
    have hv32 : mv_b6 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_32] using metaVal_le n lc c hpay 32 (by decide)
    pre1_meta_simp [m27, m13]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m13 : r 242 = mv_o6 n lc c := by simpa only [metaVal_13, Nat.reduceAdd] using hm 13 (by decide)
    pre1_meta_simp [m27, m13, metaVal_32]
    rfl

theorem metaStep33 : MetaStepOK W n lc c 33 (metaStepBlock 33) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m14 : r 243 = mv_o7 n lc c := by simpa only [metaVal_14, Nat.reduceAdd] using hm 14 (by decide)
    have e : mv_b7 n lc c = (mv_a n lc c) + (mv_o7 n lc c) := rfl
    have hv33 : mv_b7 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_33] using metaVal_le n lc c hpay 33 (by decide)
    pre1_meta_simp [m27, m14]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m14 : r 243 = mv_o7 n lc c := by simpa only [metaVal_14, Nat.reduceAdd] using hm 14 (by decide)
    pre1_meta_simp [m27, m14, metaVal_33]
    rfl

theorem metaStep34 : MetaStepOK W n lc c 34 (metaStepBlock 34) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m15 : r 244 = mv_o8 n lc c := by simpa only [metaVal_15, Nat.reduceAdd] using hm 15 (by decide)
    have e : mv_b8 n lc c = (mv_a n lc c) + (mv_o8 n lc c) := rfl
    have hv34 : mv_b8 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_34] using metaVal_le n lc c hpay 34 (by decide)
    pre1_meta_simp [m27, m15]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m15 : r 244 = mv_o8 n lc c := by simpa only [metaVal_15, Nat.reduceAdd] using hm 15 (by decide)
    pre1_meta_simp [m27, m15, metaVal_34]
    rfl

theorem metaStep35 : MetaStepOK W n lc c 35 (metaStepBlock 35) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m16 : r 245 = mv_o9 n lc c := by simpa only [metaVal_16, Nat.reduceAdd] using hm 16 (by decide)
    have e : mv_b9 n lc c = (mv_a n lc c) + (mv_o9 n lc c) := rfl
    have hv35 : mv_b9 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_35] using metaVal_le n lc c hpay 35 (by decide)
    pre1_meta_simp [m27, m16]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m16 : r 245 = mv_o9 n lc c := by simpa only [metaVal_16, Nat.reduceAdd] using hm 16 (by decide)
    pre1_meta_simp [m27, m16, metaVal_35]
    rfl

theorem metaStep36 : MetaStepOK W n lc c 36 (metaStepBlock 36) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m17 : r 246 = mv_o10 n lc c := by simpa only [metaVal_17, Nat.reduceAdd] using hm 17 (by decide)
    have e : mv_b10 n lc c = (mv_a n lc c) + (mv_o10 n lc c) := rfl
    have hv36 : mv_b10 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_36] using metaVal_le n lc c hpay 36 (by decide)
    pre1_meta_simp [m27, m17]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m17 : r 246 = mv_o10 n lc c := by simpa only [metaVal_17, Nat.reduceAdd] using hm 17 (by decide)
    pre1_meta_simp [m27, m17, metaVal_36]
    rfl

theorem metaStep37 : MetaStepOK W n lc c 37 (metaStepBlock 37) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m18 : r 247 = mv_o11 n lc c := by simpa only [metaVal_18, Nat.reduceAdd] using hm 18 (by decide)
    have e : mv_b11 n lc c = (mv_a n lc c) + (mv_o11 n lc c) := rfl
    have hv37 : mv_b11 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_37] using metaVal_le n lc c hpay 37 (by decide)
    pre1_meta_simp [m27, m18]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m18 : r 247 = mv_o11 n lc c := by simpa only [metaVal_18, Nat.reduceAdd] using hm 18 (by decide)
    pre1_meta_simp [m27, m18, metaVal_37]
    rfl

theorem metaStep38 : MetaStepOK W n lc c 38 (metaStepBlock 38) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m19 : r 248 = mv_o12 n lc c := by simpa only [metaVal_19, Nat.reduceAdd] using hm 19 (by decide)
    have e : mv_b12 n lc c = (mv_a n lc c) + (mv_o12 n lc c) := rfl
    have hv38 : mv_b12 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_38] using metaVal_le n lc c hpay 38 (by decide)
    pre1_meta_simp [m27, m19]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m19 : r 248 = mv_o12 n lc c := by simpa only [metaVal_19, Nat.reduceAdd] using hm 19 (by decide)
    pre1_meta_simp [m27, m19, metaVal_38]
    rfl

theorem metaStep39 : MetaStepOK W n lc c 39 (metaStepBlock 39) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m20 : r 249 = mv_o13 n lc c := by simpa only [metaVal_20, Nat.reduceAdd] using hm 20 (by decide)
    have e : mv_b13 n lc c = (mv_a n lc c) + (mv_o13 n lc c) := rfl
    have hv39 : mv_b13 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_39] using metaVal_le n lc c hpay 39 (by decide)
    pre1_meta_simp [m27, m20]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m20 : r 249 = mv_o13 n lc c := by simpa only [metaVal_20, Nat.reduceAdd] using hm 20 (by decide)
    pre1_meta_simp [m27, m20, metaVal_39]
    rfl

theorem metaStep40 : MetaStepOK W n lc c 40 (metaStepBlock 40) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m21 : r 250 = mv_o14 n lc c := by simpa only [metaVal_21, Nat.reduceAdd] using hm 21 (by decide)
    have e : mv_b14 n lc c = (mv_a n lc c) + (mv_o14 n lc c) := rfl
    have hv40 : mv_b14 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_40] using metaVal_le n lc c hpay 40 (by decide)
    pre1_meta_simp [m27, m21]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m21 : r 250 = mv_o14 n lc c := by simpa only [metaVal_21, Nat.reduceAdd] using hm 21 (by decide)
    pre1_meta_simp [m27, m21, metaVal_40]
    rfl

theorem metaStep41 : MetaStepOK W n lc c 41 (metaStepBlock 41) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m22 : r 251 = mv_o15 n lc c := by simpa only [metaVal_22, Nat.reduceAdd] using hm 22 (by decide)
    have e : mv_b15 n lc c = (mv_a n lc c) + (mv_o15 n lc c) := rfl
    have hv41 : mv_b15 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_41] using metaVal_le n lc c hpay 41 (by decide)
    pre1_meta_simp [m27, m22]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m22 : r 251 = mv_o15 n lc c := by simpa only [metaVal_22, Nat.reduceAdd] using hm 22 (by decide)
    pre1_meta_simp [m27, m22, metaVal_41]
    rfl

theorem metaStep42 : MetaStepOK W n lc c 42 (metaStepBlock 42) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m23 : r 252 = mv_o16 n lc c := by simpa only [metaVal_23, Nat.reduceAdd] using hm 23 (by decide)
    have e : mv_b16 n lc c = (mv_a n lc c) + (mv_o16 n lc c) := rfl
    have hv42 : mv_b16 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_42] using metaVal_le n lc c hpay 42 (by decide)
    pre1_meta_simp [m27, m23]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m23 : r 252 = mv_o16 n lc c := by simpa only [metaVal_23, Nat.reduceAdd] using hm 23 (by decide)
    pre1_meta_simp [m27, m23, metaVal_42]
    rfl

theorem metaStep43 : MetaStepOK W n lc c 43 (metaStepBlock 43) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m24 : r 253 = mv_o17 n lc c := by simpa only [metaVal_24, Nat.reduceAdd] using hm 24 (by decide)
    have e : mv_b17 n lc c = (mv_a n lc c) + (mv_o17 n lc c) := rfl
    have hv43 : mv_b17 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_43] using metaVal_le n lc c hpay 43 (by decide)
    pre1_meta_simp [m27, m24]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m24 : r 253 = mv_o17 n lc c := by simpa only [metaVal_24, Nat.reduceAdd] using hm 24 (by decide)
    pre1_meta_simp [m27, m24, metaVal_43]
    rfl

theorem metaStep44 : MetaStepOK W n lc c 44 (metaStepBlock 44) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m25 : r 254 = mv_o18 n lc c := by simpa only [metaVal_25, Nat.reduceAdd] using hm 25 (by decide)
    have e : mv_b18 n lc c = (mv_a n lc c) + (mv_o18 n lc c) := rfl
    have hv44 : mv_b18 n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_44] using metaVal_le n lc c hpay 44 (by decide)
    pre1_meta_simp [m27, m25]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m27 : r 256 = mv_a n lc c := by simpa only [metaVal_27, Nat.reduceAdd] using hm 27 (by decide)
    have m25 : r 254 = mv_o18 n lc c := by simpa only [metaVal_25, Nat.reduceAdd] using hm 25 (by decide)
    pre1_meta_simp [m27, m25, metaVal_44]
    rfl

theorem metaStep45 : MetaStepOK W n lc c 45 (metaStepBlock 45) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have m26 : r 255 = mv_acc n lc c := by simpa only [metaVal_26, Nat.reduceAdd] using hm 26 (by decide)
    have g69 : r 69 = (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n) := hg 31 (by decide)
    have g70 : r 70 = (SuccinctClose.bpFringeTableOverhead n) := hg 32 (by decide)
    have g71 : r 71 = (SuccinctClose.bpChunkSelectTableOverhead n) := hg 33 (by decide)
    have e : mv_pay n lc c = ((((2 * n) + (mv_acc n lc c)) + (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n)) + (SuccinctClose.bpFringeTableOverhead n)) + (SuccinctClose.bpChunkSelectTableOverhead n) := rfl
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    pre1_meta_simp [g38, m26, g69, g70, g71]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have m26 : r 255 = mv_acc n lc c := by simpa only [metaVal_26, Nat.reduceAdd] using hm 26 (by decide)
    have g69 : r 69 = (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n) := hg 31 (by decide)
    have g70 : r 70 = (SuccinctClose.bpFringeTableOverhead n) := hg 32 (by decide)
    have g71 : r 71 = (SuccinctClose.bpChunkSelectTableOverhead n) := hg 33 (by decide)
    pre1_meta_simp [g38, m26, g69, g70, g71, metaVal_45]
    rfl

theorem metaStep46 : MetaStepOK W n lc c 46 (metaStepBlock 46) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m45 : r 274 = mv_pay n lc c := by simpa only [metaVal_45, Nat.reduceAdd] using hm 45 (by decide)
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_oldCount n lc c = ((((mv_pay n lc c) + (packedReviewerCellWidth n)) - 1) / (packedReviewerCellWidth n)) + 1 := rfl
    have hv46 : mv_oldCount n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_46] using metaVal_le n lc c hpay 46 (by decide)
    have hv45 : mv_pay n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_45] using metaVal_le n lc c hpay 45 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos75 : 0 < (packedReviewerCellWidth n) := packedReviewerCellWidth_pos n
    have := Nat.div_le_self ((((mv_pay n lc c) + (packedReviewerCellWidth n)) - 1)) ((packedReviewerCellWidth n))
    pre1_meta_simp [m45, g75, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m45 : r 274 = mv_pay n lc c := by simpa only [metaVal_45, Nat.reduceAdd] using hm 45 (by decide)
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [m45, g75, g2, metaVal_46]
    rfl

theorem metaStep47 : MetaStepOK W n lc c 47 (metaStepBlock 47) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m46 : r 275 = mv_oldCount n lc c := by simpa only [metaVal_46, Nat.reduceAdd] using hm 46 (by decide)
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have e : mv_oldBits n lc c = (mv_oldCount n lc c) * (packedReviewerCellWidth n) := rfl
    have hv47 : mv_oldBits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_47] using metaVal_le n lc c hpay 47 (by decide)
    pre1_meta_simp [m46, g75]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m46 : r 275 = mv_oldCount n lc c := by simpa only [metaVal_46, Nat.reduceAdd] using hm 46 (by decide)
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    pre1_meta_simp [m46, g75, metaVal_47]
    rfl

theorem metaStep48 : MetaStepOK W n lc c 48 (metaStepBlock 48) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m47 : r 276 = mv_oldBits n lc c := by simpa only [metaVal_47, Nat.reduceAdd] using hm 47 (by decide)
    have g76 : r 76 = (wordWidth n) := hg 38 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    have e : mv_dcount n lc c = (((mv_oldBits n lc c) + (wordWidth n)) - 1) / (wordWidth n) := rfl
    have hv48 : mv_dcount n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_48] using metaVal_le n lc c hpay 48 (by decide)
    have hv47 : mv_oldBits n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_47] using metaVal_le n lc c hpay 47 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    have hpos76 : 0 < (wordWidth n) := wordWidth_pos n
    have := Nat.div_le_self ((((mv_oldBits n lc c) + (wordWidth n)) - 1)) ((wordWidth n))
    pre1_meta_simp [m47, g76, g2]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m47 : r 276 = mv_oldBits n lc c := by simpa only [metaVal_47, Nat.reduceAdd] using hm 47 (by decide)
    have g76 : r 76 = (wordWidth n) := hg 38 (by decide)
    have g2 : r 2 = 1 := hb.2.1
    pre1_meta_simp [m47, g76, g2, metaVal_48]
    rfl

theorem metaStep49 : MetaStepOK W n lc c 49 (metaStepBlock 49) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m48 : r 277 = mv_dcount n lc c := by simpa only [metaVal_48, Nat.reduceAdd] using hm 48 (by decide)
    have e : mv_wc n lc c = (174) + (mv_dcount n lc c) := rfl
    have hv49 : mv_wc n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_49] using metaVal_le n lc c hpay 49 (by decide)
    obtain ⟨hacc, hsc, hlcS, hsup, hI, hBW, hMR, hLT, hGT, hLL, hGL, hlw1, hlw2, hws, hws1, hrw, how, hbaw, hWl, hOW, hOW1, hfb, hsb⟩ := metaAtoms n lc c
    have epay : mv_pay n lc c = 2 * n + mv_acc n lc c + SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n + SuccinctClose.bpFringeTableOverhead n + SuccinctClose.bpChunkSelectTableOverhead n := rfl
    pre1_meta_simp [m48]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m48 : r 277 = mv_dcount n lc c := by simpa only [metaVal_48, Nat.reduceAdd] using hm 48 (by decide)
    pre1_meta_simp [m48, metaVal_49]
    rfl

theorem metaStep50 : MetaStepOK W n lc c 50 (metaStepBlock 50) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have m26 : r 255 = mv_acc n lc c := by simpa only [metaVal_26, Nat.reduceAdd] using hm 26 (by decide)
    have e : mv_ioff n lc c = (2 * n) + (mv_acc n lc c) := rfl
    have hv50 : mv_ioff n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_50] using metaVal_le n lc c hpay 50 (by decide)
    pre1_meta_simp [g38, m26]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g38 : r 38 = (2 * n) := hg 0 (by decide)
    have m26 : r 255 = mv_acc n lc c := by simpa only [metaVal_26, Nat.reduceAdd] using hm 26 (by decide)
    pre1_meta_simp [g38, m26, metaVal_50]
    rfl

theorem metaStep51 : MetaStepOK W n lc c 51 (metaStepBlock 51) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m50 : r 279 = mv_ioff n lc c := by simpa only [metaVal_50, Nat.reduceAdd] using hm 50 (by decide)
    have g69 : r 69 = (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n) := hg 31 (by decide)
    have e : mv_foff n lc c = (mv_ioff n lc c) + (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n) := rfl
    have hv51 : mv_foff n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_51] using metaVal_le n lc c hpay 51 (by decide)
    pre1_meta_simp [m50, g69]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m50 : r 279 = mv_ioff n lc c := by simpa only [metaVal_50, Nat.reduceAdd] using hm 50 (by decide)
    have g69 : r 69 = (SuccinctClose.canonicalRelativeRmmInteriorRawPayloadOverhead n) := hg 31 (by decide)
    pre1_meta_simp [m50, g69, metaVal_51]
    rfl

theorem metaStep52 : MetaStepOK W n lc c 52 (metaStepBlock 52) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m51 : r 280 = mv_foff n lc c := by simpa only [metaVal_51, Nat.reduceAdd] using hm 51 (by decide)
    have g70 : r 70 = (SuccinctClose.bpFringeTableOverhead n) := hg 32 (by decide)
    have e : mv_soff n lc c = (mv_foff n lc c) + (SuccinctClose.bpFringeTableOverhead n) := rfl
    have hv52 : mv_soff n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_52] using metaVal_le n lc c hpay 52 (by decide)
    pre1_meta_simp [m51, g70]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have m51 : r 280 = mv_foff n lc c := by simpa only [metaVal_51, Nat.reduceAdd] using hm 51 (by decide)
    have g70 : r 70 = (SuccinctClose.bpFringeTableOverhead n) := hg 32 (by decide)
    pre1_meta_simp [m51, g70, metaVal_52]
    rfl

theorem metaStep53 : MetaStepOK W n lc c 53 (metaStepBlock 53) := by
  refine metaStep_pure hW _ (by decide) (by decide) ?_ ?_
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have m51 : r 280 = mv_foff n lc c := by simpa only [metaVal_51, Nat.reduceAdd] using hm 51 (by decide)
    have e : mv_fbase n lc c = (packedReviewerCellWidth n) + (mv_foff n lc c) := rfl
    have hv53 : mv_fbase n lc c ≤ 3 * (400000 * (n + 1)) := by simpa only [metaVal_53] using metaVal_le n lc c hpay 53 (by decide)
    pre1_meta_simp [g75, m51]
    repeat' apply And.intro
    all_goals first | omega | (split <;> omega)
  · intro r ⟨hb, hg, h177, h178, h0⟩ hm
    have g75 : r 75 = (packedReviewerCellWidth n) := hg 37 (by decide)
    have m51 : r 280 = mv_foff n lc c := by simpa only [metaVal_51, Nat.reduceAdd] using hm 51 (by decide)
    pre1_meta_simp [g75, m51, metaVal_53]
    rfl

end Steps

end RMQ.SuccinctFinal.PackedConstruction.Proof
