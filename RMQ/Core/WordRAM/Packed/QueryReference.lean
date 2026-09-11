import RMQ.Core.WordRAM.Packed.QueryProof
import RMQ.Core.WordRAM.Packed.QueryStatic

/-! # Ordinary-list contract of the guarded primitive query

The local LCA interface below is discharged by the canonical interior navigator
at the final consumer. No legacy trace cost is used as a primitive step bound.
-/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

theorem optionNatPacket_decode (answer : Option Nat) :
    (if optionNatPacket answer = 0 then none else some (optionNatPacket answer - 1)) = answer := by
  cases answer <;> simp [optionNatPacket]

theorem queryTraceResult_value_reference (xs : List Int) (left right : Nat) :
    (SuccinctClassic.queryTraceResult xs left right).value =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none := by
  by_cases hv : ValidRange xs left right
  · have hlen : 0 < right - left := by exact Nat.sub_pos_of_lt hv.1
    have heq : left + (right - left) = right := by have := hv.1; omega
    have h := SuccinctClassic.queryCosted_exact xs (left := left) hlen (by rw [heq]; exact hv.2)
    rw [heq] at h
    simpa only [SuccinctClassic.queryCosted, WordRAM.TraceResult.toCosted, Costed.erase, if_pos hv] using h
  · rw [SuccinctClassic.queryTraceResult_invalid xs left right hv]
    simp [WordRAM.TraceResult.pure, hv]

theorem queryRun_result_with_lca (xs : List Int)
    (hlca : LCACorrect (SuccinctClassic.cartesianShape xs) (buildMemory xs) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (left right : Nat) :
    (queryRun (buildMemory xs) xs.length left right).result =
      some (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) := by
  by_cases hv : ValidRange xs left right
  · have h := (queryRun_valid_with_lca (SuccinctClassic.cartesianShape xs) hlca hlwrites left right
      hv.1 (by simpa only [packedReviewerCartesianShape_size] using hv.2)).1
    rw [packedReviewerPackedReference_eq_public xs left right hv] at h
    simpa only [packedReviewerCartesianShape_size] using h
  · have h := (queryRun_invalid (buildMemory xs) xs.length left right hv).1
    rw [SuccinctClassic.queryTraceResult_invalid xs left right hv]
    simpa only [WordRAM.TraceResult.pure, optionNatPacket, Option.map_none, Option.getD_none] using h

theorem Run.status_of_result (actual : Run) (value : Nat) (h : actual.result = some value) :
    actual.final.status = .halted value := by
  cases hs : actual.final.status with
  | running => simp [Run.result, hs] at h
  | fault => simp [Run.result, hs] at h
  | halted v => simp only [Run.result, hs, Option.some.injEq] at h; exact congrArg Status.halted h

theorem queryRun_halts_with_lca (xs : List Int)
    (hlca : LCACorrect (SuccinctClassic.cartesianShape xs) (buildMemory xs) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (left right : Nat) :
    (queryRun (buildMemory xs) xs.length left right).final.status =
      .halted (optionNatPacket (SuccinctClassic.queryTraceResult xs left right).value) :=
  Run.status_of_result _ _ (queryRun_result_with_lca xs hlca hlwrites left right)

theorem queryNat_reference_with_lca (xs : List Int)
    (hlca : LCACorrect (SuccinctClassic.cartesianShape xs) (buildMemory xs) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (left right : Nat) :
    queryNat (buildMemory xs) xs.length left right =
      (SuccinctClassic.queryTraceResult xs left right).value := by
  by_cases hcap : left < 2 ^ wordWidth xs.length ∧ right < 2 ^ wordWidth xs.length
  · rw [queryNat, encodeInputs, if_pos hcap]
    change ((queryRun (buildMemory xs) xs.length left right).result).bind
      (fun packet => if packet = 0 then none else some (packet - 1)) = _
    rw [queryRun_result_with_lca xs hlca hlwrites left right]
    exact optionNatPacket_decode _
  · have hv : ¬ ValidRange xs left right := by
      intro hv
      have hn := size_lt_wordCapacity xs.length
      exact hcap ⟨by have := hv.1; have := hv.2; omega, by have := hv.2; omega⟩
    rw [queryNat_invalid (buildMemory xs) xs.length left right hv,
      SuccinctClassic.queryTraceResult_invalid xs left right hv]
    rfl

theorem queryNat_exact_with_lca (xs : List Int)
    (hlca : LCACorrect (SuccinctClassic.cartesianShape xs) (buildMemory xs) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (left right : Nat) :
    queryNat (buildMemory xs) xs.length left right =
      if ValidRange xs left right then some (scanWindow xs left (right - left)) else none := by
  rw [queryNat_reference_with_lca xs hlca hlwrites, queryTraceResult_value_reference]

theorem queryNat_leftmost_with_lca (xs : List Int)
    (hlca : LCACorrect (SuccinctClassic.cartesianShape xs) (buildMemory xs) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (left right index : Nat)
    (hresult : queryNat (buildMemory xs) xs.length left right = some index) :
    LeftmostArgMin xs left right index := by
  rw [queryNat_exact_with_lca xs hlca hlwrites] at hresult
  by_cases hv : ValidRange xs left right
  · rw [if_pos hv] at hresult
    have hi : scanWindow xs left (right - left) = index := Option.some.inj hresult
    have heq : left + (right - left) = right := by have := hv.1; omega
    have h := scanWindow_leftmost xs left (right - left) (by have := hv.1; omega) (by rw [heq]; exact hv.2)
    simpa only [heq, hi] using h
  · simp [hv] at hresult

end RMQ.SuccinctFinal.PackedWordRAM
