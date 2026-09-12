import RMQ.Core.WordRAM.Bitvector.AccessExecution
import RMQ.Core.WordRAM.Bitvector.RankExecution

/-! # All-natural operation interfaces and supplied-memory agreement -/

namespace RMQ.PackedBitvector

open SuccinctFinal.PackedWordRAM

theorem decodeNatPacket_optionNatPacket (value : Option Nat) :
    decodeNatPacket (optionNatPacket value) = value := by cases value <;> rfl

theorem decodeBoolPacket_accessPacket (bits : List Bool) (index : Nat) :
    decodeBoolPacket (AccessProof.accessPacket bits index) = bits[index]? := by
  cases hg : bits[index]? with
  | none => simp [AccessProof.accessPacket, hg, decodeBoolPacket]
  | some bit => cases bit <;> simp [AccessProof.accessPacket, hg, decodeBoolPacket]

theorem queryPacket_of_result (bits : List Bool) (operation : Operation)
    (output : Nat) (houtput : resultRegister operation = output)
    (target : Bool) (argument packet : Nat)
    (ha : argument < 2 ^ Experiment.width bits.length)
    (hv : (execute bits operation target argument).final.regs output = packet) :
    queryPacket bits operation target argument = packet := by
  subst output
  simp only [queryPacket, if_pos ha]
  exact hv

theorem access_eq (bits : List Bool) (index : Nat) : access bits index = bits[index]? := by
  by_cases hi : index < 2 ^ Experiment.width bits.length
  · have hv := (execute_access bits index).2.2.1
    have hp := queryPacket_of_result bits .access 705 rfl false index _ hi hv
    exact (congrArg decodeBoolPacket hp).trans (decodeBoolPacket_accessPacket bits index)
  · have hn := size_lt_capacity bits.length
    have hout : bits.length ≤ index := by omega
    simp [access, queryPacket, hi, decodeBoolPacket, List.getElem?_eq_none hout]

theorem rank_eq (bits : List Bool) (target : Bool) (endPos : Nat) :
    rank bits target endPos =
      if endPos ≤ bits.length then some (Succinct.rankPrefix target bits endPos) else none := by
  by_cases hi : endPos < 2 ^ Experiment.width bits.length
  · have hv := (execute_rank bits target endPos).2.2.1
    have hp := queryPacket_of_result bits .rank 360 rfl target endPos _ hi hv
    have hd : decodeNatPacket (rankPacket bits target endPos) =
        if endPos ≤ bits.length then some (Succinct.rankPrefix target bits endPos) else none := by
      by_cases h : endPos ≤ bits.length <;> simp [rankPacket, h, decodeNatPacket]
    exact (congrArg decodeNatPacket hp).trans hd
  · have hn := size_lt_capacity bits.length
    have hout : ¬endPos ≤ bits.length := by omega
    simp [rank, queryPacket, hi, decodeNatPacket, hout]

theorem select_eq (bits : List Bool) (target : Bool) (occurrence : Nat) :
    select bits target occurrence = Succinct.select target bits occurrence := by
  by_cases hi : occurrence < 2 ^ Experiment.width bits.length
  · have hv := (execute_select bits target occurrence).2.2.1
    have hp := queryPacket_of_result bits .select 513 rfl target occurrence _ hi hv
    exact (congrArg decodeNatPacket hp).trans (decodeNatPacket_optionNatPacket _)
  · have hn := size_lt_capacity bits.length
    have hout : bits.length ≤ occurrence := by omega
    rw [Succinct.select_none_of_length_le_occurrence hout]
    simp [select, queryPacket, hi, decodeNatPacket]

/-- The complete same-run equality includes final state, every transition and
failed receipts as well as result and cost. The supplied memory is arbitrary. -/
theorem execution_eq_of_agree (bits : List Bool) (operation : Operation)
    (target : Bool) (argument : Nat) (supplied : Memory)
    (hagrees : ∀ receipt ∈ (execute bits operation target argument).reads,
      supplied[receipt.address]? = (Allocation.memory bits)[receipt.address]?) :
    run supplied (program operation) ((source operation).size+1) (initial operation target argument) =
      execute bits operation target argument :=
  run_eq_of_agree (Allocation.memory bits) supplied (program operation)
    ((source operation).size+1) (initial operation target argument) hagrees

end RMQ.PackedBitvector
