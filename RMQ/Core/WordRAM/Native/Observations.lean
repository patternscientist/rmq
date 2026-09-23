import RMQ.Core.WordRAM.Native.Thin

/-! # Observations against the original Run interfaces

The accumulator is connected here to the pre-existing step, read and six-category
projections. These are identities of the actual transition fold, not a new cost
predicate substituted for the primitive run's observations.
-/

namespace RMQ.SuccinctFinal.PackedNative
open PackedWordRAM

def Counts.get (a : Counts) : Category → Nat
  | .memoryRead => a.memoryRead
  | .registerWrite => a.registerWrite
  | .arithmetic => a.arithmetic
  | .comparison => a.comparison
  | .branch => a.branch
  | .control => a.control

theorem Counts.get_bump (a : Counts) (category wanted : Category) :
    (a.bump category).get wanted = a.get wanted + if category = wanted then 1 else 0 := by
  cases category <;> cases wanted <;> simp [Counts.get, Counts.bump]

theorem observationFold_steps (ts : List Transition) (observeReads : Bool) (a : Stats) :
    (ts.foldl (fun acc t => acc.record observeReads t.instruction.category t.receipt) a).steps =
      a.steps + ts.length := by
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Stats.record, List.length_cons]
      omega

theorem observationFold_category (ts : List Transition) (observeReads : Bool)
    (a : Stats) (category : Category) :
    (ts.foldl (fun acc t => acc.record observeReads t.instruction.category t.receipt) a).counts.get category =
      a.counts.get category + (ts.map (·.instruction.category)).count category := by
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [Stats.record, Counts.get_bump, List.map_cons]
      by_cases h : t.instruction.category = category
      · simp [h, List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [h, List.count_cons, beq_iff_eq]

theorem observationFold_reads (ts : List Transition) (a : Stats) :
    (ts.foldl (fun acc t => acc.record true t.instruction.category t.receipt) a).readsRev =
      (ts.filterMap (·.receipt)).reverse ++ a.readsRev := by
  induction ts generalizing a with
  | nil => simp
  | cons t ts ih =>
      simp only [List.foldl_cons]
      rw [ih]
      cases h : t.receipt <;>
        simp [h, Stats.record, List.reverse_cons, List.append_assoc]

theorem observeRun_steps (observeReads : Bool) (r : Run) :
    (observeRun observeReads r {}).2.steps = r.steps := by
  simpa [observeRun, Run.steps] using observationFold_steps r.transitions observeReads {}

theorem observeRun_category (observeReads : Bool) (r : Run) (category : Category) :
    (observeRun observeReads r {}).2.counts.get category = r.categoryCount category := by
  have h := observationFold_category r.transitions observeReads {} category
  cases category <;> simpa [observeRun, Run.categoryCount, Run.categories, Counts.get] using h

theorem observeRun_reads (r : Run) :
    (observeRun true r {}).2.readsRev.reverse = r.reads := by
  have h := observationFold_reads r.transitions {}
  simpa [observeRun, Run.reads] using congrArg List.reverse h

end RMQ.SuccinctFinal.PackedNative
