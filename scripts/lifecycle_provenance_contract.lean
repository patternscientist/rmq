import RMQ.Core.WordRAM.Lifecycle.Provenance

/-! Frozen direct consumer of the continuous production receipts. The client
types below expand the producer's occurrence and scalar-receipt predicates. -/

namespace RMQ.SuccinctFinal.PackedLifecycle.ProvenanceChecks

open PackedWordRAM (buildMemory)
open Continuous (continuousRun)
set_option maxRecDepth 30000

def ExpectedOccurrence (model : InputModel) (xs : List Int) (left right index : Nat)
    (t : Transition) : Prop :=
  (continuousRun model xs left right).transitions[index]? = some t ∧
    t.before = (run (Layout.program model) index
      (initialState model xs left right Layout.builderBase)).final ∧
    step (Layout.program model) t.before = some t

def ExpectedOutput (t : Transition) : Prop :=
  t.action = .instruction (.old (.move 0 3)) ∧
    t.after = execute (.old (.move 0 3)) t.before ∧
    t.after.core.regs 0 = t.before.core.regs 3

def ExpectedRead (dst addr : PackedConstruction.Operand) (address value : Nat) (t : Transition) : Prop :=
  t.action = .instruction (.old (.load dst addr)) ∧
    t.before.core.regs addr = address ∧ address < t.before.core.extent ∧
    t.before.core.memory address = some value ∧
    t.after = execute (.old (.load dst addr)) t.before ∧ t.after.core.regs dst = value

def ExpectedCopy (original : Nat → Option Nat) (B i : Nat) (load store : Transition) : Prop :=
  load.action = .instruction (.old (.load 5 0)) ∧
    store.action = .instruction (.old (.store 1 5)) ∧
    load.before.core.regs 0 = B + i ∧ store.before.core.regs 1 = i ∧
    load.before.core.memory (B + i) = original (B + i) ∧
    some (load.after.core.regs 5) = original (B + i) ∧ store.before = load.after ∧
    store.after.core.memory i = original (B + i) ∧
    load.read? = some (B + i, original (B + i)) ∧
    store.write? = some (i, load.after.core.regs 5)

def ExpectedRelease (a : Nat) (t : Transition) : Prop :=
  t.action = .instruction .releaseCell ∧ t.before.core.extent = a + 1 ∧
    t.after.core.extent = a ∧ t.after.core.memory a = none ∧
    (∀ other, other ≠ a → t.after.core.memory other = t.before.core.memory other) ∧
    t.after = execute .releaseCell t.before

structure ExpectedReceipts (model : InputModel) (xs : List Int) (left right : Nat)
    (producer : PackedConstruction.State) (body : List PackedConstruction.Transition) : Prop where
  output : ∃ (index : Nat) (pre : PackedConstruction.State) (transfer : Transition),
    index < body.length ∧
    ExpectedOccurrence model xs left right index
      (oldTransition (initialState model xs left right Layout.builderBase).keyExtent
        (initialState model xs left right Layout.builderBase).keyRegExtent
        ⟨pre, ⟨.reserve 3⟩, PackedConstruction.execPrim (.reserve 3) pre⟩) ∧
    producer.regs 3 = pre.extent ∧
    (∀ fuel, index + 1 ≤ fuel → fuel ≤ body.length →
      (run (Layout.program model) fuel
        (initialState model xs left right Layout.builderBase)).final.core.regs 3 = pre.extent) ∧
    ExpectedOccurrence model xs left right body.length transfer ∧
    transfer.before = Construction.producedState model xs left right producer ∧
    ExpectedOutput transfer ∧ transfer.after.core.regs 0 = pre.extent
  metadata :
    (∃ t, ExpectedOccurrence model xs left right (body.length + 1) t ∧
      ExpectedRead 302 0 (producer.regs 3) xs.length t) ∧
    (∃ t, ExpectedOccurrence model xs left right (body.length + 4) t ∧
      ExpectedRead 2 4 (producer.regs 3 + 7) (buildMemory xs).length t) ∧
    (∃ t, ExpectedOccurrence model xs left right (body.length + 8) t ∧
      ExpectedRead 300 4 (Descriptor.requestBase model xs.length) left t) ∧
    (∃ t, ExpectedOccurrence model xs left right (body.length + 10) t ∧
      ExpectedRead 301 4 (Descriptor.requestBase model xs.length + 1) right t)
  copy : ∀ i, i < (buildMemory xs).length → ∃ load store,
    ExpectedOccurrence model xs left right (body.length + 11 + (4 + 7 * i)) load ∧
    ExpectedOccurrence model xs left right (body.length + 11 + (5 + 7 * i)) store ∧
    ExpectedCopy producer.memory (producer.regs 3) i load store ∧
    load.after.core.regs 5 = (buildMemory xs).getD i 0 ∧
    store.after.core.memory i = (buildMemory xs)[i]?
  releases : ∀ k, k < producer.regs 3 → ∃ t,
    ExpectedOccurrence model xs left right
      (body.length + 11 + (5 + 7 * (buildMemory xs).length + 4 * k)) t ∧
    ExpectedRelease ((buildMemory xs).length + (producer.regs 3 - k) - 1) t

theorem producerContract (model : InputModel) (xs : List Int) (left right : Nat)
    (contract : ContinuousConstructionQuery model xs left right) :
    ∃ abstract producer body,
      Construction.BuildStage model xs left right abstract producer body ∧
      Provenance.ProductionReceipts model xs left right producer body :=
  Provenance.continuous_production contract

theorem checkP01 (model : InputModel) (xs : List Int) (left right : Nat)
    (contract : ContinuousConstructionQuery model xs left right) :
    ∃ abstract producer body,
      Construction.BuildStage model xs left right abstract producer body ∧
      ExpectedReceipts model xs left right producer body := by
  obtain ⟨abstract, producer, body, built, receipts⟩ := producerContract model xs left right contract
  exact ⟨abstract, producer, body, built,
    { output := receipts.output
      metadata := receipts.metadata
      copy := receipts.copy
      releases := receipts.releases }⟩

end RMQ.SuccinctFinal.PackedLifecycle.ProvenanceChecks
