import RMQ.Core.SuccinctSpace.WordStore
import RMQ.Core.WordRAM

/-!
# Word-RAM interpretation for payload word stores

This module connects the existing payload-word representation boundary to the
first-order `WordRAM` interpreter.  A word-store read is no longer just a
`Costed` callback: it is also the result of interpreting a one-read payload
program.
-/

namespace RMQ

namespace SuccinctSpace

namespace PayloadWordStore

/-- A one-segment Word-RAM store exposing exactly this payload word store. -/
def wordRAMStore
    {payload : List Bool} (store : PayloadWordStore payload) :
    WordRAM.Store where
  wordSegments := #[store.words]

/-- First-order program for reading one payload word from this store. -/
def readProgram
    {payload : List Bool} (_store : PayloadWordStore payload) (i : Nat) :
    WordRAM.Program .optWord :=
  WordRAM.Program.readWord 0 i

@[simp] theorem wordRAMStore_readWord?_zero
    {payload : List Bool} (store : PayloadWordStore payload) (i : Nat) :
    store.wordRAMStore.readWord? 0 i = store.words[i]? := by
  rfl

@[simp] theorem readProgram_eval_value
    {payload : List Bool} (store : PayloadWordStore payload) (i : Nat) :
    ((store.readProgram i).eval store.wordRAMStore).value =
      store.words[i]? := by
  rfl

@[simp] theorem readProgram_eval_trace
    {payload : List Bool} (store : PayloadWordStore payload) (i : Nat) :
    ((store.readProgram i).eval store.wordRAMStore).trace =
      [WordRAM.TraceEvent.readWord 0 i store.words[i]?] := by
  rfl

/-- Interpreting a payload read program refines the existing costed read. -/
theorem readProgram_refines_readWordCosted
    {payload : List Bool} (store : PayloadWordStore payload) (i : Nat) :
    ((store.readProgram i).eval store.wordRAMStore).toCosted =
      store.readWordCosted i := by
  rfl

theorem readProgram_exact
    {payload : List Bool} (store : PayloadWordStore payload) (i : Nat) :
    ((store.readProgram i).eval store.wordRAMStore).toCosted.erase =
      store.words[i]? := by
  rfl

theorem readProgram_cost
    {payload : List Bool} (store : PayloadWordStore payload) (i : Nat) :
    ((store.readProgram i).eval store.wordRAMStore).toCosted.cost = 1 := by
  rfl

end PayloadWordStore

namespace BoundedPayloadWordStore

/-- The Word-RAM store inherited from the underlying payload word store. -/
def wordRAMStore
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize) :
    WordRAM.Store :=
  store.store.wordRAMStore

theorem wordRAMStore_wordsBounded
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize) :
    store.wordRAMStore.WordsBounded wordSize := by
  intro segment index word hread
  unfold wordRAMStore PayloadWordStore.wordRAMStore
    WordRAM.Store.readWord? at hread
  cases segment with
  | zero =>
      simp at hread
      have hlist : store.store.words.toList[index]? = some word := by
        simpa [Array.getElem?_toList] using hread
      exact store.word_length_le (List.mem_of_getElem? hlist)
  | succ segment =>
      simp at hread

theorem readProgram_word_length_le
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize)
    {i : Nat} {word : WordRAM.Word}
    (hword :
      ((store.store.readProgram i).eval store.wordRAMStore).value =
        some word) :
    word.length <= wordSize := by
  have hread : store.wordRAMStore.readWord? 0 i = some word := by
    simpa [PayloadWordStore.readProgram] using hword
  exact store.wordRAMStore_wordsBounded hread

theorem readProgram_trace_word_reads_length_le
    {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize) (i : Nat) :
    forall event : WordRAM.TraceEvent,
      event ∈ ((store.store.readProgram i).eval store.wordRAMStore).trace ->
        event.wordLengthBounded wordSize := by
  exact WordRAM.Program.eval_word_reads_length_le_machine
    (store.store.readProgram i) store.wordRAMStore
    store.wordRAMStore_wordsBounded

end BoundedPayloadWordStore

end SuccinctSpace

end RMQ
