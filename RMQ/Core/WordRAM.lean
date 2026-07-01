import RMQ.Core.RAM

/-!
# First-order Word-RAM query interpreter

This module is a deliberately small anti-oracle refinement layer.  Programs are
syntax trees, evaluation computes the value and trace together, and the store is
payload-memory only.  The theorem-facing projection still lands in `Costed`,
but only after interpretation.
-/

namespace RMQ

namespace WordRAM

abbrev Word := List Bool

/-- The first small collection of value types needed by payload read programs. -/
inductive Ty where
  | unit
  | nat
  | bool
  | word
  | optWord
  | optNat
  | optOptNat
deriving Repr, DecidableEq

namespace Ty

/-- Lean interpretation of the small Word-RAM value universe. -/
def denote : Ty -> Type
  | unit => Unit
  | nat => Nat
  | bool => Bool
  | word => Word
  | optWord => Option Word
  | optNat => Option Nat
  | optOptNat => Option (Option Nat)

end Ty

/-- Interpret one Boolean bit as a little-endian binary digit. -/
def bitToNat (bit : Bool) : Nat :=
  if bit then 1 else 0

/-- Little-endian interpretation of one payload word. -/
def bitsToNatLE : Word -> Nat
  | [] => 0
  | bit :: rest => bitToNat bit + 2 * bitsToNatLE rest

/-- Decode a fixed-width optional natural number from one payload word. -/
def bitsToOptionNatLE (width : Nat) (bits : Word) : Option Nat :=
  match bits with
  | [] => none
  | present :: rest =>
      if present then
        some (bitsToNatLE (rest.take width))
      else
        none

/-- Payload-only word memory. -/
structure Store where
  wordSegments : Array (Array Word)

namespace Store

/-- Read one word from a segment, returning `none` for an invalid segment or index. -/
def readWord? (store : Store) (segment index : Nat) : Option Word :=
  match store.wordSegments[segment]? with
  | none => none
  | some words => words[index]?

/-- All dynamically readable words in the store fit within `bound`. -/
def WordsBounded (store : Store) (bound : Nat) : Prop :=
  forall {segment index : Nat} {word : Word},
    store.readWord? segment index = some word -> word.length <= bound

end Store

/-- Trace events produced by the interpreter. -/
inductive TraceEvent where
  | readWord (segment index : Nat) (word? : Option Word)
  | wordRank (target : Bool) (limit result : Nat)
  | wordSelect (target : Bool) (occurrence : Nat) (result : Option Nat)
deriving Repr, DecidableEq

namespace TraceEvent

/-- A trace event agrees with the store it claims to read. -/
def matchesStore (store : Store) : TraceEvent -> Prop
  | readWord segment index word? => store.readWord? segment index = word?
  | wordRank _ _ _ => True
  | wordSelect _ _ _ => True

/-- Any word returned by this event fits in `bound`. -/
def wordLengthBounded (bound : Nat) : TraceEvent -> Prop
  | readWord _ _ none => True
  | readWord _ _ (some word) => word.length <= bound
  | wordRank _ _ _ => True
  | wordSelect _ _ _ => True

end TraceEvent

/-- Interpreter result: erased value plus the trace used to compute it. -/
structure Result (ty : Ty) where
  value : ty.denote
  trace : List TraceEvent

namespace Result

/-- Operational step count, derived from the trace. -/
def steps (result : Result ty) : Nat :=
  result.trace.length

/-- Project an interpreted result into the existing theorem-facing cost carrier. -/
def toCosted (result : Result ty) : Costed ty.denote where
  value := result.value
  cost := result.steps

@[simp] theorem toCosted_value (result : Result ty) :
    result.toCosted.value = result.value := by
  rfl

@[simp] theorem toCosted_cost_eq_trace_length (result : Result ty) :
    result.toCosted.cost = result.trace.length := by
  rfl

theorem toCosted_run_eq_value_trace_length (result : Result ty) :
    result.toCosted.run = (result.value, result.trace.length) := by
  rfl

end Result

/--
Small first-order program syntax.

The current phase only includes payload word reads and zero-cost decoders needed
to refine existing payload table reads.  Later phases can extend this syntax
with arithmetic, branches, and word primitives without changing the one-way
`eval -> Costed` trust direction.
-/
inductive Program : Ty -> Type where
  | pure {ty : Ty} (value : ty.denote) : Program ty
  | readWord (segment index : Nat) : Program .optWord
  | mapOptWordNat (program : Program .optWord) : Program .optNat
  | mapOptWordOptionNat (width : Nat) (program : Program .optWord) :
      Program .optOptNat
  | joinOptOptNat (program : Program .optOptNat) : Program .optNat
  | sampledRank
      (target : Bool) (offset : Nat)
      (sample : Program .optNat) (word : Program .optWord) :
      Program .nat
  | wordSelectFromOpt
      (target : Bool) (occurrence : Nat) (word : Program .optWord) :
      Program .optNat

namespace Program

/-- Deterministic program evaluation against a payload-only store. -/
def eval : Program ty -> Store -> Result ty
  | pure value, _store => { value := value, trace := [] }
  | readWord segment index, store =>
      let word? := store.readWord? segment index
      { value := word?, trace := [TraceEvent.readWord segment index word?] }
  | mapOptWordNat program, store =>
      let result := eval program store
      { value := result.value.map bitsToNatLE, trace := result.trace }
  | mapOptWordOptionNat width program, store =>
      let result := eval program store
      { value := result.value.map (bitsToOptionNatLE width), trace := result.trace }
  | joinOptOptNat program, store =>
      let result := eval program store
      { value := result.value.join, trace := result.trace }
  | sampledRank target offset sample word, store =>
      let sampleResult := eval sample store
      let wordResult := eval word store
      match sampleResult.value, wordResult.value with
      | some sampleValue, some wordValue =>
          let localRank := RAM.boolRankPrefix target wordValue offset
          { value := sampleValue + localRank
            trace :=
              sampleResult.trace ++ wordResult.trace ++
                [TraceEvent.wordRank target offset localRank] }
      | _, _ =>
          { value := (0 : Nat), trace := sampleResult.trace ++ wordResult.trace }
  | wordSelectFromOpt target occurrence word, store =>
      let wordResult := eval word store
      match wordResult.value with
      | none =>
          { value := none, trace := wordResult.trace }
      | some wordValue =>
          let selected := RAM.boolSelectInWord target wordValue occurrence
          { value := selected
            trace :=
              wordResult.trace ++
                [TraceEvent.wordSelect target occurrence selected] }

@[simp] theorem eval_pure_value
    {ty : Ty} (value : ty.denote) (store : Store) :
    (eval (pure value) store).value = value := by
  rfl

@[simp] theorem eval_pure_trace
    {ty : Ty} (value : ty.denote) (store : Store) :
    (eval (pure value) store).trace = [] := by
  rfl

@[simp] theorem eval_readWord_value
    (segment index : Nat) (store : Store) :
    (eval (readWord segment index) store).value =
      store.readWord? segment index := by
  rfl

@[simp] theorem eval_readWord_trace
    (segment index : Nat) (store : Store) :
    (eval (readWord segment index) store).trace =
      [TraceEvent.readWord segment index (store.readWord? segment index)] := by
  rfl

@[simp] theorem eval_mapOptWordNat_value
    (program : Program .optWord) (store : Store) :
    (eval (mapOptWordNat program) store).value =
      (eval program store).value.map bitsToNatLE := by
  rfl

@[simp] theorem eval_mapOptWordNat_trace
    (program : Program .optWord) (store : Store) :
    (eval (mapOptWordNat program) store).trace =
      (eval program store).trace := by
  rfl

@[simp] theorem eval_mapOptWordOptionNat_value
    (width : Nat) (program : Program .optWord) (store : Store) :
    (eval (mapOptWordOptionNat width program) store).value =
      (eval program store).value.map (bitsToOptionNatLE width) := by
  rfl

@[simp] theorem eval_mapOptWordOptionNat_trace
    (width : Nat) (program : Program .optWord) (store : Store) :
    (eval (mapOptWordOptionNat width program) store).trace =
      (eval program store).trace := by
  rfl

@[simp] theorem eval_joinOptOptNat_value
    (program : Program .optOptNat) (store : Store) :
    (eval (joinOptOptNat program) store).value =
      (eval program store).value.join := by
  rfl

@[simp] theorem eval_joinOptOptNat_trace
    (program : Program .optOptNat) (store : Store) :
    (eval (joinOptOptNat program) store).trace =
      (eval program store).trace := by
  rfl

@[simp] theorem eval_sampledRank_value
    (target : Bool) (offset : Nat)
    (sample : Program .optNat) (word : Program .optWord)
    (store : Store) :
    (eval (sampledRank target offset sample word) store).value =
      match (eval sample store).value, (eval word store).value with
      | some sampleValue, some wordValue =>
          sampleValue + RAM.boolRankPrefix target wordValue offset
      | _, _ => (0 : Nat) := by
  cases hsample : (eval sample store).value <;>
    cases hword : (eval word store).value <;>
      simp [eval, hsample, hword]

@[simp] theorem eval_sampledRank_trace
    (target : Bool) (offset : Nat)
    (sample : Program .optNat) (word : Program .optWord)
    (store : Store) :
    (eval (sampledRank target offset sample word) store).trace =
      match (eval sample store).value, (eval word store).value with
      | some _sampleValue, some wordValue =>
          (eval sample store).trace ++ (eval word store).trace ++
            [TraceEvent.wordRank target offset
              (RAM.boolRankPrefix target wordValue offset)]
      | _, _ => (eval sample store).trace ++ (eval word store).trace := by
  cases hsample : (eval sample store).value <;>
    cases hword : (eval word store).value <;>
      simp [eval, hsample, hword]

@[simp] theorem eval_wordSelectFromOpt_value
    (target : Bool) (occurrence : Nat)
    (word : Program .optWord) (store : Store) :
    (eval (wordSelectFromOpt target occurrence word) store).value =
      (eval word store).value.bind
        (fun wordValue => RAM.boolSelectInWord target wordValue occurrence) := by
  cases hword : (eval word store).value <;> simp [eval, hword]

@[simp] theorem eval_wordSelectFromOpt_trace
    (target : Bool) (occurrence : Nat)
    (word : Program .optWord) (store : Store) :
    (eval (wordSelectFromOpt target occurrence word) store).trace =
      match (eval word store).value with
      | none => (eval word store).trace
      | some wordValue =>
          (eval word store).trace ++
            [TraceEvent.wordSelect target occurrence
              (RAM.boolSelectInWord target wordValue occurrence)] := by
  cases hword : (eval word store).value <;>
    simp [eval, hword]

theorem eval_joinOptOptNat_toCosted_eq_map
    (program : Program .optOptNat) (store : Store) :
    (eval (joinOptOptNat program) store).toCosted =
      Costed.map (fun entry? => entry?.join)
        (eval program store).toCosted := by
  apply Costed.ext <;>
    simp [Result.toCosted, Result.steps, Costed.map, Costed.bind,
      Costed.pure]

/-- Cost is exactly the interpreted trace length. -/
theorem eval_toCosted_cost_eq_trace_length
    (program : Program ty) (store : Store) :
    (eval program store).toCosted.cost =
      (eval program store).trace.length := by
  rfl

/-- Every interpreted read event agrees with the payload store. -/
theorem eval_reads_subset_payload
    (program : Program ty) (store : Store) :
    forall event : TraceEvent,
      event ∈ (eval program store).trace ->
        event.matchesStore store := by
  induction program with
  | pure value =>
      intro event hmem
      simp [eval] at hmem
  | readWord segment index =>
      intro event hmem
      simp [eval] at hmem
      subst event
      rfl
  | mapOptWordNat program ih =>
      intro event hmem
      exact ih event hmem
  | mapOptWordOptionNat width program ih =>
      intro event hmem
      exact ih event hmem
  | joinOptOptNat program ih =>
      intro event hmem
      exact ih event hmem
  | sampledRank target offset sample word sampleIH wordIH =>
      intro event hmem
      cases hsample : (eval sample store).value with
      | none =>
          cases hword : (eval word store).value with
          | none =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | h
              · exact sampleIH event h
              · exact wordIH event h
          | some wordValue =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | h
              · exact sampleIH event h
              · exact wordIH event h
      | some sampleValue =>
          cases hword : (eval word store).value with
          | none =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | h
              · exact sampleIH event h
              · exact wordIH event h
          | some wordValue =>
              simp [eval, hsample, hword] at hmem
              rcases hmem with h | htail
              · exact sampleIH event h
              · rcases htail with h | h
                · exact wordIH event h
                · subst event
                  trivial
  | wordSelectFromOpt target occurrence word wordIH =>
      intro event hmem
      cases hword : (eval word store).value with
      | none =>
          simp [eval, hword] at hmem
          exact wordIH event hmem
      | some wordValue =>
          simp [eval, hword] at hmem
          rcases hmem with h | h
          · exact wordIH event h
          · subst event
            trivial

/--
Every word-read trace event reports exactly the word returned by the payload
store. This is the reviewer-facing specialization of
`eval_reads_subset_payload` for the only trace event that reads stored data.
-/
theorem eval_readWord_event_eq_store
    (program : Program ty) (store : Store)
    {segment index : Nat} {word? : Option Word}
    (hmem :
      TraceEvent.readWord segment index word? ∈
        (eval program store).trace) :
    store.readWord? segment index = word? := by
  exact eval_reads_subset_payload program store
    (TraceEvent.readWord segment index word?) hmem

/-- If the store is word-bounded, every word returned by the trace is bounded. -/
theorem eval_word_reads_length_le_machine
    (program : Program ty) (store : Store) {bound : Nat}
    (hbound : store.WordsBounded bound) :
    forall event : TraceEvent,
      event ∈ (eval program store).trace ->
        event.wordLengthBounded bound := by
  intro event hmem
  have hmatch := eval_reads_subset_payload program store event hmem
  cases event with
  | readWord segment index word? =>
      cases word? with
      | none =>
          simp [TraceEvent.wordLengthBounded]
      | some word =>
          exact hbound hmatch
  | wordRank target limit result =>
      simp [TraceEvent.wordLengthBounded]
  | wordSelect target occurrence result =>
      simp [TraceEvent.wordLengthBounded]

/--
Program evaluation is extensional in the payload-read interface. If two stores
return the same word for every segment/index read, then the interpreted value
and trace are identical. This is the main small anti-oracle lemma: a program can
depend on the store only through `Store.readWord?`.
-/
theorem eval_eq_of_readWord_eq
    (program : Program ty) {storeA storeB : Store}
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    eval program storeA = eval program storeB := by
  induction program with
  | pure value =>
      rfl
  | readWord segment index =>
      simp [eval, hread segment index]
  | mapOptWordNat program ih =>
      simp [eval, ih]
  | mapOptWordOptionNat width program ih =>
      simp [eval, ih]
  | joinOptOptNat program ih =>
      simp [eval, ih]
  | sampledRank target offset sample word sampleIH wordIH =>
      simp [eval, sampleIH, wordIH]
  | wordSelectFromOpt target occurrence word wordIH =>
      simp [eval, wordIH]

/-- The `Costed` projection of a program is also extensional in payload reads. -/
theorem eval_toCosted_eq_of_readWord_eq
    (program : Program ty) {storeA storeB : Store}
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    (eval program storeA).toCosted = (eval program storeB).toCosted := by
  rw [eval_eq_of_readWord_eq program hread]

end Program

end WordRAM

end RMQ
