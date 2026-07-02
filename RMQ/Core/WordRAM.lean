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

/--
A read-only payload-store interface for theorem surfaces that need to describe
one concrete store layout without committing to the array representation used
by the executable interpreter.
-/
structure ReadStore where
  readWord? : Nat -> Nat -> Option Word

namespace ReadStore

/-- Promote the executable array-backed store to the read-only interface. -/
def ofStore (store : Store) : ReadStore where
  readWord? := store.readWord?

/-- All dynamically readable words in the read-only store fit within `bound`. -/
def WordsBounded (store : ReadStore) (bound : Nat) : Prop :=
  forall {segment index : Nat} {word : Word},
    store.readWord? segment index = some word -> word.length <= bound

end ReadStore

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

/-- A trace event agrees with a read-only payload store view. -/
def matchesReadStore (store : ReadStore) : TraceEvent -> Prop
  | readWord segment index word? => store.readWord? segment index = word?
  | wordRank _ _ _ => True
  | wordSelect _ _ _ => True

/-- Any word returned by this event fits in `bound`. -/
def wordLengthBounded (bound : Nat) : TraceEvent -> Prop
  | readWord _ _ none => True
  | readWord _ _ (some word) => word.length <= bound
  | wordRank _ _ _ => True
  | wordSelect _ _ _ => True

/-- Whether a trace event is an actual payload-memory word read. -/
def isReadWord : TraceEvent -> Prop
  | readWord _ _ _ => True
  | wordRank _ _ _ => False
  | wordSelect _ _ _ => False

/-- Whether a trace event is a bounded-cost word primitive rather than a read. -/
def isWordPrimitive : TraceEvent -> Prop
  | readWord _ _ _ => False
  | wordRank _ _ _ => True
  | wordSelect _ _ _ => True

@[simp] theorem matchesReadStore_ofStore
    (store : Store) (event : TraceEvent) :
    event.matchesReadStore (ReadStore.ofStore store) =
      event.matchesStore store := by
  cases event <;> rfl

/--
Shift payload-read segment identifiers by a fixed offset.

Word-local primitive events are left unchanged. This is the basic operation
needed to assemble component-local traces into one global payload-store trace.
-/
def relabelReadSegment (offset : Nat) : TraceEvent -> TraceEvent
  | readWord segment index word? => readWord (offset + segment) index word?
  | wordRank target limit result => wordRank target limit result
  | wordSelect target occurrence result =>
      wordSelect target occurrence result

/--
Relabel payload-read segment identifiers through an arbitrary segment map.

This is the finite-layout version of `relabelReadSegment`: one-segment tables,
three-segment rank structures, and shared BP-code stores can each map their
small local segment set into a global layout without giving the component an
infinite offset range.
-/
def relabelReadSegmentWith (segmentMap : Nat -> Nat) :
    TraceEvent -> TraceEvent
  | readWord segment index word? => readWord (segmentMap segment) index word?
  | wordRank target limit result => wordRank target limit result
  | wordSelect target occurrence result =>
      wordSelect target occurrence result

/-- Map a one-segment local store into a global segment, sending unused local
segments to a designated dead segment. -/
def singletonSegmentMap (base dead : Nat) : Nat -> Nat
  | 0 => base
  | _ + 1 => dead

/-- Map a two-segment local store into adjacent global segments. -/
def pairSegmentMap (base dead : Nat) : Nat -> Nat
  | 0 => base
  | 1 => base + 1
  | _ + 2 => dead

/-- Map a three-segment local store into adjacent global segments. -/
def tripleSegmentMap (base dead : Nat) : Nat -> Nat
  | 0 => base
  | 1 => base + 1
  | 2 => base + 2
  | _ + 3 => dead

@[simp] theorem relabelReadSegment_isReadWord
    (offset : Nat) (event : TraceEvent) :
    (event.relabelReadSegment offset).isReadWord = event.isReadWord := by
  cases event <;> simp [relabelReadSegment, isReadWord]

@[simp] theorem relabelReadSegment_isWordPrimitive
    (offset : Nat) (event : TraceEvent) :
    (event.relabelReadSegment offset).isWordPrimitive =
      event.isWordPrimitive := by
  cases event <;> simp [relabelReadSegment, isWordPrimitive]

@[simp] theorem relabelReadSegmentWith_isReadWord
    (segmentMap : Nat -> Nat) (event : TraceEvent) :
    (event.relabelReadSegmentWith segmentMap).isReadWord =
      event.isReadWord := by
  cases event <;> simp [relabelReadSegmentWith, isReadWord]

@[simp] theorem relabelReadSegmentWith_isWordPrimitive
    (segmentMap : Nat -> Nat) (event : TraceEvent) :
    (event.relabelReadSegmentWith segmentMap).isWordPrimitive =
      event.isWordPrimitive := by
  cases event <;> simp [relabelReadSegmentWith, isWordPrimitive]

theorem isReadWord_or_isWordPrimitive (event : TraceEvent) :
    event.isReadWord \/ event.isWordPrimitive := by
  cases event <;> simp [isReadWord, isWordPrimitive]

@[simp] theorem relabelReadSegment_wordLengthBounded
    (offset bound : Nat) (event : TraceEvent) :
    (event.relabelReadSegment offset).wordLengthBounded bound ↔
      event.wordLengthBounded bound := by
  cases event with
  | readWord segment index word? =>
      cases word? <;> simp [relabelReadSegment, wordLengthBounded]
  | wordRank target limit result =>
      simp [relabelReadSegment, wordLengthBounded]
  | wordSelect target occurrence result =>
      simp [relabelReadSegment, wordLengthBounded]

theorem relabelReadSegment_matchesReadStore
    (localStore globalStore : ReadStore) (offset : Nat)
    (hread :
      forall segment index,
        globalStore.readWord? (offset + segment) index =
          localStore.readWord? segment index)
    (event : TraceEvent)
    (hmatch : event.matchesReadStore localStore) :
    (event.relabelReadSegment offset).matchesReadStore globalStore := by
  cases event with
  | readWord segment index word? =>
      simp [relabelReadSegment, matchesReadStore, hread segment index]
      exact hmatch
  | wordRank target limit result =>
      simp [relabelReadSegment, matchesReadStore]
  | wordSelect target occurrence result =>
      simp [relabelReadSegment, matchesReadStore]

theorem relabelReadSegmentWith_matchesReadStore
    (localStore globalStore : ReadStore) (segmentMap : Nat -> Nat)
    (hread :
      forall segment index,
        globalStore.readWord? (segmentMap segment) index =
          localStore.readWord? segment index)
    (event : TraceEvent)
    (hmatch : event.matchesReadStore localStore) :
    (event.relabelReadSegmentWith segmentMap).matchesReadStore
      globalStore := by
  cases event with
  | readWord segment index word? =>
      simp [relabelReadSegmentWith, matchesReadStore, hread segment index]
      exact hmatch
  | wordRank target limit result =>
      simp [relabelReadSegmentWith, matchesReadStore]
  | wordSelect target occurrence result =>
      simp [relabelReadSegmentWith, matchesReadStore]

end TraceEvent

/-- Map a one-segment local store into a global segment, sending unused local
segments to a designated dead segment. -/
def singletonSegmentMap (base dead : Nat) : Nat -> Nat :=
  TraceEvent.singletonSegmentMap base dead

/-- Map a two-segment local store into adjacent global segments. -/
def pairSegmentMap (base dead : Nat) : Nat -> Nat :=
  TraceEvent.pairSegmentMap base dead

/-- Map a three-segment local store into adjacent global segments. -/
def tripleSegmentMap (base dead : Nat) : Nat -> Nat :=
  TraceEvent.tripleSegmentMap base dead

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
Polymorphic interpreted result for larger components whose values are not part
of the small first-order `Ty` universe, but whose operational evidence is still
a plain `WordRAM.TraceEvent` stream.
-/
structure TraceResult (α : Type u) where
  value : α
  trace : List TraceEvent

namespace TraceResult

/-- Operational step count, derived from the trace. -/
def steps (result : TraceResult α) : Nat := result.trace.length

/-- Project an interpreted trace result into the theorem-facing cost carrier. -/
def toCosted (result : TraceResult α) : Costed α where
  value := result.value
  cost := result.steps

/-- Lift a typed first-order result into the polymorphic trace carrier. -/
def ofResult {ty : Ty} (result : Result ty) :
    TraceResult ty.denote where
  value := result.value
  trace := result.trace

/-- Zero-step trace result. -/
def pure (value : α) : TraceResult α where
  value := value
  trace := []

/-- Sequential composition concatenates traces. -/
def bind (result : TraceResult α) (f : α -> TraceResult β) :
    TraceResult β :=
  let next := f result.value
  { value := next.value, trace := result.trace ++ next.trace }

/-- Pure map over an interpreted trace result. -/
def map (f : α -> β) (result : TraceResult α) : TraceResult β :=
  bind result (fun value => pure (f value))

/--
Shift all payload-read segments in a trace result by a fixed offset, preserving
the erased value and trace length.
-/
def relabelReadSegments {alpha : Type u} (offset : Nat)
    (result : TraceResult alpha) : TraceResult alpha where
  value := result.value
  trace := result.trace.map (fun event => event.relabelReadSegment offset)

/-- Relabel all payload-read segments in a trace result through a segment map. -/
def relabelReadSegmentsWith {alpha : Type u} (segmentMap : Nat -> Nat)
    (result : TraceResult alpha) : TraceResult alpha where
  value := result.value
  trace := result.trace.map (fun event =>
    event.relabelReadSegmentWith segmentMap)

/--
Canonical cost-only trace used when an older `Costed` component has not yet
been replayed through a first-order payload program.  The events are word
primitive events, not payload reads; theorem names using this constructor should
not claim payload-read completeness.
-/
def costOnlyTrace : Nat -> List TraceEvent
  | 0 => []
  | n + 1 => TraceEvent.wordRank false 0 0 :: costOnlyTrace n

@[simp] theorem costOnlyTrace_length (n : Nat) :
    (costOnlyTrace n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [costOnlyTrace, ih]

/--
Synthetic `Costed` adapter traces contain only word-primitive events, never
payload-memory reads.
-/
theorem costOnlyTrace_no_readWord (n : Nat) :
    forall event : TraceEvent,
      event ∈ costOnlyTrace n -> ¬ event.isReadWord := by
  induction n with
  | zero =>
      intro event hmem
      simp [costOnlyTrace] at hmem
  | succ n ih =>
      intro event hmem
      simp [costOnlyTrace] at hmem
      rcases hmem with hmem | hmem
      · subst event
        simp [TraceEvent.isReadWord]
      · exact ih event hmem

/-- Lift an existing `Costed` result to a trace result using `costOnlyTrace`. -/
def ofCosted (result : Costed α) : TraceResult α where
  value := result.value
  trace := costOnlyTrace result.cost

@[simp] theorem pure_value (value : α) :
    (pure value : TraceResult α).value = value := by
  rfl

@[simp] theorem pure_trace (value : α) :
    (pure value : TraceResult α).trace = [] := by
  rfl

@[simp] theorem bind_value (result : TraceResult α)
    (f : α -> TraceResult β) :
    (bind result f).value = (f result.value).value := by
  rfl

@[simp] theorem bind_trace (result : TraceResult α)
    (f : α -> TraceResult β) :
    (bind result f).trace = result.trace ++ (f result.value).trace := by
  rfl

@[simp] theorem map_value (f : α -> β) (result : TraceResult α) :
    (map f result).value = f result.value := by
  rfl

@[simp] theorem map_trace (f : α -> β) (result : TraceResult α) :
    (map f result).trace = result.trace := by
  simp [map, bind, pure]

@[simp] theorem relabelReadSegments_value
    {alpha : Type u} (offset : Nat) (result : TraceResult alpha) :
    (relabelReadSegments offset result).value = result.value := by
  rfl

@[simp] theorem relabelReadSegments_trace
    {alpha : Type u} (offset : Nat) (result : TraceResult alpha) :
    (relabelReadSegments offset result).trace =
      result.trace.map (fun event => event.relabelReadSegment offset) := by
  rfl

@[simp] theorem relabelReadSegmentsWith_value
    {alpha : Type u} (segmentMap : Nat -> Nat)
    (result : TraceResult alpha) :
    (relabelReadSegmentsWith segmentMap result).value = result.value := by
  rfl

@[simp] theorem relabelReadSegmentsWith_trace
    {alpha : Type u} (segmentMap : Nat -> Nat)
    (result : TraceResult alpha) :
    (relabelReadSegmentsWith segmentMap result).trace =
      result.trace.map (fun event =>
        event.relabelReadSegmentWith segmentMap) := by
  rfl

@[simp] theorem ofResult_value {ty : Ty} (result : Result ty) :
    (ofResult result).value = result.value := by
  rfl

@[simp] theorem ofResult_trace {ty : Ty} (result : Result ty) :
    (ofResult result).trace = result.trace := by
  rfl

@[simp] theorem ofCosted_toCosted (result : Costed α) :
    (ofCosted result).toCosted = result := by
  apply Costed.ext <;>
    simp [ofCosted, toCosted, steps]

theorem ofCosted_trace_no_readWord (result : Costed α) :
    forall event : TraceEvent,
      event ∈ (ofCosted result).trace -> ¬ event.isReadWord := by
  intro event hmem
  exact costOnlyTrace_no_readWord result.cost event hmem

theorem ofCosted_matchesReadStore (result : Costed α) (store : ReadStore) :
    forall event : TraceEvent,
      event ∈ (ofCosted result).trace -> event.matchesReadStore store := by
  intro event hmem
  have hnotRead := ofCosted_trace_no_readWord result event hmem
  cases event <;> simp [TraceEvent.matchesReadStore, TraceEvent.isReadWord] at hnotRead ⊢

@[simp] theorem toCosted_value (result : TraceResult α) :
    result.toCosted.value = result.value := by
  rfl

@[simp] theorem toCosted_cost_eq_trace_length (result : TraceResult α) :
    result.toCosted.cost = result.trace.length := by
  rfl

@[simp] theorem ofResult_toCosted {ty : Ty} (result : Result ty) :
    (ofResult result).toCosted = result.toCosted := by
  rfl

@[simp] theorem pure_toCosted (value : α) :
    (pure value).toCosted = Costed.pure value := by
  rfl

@[simp] theorem bind_toCosted (result : TraceResult α)
    (f : α -> TraceResult β) :
    (bind result f).toCosted =
      Costed.bind result.toCosted (fun value => (f value).toCosted) := by
  apply Costed.ext <;>
    simp [bind, toCosted, steps, Costed.bind, List.length_append]

@[simp] theorem map_toCosted (f : α -> β) (result : TraceResult α) :
    (map f result).toCosted =
      Costed.map f result.toCosted := by
  rw [map, bind_toCosted]
  rfl

@[simp] theorem relabelReadSegments_toCosted
    {alpha : Type u} (offset : Nat) (result : TraceResult alpha) :
    (relabelReadSegments offset result).toCosted = result.toCosted := by
  apply Costed.ext <;>
    simp [relabelReadSegments, toCosted, steps]

@[simp] theorem relabelReadSegmentsWith_toCosted
    {alpha : Type u} (segmentMap : Nat -> Nat)
    (result : TraceResult alpha) :
    (relabelReadSegmentsWith segmentMap result).toCosted =
      result.toCosted := by
  apply Costed.ext <;>
    simp [relabelReadSegmentsWith, toCosted, steps]

/-- Zero-step trace results satisfy any event invariant. -/
theorem pure_trace_forall
    (P : TraceEvent -> Prop) (value : alpha) :
    forall event,
      event ∈ (pure value : TraceResult alpha).trace -> P event := by
  intro event hmem
  simp at hmem

/-- Sequential traces preserve event invariants componentwise. -/
theorem bind_trace_forall
    (P : TraceEvent -> Prop)
    (result : TraceResult alpha) (f : alpha -> TraceResult beta)
    (hresult :
      forall event, event ∈ result.trace -> P event)
    (hnext :
      forall event, event ∈ (f result.value).trace -> P event) :
    forall event,
      event ∈ (bind result f).trace -> P event := by
  intro event hmem
  simp [bind] at hmem
  rcases hmem with hmem | hmem
  · exact hresult event hmem
  · exact hnext event hmem

/-- Pure maps do not change the event invariant of a trace. -/
theorem map_trace_forall
    (P : TraceEvent -> Prop) (f : alpha -> beta)
    (result : TraceResult alpha)
    (hresult :
      forall event, event ∈ result.trace -> P event) :
    forall event,
      event ∈ (map f result).trace -> P event := by
  intro event hmem
  simp [map] at hmem
  exact hresult event hmem

/-- Fixed-offset relabeling preserves read-store agreement. -/
theorem relabelReadSegments_matchesReadStore
    {alpha : Type u} (result : TraceResult alpha)
    (localStore globalStore : ReadStore) (offset : Nat)
    (hread :
      forall segment index,
        globalStore.readWord? (offset + segment) index =
          localStore.readWord? segment index)
    (hresult :
      forall event,
        event ∈ result.trace -> event.matchesReadStore localStore) :
    forall event,
      event ∈ (relabelReadSegments offset result).trace ->
        event.matchesReadStore globalStore := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, hlocal, rfl⟩
  exact TraceEvent.relabelReadSegment_matchesReadStore
    localStore globalStore offset hread localEvent
    (hresult localEvent hlocal)

/-- Segment-map relabeling preserves read-store agreement. -/
theorem relabelReadSegmentsWith_matchesReadStore
    {alpha : Type u} (result : TraceResult alpha)
    (localStore globalStore : ReadStore) (segmentMap : Nat -> Nat)
    (hread :
      forall segment index,
        globalStore.readWord? (segmentMap segment) index =
          localStore.readWord? segment index)
    (hresult :
      forall event,
        event ∈ result.trace -> event.matchesReadStore localStore) :
    forall event,
      event ∈ (relabelReadSegmentsWith segmentMap result).trace ->
        event.matchesReadStore globalStore := by
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, hlocal, rfl⟩
  exact TraceEvent.relabelReadSegmentWith_matchesReadStore
    localStore globalStore segmentMap hread localEvent
    (hresult localEvent hlocal)

end TraceResult

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

theorem eval_reads_subset_readStore
    (program : Program ty) (store : Store) :
    forall event : TraceEvent,
      event ∈ (eval program store).trace ->
        event.matchesReadStore (ReadStore.ofStore store) := by
  intro event hmem
  simpa [TraceEvent.matchesReadStore_ofStore] using
    eval_reads_subset_payload program store event hmem

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
