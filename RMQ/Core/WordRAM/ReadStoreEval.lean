import RMQ.Core.WordRAM.Register

/-!
# ReadStore-parameterized evaluation

The leaf interpreters (`Program.eval`, `Register.RegProgram.eval`,
`Register.NatProgram.eval`) evaluate against the executable array-backed
`Store`.  The whole-query store-parametric layer needs the same evaluation
against the read-only `ReadStore` interface, so that a query evaluator can be a
genuine function of a supplied payload-read store.

This module adds the `ReadStore` mirrors (`evalR`) of the three first-order
evaluators, the segment-map pullback used to run a component-local program
against a global store, and the two lemmas every store-parametric leaf uses:

* `evalR_ofStore` — the mirror agrees with the executable interpreter; and
* `pullback` extensionality — if a global read store agrees with a component's
  local store along the component's segment map, evaluating the component's
  program against the pulled-back global store is literally evaluating it
  against the local store.

The trust direction is unchanged: programs are still first-order syntax, values
still come only from `readWord?` and word-local primitives, and the `Costed`
projection still happens after interpretation.
-/

namespace RMQ

namespace WordRAM

namespace ReadStore

/-- Read stores with the same read interface are equal. -/
theorem ext {storeA storeB : ReadStore}
    (hread :
      forall segment index,
        storeA.readWord? segment index = storeB.readWord? segment index) :
    storeA = storeB := by
  cases storeA with
  | mk readA =>
      cases storeB with
      | mk readB =>
          have hfun : readA = readB := by
            funext segment index
            exact hread segment index
          rw [hfun]

/-- Pull a read store back along a segment relabeling map: local segment
`segment` reads global segment `segmentMap segment`. -/
def pullback (segmentMap : Nat -> Nat) (store : ReadStore) : ReadStore where
  readWord? := fun segment index =>
    store.readWord? (segmentMap segment) index

@[simp] theorem pullback_readWord?
    (segmentMap : Nat -> Nat) (store : ReadStore)
    (segment index : Nat) :
    (store.pullback segmentMap).readWord? segment index =
      store.readWord? (segmentMap segment) index := by
  rfl

/--
If a global read store agrees with a component-local store along the
component's segment map, the pulled-back global store is the local store's
read interface.
-/
theorem pullback_eq_ofStore_of_agree
    (segmentMap : Nat -> Nat) (global : ReadStore) (localStore : Store)
    (hagree :
      forall segment index,
        global.readWord? (segmentMap segment) index =
          localStore.readWord? segment index) :
    global.pullback segmentMap = ReadStore.ofStore localStore := by
  apply ext
  intro segment index
  simpa [pullback, ofStore] using hagree segment index

/--
Two read stores agreeing on every segment in a map's image have equal
pullbacks.  This is the whole-query parametricity workhorse: a query touching
only mapped segments cannot distinguish the two stores.
-/
theorem pullback_eq_of_agree_on_map
    (segmentMap : Nat -> Nat) {storeA storeB : ReadStore}
    (hagree :
      forall segment index,
        storeA.readWord? (segmentMap segment) index =
          storeB.readWord? (segmentMap segment) index) :
    storeA.pullback segmentMap = storeB.pullback segmentMap := by
  apply ext
  intro segment index
  simpa [pullback] using hagree segment index

end ReadStore

namespace TraceEvent

/--
Relabeling transports pullback-store agreement to the global store: an event
that matches the pulled-back store matches the global store once its segment is
relabeled through the same map.
-/
theorem relabelReadSegmentWith_matchesReadStore_of_pullback
    (segmentMap : Nat -> Nat) (store : ReadStore) {event : TraceEvent}
    (hmatch : event.matchesReadStore (store.pullback segmentMap)) :
    (event.relabelReadSegmentWith segmentMap).matchesReadStore store := by
  cases event with
  | readWord segment index word? =>
      simpa [relabelReadSegmentWith, matchesReadStore,
        ReadStore.pullback] using hmatch
  | wordRank target limit result =>
      trivial
  | wordSelect target occurrence result =>
      trivial
  | syntheticCostOnlyPrimitive =>
      trivial

end TraceEvent

namespace Program

/-- ReadStore-parameterized mirror of `Program.eval`. -/
def evalR : Program ty -> ReadStore -> Result ty
  | pure value, _store => { value := value, trace := [] }
  | readWord segment index, store =>
      let word? := store.readWord? segment index
      { value := word?, trace := [TraceEvent.readWord segment index word?] }
  | mapOptWordNat program, store =>
      let result := evalR program store
      { value := result.value.map bitsToNatLE, trace := result.trace }
  | mapOptWordOptionNat width program, store =>
      let result := evalR program store
      { value := result.value.map (bitsToOptionNatLE width)
        trace := result.trace }
  | joinOptOptNat program, store =>
      let result := evalR program store
      { value := result.value.join, trace := result.trace }
  | sampledRank target offset sample word, store =>
      let sampleResult := evalR sample store
      let wordResult := evalR word store
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
      let wordResult := evalR word store
      match wordResult.value with
      | none =>
          { value := none, trace := wordResult.trace }
      | some wordValue =>
          let selected := RAM.boolSelectInWord target wordValue occurrence
          { value := selected
            trace :=
              wordResult.trace ++
                [TraceEvent.wordSelect target occurrence selected] }

/-- The ReadStore mirror agrees with the executable interpreter. -/
theorem evalR_ofStore (program : Program ty) (store : Store) :
    program.evalR (ReadStore.ofStore store) = program.eval store := by
  induction program with
  | pure value =>
      rfl
  | readWord segment index =>
      rfl
  | mapOptWordNat program ih =>
      simp [evalR, eval, ih]
  | mapOptWordOptionNat width program ih =>
      simp [evalR, eval, ih]
  | joinOptOptNat program ih =>
      simp [evalR, eval, ih]
  | sampledRank target offset sample word sampleIH wordIH =>
      cases hsample : (Program.eval sample store).value <;>
        cases hword : (Program.eval word store).value <;>
          simp [evalR, eval, sampleIH, wordIH, hsample, hword]
  | wordSelectFromOpt target occurrence word wordIH =>
      cases hword : (Program.eval word store).value <;>
        simp [evalR, eval, wordIH, hword]

/-- Every read event in an interpreted `evalR` trace agrees with the supplied
read store, for every store. -/
theorem evalR_matchesReadStore
    (program : Program ty) (store : ReadStore) :
    forall event : TraceEvent,
      event ∈ (program.evalR store).trace ->
        event.matchesReadStore store := by
  induction program with
  | pure value =>
      intro event hmem
      simp [evalR] at hmem
  | readWord segment index =>
      intro event hmem
      simp [evalR] at hmem
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
      cases hsample : (evalR sample store).value with
      | none =>
          cases hword : (evalR word store).value with
          | none =>
              simp [evalR, hsample, hword] at hmem
              rcases hmem with h | h
              · exact sampleIH event h
              · exact wordIH event h
          | some wordValue =>
              simp [evalR, hsample, hword] at hmem
              rcases hmem with h | h
              · exact sampleIH event h
              · exact wordIH event h
      | some sampleValue =>
          cases hword : (evalR word store).value with
          | none =>
              simp [evalR, hsample, hword] at hmem
              rcases hmem with h | h
              · exact sampleIH event h
              · exact wordIH event h
          | some wordValue =>
              simp [evalR, hsample, hword] at hmem
              rcases hmem with h | htail
              · exact sampleIH event h
              · rcases htail with h | h
                · exact wordIH event h
                · subst event
                  trivial
  | wordSelectFromOpt target occurrence word wordIH =>
      intro event hmem
      cases hword : (evalR word store).value with
      | none =>
          simp [evalR, hword] at hmem
          exact wordIH event hmem
      | some wordValue =>
          simp [evalR, hword] at hmem
          rcases hmem with h | h
          · exact wordIH event h
          · subst event
            trivial

/--
The one-step atom lemma for store-parametric leaves: evaluating a component
program against a global store pulled back along the component's segment map is
evaluating it against the component's own local store, whenever the two agree
along that map.
-/
theorem evalR_pullback_eq_eval
    (program : Program ty) (segmentMap : Nat -> Nat)
    (global : ReadStore) (localStore : Store)
    (hagree :
      forall segment index,
        global.readWord? (segmentMap segment) index =
          localStore.readWord? segment index) :
    program.evalR (global.pullback segmentMap) = program.eval localStore := by
  rw [ReadStore.pullback_eq_ofStore_of_agree segmentMap global localStore hagree,
    evalR_ofStore]

end Program

namespace Register

namespace RegProgram

/-- ReadStore-parameterized mirror of `RegProgram.eval`. -/
def evalR : RegProgram -> ReadStore -> RegFile -> Result .optNat
  | pureOpt value, _store, regs =>
      { value := value.eval regs, trace := [] }
  | readJoinedOptionNat segment width index, store, regs =>
      let i := index.eval regs
      let word? := store.readWord? segment i
      { value := (word?.map (bitsToOptionNatLE width)).join
        trace := [TraceEvent.readWord segment i word?] }
  | ifSomeNat reg thenProgram elseProgram, store, regs =>
      match regs.optNat reg with
      | some _ => thenProgram.evalR store regs
      | none => elseProgram.evalR store regs

/-- The ReadStore mirror agrees with the executable interpreter. -/
theorem evalR_ofStore (program : RegProgram) (store : Store)
    (regs : RegFile) :
    program.evalR (ReadStore.ofStore store) regs = program.eval store regs := by
  induction program with
  | pureOpt value =>
      rfl
  | readJoinedOptionNat segment width index =>
      rfl
  | ifSomeNat reg thenProgram elseProgram thenIH elseIH =>
      cases hreg : regs.optNat reg with
      | none =>
          simpa [evalR, eval, hreg] using elseIH
      | some value =>
          simpa [evalR, eval, hreg] using thenIH

/-- Every read event in an interpreted `evalR` trace agrees with the supplied
read store, for every store. -/
theorem evalR_matchesReadStore
    (program : RegProgram) (store : ReadStore) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (program.evalR store regs).trace ->
        event.matchesReadStore store := by
  induction program with
  | pureOpt value =>
      intro event hmem
      simp [evalR] at hmem
  | readJoinedOptionNat segment width index =>
      intro event hmem
      simp [evalR] at hmem
      subst event
      rfl
  | ifSomeNat reg thenProgram elseProgram thenIH elseIH =>
      intro event hmem
      cases hreg : regs.optNat reg with
      | none =>
          exact elseIH event (by simpa [evalR, hreg] using hmem)
      | some value =>
          exact thenIH event (by simpa [evalR, hreg] using hmem)

/-- Atom lemma for register-program leaves. -/
theorem evalR_pullback_eq_eval
    (program : RegProgram) (segmentMap : Nat -> Nat)
    (global : ReadStore) (localStore : Store) (regs : RegFile)
    (hagree :
      forall segment index,
        global.readWord? (segmentMap segment) index =
          localStore.readWord? segment index) :
    program.evalR (global.pullback segmentMap) regs =
      program.eval localStore regs := by
  rw [ReadStore.pullback_eq_ofStore_of_agree segmentMap global localStore hagree,
    evalR_ofStore]

end RegProgram

namespace NatProgram

/-- ReadStore-parameterized mirror of `NatProgram.eval`. -/
def evalR : NatProgram -> ReadStore -> RegFile -> Result .nat
  | pureNat value, _store, regs =>
      { value := value.eval regs, trace := [] }
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex, store, regs =>
      let sampleI := sampleIndex.eval regs
      let wordI := wordIndex.eval regs
      let sampleWord? := store.readWord? sampleSegment sampleI
      let word? := store.readWord? wordSegment wordI
      let sample? := sampleWord?.map bitsToNatLE
      match sample?, word? with
      | some sample, some word =>
          let localRank := RAM.boolRankPrefix target word (offset.eval regs)
          { value := sample + localRank
            trace :=
              [TraceEvent.readWord sampleSegment sampleI sampleWord?,
                TraceEvent.readWord wordSegment wordI word?,
                TraceEvent.wordRank target (offset.eval regs) localRank] }
      | _, _ =>
          { value := (0 : Nat)
            trace :=
              [TraceEvent.readWord sampleSegment sampleI sampleWord?,
                TraceEvent.readWord wordSegment wordI word?] }
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex, store, regs =>
      let superI := superIndex.eval regs
      let blockI := blockIndex.eval regs
      let wordI := wordIndex.eval regs
      let superWord? := store.readWord? superSegment superI
      let blockWord? := store.readWord? blockSegment blockI
      let word? := store.readWord? wordSegment wordI
      let super? := superWord?.map bitsToNatLE
      let block? := blockWord?.map bitsToNatLE
      match super?, block?, word? with
      | some super, some block, some word =>
          let localRank := RAM.boolRankPrefix target word (offset.eval regs)
          { value := super + block + localRank
            trace :=
              [TraceEvent.readWord superSegment superI superWord?,
                TraceEvent.readWord blockSegment blockI blockWord?,
                TraceEvent.readWord wordSegment wordI word?,
                TraceEvent.wordRank target (offset.eval regs) localRank] }
      | _, _, _ =>
          { value := (0 : Nat)
            trace :=
              [TraceEvent.readWord superSegment superI superWord?,
                TraceEvent.readWord blockSegment blockI blockWord?,
                TraceEvent.readWord wordSegment wordI word?] }

/-- The ReadStore mirror agrees with the executable interpreter. -/
theorem evalR_ofStore (program : NatProgram) (store : Store)
    (regs : RegFile) :
    program.evalR (ReadStore.ofStore store) regs = program.eval store regs := by
  cases program with
  | pureNat value =>
      rfl
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex =>
      cases hsample :
          store.readWord? sampleSegment (sampleIndex.eval regs) <;>
        cases hword :
          store.readWord? wordSegment (wordIndex.eval regs) <;>
          simp [evalR, eval, ReadStore.ofStore, hsample, hword]
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex =>
      cases hsuper :
          store.readWord? superSegment (superIndex.eval regs) <;>
        cases hblock :
          store.readWord? blockSegment (blockIndex.eval regs) <;>
          cases hword :
            store.readWord? wordSegment (wordIndex.eval regs) <;>
            simp [evalR, eval, ReadStore.ofStore, hsuper, hblock, hword]

/-- Every read event in an interpreted `evalR` trace agrees with the supplied
read store, for every store. -/
theorem evalR_matchesReadStore
    (program : NatProgram) (store : ReadStore) (regs : RegFile) :
    forall event : TraceEvent,
      event ∈ (program.evalR store regs).trace ->
        event.matchesReadStore store := by
  cases program with
  | pureNat value =>
      intro event hmem
      simp [evalR] at hmem
  | sampledRank target offset sampleSegment sampleIndex
      wordSegment wordIndex =>
      intro event hmem
      cases hsample :
          store.readWord? sampleSegment (sampleIndex.eval regs) with
      | none =>
          cases hword :
              store.readWord? wordSegment (wordIndex.eval regs) <;>
            simp [evalR, hsample, hword] at hmem <;>
            (rcases hmem with h | h
             · subst event
               exact hsample
             · subst event
               exact hword)
      | some sampleWord =>
          cases hword :
              store.readWord? wordSegment (wordIndex.eval regs) with
          | none =>
              simp [evalR, hsample, hword] at hmem
              rcases hmem with h | h
              · subst event
                exact hsample
              · subst event
                exact hword
          | some word =>
              simp [evalR, hsample, hword] at hmem
              rcases hmem with h | htail
              · subst event
                exact hsample
              · rcases htail with h | h
                · subst event
                  exact hword
                · subst event
                  trivial
  | twoLevelSampledRank target offset superSegment superIndex
      blockSegment blockIndex wordSegment wordIndex =>
      intro event hmem
      cases hsuper :
          store.readWord? superSegment (superIndex.eval regs) with
      | none =>
          cases hblock :
              store.readWord? blockSegment (blockIndex.eval regs) <;>
            cases hword :
              store.readWord? wordSegment (wordIndex.eval regs) <;>
            simp [evalR, hsuper, hblock, hword] at hmem <;>
            (rcases hmem with h | htail
             · subst event
               exact hsuper
             · rcases htail with h | h
               · subst event
                 exact hblock
               · subst event
                 exact hword)
      | some superWord =>
          cases hblock :
              store.readWord? blockSegment (blockIndex.eval regs) with
          | none =>
              cases hword :
                  store.readWord? wordSegment (wordIndex.eval regs) <;>
                simp [evalR, hsuper, hblock, hword] at hmem <;>
                (rcases hmem with h | htail
                 · subst event
                   exact hsuper
                 · rcases htail with h | h
                   · subst event
                     exact hblock
                   · subst event
                     exact hword)
          | some blockWord =>
              cases hword :
                  store.readWord? wordSegment (wordIndex.eval regs) with
              | none =>
                  simp [evalR, hsuper, hblock, hword] at hmem
                  rcases hmem with h | htail
                  · subst event
                    exact hsuper
                  · rcases htail with h | h
                    · subst event
                      exact hblock
                    · subst event
                      exact hword
              | some word =>
                  simp [evalR, hsuper, hblock, hword] at hmem
                  rcases hmem with h | htail
                  · subst event
                    exact hsuper
                  · rcases htail with h | htail
                    · subst event
                      exact hblock
                    · rcases htail with h | h
                      · subst event
                        exact hword
                      · subst event
                        trivial

/-- Atom lemma for natural-register-program leaves. -/
theorem evalR_pullback_eq_eval
    (program : NatProgram) (segmentMap : Nat -> Nat)
    (global : ReadStore) (localStore : Store) (regs : RegFile)
    (hagree :
      forall segment index,
        global.readWord? (segmentMap segment) index =
          localStore.readWord? segment index) :
    program.evalR (global.pullback segmentMap) regs =
      program.eval localStore regs := by
  rw [ReadStore.pullback_eq_ofStore_of_agree segmentMap global localStore hagree,
    evalR_ofStore]

end NatProgram

end Register

end WordRAM

end RMQ
