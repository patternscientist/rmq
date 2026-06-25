import RMQ.Core.SuccinctSelectProposal

/-!
# Generic select directory: target-threaded decode primitives (Tier 0/1)

Generic `(target : Bool)` analogues of the BP-specialised (`false`-hardcoded)
decode primitives in `SuccinctSelectProposal` (e.g. `denseTwoWordFalseSelectCosted`,
`falseSelectPositions`).  These already operate over an arbitrary `bits : List Bool`;
the only change is replacing the hardcoded `false` in the charged
`RAM.rankBoolWordPrefix` / `RAM.selectBoolWord` calls with `target`.  Pure
arithmetic slot/position helpers (`falseSelectSuperSlot`, the `relativeSplitFalseSelect*`
slot maths) are already target-agnostic and are reused directly.
-/

namespace RMQ.GenericSelect

open RMQ.SuccinctSelectProposal SuccinctSpace SuccinctRankProposal

/--
Generic two-word select decode: find the `(q - baseOccurrence)`-th `target` bit
at or after `basePosition`, reading at most two payload words and using the
charged `RAM.rankBoolWordPrefix`/`RAM.selectBoolWord` primitives.  This is
`denseTwoWordFalseSelectCosted` (SuccinctSelectProposal) with the hardcoded
`false` replaced by `target`; it already operated over an arbitrary
`bits : List Bool`.
-/
def denseTwoWordSelectCosted
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind (bitWords.store.readWordCosted firstWordIndex) fun firstWord? =>
    match firstWord? with
    | none => Costed.pure none
    | some firstWord =>
        Costed.bind
          (RMQ.RAM.rankBoolWordPrefix target firstWord firstOffset).toCosted
          fun beforeFirst =>
            Costed.bind
              (RMQ.RAM.rankBoolWordPrefix
                target firstWord firstWord.length).toCosted
              fun uptoFirst =>
                let firstCount := uptoFirst - beforeFirst
                if localOccurrence < firstCount then
                  Costed.map
                    (fun local? =>
                      local?.map fun offset => firstWordStart + offset)
                    (RMQ.RAM.selectBoolWord target firstWord
                      (beforeFirst + localOccurrence)).toCosted
                else
                  Costed.bind
                    (bitWords.store.readWordCosted (firstWordIndex + 1))
                    fun secondWord? =>
                      match secondWord? with
                      | none => Costed.pure none
                      | some secondWord =>
                          Costed.map
                            (fun local? =>
                              local?.map fun offset =>
                                (firstWordIndex + 1) * wordSize + offset)
                            (RMQ.RAM.selectBoolWord target secondWord
                              (localOccurrence - firstCount)).toCosted

/-- The BP-specialised primitive is the `target := false` instance. -/
theorem denseTwoWordFalseSelectCosted_eq
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    denseTwoWordFalseSelectCosted bitWords basePosition baseOccurrence q =
      denseTwoWordSelectCosted false bitWords basePosition baseOccurrence q :=
  rfl

theorem denseTwoWordSelectCosted_cost_le_five
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (denseTwoWordSelectCosted
      target bitWords basePosition baseOccurrence q).cost <= 5 := by
  unfold denseTwoWordSelectCosted
  cases hfirst :
      (bitWords.store.readWordCosted
        (basePosition / wordSize)).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfirst]
  | some firstWord =>
      by_cases hchoose :
          q - baseOccurrence <
            RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
              RMQ.RAM.boolRankPrefix target firstWord
                (basePosition - basePosition / wordSize * wordSize)
      · simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose]
      · cases hsecond :
            (bitWords.store.readWordCosted
              (basePosition / wordSize + 1)).value with
        | none =>
            simp [Costed.bind, Costed.pure, hfirst, hchoose,
              hsecond]
        | some secondWord =>
            simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose,
              hsecond]

def denseLocalFirstCount
    (target : Bool) (bits : List Bool)
    (wordSize baseWordIndex firstOffset : Nat) : Nat :=
  RMQ.RAM.boolRankPrefix target
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex).length -
    RMQ.RAM.boolRankPrefix target
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
      firstOffset

structure DenseLocalPayloadRoutingFacts
    (target : Bool)
    (bits : List Bool) (wordSize basePosition baseOccurrence q : Nat) where
  baseWordIndex : Nat
  rankBefore : Nat
  firstOffset : Nat
  baseWordIndex_eq :
    baseWordIndex = basePosition / wordSize
  rankBefore_eq :
    rankBefore =
      RMQ.Succinct.rankPrefix target bits
        (falseSelectDenseLocalFirstStart wordSize baseWordIndex)
  firstOffset_eq :
    firstOffset =
      basePosition - falseSelectDenseLocalFirstStart wordSize baseWordIndex
  firstWordStart_readable :
    falseSelectDenseLocalFirstStart wordSize baseWordIndex < bits.length
  rankBefore_le_query :
    rankBefore <= q
  first_branch_rank :
    q - baseOccurrence <
        denseLocalFirstCount
          target bits wordSize baseWordIndex firstOffset ->
      q <
        RMQ.Succinct.rankPrefix target bits
          (falseSelectDenseLocalSecondStart wordSize baseWordIndex)
  first_local_occurrence :
    RMQ.RAM.boolRankPrefix target
        (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
        firstOffset +
        (q - baseOccurrence) =
      q - rankBefore
  second_branch_rank :
    Not (q - baseOccurrence <
        denseLocalFirstCount
          target bits wordSize baseWordIndex firstOffset) ->
      RMQ.Succinct.rankPrefix target bits
          (falseSelectDenseLocalSecondStart wordSize baseWordIndex) <= q /\
        q <
          RMQ.Succinct.rankPrefix target bits
            (falseSelectDenseLocalSpanEnd wordSize baseWordIndex) /\
          falseSelectDenseLocalSecondStart wordSize baseWordIndex <
            bits.length
  second_local_occurrence :
    Not (q - baseOccurrence <
        denseLocalFirstCount
          target bits wordSize baseWordIndex firstOffset) ->
      q - baseOccurrence -
          denseLocalFirstCount
            target bits wordSize baseWordIndex firstOffset =
        q -
          RMQ.Succinct.rankPrefix target bits
            (falseSelectDenseLocalSecondStart wordSize baseWordIndex)

structure DenseLocalSpanCertificate
    (target : Bool) (bits : List Bool) (wordSize : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) where
  firstWord : List Bool
  first_read :
    bitWords.store.words[basePosition / wordSize]? = some firstWord
  first_branch_exact :
    q - baseOccurrence <
      RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
        RMQ.RAM.boolRankPrefix target firstWord
          (basePosition - basePosition / wordSize * wordSize) ->
      (RMQ.RAM.boolSelectInWord target firstWord
        (RMQ.RAM.boolRankPrefix target firstWord
            (basePosition - basePosition / wordSize * wordSize) +
          (q - baseOccurrence))).map
        (fun offset => basePosition / wordSize * wordSize + offset) =
          RMQ.Succinct.select target bits q
  second_branch_exact :
    Not (q - baseOccurrence <
      RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
        RMQ.RAM.boolRankPrefix target firstWord
          (basePosition - basePosition / wordSize * wordSize)) ->
      exists secondWord,
        bitWords.store.words[basePosition / wordSize + 1]? =
            some secondWord /\
          (RMQ.RAM.boolSelectInWord target secondWord
            (q - baseOccurrence -
              (RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
                RMQ.RAM.boolRankPrefix target firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize)))).map
            (fun offset =>
              (basePosition / wordSize + 1) * wordSize + offset) =
              RMQ.Succinct.select target bits q

def denseLocalSpanCertificate_of_payload_routing_facts
    {target : Bool} {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (haligned : FalseSelectAlignedBitWords bits wordSize bitWords)
    (hfacts :
      DenseLocalPayloadRoutingFacts
        target bits wordSize basePosition baseOccurrence q) :
    DenseLocalSpanCertificate
      target bits wordSize bitWords basePosition baseOccurrence q := by
  let firstStart :=
    falseSelectDenseLocalFirstStart wordSize hfacts.baseWordIndex
  let secondStart :=
    falseSelectDenseLocalSecondStart wordSize hfacts.baseWordIndex
  let spanEnd :=
    falseSelectDenseLocalSpanEnd wordSize hfacts.baseWordIndex
  let firstWord :=
    falseSelectDenseLocalFirstWord bits wordSize hfacts.baseWordIndex
  have hfirstReadAtBase :
      bitWords.store.words[hfacts.baseWordIndex]? = some firstWord := by
    cases haligned.get_some_of_mul_lt
        hfacts.firstWordStart_readable with
    | intro word hread =>
        have hword := haligned.get_eq_take_drop hread
        simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
          falseSelectDenseLocalFirstStart, hword] using hread
  have hfirstRead :
      bitWords.store.words[basePosition / wordSize]? = some firstWord := by
    rw [<- hfacts.baseWordIndex_eq]
    exact hfirstReadAtBase
  have hoffset :
      basePosition - basePosition / wordSize * wordSize =
        hfacts.firstOffset := by
    rw [<- hfacts.baseWordIndex_eq]
    simpa [firstStart, falseSelectDenseLocalFirstStart] using
      hfacts.firstOffset_eq.symm
  have hfirstStartDiv :
      basePosition / wordSize * wordSize = firstStart := by
    rw [<- hfacts.baseWordIndex_eq]
    rfl
  have hsecondStartDiv :
      (basePosition / wordSize + 1) * wordSize = secondStart := by
    rw [<- hfacts.baseWordIndex_eq]
    rfl
  have hfirstEnd :
      secondStart = firstStart + wordSize := by
    simp [secondStart, firstStart, falseSelectDenseLocalSecondStart,
      falseSelectDenseLocalFirstStart, Nat.succ_mul]
  have hspanEnd :
      spanEnd = secondStart + wordSize := by
    simp [spanEnd, secondStart, falseSelectDenseLocalSpanEnd,
      falseSelectDenseLocalSecondStart, Nat.add_assoc, Nat.succ_mul]
  refine {
    firstWord := firstWord
    first_read := hfirstRead
    first_branch_exact := ?_
    second_branch_exact := ?_ }
  · intro hchoose
    have hchoiceFacts :
        q - baseOccurrence <
          denseLocalFirstCount
            target bits wordSize hfacts.baseWordIndex hfacts.firstOffset := by
      simpa [firstWord, denseLocalFirstCount,
        falseSelectDenseLocalFirstWord, hoffset] using hchoose
    have hqFirstRank := hfacts.first_branch_rank hchoiceFacts
    have hqFirstRankAtSecond :
        q < RMQ.Succinct.rankPrefix target bits secondStart := by
      simpa [secondStart] using hqFirstRank
    cases select_exists_of_lt_rankPrefix
        (target := target) (bits := bits) (occurrence := q)
        (limit := secondStart) hqFirstRankAtSecond with
    | intro pos hselect =>
        have hrankBeforeLe :
            RMQ.Succinct.rankPrefix target bits firstStart <= q := by
          simpa [firstStart] using
            (by
              rw [<- hfacts.rankBefore_eq]
              exact hfacts.rankBefore_le_query)
        have hstart_le_pos : firstStart <= pos := by
          by_cases hle : firstStart <= pos
          · exact hle
          · have hpos_lt_start : pos < firstStart :=
              Nat.lt_of_not_ge hle
            have hocc_lt :=
              occurrence_lt_rankPrefix_of_select_lt hselect hpos_lt_start
            omega
        have hpos_lt_second : pos < secondStart := by
          by_cases hlt : pos < secondStart
          · exact hlt
          · have hsecond_le_pos : secondStart <= pos := Nat.le_of_not_gt hlt
            have hprefix_le :=
              RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
                hselect hsecond_le_pos
            omega
        have hpos_lt_word : pos < firstStart + wordSize := by
          omega
        have hstartLen : firstStart <= bits.length :=
          Nat.le_of_lt hfacts.firstWordStart_readable
        have hlocal :=
          RMQ.Succinct.select_drop_take_eq_sub_of_select
            (target := target) (bits := bits) (occurrence := q)
            (idx := pos) (start := firstStart) (width := wordSize)
            hselect hstart_le_pos hpos_lt_word hstartLen hrankBeforeLe
        have hlocalOccurrence :
            RMQ.RAM.boolRankPrefix target firstWord hfacts.firstOffset +
                (q - baseOccurrence) =
              q - RMQ.Succinct.rankPrefix target bits firstStart := by
          simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
            hfacts.rankBefore_eq] using hfacts.first_local_occurrence
        have hlocalOccurrenceCert :
            RMQ.RAM.boolRankPrefix target firstWord
                (basePosition - basePosition / wordSize * wordSize) +
                (q - baseOccurrence) =
              q - RMQ.Succinct.rankPrefix target bits firstStart := by
          simpa [hoffset] using hlocalOccurrence
        have hselectWord :
            RMQ.Succinct.select target firstWord
                (RMQ.RAM.boolRankPrefix target firstWord
                    (basePosition -
                      basePosition / wordSize * wordSize) +
                  (q - baseOccurrence)) =
              some (pos - firstStart) := by
          rw [hlocalOccurrenceCert]
          simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
            falseSelectDenseLocalFirstStart] using hlocal
        calc
          (RMQ.RAM.boolSelectInWord target firstWord
              (RMQ.RAM.boolRankPrefix target firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize) +
                (q - baseOccurrence))).map
              (fun offset =>
                basePosition / wordSize * wordSize + offset) =
            (RMQ.Succinct.select target firstWord
              (RMQ.RAM.boolRankPrefix target firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize) +
                (q - baseOccurrence))).map
              (fun offset =>
                basePosition / wordSize * wordSize + offset) := by
              simp [RMQ.Succinct.ram_boolSelectInWord_eq_select]
          _ = some
              (basePosition / wordSize * wordSize +
                (pos - firstStart)) := by
              simp [hselectWord]
          _ = some pos := by
              have hposEq :
                  basePosition / wordSize * wordSize +
                      (pos - firstStart) = pos := by
                omega
              simp [hposEq]
          _ = RMQ.Succinct.select target bits q := hselect.symm
  · intro hnot
    have hnotFacts :
        Not (q - baseOccurrence <
          denseLocalFirstCount
            target bits wordSize hfacts.baseWordIndex hfacts.firstOffset) := by
      intro hchoice
      exact hnot (by
        simpa [firstWord, denseLocalFirstCount,
          falseSelectDenseLocalFirstWord, hoffset] using hchoice)
    have hbranch := hfacts.second_branch_rank hnotFacts
    cases hbranch with
    | intro hsecondRankLe hbranch =>
        cases hbranch with
        | intro hqSpan hsecondReadable =>
            have hsecondRankLeAt :
                RMQ.Succinct.rankPrefix target bits secondStart <= q := by
              simpa [secondStart] using hsecondRankLe
            have hqSpanAt :
                q < RMQ.Succinct.rankPrefix target bits spanEnd := by
              simpa [spanEnd] using hqSpan
            cases haligned.get_some_of_mul_lt hsecondReadable with
            | intro secondWord hsecondReadAtBase =>
                have hsecondWord :=
                  haligned.get_eq_take_drop hsecondReadAtBase
                have hsecondRead :
                    bitWords.store.words[basePosition / wordSize + 1]? =
                      some secondWord := by
                  rw [<- hfacts.baseWordIndex_eq]
                  exact hsecondReadAtBase
                refine ⟨secondWord, hsecondRead, ?_⟩
                cases select_exists_of_lt_rankPrefix
                    (target := target) (bits := bits) (occurrence := q)
                    (limit := spanEnd) hqSpanAt with
                | intro pos hselect =>
                    have hsecond_le_pos : secondStart <= pos := by
                      by_cases hle : secondStart <= pos
                      · exact hle
                      · have hpos_lt_second :
                            pos < secondStart := Nat.lt_of_not_ge hle
                        have hocc_lt :=
                          occurrence_lt_rankPrefix_of_select_lt
                            hselect hpos_lt_second
                        omega
                    have hpos_lt_span : pos < spanEnd := by
                      by_cases hlt : pos < spanEnd
                      · exact hlt
                      · have hend_le_pos : spanEnd <= pos :=
                          Nat.le_of_not_gt hlt
                        have hprefix_le :=
                          RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
                            hselect hend_le_pos
                        omega
                    have hpos_lt_word : pos < secondStart + wordSize := by
                      omega
                    have hstartLen : secondStart <= bits.length :=
                      Nat.le_of_lt hsecondReadable
                    have hlocal :=
                      RMQ.Succinct.select_drop_take_eq_sub_of_select
                        (target := target) (bits := bits) (occurrence := q)
                        (idx := pos) (start := secondStart)
                        (width := wordSize) hselect hsecond_le_pos
                        hpos_lt_word hstartLen hsecondRankLeAt
                    have hlocalOccurrence :
                        q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix target firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix target firstWord
                                (basePosition -
                                  basePosition / wordSize * wordSize)) =
                          q -
                            RMQ.Succinct.rankPrefix target bits
                              secondStart := by
                      simpa [firstWord, denseLocalFirstCount,
                        falseSelectDenseLocalFirstWord, secondStart,
                        hoffset] using
                        hfacts.second_local_occurrence hnotFacts
                    have hselectWord :
                        RMQ.Succinct.select target secondWord
                            (q - baseOccurrence -
                              (RMQ.RAM.boolRankPrefix target firstWord
                                  firstWord.length -
                                RMQ.RAM.boolRankPrefix target firstWord
                                  (basePosition -
                                    basePosition / wordSize *
                                      wordSize))) =
                          some (pos - secondStart) := by
                      rw [hsecondWord]
                      rw [hlocalOccurrence]
                      simpa [secondStart,
                        falseSelectDenseLocalSecondStart] using hlocal
                    calc
                      (RMQ.RAM.boolSelectInWord target secondWord
                          (q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix target firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix target firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)))).map
                          (fun offset =>
                            (basePosition / wordSize + 1) * wordSize +
                              offset) =
                        (RMQ.Succinct.select target secondWord
                          (q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix target firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix target firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)))).map
                          (fun offset =>
                            (basePosition / wordSize + 1) * wordSize +
                              offset) := by
                          simp [RMQ.Succinct.ram_boolSelectInWord_eq_select]
                      _ = some
                          ((basePosition / wordSize + 1) * wordSize +
                            (pos - secondStart)) := by
                          simp [hselectWord]
                      _ = some pos := by
                          have hposEq :
                              (basePosition / wordSize + 1) * wordSize +
                                  (pos - secondStart) = pos := by
                            omega
                          simp [hposEq]
                      _ = RMQ.Succinct.select target bits q := hselect.symm

set_option linter.unusedSimpArgs false in
theorem denseTwoWordSelectCosted_exact_of_local_span
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (hcert :
      DenseLocalSpanCertificate
        target bits wordSize bitWords basePosition baseOccurrence q) :
    (denseTwoWordSelectCosted
      target bitWords basePosition baseOccurrence q).erase =
      RMQ.Succinct.select target bits q := by
  by_cases hchoose :
      q - baseOccurrence <
        RMQ.RAM.boolRankPrefix target hcert.firstWord
          hcert.firstWord.length -
          RMQ.RAM.boolRankPrefix target hcert.firstWord
            (basePosition - basePosition / wordSize * wordSize)
  case pos =>
    have hexact := hcert.first_branch_exact hchoose
    simp [denseTwoWordSelectCosted,
      SuccinctSpace.PayloadWordStore.readWordCosted,
      RMQ.RAM.readArray?, Costed.bind, Costed.map,
      Costed.pure, Costed.erase, RMQ.RAM.Exec.toCosted,
      hcert.first_read, hchoose, hexact]
  case neg =>
    have hsecond := hcert.second_branch_exact hchoose
    cases hsecond with
    | intro secondWord hpair =>
        cases hpair with
        | intro hread hexact =>
            simp [denseTwoWordSelectCosted,
              SuccinctSpace.PayloadWordStore.readWordCosted,
              RMQ.RAM.readArray?, Costed.bind, Costed.map,
              Costed.pure, Costed.erase, RMQ.RAM.Exec.toCosted,
              hcert.first_read, hchoose, hread, hexact]

theorem denseTwoWordSelectCosted_exact_of_payload_routing_facts
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (haligned : FalseSelectAlignedBitWords bits wordSize bitWords)
    (hfacts :
      DenseLocalPayloadRoutingFacts
        target bits wordSize basePosition baseOccurrence q) :
    (denseTwoWordSelectCosted
      target bitWords basePosition baseOccurrence q).erase =
      RMQ.Succinct.select target bits q := by
  exact
    denseTwoWordSelectCosted_exact_of_local_span target
      (denseLocalSpanCertificate_of_payload_routing_facts
        haligned hfacts)

def denseLocalPayloadRoutingFacts_of_selected_span
    {target : Bool} {bits : List Bool}
    {wordSize basePosition baseOccurrence q pos : Nat}
    (hwordSize : 0 < wordSize)
    (hbaseSelect :
      RMQ.Succinct.select target bits baseOccurrence = some basePosition)
    (hselect : RMQ.Succinct.select target bits q = some pos)
    (hbaseLe : baseOccurrence <= q)
    (hposSpan : pos < basePosition + wordSize) :
    DenseLocalPayloadRoutingFacts
      target bits wordSize basePosition baseOccurrence q := by
  let baseWordIndex := basePosition / wordSize
  let firstStart := falseSelectDenseLocalFirstStart wordSize baseWordIndex
  let secondStart := falseSelectDenseLocalSecondStart wordSize baseWordIndex
  let spanEnd := falseSelectDenseLocalSpanEnd wordSize baseWordIndex
  let firstOffset := basePosition - firstStart
  let rankBefore := RMQ.Succinct.rankPrefix target bits firstStart
  have hfirstStartLeBase : firstStart <= basePosition := by
    simpa [firstStart, baseWordIndex, falseSelectDenseLocalFirstStart] using
      Nat.div_mul_le_self basePosition wordSize
  have hbaseLtSecond : basePosition < secondStart := by
    have hmodLt : basePosition % wordSize < wordSize :=
      Nat.mod_lt basePosition hwordSize
    have hdecomp :
        basePosition / wordSize * wordSize +
            basePosition % wordSize = basePosition := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod basePosition wordSize
    simp [secondStart, baseWordIndex,
      falseSelectDenseLocalSecondStart, Nat.succ_mul]
    omega
  have hsecondEq : secondStart = firstStart + wordSize := by
    simp [secondStart, firstStart, falseSelectDenseLocalSecondStart,
      falseSelectDenseLocalFirstStart, Nat.succ_mul]
  have hspanEndEq : spanEnd = secondStart + wordSize := by
    simp [spanEnd, secondStart, falseSelectDenseLocalSpanEnd,
      falseSelectDenseLocalSecondStart, Nat.add_assoc, Nat.succ_mul]
  have hfirstStartReadable : firstStart < bits.length := by
    have hbaseBounds : basePosition < bits.length :=
      RMQ.Succinct.select_bounds hbaseSelect
    exact Nat.lt_of_le_of_lt hfirstStartLeBase hbaseBounds
  have hrankBeforeLeBase : rankBefore <= baseOccurrence := by
    simpa [rankBefore] using
      RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
        hbaseSelect hfirstStartLeBase
  have hrankBeforeLeQ : rankBefore <= q := by
    omega
  have hposLtSpanEnd : pos < spanEnd := by
    have hbaseLtFirstEnd : basePosition < firstStart + wordSize := by
      omega
    rw [hspanEndEq, hsecondEq]
    omega
  have hqLtSpanRank :
      q < RMQ.Succinct.rankPrefix target bits spanEnd := by
    exact occurrence_lt_rankPrefix_of_select_lt hselect hposLtSpanEnd
  let hi := Nat.min secondStart bits.length
  have hhiLen : hi <= bits.length := Nat.min_le_right _ _
  have hfirstStartHi : firstStart <= hi := by
    exact Nat.le_min.mpr
      ⟨by omega, Nat.le_of_lt hfirstStartReadable⟩
  have hhiSub :
      hi - firstStart =
        Nat.min wordSize (bits.drop firstStart).length := by
    by_cases hcase : secondStart <= bits.length
    · have hhiEq : hi = secondStart := by
        exact Nat.min_eq_left hcase
      have hdropLenGe :
          wordSize <= (bits.drop firstStart).length := by
        simp [List.length_drop]
        omega
      have hminEq :
          Nat.min wordSize (bits.drop firstStart).length = wordSize :=
        Nat.min_eq_left hdropLenGe
      rw [hhiEq, hminEq, hsecondEq]
      omega
    · have hhiEq : hi = bits.length := by
        exact Nat.min_eq_right (Nat.le_of_not_ge hcase)
      have hdropLenLe :
          (bits.drop firstStart).length <= wordSize := by
        simp [List.length_drop]
        omega
      have hminEq :
          Nat.min wordSize (bits.drop firstStart).length =
            (bits.drop firstStart).length :=
        Nat.min_eq_right hdropLenLe
      rw [hhiEq, hminEq]
      simp [List.length_drop]
  have hdrop :=
    RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
      target bits hfirstStartHi hhiLen
  have hbitsHiRank :
      RMQ.Succinct.rankPrefix target bits hi =
        RMQ.Succinct.rankPrefix target bits secondStart := by
    simpa [hi] using
      RMQ.Succinct.rankPrefix_min_length_eq target bits secondStart
  have hdropWordRank :
      RMQ.Succinct.rankPrefix target (bits.drop firstStart)
          wordSize =
        RMQ.Succinct.rankPrefix target (bits.drop firstStart)
          (hi - firstStart) := by
    have hmin :=
      RMQ.Succinct.rankPrefix_min_length_eq
        target (bits.drop firstStart) wordSize
    rw [<- hmin]
    rw [hhiSub]
  have hfirstTotal :
      RMQ.RAM.boolRankPrefix target
          (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
          (falseSelectDenseLocalFirstWord bits wordSize
            baseWordIndex).length =
        RMQ.Succinct.rankPrefix target bits secondStart -
          RMQ.Succinct.rankPrefix target bits firstStart := by
    rw [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix]
    change
      RMQ.Succinct.rankPrefix target
          ((bits.drop firstStart).take wordSize)
          ((bits.drop firstStart).take wordSize).length =
        RMQ.Succinct.rankPrefix target bits secondStart -
          RMQ.Succinct.rankPrefix target bits firstStart
    rw [rankPrefix_take_length_eq]
    change
      RMQ.Succinct.rankPrefix target
          (bits.drop firstStart) wordSize =
        RMQ.Succinct.rankPrefix target bits secondStart -
          RMQ.Succinct.rankPrefix target bits firstStart
    rw [hdropWordRank]
    rw [hdrop]
    rw [hbitsHiRank]
  have hfirstOffsetRank :
      RMQ.RAM.boolRankPrefix target
          (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
          firstOffset =
        baseOccurrence -
          RMQ.Succinct.rankPrefix target bits firstStart := by
    rw [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix]
    change
      RMQ.Succinct.rankPrefix target
          ((bits.drop firstStart).take wordSize)
          firstOffset =
        baseOccurrence -
          RMQ.Succinct.rankPrefix target bits firstStart
    have hoffLen : firstOffset <=
        (falseSelectDenseLocalFirstWord bits wordSize
          baseWordIndex).length := by
      have hbaseLen : basePosition < bits.length :=
        RMQ.Succinct.select_bounds hbaseSelect
      have hoffWord : firstOffset <= wordSize := by
        omega
      have hoffDrop : firstOffset <= (bits.drop firstStart).length := by
        simp [List.length_drop]
        omega
      simpa [falseSelectDenseLocalFirstWord] using
        (Nat.le_min.mpr ⟨hoffWord, hoffDrop⟩)
    have htake :=
      RMQ.Succinct.rankPrefix_take_eq_of_le
        target (bits.drop firstStart) (n := wordSize)
        (limit := firstOffset) hoffLen
    rw [htake]
    have hlimit : firstStart + firstOffset <= bits.length := by
      have hbaseLen : basePosition < bits.length :=
        RMQ.Succinct.select_bounds hbaseSelect
      omega
    have hdropOffset :=
      RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
        target bits (start := firstStart)
        (limit := firstStart + firstOffset)
        (by omega) hlimit
    have hbaseEq : firstStart + firstOffset = basePosition := by
      simp [firstOffset]
      omega
    rw [hbaseEq] at hdropOffset
    have hbaseRank :
        RMQ.Succinct.rankPrefix target bits basePosition =
          baseOccurrence := by
      exact RMQ.Succinct.select_rankPrefix_eq hbaseSelect
    rw [hdropOffset, hbaseRank]
  have hbaseLtSecondRank :
      baseOccurrence <
        RMQ.Succinct.rankPrefix target bits secondStart :=
    occurrence_lt_rankPrefix_of_select_lt hbaseSelect hbaseLtSecond
  have hfirstCountEq :
      denseLocalFirstCount
          target bits wordSize baseWordIndex firstOffset =
        RMQ.Succinct.rankPrefix target bits secondStart - baseOccurrence := by
    unfold denseLocalFirstCount
    rw [hfirstTotal, hfirstOffsetRank]
    omega
  refine {
    baseWordIndex := baseWordIndex
    rankBefore := rankBefore
    firstOffset := firstOffset
    baseWordIndex_eq := rfl
    rankBefore_eq := rfl
    firstOffset_eq := rfl
    firstWordStart_readable := hfirstStartReadable
    rankBefore_le_query := hrankBeforeLeQ
    first_branch_rank := ?_
    first_local_occurrence := ?_
    second_branch_rank := ?_
    second_local_occurrence := ?_ }
  · intro hchoice
    rw [hfirstCountEq] at hchoice
    have hq :
        q < RMQ.Succinct.rankPrefix target bits secondStart := by
      omega
    simpa [secondStart] using hq
  · rw [hfirstOffsetRank]
    have hcalc :
        baseOccurrence -
            RMQ.Succinct.rankPrefix target bits firstStart +
            (q - baseOccurrence) =
          q - rankBefore := by
      simp [rankBefore]
      omega
    exact hcalc
  · intro hnot
    have hsecondLe :
        RMQ.Succinct.rankPrefix target bits secondStart <= q := by
      by_cases hlt :
          q < RMQ.Succinct.rankPrefix target bits secondStart
      · have hchoice :
            q - baseOccurrence <
              denseLocalFirstCount
                target bits wordSize baseWordIndex firstOffset := by
          rw [hfirstCountEq]
          omega
        exact False.elim (hnot hchoice)
      · exact Nat.le_of_not_gt hlt
    have hsecondReadable :
        secondStart < bits.length := by
      by_cases hle : secondStart <= pos
      · exact Nat.lt_of_le_of_lt hle (RMQ.Succinct.select_bounds hselect)
      · have hposLtSecond : pos < secondStart := Nat.lt_of_not_ge hle
        have hoccLt :=
          occurrence_lt_rankPrefix_of_select_lt hselect hposLtSecond
        omega
    exact
      ⟨by simpa [secondStart] using hsecondLe,
        by simpa [spanEnd] using hqLtSpanRank,
        by simpa [secondStart] using hsecondReadable⟩
  · intro hnot
    have hsecondLe :
        RMQ.Succinct.rankPrefix target bits secondStart <= q := by
      by_cases hlt :
          q < RMQ.Succinct.rankPrefix target bits secondStart
      · have hchoice :
            q - baseOccurrence <
              denseLocalFirstCount
                target bits wordSize baseWordIndex firstOffset := by
          rw [hfirstCountEq]
          omega
        exact False.elim (hnot hchoice)
      · exact Nat.le_of_not_gt hlt
    rw [hfirstCountEq]
    simpa [secondStart] using
      (by
        omega :
          q - baseOccurrence -
              (RMQ.Succinct.rankPrefix target bits secondStart -
                baseOccurrence) =
            q - RMQ.Succinct.rankPrefix target bits secondStart)

/-- Generic dense-local entry decode: `denseTwoWordSelectCosted` anchored at an
entry's base word/offset and base occurrence. -/
def denseLocalEntrySelectCosted
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry)
    (q : Nat) : Costed (Option Nat) :=
  denseTwoWordSelectCosted target bitWords
    (sparseDenseFalseSelectDenseLocalEntryBasePosition wordSize entry)
    entry.baseOccurrence q

theorem denseLocalEntryFalseSelectCosted_eq
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry) (q : Nat) :
    denseLocalEntryFalseSelectCosted bitWords entry q =
      denseLocalEntrySelectCosted false bitWords entry q :=
  rfl

theorem denseLocalEntrySelectCosted_cost_le_five
    (target : Bool) {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry) (q : Nat) :
    (denseLocalEntrySelectCosted target bitWords entry q).cost <= 5 :=
  denseTwoWordSelectCosted_cost_le_five target bitWords
    (sparseDenseFalseSelectDenseLocalEntryBasePosition wordSize entry)
    entry.baseOccurrence q

/-- Generic explicit position list: the `target`-occurrence positions
`[base, base+count)`, clamped to `bits.length`. -/
def selectPositions (target : Bool) (bits : List Bool) (base count : Nat) :
    List Nat :=
  (List.range count).map fun offset =>
    (RMQ.Succinct.select target bits (base + offset)).getD bits.length

theorem falseSelectPositions_eq (bits : List Bool) (base count : Nat) :
    falseSelectPositions bits base count = selectPositions false bits base count :=
  rfl

/-- Generic relative-offset list: for each `offset < count` whose occurrence is
below `endOccurrence`, the position of the `(baseOccurrence + offset)`-th
`target` bit minus `basePosition`; otherwise `0`.  This is
`falseSelectRelativeOffsetsOrZero` with the hardcoded `false` replaced by
`target`. -/
def relativeOffsetsOrZero (target : Bool) (bits : List Bool)
    (baseOccurrence count endOccurrence basePosition : Nat) : List Nat :=
  (List.range count).map fun offset =>
    if baseOccurrence + offset < endOccurrence then
      match RMQ.Succinct.select target bits (baseOccurrence + offset) with
      | some pos => pos - basePosition
      | none => 0
    else
      0

theorem falseSelectRelativeOffsetsOrZero_eq
    (bits : List Bool) (baseOccurrence count endOccurrence basePosition : Nat) :
    falseSelectRelativeOffsetsOrZero bits baseOccurrence count endOccurrence
        basePosition =
      relativeOffsetsOrZero false bits baseOccurrence count endOccurrence
        basePosition :=
  rfl

theorem relativeOffsetsOrZero_length
    (target : Bool) (bits : List Bool)
    (baseOccurrence count endOccurrence basePosition : Nat) :
    (relativeOffsetsOrZero target bits baseOccurrence count endOccurrence
      basePosition).length = count := by
  simp [relativeOffsetsOrZero]

theorem relativeOffsetsOrZero_mem_cases
    {target : Bool} {bits : List Bool} {baseOccurrence count endOccurrence
      basePosition entry : Nat}
    (hmem :
      List.Mem entry
        (relativeOffsetsOrZero target bits baseOccurrence count endOccurrence
          basePosition)) :
    entry = 0 \/
      exists offset pos,
        offset < count /\
          baseOccurrence + offset < endOccurrence /\
          RMQ.Succinct.select target bits (baseOccurrence + offset) = some pos /\
          entry = pos - basePosition := by
  unfold relativeOffsetsOrZero at hmem
  rcases List.mem_map.mp hmem with ⟨offset, hoffMem, hentry⟩
  have hoff : offset < count := by
    simpa using (List.mem_range.mp hoffMem)
  by_cases hlt : baseOccurrence + offset < endOccurrence
  · cases hselect :
      RMQ.Succinct.select target bits (baseOccurrence + offset) with
    | none =>
        left
        simpa [hlt, hselect] using hentry.symm
    | some pos =>
        right
        refine ⟨offset, pos, hoff, hlt, hselect, ?_⟩
        simpa [hlt, hselect] using hentry.symm
  · left
    simpa [hlt] using hentry.symm

theorem relativeOffsetsOrZero_lookup_exact
    {target : Bool} {bits : List Bool} {baseOccurrence count endOccurrence
      basePosition localOccurrence pos : Nat}
    (hocc : localOccurrence < count)
    (hend : baseOccurrence + localOccurrence < endOccurrence)
    (hselect :
      RMQ.Succinct.select target bits (baseOccurrence + localOccurrence) =
        some pos) :
    (relativeOffsetsOrZero target bits baseOccurrence count endOccurrence
      basePosition)[localOccurrence]? =
      some (pos - basePosition) := by
  simp [relativeOffsetsOrZero, List.getElem?_map,
    List.getElem?_range hocc, hend, hselect]

theorem selectPositions_length (target : Bool) (bits : List Bool)
    (base count : Nat) :
    (selectPositions target bits base count).length = count := by
  simp [selectPositions]

theorem selectPositions_mem_le_length
    {target : Bool} {bits : List Bool} {base count pos : Nat}
    (hmem : List.Mem pos (selectPositions target bits base count)) :
    pos <= bits.length := by
  rcases List.mem_map.mp hmem with ⟨offset, _hoffset, rfl⟩
  cases hselect : RMQ.Succinct.select target bits (base + offset) with
  | none =>
      simp
  | some selected =>
      have hbound : selected < bits.length :=
        RMQ.Succinct.select_bounds hselect
      simp
      omega

end RMQ.GenericSelect
