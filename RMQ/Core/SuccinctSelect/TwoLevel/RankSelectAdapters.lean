import RMQ.Core.SuccinctSelect.TwoLevel.SelectData

/-!
# Two-level rank/select adapters

Split implementation layer for two-level select and rank/select helpers.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect
open SuccinctSpace

/-!
## Non-oracular Clark select-position source

`chargedSelectPositionSource_allows_empty_select_oracle` shows the
`ChargedSelectPositionSource` interface, taken alone, can be inhabited by a
zero-payload semantic-select oracle (`payload := []`,
`selectPositionCosted := Costed.pure (Succinct.select ...)`).  The builder below
is the constructive contrast: it backs the source with the genuine two-level
`selectCosted` query, whose answer is decoded from the stored super sample,
block delta sample, and indexed payload word via the charged
`RAM.selectBoolWord` primitive.  The payload is the actual super/block sample
tables and `readWords` are the actual stored payload words, so the source no
longer hides a semantic-select shortcut.
-/

/--
Build a `ChargedSelectPositionSource` from genuine two-level select data.

The query is `data.selectCosted target` (charged super/block/word reads + word
select), never `Succinct.select` directly; the payload is `data.auxPayload`
(the real sample tables) and `readWords` are the real stored payload words.  The
caller supplies the overhead envelope and its `LittleOLinear` proof, plus a
bound placing the concrete `superOverhead + blockOverhead` table size inside
that envelope.
-/
def ChargedSelectPositionSource.ofTwoLevelSelectData
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (target : Bool)
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (overhead : Nat -> Nat)
    (hlittleO : SuccinctSpace.LittleOLinear overhead)
    (hpayload : superOverhead + blockOverhead <= overhead bits.length) :
    ChargedSelectPositionSource target bits overhead queryCost where
  domainSize := bits.length
  payload := data.auxPayload
  readWords := data.bitWords.store.words.toList
  selectPositionCosted := fun occurrence => data.selectCosted target occurrence
  payload_length_le := by
    simpa [data.auxPayload_length] using hpayload
  overhead_littleO := hlittleO
  selectPositionCosted_cost_le := fun occurrence =>
    data.selectCosted_cost_le target occurrence
  selectPositionCosted_exact := fun occurrence =>
    data.selectCosted_exact target occurrence
  read_word_length_le_machine := fun hmem =>
    data.payload_word_length_le_machine hmem

/--
The built source is genuinely non-oracular: its `selectPositionCosted` is
definitionally the two-level `selectCosted` query and its `payload` is the real
sample-table payload.  The remaining facts are exact select, constant cost, and
machine-word bounded reads, inherited from the two-level select data.
-/
theorem ChargedSelectPositionSource.ofTwoLevelSelectData_profile
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (target : Bool)
    (data :
      TwoLevelPayloadLiveStoredWordSelectData
        bits superOverhead blockOverhead queryCost)
    (overhead : Nat -> Nat)
    (hlittleO : SuccinctSpace.LittleOLinear overhead)
    (hpayload : superOverhead + blockOverhead <= overhead bits.length) :
    let source :=
      ChargedSelectPositionSource.ofTwoLevelSelectData
        target data overhead hlittleO hpayload
    (source.selectPositionCosted =
        fun occurrence => data.selectCosted target occurrence) /\
      source.payload = data.auxPayload /\
      source.payload.length = superOverhead + blockOverhead /\
      SuccinctSpace.LittleOLinear overhead /\
      (forall occurrence,
        (source.selectPositionCosted occurrence).cost <= queryCost) /\
      (forall occurrence,
        (source.selectPositionCosted occurrence).erase =
          RMQ.Succinct.select target bits occurrence) /\
      forall {word : List Bool},
        List.Mem word source.readWords ->
          word.length <= SuccinctRank.machineWordBits bits.length := by
  refine ⟨rfl, rfl, ?_, hlittleO, ?_, ?_, ?_⟩
  · exact data.auxPayload_length
  · intro occurrence
    exact data.selectCosted_cost_le target occurrence
  · intro occurrence
    exact data.selectCosted_exact target occurrence
  · intro word hmem
    exact data.payload_word_length_le_machine hmem

/--
Family-level non-oracular two-level Clark select source.

For every bitvector, produce a `ChargedSelectPositionSource` backed by the
two-level select family's component data.  Because the family carries genuine
`super_littleO`/`block_littleO`, the source overhead `twoLevelSelectOverhead
super block` is genuinely `LittleOLinear` (not a constant-function escape), so
this is a real `o(n)`-payload Clark select source -- reduced to supplying a
two-level select family with `o(n)` super and block budgets.
-/
def TwoLevelPayloadLiveStoredWordSelectFamily.toChargedSelectPositionSource
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily super block queryCost)
    (target : Bool) (bits : List Bool) :
    ChargedSelectPositionSource target bits
      (twoLevelSelectOverhead super block) queryCost :=
  ChargedSelectPositionSource.ofTwoLevelSelectData target
    (family.component bits)
    (twoLevelSelectOverhead super block)
    (twoLevelSelectOverhead_littleO family.super_littleO family.block_littleO)
    (Nat.le_refl _)

theorem TwoLevelPayloadLiveStoredWordSelectFamily.toChargedSelectPositionSource_profile
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordSelectFamily super block queryCost)
    (target : Bool) :
    SuccinctSpace.LittleOLinear (twoLevelSelectOverhead super block) /\
      forall bits : List Bool,
        let source := family.toChargedSelectPositionSource target bits
        (source.selectPositionCosted =
            fun occurrence =>
              (family.component bits).selectCosted target occurrence) /\
          source.payload = (family.component bits).auxPayload /\
          source.payload.length =
            twoLevelSelectOverhead super block bits.length /\
          (forall occurrence,
            (source.selectPositionCosted occurrence).cost <= queryCost) /\
          (forall occurrence,
            (source.selectPositionCosted occurrence).erase =
              RMQ.Succinct.select target bits occurrence) /\
          forall {word : List Bool},
            List.Mem word source.readWords ->
              word.length <=
                SuccinctRank.machineWordBits bits.length := by
  refine
    ⟨twoLevelSelectOverhead_littleO family.super_littleO family.block_littleO,
      ?_⟩
  intro bits
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · show ((family.component bits).auxPayload).length =
        twoLevelSelectOverhead super block bits.length
    rw [(family.component bits).auxPayload_length]
    rfl
  · intro occurrence
    exact (family.component bits).selectCosted_cost_le target occurrence
  · intro occurrence
    exact (family.component bits).selectCosted_exact target occurrence
  · intro word hmem
    exact (family.component bits).payload_word_length_le_machine hmem

def twoLevelRankSelectOverhead
    (rankSuper rankBlock selectSuper selectBlock : Nat -> Nat)
    (n : Nat) : Nat :=
  SuccinctRank.twoLevelRankOverhead rankSuper rankBlock n +
    twoLevelSelectOverhead selectSuper selectBlock n

theorem twoLevelRankSelectOverhead_littleO
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    (hrankSuper : SuccinctSpace.LittleOLinear rankSuper)
    (hrankBlock : SuccinctSpace.LittleOLinear rankBlock)
    (hselectSuper : SuccinctSpace.LittleOLinear selectSuper)
    (hselectBlock : SuccinctSpace.LittleOLinear selectBlock) :
    SuccinctSpace.LittleOLinear
      (twoLevelRankSelectOverhead
        rankSuper rankBlock selectSuper selectBlock) := by
  unfold twoLevelRankSelectOverhead
  exact
      (SuccinctRank.twoLevelRankOverhead_littleO
      hrankSuper hrankBlock).add
      (twoLevelSelectOverhead_littleO hselectSuper hselectBlock)

/-- Canonical rank/select directory overhead under `Theta(log n)` words. -/
def canonicalTwoLevelRankSelectOverhead
    (rankSuperSlots rankBlockSlots selectSuperSlots selectBlockSlots :
      Nat) : Nat -> Nat :=
  twoLevelRankSelectOverhead
    (SuccinctRank.canonicalTwoLevelRankSuperOverhead
      rankSuperSlots)
    (SuccinctRank.canonicalTwoLevelRankBlockOverhead
      rankBlockSlots)
    (canonicalTwoLevelSelectSuperOverhead selectSuperSlots)
    (canonicalTwoLevelSelectBlockOverhead selectBlockSlots)

theorem canonicalTwoLevelRankSelectOverhead_littleO
    (rankSuperSlots rankBlockSlots selectSuperSlots selectBlockSlots :
      Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelRankSelectOverhead
        rankSuperSlots rankBlockSlots selectSuperSlots selectBlockSlots) := by
  exact
    twoLevelRankSelectOverhead_littleO
      (SuccinctRank.canonicalTwoLevelRankSuperOverhead_littleO
        rankSuperSlots)
      (SuccinctRank.canonicalTwoLevelRankBlockOverhead_littleO
        rankBlockSlots)
      (canonicalTwoLevelSelectSuperOverhead_littleO selectSuperSlots)
      (canonicalTwoLevelSelectBlockOverhead_littleO selectBlockSlots)

def twoLevelRankSelectDirectory
    {bits : List Bool}
    {rankSuper rankBlock selectSuper selectBlock queryCost : Nat}
    (rankData :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits rankSuper rankBlock queryCost)
    (selectData :
      TwoLevelPayloadLiveStoredWordSelectData
        bits selectSuper selectBlock queryCost) :
    SuccinctSpace.RankSelectDirectory
      bits ((rankSuper + rankBlock) + (selectSuper + selectBlock))
      queryCost where
  Aux := Unit
  buildAux := ()
  encodeAux _ := rankData.auxPayload ++ selectData.auxPayload
  rankCosted _ target pos := rankData.rankCosted target pos
  selectCosted _ target occurrence :=
    selectData.selectCosted target occurrence
  aux_length_eq := by
    simp [rankData.auxPayload_length, selectData.auxPayload_length]
  rank_cost_le := by
    intro target pos
    exact rankData.rankCosted_cost_le target pos
  select_cost_le := by
    intro target occurrence
    exact selectData.selectCosted_cost_le target occurrence
  rank_exact := by
    intro target pos
    exact rankData.rankCosted_exact target pos
  select_exact := by
    intro target occurrence
    exact selectData.selectCosted_exact target occurrence

theorem twoLevelRankSelectDirectory_profile
    {bits : List Bool}
    {rankSuper rankBlock selectSuper selectBlock queryCost : Nat}
    (rankData :
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits rankSuper rankBlock queryCost)
    (selectData :
      TwoLevelPayloadLiveStoredWordSelectData
        bits selectSuper selectBlock queryCost) :
    (twoLevelRankSelectDirectory rankData selectData).auxPayload.length =
        (rankSuper + rankBlock) + (selectSuper + selectBlock) /\
      (forall target pos,
        ((twoLevelRankSelectDirectory rankData selectData).rankQueryCosted
            target pos).cost <= queryCost /\
          ((twoLevelRankSelectDirectory rankData selectData).rankQueryCosted
              target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((twoLevelRankSelectDirectory rankData selectData).selectQueryCosted
            target occurrence).cost <= queryCost /\
          ((twoLevelRankSelectDirectory rankData selectData).selectQueryCosted
              target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact
      (twoLevelRankSelectDirectory rankData selectData).auxPayload_length
  · constructor
    · intro target pos
      let directory := twoLevelRankSelectDirectory rankData selectData
      exact ⟨directory.rankQueryCosted_cost_le target pos,
        directory.rankQueryCosted_erase target pos⟩
    · intro target occurrence
      let directory := twoLevelRankSelectDirectory rankData selectData
      exact ⟨directory.selectQueryCosted_cost_le target occurrence,
        directory.selectQueryCosted_erase target occurrence⟩

def canonicalTwoLevelRankSelectDirectoryOfChunksExact
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.RankSelectDirectory bits
      (((SuccinctRank.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTables
          bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost :=
  twoLevelRankSelectDirectory
    (SuccinctRank.canonicalTwoLevelRankDataOfChunksExact
      bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
    (canonicalTwoLevelSelectDataOfChunksExact
      bits hword hwordMachine hoccurrences hselectSuperBits
        hselectBlockBits hquery)

theorem canonicalTwoLevelRankSelectDirectoryOfChunksExact_profile
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    (canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
        hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
        hselectSuperBits hselectBlockBits hquery).auxPayload.length =
        (((SuccinctRank.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTables
          bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExact bits hword
            hwordMachine hblocks hoccurrences hrankSuperBits hrankBlockBits
            hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact
    twoLevelRankSelectDirectory_profile
      (SuccinctRank.canonicalTwoLevelRankDataOfChunksExact
        bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
      (canonicalTwoLevelSelectDataOfChunksExact
        bits hword hwordMachine hoccurrences hselectSuperBits
          hselectBlockBits hquery)

def canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.RankSelectDirectory bits
      (((SuccinctRank.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
          bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost :=
  twoLevelRankSelectDirectory
    (SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
      bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
    (canonicalTwoLevelSelectDataOfChunksExact
      bits hword hwordMachine hoccurrences hselectSuperBits
        hselectBlockBits hquery)

theorem canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock_profile
    (bits : List Bool)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    (canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
        bits hword hwordMachine hblocks hoccurrences hrankSuperBits
        hrankBlockBits hselectSuperBits hselectBlockBits hquery).auxPayload.length =
        (((SuccinctRank.canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
          bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).rankQueryCosted
              target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).cost <= queryCost /\
          ((canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
            bits hword hwordMachine hblocks hoccurrences hrankSuperBits
            hrankBlockBits hselectSuperBits hselectBlockBits hquery).selectQueryCosted
              target occurrence).erase =
            RMQ.Succinct.select target bits occurrence) := by
  exact
    twoLevelRankSelectDirectory_profile
      (SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock
        bits hword hwordMachine hblocks hrankSuperBits hrankBlockBits hquery)
      (canonicalTwoLevelSelectDataOfChunksExact
        bits hword hwordMachine hoccurrences hselectSuperBits
          hselectBlockBits hquery)

def canonicalTwoLevelBalancedParensAccessOfChunksExact
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : parens.bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.BalancedParensAccess parens
      (((SuccinctRank.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTables
          parens.bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost where
  rankSelect :=
    canonicalTwoLevelRankSelectDirectoryOfChunksExact
      parens.bits hword hwordMachine hblocks hoccurrences
      hrankSuperBits hrankBlockBits hselectSuperBits hselectBlockBits
      hquery

theorem canonicalTwoLevelBalancedParensAccessOfChunksExact_profile
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : parens.bits.length < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    let access :=
      canonicalTwoLevelBalancedParensAccessOfChunksExact
        parens hword hwordMachine hblocks hoccurrences hrankSuperBits
        hrankBlockBits hselectSuperBits hselectBlockBits hquery
    access.rankSelect.auxPayload.length =
        (((SuccinctRank.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTables
          parens.bits wordSize blocksPerSuper rankBlockWidth
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos) := by
  dsimp
  let access :=
    canonicalTwoLevelBalancedParensAccessOfChunksExact
      parens hword hwordMachine hblocks hoccurrences hrankSuperBits
      hrankBlockBits hselectSuperBits hselectBlockBits hquery
  change
    access.rankSelect.auxPayload.length = _ /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos)
  constructor
  · exact access.auxPayload_length
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le target pos,
        access.rankCosted_erase target pos⟩
    · constructor
      · intro target occurrence
        exact ⟨access.selectCosted_cost_le target occurrence,
          access.selectCosted_erase target occurrence⟩
      · constructor
        · intro pos hpos
          exact access.close_rank_le_open_rank hpos
        · constructor
          · exact access.final_rank_eq
          · intro pos
            exact ⟨access.excessCosted_cost_le pos,
              access.excessCosted_erase pos⟩

def canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    SuccinctSpace.BalancedParensAccess parens
      (((SuccinctRank.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
          parens.bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length))
      queryCost where
  rankSelect :=
    canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock
      parens.bits hword hwordMachine hblocks hoccurrences
      hrankSuperBits hrankBlockBits hselectSuperBits hselectBlockBits
      hquery

theorem canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock_profile
    (parens : RMQ.Succinct.BalancedParens)
    {wordSize blocksPerSuper rankSuperWidth rankBlockWidth
      occurrencesPerSuper selectSuperWidth selectBlockWidth queryCost :
        Nat}
    (hword : 0 < wordSize)
    (hwordMachine :
      wordSize <= SuccinctRank.machineWordBits parens.bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hoccurrences : 0 < occurrencesPerSuper)
    (hrankSuperBits : parens.bits.length < 2 ^ rankSuperWidth)
    (hrankBlockBits : blocksPerSuper * wordSize < 2 ^ rankBlockWidth)
    (hselectSuperBits : parens.bits.length < 2 ^ selectSuperWidth)
    (hselectBlockBits : parens.bits.length < 2 ^ selectBlockWidth)
    (hquery : 4 <= queryCost) :
    let access :=
      canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock
        parens hword hwordMachine hblocks hoccurrences hrankSuperBits
        hrankBlockBits hselectSuperBits hselectBlockBits hquery
    access.rankSelect.auxPayload.length =
        (((SuccinctRank.canonicalSuperRankSampleTables
          parens.bits wordSize blocksPerSuper rankSuperWidth
          hrankSuperBits).payload.length +
        (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
          parens.bits wordSize blocksPerSuper rankBlockWidth hblocks
          hrankBlockBits).payload.length) +
        ((canonicalSelectSuperTablesFinite
          parens.bits wordSize occurrencesPerSuper selectSuperWidth
          hselectSuperBits).payload.length +
        (canonicalSelectBlockTablesFinite
          parens.bits wordSize occurrencesPerSuper selectBlockWidth
          hselectBlockBits).payload.length)) /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos) := by
  dsimp
  let access :=
    canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock
      parens hword hwordMachine hblocks hoccurrences hrankSuperBits
      hrankBlockBits hselectSuperBits hselectBlockBits hquery
  change
    access.rankSelect.auxPayload.length = _ /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (access.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        (access.selectCosted target occurrence).cost <= queryCost /\
          (access.selectCosted target occurrence).erase =
            RMQ.Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (access.excessCosted pos).erase =
            RMQ.Succinct.rankPrefix true parens.bits pos -
              RMQ.Succinct.rankPrefix false parens.bits pos)
  constructor
  · exact access.auxPayload_length
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le target pos,
        access.rankCosted_erase target pos⟩
    · constructor
      · intro target occurrence
        exact ⟨access.selectCosted_cost_le target occurrence,
          access.selectCosted_erase target occurrence⟩
      · constructor
        · intro pos hpos
          exact access.close_rank_le_open_rank hpos
        · constructor
          · exact access.final_rank_eq
          · intro pos
            exact ⟨access.excessCosted_cost_le pos,
              access.excessCosted_erase pos⟩

structure TwoLevelPayloadLiveStoredWordRankSelectFamily
    (rankSuper rankBlock selectSuper selectBlock : Nat -> Nat)
    (queryCost : Nat) where
  rankComponent :
    forall bits : List Bool,
      SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
        bits (rankSuper bits.length) (rankBlock bits.length) queryCost
  selectComponent :
    forall bits : List Bool,
      TwoLevelPayloadLiveStoredWordSelectData
        bits (selectSuper bits.length) (selectBlock bits.length) queryCost
  rankSuper_littleO : SuccinctSpace.LittleOLinear rankSuper
  rankBlock_littleO : SuccinctSpace.LittleOLinear rankBlock
  selectSuper_littleO : SuccinctSpace.LittleOLinear selectSuper
  selectBlock_littleO : SuccinctSpace.LittleOLinear selectBlock

namespace TwoLevelPayloadLiveStoredWordRankSelectFamily

def overhead
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (_family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    Nat -> Nat :=
  twoLevelRankSelectOverhead
    rankSuper rankBlock selectSuper selectBlock

theorem overhead_littleO
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact
    twoLevelRankSelectOverhead_littleO
      family.rankSuper_littleO family.rankBlock_littleO
      family.selectSuper_littleO family.selectBlock_littleO

def directory
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (bits : List Bool) :
    SuccinctSpace.RankSelectDirectory
      bits (family.overhead bits.length) queryCost :=
  twoLevelRankSelectDirectory
    (family.rankComponent bits) (family.selectComponent bits)

def toRankSelectFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.RankSelectFamily family.overhead queryCost where
  directory bits := family.directory bits
  overhead_littleO := family.overhead_littleO

def toBitVectorRankSelectFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (haccess : 1 <= queryCost) :
    RankSelectSpec.BitVectorRankSelectFamily
      family.overhead queryCost where
  directory bits :=
    RankSelectSpec.BitVectorRankSelectDirectory.ofRankSelectDirectoryWithStoredBits
      (family.directory bits) haccess
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length =
          family.overhead bits.length) /\
        (forall target pos,
          ((family.directory bits).rankQueryCosted target pos).cost <=
              queryCost /\
            ((family.directory bits).rankQueryCosted target pos).erase =
              RMQ.Succinct.rankPrefix target bits pos) /\
        (forall target occurrence,
          ((family.directory bits).selectQueryCosted target occurrence).cost <=
              queryCost /\
            ((family.directory bits).selectQueryCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact twoLevelRankSelectDirectory_profile
      (family.rankComponent bits) (family.selectComponent bits)

theorem n_plus_o_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (haccess : 1 <= queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        let directory :=
          (family.toBitVectorRankSelectFamily haccess).directory bits
        directory.payload.length =
          bits.length + family.overhead bits.length /\
          (forall i,
            (directory.accessQueryCosted i).cost <= queryCost /\
              (directory.accessQueryCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankQueryCosted target pos).cost <= queryCost /\
              (directory.rankQueryCosted target pos).erase =
                RMQ.Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectQueryCosted target occurrence).cost <= queryCost /\
              (directory.selectQueryCosted target occurrence).erase =
                RMQ.Succinct.select target bits occurrence) := by
  simpa using
    RankSelectSpec.BitVectorRankSelectFamily.n_plus_o_constant_query_profile
        (family.toBitVectorRankSelectFamily haccess)

/--
Rank/select profile with the word-RAM side condition exposed.

This strengthens `constant_query_profile`: in addition to exact queries and
sublinear auxiliary payload, both payload stores erase to the same bit vector
and every stored word is bounded by `machineWordBits bits.length`.
-/
theorem word_bounded_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length =
          family.overhead bits.length) /\
        ((family.rankComponent bits).wordSize <=
          SuccinctRank.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.rankComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.rankComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRank.machineWordBits bits.length) /\
        ((family.selectComponent bits).wordSize <=
          SuccinctRank.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.selectComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.selectComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRank.machineWordBits bits.length) /\
        (forall target pos,
          ((family.directory bits).rankQueryCosted target pos).cost <=
              queryCost /\
            ((family.directory bits).rankQueryCosted target pos).erase =
              RMQ.Succinct.rankPrefix target bits pos) /\
        (forall target occurrence,
          ((family.directory bits).selectQueryCosted target occurrence).cost <=
              queryCost /\
            ((family.directory bits).selectQueryCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    rcases twoLevelRankSelectDirectory_profile
        (family.rankComponent bits) (family.selectComponent bits) with
      ⟨haux, hrankQuery, hselectQuery⟩
    rcases (family.rankComponent bits).profile with
      ⟨_hrankAux, hrankWord, hrankErase, hrankWordBound,
        _hrankProfile⟩
    rcases (family.selectComponent bits).profile with
      ⟨_hselectAux, hselectWord, hselectErase, hselectWordBound,
        _hselectProfile⟩
    exact
      ⟨haux, hrankWord, hrankErase, hrankWordBound, hselectWord,
        hselectErase, hselectWordBound, hrankQuery, hselectQuery⟩

theorem word_bounded_n_plus_o_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost)
    (haccess : 1 <= queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        let directory :=
          (family.toBitVectorRankSelectFamily haccess).directory bits
        directory.payload.length =
          bits.length + family.overhead bits.length /\
        ((family.rankComponent bits).wordSize <=
          SuccinctRank.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.rankComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.rankComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRank.machineWordBits bits.length) /\
        ((family.selectComponent bits).wordSize <=
          SuccinctRank.machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.selectComponent bits).bitWords.store.words.toList =
          bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.selectComponent bits).bitWords.store.words.toList ->
            word.length <=
              SuccinctRank.machineWordBits bits.length) /\
        (forall i,
          (directory.accessQueryCosted i).cost <= queryCost /\
            (directory.accessQueryCosted i).erase = bits[i]?) /\
        (forall target pos,
          (directory.rankQueryCosted target pos).cost <= queryCost /\
            (directory.rankQueryCosted target pos).erase =
              RMQ.Succinct.rankPrefix target bits pos) /\
        (forall target occurrence,
          (directory.selectQueryCosted target occurrence).cost <= queryCost /\
            (directory.selectQueryCosted target occurrence).erase =
              RMQ.Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    rcases family.word_bounded_constant_query_profile.2 bits with
      ⟨_haux, hrankWord, hrankErase, hrankWordBound, hselectWord,
        hselectErase, hselectWordBound, _hrankQuery, _hselectQuery⟩
    rcases
      RankSelectSpec.BitVectorRankSelectDirectory.profile
        ((family.toBitVectorRankSelectFamily haccess).directory bits) with
      ⟨hpayload, haccessProfile, hrankProfile, hselectProfile⟩
    exact
      ⟨hpayload, hrankWord, hrankErase, hrankWordBound, hselectWord,
        hselectErase, hselectWordBound, haccessProfile, hrankProfile,
        hselectProfile⟩

def toBalancedParensAccessFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.BalancedParensAccessFamily family.overhead queryCost where
  access parens :=
    { rankSelect := family.directory parens.bits }
  overhead_littleO := family.overhead_littleO

theorem bp_constant_query_profile
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall parens : RMQ.Succinct.BalancedParens,
        (((family.toBalancedParensAccessFamily).access parens).rankSelect.auxPayload.length =
          family.overhead parens.bits.length) /\
        (forall target pos,
          (((family.toBalancedParensAccessFamily).access parens).rankCosted
              target pos).cost <= queryCost /\
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
              target pos).erase =
              RMQ.Succinct.rankPrefix target parens.bits pos) /\
        (forall target occurrence,
          (((family.toBalancedParensAccessFamily).access parens).selectCosted
              target occurrence).cost <= queryCost /\
            (((family.toBalancedParensAccessFamily).access parens).selectCosted
              target occurrence).erase =
              RMQ.Succinct.select target parens.bits occurrence) /\
        (forall {pos : Nat},
          pos <= parens.bits.length ->
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
              false pos).erase <=
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                true pos).erase) /\
        ((((family.toBalancedParensAccessFamily).access parens).rankCosted
          true parens.bits.length).erase =
          (((family.toBalancedParensAccessFamily).access parens).rankCosted
            false parens.bits.length).erase) /\
        (forall pos,
          (((family.toBalancedParensAccessFamily).access parens).excessCosted
              pos).cost <= 2 * queryCost /\
            (((family.toBalancedParensAccessFamily).access parens).excessCosted
              pos).erase =
              RMQ.Succinct.rankPrefix true parens.bits pos -
                RMQ.Succinct.rankPrefix false parens.bits pos) := by
  exact family.toBalancedParensAccessFamily.constant_query_profile

end TwoLevelPayloadLiveStoredWordRankSelectFamily

end SuccinctSelect
end RMQ

