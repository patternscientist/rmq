import RMQ.Core.SuccinctSpace.RankSelect
import RMQ.Core.SuccinctSpace.TablesRAM
import RMQ.Core.SuccinctSpace.SelectSamplesRAM

/-!
# Word-RAM interpretation for stored-word rank/select leaves

This module ties the payload-live rank/select leaves to the first-order
`WordRAM` interpreter.  Rank is a single interpreted program over a combined
sample/bit-word store.  Select keeps the domain-specific locator decoder in a
bridge layer, but every locator and bit word it consumes is read through
interpreted payload memory.
-/

namespace RMQ

namespace SuccinctSpace

namespace PayloadLiveStoredWordRankData

/-- The sample words for the selected rank target. -/
def sampleWords
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) : Array (List Bool) :=
  match target with
  | true => data.samples.trueTable.store.words
  | false => data.samples.falseTable.store.words

/--
Combined Word-RAM store for one sampled-rank query.

Segment `0` is the target-specific sample table.  Segment `1` is the packed
bitvector word store.
-/
def rankWordRAMStore
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) : RMQ.WordRAM.Store where
  wordSegments := #[data.sampleWords target, data.bitWords.words]

@[simp] theorem rankWordRAMStore_readWord?_sample
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (i : Nat) :
    (data.rankWordRAMStore target).readWord? 0 i =
      (data.sampleWords target)[i]? := by
  cases target <;> rfl

@[simp] theorem rankWordRAMStore_readWord?_bits
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (i : Nat) :
    (data.rankWordRAMStore target).readWord? 1 i =
      data.bitWords.words[i]? := by
  cases target <;> rfl

@[simp] theorem rankWordRAMStore_sampleProgram_eval_value
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (i : Nat) :
    ((data.samples.sampleProgram target i).eval
        (data.rankWordRAMStore target)).value =
      ((data.sampleWords target)[i]?).map RMQ.WordRAM.bitsToNatLE := by
  cases target <;> rfl

@[simp] theorem rankWordRAMStore_sampleProgram_eval_trace_length
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (i : Nat) :
    ((data.samples.sampleProgram target i).eval
        (data.rankWordRAMStore target)).trace.length = 1 := by
  cases target <;> rfl

/-- First-order sampled-rank program for the stored-word rank leaf. -/
def rankProgram
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : RMQ.WordRAM.Program .nat :=
  RMQ.WordRAM.Program.sampledRank target (data.wordOffset pos)
    (data.samples.sampleProgram target (data.wordIndex pos))
    (RMQ.WordRAM.Program.readWord 1 (data.wordIndex pos))

/-- Clamped variant matching `rankCostedClamped`. -/
def rankProgramClamped
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) : RMQ.WordRAM.Program .nat :=
  data.rankProgram target (Nat.min pos bits.length)

theorem rankProgram_refines_rankCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    ((data.rankProgram target pos).eval
        (data.rankWordRAMStore target)).toCosted =
      data.rankCosted target pos := by
  apply Costed.ext
  · cases target
    · unfold rankProgram rankCosted
      simp [FixedWidthRankSampleTables.sampleCosted,
        FixedWidthNatTable.readCosted,
        PayloadWordStore.readWordCosted, Costed.bind, Costed.map,
        Costed.pure]
      cases hsample :
          data.samples.falseTable.store.words[data.wordIndex pos]? with
      | none =>
          simp [sampleWords, hsample]
      | some sampleWord =>
          cases hword : data.bitWords.words[data.wordIndex pos]? with
          | none =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]
          | some word =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]
    · unfold rankProgram rankCosted
      simp [FixedWidthRankSampleTables.sampleCosted,
        FixedWidthNatTable.readCosted,
        PayloadWordStore.readWordCosted, Costed.bind, Costed.map,
        Costed.pure]
      cases hsample :
          data.samples.trueTable.store.words[data.wordIndex pos]? with
      | none =>
          simp [sampleWords, hsample]
      | some sampleWord =>
          cases hword : data.bitWords.words[data.wordIndex pos]? with
          | none =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]
          | some word =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]
  · cases target
    · unfold rankProgram rankCosted
      simp [FixedWidthRankSampleTables.sampleCosted,
        FixedWidthNatTable.readCosted,
        PayloadWordStore.readWordCosted, Costed.bind, Costed.map,
        Costed.pure]
      cases hsample :
          data.samples.falseTable.store.words[data.wordIndex pos]? with
      | none =>
          simp [sampleWords, hsample]
      | some sampleWord =>
          cases hword : data.bitWords.words[data.wordIndex pos]? with
          | none =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]
          | some word =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]
    · unfold rankProgram rankCosted
      simp [FixedWidthRankSampleTables.sampleCosted,
        FixedWidthNatTable.readCosted,
        PayloadWordStore.readWordCosted, Costed.bind, Costed.map,
        Costed.pure]
      cases hsample :
          data.samples.trueTable.store.words[data.wordIndex pos]? with
      | none =>
          simp [sampleWords, hsample]
      | some sampleWord =>
          cases hword : data.bitWords.words[data.wordIndex pos]? with
          | none =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]
          | some word =>
              simp [hsample, WordRAMBridge.bitsToNatLE_eq sampleWord,
                sampleWords]

theorem rankProgramClamped_refines_rankCostedClamped
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    ((data.rankProgramClamped target pos).eval
        (data.rankWordRAMStore target)).toCosted =
      data.rankCostedClamped target pos := by
  exact data.rankProgram_refines_rankCosted target (Nat.min pos bits.length)

theorem rankProgramClamped_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    ((data.rankProgramClamped target pos).eval
        (data.rankWordRAMStore target)).toCosted.cost <= 3 := by
  rw [data.rankProgramClamped_refines_rankCostedClamped target pos]
  exact data.rankCostedClamped_cost_le_three target pos

theorem rankProgramClamped_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead)
    (target : Bool) (pos : Nat) :
    ((data.rankProgramClamped target pos).eval
        (data.rankWordRAMStore target)).toCosted.erase =
      Succinct.rankPrefix target bits pos := by
  rw [data.rankProgramClamped_refines_rankCostedClamped target pos]
  exact data.rankCostedClamped_exact target pos

theorem rankProgram_profile
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordRankData bits overhead) :
    data.auxPayload.length = overhead /\
      flattenPayloadWords data.bitWords.words.toList = bits /\
      (forall target pos,
        ((data.rankProgramClamped target pos).eval
            (data.rankWordRAMStore target)).toCosted.cost <= 3 /\
          ((data.rankProgramClamped target pos).eval
              (data.rankWordRAMStore target)).toCosted.erase =
            Succinct.rankPrefix target bits pos) := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.bitWords.payload_eq_words_join
    · intro target pos
      exact ⟨data.rankProgramClamped_cost_le_three target pos,
        data.rankProgramClamped_exact target pos⟩

end PayloadLiveStoredWordRankData

namespace PayloadLiveStoredWordSelectData

/-- Interpreted word-select read against the bitvector payload store. -/
def wordSelectInterpretedCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (wordIndex occurrence : Nat) :
    Costed (Option Nat) :=
  ((RMQ.WordRAM.Program.wordSelectFromOpt target occurrence
      (data.bitWords.readProgram wordIndex)).eval
    data.bitWords.wordRAMStore).toCosted

theorem wordSelectInterpretedCosted_refines_wordRead
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (wordIndex occurrence : Nat) :
    data.wordSelectInterpretedCosted target wordIndex occurrence =
      Costed.bind (data.bitWords.readWordCosted wordIndex) fun word? =>
        match word? with
        | none => Costed.pure none
        | some word => (RAM.selectBoolWord target word occurrence).toCosted := by
  apply Costed.ext
  · unfold wordSelectInterpretedCosted
    cases hword : data.bitWords.words[wordIndex]? with
    | none =>
        simp [PayloadWordStore.readWordCosted, hword, Costed.bind,
          Costed.pure]
    | some word =>
        simp [PayloadWordStore.readWordCosted, hword, Costed.bind,
          RAM.Exec.toCosted]
  · unfold wordSelectInterpretedCosted
    cases hword : data.bitWords.words[wordIndex]? with
    | none =>
        simp [PayloadWordStore.readWordCosted, hword, Costed.bind,
          RAM.Exec.toCosted, RAM.Exec.steps]
        change 1 = (RAM.readArray? data.bitWords.words wordIndex).steps
        simp
    | some word =>
        simp [PayloadWordStore.readWordCosted, hword, Costed.bind,
          RAM.Exec.toCosted, RAM.Exec.steps]
        change 2 =
          (RAM.readArray? data.bitWords.words wordIndex).steps +
            (RAM.selectBoolWord target word occurrence).steps
        simp

/--
Select query whose locator and bit-word reads are both interpreter-backed.

The select-sample decoder remains a bridge-layer map over an interpreted word
read; the in-word select itself is a `WordRAM` primitive.
-/
def selectInterpretedCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind (data.samples.sampleInterpretedCosted target occurrence)
    fun entry? =>
      match entry? with
      | none => Costed.pure none
      | some none => Costed.pure none
      | some (some sample) =>
          Costed.map
            (fun local? =>
              local?.map fun offset => sample.wordStart + offset)
            (data.wordSelectInterpretedCosted target sample.wordIndex
              (occurrence - sample.rankBefore))

theorem selectInterpretedCosted_refines_selectCosted
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    data.selectInterpretedCosted target occurrence =
      data.selectCosted target occurrence := by
  unfold selectInterpretedCosted selectCosted
  rw [data.samples.sampleInterpretedCosted_refines_sampleCosted target
    occurrence]
  cases hentry :
      (data.samples.sampleCosted target occurrence).value with
  | none =>
      simp [Costed.bind, Costed.pure, hentry]
  | some entry =>
      cases entry with
      | none =>
          simp [Costed.bind, Costed.pure, hentry]
      | some sample =>
          simp [Costed.bind, hentry]
          rw [data.wordSelectInterpretedCosted_refines_wordRead target
            sample.wordIndex (occurrence - sample.rankBefore)]
          cases hword :
              (data.bitWords.readWordCosted sample.wordIndex).value with
          | none =>
              simp [Costed.bind, Costed.pure, hword]
          | some word =>
              simp [Costed.bind, Costed.map, Costed.pure, hword,
                RAM.selectBoolWord]

theorem selectInterpretedCosted_cost_le_three
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectInterpretedCosted target occurrence).cost <= 3 := by
  rw [data.selectInterpretedCosted_refines_selectCosted target occurrence]
  exact data.selectCosted_cost_le_three target occurrence

theorem selectInterpretedCosted_exact
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead)
    (target : Bool) (occurrence : Nat) :
    (data.selectInterpretedCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  rw [data.selectInterpretedCosted_refines_selectCosted target occurrence]
  exact data.selectCosted_exact target occurrence

theorem selectInterpreted_profile
    {bits : List Bool} {overhead : Nat}
    (data : PayloadLiveStoredWordSelectData bits overhead) :
    data.auxPayload.length = overhead /\
      flattenPayloadWords data.bitWords.words.toList = bits /\
      forall target occurrence,
        (data.selectInterpretedCosted target occurrence).cost <= 3 /\
          (data.selectInterpretedCosted target occurrence).erase =
            Succinct.select target bits occurrence := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.bitWords.payload_eq_words_join
    · intro target occurrence
      exact ⟨data.selectInterpretedCosted_cost_le_three target occurrence,
        data.selectInterpretedCosted_exact target occurrence⟩

end PayloadLiveStoredWordSelectData

end SuccinctSpace

end RMQ
