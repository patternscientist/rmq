import RMQ.Core.SuccinctSelectProposal
import RMQ.Core.SuccinctCloseProposal

namespace RMQ
namespace SuccinctFinal

open SuccinctSpace

def concreteBPNativeSuccinctRMQOverhead
    (closeAccessOverhead : Nat -> Nat) (n : Nat) : Nat :=
  closeAccessOverhead n +
    SuccinctCloseProposal.compactBPCloseOverhead n

def concreteBPNativeSuccinctRMQQueryCost
    (closeAccessCost : Nat) : Nat :=
  3 * closeAccessCost +
    SuccinctCloseProposal.concreteCompactBPCloseQueryCostWithRankSeed
      closeAccessCost

def concreteBPNativeRankSelectDirectory
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.RankSelectDirectory
      shape.bpCode (family.overhead shape.bpCode.length) rankSelectCost :=
  family.directory shape.bpCode

def concreteBPNativeCloseDirectory
    (shape : Cartesian.CartesianShape) :
    SuccinctCloseProposal.ConcreteCompactBPCloseLCADirectory shape :=
  SuccinctCloseProposal.concreteCompactBPCloseLCADirectory shape

/--
Weak false-only access to the BP close/rank operations needed by the BP-native
RMQ join.

This adapter surface is intentionally kept for compatibility and for theorem
composition. It is not, by itself, the final word-RAM-fidelity target: the
costed functions are fields, so a concrete headline theorem should consume a
read-backed construction that derives those functions from stored rank/select
data instead of supplying them directly.
-/
structure BPCloseAccessDirectory
    (shape : Cartesian.CartesianShape) (overhead queryCost : Nat) where
  payload : List Bool
  payload_length_le_overhead : payload.length <= overhead
  selectCloseCosted : Nat -> Costed (Option Nat)
  rankCloseCosted : Nat -> Costed Nat
  selectClose_cost_le :
    forall idx, (selectCloseCosted idx).cost <= queryCost
  rankClose_cost_le :
    forall pos, (rankCloseCosted pos).cost <= queryCost
  selectClose_exact :
    forall idx,
      (selectCloseCosted idx).erase =
        SuccinctSpace.bpCloseOfInorder? shape idx
  rankClose_exact :
    forall pos,
      (rankCloseCosted pos).erase =
        Succinct.rankPrefix false shape.bpCode pos
  rankReadWords : List (List Bool)
  selectReadWords : List (List Bool)
  rank_read_words_length_le_machine :
    forall {word : List Bool},
      List.Mem word rankReadWords ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length
  select_read_words_length_le_machine :
    forall {word : List Bool},
      List.Mem word selectReadWords ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length

namespace BPCloseAccessDirectory

end BPCloseAccessDirectory

/-- Family form of the false-only BP close access surface. -/
structure PayloadLiveBPCloseAccessFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall shape : Cartesian.CartesianShape,
      BPCloseAccessDirectory shape (overhead shape.size) queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace PayloadLiveBPCloseAccessFamily

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : PayloadLiveBPCloseAccessFamily overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall shape : Cartesian.CartesianShape,
        ((family.directory shape).payload.length <=
          overhead shape.size) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).cost <=
              queryCost) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).cost <=
              queryCost) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).erase =
              SuccinctSpace.bpCloseOfInorder? shape idx) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).erase =
              Succinct.rankPrefix false shape.bpCode pos) /\
          (forall {word : List Bool},
            List.Mem word (family.directory shape).rankReadWords ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
          (forall {word : List Bool},
            List.Mem word (family.directory shape).selectReadWords ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  constructor
  · exact family.overhead_littleO
  · intro shape
    exact
      ⟨(family.directory shape).payload_length_le_overhead,
        (family.directory shape).selectClose_cost_le,
        (family.directory shape).rankClose_cost_le,
        (family.directory shape).selectClose_exact,
        (family.directory shape).rankClose_exact,
        (family.directory shape).rank_read_words_length_le_machine,
        (family.directory shape).select_read_words_length_le_machine⟩

end PayloadLiveBPCloseAccessFamily

/-!
## Read-backed close-access surface

The weak access surface above is convenient for composing the final RMQ query,
but it is too permissive as a worker target: an inhabitant can put reference
semantics inside the `selectCloseCosted` or `rankCloseCosted` fields and charge
a dummy read.  The structures below are the stronger target. They derive the
close-select and rank-close operations from the existing two-level stored-word
rank/select data, whose query definitions read fixed-width locator tables,
payload words, and word-RAM primitives.
-/

/--
Read-backed false-only close access for a single Cartesian shape.

The auxiliary payload is exactly the concatenation of the rank and select
directory payloads.  The query operations are definitions below, not fields, so
workers cannot satisfy this surface by supplying arbitrary costed functions.
-/
structure ReadBackedBPCloseAccessDirectory
    (shape : Cartesian.CartesianShape)
    (rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat) where
  rankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      shape.bpCode rankSuperOverhead rankBlockOverhead queryCost
  selectData :
    SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData
      shape.bpCode selectSuperOverhead selectBlockOverhead queryCost
  payload_le_overhead :
    (rankData.auxPayload ++ selectData.auxPayload).length <= overhead

namespace ReadBackedBPCloseAccessDirectory

def payload
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost) : List Bool :=
  directory.rankData.auxPayload ++ directory.selectData.auxPayload

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    (idx : Nat) : Costed (Option Nat) :=
  directory.selectData.selectCosted false idx

def rankCloseCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    (pos : Nat) : Costed Nat :=
  directory.rankData.rankCosted false pos

theorem payload_length_le_overhead
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost) :
    directory.payload.length <= overhead := by
  exact directory.payload_le_overhead

theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    (idx : Nat) :
    (directory.selectCloseCosted idx).cost <= queryCost := by
  exact directory.selectData.selectCosted_cost_le false idx

theorem rankCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    (pos : Nat) :
    (directory.rankCloseCosted pos).cost <= queryCost := by
  exact directory.rankData.rankCosted_cost_le false pos

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    (idx : Nat) :
    (directory.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  calc
    (directory.selectCloseCosted idx).erase =
        Succinct.select false shape.bpCode idx := by
      exact directory.selectData.selectCosted_exact false idx
    _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
      exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx

theorem rankCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    (pos : Nat) :
    (directory.rankCloseCosted pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact directory.rankData.rankCosted_exact false pos

theorem rank_read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word directory.rankData.bitWords.store.words.toList) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact directory.rankData.payload_word_length_le_machine hmem

theorem select_read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word directory.selectData.bitWords.store.words.toList) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact directory.selectData.payload_word_length_le_machine hmem

def toWeakDirectory
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead queryCost : Nat}
    (directory :
      ReadBackedBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost) :
    BPCloseAccessDirectory shape overhead queryCost where
  payload := directory.payload
  payload_length_le_overhead := directory.payload_length_le_overhead
  selectCloseCosted := directory.selectCloseCosted
  rankCloseCosted := directory.rankCloseCosted
  selectClose_cost_le := directory.selectCloseCosted_cost_le
  rankClose_cost_le := directory.rankCloseCosted_cost_le
  selectClose_exact := directory.selectCloseCosted_exact
  rankClose_exact := directory.rankCloseCosted_exact
  rankReadWords := directory.rankData.bitWords.store.words.toList
  selectReadWords := directory.selectData.bitWords.store.words.toList
  rank_read_words_length_le_machine := by
    intro word hmem
    exact directory.rank_read_words_length_le_machine hmem
  select_read_words_length_le_machine := by
    intro word hmem
    exact directory.select_read_words_length_le_machine hmem

end ReadBackedBPCloseAccessDirectory

/--
Family form of the read-backed close-access target.  Overhead functions are
indexed by Cartesian-shape size, while the stored rank/select data themselves
operate on `shape.bpCode`.
-/
structure ReadBackedBPCloseAccessFamily
    (rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead : Nat -> Nat)
    (queryCost : Nat) where
  directory :
    forall shape : Cartesian.CartesianShape,
      ReadBackedBPCloseAccessDirectory shape
        (rankSuperOverhead shape.size)
        (rankBlockOverhead shape.size)
        (selectSuperOverhead shape.size)
        (selectBlockOverhead shape.size)
        (overhead shape.size)
        queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace ReadBackedBPCloseAccessFamily

def toWeakFamily
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      ReadBackedBPCloseAccessFamily
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost) :
    PayloadLiveBPCloseAccessFamily overhead queryCost where
  directory shape := (family.directory shape).toWeakDirectory
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      overhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      ReadBackedBPCloseAccessFamily
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall shape : Cartesian.CartesianShape,
        (((family.directory shape).payload).length <= overhead shape.size) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).cost <=
              queryCost) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).cost <=
              queryCost) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).erase =
              SuccinctSpace.bpCloseOfInorder? shape idx) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).erase =
              Succinct.rankPrefix false shape.bpCode pos) /\
          (forall {word : List Bool},
            List.Mem word
                (family.directory shape).rankData.bitWords.store.words.toList ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
          (forall {word : List Bool},
            List.Mem word
                (family.directory shape).selectData.bitWords.store.words.toList ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  constructor
  · exact family.overhead_littleO
  · intro shape
    exact
      ⟨(family.directory shape).payload_length_le_overhead,
        (family.directory shape).selectCloseCosted_cost_le,
        (family.directory shape).rankCloseCosted_cost_le,
        (family.directory shape).selectCloseCosted_exact,
        (family.directory shape).rankCloseCosted_exact,
        fun hmem =>
          (family.directory shape).rank_read_words_length_le_machine hmem,
        fun hmem =>
          (family.directory shape).select_read_words_length_le_machine hmem⟩

end ReadBackedBPCloseAccessFamily

/--
Sibling false-only close access for the sparse/dense close-select component.

This keeps the read-backed rank side, but takes close-select from
`SparseDenseFalseSelectCloseData`, whose query branches through packed
super/local locator tables, explicit exception tables, or the dense two-word BP
payload path.
-/
structure SparseDenseFalseSelectBPCloseAccessDirectory
    (shape : Cartesian.CartesianShape)
    (rankSuperOverhead rankBlockOverhead overhead queryCost : Nat) where
  rankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      shape.bpCode rankSuperOverhead rankBlockOverhead queryCost
  selectData :
    SuccinctSelectProposal.SparseDenseFalseSelectCloseData shape
  selectCost_le_query :
    SuccinctSelectProposal.sparseDenseFalseSelectQueryCost <= queryCost
  payload_le_overhead :
    (rankData.auxPayload ++ selectData.payload).length <= overhead

namespace SparseDenseFalseSelectBPCloseAccessDirectory

def payload
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost) :
    List Bool :=
  directory.rankData.auxPayload ++ directory.selectData.payload

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    (idx : Nat) : Costed (Option Nat) :=
  directory.selectData.selectCloseCosted idx

def rankCloseCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    (pos : Nat) : Costed Nat :=
  directory.rankData.rankCosted false pos

theorem payload_length_le_overhead
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost) :
    directory.payload.length <= overhead := by
  exact directory.payload_le_overhead

theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    (idx : Nat) :
    (directory.selectCloseCosted idx).cost <= queryCost := by
  exact Nat.le_trans
    (directory.selectData.selectCloseCosted_cost_le idx)
    directory.selectCost_le_query

theorem rankCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    (pos : Nat) :
    (directory.rankCloseCosted pos).cost <= queryCost := by
  exact directory.rankData.rankCosted_cost_le false pos

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    (idx : Nat) :
    (directory.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  exact directory.selectData.selectCloseCosted_exact idx

theorem rankCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    (pos : Nat) :
    (directory.rankCloseCosted pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact directory.rankData.rankCosted_exact false pos

theorem rank_read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word directory.rankData.bitWords.store.words.toList) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact directory.rankData.payload_word_length_le_machine hmem

theorem select_read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word directory.selectData.readWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact directory.selectData.read_word_length_le_machine hmem

def toWeakDirectory
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost) :
    BPCloseAccessDirectory shape overhead queryCost where
  payload := directory.payload
  payload_length_le_overhead := directory.payload_length_le_overhead
  selectCloseCosted := directory.selectCloseCosted
  rankCloseCosted := directory.rankCloseCosted
  selectClose_cost_le := directory.selectCloseCosted_cost_le
  rankClose_cost_le := directory.rankCloseCosted_cost_le
  selectClose_exact := directory.selectCloseCosted_exact
  rankClose_exact := directory.rankCloseCosted_exact
  rankReadWords := directory.rankData.bitWords.store.words.toList
  selectReadWords := directory.selectData.readWords
  rank_read_words_length_le_machine := by
    intro word hmem
    exact directory.rank_read_words_length_le_machine hmem
  select_read_words_length_le_machine := by
    intro word hmem
    exact directory.select_read_words_length_le_machine hmem

theorem profile
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead overhead queryCost : Nat}
    (directory :
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        rankSuperOverhead rankBlockOverhead overhead queryCost) :
    directory.payload.length <= overhead /\
      (forall idx,
        (directory.selectCloseCosted idx).cost <= queryCost) /\
      (forall pos,
        (directory.rankCloseCosted pos).cost <= queryCost) /\
      (forall idx,
        (directory.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      (forall pos,
        (directory.rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos) /\
      (forall {word : List Bool},
        List.Mem word directory.rankData.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      forall {word : List Bool},
        List.Mem word directory.selectData.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  constructor
  · exact directory.payload_length_le_overhead
  · constructor
    · exact directory.selectCloseCosted_cost_le
    · constructor
      · exact directory.rankCloseCosted_cost_le
      · constructor
        · exact directory.selectCloseCosted_exact
        · constructor
          · exact directory.rankCloseCosted_exact
          · constructor
            · intro word hmem
              exact directory.rank_read_words_length_le_machine hmem
            · intro word hmem
              exact directory.select_read_words_length_le_machine hmem

end SparseDenseFalseSelectBPCloseAccessDirectory

/-- Family form of the sparse/dense false-select close-access target. -/
structure SparseDenseFalseSelectBPCloseAccessFamily
    (rankSuperOverhead rankBlockOverhead overhead : Nat -> Nat)
    (queryCost : Nat) where
  directory :
    forall shape : Cartesian.CartesianShape,
      SparseDenseFalseSelectBPCloseAccessDirectory shape
        (rankSuperOverhead shape.size)
        (rankBlockOverhead shape.size)
        (overhead shape.size)
        queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace SparseDenseFalseSelectBPCloseAccessFamily

def toWeakFamily
    {rankSuperOverhead rankBlockOverhead overhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      SparseDenseFalseSelectBPCloseAccessFamily
        rankSuperOverhead rankBlockOverhead overhead queryCost) :
    PayloadLiveBPCloseAccessFamily overhead queryCost where
  directory shape := (family.directory shape).toWeakDirectory
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {rankSuperOverhead rankBlockOverhead overhead : Nat -> Nat}
    {queryCost : Nat}
    (family :
      SparseDenseFalseSelectBPCloseAccessFamily
        rankSuperOverhead rankBlockOverhead overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall shape : Cartesian.CartesianShape,
        (((family.directory shape).payload).length <= overhead shape.size) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).cost <=
              queryCost) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).cost <=
              queryCost) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).erase =
              SuccinctSpace.bpCloseOfInorder? shape idx) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).erase =
              Succinct.rankPrefix false shape.bpCode pos) /\
          (forall {word : List Bool},
            List.Mem word
                (family.directory shape).rankData.bitWords.store.words.toList ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
          forall {word : List Bool},
            List.Mem word (family.directory shape).selectData.readWords ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  constructor
  · exact family.overhead_littleO
  · intro shape
    exact (family.directory shape).profile

end SparseDenseFalseSelectBPCloseAccessFamily

/--
Final-facing close access for the repaired relative-split sparse-exception
false-select component.

The rank side remains the stored-word two-level rank data used by the existing
BP-native join.  The close-select side is the repaired compact long-super
component, whose query path charges rank over its own long-super flag vector
before reading the compact relative table.
-/
structure RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
    (shape : Cartesian.CartesianShape)
    (overhead queryCost : Nat) where
  rankSuperOverhead : Nat
  rankBlockOverhead : Nat
  rankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      shape.bpCode rankSuperOverhead rankBlockOverhead queryCost
  selectRankSuperOverhead : Nat
  selectRankBlockOverhead : Nat
  selectData :
    SuccinctSelectProposal.RelativeSplitSparseExceptionFalseSelectCloseData
      shape selectRankSuperOverhead selectRankBlockOverhead
  selectCost_le_query :
    SuccinctSelectProposal.sparseDenseFalseSelectQueryCost <= queryCost
  payload_le_overhead :
    (rankData.auxPayload ++ selectData.payload).length <= overhead

namespace RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory

def payload
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost) : List Bool :=
  directory.rankData.auxPayload ++ directory.selectData.payload

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    (idx : Nat) : Costed (Option Nat) :=
  directory.selectData.selectCloseCosted idx

def rankCloseCosted
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    (pos : Nat) : Costed Nat :=
  directory.rankData.rankCosted false pos

theorem payload_length_le_overhead
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost) :
    directory.payload.length <= overhead := by
  exact directory.payload_le_overhead

theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    (idx : Nat) :
    (directory.selectCloseCosted idx).cost <= queryCost := by
  exact Nat.le_trans
    (directory.selectData.selectCloseCosted_cost_le idx)
    directory.selectCost_le_query

theorem rankCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    (pos : Nat) :
    (directory.rankCloseCosted pos).cost <= queryCost := by
  exact directory.rankData.rankCosted_cost_le false pos

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    (idx : Nat) :
    (directory.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  exact directory.selectData.selectCloseCosted_exact idx

theorem rankCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    (pos : Nat) :
    (directory.rankCloseCosted pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact directory.rankData.rankCosted_exact false pos

theorem rank_read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word directory.rankData.bitWords.store.words.toList) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact directory.rankData.payload_word_length_le_machine hmem

theorem select_read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word directory.selectData.readWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact directory.selectData.read_word_length_le_machine hmem

def toWeakDirectory
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost) :
    BPCloseAccessDirectory shape overhead queryCost where
  payload := directory.payload
  payload_length_le_overhead := directory.payload_length_le_overhead
  selectCloseCosted := directory.selectCloseCosted
  rankCloseCosted := directory.rankCloseCosted
  selectClose_cost_le := directory.selectCloseCosted_cost_le
  rankClose_cost_le := directory.rankCloseCosted_cost_le
  selectClose_exact := directory.selectCloseCosted_exact
  rankClose_exact := directory.rankCloseCosted_exact
  rankReadWords := directory.rankData.bitWords.store.words.toList
  selectReadWords := directory.selectData.readWords
  rank_read_words_length_le_machine := by
    intro word hmem
    exact directory.rank_read_words_length_le_machine hmem
  select_read_words_length_le_machine := by
    intro word hmem
    exact directory.select_read_words_length_le_machine hmem

theorem profile
    {shape : Cartesian.CartesianShape}
    {overhead queryCost : Nat}
    (directory :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape overhead queryCost) :
    directory.payload.length <= overhead /\
      (forall idx,
        (directory.selectCloseCosted idx).cost <= queryCost) /\
      (forall pos,
        (directory.rankCloseCosted pos).cost <= queryCost) /\
      (forall idx,
        (directory.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      (forall pos,
        (directory.rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos) /\
      (forall {word : List Bool},
        List.Mem word directory.rankData.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      forall {word : List Bool},
        List.Mem word directory.selectData.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    ⟨directory.payload_length_le_overhead,
      directory.selectCloseCosted_cost_le,
      directory.rankCloseCosted_cost_le,
      directory.selectCloseCosted_exact,
      directory.rankCloseCosted_exact,
      fun hmem => directory.rank_read_words_length_le_machine hmem,
      fun hmem => directory.select_read_words_length_le_machine hmem⟩

end RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory

/-- Family form of the repaired relative-split close-access target. -/
structure RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall shape : Cartesian.CartesianShape,
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
        shape (overhead shape.size) queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily

def toWeakFamily
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily
        overhead queryCost) :
    PayloadLiveBPCloseAccessFamily overhead queryCost where
  directory shape := (family.directory shape).toWeakDirectory
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family :
      RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily
        overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall shape : Cartesian.CartesianShape,
        (((family.directory shape).payload).length <= overhead shape.size) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).cost <=
              queryCost) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).cost <=
              queryCost) /\
          (forall idx,
            ((family.directory shape).selectCloseCosted idx).erase =
              SuccinctSpace.bpCloseOfInorder? shape idx) /\
          (forall pos,
            ((family.directory shape).rankCloseCosted pos).erase =
              Succinct.rankPrefix false shape.bpCode pos) /\
          (forall {word : List Bool},
            List.Mem word
                (family.directory shape).rankData.bitWords.store.words.toList ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
          forall {word : List Bool},
            List.Mem word (family.directory shape).selectData.readWords ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  constructor
  · exact family.overhead_littleO
  · intro shape
    exact (family.directory shape).profile

end RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily

def builtRelativeSplitBPCloseRankWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits shape.bpCode.length

def builtRelativeSplitBPCloseRankBlocksPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitBPCloseRankWordSize shape

def builtRelativeSplitBPCloseRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits
    (builtRelativeSplitBPCloseRankWordSize shape *
      builtRelativeSplitBPCloseRankWordSize shape)

theorem builtRelativeSplitBPCloseRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitBPCloseRankWordSize shape := by
  simp [builtRelativeSplitBPCloseRankWordSize,
    SuccinctRankProposal.machineWordBits_pos]

theorem builtRelativeSplitBPCloseRankBlocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitBPCloseRankBlocksPerSuper shape := by
  simpa [builtRelativeSplitBPCloseRankBlocksPerSuper] using
    builtRelativeSplitBPCloseRankWordSize_pos shape

theorem builtRelativeSplitBPCloseRank_bpCode_length_lt_word_pow
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      2 ^ builtRelativeSplitBPCloseRankWordSize shape := by
  simpa [builtRelativeSplitBPCloseRankWordSize,
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self (n := shape.bpCode.length))

theorem builtRelativeSplitBPCloseRankBlockSpan_lt_pow
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankBlocksPerSuper shape *
        builtRelativeSplitBPCloseRankWordSize shape <
      2 ^ builtRelativeSplitBPCloseRankBlockWidth shape := by
  simpa [builtRelativeSplitBPCloseRankBlocksPerSuper,
    builtRelativeSplitBPCloseRankBlockWidth,
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self
      (n := builtRelativeSplitBPCloseRankWordSize shape *
        builtRelativeSplitBPCloseRankWordSize shape))

def builtRelativeSplitBPCloseRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRankProposal.canonicalSuperRankSampleTables
      shape.bpCode
      (builtRelativeSplitBPCloseRankWordSize shape)
      (builtRelativeSplitBPCloseRankBlocksPerSuper shape)
      (builtRelativeSplitBPCloseRankWordSize shape)
      (builtRelativeSplitBPCloseRank_bpCode_length_lt_word_pow shape)).payload.length

def builtRelativeSplitBPCloseRankBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
      shape.bpCode
      (builtRelativeSplitBPCloseRankWordSize shape)
      (builtRelativeSplitBPCloseRankBlocksPerSuper shape)
      (builtRelativeSplitBPCloseRankBlockWidth shape)
      (builtRelativeSplitBPCloseRankBlocksPerSuper_pos shape)
      (builtRelativeSplitBPCloseRankBlockSpan_lt_pow shape)).payload.length

def builtRelativeSplitBPCloseRankData
    (shape : Cartesian.CartesianShape) :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      shape.bpCode
      (builtRelativeSplitBPCloseRankSuperOverhead shape)
      (builtRelativeSplitBPCloseRankBlockOverhead shape)
      SuccinctSelectProposal.sparseDenseFalseSelectQueryCost :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    shape.bpCode
    (builtRelativeSplitBPCloseRankWordSize_pos shape)
    (by simp [builtRelativeSplitBPCloseRankWordSize])
    (builtRelativeSplitBPCloseRankBlocksPerSuper_pos shape)
    (builtRelativeSplitBPCloseRank_bpCode_length_lt_word_pow shape)
    (builtRelativeSplitBPCloseRankBlockSpan_lt_pow shape)
    (by
      unfold SuccinctSelectProposal.sparseDenseFalseSelectQueryCost
      omega)

theorem builtRelativeSplitBPCloseRankData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtRelativeSplitBPCloseRankData shape
    data.auxPayload.length =
        builtRelativeSplitBPCloseRankSuperOverhead shape +
          builtRelativeSplitBPCloseRankBlockOverhead shape /\
      data.wordSize <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        shape.bpCode /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <=
            SuccinctSelectProposal.sparseDenseFalseSelectQueryCost /\
          (data.rankCosted target pos).erase =
            Succinct.rankPrefix target shape.bpCode pos := by
  exact
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      shape.bpCode
      (builtRelativeSplitBPCloseRankWordSize_pos shape)
      (by simp [builtRelativeSplitBPCloseRankWordSize])
      (builtRelativeSplitBPCloseRankBlocksPerSuper_pos shape)
      (builtRelativeSplitBPCloseRank_bpCode_length_lt_word_pow shape)
      (builtRelativeSplitBPCloseRankBlockSpan_lt_pow shape)
      (by
        unfold SuccinctSelectProposal.sparseDenseFalseSelectQueryCost
        omega)

theorem canonicalSuperRankEntries_length
    (target : Bool) (bits : List Bool)
    (wordSize blocksPerSuper : Nat) :
    (SuccinctRankProposal.canonicalSuperRankEntries
      target bits wordSize blocksPerSuper).length =
      bits.length / wordSize / blocksPerSuper + 1 := by
  simp [SuccinctRankProposal.canonicalSuperRankEntries]

theorem canonicalBlockRankEntries_length
    (target : Bool) (bits : List Bool)
    (wordSize blocksPerSuper : Nat) :
    (SuccinctRankProposal.canonicalBlockRankEntries
      target bits wordSize blocksPerSuper).length =
      bits.length / wordSize + 1 := by
  simp [SuccinctRankProposal.canonicalBlockRankEntries]

theorem builtRelativeSplitBPCloseRankBlockWidth_le_two_ell
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankBlockWidth shape <=
      2 * SuccinctSelectProposal.sparseDenseFalseSelectEll shape := by
  let wordBits := builtRelativeSplitBPCloseRankWordSize shape
  let ell := SuccinctSelectProposal.sparseDenseFalseSelectEll shape
  have hwordPos : 0 < wordBits := by
    simpa [wordBits] using builtRelativeSplitBPCloseRankWordSize_pos shape
  have hwwPos : 0 < wordBits * wordBits :=
    Nat.mul_pos hwordPos hwordPos
  have hwordLt : wordBits < 2 ^ ell := by
    simpa [wordBits, ell,
      builtRelativeSplitBPCloseRankWordSize,
      SuccinctSelectProposal.sparseDenseFalseSelectEll,
      SuccinctSelectProposal.sparseDenseFalseSelectWordBits,
      SuccinctRankProposal.machineWordBits] using
      (Nat.lt_log2_self (n := wordBits))
  have hellPowPos : 0 < 2 ^ ell := Nat.pow_pos (by omega : 0 < 2)
  have hwwLtMul : wordBits * wordBits < 2 ^ ell * 2 ^ ell := by
    calc
      wordBits * wordBits < 2 ^ ell * wordBits := by
        exact Nat.mul_lt_mul_of_pos_right hwordLt hwordPos
      _ < 2 ^ ell * 2 ^ ell := by
        exact Nat.mul_lt_mul_of_pos_left hwordLt hellPowPos
  have hwwLtPow : wordBits * wordBits < 2 ^ (2 * ell) := by
    have hpowEq : 2 ^ ell * 2 ^ ell = 2 ^ (2 * ell) := by
      calc
        2 ^ ell * 2 ^ ell = 2 ^ (ell + ell) := by
          rw [Nat.pow_add]
        _ = 2 ^ (2 * ell) := by
          have hell : ell + ell = 2 * ell := by omega
          rw [hell]
    simpa [hpowEq] using hwwLtMul
  have hle :=
    SuccinctSelectProposal.natLog2_succ_le_of_pos_lt_pow
      (n := wordBits * wordBits) (k := 2 * ell) hwwPos hwwLtPow
  simpa [wordBits, ell, builtRelativeSplitBPCloseRankBlockWidth,
    SuccinctRankProposal.machineWordBits] using hle

def relativeSplitSparseExceptionBPCloseRankOverhead
    (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 36 (2 * n) + 16

theorem relativeSplitSparseExceptionBPCloseRankOverhead_littleO :
    SuccinctSpace.LittleOLinear
      relativeSplitSparseExceptionBPCloseRankOverhead := by
  unfold relativeSplitSparseExceptionBPCloseRankOverhead
  exact
    ((SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 36)
      |>.comp_two_mul_arg).add_const 16

theorem builtRelativeSplitBPCloseRankData_auxPayload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).auxPayload.length <=
      relativeSplitSparseExceptionBPCloseRankOverhead shape.size := by
  let data := builtRelativeSplitBPCloseRankData shape
  let payload := data.auxPayload.length
  let n := shape.bpCode.length
  let wordBits := builtRelativeSplitBPCloseRankWordSize shape
  let ell := SuccinctSelectProposal.sparseDenseFalseSelectEll shape
  let blockWidth := builtRelativeSplitBPCloseRankBlockWidth shape
  have hbp : n = 2 * shape.size := by
    simpa [n] using Cartesian.CartesianShape.bpCode_length shape
  by_cases hnZero : n = 0
  · have hsize : shape.size = 0 := by omega
    have hbpLen : shape.bpCode.length = 0 := by
      simpa [n] using hnZero
    have hpayload : payload <= 16 := by
      have hprofile := builtRelativeSplitBPCloseRankData_profile shape
      have hlog1 : Nat.log2 1 = 0 := by
        have hpow : (1 : Nat) < 2 ^ (1 : Nat) := by simp
        have hlt : Nat.log2 1 < 1 :=
          (Nat.log2_lt (by omega : (1 : Nat) ≠ 0)).2 hpow
        omega
      have hsuper :
          builtRelativeSplitBPCloseRankSuperOverhead shape = 2 := by
        simp [builtRelativeSplitBPCloseRankSuperOverhead,
          SuccinctRankProposal.canonicalSuperRankSampleTables_payload_length,
          canonicalSuperRankEntries_length,
          builtRelativeSplitBPCloseRankWordSize,
          builtRelativeSplitBPCloseRankBlocksPerSuper,
          SuccinctRankProposal.machineWordBits,
          hbpLen]
      have hblock :
          builtRelativeSplitBPCloseRankBlockOverhead shape = 2 := by
        simp [builtRelativeSplitBPCloseRankBlockOverhead,
          SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
          canonicalBlockRankEntries_length,
          builtRelativeSplitBPCloseRankWordSize,
          builtRelativeSplitBPCloseRankBlocksPerSuper,
          builtRelativeSplitBPCloseRankBlockWidth,
          SuccinctRankProposal.machineWordBits,
          hbpLen, hlog1]
      have hpayloadEq :
          payload =
            builtRelativeSplitBPCloseRankSuperOverhead shape +
              builtRelativeSplitBPCloseRankBlockOverhead shape := by
        simpa [payload, data] using hprofile.1
      omega
    have hover :
        16 <= relativeSplitSparseExceptionBPCloseRankOverhead shape.size := by
      simp [relativeSplitSparseExceptionBPCloseRankOverhead,
        SuccinctSpace.logLogCubedSampledDirectoryOverhead, hsize]
    exact Nat.le_trans (by simpa [payload, data] using hpayload) hover
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
    have hwordPos : 0 < wordBits := by
      simpa [wordBits] using builtRelativeSplitBPCloseRankWordSize_pos shape
    have hellOne : 1 <= ell := by
      simp [ell, SuccinctSelectProposal.sparseDenseFalseSelectEll]
    have hell3One : 1 <= ell * (ell * ell) := by
      have hmul := Nat.mul_le_mul hellOne (Nat.mul_le_mul hellOne hellOne)
      simpa [Nat.mul_assoc] using hmul
    have hwordLeN : wordBits <= n := by
      simpa [wordBits, builtRelativeSplitBPCloseRankWordSize] using
        SuccinctSelectProposal.machineWordBits_le_self_of_pos hnPos
    let superLen := n / wordBits / wordBits + 1
    let blockLen := n / wordBits + 1
    have hsuperPayload :
        builtRelativeSplitBPCloseRankSuperOverhead shape =
          superLen * wordBits + superLen * wordBits := by
      simp [builtRelativeSplitBPCloseRankSuperOverhead,
        SuccinctRankProposal.canonicalSuperRankSampleTables_payload_length,
        canonicalSuperRankEntries_length, superLen, wordBits, n,
        builtRelativeSplitBPCloseRankSuperOverhead,
        builtRelativeSplitBPCloseRankWordSize,
        builtRelativeSplitBPCloseRankBlocksPerSuper,
        builtRelativeSplitBPCloseRankBlocksPerSuper]
    have hblockPayload :
        builtRelativeSplitBPCloseRankBlockOverhead shape =
          blockLen * blockWidth + blockLen * blockWidth := by
      simp [builtRelativeSplitBPCloseRankBlockOverhead,
        SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
        canonicalBlockRankEntries_length, blockLen, blockWidth, wordBits, n,
        builtRelativeSplitBPCloseRankWordSize,
        builtRelativeSplitBPCloseRankBlocksPerSuper,
        builtRelativeSplitBPCloseRankBlockWidth]
    have hprofile := builtRelativeSplitBPCloseRankData_profile shape
    have hpayloadEq :
        payload =
          builtRelativeSplitBPCloseRankSuperOverhead shape +
            builtRelativeSplitBPCloseRankBlockOverhead shape := by
      simpa [payload, data] using hprofile.1
    have hsuperLenMul :
        superLen * (wordBits * wordBits) <= 5 * n := by
      have hdiv :
          (n / wordBits / wordBits) * (wordBits * wordBits) <= n := by
        have hfirst :
            (n / wordBits / wordBits) * wordBits <= n / wordBits := by
          exact Nat.div_mul_le_self (n / wordBits) wordBits
        have hscaled := Nat.mul_le_mul_right wordBits hfirst
        have hsecond :
            (n / wordBits) * wordBits <= n :=
          Nat.div_mul_le_self n wordBits
        exact Nat.le_trans (by
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            hscaled) hsecond
      have hww : wordBits * wordBits <= 4 * n := by
        simpa [wordBits, builtRelativeSplitBPCloseRankWordSize] using
          SuccinctSelectProposal.machineWordBits_sq_le_four_mul_self_of_pos
            hnPos
      calc
        superLen * (wordBits * wordBits) =
            (n / wordBits / wordBits) * (wordBits * wordBits) +
              wordBits * wordBits := by
                simp [superLen, Nat.add_mul]
        _ <= n + 4 * n := Nat.add_le_add hdiv hww
        _ = 5 * n := by omega
    have hblockLenMul :
        blockLen * wordBits <= 2 * n := by
      have hdiv : (n / wordBits) * wordBits <= n :=
        Nat.div_mul_le_self n wordBits
      calc
        blockLen * wordBits =
            (n / wordBits) * wordBits + wordBits := by
              simp [blockLen, Nat.add_mul]
        _ <= n + n := Nat.add_le_add hdiv hwordLeN
        _ = 2 * n := by omega
    have hblockWidth : blockWidth <= 2 * ell := by
      simpa [blockWidth, ell] using
        builtRelativeSplitBPCloseRankBlockWidth_le_two_ell shape
    have hsuperMul :
        builtRelativeSplitBPCloseRankSuperOverhead shape * wordBits <=
          10 * n := by
      rw [hsuperPayload]
      calc
        (superLen * wordBits + superLen * wordBits) * wordBits =
            superLen * (wordBits * wordBits) +
              superLen * (wordBits * wordBits) := by
              rw [Nat.add_mul]
              simp [Nat.mul_assoc]
        _ = 2 * (superLen * (wordBits * wordBits)) := by omega
        _ <= 2 * (5 * n) := Nat.mul_le_mul_left 2 hsuperLenMul
        _ = 10 * n := by omega
    have hblockMul :
        builtRelativeSplitBPCloseRankBlockOverhead shape * wordBits <=
          8 * (n * ell) := by
      rw [hblockPayload]
      calc
        (blockLen * blockWidth + blockLen * blockWidth) * wordBits =
            (blockLen * wordBits) * blockWidth +
            (blockLen * wordBits) * blockWidth := by
              rw [Nat.add_mul]
              simp [Nat.mul_left_comm, Nat.mul_comm]
        _ = 2 * ((blockLen * wordBits) * blockWidth) := by omega
        _ <= 2 * ((2 * n) * blockWidth) := by
              exact Nat.mul_le_mul_left 2
                (Nat.mul_le_mul_right blockWidth hblockLenMul)
        _ <= 2 * ((2 * n) * (2 * ell)) := by
              exact Nat.mul_le_mul_left 2
                (Nat.mul_le_mul_left (2 * n) hblockWidth)
        _ = 8 * (n * ell) := by
              rw [show 2 * ell = ell * 2 by omega]
              simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
              let t := ell * n
              change 2 * (2 * (2 * t)) = 8 * t
              omega
    have hpayloadMul :
        payload * wordBits <=
          18 * (n * (ell * (ell * ell))) := by
      rw [hpayloadEq]
      calc
        (builtRelativeSplitBPCloseRankSuperOverhead shape +
            builtRelativeSplitBPCloseRankBlockOverhead shape) *
            wordBits =
            builtRelativeSplitBPCloseRankSuperOverhead shape * wordBits +
              builtRelativeSplitBPCloseRankBlockOverhead shape * wordBits := by
                rw [Nat.add_mul]
        _ <= 10 * n + 8 * (n * ell) :=
              Nat.add_le_add hsuperMul hblockMul
        _ <= 10 * (n * (ell * (ell * ell))) +
              8 * (n * (ell * (ell * ell))) := by
              have hscale1 :
                  n <= n * (ell * (ell * ell)) :=
                Nat.le_trans (by omega : n <= 1 * n)
                  (by
                    have h := Nat.mul_le_mul_right n hell3One
                    simpa [Nat.mul_comm] using h)
              have hscale2 :
                  n * ell <= n * (ell * (ell * ell)) := by
                have hellSq : 1 <= ell * ell :=
                  Nat.mul_le_mul hellOne hellOne
                have h := Nat.mul_le_mul_left (n * ell) hellSq
                simpa [Nat.mul_assoc] using h
              exact Nat.add_le_add
                (Nat.mul_le_mul_left 10 hscale1)
                (Nat.mul_le_mul_left 8 hscale2)
        _ = 18 * (n * (ell * (ell * ell))) := by omega
    have hpacked :
        payload <=
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 36 n :=
      SuccinctSelectProposal.payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (shape := shape) (payload := payload) (scale := 18)
        (by
          simpa [wordBits, ell, n,
            SuccinctSelectProposal.sparseDenseFalseSelectWordBits,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            hpayloadMul)
    have hwithConst :
        payload <=
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 36 n + 16 :=
      Nat.le_trans hpacked (Nat.le_add_right _ _)
    simpa [relativeSplitSparseExceptionBPCloseRankOverhead, hbp, n] using
      hwithConst

def relativeSplitSparseExceptionBPCloseAccessOverhead
    (n : Nat) : Nat :=
  relativeSplitSparseExceptionBPCloseRankOverhead n +
    SuccinctSelectProposal.canonicalRelativeSplitSparseExceptionFalseSelectOverhead n

theorem relativeSplitSparseExceptionBPCloseAccessOverhead_littleO :
    SuccinctSpace.LittleOLinear
      relativeSplitSparseExceptionBPCloseAccessOverhead := by
  unfold relativeSplitSparseExceptionBPCloseAccessOverhead
  exact
    relativeSplitSparseExceptionBPCloseRankOverhead_littleO.add
      SuccinctSelectProposal.canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO

def builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
    (shape : Cartesian.CartesianShape) :
    RelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory
      shape
      (relativeSplitSparseExceptionBPCloseAccessOverhead shape.size)
      SuccinctSelectProposal.sparseDenseFalseSelectQueryCost where
  rankSuperOverhead := builtRelativeSplitBPCloseRankSuperOverhead shape
  rankBlockOverhead := builtRelativeSplitBPCloseRankBlockOverhead shape
  rankData := builtRelativeSplitBPCloseRankData shape
  selectRankSuperOverhead :=
    SuccinctSelectProposal.builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
      shape
  selectRankBlockOverhead :=
    SuccinctSelectProposal.builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
      shape
  selectData :=
    SuccinctSelectProposal.builtRelativeSplitSparseExceptionFalseSelectCloseData shape
  selectCost_le_query := Nat.le_refl _
  payload_le_overhead := by
    have hrank :=
      builtRelativeSplitBPCloseRankData_auxPayload_le_overhead shape
    have hselect :
        (SuccinctSelectProposal.builtRelativeSplitSparseExceptionFalseSelectCloseData
          shape).payload.length <=
          SuccinctSelectProposal.canonicalRelativeSplitSparseExceptionFalseSelectOverhead
            shape.size :=
      (SuccinctSelectProposal.builtRelativeSplitSparseExceptionFalseSelectCloseData
          shape).payload_length_le_canonical
    simp [relativeSplitSparseExceptionBPCloseAccessOverhead,
      List.length_append]
    omega

def builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily :
    RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily
      relativeSplitSparseExceptionBPCloseAccessOverhead
      SuccinctSelectProposal.sparseDenseFalseSelectQueryCost where
  directory shape :=
    builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessDirectory shape
  overhead_littleO :=
    relativeSplitSparseExceptionBPCloseAccessOverhead_littleO

theorem builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily_profile :
    SuccinctSpace.LittleOLinear
        relativeSplitSparseExceptionBPCloseAccessOverhead /\
      forall shape : Cartesian.CartesianShape,
        (((builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.directory
            shape).payload).length <=
            relativeSplitSparseExceptionBPCloseAccessOverhead shape.size) /\
          (forall idx,
            ((builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.directory
              shape).selectCloseCosted idx).cost <=
              SuccinctSelectProposal.sparseDenseFalseSelectQueryCost) /\
          (forall pos,
            ((builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.directory
              shape).rankCloseCosted pos).cost <=
              SuccinctSelectProposal.sparseDenseFalseSelectQueryCost) /\
          (forall idx,
            ((builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.directory
              shape).selectCloseCosted idx).erase =
              SuccinctSpace.bpCloseOfInorder? shape idx) /\
          (forall pos,
            ((builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.directory
              shape).rankCloseCosted pos).erase =
              Succinct.rankPrefix false shape.bpCode pos) /\
          (forall {word : List Bool},
            List.Mem word
                (builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.directory
                  shape).rankData.bitWords.store.words.toList ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
          forall {word : List Bool},
            List.Mem word
                (builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.directory
                  shape).selectData.readWords ->
              word.length <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    RelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.constant_query_profile
      builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily

def rankSelectBPCloseAccessOverhead
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost) :
    Nat -> Nat :=
  fun n => family.overhead (2 * n)

def concreteBPNativeCloseAccessDirectoryOfRankSelectFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost)
    (shape : Cartesian.CartesianShape) :
    BPCloseAccessDirectory shape
      (rankSelectBPCloseAccessOverhead family shape.size) rankSelectCost where
  payload := (concreteBPNativeRankSelectDirectory family shape).auxPayload
  payload_length_le_overhead := by
    have hbp : shape.bpCode.length = 2 * shape.size :=
      Cartesian.CartesianShape.bpCode_length shape
    have hlen :
        (concreteBPNativeRankSelectDirectory family shape).auxPayload.length =
          rankSelectBPCloseAccessOverhead family shape.size := by
      simp [rankSelectBPCloseAccessOverhead,
        concreteBPNativeRankSelectDirectory, hbp]
    omega
  selectCloseCosted := fun idx =>
    (concreteBPNativeRankSelectDirectory family shape).selectQueryCosted
      false idx
  rankCloseCosted := fun pos =>
    (concreteBPNativeRankSelectDirectory family shape).rankQueryCosted
      false pos
  selectClose_cost_le := by
    intro idx
    exact
      (concreteBPNativeRankSelectDirectory family shape).selectQueryCosted_cost_le
        false idx
  rankClose_cost_le := by
    intro pos
    exact
      (concreteBPNativeRankSelectDirectory family shape).rankQueryCosted_cost_le
        false pos
  selectClose_exact := by
    intro idx
    calc
      ((concreteBPNativeRankSelectDirectory family shape).selectQueryCosted
          false idx).erase =
          Succinct.select false shape.bpCode idx := by
        exact
          SuccinctSpace.RankSelectDirectory.selectQueryCosted_erase
            (concreteBPNativeRankSelectDirectory family shape) false idx
      _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
        exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx
  rankClose_exact := by
    intro pos
    exact
      SuccinctSpace.RankSelectDirectory.rankQueryCosted_erase
        (concreteBPNativeRankSelectDirectory family shape) false pos
  rankReadWords :=
    (family.rankComponent shape.bpCode).bitWords.store.words.toList
  selectReadWords :=
    (family.selectComponent shape.bpCode).bitWords.store.words.toList
  rank_read_words_length_le_machine := by
    intro word hmem
    exact
      (family.rankComponent shape.bpCode).payload_word_length_le_machine
        hmem
  select_read_words_length_le_machine := by
    intro word hmem
    exact
      (family.selectComponent shape.bpCode).payload_word_length_le_machine
        hmem

def concreteBPNativeCloseAccessFamilyOfRankSelectFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost) :
    PayloadLiveBPCloseAccessFamily
      (rankSelectBPCloseAccessOverhead family) rankSelectCost where
  directory shape :=
    concreteBPNativeCloseAccessDirectoryOfRankSelectFamily family shape
  overhead_littleO := family.overhead_littleO.comp_two_mul_arg

def concreteBPNativeSuccinctRMQAuxPayload
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape) :
    List Bool :=
  let accessDirectory := accessFamily.directory shape
  let closeDirectory := concreteBPNativeCloseDirectory shape
  accessDirectory.payload ++
    List.replicate
      (closeAccessOverhead shape.size - accessDirectory.payload.length)
      false ++
    closeDirectory.payload ++
      List.replicate
        (SuccinctCloseProposal.compactBPCloseOverhead shape.size -
          closeDirectory.payload.length)
        false

def concreteBPNativeSuccinctRMQPayload
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape) :
    List Bool :=
  shape.bpCode ++
    concreteBPNativeSuccinctRMQAuxPayload accessFamily shape

def concreteBPNativeSelectCloseCosted
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape)
    (idx : Nat) : Costed (Option Nat) :=
  (accessFamily.directory shape).selectCloseCosted idx

def concreteBPNativeRankCloseCosted
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape)
    (pos : Nat) : Costed Nat :=
  (accessFamily.directory shape).rankCloseCosted pos

def concreteBPNativeLCACloseCosted
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseCostedWithRankSeed
    (concreteBPNativeRankCloseCosted accessFamily shape)
    leftClose rightClose

def concreteBPNativeSuccinctRMQQueryCosted
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind (concreteBPNativeSelectCloseCosted accessFamily shape left)
    fun leftClose? =>
      Costed.bind
        (concreteBPNativeSelectCloseCosted accessFamily shape (right - 1))
        fun rightClose? =>
          match leftClose?, rightClose? with
          | some leftClose, some rightClose =>
              Costed.bind
                (concreteBPNativeLCACloseCosted accessFamily shape
                  leftClose rightClose)
                fun answerClose? =>
                  match answerClose? with
                  | some answerClose =>
                      Costed.map (fun closeRank => some (closeRank - 1))
                        (concreteBPNativeRankCloseCosted
                          accessFamily shape (answerClose + 1))
                  | none => Costed.pure none
          | _, _ => Costed.pure none

theorem concreteBPNativeSuccinctRMQOverhead_littleO
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost) :
    SuccinctSpace.LittleOLinear
      (concreteBPNativeSuccinctRMQOverhead closeAccessOverhead) := by
  exact
    accessFamily.overhead_littleO.add
      SuccinctCloseProposal.compactBPCloseOverhead_littleO

theorem concreteBPNativeSelectCloseCosted_cost_le
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseCosted accessFamily shape idx).cost <=
      closeAccessCost := by
  exact (accessFamily.directory shape).selectClose_cost_le idx

theorem concreteBPNativeRankCloseCosted_cost_le
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseCosted accessFamily shape pos).cost <=
      closeAccessCost := by
  exact (accessFamily.directory shape).rankClose_cost_le pos

theorem concreteBPNativeLCACloseCosted_cost_le
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseCosted accessFamily shape leftClose
        rightClose).cost <=
      SuccinctCloseProposal.concreteCompactBPCloseQueryCostWithRankSeed
        closeAccessCost := by
  exact
    (concreteBPNativeCloseDirectory shape).lcaCloseCostedWithRankSeed_cost_le
      (concreteBPNativeRankCloseCosted accessFamily shape)
      leftClose rightClose closeAccessCost
      (by
        intro pos
        exact concreteBPNativeRankCloseCosted_cost_le accessFamily shape pos)

theorem concreteBPNativeSelectCloseCosted_exact
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape) (idx : Nat) :
    (concreteBPNativeSelectCloseCosted accessFamily shape idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  exact (accessFamily.directory shape).selectClose_exact idx

theorem concreteBPNativeRankCloseCosted_exact
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape) (pos : Nat) :
    (concreteBPNativeRankCloseCosted accessFamily shape pos).erase =
      Succinct.rankPrefix false shape.bpCode pos := by
  exact (accessFamily.directory shape).rankClose_exact pos

theorem concreteBPNativeCloseAccessPayload_length_le_overhead
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost n : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (accessFamily.directory shape).payload.length <=
      closeAccessOverhead n := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  simpa [Cartesian.ShapeOfSize.size_eq hshapeSize] using
    (accessFamily.directory shape).payload_length_le_overhead

theorem concreteBPNativeLCACloseCosted_exact
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : SuccinctSpace.bpCloseOfInorder? shape left = some leftClose)
    (hright :
      SuccinctSpace.bpCloseOfInorder? shape (left + len - 1) =
        some rightClose)
    (hanswer :
      SuccinctSpace.bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (concreteBPNativeLCACloseCosted accessFamily shape leftClose
        rightClose).erase =
      some answerClose := by
  exact
    (concreteBPNativeCloseDirectory shape).lcaCloseCostedWithRankSeed_exact_of_query
      (concreteBPNativeRankCloseCosted accessFamily shape)
      (by
        intro pos
        exact concreteBPNativeRankCloseCosted_exact accessFamily shape pos)
      hlen hbound hleft hright hanswer

theorem concreteBPNativeSuccinctRMQAuxPayload_length
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost n : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (concreteBPNativeSuccinctRMQAuxPayload accessFamily shape).length =
      concreteBPNativeSuccinctRMQOverhead closeAccessOverhead n := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have haccessLe :
      ((accessFamily.directory shape).payload).length <=
        closeAccessOverhead n :=
    concreteBPNativeCloseAccessPayload_length_le_overhead
      accessFamily hshape
  have hcloseLe :
      (concreteBPNativeCloseDirectory shape).payload.length <=
        SuccinctCloseProposal.compactBPCloseOverhead n := by
    have hprofile :=
      SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile shape
    simpa [concreteBPNativeCloseDirectory,
      Cartesian.ShapeOfSize.size_eq hshapeSize] using hprofile.1
  simp [concreteBPNativeSuccinctRMQAuxPayload,
    concreteBPNativeSuccinctRMQOverhead,
    Cartesian.ShapeOfSize.size_eq hshapeSize]
  omega

theorem concreteBPNativeSuccinctRMQPayload_length
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost n : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    (concreteBPNativeSuccinctRMQPayload accessFamily shape).length =
      2 * n + concreteBPNativeSuccinctRMQOverhead closeAccessOverhead n := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hbp :
      shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshapeSize
  have haux :=
    concreteBPNativeSuccinctRMQAuxPayload_length accessFamily hshape
  simp [concreteBPNativeSuccinctRMQPayload, hbp, haux]

theorem concreteBPNativeSuccinctRMQQueryCosted_cost_le
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    (concreteBPNativeSuccinctRMQQueryCosted
        accessFamily shape left right).cost <=
      concreteBPNativeSuccinctRMQQueryCost closeAccessCost := by
  unfold concreteBPNativeSuccinctRMQQueryCosted
  have hleft :=
    concreteBPNativeSelectCloseCosted_cost_le accessFamily shape left
  have hright :=
    concreteBPNativeSelectCloseCosted_cost_le
      accessFamily shape (right - 1)
  cases hleftValue :
      (concreteBPNativeSelectCloseCosted
        accessFamily shape left).value with
  | none =>
      simp [Costed.bind, concreteBPNativeSuccinctRMQQueryCost,
        hleftValue]
      omega
  | some leftClose =>
      cases hrightValue :
          (concreteBPNativeSelectCloseCosted
            accessFamily shape (right - 1)).value with
      | none =>
          simp [Costed.bind, concreteBPNativeSuccinctRMQQueryCost,
            hleftValue, hrightValue]
          omega
      | some rightClose =>
          have hlca :=
            concreteBPNativeLCACloseCosted_cost_le
              accessFamily shape leftClose rightClose
          cases hlcaValue :
              (concreteBPNativeLCACloseCosted
                accessFamily shape leftClose rightClose).value with
          | none =>
              simp [Costed.bind, concreteBPNativeSuccinctRMQQueryCost,
                hleftValue, hrightValue, hlcaValue]
              omega
          | some answerClose =>
              have hrank :=
                concreteBPNativeRankCloseCosted_cost_le
                  accessFamily shape (answerClose + 1)
              simp [Costed.bind, Costed.map,
                concreteBPNativeSuccinctRMQQueryCost, hleftValue,
                hrightValue, hlcaValue]
              omega

theorem concreteBPNativeSuccinctRMQQueryCosted_exact
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost n : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQQueryCosted
      accessFamily shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  have hshapeSize := Cartesian.mem_shapesOfSize_shapeOfSize hshape
  have hleftLt : left < n := by omega
  have hrightLt : left + len - 1 < n := by omega
  have hboundShape : left + len <= shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hbound
  have hleftLtShape : left < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hleftLt
  have hrightLtShape : left + len - 1 < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    exact hrightLt
  have hscanBounds :=
    Cartesian.scanWindow_bounds shape.representative left len hlen
  have hscanLt :
      scanWindow shape.representative left len < shape.size := by
    rw [Cartesian.ShapeOfSize.size_eq hshapeSize]
    omega
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hleftLtShape with
    ⟨leftClose, hleftClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt
      shape hrightLtShape with
    ⟨rightClose, hrightClose⟩
  rcases SuccinctSpace.bpCloseOfInorder?_some_of_lt shape hscanLt with
    ⟨answerClose, hanswerClose⟩
  have hselectLeft :
      (concreteBPNativeSelectCloseCosted
          accessFamily shape left).value = some leftClose := by
    have h :=
      concreteBPNativeSelectCloseCosted_exact accessFamily shape left
    simpa [Costed.erase, hleftClose] using h
  have hselectRight :
      (concreteBPNativeSelectCloseCosted
          accessFamily shape (left + len - 1)).value =
        some rightClose := by
    have h :=
      concreteBPNativeSelectCloseCosted_exact
        accessFamily shape (left + len - 1)
    simpa [Costed.erase, hrightClose] using h
  have hlca :
      (concreteBPNativeLCACloseCosted
          accessFamily shape leftClose rightClose).value =
        some answerClose := by
    have h :=
      concreteBPNativeLCACloseCosted_exact
        accessFamily (shape := shape) hlen hboundShape hleftClose
        hrightClose hanswerClose
    simpa [Costed.erase] using h
  have hrank :
      (concreteBPNativeRankCloseCosted
          accessFamily shape (answerClose + 1)).value =
        scanWindow shape.representative left len + 1 := by
    have hrankExact :=
      concreteBPNativeRankCloseCosted_exact
        accessFamily shape (answerClose + 1)
    have hrankRecover :=
      SuccinctSpace.bpCloseOfInorder?_rankFalse_succ shape hanswerClose
    calc
      (concreteBPNativeRankCloseCosted
          accessFamily shape (answerClose + 1)).value =
          Succinct.rankPrefix false shape.bpCode
            (answerClose + 1) := by
        simpa [Costed.erase] using hrankExact
      _ = scanWindow shape.representative left len + 1 :=
        hrankRecover
  have hrankSub :
      scanWindow shape.representative left len + 1 - 1 =
        scanWindow shape.representative left len := by
    omega
  unfold concreteBPNativeSuccinctRMQQueryCosted
  simp [Costed.erase, Costed.bind, Costed.map, Costed.pure,
    hselectLeft, hselectRight, hlca, hrank, hrankSub]

theorem concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
    {closeAccessOverhead : Nat -> Nat} {closeAccessCost : Nat}
    (accessFamily :
      PayloadLiveBPCloseAccessFamily
        closeAccessOverhead closeAccessCost) :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead closeAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead closeAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (accessFamily.directory shape).payload.length <=
              closeAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload accessFamily shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  closeAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            accessFamily shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost closeAccessCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryCosted
                    accessFamily shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  constructor
  · exact concreteBPNativeSuccinctRMQOverhead_littleO accessFamily
  intro n
  constructor
  · have hbase :=
      EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_lower_le_upper n
    omega
  constructor
  · intro shape hshape
    exact concreteBPNativeCloseAccessPayload_length_le_overhead
      accessFamily hshape
  constructor
  · intro shape hshape
    exact concreteBPNativeSuccinctRMQPayload_length accessFamily hshape
  constructor
  · intro shape left right
    exact concreteBPNativeSuccinctRMQQueryCosted_cost_le
      accessFamily shape left right
  · intro shape hshape left len hlen hbound
    exact concreteBPNativeSuccinctRMQQueryCosted_exact
      accessFamily hshape hlen hbound

theorem readBackedBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
    {rankSuperOverhead rankBlockOverhead
      selectSuperOverhead selectBlockOverhead
      closeAccessOverhead : Nat -> Nat}
    {closeAccessCost : Nat}
    (accessFamily :
      ReadBackedBPCloseAccessFamily
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        closeAccessOverhead closeAccessCost) :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead closeAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead closeAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((accessFamily.toWeakFamily).directory shape).payload.length <=
              closeAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              accessFamily.toWeakFamily shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  closeAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            accessFamily.toWeakFamily shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost closeAccessCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryCosted
                    accessFamily.toWeakFamily shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  exact
    concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
      accessFamily.toWeakFamily

theorem concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile_of_rankSelectFamily
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {rankSelectCost : Nat}
    (family :
      SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock rankSelectCost) :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          (rankSelectBPCloseAccessOverhead family)) /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              (rankSelectBPCloseAccessOverhead family) n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeCloseAccessFamilyOfRankSelectFamily family
              |>.directory shape).payload.length <=
              rankSelectBPCloseAccessOverhead family n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              (concreteBPNativeCloseAccessFamilyOfRankSelectFamily family)
              shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  (rankSelectBPCloseAccessOverhead family) n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            (concreteBPNativeCloseAccessFamilyOfRankSelectFamily family)
            shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost rankSelectCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryCosted
                    (concreteBPNativeCloseAccessFamilyOfRankSelectFamily
                      family)
                    shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  exact
    concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
      (concreteBPNativeCloseAccessFamilyOfRankSelectFamily family)

theorem builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile :
    let accessFamily :=
      builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.toWeakFamily
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          relativeSplitSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              relativeSplitSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (accessFamily.directory shape).payload.length <=
              relativeSplitSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              accessFamily shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  relativeSplitSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            accessFamily shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelectProposal.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryCosted
                    accessFamily shape left (left + len)).erase =
                    some (scanWindow shape.representative left len)) := by
  exact
    concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
      builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily.toWeakFamily

end SuccinctFinal
end RMQ
