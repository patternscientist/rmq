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
    SuccinctCloseProposal.concreteCompactBPCloseQueryCost

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
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  (concreteBPNativeCloseDirectory shape).lcaCloseCosted
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
                (concreteBPNativeLCACloseCosted shape leftClose rightClose)
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
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (concreteBPNativeLCACloseCosted shape leftClose rightClose).cost <=
      SuccinctCloseProposal.concreteCompactBPCloseQueryCost := by
  have hprofile :=
    SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile shape
  simpa [concreteBPNativeLCACloseCosted, concreteBPNativeCloseDirectory]
    using hprofile.2.2.1 leftClose rightClose

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
    (concreteBPNativeLCACloseCosted shape leftClose rightClose).erase =
      some answerClose := by
  have hprofile :=
    SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile shape
  simpa [concreteBPNativeLCACloseCosted, concreteBPNativeCloseDirectory]
    using hprofile.2.2.2.1 hlen hbound hleft hright hanswer

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
              shape leftClose rightClose
          cases hlcaValue :
              (concreteBPNativeLCACloseCosted
                shape leftClose rightClose).value with
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
          shape leftClose rightClose).value =
        some answerClose := by
    have h :=
      concreteBPNativeLCACloseCosted_exact
        (shape := shape) hlen hboundShape hleftClose hrightClose
        hanswerClose
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

end SuccinctFinal
end RMQ
