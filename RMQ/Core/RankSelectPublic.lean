import RMQ.Core.RankSelectSpec
import RMQ.Core.RankSelectCompressed
import RMQ.Core.GenericSelect.Family

/-!
Public facade for the standalone rank/select spoke.

The construction modules keep detailed Jacobson/Clark and sparse-exception
names. This module gives the reusable bitvector surface short, neutral names
for downstream data-structure spokes.
-/

namespace RMQ.RankSelect

/-- Public bitvector rank/select directory shape. -/
abbrev Directory :=
  RMQ.RankSelectSpec.BitVectorRankSelectDirectory

/-- Public bitvector rank/select family shape. -/
abbrev Family :=
  RMQ.RankSelectSpec.BitVectorRankSelectFamily

/-- Public compressed/FID bitvector rank/select directory shape. -/
abbrev CompressedDirectory :=
  RMQ.RankSelectSpec.CompressedBitVectorRankSelectDirectory

/-- Public compressed/FID bitvector rank/select family shape. -/
abbrev CompressedFamily :=
  RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily

/-- Counted fixed-weight bitvector universe used by the compressed/FID budget. -/
abbrev fixedWeightBitstrings :=
  RMQ.RankSelectSpec.fixedWeightBitstrings

/-- Mathlib-free binomial-count recurrence for fixed-weight bitvectors. -/
abbrev binomialCount :=
  RMQ.RankSelectSpec.binomialCount

/-- Number of true bits in a bitvector. -/
abbrev trueCount :=
  RMQ.RankSelectSpec.trueCount

/-- Fixed-weight information-theoretic payload budget for one bitvector. -/
abbrev fixedWeightPayloadBudget :=
  RMQ.RankSelectSpec.fixedWeightPayloadBudget

/-- Fixed-weight bitvector universe count. -/
abbrev fixedWeightBitstringsLength :=
  RMQ.RankSelectSpec.fixedWeightBitstrings_length

/-- Fixed-weight bitvector universes contain no duplicate entries. -/
abbrev fixedWeightBitstringsNodup :=
  RMQ.RankSelectSpec.fixedWeightBitstrings_nodup

/-- Canonical fixed-weight encoder into the counted universe. -/
abbrev fixedWeightEncode? :=
  RMQ.RankSelectSpec.fixedWeightEncode?

/-- Canonical fixed-weight decoder from the counted universe. -/
abbrev fixedWeightDecode? :=
  RMQ.RankSelectSpec.fixedWeightDecode?

/-- Total canonical fixed-weight code for a bitvector. -/
abbrev fixedWeightCode :=
  RMQ.RankSelectSpec.fixedWeightCode

/-- The total canonical code is produced by `fixedWeightEncode?`. -/
abbrev fixedWeightEncodeEqSomeFixedWeightCode :=
  RMQ.RankSelectSpec.fixedWeightEncode?_eq_some_fixedWeightCode

/-- Encode/decode round-trip fact for the canonical fixed-weight codec spine. -/
abbrev fixedWeightCodecRoundTrip :=
  RMQ.RankSelectSpec.fixedWeightCodec_roundTrip

/-- Valid decoded entries encode back to their source index. -/
abbrev fixedWeightEncodeFixedWeightDecode
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :=
  RMQ.RankSelectSpec.fixedWeightEncode?_fixedWeightDecode? hdec

/-- Two-sided characterization of canonical fixed-weight decode. -/
abbrev fixedWeightDecodeEqSomeIff
    {n k code : Nat} {bits : List Bool} :=
  RMQ.RankSelectSpec.fixedWeightDecode?_eq_some_iff
    (n := n) (k := k) (code := code) (bits := bits)

/-- Encoded fixed-weight indices are bounded by the binomial-count universe. -/
abbrev fixedWeightEncodeLtBinomialCount
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :=
  RMQ.RankSelectSpec.fixedWeightEncode?_lt_binomialCount henc

/-- The total canonical code is bounded by the binomial-count universe. -/
abbrev fixedWeightCodeLtBinomialCount :=
  RMQ.RankSelectSpec.fixedWeightCode_lt_binomialCount

/-- Encoded fixed-weight indices fit in the fixed-weight payload budget. -/
abbrev fixedWeightEncodeLtPayloadBudgetPow
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :=
  RMQ.RankSelectSpec.fixedWeightEncode?_lt_payloadBudgetPow henc

/-- The total canonical code fits in the fixed-weight payload budget. -/
abbrev fixedWeightCodeLtPayloadBudgetPow :=
  RMQ.RankSelectSpec.fixedWeightCode_lt_payloadBudgetPow

/-- Concrete fixed-weight packed payload for one bitvector. -/
abbrev fixedWeightPackedPayload :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload

/-- The packed fixed-weight payload has exactly the fixed-weight budget length. -/
abbrev fixedWeightPackedPayloadLength :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload_length

/-- Decoding the packed payload word as a natural recovers the canonical code. -/
abbrev fixedWeightPackedPayloadBitsToNatLE :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload_bitsToNatLE

/-- Decoding the packed payload code recovers the original bitvector. -/
abbrev fixedWeightDecodePackedPayload :=
  RMQ.RankSelectSpec.fixedWeightDecode?_packedPayload

/-- Combined fixed-weight packed-payload profile. -/
abbrev fixedWeightPackedPayloadProfile :=
  RMQ.RankSelectSpec.fixedWeightPackedPayload_profile

/-- Charged full-payload readback of the concrete fixed-weight packed payload. -/
abbrev fixedWeightPackedReadbackPayloadCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackPayloadCosted

/-- Charged full-payload decode of the concrete fixed-weight packed payload. -/
abbrev fixedWeightPackedReadbackDecodeCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackDecodeCosted

/-- Access through the charged fixed-weight packed readback decoder. -/
abbrev fixedWeightPackedReadbackAccessCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackAccessCosted

/-- Rank through the charged fixed-weight packed readback decoder. -/
abbrev fixedWeightPackedReadbackRankCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackRankCosted

/-- Select through the charged fixed-weight packed readback decoder. -/
abbrev fixedWeightPackedReadbackSelectCosted :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackSelectCosted

/-- Concrete charged packed-payload readback directory for one bitvector. -/
abbrev fixedWeightPackedReadbackDirectory :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackDirectory

/-- Profile for the charged packed-payload readback directory. -/
abbrev fixedWeightPackedReadbackDirectoryProfile :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackDirectory_profile

/-- Number of bounded payload words in the chunked packed readback view. -/
abbrev fixedWeightPackedReadbackWordCount :=
  RMQ.RankSelectSpec.fixedWeightPackedReadbackWordCount

/-- Chunked bounded-word readback data for the packed fixed-weight payload. -/
abbrev FixedWeightPackedReadbackData :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData

/-- Canonical chunked bounded-word readback data. -/
abbrev fixedWeightPackedReadbackDataOfChunks :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData.ofChunks

/-- Profile for chunked bounded-word packed readback data. -/
abbrev fixedWeightPackedReadbackDataProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData.profile data

/-- Profile for canonical chunked bounded-word packed readback data. -/
abbrev fixedWeightPackedReadbackDataOfChunksProfile
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :=
  RMQ.RankSelectSpec.FixedWeightPackedReadbackData.ofChunks_profile
    bits hword

/-- Decoded fixed-weight entries have the requested length and true-count. -/
abbrev fixedWeightDecodeMemLengthTrueCount
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :=
  RMQ.RankSelectSpec.fixedWeightDecode?_mem_length_trueCount hdec

/-- Public compressed/FID family theorem shape. -/
abbrev compressedFixedWeightConstantQueryProfile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family :
      CompressedFamily overhead queryCost) :=
  RMQ.RankSelectSpec.CompressedBitVectorRankSelectFamily.fixed_weight_constant_query_profile
    family

/-- Auxiliary-overhead budget for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkOverhead :=
  RMQ.GenericSelect.jacobsonClarkRankSelectOverhead

/-- Uniform modeled query cost for the concrete Jacobson/Clark family. -/
abbrev jacobsonClarkQueryCost :=
  RMQ.GenericSelect.jacobsonClarkRankSelectQueryCost

/-- Concrete Jacobson/Clark directory for one stored bitvector. -/
abbrev jacobsonClarkDirectory :=
  RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory

/-- Concrete Jacobson/Clark rank/select family. -/
abbrev jacobsonClarkFamily :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily

/--
Public `n + o(n)`, constant-query theorem for the concrete Jacobson/Clark
rank/select family.
-/
abbrev jacobsonClarkNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile

/--
Public word-bounded profile for the concrete Jacobson/Clark rank/select
family, exposing the machine-word read bounds carried by the concrete
components.
-/
abbrev jacobsonClarkWordBoundedNPlusOConstantQuery :=
  RMQ.GenericSelect.jacobsonClarkRankSelectFamily_word_bounded_n_plus_o_constant_query_profile

end RMQ.RankSelect
