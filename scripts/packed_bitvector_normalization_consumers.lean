import RMQ.Core.WordRAM.Bitvector.Normalization
open RMQ.PackedBitvector
example (target : Bool) (bits : List Bool) (limit : Nat) :
    RMQ.Succinct.rankPrefix false (normalize target bits) limit =
      RMQ.Succinct.rankPrefix target bits limit :=
  (normalization_semantics target bits).2.1 limit
example (target : Bool) (bits : List Bool) (occurrence : Nat) :
    RMQ.Succinct.select false (normalize target bits) occurrence =
      RMQ.Succinct.select target bits occurrence :=
  (normalization_semantics target bits).2.2 occurrence
#print axioms RMQ.PackedBitvector.normalize_length
#print axioms RMQ.PackedBitvector.rankPrefix_normalize
#print axioms RMQ.PackedBitvector.selectFrom_normalize
#print axioms RMQ.PackedBitvector.select_normalize
#print axioms RMQ.PackedBitvector.normalize_numeric
#print axioms RMQ.PackedBitvector.normalize_numeric_packet
#print axioms RMQ.PackedBitvector.normalize_optional_numeric_packet
#print axioms RMQ.PackedBitvector.normalization_semantics
#print axioms RMQ.PackedBitvector.identity_rank_transport_fails
#print axioms RMQ.PackedBitvector.identity_select_transport_fails