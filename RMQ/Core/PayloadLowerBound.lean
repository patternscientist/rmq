import RMQ.Core.TableModel
import RMQ.Core.LowerBound

/-!
# Payload-accounted lossless encodings

This module is the small joint between the table/payload accounting model and
the generic finite encoding lower-bound API.  It keeps `Core.LowerBound` pure:
fixed-length bitstring capacity does not know about states or payload views,
while this adapter explains how a state with counted payload bits induces a
lossless fixed-length encoding.
-/

namespace RMQ

namespace LowerBound

/--
A lossless finite-domain encoding obtained by building a state and reading its
counted payload view.

The lower-bound encoding is over the serialized `payloadBits`.  The charged
`payloadBitCount` may include padding or side conditions, so it is related by
separate inequalities rather than identified with `bits`.
-/
structure PayloadLosslessEncoding (domain : List alpha) (bits : Nat) where
  State : Type u
  buildState : alpha -> State
  payloadView : TableModel.PayloadView State
  length_eq :
    forall {x : alpha}, List.Mem x domain ->
      (payloadView.payloadBits (buildState x)).length = bits
  injective_on :
    forall {left right : alpha},
      List.Mem left domain ->
        List.Mem right domain ->
          payloadView.payloadBits (buildState left) =
            payloadView.payloadBits (buildState right) ->
          left = right

namespace PayloadLosslessEncoding

/-- Promote a plain fixed-length lossless encoding to an exact payload view. -/
def ofLosslessEncoding
    {domain : List alpha} {bits : Nat}
    (encoding : LosslessEncoding domain bits) :
    PayloadLosslessEncoding domain bits where
  State := alpha
  buildState x := x
  payloadView := TableModel.PayloadView.exact encoding.encode
  length_eq := by
    intro x hx
    exact encoding.length_eq hx
  injective_on := by
    intro left right hleft hright hpayload
    exact encoding.injective_on hleft hright hpayload

/-- Forget payload accounting and keep only the fixed-length lossless encoder. -/
def toLosslessEncoding
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits) :
    LosslessEncoding domain bits where
  encode x := encoding.payloadView.payloadBits (encoding.buildState x)
  length_eq := by
    intro x hx
    exact encoding.length_eq hx
  injective_on := by
    intro left right hleft hright hpayload
    exact encoding.injective_on hleft hright hpayload

theorem toLosslessEncoding_encode
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits) (x : alpha) :
    (encoding.toLosslessEncoding).encode x =
      encoding.payloadView.payloadBits (encoding.buildState x) := by
  rfl

theorem ofLosslessEncoding_payloadBits
    {domain : List alpha} {bits : Nat}
    (encoding : LosslessEncoding domain bits) (x : alpha) :
    (ofLosslessEncoding encoding).payloadView.payloadBits
        ((ofLosslessEncoding encoding).buildState x) =
      encoding.encode x := by
  rfl

theorem ofLosslessEncoding_payloadBitCount
    {domain : List alpha} {bits : Nat}
    (encoding : LosslessEncoding domain bits) (x : alpha) :
    (ofLosslessEncoding encoding).payloadView.payloadBitCount
        ((ofLosslessEncoding encoding).buildState x) =
      (encoding.encode x).length := by
  rfl

theorem ofLosslessEncoding_toLosslessEncoding_encode
    {domain : List alpha} {bits : Nat}
    (encoding : LosslessEncoding domain bits) (x : alpha) :
    ((ofLosslessEncoding encoding).toLosslessEncoding).encode x =
      encoding.encode x := by
  rfl

/--
Add proof-only or auxiliary state without changing the payload encoding.

This is the generic version of the RMQ state-encoding pattern where certificates
or materialized views are carried by the state but not counted as payload bits.
-/
def withUnchargedAux
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (aux : encoding.State -> Type v)
    (mkAux : forall x : alpha, aux (encoding.buildState x)) :
    PayloadLosslessEncoding domain bits where
  State := Sigma aux
  buildState x := ⟨encoding.buildState x, mkAux x⟩
  payloadView := encoding.payloadView.withUnchargedAux aux
  length_eq := by
    intro x hx
    simpa using encoding.length_eq hx
  injective_on := by
    intro left right hleft hright hpayload
    apply encoding.injective_on hleft hright
    simpa using hpayload

@[simp] theorem withUnchargedAux_payloadBits
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (aux : encoding.State -> Type v)
    (mkAux : forall x : alpha, aux (encoding.buildState x))
    (x : alpha) :
    (encoding.withUnchargedAux aux mkAux).payloadView.payloadBits
        ((encoding.withUnchargedAux aux mkAux).buildState x) =
      encoding.payloadView.payloadBits (encoding.buildState x) := by
  rfl

@[simp] theorem withUnchargedAux_payloadBitCount
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (aux : encoding.State -> Type v)
    (mkAux : forall x : alpha, aux (encoding.buildState x))
    (x : alpha) :
    (encoding.withUnchargedAux aux mkAux).payloadView.payloadBitCount
        ((encoding.withUnchargedAux aux mkAux).buildState x) =
      encoding.payloadView.payloadBitCount (encoding.buildState x) := by
  rfl

/-- Capacity bound for payload-accounted lossless encodings. -/
theorem domain_length_le_two_pow
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (hnodup : domain.Nodup) :
    domain.length <= 2 ^ bits :=
  domain_length_le_two_pow_of_lossless_encoding
    encoding.toLosslessEncoding hnodup

/--
Counting lower bound for payload-accounted fixed-length encodings.

This is the same capacity argument as `LowerBound.lower_le_bits...`, routed
through the payload-accounted state view.
-/
theorem lower_le_bits_of_count_lower_bound
    {domain : List alpha} {bits lower : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (hnodup : domain.Nodup)
    (hcount_lower : 2 ^ lower <= domain.length) :
    lower <= bits :=
  RMQ.LowerBound.lower_le_bits_of_count_lower_bound
    (encoding.domain_length_le_two_pow hnodup) hcount_lower

/-- Any state in the encoded domain charges at least the fixed payload length. -/
theorem payloadBitCount_ge_bits_of_mem
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    {x : alpha} (hx : List.Mem x domain) :
    bits <=
      encoding.payloadView.payloadBitCount (encoding.buildState x) := by
  have hlen := encoding.length_eq hx
  have hle :=
    encoding.payloadView.payloadBits_length_le (encoding.buildState x)
  rw [hlen] at hle
  exact hle

theorem bits_le_of_payloadBitCount_le_of_mem
    {domain : List alpha} {bits budget : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    {x : alpha} (hx : List.Mem x domain)
    (hbudget :
      encoding.payloadView.payloadBitCount (encoding.buildState x) <= budget) :
    bits <= budget := by
  exact Nat.le_trans
    (encoding.payloadBitCount_ge_bits_of_mem hx) hbudget

theorem lower_le_payloadBitCount_of_mem_of_count_lower_bound
    {domain : List alpha} {bits lower : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (hnodup : domain.Nodup)
    (hcount_lower : 2 ^ lower <= domain.length)
    {x : alpha} (hx : List.Mem x domain) :
    lower <=
      encoding.payloadView.payloadBitCount (encoding.buildState x) := by
  exact Nat.le_trans
    (encoding.lower_le_bits_of_count_lower_bound hnodup hcount_lower)
    (encoding.payloadBitCount_ge_bits_of_mem hx)

theorem lower_le_budget_of_payloadBitCount_bound
    {domain : List alpha} {bits lower budget : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (hnodup : domain.Nodup)
    (hcount_lower : 2 ^ lower <= domain.length)
    {x : alpha} (hx : List.Mem x domain)
    (hbudget :
      forall {y : alpha}, List.Mem y domain ->
        encoding.payloadView.payloadBitCount (encoding.buildState y) <=
          budget) :
    lower <= budget := by
  exact Nat.le_trans
    (encoding.lower_le_payloadBitCount_of_mem_of_count_lower_bound
      hnodup hcount_lower hx)
    (hbudget hx)

/-- Exact payload views charge exactly the fixed payload length on-domain. -/
theorem exact_payloadBitCount_eq_bits_of_mem
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (hexact :
      forall s,
        encoding.payloadView.payloadBitCount s =
          (encoding.payloadView.payloadBits s).length)
    {x : alpha} (hx : List.Mem x domain) :
    encoding.payloadView.payloadBitCount (encoding.buildState x) = bits := by
  rw [hexact, encoding.length_eq hx]

end PayloadLosslessEncoding

/-- Capacity bound spelling that keeps the payload-accounted adapter explicit. -/
theorem domain_length_le_two_pow_of_payload_lossless_encoding
    {domain : List alpha} {bits : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (hnodup : domain.Nodup) :
    domain.length <= 2 ^ bits :=
  PayloadLosslessEncoding.domain_length_le_two_pow encoding hnodup

theorem lower_le_budget_of_payload_lossless_encoding
    {domain : List alpha} {bits lower budget : Nat}
    (encoding : PayloadLosslessEncoding domain bits)
    (hnodup : domain.Nodup)
    (hcount_lower : 2 ^ lower <= domain.length)
    {x : alpha} (hx : List.Mem x domain)
    (hbudget :
      forall {y : alpha}, List.Mem y domain ->
        encoding.payloadView.payloadBitCount (encoding.buildState y) <=
          budget) :
    lower <= budget :=
  encoding.lower_le_budget_of_payloadBitCount_bound
    hnodup hcount_lower hx hbudget

/--
Two-sided payload-space bounds for a finite domain.

`count_lower` is the reusable information-theoretic lower side, while
`upperEncoding` is a concrete payload-accounted upper witness.  This structure
does not prescribe how queries are answered; spokes instantiate it with their
own exact decoder contracts.
-/
structure PayloadSpaceBounds (domain : List alpha) (lower upper : Nat) where
  nodup : domain.Nodup
  count_lower : 2 ^ lower <= domain.length
  upperEncoding : PayloadLosslessEncoding domain upper

namespace PayloadSpaceBounds

theorem lower_le_bits
    {domain : List alpha} {lower upper bits : Nat}
    (bounds : PayloadSpaceBounds domain lower upper)
    (encoding : PayloadLosslessEncoding domain bits) :
    lower <= bits :=
  encoding.lower_le_bits_of_count_lower_bound
    bounds.nodup bounds.count_lower

theorem lower_le_payloadBitCount_of_mem
    {domain : List alpha} {lower upper bits : Nat}
    (bounds : PayloadSpaceBounds domain lower upper)
    (encoding : PayloadLosslessEncoding domain bits)
    {x : alpha} (hx : List.Mem x domain) :
    lower <=
      encoding.payloadView.payloadBitCount (encoding.buildState x) :=
  encoding.lower_le_payloadBitCount_of_mem_of_count_lower_bound
    bounds.nodup bounds.count_lower hx

theorem lower_le_budget
    {domain : List alpha} {lower upper bits budget : Nat}
    (bounds : PayloadSpaceBounds domain lower upper)
    (encoding : PayloadLosslessEncoding domain bits)
    {x : alpha} (hx : List.Mem x domain)
    (hbudget :
      forall {y : alpha}, List.Mem y domain ->
        encoding.payloadView.payloadBitCount (encoding.buildState y) <=
          budget) :
    lower <= budget :=
  encoding.lower_le_budget_of_payloadBitCount_bound
    bounds.nodup bounds.count_lower hx hbudget

theorem upper_domain_length_le_two_pow
    {domain : List alpha} {lower upper : Nat}
    (bounds : PayloadSpaceBounds domain lower upper) :
    domain.length <= 2 ^ upper :=
  bounds.upperEncoding.domain_length_le_two_pow bounds.nodup

theorem lower_le_upper
    {domain : List alpha} {lower upper : Nat}
    (bounds : PayloadSpaceBounds domain lower upper) :
    lower <= upper :=
  bounds.lower_le_bits bounds.upperEncoding

end PayloadSpaceBounds

end LowerBound

end RMQ
