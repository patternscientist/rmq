import RMQ.Core.SuccinctSpace.BPAccess

namespace RMQ

namespace SuccinctSpace

/--
A certified word-RAM/broadword directory for exact RMQ over Cartesian-shape
representatives of size `n`.

The encoded payload is the canonical `2*n` shape payload followed by an
auxiliary payload of exactly `overhead` bits.  The query procedure consumes only
that encoded payload and is costed by the supplied model.  The `query_exact`
field is the anti-vacuity condition: the costed query must refine the ordinary
leftmost RMQ answer on the canonical representative array.
-/
structure BroadwordRMQDirectory
    (n overhead queryCost : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  queryEncodedCosted : List Bool -> Nat -> Nat -> Costed (Option Nat)
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  query_cost_le :
    forall payload left right,
      (queryEncodedCosted payload left right).cost <= queryCost
  query_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len : Nat},
          0 < len ->
            left + len <= n ->
              (queryEncodedCosted
                (EncodingLowerBound.canonicalShapePayload shape ++
                  encodeAux (buildAux shape))
                left (left + len)).erase =
                  some (scanWindow shape.representative left len)

namespace BroadwordRMQDirectory

private theorem take_append_replicate_of_lengths
    {alpha : Type} (xs ys : List alpha) (pad : Nat) (x : alpha)
    {xsLen ysLen : Nat}
    (hxs : xs.length = xsLen) (hys : ys.length = ysLen) :
    ((xs ++ ys) ++ List.replicate pad x).take (xsLen + ysLen) =
      xs ++ ys := by
  have hlen : (xs ++ ys).length = xsLen + ysLen := by
    simp [hxs, hys]
  calc
    ((xs ++ ys) ++ List.replicate pad x).take (xsLen + ysLen) =
        ((xs ++ ys) ++ List.replicate pad x).take (xs ++ ys).length := by
      rw [hlen]
    _ = (xs ++ ys).take (xs ++ ys).length := by
      rw [List.take_append_of_le_length (Nat.le_refl _)]
    _ = xs ++ ys := by
      rw [List.take_of_length_le (Nat.le_refl _)]

def State {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) : Type :=
  Cartesian.CartesianShape × directory.Aux

def buildState {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (shape : Cartesian.CartesianShape) : directory.State :=
  (shape, directory.buildAux shape)

def encodeState {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) : List Bool :=
  EncodingLowerBound.canonicalShapePayload state.1 ++
    directory.encodeAux state.2

def queryStateCosted {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) : Costed (Option Nat) :=
  directory.queryEncodedCosted (directory.encodeState state) left right

theorem queryStateCosted_cost_le
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) :
    (directory.queryStateCosted state left right).cost <= queryCost := by
  exact directory.query_cost_le (directory.encodeState state) left right

theorem queryStateCosted_exact
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryStateCosted (directory.buildState shape)
        left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  exact directory.query_exact hshape hlen hbound

/-- Forget a certified broadword directory to the existing exact RMQ payload API. -/
def stateEncoding
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.ExactRMQStateEncoding n (2 * n + overhead) where
  State := directory.State
  buildState := directory.buildState
  encodeState := directory.encodeState
  queryEncoded := fun payload left right =>
    (directory.queryEncodedCosted payload left right).erase
  sample shape := shape.representative
  length_eq := by
    intro shape hshape
    have hshapePayload :
        (EncodingLowerBound.canonicalShapePayload shape).length = 2 * n := by
      simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
        (EncodingLowerBound.canonicalRepresentativeStateEncoding n).length_eq
          hshape
    have haux := directory.aux_length_eq hshape
    simp [encodeState, buildState, hshapePayload, haux]
  sample_length_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_length_eq
        hshape
  sample_shape_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_shape_eq
        hshape
  query_exact := by
    intro shape hshape left len hlen hbound
    exact directory.query_exact hshape hlen hbound

theorem payloadBitCount_eq
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    ((directory.stateEncoding).payloadView).payloadBitCount
        ((directory.stateEncoding).buildState shape) =
      2 * n + overhead := by
  exact
    EncodingLowerBound.ExactRMQStateEncoding.payloadBitCount_eq_bits_of_mem
      directory.stateEncoding hshape

/-- Payload-space bounds induced by a certified broadword directory. -/
def payloadSpaceBounds
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) :
    LowerBound.PayloadSpaceBounds
      (Cartesian.shapesOfSize n)
      (EncodingLowerBound.logSlackLower n)
      (2 * n + overhead) where
  nodup := Cartesian.shapesOfSize_nodup n
  count_lower := by
    simpa [EncodingLowerBound.logSlackLower, Cartesian.shapeCount] using
      EncodingLowerBound.shapeCount_log_lower_of_quadratic_bound
        (EncodingLowerBound.shapeCount_quadratic_lower n)
  upperEncoding := directory.stateEncoding.payloadLosslessEncoding

theorem payloadSpaceBounds_lower_le_upper
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.logSlackLower n <= 2 * n + overhead := by
  exact directory.payloadSpaceBounds.lower_le_upper

theorem logSlackLower_le_payloadBudget
    {n overhead queryCost : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    EncodingLowerBound.logSlackLower n <= 2 * n + overhead := by
  have hbudget :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          ((directory.stateEncoding).payloadView).payloadBitCount
            ((directory.stateEncoding).buildState shape) <=
              2 * n + overhead := by
    intro shape hmem
    rw [directory.payloadBitCount_eq hmem]
    exact Nat.le_refl _
  exact
    EncodingLowerBound.logSlackLower_le_budget_of_exactRMQStateEncoding
      directory.stateEncoding hshape hbudget

/--
Pad a certified directory to a larger published overhead budget.

This is useful when a concrete construction has an exact auxiliary encoding
length but the final theorem wants a cleaner upper-bound expression.  The query
decoder truncates the padded payload back to the original exact prefix, so the
query proof and query-cost bound are preserved rather than re-assumed.
-/
def padToOverhead
    {n overhead queryCost budget : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (hbudget : overhead <= budget) :
    BroadwordRMQDirectory n budget queryCost where
  Aux := directory.Aux
  buildAux := directory.buildAux
  encodeAux aux :=
    directory.encodeAux aux ++ List.replicate (budget - overhead) false
  queryEncodedCosted payload left right :=
    directory.queryEncodedCosted (payload.take (2 * n + overhead)) left right
  aux_length_eq := by
    intro shape hshape
    have haux := directory.aux_length_eq hshape
    simp [haux]
    omega
  query_cost_le := by
    intro payload left right
    exact directory.query_cost_le (payload.take (2 * n + overhead)) left right
  query_exact := by
    intro shape hshape left len hlen hbound
    have hshapePayload :
        (EncodingLowerBound.canonicalShapePayload shape).length = 2 * n := by
      simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
        (EncodingLowerBound.canonicalRepresentativeStateEncoding n).length_eq
          hshape
    have haux := directory.aux_length_eq hshape
    have htake :
        ((EncodingLowerBound.canonicalShapePayload shape ++
            directory.encodeAux (directory.buildAux shape)) ++
              List.replicate (budget - overhead) false).take
            (2 * n + overhead) =
          EncodingLowerBound.canonicalShapePayload shape ++
            directory.encodeAux (directory.buildAux shape) :=
      take_append_replicate_of_lengths
        (EncodingLowerBound.canonicalShapePayload shape)
        (directory.encodeAux (directory.buildAux shape))
        (budget - overhead) false hshapePayload haux
    have hexact := directory.query_exact hshape hlen hbound
    have hpayload :
        (EncodingLowerBound.canonicalShapePayload shape ++
            (directory.encodeAux (directory.buildAux shape) ++
              List.replicate (budget - overhead) false)).take
            (2 * n + overhead) =
          EncodingLowerBound.canonicalShapePayload shape ++
            directory.encodeAux (directory.buildAux shape) := by
      simpa [List.append_assoc] using htake
    simpa [hpayload] using hexact

theorem padToOverhead_payloadBitCount_eq
    {n overhead queryCost budget : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (hbudget : overhead <= budget)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    ((((directory.padToOverhead hbudget).stateEncoding).payloadView).payloadBitCount
        (((directory.padToOverhead hbudget).stateEncoding).buildState shape)) =
      2 * n + budget := by
  exact (directory.padToOverhead hbudget).payloadBitCount_eq hshape

theorem padToOverhead_queryStateCosted_cost_le
    {n overhead queryCost budget : Nat}
    (directory : BroadwordRMQDirectory n overhead queryCost)
    (hbudget : overhead <= budget)
    (state : (directory.padToOverhead hbudget).State)
    (left right : Nat) :
    ((directory.padToOverhead hbudget).queryStateCosted state left right).cost <=
      queryCost := by
  exact (directory.padToOverhead hbudget).queryStateCosted_cost_le
    state left right

end BroadwordRMQDirectory

/--
A family of certified broadword RMQ directories with one query-cost constant and
sublinear auxiliary payload overhead.
-/
structure BroadwordSuccinctRMQFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall n : Nat, BroadwordRMQDirectory n (overhead n) queryCost
  overhead_littleO : LittleOLinear overhead

namespace BroadwordSuccinctRMQFamily

/--
The theorem shape for a researcher-facing `2*n + o(n)`, constant-query RMQ
upper bound in the word-RAM model.

The statement keeps all anti-vacuity witnesses visible: each size has an exact
RMQ state encoding, every on-domain built state charges exactly `2*n + overhead
n` payload bits, every supplied broadword query costs at most `queryCost`, and
valid queries refine the canonical representative RMQ answer.
-/
theorem two_n_plus_o_constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : BroadwordSuccinctRMQFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <= 2 * n + overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((((family.directory n).stateEncoding).payloadView).payloadBitCount
              (((family.directory n).stateEncoding).buildState shape) =
                2 * n + overhead n)) /\
        (forall (state : (family.directory n).State) left right,
          ((family.directory n).queryStateCosted state left right).cost <=
            queryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  ((family.directory n).queryStateCosted
                    ((family.directory n).buildState shape)
                    left (left + len)).erase =
                      some (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    constructor
    · exact (family.directory n).payloadSpaceBounds_lower_le_upper
    · constructor
      · intro shape hshape
        exact (family.directory n).payloadBitCount_eq hshape
      · constructor
        · intro state left right
          exact (family.directory n).queryStateCosted_cost_le state left right
        · intro shape hshape left len hlen hbound
          exact (family.directory n).queryStateCosted_exact hshape hlen hbound

end BroadwordSuccinctRMQFamily

/--
Canonical componentized auxiliary-budget shape for the eventual
balanced-parentheses broadword directory.

The four slots are intentionally generic: rank directory, select directory,
excess/RMQ navigation directory, and fixed microtable/block metadata.  Concrete
implementations can set unused components to zero.
-/
def bpAuxOverhead
    (rank select excess micro : Nat -> Nat) (n : Nat) : Nat :=
  rank n + select n + excess n + micro n

theorem bpAuxOverhead_littleO
    {rank select excess micro : Nat -> Nat}
    (hrank : LittleOLinear rank)
    (hselect : LittleOLinear select)
    (hexcess : LittleOLinear excess)
    (hmicro : LittleOLinear micro) :
    LittleOLinear (bpAuxOverhead rank select excess micro) := by
  unfold bpAuxOverhead
  exact ((hrank.add hselect).add hexcess).add hmicro

def sampledBPAuxOverhead
    (rankSlots selectSlots excessSlots microSlots : Nat) : Nat -> Nat :=
  bpAuxOverhead
    (sampledDirectoryOverhead rankSlots)
    (sampledDirectoryOverhead selectSlots)
    (sampledDirectoryOverhead excessSlots)
    (sampledDirectoryOverhead microSlots)

theorem sampledBPAuxOverhead_littleO
    (rankSlots selectSlots excessSlots microSlots : Nat) :
    LittleOLinear
      (sampledBPAuxOverhead rankSlots selectSlots excessSlots microSlots) := by
  unfold sampledBPAuxOverhead
  exact bpAuxOverhead_littleO
    (sampledDirectoryOverhead_littleO rankSlots)
    (sampledDirectoryOverhead_littleO selectSlots)
    (sampledDirectoryOverhead_littleO excessSlots)
    (sampledDirectoryOverhead_littleO microSlots)

/--
BP-native certified word-RAM/broadword directory for exact RMQ over
Cartesian-shape representatives of size `n`.

Unlike `BroadwordRMQDirectory`, whose base payload is the decoder-oriented
`canonicalShapePayload`, this interface stores the literal balanced-parentheses
code `shape.bpCode` as the counted `2*n` payload.  This is the representation
boundary expected by a packed BP/rank-select RMQ construction.
-/
structure BPBroadwordRMQDirectory
    (n overhead queryCost : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  queryEncodedCosted : List Bool -> Nat -> Nat -> Costed (Option Nat)
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  query_cost_le :
    forall payload left right,
      (queryEncodedCosted payload left right).cost <= queryCost
  query_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len : Nat},
          0 < len ->
            left + len <= n ->
              (queryEncodedCosted
                (shape.bpCode ++ encodeAux (buildAux shape))
                left (left + len)).erase =
                  some (scanWindow shape.representative left len)

namespace BPBroadwordRMQDirectory

def State {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) : Type :=
  Cartesian.CartesianShape × directory.Aux

def buildState {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (shape : Cartesian.CartesianShape) : directory.State :=
  (shape, directory.buildAux shape)

def encodeState {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) : List Bool :=
  state.1.bpCode ++ directory.encodeAux state.2

def queryStateCosted {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) : Costed (Option Nat) :=
  directory.queryEncodedCosted (directory.encodeState state) left right

theorem queryStateCosted_cost_le
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (state : directory.State) (left right : Nat) :
    (directory.queryStateCosted state left right).cost <= queryCost := by
  exact directory.query_cost_le (directory.encodeState state) left right

theorem queryStateCosted_exact
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (directory.queryStateCosted (directory.buildState shape)
        left (left + len)).erase =
      some (scanWindow shape.representative left len) := by
  exact directory.query_exact hshape hlen hbound

/-- Forget a BP-native directory to the existing exact RMQ payload API. -/
def stateEncoding
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.ExactRMQStateEncoding n (2 * n + overhead) where
  State := directory.State
  buildState := directory.buildState
  encodeState := directory.encodeState
  queryEncoded := fun payload left right =>
    (directory.queryEncodedCosted payload left right).erase
  sample shape := shape.representative
  length_eq := by
    intro shape hshape
    have hshapePayload :
        shape.bpCode.length = 2 * n :=
      Cartesian.CartesianShape.bpCode_length_of_shapeOfSize
        (Cartesian.mem_shapesOfSize_shapeOfSize hshape)
    have haux := directory.aux_length_eq hshape
    simp [encodeState, buildState, hshapePayload, haux]
  sample_length_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_length_eq
        hshape
  sample_shape_eq := by
    intro shape hshape
    simpa [EncodingLowerBound.canonicalRepresentativeStateEncoding] using
      (EncodingLowerBound.canonicalRepresentativeStateEncoding n).sample_shape_eq
        hshape
  query_exact := by
    intro shape hshape left len hlen hbound
    exact directory.query_exact hshape hlen hbound

theorem payloadOf_eq
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    (shape : Cartesian.CartesianShape) :
    (directory.stateEncoding).payloadOf shape =
      shape.bpCode ++ directory.encodeAux (directory.buildAux shape) := by
  rfl

theorem payloadBitCount_eq
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n)) :
    ((directory.stateEncoding).payloadView).payloadBitCount
        ((directory.stateEncoding).buildState shape) =
      2 * n + overhead := by
  exact
    EncodingLowerBound.ExactRMQStateEncoding.payloadBitCount_eq_bits_of_mem
      directory.stateEncoding hshape

/-- Payload-space bounds induced by a BP-native broadword directory. -/
def payloadSpaceBounds
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) :
    LowerBound.PayloadSpaceBounds
      (Cartesian.shapesOfSize n)
      (EncodingLowerBound.logSlackLower n)
      (2 * n + overhead) where
  nodup := Cartesian.shapesOfSize_nodup n
  count_lower := by
    simpa [EncodingLowerBound.logSlackLower, Cartesian.shapeCount] using
      EncodingLowerBound.shapeCount_log_lower_of_quadratic_bound
        (EncodingLowerBound.shapeCount_quadratic_lower n)
  upperEncoding := directory.stateEncoding.payloadLosslessEncoding

theorem payloadSpaceBounds_lower_le_upper
    {n overhead queryCost : Nat}
    (directory : BPBroadwordRMQDirectory n overhead queryCost) :
    EncodingLowerBound.logSlackLower n <= 2 * n + overhead := by
  exact directory.payloadSpaceBounds.lower_le_upper

end BPBroadwordRMQDirectory

end SuccinctSpace

end RMQ
