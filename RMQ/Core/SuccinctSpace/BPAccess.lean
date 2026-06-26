import RMQ.Core.SuccinctSpace.RankSelect

namespace RMQ

namespace SuccinctSpace

/--
Rank-only directory with the validity condition made explicit.

The older `RankSelectDirectory` requires total rank exactness for every `pos`.
Faithful stored-word rank is naturally exact for `pos <= bits.length`, because
out-of-domain positions need not have a stored sample or payload word.  This
interface is therefore the honest component boundary for broadword
balanced-parentheses access: queries are still uniformly costed for every
input, while semantic exactness is stated on the valid prefix range.
-/
structure ValidRankDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  Aux : Type
  buildAux : Aux
  encodeAux : Aux -> List Bool
  rankCosted : Aux -> Bool -> Nat -> Costed Nat
  aux_length_eq : (encodeAux buildAux).length = overhead
  rank_cost_le :
    forall target pos, (rankCosted buildAux target pos).cost <= queryCost
  rank_exact_of_le :
    forall target {pos : Nat}, pos <= bits.length ->
      (rankCosted buildAux target pos).erase =
        Succinct.rankPrefix target bits pos

namespace ValidRankDirectory

def auxPayload
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost) :
    List Bool :=
  directory.encodeAux directory.buildAux

@[simp] theorem auxPayload_length
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost) :
    directory.auxPayload.length = overhead := by
  exact directory.aux_length_eq

def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankCosted directory.buildAux target pos

theorem rankQueryCosted_cost_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) :
    (directory.rankQueryCosted target pos).cost <= queryCost := by
  exact directory.rank_cost_le target pos

theorem rankQueryCosted_exact_of_le
    {bits : List Bool} {overhead queryCost : Nat}
    (directory : ValidRankDirectory bits overhead queryCost)
    (target : Bool) {pos : Nat} (hpos : pos <= bits.length) :
    (directory.rankQueryCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  exact directory.rank_exact_of_le target hpos

/-- Faithful stored-word rank data exposed through the valid-rank interface. -/
def ofStoredWordRankData
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) :
    ValidRankDirectory bits overhead 3 where
  Aux := Unit
  buildAux := ()
  encodeAux _ := data.encodeAux
  rankCosted _ target pos := data.rankCosted target pos
  aux_length_eq := data.aux_length_eq
  rank_cost_le := by
    intro target pos
    exact data.rankCosted_cost_le_three target pos
  rank_exact_of_le := by
    intro target pos hpos
    exact data.rankCosted_exact target hpos

theorem ofStoredWordRankData_profile
    {bits : List Bool} {overhead : Nat}
    (data : StoredWordRankData bits overhead) :
    ((ofStoredWordRankData data).auxPayload.length = overhead) /\
      forall target pos,
        ((ofStoredWordRankData data).rankQueryCosted target pos).cost <= 3 /\
          (pos <= bits.length ->
            ((ofStoredWordRankData data).rankQueryCosted target pos).erase =
              Succinct.rankPrefix target bits pos) := by
  constructor
  · exact (ofStoredWordRankData data).auxPayload_length
  · intro target pos
    exact ⟨
      (ofStoredWordRankData data).rankQueryCosted_cost_le target pos,
      fun hpos =>
        (ofStoredWordRankData data).rankQueryCosted_exact_of_le target hpos⟩

end ValidRankDirectory

/--
Family-level valid rank component.

This is the rank half of the eventual rank/select layer.  It can already be
fed by `StoredWordRankData`, and later select/navigation components can be
added without weakening this validity-scoped exactness theorem.
-/
structure ValidRankFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall bits : List Bool,
      ValidRankDirectory bits (overhead bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace ValidRankFamily

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).auxPayload.length = overhead bits.length) /\
          forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              (pos <= bits.length ->
                ((family.directory bits).rankQueryCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    constructor
    · exact (family.directory bits).auxPayload_length
    · intro target pos
      exact ⟨
        (family.directory bits).rankQueryCosted_cost_le target pos,
        fun hpos =>
          (family.directory bits).rankQueryCosted_exact_of_le target hpos⟩

end ValidRankFamily

/-- Family of faithful stored-word rank directories over arbitrary bitvectors. -/
structure StoredWordRankDataFamily
    (overhead : Nat -> Nat) where
  data :
    forall bits : List Bool,
      StoredWordRankData bits (overhead bits.length)
  overhead_littleO : LittleOLinear overhead

namespace StoredWordRankDataFamily

def toValidRankFamily
    {overhead : Nat -> Nat}
    (family : StoredWordRankDataFamily overhead) :
    ValidRankFamily overhead 3 where
  directory bits := ValidRankDirectory.ofStoredWordRankData (family.data bits)
  overhead_littleO := family.overhead_littleO

theorem constant_rank_profile
    {overhead : Nat -> Nat}
    (family : StoredWordRankDataFamily overhead) :
    LittleOLinear overhead /\
      forall bits : List Bool,
        (((family.toValidRankFamily).directory bits).auxPayload.length =
            overhead bits.length) /\
          forall target pos,
            (((family.toValidRankFamily).directory bits).rankQueryCosted
                target pos).cost <= 3 /\
              (pos <= bits.length ->
                (((family.toValidRankFamily).directory bits).rankQueryCosted
                    target pos).erase =
                  Succinct.rankPrefix target bits pos) := by
  exact family.toValidRankFamily.constant_query_profile

end StoredWordRankDataFamily

/--
Balanced-parentheses rank/excess access backed by any valid-position rank
directory.

This is the generic version of the stored-word rank/excess component below:
rank exactness is only required for valid prefix positions, which is exactly
what balanced-parentheses excess and prefix-balance facts consume.
-/
structure ValidRankBalancedParensAccess
    (parens : Succinct.BalancedParens) (overhead queryCost : Nat) where
  rankDirectory : ValidRankDirectory parens.bits overhead queryCost

namespace ValidRankBalancedParensAccess

def rankCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  access.rankDirectory.rankQueryCosted target pos

def excessCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (pos : Nat) : Costed Nat :=
  Costed.bind (access.rankCosted true pos) fun opens =>
    Costed.map (fun closes => opens - closes)
      (access.rankCosted false pos)

theorem auxPayload_length
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost) :
    access.rankDirectory.auxPayload.length = overhead := by
  exact access.rankDirectory.auxPayload_length

theorem rankCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).cost <= queryCost := by
  exact access.rankDirectory.rankQueryCosted_cost_le target pos

theorem rankCosted_exact_of_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (target : Bool) {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted target pos).erase =
      Succinct.rankPrefix target parens.bits pos := by
  exact access.rankDirectory.rankQueryCosted_exact_of_le target hpos

theorem close_rank_le_open_rank
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted false pos).erase <=
      (access.rankCosted true pos).erase := by
  calc
    (access.rankCosted false pos).erase =
        Succinct.rankPrefix false parens.bits pos := by
      exact access.rankCosted_exact_of_le false hpos
    _ <= Succinct.rankPrefix true parens.bits pos := by
      exact Succinct.BalancedParens.close_rank_le_open_rank parens hpos
    _ = (access.rankCosted true pos).erase := by
      exact (access.rankCosted_exact_of_le true hpos).symm

theorem final_rank_eq
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost) :
    (access.rankCosted true parens.bits.length).erase =
      (access.rankCosted false parens.bits.length).erase := by
  have hpos : parens.bits.length <= parens.bits.length := Nat.le_refl _
  calc
    (access.rankCosted true parens.bits.length).erase =
        Succinct.rankPrefix true parens.bits parens.bits.length := by
      exact access.rankCosted_exact_of_le true hpos
    _ = Succinct.rankPrefix false parens.bits parens.bits.length := by
      exact Succinct.BalancedParens.final_rank_eq parens
    _ = (access.rankCosted false parens.bits.length).erase := by
      exact (access.rankCosted_exact_of_le false hpos).symm

theorem excessCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    (pos : Nat) :
    (access.excessCosted pos).cost <= 2 * queryCost := by
  have hopen := access.rankCosted_cost_le true pos
  have hclose := access.rankCosted_cost_le false pos
  have hsum :
      (access.rankCosted true pos).cost +
          (access.rankCosted false pos).cost <=
        queryCost + queryCost :=
    Nat.add_le_add hopen hclose
  simpa [excessCosted, Costed.map, Nat.two_mul] using hsum

theorem excessCosted_exact_of_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.excessCosted pos).erase =
      Succinct.rankPrefix true parens.bits pos -
        Succinct.rankPrefix false parens.bits pos := by
  unfold excessCosted
  rw [Costed.erase_bind, Costed.erase_map]
  rw [access.rankCosted_exact_of_le true hpos,
    access.rankCosted_exact_of_le false hpos]

theorem profile
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : ValidRankBalancedParensAccess parens overhead queryCost) :
    access.rankDirectory.auxPayload.length = overhead /\
      (forall target pos,
        (access.rankCosted target pos).cost <= queryCost /\
          (pos <= parens.bits.length ->
            (access.rankCosted target pos).erase =
              Succinct.rankPrefix target parens.bits pos)) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 2 * queryCost /\
          (pos <= parens.bits.length ->
            (access.excessCosted pos).erase =
              Succinct.rankPrefix true parens.bits pos -
                Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact access.auxPayload_length
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le target pos,
        fun hpos => access.rankCosted_exact_of_le target hpos⟩
    · constructor
      · intro pos hpos
        exact access.close_rank_le_open_rank hpos
      · constructor
        · exact access.final_rank_eq
        · intro pos
          exact ⟨access.excessCosted_cost_le pos,
            fun hpos => access.excessCosted_exact_of_le hpos⟩

end ValidRankBalancedParensAccess

/-- Family-level BP rank/excess component backed by valid-position rank. -/
structure ValidRankBalancedParensAccessFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  access :
    forall parens : Succinct.BalancedParens,
      ValidRankBalancedParensAccess parens
        (overhead parens.bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace ValidRankBalancedParensAccessFamily

def ofValidRankFamily
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankFamily overhead queryCost) :
    ValidRankBalancedParensAccessFamily overhead queryCost where
  access parens := { rankDirectory := family.directory parens.bits }
  overhead_littleO := family.overhead_littleO

theorem constant_rank_excess_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankBalancedParensAccessFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        ((family.access parens).rankDirectory.auxPayload.length =
          overhead parens.bits.length) /\
          (forall target pos,
            ((family.access parens).rankCosted target pos).cost <=
                queryCost /\
              (pos <= parens.bits.length ->
                ((family.access parens).rankCosted target pos).erase =
                  Succinct.rankPrefix target parens.bits pos)) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              ((family.access parens).rankCosted false pos).erase <=
                ((family.access parens).rankCosted true pos).erase) /\
          (((family.access parens).rankCosted true parens.bits.length).erase =
            ((family.access parens).rankCosted false parens.bits.length).erase) /\
          (forall pos,
            ((family.access parens).excessCosted pos).cost <=
                2 * queryCost /\
              (pos <= parens.bits.length ->
                ((family.access parens).excessCosted pos).erase =
                  Succinct.rankPrefix true parens.bits pos -
                    Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact family.overhead_littleO
  · intro parens
    exact (family.access parens).profile

theorem ofValidRankFamily_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : ValidRankFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        (((ofValidRankFamily family).access parens).rankDirectory.auxPayload.length =
          overhead parens.bits.length) /\
          (forall target pos,
            (((ofValidRankFamily family).access parens).rankCosted
                target pos).cost <= queryCost /\
              (pos <= parens.bits.length ->
                (((ofValidRankFamily family).access parens).rankCosted
                    target pos).erase =
                  Succinct.rankPrefix target parens.bits pos)) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              (((ofValidRankFamily family).access parens).rankCosted
                  false pos).erase <=
                (((ofValidRankFamily family).access parens).rankCosted
                  true pos).erase) /\
          ((((ofValidRankFamily family).access parens).rankCosted
              true parens.bits.length).erase =
            (((ofValidRankFamily family).access parens).rankCosted
              false parens.bits.length).erase) /\
          (forall pos,
            (((ofValidRankFamily family).access parens).excessCosted pos).cost <=
                2 * queryCost /\
              (pos <= parens.bits.length ->
                (((ofValidRankFamily family).access parens).excessCosted
                    pos).erase =
                  Succinct.rankPrefix true parens.bits pos -
                    Succinct.rankPrefix false parens.bits pos)) := by
  exact (ofValidRankFamily family).constant_rank_excess_profile

end ValidRankBalancedParensAccessFamily

/--
Balanced-parentheses rank/excess access backed by the faithful stored word-rank
component above.
-/
structure StoredRankBalancedParensAccess
    (parens : Succinct.BalancedParens) (overhead : Nat) where
  rankData : StoredWordRankData parens.bits overhead

namespace StoredRankBalancedParensAccess

def rankCosted
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (target : Bool) (pos : Nat) : Costed Nat :=
  access.rankData.rankCosted target pos

def excessCosted
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (pos : Nat) : Costed Nat :=
  Costed.bind (access.rankCosted true pos) fun opens =>
    Costed.map (fun closes => opens - closes)
      (access.rankCosted false pos)

theorem rankCosted_cost_le_three
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).cost <= 3 := by
  exact access.rankData.rankCosted_cost_le_three target pos

theorem rankCosted_exact
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (target : Bool) {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted target pos).erase =
      Succinct.rankPrefix target parens.bits pos := by
  exact access.rankData.rankCosted_exact target hpos

theorem close_rank_le_open_rank
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted false pos).erase <=
      (access.rankCosted true pos).erase := by
  calc
    (access.rankCosted false pos).erase =
        Succinct.rankPrefix false parens.bits pos := by
      exact access.rankCosted_exact false hpos
    _ <= Succinct.rankPrefix true parens.bits pos := by
      exact Succinct.BalancedParens.close_rank_le_open_rank parens hpos
    _ = (access.rankCosted true pos).erase := by
      exact (access.rankCosted_exact true hpos).symm

theorem final_rank_eq
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead) :
    (access.rankCosted true parens.bits.length).erase =
      (access.rankCosted false parens.bits.length).erase := by
  have hpos : parens.bits.length <= parens.bits.length := Nat.le_refl _
  calc
    (access.rankCosted true parens.bits.length).erase =
        Succinct.rankPrefix true parens.bits parens.bits.length := by
      exact access.rankCosted_exact true hpos
    _ = Succinct.rankPrefix false parens.bits parens.bits.length := by
      exact Succinct.BalancedParens.final_rank_eq parens
    _ = (access.rankCosted false parens.bits.length).erase := by
      exact (access.rankCosted_exact false hpos).symm

theorem excessCosted_cost_le_six
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    (pos : Nat) :
    (access.excessCosted pos).cost <= 6 := by
  have hopen := access.rankCosted_cost_le_three true pos
  have hclose := access.rankCosted_cost_le_three false pos
  have hsum :
      (access.rankCosted true pos).cost +
          (access.rankCosted false pos).cost <= 3 + 3 :=
    Nat.add_le_add hopen hclose
  simpa [excessCosted, Costed.map] using hsum

theorem excessCosted_exact
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.excessCosted pos).erase =
      Succinct.rankPrefix true parens.bits pos -
        Succinct.rankPrefix false parens.bits pos := by
  unfold excessCosted
  rw [Costed.erase_bind, Costed.erase_map]
  rw [access.rankCosted_exact true hpos,
    access.rankCosted_exact false hpos]

theorem profile
    {parens : Succinct.BalancedParens} {overhead : Nat}
    (access : StoredRankBalancedParensAccess parens overhead) :
    access.rankData.encodeAux.length = overhead /\
      (forall target pos,
        (access.rankCosted target pos).cost <= 3 /\
          (pos <= parens.bits.length ->
            (access.rankCosted target pos).erase =
              Succinct.rankPrefix target parens.bits pos)) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          (access.rankCosted false pos).erase <=
            (access.rankCosted true pos).erase) /\
      ((access.rankCosted true parens.bits.length).erase =
        (access.rankCosted false parens.bits.length).erase) /\
      (forall pos,
        (access.excessCosted pos).cost <= 6 /\
          (pos <= parens.bits.length ->
            (access.excessCosted pos).erase =
              Succinct.rankPrefix true parens.bits pos -
                Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact access.rankData.aux_length_eq
  · constructor
    · intro target pos
      exact ⟨access.rankCosted_cost_le_three target pos,
        fun hpos => access.rankCosted_exact target hpos⟩
    · constructor
      · intro pos hpos
        exact access.close_rank_le_open_rank hpos
      · constructor
        · exact access.final_rank_eq
        · intro pos
          exact ⟨access.excessCosted_cost_le_six pos,
            fun hpos => access.excessCosted_exact hpos⟩

end StoredRankBalancedParensAccess

/-- Family of faithful stored-read BP rank/excess access structures. -/
structure StoredRankBalancedParensAccessFamily
    (overhead : Nat -> Nat) where
  access :
    forall parens : Succinct.BalancedParens,
      StoredRankBalancedParensAccess parens (overhead parens.bits.length)
  overhead_littleO : LittleOLinear overhead

namespace StoredRankBalancedParensAccessFamily

theorem constant_rank_excess_profile
    {overhead : Nat -> Nat}
    (family : StoredRankBalancedParensAccessFamily overhead) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        ((family.access parens).rankData.encodeAux.length =
          overhead parens.bits.length) /\
          (forall target pos,
            ((family.access parens).rankCosted target pos).cost <= 3 /\
              (pos <= parens.bits.length ->
                ((family.access parens).rankCosted target pos).erase =
                  Succinct.rankPrefix target parens.bits pos)) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              ((family.access parens).rankCosted false pos).erase <=
                ((family.access parens).rankCosted true pos).erase) /\
          (((family.access parens).rankCosted true parens.bits.length).erase =
            ((family.access parens).rankCosted false parens.bits.length).erase) /\
          (forall pos,
            ((family.access parens).excessCosted pos).cost <= 6 /\
              (pos <= parens.bits.length ->
                ((family.access parens).excessCosted pos).erase =
                  Succinct.rankPrefix true parens.bits pos -
                    Succinct.rankPrefix false parens.bits pos)) := by
  constructor
  · exact family.overhead_littleO
  · intro parens
    exact (family.access parens).profile

end StoredRankBalancedParensAccessFamily

/--
Balanced-parentheses access layer backed by a certified rank/select directory.

This is the next component slot toward a BP-native succinct RMQ/LCA structure:
the parenthesis balance facts are transported through costed rank queries, and
the excess operation charges exactly two rank queries.
-/
structure BalancedParensAccess
    (parens : Succinct.BalancedParens) (overhead queryCost : Nat) where
  rankSelect : RankSelectDirectory parens.bits overhead queryCost

namespace BalancedParensAccess

def rankCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  access.rankSelect.rankQueryCosted target pos

def selectCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  access.rankSelect.selectQueryCosted target occurrence

def excessCosted
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (pos : Nat) : Costed Nat :=
  Costed.bind (access.rankCosted true pos) fun opens =>
    Costed.map (fun closes => opens - closes)
      (access.rankCosted false pos)

def ofPayloadBackedStoredWordRankSelectData
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData parens.bits
        rankOverhead selectOverhead) :
    BalancedParensAccess parens (rankOverhead + selectOverhead) 3 where
  rankSelect := backed.toRankSelectDirectory

/--
Payload-live stored-word rank/select data instantiate balanced-parentheses
rank/select access without routing through decoded auxiliary tables.
-/
def ofPayloadLiveStoredWordRankSelectData
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData parens.bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData parens.bits selectOverhead) :
    BalancedParensAccess parens (rankOverhead + selectOverhead) 3 where
  rankSelect :=
    RankSelectDirectory.ofPayloadLiveRankSelectData rankData selectData

theorem auxPayload_length
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost) :
    access.rankSelect.auxPayload.length = overhead := by
  exact access.rankSelect.auxPayload_length

theorem rankCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).cost <= queryCost := by
  exact access.rankSelect.rankQueryCosted_cost_le target pos

theorem selectCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (access.selectCosted target occurrence).cost <= queryCost := by
  exact access.rankSelect.selectQueryCosted_cost_le target occurrence

@[simp] theorem rankCosted_erase
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (pos : Nat) :
    (access.rankCosted target pos).erase =
      Succinct.rankPrefix target parens.bits pos := by
  exact access.rankSelect.rankQueryCosted_erase target pos

@[simp] theorem selectCosted_erase
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (target : Bool) (occurrence : Nat) :
    (access.selectCosted target occurrence).erase =
      Succinct.select target parens.bits occurrence := by
  exact access.rankSelect.selectQueryCosted_erase target occurrence

theorem close_rank_le_open_rank
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    {pos : Nat} (hpos : pos <= parens.bits.length) :
    (access.rankCosted false pos).erase <=
      (access.rankCosted true pos).erase := by
  calc
    (access.rankCosted false pos).erase =
        Succinct.rankPrefix false parens.bits pos := by
      exact access.rankCosted_erase false pos
    _ <= Succinct.rankPrefix true parens.bits pos := by
      exact Succinct.BalancedParens.close_rank_le_open_rank parens hpos
    _ = (access.rankCosted true pos).erase := by
      exact (access.rankCosted_erase true pos).symm

theorem final_rank_eq
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost) :
    (access.rankCosted true parens.bits.length).erase =
      (access.rankCosted false parens.bits.length).erase := by
  calc
    (access.rankCosted true parens.bits.length).erase =
        Succinct.rankPrefix true parens.bits parens.bits.length := by
      exact access.rankCosted_erase true parens.bits.length
    _ = Succinct.rankPrefix false parens.bits parens.bits.length := by
      exact Succinct.BalancedParens.final_rank_eq parens
    _ = (access.rankCosted false parens.bits.length).erase := by
      exact (access.rankCosted_erase false parens.bits.length).symm

theorem excessCosted_erase
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (pos : Nat) :
    (access.excessCosted pos).erase =
      Succinct.rankPrefix true parens.bits pos -
        Succinct.rankPrefix false parens.bits pos := by
  unfold excessCosted
  rw [Costed.erase_bind, Costed.erase_map]
  rw [access.rankCosted_erase true pos, access.rankCosted_erase false pos]

theorem excessCosted_cost_le
    {parens : Succinct.BalancedParens} {overhead queryCost : Nat}
    (access : BalancedParensAccess parens overhead queryCost)
    (pos : Nat) :
    (access.excessCosted pos).cost <= 2 * queryCost := by
  have hopen := access.rankCosted_cost_le true pos
  have hclose := access.rankCosted_cost_le false pos
  have hsum :
      (access.rankCosted true pos).cost +
          (access.rankCosted false pos).cost <=
        queryCost + queryCost :=
    Nat.add_le_add hopen hclose
  simpa [excessCosted, Costed.map, Nat.two_mul] using hsum

theorem ofPayloadBackedStoredWordRankSelectData_profile
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData parens.bits
        rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead /\
      ((ofPayloadBackedStoredWordRankSelectData backed).rankSelect.auxPayload =
        backed.payload) /\
      (forall target pos,
        ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
            target pos).cost <= 3 /\
          ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
            target pos).erase =
            Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        ((ofPayloadBackedStoredWordRankSelectData backed).selectCosted
            target occurrence).cost <= 3 /\
          ((ofPayloadBackedStoredWordRankSelectData backed).selectCosted
            target occurrence).erase =
            Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
              false pos).erase <=
            ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
              true pos).erase) /\
      (((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
          true parens.bits.length).erase =
        ((ofPayloadBackedStoredWordRankSelectData backed).rankCosted
          false parens.bits.length).erase) /\
      (forall pos,
        ((ofPayloadBackedStoredWordRankSelectData backed).excessCosted pos).cost <=
            6 /\
          ((ofPayloadBackedStoredWordRankSelectData backed).excessCosted
            pos).erase =
            Succinct.rankPrefix true parens.bits pos -
              Succinct.rankPrefix false parens.bits pos) := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.directory_auxPayload_eq_payload
    · constructor
      · intro target pos
        let access := ofPayloadBackedStoredWordRankSelectData backed
        exact ⟨access.rankCosted_cost_le target pos,
          access.rankCosted_erase target pos⟩
      · constructor
        · intro target occurrence
          let access := ofPayloadBackedStoredWordRankSelectData backed
          exact ⟨access.selectCosted_cost_le target occurrence,
            access.selectCosted_erase target occurrence⟩
        · constructor
          · intro pos hpos
            let access := ofPayloadBackedStoredWordRankSelectData backed
            exact access.close_rank_le_open_rank hpos
          · constructor
            · exact
                (ofPayloadBackedStoredWordRankSelectData backed).final_rank_eq
            · intro pos
              let access := ofPayloadBackedStoredWordRankSelectData backed
              exact ⟨by
                simpa using access.excessCosted_cost_le pos,
                access.excessCosted_erase pos⟩

theorem ofPayloadLiveStoredWordRankSelectData_profile
    {parens : Succinct.BalancedParens}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData parens.bits rankOverhead)
    (selectData : PayloadLiveStoredWordSelectData parens.bits selectOverhead) :
    ((ofPayloadLiveStoredWordRankSelectData
        rankData selectData).rankSelect.auxPayload.length =
        rankOverhead + selectOverhead) /\
      ((ofPayloadLiveStoredWordRankSelectData
          rankData selectData).rankSelect.auxPayload =
        rankData.auxPayload ++ selectData.auxPayload) /\
      (forall target pos,
        ((ofPayloadLiveStoredWordRankSelectData rankData selectData).rankCosted
            target pos).cost <= 3 /\
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted target pos).erase =
            Succinct.rankPrefix target parens.bits pos) /\
      (forall target occurrence,
        ((ofPayloadLiveStoredWordRankSelectData
            rankData selectData).selectCosted target occurrence).cost <= 3 /\
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).selectCosted target occurrence).erase =
            Succinct.select target parens.bits occurrence) /\
      (forall {pos : Nat},
        pos <= parens.bits.length ->
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted false pos).erase <=
            ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted true pos).erase) /\
      (((ofPayloadLiveStoredWordRankSelectData rankData selectData).rankCosted
          true parens.bits.length).erase =
        ((ofPayloadLiveStoredWordRankSelectData rankData selectData).rankCosted
          false parens.bits.length).erase) /\
      (forall pos,
        ((ofPayloadLiveStoredWordRankSelectData
            rankData selectData).excessCosted pos).cost <= 6 /\
          ((ofPayloadLiveStoredWordRankSelectData
              rankData selectData).excessCosted pos).erase =
            Succinct.rankPrefix true parens.bits pos -
              Succinct.rankPrefix false parens.bits pos) := by
  constructor
  · exact
      (ofPayloadLiveStoredWordRankSelectData
        rankData selectData).auxPayload_length
  · constructor
    · simp [ofPayloadLiveStoredWordRankSelectData,
        RankSelectDirectory.ofPayloadLiveRankSelectData,
        RankSelectDirectory.auxPayload]
    · constructor
      · intro target pos
        let access :=
          ofPayloadLiveStoredWordRankSelectData rankData selectData
        exact ⟨access.rankCosted_cost_le target pos,
          access.rankCosted_erase target pos⟩
      · constructor
        · intro target occurrence
          let access :=
            ofPayloadLiveStoredWordRankSelectData rankData selectData
          exact ⟨access.selectCosted_cost_le target occurrence,
            access.selectCosted_erase target occurrence⟩
        · constructor
          · intro pos hpos
            let access :=
              ofPayloadLiveStoredWordRankSelectData rankData selectData
            exact access.close_rank_le_open_rank hpos
          · constructor
            · exact
                (ofPayloadLiveStoredWordRankSelectData
                  rankData selectData).final_rank_eq
            · intro pos
              let access :=
                ofPayloadLiveStoredWordRankSelectData rankData selectData
              exact ⟨by
                simpa using access.excessCosted_cost_le pos,
                access.excessCosted_erase pos⟩

def ofShapePayloadBackedStoredWordRankSelectData
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData shape.bpCode
        rankOverhead selectOverhead) :
    BalancedParensAccess (bpParensOfShape shape)
      (rankOverhead + selectOverhead) 3 :=
  ofPayloadBackedStoredWordRankSelectData backed

/-- Payload-live BP rank/select access specialized to Cartesian BP codes. -/
def ofShapePayloadLiveStoredWordRankSelectData
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (selectData :
      PayloadLiveStoredWordSelectData shape.bpCode selectOverhead) :
    BalancedParensAccess (bpParensOfShape shape)
      (rankOverhead + selectOverhead) 3 :=
  ofPayloadLiveStoredWordRankSelectData rankData selectData

theorem ofShapePayloadBackedStoredWordRankSelectData_close_profile
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (backed :
      PayloadBackedStoredWordRankSelectData shape.bpCode
        rankOverhead selectOverhead) :
    backed.payload.length = rankOverhead + selectOverhead /\
      ((ofShapePayloadBackedStoredWordRankSelectData backed).rankSelect.auxPayload =
        backed.payload) /\
      (forall idx,
        ((ofShapePayloadBackedStoredWordRankSelectData backed).selectCosted
            false idx).cost <= 3 /\
          ((ofShapePayloadBackedStoredWordRankSelectData backed).selectCosted
              false idx).erase =
            bpCloseOfInorder? shape idx) /\
      (forall pos,
        ((ofShapePayloadBackedStoredWordRankSelectData backed).rankCosted
            false pos).cost <= 3 /\
          ((ofShapePayloadBackedStoredWordRankSelectData backed).rankCosted
              false pos).erase =
            Succinct.rankPrefix false shape.bpCode pos) := by
  constructor
  · exact backed.payload_length_eq
  · constructor
    · exact backed.directory_auxPayload_eq_payload
    · constructor
      · intro idx
        let access := ofShapePayloadBackedStoredWordRankSelectData backed
        constructor
        · exact access.selectCosted_cost_le false idx
        · calc
            (access.selectCosted false idx).erase =
              Succinct.select false shape.bpCode idx := by
                exact access.selectCosted_erase false idx
            _ = bpCloseOfInorder? shape idx := by
                exact select_false_bpCode_eq_bpCloseOfInorder? shape idx
      · intro pos
        let access := ofShapePayloadBackedStoredWordRankSelectData backed
        exact ⟨access.rankCosted_cost_le false pos,
          access.rankCosted_erase false pos⟩

theorem ofShapePayloadLiveStoredWordRankSelectData_close_profile
    {shape : Cartesian.CartesianShape}
    {rankOverhead selectOverhead : Nat}
    (rankData : PayloadLiveStoredWordRankData shape.bpCode rankOverhead)
    (selectData :
      PayloadLiveStoredWordSelectData shape.bpCode selectOverhead) :
    ((ofShapePayloadLiveStoredWordRankSelectData
        rankData selectData).rankSelect.auxPayload.length =
        rankOverhead + selectOverhead) /\
      ((ofShapePayloadLiveStoredWordRankSelectData
          rankData selectData).rankSelect.auxPayload =
        rankData.auxPayload ++ selectData.auxPayload) /\
      (forall idx,
        ((ofShapePayloadLiveStoredWordRankSelectData
            rankData selectData).selectCosted false idx).cost <= 3 /\
          ((ofShapePayloadLiveStoredWordRankSelectData
              rankData selectData).selectCosted false idx).erase =
            bpCloseOfInorder? shape idx) /\
      (forall pos,
        ((ofShapePayloadLiveStoredWordRankSelectData
            rankData selectData).rankCosted false pos).cost <= 3 /\
          ((ofShapePayloadLiveStoredWordRankSelectData
              rankData selectData).rankCosted false pos).erase =
            Succinct.rankPrefix false shape.bpCode pos) := by
  constructor
  · exact
      (ofShapePayloadLiveStoredWordRankSelectData
        rankData selectData).auxPayload_length
  · constructor
    · simp [ofShapePayloadLiveStoredWordRankSelectData,
        ofPayloadLiveStoredWordRankSelectData,
        RankSelectDirectory.ofPayloadLiveRankSelectData,
        RankSelectDirectory.auxPayload]
    · constructor
      · intro idx
        let access :=
          ofShapePayloadLiveStoredWordRankSelectData rankData selectData
        constructor
        · exact access.selectCosted_cost_le false idx
        · calc
            (access.selectCosted false idx).erase =
              Succinct.select false shape.bpCode idx := by
                exact access.selectCosted_erase false idx
            _ = bpCloseOfInorder? shape idx := by
                exact select_false_bpCode_eq_bpCloseOfInorder? shape idx
      · intro pos
        let access :=
          ofShapePayloadLiveStoredWordRankSelectData rankData selectData
        exact ⟨access.rankCosted_cost_le false pos,
          access.rankCosted_erase false pos⟩

end BalancedParensAccess

/--
Family-level balanced-parentheses access component.

This is the BP analogue of `RankSelectFamily`: every certified balanced
parentheses string gets rank/select access, transported balance facts, and
two-rank excess queries under one uniform cost bound and one `o(n)` auxiliary
overhead function.
-/
structure BalancedParensAccessFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  access :
    forall parens : Succinct.BalancedParens,
      BalancedParensAccess parens (overhead parens.bits.length) queryCost
  overhead_littleO : LittleOLinear overhead

namespace BalancedParensAccessFamily

theorem constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : BalancedParensAccessFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall parens : Succinct.BalancedParens,
        ((family.access parens).rankSelect.auxPayload.length =
          overhead parens.bits.length) /\
          (forall target pos,
            ((family.access parens).rankCosted target pos).cost <=
                queryCost /\
              ((family.access parens).rankCosted target pos).erase =
                Succinct.rankPrefix target parens.bits pos) /\
          (forall target occurrence,
            ((family.access parens).selectCosted target occurrence).cost <=
                queryCost /\
              ((family.access parens).selectCosted target occurrence).erase =
                Succinct.select target parens.bits occurrence) /\
          (forall {pos : Nat},
            pos <= parens.bits.length ->
              ((family.access parens).rankCosted false pos).erase <=
                ((family.access parens).rankCosted true pos).erase) /\
          (((family.access parens).rankCosted true parens.bits.length).erase =
            ((family.access parens).rankCosted false parens.bits.length).erase) /\
          (forall pos,
            ((family.access parens).excessCosted pos).cost <=
                2 * queryCost /\
              ((family.access parens).excessCosted pos).erase =
                Succinct.rankPrefix true parens.bits pos -
                  Succinct.rankPrefix false parens.bits pos) := by
  constructor
  · exact family.overhead_littleO
  · intro parens
    constructor
    · exact (family.access parens).auxPayload_length
    · constructor
      · intro target pos
        exact ⟨(family.access parens).rankCosted_cost_le target pos,
          (family.access parens).rankCosted_erase target pos⟩
      · constructor
        · intro target occurrence
          exact ⟨(family.access parens).selectCosted_cost_le target occurrence,
            (family.access parens).selectCosted_erase target occurrence⟩
        · constructor
          · intro pos hpos
            exact (family.access parens).close_rank_le_open_rank hpos
          · constructor
            · exact (family.access parens).final_rank_eq
            · intro pos
              exact ⟨(family.access parens).excessCosted_cost_le pos,
                (family.access parens).excessCosted_erase pos⟩

end BalancedParensAccessFamily

/--
Payload-live stored-word rank/select components instantiate the generic
balanced-parentheses access-family interface.
-/
def PayloadLiveStoredWordRankSelectFamily.toBalancedParensAccessFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    BalancedParensAccessFamily family.overhead 3 where
  access parens :=
    BalancedParensAccess.ofPayloadLiveStoredWordRankSelectData
      (family.rankComponent parens.bits) (family.selectComponent parens.bits)
  overhead_littleO := family.overhead_littleO

theorem PayloadLiveStoredWordRankSelectFamily.bp_constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadLiveStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall parens : Succinct.BalancedParens,
        (((family.toBalancedParensAccessFamily).access parens).rankSelect.auxPayload.length =
          family.overhead parens.bits.length) /\
          (forall target pos,
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).erase =
                Succinct.rankPrefix target parens.bits pos) /\
          (forall target occurrence,
            (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).erase =
                Succinct.select target parens.bits occurrence) /\
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
                pos).cost <= 6 /\
              (((family.toBalancedParensAccessFamily).access parens).excessCosted
                pos).erase =
                Succinct.rankPrefix true parens.bits pos -
                  Succinct.rankPrefix false parens.bits pos) := by
  have hprofile :=
    (family.toBalancedParensAccessFamily).constant_query_profile
  constructor
  · exact hprofile.1
  · intro parens
    rcases hprofile.2 parens with
      ⟨haux, hrank, hselect, hprefix, hfinal, hexcess⟩
    constructor
    · exact haux
    · constructor
      · exact hrank
      · constructor
        · exact hselect
        · constructor
          · exact hprefix
          · constructor
            · exact hfinal
            · intro pos
              exact hexcess pos

/--
Payload-backed stored-word rank/select components instantiate the generic
balanced-parentheses access-family interface.
-/
def PayloadBackedStoredWordRankSelectFamily.toBalancedParensAccessFamily
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    BalancedParensAccessFamily family.overhead 3 where
  access parens :=
    BalancedParensAccess.ofPayloadBackedStoredWordRankSelectData
      (family.component parens.bits)
  overhead_littleO := family.overhead_littleO

theorem PayloadBackedStoredWordRankSelectFamily.bp_constant_query_profile
    {rankOverhead selectOverhead : Nat -> Nat}
    (family :
      PayloadBackedStoredWordRankSelectFamily rankOverhead selectOverhead) :
    LittleOLinear family.overhead /\
      forall parens : Succinct.BalancedParens,
        (((family.toBalancedParensAccessFamily).access parens).rankSelect.auxPayload.length =
          family.overhead parens.bits.length) /\
          (forall target pos,
            (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).rankCosted
                target pos).erase =
                Succinct.rankPrefix target parens.bits pos) /\
          (forall target occurrence,
            (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).cost <= 3 /\
              (((family.toBalancedParensAccessFamily).access parens).selectCosted
                target occurrence).erase =
                Succinct.select target parens.bits occurrence) /\
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
                pos).cost <= 6 /\
              (((family.toBalancedParensAccessFamily).access parens).excessCosted
                pos).erase =
                Succinct.rankPrefix true parens.bits pos -
                  Succinct.rankPrefix false parens.bits pos) := by
  have hprofile :=
    (family.toBalancedParensAccessFamily).constant_query_profile
  constructor
  · exact hprofile.1
  · intro parens
    rcases hprofile.2 parens with
      ⟨haux, hrank, hselect, hprefix, hfinal, hexcess⟩
    constructor
    · exact haux
    · constructor
      · exact hrank
      · constructor
        · exact hselect
        · constructor
          · exact hprefix
          · constructor
            · exact hfinal
            · intro pos
              have h := hexcess pos
              exact ⟨by simpa using h.1, h.2⟩

end SuccinctSpace

end RMQ
