import RMQ.Core.RankSelectSpec

/-!
# Compressed/FID rank-select specification surface

This module adds the fixed-weight bitvector counting layer and the public
compressed rank/select theorem shape.  It is deliberately a spec/profile layer:
the fixed-weight codec and packed-payload spine live here, while the full
compressed/FID construction remains below this interface.
-/

namespace RMQ

namespace RankSelectSpec

/--
Mathlib-free binomial-count recurrence.

`binomialCount n k` counts the number of length-`n` bitvectors with exactly
`k` true bits.  It intentionally avoids depending on `Nat.choose`, which is not
part of the repository's Lean/Std footprint.
-/
def binomialCount : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => binomialCount n 0
  | n + 1, k + 1 => binomialCount n (k + 1) + binomialCount n k

/-- Bitvectors of length `n` with exactly `k` true bits. -/
def fixedWeightBitstrings : Nat -> Nat -> List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 =>
      (fixedWeightBitstrings n 0).map fun bits => false :: bits
  | n + 1, k + 1 =>
      ((fixedWeightBitstrings n (k + 1)).map fun bits => false :: bits) ++
        ((fixedWeightBitstrings n k).map fun bits => true :: bits)

theorem fixedWeightBitstrings_length
    (n k : Nat) :
    (fixedWeightBitstrings n k).length = binomialCount n k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [fixedWeightBitstrings, binomialCount]
  | succ n ih =>
      cases k with
      | zero =>
          simp [fixedWeightBitstrings, binomialCount, ih]
      | succ k =>
          simp [fixedWeightBitstrings, binomialCount, ih, Nat.add_comm]

/-- Number of true bits in a bitvector. -/
def trueCount (bits : List Bool) : Nat :=
  Succinct.rankPrefix true bits bits.length

@[simp] theorem trueCount_nil : trueCount [] = 0 := by
  rfl

@[simp] theorem trueCount_cons_false (bits : List Bool) :
    trueCount (false :: bits) = trueCount bits := by
  simp [trueCount, Succinct.rankPrefix]

@[simp] theorem trueCount_cons_true (bits : List Bool) :
    trueCount (true :: bits) = trueCount bits + 1 := by
  simp [trueCount, Succinct.rankPrefix, Nat.add_comm]

theorem fixedWeightBitstrings_mem_length_trueCount
    {bits : List Bool} {n k : Nat}
    (hmem : List.Mem bits (fixedWeightBitstrings n k)) :
    bits.length = n /\ trueCount bits = k := by
  induction n generalizing bits k with
  | zero =>
      cases k with
      | zero =>
          cases hmem with
          | head =>
              simp
          | tail _ htail =>
              cases htail
      | succ k =>
          cases hmem
  | succ n ih =>
      cases k with
      | zero =>
          rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
          have htailFacts := ih htail
          simp [htailFacts.1, htailFacts.2]
      | succ k =>
          rcases List.mem_append.mp hmem with hmem | hmem
          · rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
            have htailFacts := ih htail
            simp [htailFacts.1, htailFacts.2]
          · rcases List.mem_map.mp hmem with ⟨tail, htail, rfl⟩
            have htailFacts := ih htail
            simp [htailFacts.1, htailFacts.2]

theorem fixedWeightBitstrings_mem_of_length_trueCount
    {bits : List Bool} {n k : Nat}
    (hlen : bits.length = n) (hcount : trueCount bits = k) :
    List.Mem bits (fixedWeightBitstrings n k) := by
  induction n generalizing bits k with
  | zero =>
      cases bits with
      | nil =>
          cases k with
          | zero =>
              exact List.Mem.head []
          | succ k =>
              simp at hcount
      | cons bit rest =>
          simp at hlen
  | succ n ih =>
      cases bits with
      | nil =>
          simp at hlen
      | cons bit rest =>
          have hrestLen : rest.length = n := by
            simp at hlen
            exact hlen
          cases bit
          case false =>
            cases k with
            | zero =>
                exact
                  List.mem_map.mpr
                    ⟨rest, ih hrestLen (by simpa using hcount), rfl⟩
            | succ k =>
                exact
                  List.mem_append.mpr
                    (Or.inl
                      (List.mem_map.mpr
                        ⟨rest, ih hrestLen (by simpa using hcount), rfl⟩))
          case true =>
            cases k with
            | zero =>
                simp at hcount
            | succ k =>
                have htailCount : trueCount rest = k := by
                  simpa using hcount
                exact
                  List.mem_append.mpr
                    (Or.inr
                      (List.mem_map.mpr
                        ⟨rest, ih hrestLen htailCount, rfl⟩))

theorem fixedWeightBitstrings_mem_iff
    {bits : List Bool} {n k : Nat} :
    List.Mem bits (fixedWeightBitstrings n k) <->
      bits.length = n /\ trueCount bits = k := by
  constructor
  · exact fixedWeightBitstrings_mem_length_trueCount
  · intro h
    exact fixedWeightBitstrings_mem_of_length_trueCount h.1 h.2

private theorem nodup_map_cons_bool
    (head : Bool) {xs : List (List Bool)}
    (hxs : xs.Nodup) :
    (xs.map (fun bits => head :: bits)).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      change ((head :: x) :: xs.map (fun bits => head :: bits)).Nodup
      rw [List.nodup_cons]
      constructor
      · intro hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨tail, htail, htailEq⟩
        exact hxs.1 (by
          cases htailEq
          exact htail)
      · exact ih hxs.2

/-- The fixed-weight bitvector universe has no duplicate entries. -/
theorem fixedWeightBitstrings_nodup
    (n k : Nat) :
    (fixedWeightBitstrings n k).Nodup := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [fixedWeightBitstrings]
  | succ n ih =>
      cases k with
      | zero =>
          exact nodup_map_cons_bool false (ih 0)
      | succ k =>
          rw [fixedWeightBitstrings]
          rw [List.nodup_append]
          constructor
          · exact nodup_map_cons_bool false (ih (k + 1))
          · constructor
            · exact nodup_map_cons_bool true (ih k)
            · intro a ha b hb hab
              rw [List.mem_map] at ha
              rw [List.mem_map] at hb
              rcases ha with ⟨tailA, htailA, haEq⟩
              rcases hb with ⟨tailB, htailB, hbEq⟩
              subst a
              subst b
              cases haEq

/--
First index of a value in a list, local to the compressed rank/select codec
spine. This keeps the codec proofs independent of heavier downstream modules.
-/
def listIndexOf? {alpha : Type u} [DecidableEq alpha]
    (target : alpha) : List alpha -> Option Nat
  | [] => none
  | x :: xs =>
      if x = target then
        some 0
      else
        match listIndexOf? target xs with
        | none => none
        | some idx => some (idx + 1)

theorem listIndexOf?_lt_length
    {alpha : Type u} [DecidableEq alpha] {target : alpha} :
    forall {xs : List alpha} {idx : Nat},
      listIndexOf? target xs = some idx -> idx < xs.length
  | [], _, h => by
      simp [listIndexOf?] at h
  | x :: xs, idx, h => by
      unfold listIndexOf? at h
      by_cases hx : x = target
      · simp [hx] at h
        cases h
        simp
      · simp [hx] at h
        cases htail : listIndexOf? target xs with
        | none =>
            simp [htail] at h
        | some tailIdx =>
            simp [htail] at h
            have htail_lt :
                tailIdx < xs.length :=
              listIndexOf?_lt_length (target := target) htail
            cases h
            simp
            omega

theorem listIndexOf?_get?
    {alpha : Type u} [DecidableEq alpha] {target : alpha} :
    forall {xs : List alpha} {idx : Nat},
      listIndexOf? target xs = some idx -> xs[idx]? = some target
  | [], _, h => by
      simp [listIndexOf?] at h
  | x :: xs, idx, h => by
      unfold listIndexOf? at h
      by_cases hx : x = target
      · simp [hx] at h
        cases h
        simp [hx]
      · simp [hx] at h
        cases htail : listIndexOf? target xs with
        | none =>
            simp [htail] at h
        | some tailIdx =>
            simp [htail] at h
            cases h
            have hget :
                xs[tailIdx]? = some target :=
              listIndexOf?_get? (target := target) htail
            simpa using hget

theorem listIndexOf?_mem
    {alpha : Type u} [DecidableEq alpha] {target : alpha}
    {xs : List alpha} {idx : Nat}
    (h : listIndexOf? target xs = some idx) :
    target ∈ xs := by
  exact List.mem_of_getElem? (listIndexOf?_get? h)

theorem listIndexOf?_exists_of_mem
    {alpha : Type u} [DecidableEq alpha] {target : alpha} :
    forall {xs : List alpha},
      target ∈ xs -> exists idx, listIndexOf? target xs = some idx
  | [], hmem => by
      simp at hmem
  | x :: xs, hmem => by
      unfold listIndexOf?
      by_cases hx : x = target
      · exact ⟨0, by simp [hx]⟩
      · have htarget_x : target ≠ x := by
          intro htarget_x
          exact hx htarget_x.symm
        simp [hx, htarget_x] at hmem ⊢
        rcases listIndexOf?_exists_of_mem (target := target) hmem with
          ⟨idx, hidx⟩
        exact ⟨idx + 1, by simp [hidx]⟩

theorem listIndexOf?_eq_of_get?_nodup
    {alpha : Type u} [DecidableEq alpha] {target : alpha}
    {xs : List alpha} {idx : Nat}
    (hnodup : xs.Nodup)
    (hget : xs[idx]? = some target) :
    listIndexOf? target xs = some idx := by
  induction xs generalizing idx with
  | nil =>
      simp at hget
  | cons x xs ih =>
      unfold listIndexOf?
      by_cases hx : x = target
      · simp [hx]
        rw [List.nodup_cons] at hnodup
        cases idx with
        | zero =>
            rfl
        | succ idx =>
            simp [hx] at hget
            have hmemTarget : target ∈ xs :=
              List.mem_of_getElem? hget
            have hmemX : x ∈ xs := by
              simpa [hx] using hmemTarget
            exact False.elim (hnodup.1 hmemX)
      · simp [hx]
        cases idx with
        | zero =>
            simp [hx] at hget
        | succ idx =>
            rw [List.nodup_cons] at hnodup
            have htail :
                listIndexOf? target xs = some idx :=
              ih hnodup.2 (by simpa using hget)
            simp [htail]

/--
Canonical fixed-weight encoder: the first index of `bits` in the finite
fixed-weight universe for its own length and true-count.
-/
def fixedWeightEncode? (bits : List Bool) : Option Nat :=
  listIndexOf? bits (fixedWeightBitstrings bits.length (trueCount bits))

/-- Canonical fixed-weight decoder by indexing the counted universe. -/
def fixedWeightDecode? (n k code : Nat) : Option (List Bool) :=
  (fixedWeightBitstrings n k)[code]?

theorem fixedWeightEncode?_exists (bits : List Bool) :
    exists code, fixedWeightEncode? bits = some code := by
  unfold fixedWeightEncode?
  exact
    listIndexOf?_exists_of_mem
      (target := bits)
      (fixedWeightBitstrings_mem_of_length_trueCount rfl rfl)

theorem fixedWeightEncode?_lt_binomialCount
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :
    code < binomialCount bits.length (trueCount bits) := by
  have hlt :
      code <
        (fixedWeightBitstrings bits.length (trueCount bits)).length := by
    exact listIndexOf?_lt_length henc
  simpa [fixedWeightBitstrings_length] using hlt

/-- Total canonical code for a bitvector in its own fixed-weight universe. -/
def fixedWeightCode (bits : List Bool) : Nat :=
  (fixedWeightEncode? bits).getD 0

theorem fixedWeightEncode?_eq_some_fixedWeightCode
    (bits : List Bool) :
    fixedWeightEncode? bits = some (fixedWeightCode bits) := by
  rcases fixedWeightEncode?_exists bits with ⟨code, hcode⟩
  simp [fixedWeightCode, hcode]

theorem fixedWeightCode_lt_binomialCount
    (bits : List Bool) :
    fixedWeightCode bits <
      binomialCount bits.length (trueCount bits) := by
  exact fixedWeightEncode?_lt_binomialCount
    (fixedWeightEncode?_eq_some_fixedWeightCode bits)

theorem fixedWeightDecode?_fixedWeightEncode?
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :
    fixedWeightDecode? bits.length (trueCount bits) code = some bits := by
  exact listIndexOf?_get? henc

theorem fixedWeightDecode?_mem_length_trueCount
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :
    bits.length = n /\ trueCount bits = k := by
  unfold fixedWeightDecode? at hdec
  have hmem : List.Mem bits (fixedWeightBitstrings n k) :=
    List.mem_of_getElem? hdec
  exact fixedWeightBitstrings_mem_length_trueCount hmem

theorem fixedWeightEncode?_fixedWeightDecode?
    {n k code : Nat} {bits : List Bool}
    (hdec : fixedWeightDecode? n k code = some bits) :
    fixedWeightEncode? bits = some code := by
  unfold fixedWeightDecode? at hdec
  have hfacts := fixedWeightBitstrings_mem_length_trueCount
    (List.mem_of_getElem? hdec)
  unfold fixedWeightEncode?
  rw [hfacts.1, hfacts.2]
  exact listIndexOf?_eq_of_get?_nodup
    (fixedWeightBitstrings_nodup n k) hdec

theorem fixedWeightDecode?_eq_some_iff
    {n k code : Nat} {bits : List Bool} :
    fixedWeightDecode? n k code = some bits <->
      bits.length = n /\ trueCount bits = k /\
        fixedWeightEncode? bits = some code := by
  constructor
  · intro hdec
    have hfacts := fixedWeightDecode?_mem_length_trueCount hdec
    exact ⟨hfacts.1, hfacts.2,
      fixedWeightEncode?_fixedWeightDecode? hdec⟩
  · intro h
    have hdec :=
      fixedWeightDecode?_fixedWeightEncode? h.2.2
    simpa [h.1, h.2.1] using hdec

theorem fixedWeightCodec_roundTrip
    (bits : List Bool) :
    exists code,
      fixedWeightEncode? bits = some code /\
        fixedWeightDecode? bits.length (trueCount bits) code = some bits /\
        code < binomialCount bits.length (trueCount bits) := by
  rcases fixedWeightEncode?_exists bits with ⟨code, henc⟩
  exact
    ⟨code, henc, fixedWeightDecode?_fixedWeightEncode? henc,
      fixedWeightEncode?_lt_binomialCount henc⟩

/--
The information-theoretic fixed-weight payload budget used by the compressed
rank/select profile.  The `+ 1` is the usual whole-number ceiling slack for a
binary code over `binomialCount n m` states.
-/
def fixedWeightPayloadBudget (bits : List Bool) : Nat :=
  Nat.log2 (binomialCount bits.length (trueCount bits)) + 1

theorem fixedWeightEncode?_lt_payloadBudgetPow
    {bits : List Bool} {code : Nat}
    (henc : fixedWeightEncode? bits = some code) :
    code < 2 ^ fixedWeightPayloadBudget bits := by
  have hcode :
      code < binomialCount bits.length (trueCount bits) :=
    fixedWeightEncode?_lt_binomialCount henc
  have hcount :
      binomialCount bits.length (trueCount bits) <
        2 ^ (Nat.log2 (binomialCount bits.length (trueCount bits)) + 1) :=
    Nat.lt_log2_self
  exact Nat.lt_trans hcode (by simpa [fixedWeightPayloadBudget] using hcount)

theorem fixedWeightCode_lt_payloadBudgetPow
    (bits : List Bool) :
    fixedWeightCode bits < 2 ^ fixedWeightPayloadBudget bits := by
  exact fixedWeightEncode?_lt_payloadBudgetPow
    (fixedWeightEncode?_eq_some_fixedWeightCode bits)

/--
Packed fixed-weight payload for one bitvector.

This is the concrete bit-level realization of the canonical fixed-weight code:
store `fixedWeightCode bits` in exactly `fixedWeightPayloadBudget bits`
little-endian bits.
-/
def fixedWeightPackedPayload (bits : List Bool) : List Bool :=
  SuccinctSpace.natToBitsLE
    (fixedWeightPayloadBudget bits) (fixedWeightCode bits)

@[simp] theorem fixedWeightPackedPayload_length
    (bits : List Bool) :
    (fixedWeightPackedPayload bits).length =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedPayload, SuccinctSpace.natToBitsLE_length]

theorem fixedWeightPackedPayload_bitsToNatLE
    (bits : List Bool) :
    SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits) =
      fixedWeightCode bits := by
  simpa [fixedWeightPackedPayload] using
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt
      (fixedWeightCode_lt_payloadBudgetPow bits)

theorem fixedWeightDecode?_packedPayload
    (bits : List Bool) :
    fixedWeightDecode? bits.length (trueCount bits)
        (SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits)) =
      some bits := by
  rw [fixedWeightPackedPayload_bitsToNatLE]
  exact
    fixedWeightDecode?_fixedWeightEncode?
      (fixedWeightEncode?_eq_some_fixedWeightCode bits)

theorem fixedWeightPackedPayload_profile
    (bits : List Bool) :
    (fixedWeightPackedPayload bits).length =
        fixedWeightPayloadBudget bits /\
      SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits) =
        fixedWeightCode bits /\
      fixedWeightDecode? bits.length (trueCount bits)
          (SuccinctSpace.bitsToNatLE (fixedWeightPackedPayload bits)) =
        some bits := by
  exact
    ⟨fixedWeightPackedPayload_length bits,
      fixedWeightPackedPayload_bitsToNatLE bits,
      fixedWeightDecode?_packedPayload bits⟩

/--
Charged read of the fixed-weight packed payload.

The cost is the packed payload length, so this is an honest readback scaffold,
not the final constant-time FID query layer.
-/
def fixedWeightPackedReadbackPayloadCosted
    (bits : List Bool) : Costed (List Bool) :=
  Costed.tickValue (fixedWeightPayloadBudget bits)
    (fixedWeightPackedPayload bits)

@[simp] theorem fixedWeightPackedReadbackPayloadCosted_cost
    (bits : List Bool) :
    (fixedWeightPackedReadbackPayloadCosted bits).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackPayloadCosted]

@[simp] theorem fixedWeightPackedReadbackPayloadCosted_erase
    (bits : List Bool) :
    (fixedWeightPackedReadbackPayloadCosted bits).erase =
      fixedWeightPackedPayload bits := by
  simp [fixedWeightPackedReadbackPayloadCosted]

/-- Charged readback decode through `bitsToNatLE` and `fixedWeightDecode?`. -/
def fixedWeightPackedReadbackDecodeCosted
    (bits : List Bool) : Costed (Option (List Bool)) :=
  Costed.bind (fixedWeightPackedReadbackPayloadCosted bits) fun payload =>
    Costed.pure
      (fixedWeightDecode? bits.length (trueCount bits)
        (SuccinctSpace.bitsToNatLE payload))

@[simp] theorem fixedWeightPackedReadbackDecodeCosted_cost
    (bits : List Bool) :
    (fixedWeightPackedReadbackDecodeCosted bits).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackDecodeCosted]

@[simp] theorem fixedWeightPackedReadbackDecodeCosted_erase
    (bits : List Bool) :
    (fixedWeightPackedReadbackDecodeCosted bits).erase = some bits := by
  simp [fixedWeightPackedReadbackDecodeCosted,
    fixedWeightDecode?_packedPayload]

/-- Access through the charged fixed-weight packed readback decoder. -/
def fixedWeightPackedReadbackAccessCosted
    (bits : List Bool) (i : Nat) : Costed (Option Bool) :=
  Costed.bind (fixedWeightPackedReadbackDecodeCosted bits) fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => bits[i]?
      | none => none)

@[simp] theorem fixedWeightPackedReadbackAccessCosted_cost
    (bits : List Bool) (i : Nat) :
    (fixedWeightPackedReadbackAccessCosted bits i).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackAccessCosted]

@[simp] theorem fixedWeightPackedReadbackAccessCosted_erase
    (bits : List Bool) (i : Nat) :
    (fixedWeightPackedReadbackAccessCosted bits i).erase = bits[i]? := by
  simp [fixedWeightPackedReadbackAccessCosted]

/-- Rank through the charged fixed-weight packed readback decoder. -/
def fixedWeightPackedReadbackRankCosted
    (bits : List Bool) (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind (fixedWeightPackedReadbackDecodeCosted bits) fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.rankPrefix target bits pos
      | none => 0)

@[simp] theorem fixedWeightPackedReadbackRankCosted_cost
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (fixedWeightPackedReadbackRankCosted bits target pos).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackRankCosted]

@[simp] theorem fixedWeightPackedReadbackRankCosted_erase
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (fixedWeightPackedReadbackRankCosted bits target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [fixedWeightPackedReadbackRankCosted]

/-- Select through the charged fixed-weight packed readback decoder. -/
def fixedWeightPackedReadbackSelectCosted
    (bits : List Bool) (target : Bool)
    (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind (fixedWeightPackedReadbackDecodeCosted bits) fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.select target bits occurrence
      | none => none)

@[simp] theorem fixedWeightPackedReadbackSelectCosted_cost
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightPackedReadbackSelectCosted bits target occurrence).cost =
      fixedWeightPayloadBudget bits := by
  simp [fixedWeightPackedReadbackSelectCosted]

@[simp] theorem fixedWeightPackedReadbackSelectCosted_erase
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    (fixedWeightPackedReadbackSelectCosted bits target occurrence).erase =
      Succinct.select target bits occurrence := by
  simp [fixedWeightPackedReadbackSelectCosted]

/--
Compressed rank/select directory profile for one bitvector.

Unlike `BitVectorRankSelectDirectory`, this surface does not charge the raw
`bits.length` stored-bit prefix.  Its payload is bounded by the fixed-weight
universe budget plus `overhead bits.length` auxiliary bits.
-/
structure CompressedBitVectorRankSelectDirectory
    (bits : List Bool) (overhead queryCost : Nat) where
  payload : List Bool
  payload_length_le :
    payload.length <= fixedWeightPayloadBudget bits + overhead
  accessCosted : Nat -> Costed (Option Bool)
  rankCosted : Bool -> Nat -> Costed Nat
  selectCosted : Bool -> Nat -> Costed (Option Nat)
  access_cost_le : forall i, (accessCosted i).cost <= queryCost
  rank_cost_le :
    forall target pos, (rankCosted target pos).cost <= queryCost
  select_cost_le :
    forall target occurrence,
      (selectCosted target occurrence).cost <= queryCost
  access_exact : forall i, (accessCosted i).erase = bits[i]?
  rank_exact :
    forall target pos,
      (rankCosted target pos).erase =
        Succinct.rankPrefix target bits pos
  select_exact :
    forall target occurrence,
      (selectCosted target occurrence).erase =
        Succinct.select target bits occurrence

namespace CompressedBitVectorRankSelectDirectory

def accessQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (i : Nat) : Costed (Option Bool) :=
  directory.accessCosted i

def rankQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  directory.rankCosted target pos

def selectQueryCosted
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  directory.selectCosted target occurrence

theorem profile
    {bits : List Bool} {overhead queryCost : Nat}
    (directory :
      CompressedBitVectorRankSelectDirectory bits overhead queryCost) :
    directory.payload.length <=
        fixedWeightPayloadBudget bits + overhead /\
      (forall i,
        (directory.accessQueryCosted i).cost <= queryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= queryCost /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <= queryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · exact directory.payload_length_le
  · constructor
    · intro i
      exact ⟨directory.access_cost_le i, directory.access_exact i⟩
    · constructor
      · intro target pos
        exact
          ⟨directory.rank_cost_le target pos,
            directory.rank_exact target pos⟩
      · intro target occurrence
        exact
          ⟨directory.select_cost_le target occurrence,
            directory.select_exact target occurrence⟩

end CompressedBitVectorRankSelectDirectory

/--
Concrete packed fixed-weight readback directory for one bitvector.

This consumes the packed payload through the charged readback decoder above.
Its query budget is the packed payload budget for this bitvector, so it is a
non-oracular readback construction rather than the final constant-query FID
family.
-/
def fixedWeightPackedReadbackDirectory
    (bits : List Bool) :
    CompressedBitVectorRankSelectDirectory
      bits 0 (fixedWeightPayloadBudget bits) where
  payload := fixedWeightPackedPayload bits
  payload_length_le := by
    simp [fixedWeightPackedPayload_length]
  accessCosted := fixedWeightPackedReadbackAccessCosted bits
  rankCosted := fixedWeightPackedReadbackRankCosted bits
  selectCosted := fixedWeightPackedReadbackSelectCosted bits
  access_cost_le := by
    intro i
    simp
  rank_cost_le := by
    intro target pos
    simp
  select_cost_le := by
    intro target occurrence
    simp
  access_exact := by
    intro i
    simp
  rank_exact := by
    intro target pos
    simp
  select_exact := by
    intro target occurrence
    simp

theorem fixedWeightPackedReadbackDirectory_profile
    (bits : List Bool) :
    (fixedWeightPackedReadbackDirectory bits).payload =
        fixedWeightPackedPayload bits /\
      (fixedWeightPackedReadbackDirectory bits).payload.length =
        fixedWeightPayloadBudget bits /\
      (forall i,
        ((fixedWeightPackedReadbackDirectory bits).accessQueryCosted i).cost =
            fixedWeightPayloadBudget bits /\
          ((fixedWeightPackedReadbackDirectory bits).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((fixedWeightPackedReadbackDirectory bits).rankQueryCosted
            target pos).cost = fixedWeightPayloadBudget bits /\
          ((fixedWeightPackedReadbackDirectory bits).rankQueryCosted
            target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((fixedWeightPackedReadbackDirectory bits).selectQueryCosted
            target occurrence).cost =
            fixedWeightPayloadBudget bits /\
          ((fixedWeightPackedReadbackDirectory bits).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · rfl
  · constructor
    · exact fixedWeightPackedPayload_length bits
    · constructor
      · intro i
        exact
          ⟨fixedWeightPackedReadbackAccessCosted_cost bits i,
            fixedWeightPackedReadbackAccessCosted_erase bits i⟩
      · constructor
        · intro target pos
          exact
            ⟨fixedWeightPackedReadbackRankCosted_cost bits target pos,
              fixedWeightPackedReadbackRankCosted_erase bits target pos⟩
        · intro target occurrence
          exact
            ⟨fixedWeightPackedReadbackSelectCosted_cost bits target occurrence,
              fixedWeightPackedReadbackSelectCosted_erase
                bits target occurrence⟩

/-- Number of bounded payload words in the chunked fixed-weight readback view. -/
def fixedWeightPackedReadbackWordCount
    (bits : List Bool) (wordSize : Nat) : Nat :=
  (SuccinctSpace.chunkPayloadWords wordSize
    (fixedWeightPackedPayload bits)).length

/--
Chunked readback data for the fixed-weight packed payload.

The store is tied to `fixedWeightPackedPayload bits`, and every stored word is
bounded by `wordSize`.
-/
structure FixedWeightPackedReadbackData
    (bits : List Bool) (wordSize : Nat) where
  wordSize_pos : 0 < wordSize
  wordStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize

namespace FixedWeightPackedReadbackData

/-- Canonical chunked readback data for one bitvector and positive word size. -/
def ofChunks
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    FixedWeightPackedReadbackData bits wordSize where
  wordSize_pos := hword
  wordStore :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunks
      (fixedWeightPackedPayload bits) hword

/-- Read and flatten all payload words, charging one read per stored word. -/
def readCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    Costed (List Bool) :=
  Costed.map SuccinctSpace.flattenPayloadWords
    data.wordStore.store.readAllWordsCosted

@[simp] theorem readCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.readCosted.cost = data.wordStore.store.words.size := by
  simp [readCosted]

@[simp] theorem readCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.readCosted.erase = fixedWeightPackedPayload bits := by
  simpa [readCosted] using
    data.wordStore.store.readAllWordsCosted_flatten_erase

/-- Decode the charged chunked payload readback. -/
def decodeCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    Costed (Option (List Bool)) :=
  Costed.bind data.readCosted fun payload =>
    Costed.pure
      (fixedWeightDecode? bits.length (trueCount bits)
        (SuccinctSpace.bitsToNatLE payload))

@[simp] theorem decodeCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.decodeCosted.cost = data.wordStore.store.words.size := by
  simp [decodeCosted]

@[simp] theorem decodeCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    data.decodeCosted.erase = some bits := by
  simp [decodeCosted, fixedWeightDecode?_packedPayload]

/-- Access through chunked packed-payload readback. -/
def accessCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (i : Nat) : Costed (Option Bool) :=
  Costed.bind data.decodeCosted fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => bits[i]?
      | none => none)

@[simp] theorem accessCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).cost = data.wordStore.store.words.size := by
  simp [accessCosted]

@[simp] theorem accessCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted]

/-- Rank through chunked packed-payload readback. -/
def rankCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind data.decodeCosted fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.rankPrefix target bits pos
      | none => 0)

@[simp] theorem rankCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      data.wordStore.store.words.size := by
  simp [rankCosted]

@[simp] theorem rankCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [rankCosted]

/-- Select through chunked packed-payload readback. -/
def selectCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind data.decodeCosted fun decoded =>
    Costed.pure
      (match decoded with
      | some bits => Succinct.select target bits occurrence
      | none => none)

@[simp] theorem selectCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      data.wordStore.store.words.size := by
  simp [selectCosted]

@[simp] theorem selectCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  simp [selectCosted]

theorem read_words_length_le
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize)
    {word : List Bool}
    (hmem : List.Mem word data.wordStore.store.words.toList) :
    word.length <= wordSize :=
  data.wordStore.word_length_le_of_mem hmem

/-- Chunked readback data as a compressed directory with word-count query cost. -/
def toCompressedDirectory
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    CompressedBitVectorRankSelectDirectory
      bits 0 data.wordStore.store.words.size where
  payload := fixedWeightPackedPayload bits
  payload_length_le := by
    simp [fixedWeightPackedPayload_length]
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    simp
  rank_cost_le := by
    intro target pos
    simp
  select_cost_le := by
    intro target occurrence
    simp
  access_exact := by
    intro i
    simp
  rank_exact := by
    intro target pos
    simp
  select_exact := by
    intro target occurrence
    simp

theorem profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightPackedReadbackData bits wordSize) :
    (data.toCompressedDirectory).payload =
        fixedWeightPackedPayload bits /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost =
            data.wordStore.store.words.size /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost =
            data.wordStore.store.words.size /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost =
            data.wordStore.store.words.size /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  exact
    And.intro rfl
      (And.intro (fixedWeightPackedPayload_length bits)
        (And.intro
          (fun i =>
            And.intro (data.accessCosted_cost i)
              (data.accessCosted_erase i))
          (And.intro
            (fun target pos =>
              And.intro (data.rankCosted_cost target pos)
                (data.rankCosted_erase target pos))
            (fun target occurrence =>
              And.intro (data.selectCosted_cost target occurrence)
                (data.selectCosted_erase target occurrence)))))

theorem ofChunks_word_count
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    ((ofChunks bits hword).wordStore.store.words.size) =
      fixedWeightPackedReadbackWordCount bits wordSize := by
  simp [ofChunks, fixedWeightPackedReadbackWordCount,
    SuccinctSpace.BoundedPayloadWordStore.ofChunks]

theorem ofChunks_profile
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    let data := ofChunks bits hword
    (data.toCompressedDirectory).payload =
        fixedWeightPackedPayload bits /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost =
            fixedWeightPackedReadbackWordCount bits wordSize /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost =
            fixedWeightPackedReadbackWordCount bits wordSize /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost =
            fixedWeightPackedReadbackWordCount bits wordSize /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  dsimp
  simpa [ofChunks_word_count bits hword] using
    profile (ofChunks bits hword)

end FixedWeightPackedReadbackData

/--
Read a bounded payload-word store at a fixed list of word indices.

This is the small RAM-model kernel used by the compressed/FID auxiliary layer
below: one modeled read is charged per requested word, and the erased result is
exactly the list of words returned by the counted store.
-/
def boundedPayloadWordReadValues
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) : List (Option (List Bool)) :=
  indices.map fun i => store.store.words[i]?

def boundedPayloadWordReadsCosted
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize) :
    List Nat -> Costed (List (Option (List Bool)))
  | [] => Costed.pure []
  | i :: rest =>
      Costed.bind (store.store.readWordCosted i) fun word? =>
        Costed.bind (boundedPayloadWordReadsCosted store rest) fun words =>
          Costed.pure (word? :: words)

@[simp] theorem boundedPayloadWordReadsCosted_cost
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (boundedPayloadWordReadsCosted store indices).cost = indices.length := by
  induction indices with
  | nil =>
      simp [boundedPayloadWordReadsCosted]
  | cons i rest ih =>
      simp [boundedPayloadWordReadsCosted, ih, Nat.add_comm]

@[simp] theorem boundedPayloadWordReadsCosted_erase
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (boundedPayloadWordReadsCosted store indices).erase =
      boundedPayloadWordReadValues store indices := by
  induction indices with
  | nil =>
      simp [boundedPayloadWordReadsCosted, boundedPayloadWordReadValues]
  | cons i rest ih =>
      simp [boundedPayloadWordReadsCosted, boundedPayloadWordReadValues, ih]

@[simp] theorem boundedPayloadWordReadsCosted_value
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    (indices : List Nat) :
    (boundedPayloadWordReadsCosted store indices).value =
      boundedPayloadWordReadValues store indices := by
  simpa [Costed.erase] using
    boundedPayloadWordReadsCosted_erase store indices

/--
Read a primary bounded payload-word store, then choose the auxiliary read
schedule from the charged primary read values.

This is the generic RAM-model kernel needed by RRR-style local blocks: the
second table address can depend on the packed class/code read without becoming
a proof-only oracle.
-/
def dependentPayloadWordReadsCosted
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    Costed (List (Option (List Bool)) × List (Option (List Bool))) :=
  Costed.bind (boundedPayloadWordReadsCosted primaryStore primaryReads)
    fun primaryWords =>
      Costed.bind
          (boundedPayloadWordReadsCosted auxStore (auxReads primaryWords))
        fun auxWords =>
          Costed.pure (primaryWords, auxWords)

@[simp] theorem dependentPayloadWordReadsCosted_cost
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (dependentPayloadWordReadsCosted primaryStore auxStore primaryReads
        auxReads).cost =
      primaryReads.length +
        (auxReads
          (boundedPayloadWordReadValues primaryStore primaryReads)).length := by
  simp [dependentPayloadWordReadsCosted]

@[simp] theorem dependentPayloadWordReadsCosted_erase
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (dependentPayloadWordReadsCosted primaryStore auxStore primaryReads
        auxReads).erase =
      (boundedPayloadWordReadValues primaryStore primaryReads,
        boundedPayloadWordReadValues auxStore
          (auxReads
            (boundedPayloadWordReadValues primaryStore primaryReads))) := by
  simp [dependentPayloadWordReadsCosted]

@[simp] theorem dependentPayloadWordReadsCosted_value
    {primaryPayload auxPayload : List Bool} {wordSize : Nat}
    (primaryStore :
      SuccinctSpace.BoundedPayloadWordStore primaryPayload wordSize)
    (auxStore :
      SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize)
    (primaryReads : List Nat)
    (auxReads : List (Option (List Bool)) -> List Nat) :
    (dependentPayloadWordReadsCosted primaryStore auxStore primaryReads
        auxReads).value =
      (boundedPayloadWordReadValues primaryStore primaryReads,
        boundedPayloadWordReadValues auxStore
          (auxReads
            (boundedPayloadWordReadValues primaryStore primaryReads))) := by
  simpa [Costed.erase] using
    dependentPayloadWordReadsCosted_erase primaryStore auxStore primaryReads
      auxReads

/--
Compressed fixed-weight auxiliary data with constant-bounded word reads.

The counted payload is the canonical fixed-weight packed code plus an auxiliary
payload of `overhead` bits. Each operation supplies a finite read schedule for
the packed store and the auxiliary store, and the cost is the number of
requested words. A constant-query family must bound those schedules uniformly.
The evaluator fields are the abstract local RAM kernel; the exactness fields
state that those kernels answer the public access/rank/select semantics from
the charged read values. Concrete non-oracular instances must ensure those
evaluators are fixed code over the read values, not proof-only access to the
decoded bitvector.
-/
structure FixedWeightCompressedAuxiliaryData
    (bits : List Bool) (overhead wordSize queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  packedStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize
  auxPayload : List Bool
  auxStore :
    SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize
  aux_length_eq : auxPayload.length = overhead
  accessPackedReads : Nat -> List Nat
  accessAuxReads : Nat -> List Nat
  rankPackedReads : Bool -> Nat -> List Nat
  rankAuxReads : Bool -> Nat -> List Nat
  selectPackedReads : Bool -> Nat -> List Nat
  selectAuxReads : Bool -> Nat -> List Nat
  accessEval :
    Nat -> List (Option (List Bool)) -> List (Option (List Bool)) ->
      Option Bool
  rankEval :
    Bool -> Nat -> List (Option (List Bool)) ->
      List (Option (List Bool)) -> Nat
  selectEval :
    Bool -> Nat -> List (Option (List Bool)) ->
      List (Option (List Bool)) -> Option Nat
  access_read_count_le :
    forall i,
      (accessPackedReads i).length + (accessAuxReads i).length <= queryCost
  rank_read_count_le :
    forall target pos,
      (rankPackedReads target pos).length +
          (rankAuxReads target pos).length <= queryCost
  select_read_count_le :
    forall target occurrence,
      (selectPackedReads target occurrence).length +
          (selectAuxReads target occurrence).length <= queryCost
  access_eval_exact :
    forall i,
      accessEval i
          (boundedPayloadWordReadValues packedStore (accessPackedReads i))
          (boundedPayloadWordReadValues auxStore (accessAuxReads i)) =
        bits[i]?
  rank_eval_exact :
    forall target pos,
      rankEval target pos
          (boundedPayloadWordReadValues packedStore
            (rankPackedReads target pos))
          (boundedPayloadWordReadValues auxStore
            (rankAuxReads target pos)) =
        Succinct.rankPrefix target bits pos
  select_eval_exact :
    forall target occurrence,
      selectEval target occurrence
          (boundedPayloadWordReadValues packedStore
            (selectPackedReads target occurrence))
          (boundedPayloadWordReadValues auxStore
            (selectAuxReads target occurrence)) =
        Succinct.select target bits occurrence

namespace FixedWeightCompressedAuxiliaryData

def payload
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost) :
    List Bool :=
  fixedWeightPackedPayload bits ++ data.auxPayload

@[simp] theorem payload_length
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost) :
    data.payload.length = fixedWeightPayloadBudget bits + overhead := by
  simp [payload, fixedWeightPackedPayload_length, data.aux_length_eq]

def accessCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) : Costed (Option Bool) :=
  Costed.bind
      (boundedPayloadWordReadsCosted data.packedStore
        (data.accessPackedReads i)) fun packedWords =>
    Costed.bind
        (boundedPayloadWordReadsCosted data.auxStore
          (data.accessAuxReads i)) fun auxWords =>
      Costed.pure (data.accessEval i packedWords auxWords)

@[simp] theorem accessCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost =
      (data.accessPackedReads i).length +
        (data.accessAuxReads i).length := by
  simp [accessCosted]

theorem accessCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost <= queryCost := by
  simpa using data.access_read_count_le i

@[simp] theorem accessCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted, data.access_eval_exact]

def rankCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind
      (boundedPayloadWordReadsCosted data.packedStore
        (data.rankPackedReads target pos)) fun packedWords =>
    Costed.bind
        (boundedPayloadWordReadsCosted data.auxStore
          (data.rankAuxReads target pos)) fun auxWords =>
      Costed.pure (data.rankEval target pos packedWords auxWords)

@[simp] theorem rankCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      (data.rankPackedReads target pos).length +
        (data.rankAuxReads target pos).length := by
  simp [rankCosted]

theorem rankCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= queryCost := by
  simpa using data.rank_read_count_le target pos

@[simp] theorem rankCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [rankCosted, data.rank_eval_exact]

def selectCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind
      (boundedPayloadWordReadsCosted data.packedStore
        (data.selectPackedReads target occurrence)) fun packedWords =>
    Costed.bind
        (boundedPayloadWordReadsCosted data.auxStore
          (data.selectAuxReads target occurrence)) fun auxWords =>
      Costed.pure
        (data.selectEval target occurrence packedWords auxWords)

@[simp] theorem selectCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      (data.selectPackedReads target occurrence).length +
        (data.selectAuxReads target occurrence).length := by
  simp [selectCosted]

theorem selectCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  simpa using data.select_read_count_le target occurrence

@[simp] theorem selectCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  simp [selectCosted, data.select_eval_exact]

def toCompressedDirectory
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost) :
    CompressedBitVectorRankSelectDirectory bits overhead queryCost where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := data.accessCosted_cost_le
  rank_cost_le := data.rankCosted_cost_le
  select_cost_le := data.selectCosted_cost_le
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

theorem directory_profile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightCompressedAuxiliaryData bits overhead wordSize queryCost) :
    (data.toCompressedDirectory).payload = data.payload /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits + overhead /\
      SuccinctSpace.flattenPayloadWords
          data.packedStore.store.words.toList =
        fixedWeightPackedPayload bits /\
      SuccinctSpace.flattenPayloadWords data.auxStore.store.words.toList =
        data.auxPayload /\
      (forall {word : List Bool},
        List.Mem word data.packedStore.store.words.toList ->
          word.length <= wordSize) /\
      (forall {word : List Bool},
        List.Mem word data.auxStore.store.words.toList ->
          word.length <= wordSize) /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost <=
            queryCost /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost <=
            queryCost /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost <= queryCost /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · rfl
  constructor
  · exact data.payload_length
  constructor
  · exact data.packedStore.erases
  constructor
  · exact data.auxStore.erases
  constructor
  · intro word hmem
    exact data.packedStore.word_length_le_of_mem hmem
  constructor
  · intro word hmem
    exact data.auxStore.word_length_le_of_mem hmem
  constructor
  · intro i
    exact ⟨data.accessCosted_cost_le i, data.accessCosted_erase i⟩
  constructor
  · intro target pos
    exact
      ⟨data.rankCosted_cost_le target pos,
        data.rankCosted_erase target pos⟩
  · intro target occurrence
    exact
      ⟨data.selectCosted_cost_le target occurrence,
        data.selectCosted_erase target occurrence⟩

end FixedWeightCompressedAuxiliaryData

/--
Compressed fixed-weight auxiliary data with dependent auxiliary reads.

The payload is still the packed fixed-weight code plus counted auxiliary bits,
but the auxiliary read schedule may depend on the charged packed-store read
values. This is a generic scaffold for local RRR-style blocks, where the
packed code determines the decoded-word table address. The evaluator fields
are still abstract; concrete non-oracular instances must expose fixed code over
the charged read values.
-/
structure FixedWeightDependentAuxiliaryData
    (bits : List Bool) (overhead wordSize queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  packedStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize
  auxPayload : List Bool
  auxStore :
    SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize
  aux_length_eq : auxPayload.length = overhead
  accessPackedReads : Nat -> List Nat
  accessAuxReads : Nat -> List (Option (List Bool)) -> List Nat
  rankPackedReads : Bool -> Nat -> List Nat
  rankAuxReads : Bool -> Nat -> List (Option (List Bool)) -> List Nat
  selectPackedReads : Bool -> Nat -> List Nat
  selectAuxReads : Bool -> Nat -> List (Option (List Bool)) -> List Nat
  accessEvalCosted :
    Nat -> List (Option (List Bool)) -> List (Option (List Bool)) ->
      Costed (Option Bool)
  rankEvalCosted :
    Bool -> Nat -> List (Option (List Bool)) ->
      List (Option (List Bool)) -> Costed Nat
  selectEvalCosted :
    Bool -> Nat -> List (Option (List Bool)) ->
      List (Option (List Bool)) -> Costed (Option Nat)
  access_query_cost_le :
    forall i,
      (accessPackedReads i).length +
          (accessAuxReads i
            (boundedPayloadWordReadValues packedStore
              (accessPackedReads i))).length +
          (accessEvalCosted i
            (boundedPayloadWordReadValues packedStore
              (accessPackedReads i))
            (boundedPayloadWordReadValues auxStore
              (accessAuxReads i
                (boundedPayloadWordReadValues packedStore
                  (accessPackedReads i))))).cost <=
        queryCost
  rank_query_cost_le :
    forall target pos,
      (rankPackedReads target pos).length +
          (rankAuxReads target pos
            (boundedPayloadWordReadValues packedStore
              (rankPackedReads target pos))).length +
          (rankEvalCosted target pos
            (boundedPayloadWordReadValues packedStore
              (rankPackedReads target pos))
            (boundedPayloadWordReadValues auxStore
              (rankAuxReads target pos
                (boundedPayloadWordReadValues packedStore
                  (rankPackedReads target pos))))).cost <=
        queryCost
  select_query_cost_le :
    forall target occurrence,
      (selectPackedReads target occurrence).length +
          (selectAuxReads target occurrence
            (boundedPayloadWordReadValues packedStore
              (selectPackedReads target occurrence))).length +
          (selectEvalCosted target occurrence
            (boundedPayloadWordReadValues packedStore
              (selectPackedReads target occurrence))
            (boundedPayloadWordReadValues auxStore
              (selectAuxReads target occurrence
                (boundedPayloadWordReadValues packedStore
                  (selectPackedReads target occurrence))))).cost <=
        queryCost
  access_eval_exact :
    forall i,
      (accessEvalCosted i
          (boundedPayloadWordReadValues packedStore (accessPackedReads i))
          (boundedPayloadWordReadValues auxStore
            (accessAuxReads i
              (boundedPayloadWordReadValues packedStore
                (accessPackedReads i))))).erase =
        bits[i]?
  rank_eval_exact :
    forall target pos,
      (rankEvalCosted target pos
          (boundedPayloadWordReadValues packedStore
            (rankPackedReads target pos))
          (boundedPayloadWordReadValues auxStore
            (rankAuxReads target pos
              (boundedPayloadWordReadValues packedStore
                (rankPackedReads target pos))))).erase =
        Succinct.rankPrefix target bits pos
  select_eval_exact :
    forall target occurrence,
      (selectEvalCosted target occurrence
          (boundedPayloadWordReadValues packedStore
            (selectPackedReads target occurrence))
          (boundedPayloadWordReadValues auxStore
            (selectAuxReads target occurrence
              (boundedPayloadWordReadValues packedStore
                (selectPackedReads target occurrence))))).erase =
        Succinct.select target bits occurrence

namespace FixedWeightDependentAuxiliaryData

def payload
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost) :
    List Bool :=
  fixedWeightPackedPayload bits ++ data.auxPayload

@[simp] theorem payload_length
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost) :
    data.payload.length = fixedWeightPayloadBudget bits + overhead := by
  simp [payload, fixedWeightPackedPayload_length, data.aux_length_eq]

def accessCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) : Costed (Option Bool) :=
  Costed.bind
      (dependentPayloadWordReadsCosted data.packedStore data.auxStore
        (data.accessPackedReads i) (data.accessAuxReads i)) fun readWords =>
    data.accessEvalCosted i readWords.1 readWords.2

@[simp] theorem accessCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost =
      (data.accessPackedReads i).length +
        (data.accessAuxReads i
          (boundedPayloadWordReadValues data.packedStore
            (data.accessPackedReads i))).length +
        (data.accessEvalCosted i
          (boundedPayloadWordReadValues data.packedStore
            (data.accessPackedReads i))
          (boundedPayloadWordReadValues data.auxStore
            (data.accessAuxReads i
              (boundedPayloadWordReadValues data.packedStore
                (data.accessPackedReads i))))).cost := by
  simp [accessCosted, Nat.add_assoc]

theorem accessCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost <= queryCost := by
  rw [data.accessCosted_cost i]
  exact data.access_query_cost_le i

@[simp] theorem accessCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted, data.access_eval_exact]

def rankCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind
      (dependentPayloadWordReadsCosted data.packedStore data.auxStore
        (data.rankPackedReads target pos)
        (data.rankAuxReads target pos)) fun readWords =>
    data.rankEvalCosted target pos readWords.1 readWords.2

@[simp] theorem rankCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      (data.rankPackedReads target pos).length +
        (data.rankAuxReads target pos
          (boundedPayloadWordReadValues data.packedStore
            (data.rankPackedReads target pos))).length +
        (data.rankEvalCosted target pos
          (boundedPayloadWordReadValues data.packedStore
            (data.rankPackedReads target pos))
          (boundedPayloadWordReadValues data.auxStore
            (data.rankAuxReads target pos
              (boundedPayloadWordReadValues data.packedStore
                (data.rankPackedReads target pos))))).cost := by
  simp [rankCosted, Nat.add_assoc]

theorem rankCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= queryCost := by
  rw [data.rankCosted_cost target pos]
  exact data.rank_query_cost_le target pos

@[simp] theorem rankCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [rankCosted, data.rank_eval_exact]

def selectCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind
      (dependentPayloadWordReadsCosted data.packedStore data.auxStore
        (data.selectPackedReads target occurrence)
        (data.selectAuxReads target occurrence)) fun readWords =>
    data.selectEvalCosted target occurrence readWords.1 readWords.2

@[simp] theorem selectCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      (data.selectPackedReads target occurrence).length +
        (data.selectAuxReads target occurrence
          (boundedPayloadWordReadValues data.packedStore
            (data.selectPackedReads target occurrence))).length +
        (data.selectEvalCosted target occurrence
          (boundedPayloadWordReadValues data.packedStore
            (data.selectPackedReads target occurrence))
          (boundedPayloadWordReadValues data.auxStore
            (data.selectAuxReads target occurrence
              (boundedPayloadWordReadValues data.packedStore
                (data.selectPackedReads target occurrence))))).cost := by
  simp [selectCosted, Nat.add_assoc]

theorem selectCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  rw [data.selectCosted_cost target occurrence]
  exact data.select_query_cost_le target occurrence

@[simp] theorem selectCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  simp [selectCosted, data.select_eval_exact]

def toCompressedDirectory
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost) :
    CompressedBitVectorRankSelectDirectory bits overhead queryCost where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := data.accessCosted_cost_le
  rank_cost_le := data.rankCosted_cost_le
  select_cost_le := data.selectCosted_cost_le
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

def DirectoryProfile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost) :
    Prop :=
  (data.toCompressedDirectory).payload = data.payload /\
    (data.toCompressedDirectory).payload.length =
      fixedWeightPayloadBudget bits + overhead /\
    SuccinctSpace.flattenPayloadWords
        data.packedStore.store.words.toList =
      fixedWeightPackedPayload bits /\
    SuccinctSpace.flattenPayloadWords data.auxStore.store.words.toList =
      data.auxPayload /\
    (forall {word : List Bool},
      List.Mem word data.packedStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall {word : List Bool},
      List.Mem word data.auxStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      ((data.toCompressedDirectory).accessQueryCosted i).cost <=
          queryCost /\
        ((data.toCompressedDirectory).accessQueryCosted i).erase =
          bits[i]?) /\
    (forall target pos,
      ((data.toCompressedDirectory).rankQueryCosted target pos).cost <=
          queryCost /\
        ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
          Succinct.rankPrefix target bits pos) /\
    (forall target occurrence,
      ((data.toCompressedDirectory).selectQueryCosted
          target occurrence).cost <= queryCost /\
        ((data.toCompressedDirectory).selectQueryCosted
          target occurrence).erase =
          Succinct.select target bits occurrence)

theorem directory_profile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightDependentAuxiliaryData bits overhead wordSize queryCost) :
    data.DirectoryProfile := by
  constructor
  · rfl
  constructor
  · exact data.payload_length
  constructor
  · exact data.packedStore.erases
  constructor
  · exact data.auxStore.erases
  constructor
  · intro word hmem
    exact data.packedStore.word_length_le_of_mem hmem
  constructor
  · intro word hmem
    exact data.auxStore.word_length_le_of_mem hmem
  constructor
  · intro i
    exact ⟨data.accessCosted_cost_le i, data.accessCosted_erase i⟩
  constructor
  · intro target pos
    exact
      ⟨data.rankCosted_cost_le target pos,
        data.rankCosted_erase target pos⟩
  · intro target occurrence
    exact
      ⟨data.selectCosted_cost_le target occurrence,
        data.selectCosted_erase target occurrence⟩

end FixedWeightDependentAuxiliaryData

/-- Packed fixed-weight code word for each block in a block decomposition. -/
def fixedWeightBlockCodeWords (blocks : List (List Bool)) :
    List (List Bool) :=
  blocks.map fixedWeightPackedPayload

/-- Counted primary payload for a block-coded fixed-weight bitvector. -/
def fixedWeightBlockCodePayload (blocks : List (List Bool)) : List Bool :=
  SuccinctSpace.flattenPayloadWords (fixedWeightBlockCodeWords blocks)

/-- Sum of the fixed-weight code widths of all blocks. -/
def fixedWeightBlockPayloadBudget (blocks : List (List Bool)) : Nat :=
  (blocks.map fixedWeightPayloadBudget).sum

@[simp] theorem fixedWeightBlockCodeWords_length
    (blocks : List (List Bool)) :
    (fixedWeightBlockCodeWords blocks).length = blocks.length := by
  simp [fixedWeightBlockCodeWords]

theorem fixedWeightBlockCodePayload_length
    (blocks : List (List Bool)) :
    (fixedWeightBlockCodePayload blocks).length =
      fixedWeightBlockPayloadBudget blocks := by
  induction blocks with
  | nil =>
      simp [fixedWeightBlockCodePayload, fixedWeightBlockCodeWords,
        fixedWeightBlockPayloadBudget, SuccinctSpace.flattenPayloadWords]
  | cons block rest ih =>
      simp [fixedWeightBlockCodePayload, fixedWeightBlockCodeWords,
        fixedWeightBlockPayloadBudget, SuccinctSpace.flattenPayloadWords,
        fixedWeightPackedPayload_length]
      simpa [fixedWeightBlockCodePayload, fixedWeightBlockCodeWords,
        fixedWeightBlockPayloadBudget] using ih

/-- Bounded word store for the per-block fixed-weight code payload. -/
def fixedWeightBlockCodeBoundedStore
    (blocks : List (List Bool)) {wordSize : Nat}
    (hcode :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightPayloadBudget block <= wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload blocks) wordSize where
  store :=
    { words := (fixedWeightBlockCodeWords blocks).toArray
      erases := by
        simp [fixedWeightBlockCodePayload] }
  word_length_le := by
    intro word hmem
    have hlist :
        List.Mem word (fixedWeightBlockCodeWords blocks) := by
      simpa using hmem
    have hmap :
        List.Mem word (blocks.map fixedWeightPackedPayload) := by
      simpa [fixedWeightBlockCodeWords] using hlist
    rcases List.mem_map.mp hmap with ⟨block, hblock, rfl⟩
    rw [fixedWeightPackedPayload_length]
    exact hcode hblock

theorem fixedWeightBlockCodeBoundedStore_words_toList
    (blocks : List (List Bool)) {wordSize : Nat}
    (hcode :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightPayloadBudget block <= wordSize) :
    (fixedWeightBlockCodeBoundedStore blocks hcode).store.words.toList =
      fixedWeightBlockCodeWords blocks := by
  simp [fixedWeightBlockCodeBoundedStore]

theorem fixedWeightAmbientBlockCodeStore_get?_of_aligned
    {blocks : List (List Bool)} {wordSize : Nat}
    {store :
      SuccinctSpace.BoundedPayloadWordStore
        (fixedWeightBlockCodePayload blocks) wordSize}
    (halign : store.store.words.toList = fixedWeightBlockCodeWords blocks)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    store.store.words[blockIndex]? =
      some (fixedWeightPackedPayload block) := by
  have hlist :
      store.store.words.toList[blockIndex]? =
        some (fixedWeightPackedPayload block) := by
    rw [halign]
    simp [fixedWeightBlockCodeWords, List.getElem?_map, hblock]
  simpa [Array.getElem?_toList] using hlist

theorem fixedWeightBlockCodeBoundedStore_get?_of_block
    (blocks : List (List Bool)) {wordSize : Nat}
    (hcode :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightPayloadBudget block <= wordSize)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    (fixedWeightBlockCodeBoundedStore blocks hcode).store.words[blockIndex]? =
      some (fixedWeightPackedPayload block) := by
  exact
    fixedWeightAmbientBlockCodeStore_get?_of_aligned
      (fixedWeightBlockCodeBoundedStore_words_toList blocks hcode)
      hblock

/--
Ambient auxiliary envelope for block-composed fixed-weight dictionaries.

This is the counted global directory budget, separate from the primary
per-block fixed-weight codes. It deliberately does not include the local dense
decoded-word table from `FixedWeightTableRAMBlockData`.
-/
def fixedWeightAmbientBlockAuxiliaryOverhead (slots n : Nat) : Nat :=
  SuccinctSpace.logLogSampledDirectoryOverhead slots n

theorem fixedWeightAmbientBlockAuxiliaryOverhead_littleO
    (slots : Nat) :
    SuccinctSpace.LittleOLinear
      (fixedWeightAmbientBlockAuxiliaryOverhead slots) := by
  unfold fixedWeightAmbientBlockAuxiliaryOverhead
  exact SuccinctSpace.logLogSampledDirectoryOverhead_littleO slots

/--
Ambient/global block composition data for fixed-weight blocks.

The primary payload is the concatenation of each block's canonical
fixed-weight code. The auxiliary payload is counted separately and can be
budgeted by an `o(n)` family. Query code may make dependent reads from the
block-code payload into the auxiliary payload, but exactness is still supplied
as a field; concrete non-oracular instances must instantiate these evaluators
from fixed table/RAM code over the charged reads.
-/
structure FixedWeightAmbientBlockCompositionData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
  blockSize : Nat
  blockSize_pos : 0 < blockSize
  blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits
  block_length_le :
    forall {block : List Bool}, List.Mem block blocks ->
      block.length <= blockSize
  blockSize_le_wordSize : blockSize <= wordSize
  block_code_width_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightPayloadBudget block <= wordSize
  codeStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload blocks) wordSize
  auxPayload : List Bool
  auxStore :
    SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize
  aux_length_eq : auxPayload.length = overhead
  accessCodeReads : Nat -> List Nat
  accessAuxReads : Nat -> List (Option (List Bool)) -> List Nat
  rankCodeReads : Bool -> Nat -> List Nat
  rankAuxReads : Bool -> Nat -> List (Option (List Bool)) -> List Nat
  selectCodeReads : Bool -> Nat -> List Nat
  selectAuxReads : Bool -> Nat -> List (Option (List Bool)) -> List Nat
  accessEvalCosted :
    Nat -> List (Option (List Bool)) -> List (Option (List Bool)) ->
      Costed (Option Bool)
  rankEvalCosted :
    Bool -> Nat -> List (Option (List Bool)) ->
      List (Option (List Bool)) -> Costed Nat
  selectEvalCosted :
    Bool -> Nat -> List (Option (List Bool)) ->
      List (Option (List Bool)) -> Costed (Option Nat)
  access_query_cost_le :
    forall i,
      (accessCodeReads i).length +
          (accessAuxReads i
            (boundedPayloadWordReadValues codeStore
              (accessCodeReads i))).length +
          (accessEvalCosted i
            (boundedPayloadWordReadValues codeStore
              (accessCodeReads i))
            (boundedPayloadWordReadValues auxStore
              (accessAuxReads i
                (boundedPayloadWordReadValues codeStore
                  (accessCodeReads i))))).cost <=
        queryCost
  rank_query_cost_le :
    forall target pos,
      (rankCodeReads target pos).length +
          (rankAuxReads target pos
            (boundedPayloadWordReadValues codeStore
              (rankCodeReads target pos))).length +
          (rankEvalCosted target pos
            (boundedPayloadWordReadValues codeStore
              (rankCodeReads target pos))
            (boundedPayloadWordReadValues auxStore
              (rankAuxReads target pos
                (boundedPayloadWordReadValues codeStore
                  (rankCodeReads target pos))))).cost <=
        queryCost
  select_query_cost_le :
    forall target occurrence,
      (selectCodeReads target occurrence).length +
          (selectAuxReads target occurrence
            (boundedPayloadWordReadValues codeStore
              (selectCodeReads target occurrence))).length +
          (selectEvalCosted target occurrence
            (boundedPayloadWordReadValues codeStore
              (selectCodeReads target occurrence))
            (boundedPayloadWordReadValues auxStore
              (selectAuxReads target occurrence
                (boundedPayloadWordReadValues codeStore
                  (selectCodeReads target occurrence))))).cost <=
        queryCost
  access_eval_exact :
    forall i,
      (accessEvalCosted i
          (boundedPayloadWordReadValues codeStore (accessCodeReads i))
          (boundedPayloadWordReadValues auxStore
            (accessAuxReads i
              (boundedPayloadWordReadValues codeStore
                (accessCodeReads i))))).erase =
        bits[i]?
  rank_eval_exact :
    forall target pos,
      (rankEvalCosted target pos
          (boundedPayloadWordReadValues codeStore
            (rankCodeReads target pos))
          (boundedPayloadWordReadValues auxStore
            (rankAuxReads target pos
              (boundedPayloadWordReadValues codeStore
                (rankCodeReads target pos))))).erase =
        Succinct.rankPrefix target bits pos
  select_eval_exact :
    forall target occurrence,
      (selectEvalCosted target occurrence
          (boundedPayloadWordReadValues codeStore
            (selectCodeReads target occurrence))
          (boundedPayloadWordReadValues auxStore
            (selectAuxReads target occurrence
              (boundedPayloadWordReadValues codeStore
                (selectCodeReads target occurrence))))).erase =
        Succinct.select target bits occurrence

namespace FixedWeightAmbientBlockCompositionData

def payload
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) :
    List Bool :=
  fixedWeightBlockCodePayload blocks ++ data.auxPayload

@[simp] theorem payload_length
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) :
    data.payload.length =
      fixedWeightBlockPayloadBudget blocks + overhead := by
  simp [payload, fixedWeightBlockCodePayload_length, data.aux_length_eq]

def accessCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (i : Nat) : Costed (Option Bool) :=
  Costed.bind
      (dependentPayloadWordReadsCosted data.codeStore data.auxStore
        (data.accessCodeReads i) (data.accessAuxReads i)) fun readWords =>
    data.accessEvalCosted i readWords.1 readWords.2

@[simp] theorem accessCosted_cost
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost =
      (data.accessCodeReads i).length +
        (data.accessAuxReads i
          (boundedPayloadWordReadValues data.codeStore
            (data.accessCodeReads i))).length +
        (data.accessEvalCosted i
          (boundedPayloadWordReadValues data.codeStore
            (data.accessCodeReads i))
          (boundedPayloadWordReadValues data.auxStore
            (data.accessAuxReads i
              (boundedPayloadWordReadValues data.codeStore
                (data.accessCodeReads i))))).cost := by
  simp [accessCosted, Nat.add_assoc]

theorem accessCosted_cost_le
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost <= queryCost := by
  rw [data.accessCosted_cost i]
  exact data.access_query_cost_le i

@[simp] theorem accessCosted_erase
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted, data.access_eval_exact]

def rankCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind
      (dependentPayloadWordReadsCosted data.codeStore data.auxStore
        (data.rankCodeReads target pos)
        (data.rankAuxReads target pos)) fun readWords =>
    data.rankEvalCosted target pos readWords.1 readWords.2

@[simp] theorem rankCosted_cost
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      (data.rankCodeReads target pos).length +
        (data.rankAuxReads target pos
          (boundedPayloadWordReadValues data.codeStore
            (data.rankCodeReads target pos))).length +
        (data.rankEvalCosted target pos
          (boundedPayloadWordReadValues data.codeStore
            (data.rankCodeReads target pos))
          (boundedPayloadWordReadValues data.auxStore
            (data.rankAuxReads target pos
              (boundedPayloadWordReadValues data.codeStore
                (data.rankCodeReads target pos))))).cost := by
  simp [rankCosted, Nat.add_assoc]

theorem rankCosted_cost_le
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= queryCost := by
  rw [data.rankCosted_cost target pos]
  exact data.rank_query_cost_le target pos

@[simp] theorem rankCosted_erase
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [rankCosted, data.rank_eval_exact]

def selectCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind
      (dependentPayloadWordReadsCosted data.codeStore data.auxStore
        (data.selectCodeReads target occurrence)
        (data.selectAuxReads target occurrence)) fun readWords =>
    data.selectEvalCosted target occurrence readWords.1 readWords.2

@[simp] theorem selectCosted_cost
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      (data.selectCodeReads target occurrence).length +
        (data.selectAuxReads target occurrence
          (boundedPayloadWordReadValues data.codeStore
            (data.selectCodeReads target occurrence))).length +
        (data.selectEvalCosted target occurrence
          (boundedPayloadWordReadValues data.codeStore
            (data.selectCodeReads target occurrence))
          (boundedPayloadWordReadValues data.auxStore
            (data.selectAuxReads target occurrence
              (boundedPayloadWordReadValues data.codeStore
                (data.selectCodeReads target occurrence))))).cost := by
  simp [selectCosted, Nat.add_assoc]

theorem selectCosted_cost_le
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  rw [data.selectCosted_cost target occurrence]
  exact data.select_query_cost_le target occurrence

@[simp] theorem selectCosted_erase
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  simp [selectCosted, data.select_eval_exact]

def DirectoryProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) : Prop :=
  data.payload.length =
      fixedWeightBlockPayloadBudget blocks + overhead /\
    fixedWeightBlockCodePayload blocks =
      SuccinctSpace.flattenPayloadWords
        (fixedWeightBlockCodeWords blocks) /\
    (fixedWeightBlockCodePayload blocks).length =
      fixedWeightBlockPayloadBudget blocks /\
    SuccinctSpace.flattenPayloadWords blocks = bits /\
    SuccinctSpace.flattenPayloadWords data.codeStore.store.words.toList =
      fixedWeightBlockCodePayload blocks /\
    SuccinctSpace.flattenPayloadWords data.auxStore.store.words.toList =
      data.auxPayload /\
    data.auxPayload.length = overhead /\
    (forall {word : List Bool},
      List.Mem word data.codeStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall {word : List Bool},
      List.Mem word data.auxStore.store.words.toList ->
        word.length <= wordSize) /\
    wordSize <= Nat.log2 bits.length + 1 /\
    data.blockSize <= wordSize /\
    (forall {block : List Bool}, List.Mem block blocks ->
      block.length <= data.blockSize /\
        fixedWeightPayloadBudget block <= wordSize) /\
    (forall i,
      (data.accessCosted i).cost <= queryCost /\
        (data.accessCosted i).erase = bits[i]?) /\
    (forall target pos,
      (data.rankCosted target pos).cost <= queryCost /\
        (data.rankCosted target pos).erase =
          Succinct.rankPrefix target bits pos) /\
    (forall target occurrence,
      (data.selectCosted target occurrence).cost <= queryCost /\
        (data.selectCosted target occurrence).erase =
          Succinct.select target bits occurrence)

theorem directory_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) :
    data.DirectoryProfile := by
  constructor
  · exact data.payload_length
  constructor
  · rfl
  constructor
  · exact fixedWeightBlockCodePayload_length blocks
  constructor
  · exact data.blocks_flatten
  constructor
  · exact data.codeStore.erases
  constructor
  · exact data.auxStore.erases
  constructor
  · exact data.aux_length_eq
  constructor
  · intro word hmem
    exact data.codeStore.word_length_le_of_mem hmem
  constructor
  · intro word hmem
    exact data.auxStore.word_length_le_of_mem hmem
  constructor
  · exact data.wordSize_le_ambient
  constructor
  · exact data.blockSize_le_wordSize
  constructor
  · intro block hmem
    exact ⟨data.block_length_le hmem, data.block_code_width_le hmem⟩
  constructor
  · intro i
    exact ⟨data.accessCosted_cost_le i, data.accessCosted_erase i⟩
  constructor
  · intro target pos
    exact ⟨data.rankCosted_cost_le target pos,
      data.rankCosted_erase target pos⟩
  · intro target occurrence
    exact ⟨data.selectCosted_cost_le target occurrence,
      data.selectCosted_erase target occurrence⟩

/--
Ambient profile strengthened with explicit machine-word bounds for both the
block-code payload store and the auxiliary store.
-/
theorem word_bounded_directory_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightAmbientBlockCompositionData
        bits blocks overhead wordSize queryCost) :
    data.DirectoryProfile /\
      (forall {word : List Bool},
        List.Mem word data.codeStore.store.words.toList ->
          word.length <= Nat.log2 bits.length + 1) /\
      (forall {word : List Bool},
        List.Mem word data.auxStore.store.words.toList ->
          word.length <= Nat.log2 bits.length + 1) := by
  exact
    ⟨data.directory_profile,
      (fun hmem =>
        Nat.le_trans
          (data.codeStore.word_length_le_of_mem hmem)
          data.wordSize_le_ambient),
      (fun hmem =>
        Nat.le_trans
          (data.auxStore.word_length_le_of_mem hmem)
          data.wordSize_le_ambient)⟩

end FixedWeightAmbientBlockCompositionData

/--
Family of ambient/global block-composed fixed-weight dictionaries.

This is a predecessor surface for RRR/FID: it proves that the counted
auxiliary payload can follow an `o(n)` ambient budget, while the primary
payload is the sum of per-block fixed-weight code widths. The later FID step
is to relate that block-code primary payload to the global
`log binomial(n,m)` budget.
-/
structure FixedWeightAmbientBlockCompositionFamily
    (slots queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientBlockCompositionData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) queryCost

namespace FixedWeightAmbientBlockCompositionFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  fun n => primaryOverhead n + fixedWeightAmbientBlockAuxiliaryOverhead slots n

def directory
    {slots queryCost : Nat}
    (family : FixedWeightAmbientBlockCompositionFamily slots queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  family.component bits

theorem ambient_block_composition_profile
    {slots queryCost : Nat}
    (family : FixedWeightAmbientBlockCompositionFamily slots queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.directory bits
        data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (family.wordSize bits.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.directory bits
    have hprofile := data.directory_profile
    exact
      ⟨data.payload_length,
        data.aux_length_eq,
        data.blocks_flatten,
        data.wordSize_le_ambient,
        (fun i => ⟨data.accessCosted_cost_le i,
          data.accessCosted_erase i⟩),
        (fun target pos => ⟨data.rankCosted_cost_le target pos,
          data.rankCosted_erase target pos⟩),
        (fun target occurrence =>
          ⟨data.selectCosted_cost_le target occurrence,
            data.selectCosted_erase target occurrence⟩)⟩

/-- Family profile with explicit ambient machine-word bounds for read stores. -/
theorem word_bounded_profile
    {slots queryCost : Nat}
    (family : FixedWeightAmbientBlockCompositionFamily slots queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.directory bits
        data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.directory bits
    have hbounded := data.word_bounded_directory_profile
    exact
      ⟨data.payload_length,
        data.aux_length_eq,
        data.blocks_flatten,
        hbounded.2.1,
        hbounded.2.2,
        (fun i => ⟨data.accessCosted_cost_le i,
          data.accessCosted_erase i⟩),
        (fun target pos => ⟨data.rankCosted_cost_le target pos,
          data.rankCosted_erase target pos⟩),
        (fun target occurrence =>
          ⟨data.selectCosted_cost_le target occurrence,
            data.selectCosted_erase target occurrence⟩)⟩

/--
Conditional bridge from ambient block composition to the public compressed/FID
payload shape. The remaining primary theorem is isolated as `hprimary`.
-/
theorem compressed_profile_of_primary_budget
    {slots queryCost : Nat}
    (family : FixedWeightAmbientBlockCompositionFamily slots queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (fun n =>
          primaryOverhead n +
            fixedWeightAmbientBlockAuxiliaryOverhead slots n) /\
      forall bits : List Bool,
        let data := family.directory bits
        data.payload.length <=
            fixedWeightPayloadBudget bits +
              (primaryOverhead bits.length +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact hprimaryO.add
      (fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots)
  · intro bits
    let data := family.directory bits
    have hlen := data.payload_length
    have hbudget := hprimary bits
    constructor
    · rw [hlen]
      omega
    constructor
    · intro i
      exact ⟨data.accessCosted_cost_le i, data.accessCosted_erase i⟩
    constructor
    · intro target pos
      exact ⟨data.rankCosted_cost_le target pos,
        data.rankCosted_erase target pos⟩
    · intro target occurrence
      exact ⟨data.selectCosted_cost_le target occurrence,
        data.selectCosted_erase target occurrence⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots queryCost : Nat}
    (family : FixedWeightAmbientBlockCompositionFamily slots queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        let data := family.directory bits
        data.DirectoryProfile /\
          data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead slots primaryOverhead bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · simpa [compressedOverhead] using
      hprimaryO.add
        (fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots)
  · intro bits
    let data := family.directory bits
    have hbounded := data.word_bounded_directory_profile
    have hbudget := hprimary bits
    exact
      ⟨data.directory_profile,
        data.payload_length,
        by
          rw [data.payload_length]
          dsimp [compressedOverhead]
          omega,
        data.aux_length_eq,
        data.blocks_flatten,
        hbounded.2.1,
        hbounded.2.2,
        (fun i => ⟨data.accessCosted_cost_le i,
          data.accessCosted_erase i⟩),
        (fun target pos => ⟨data.rankCosted_cost_le target pos,
          data.rankCosted_erase target pos⟩),
        (fun target occurrence =>
          ⟨data.selectCosted_cost_le target occurrence,
            data.selectCosted_erase target occurrence⟩)⟩

end FixedWeightAmbientBlockCompositionFamily

/--
Family-level compressed/FID rank-select theorem surface.

The target profile is
`log2 (binomialCount n m) + 1 + o(n)` payload bits, where
`m = trueCount bits`, and constant modeled `access`, `rank`, and `select`.
-/
structure CompressedBitVectorRankSelectFamily
    (overhead : Nat -> Nat) (queryCost : Nat) where
  directory :
    forall bits : List Bool,
      CompressedBitVectorRankSelectDirectory
        bits (overhead bits.length) queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace CompressedBitVectorRankSelectFamily

theorem fixed_weight_constant_query_profile
    {overhead : Nat -> Nat} {queryCost : Nat}
    (family : CompressedBitVectorRankSelectFamily overhead queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        ((family.directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            ((family.directory bits).accessQueryCosted i).cost <=
                queryCost /\
              ((family.directory bits).accessQueryCosted i).erase =
                bits[i]?) /\
          (forall target pos,
            ((family.directory bits).rankQueryCosted target pos).cost <=
                queryCost /\
              ((family.directory bits).rankQueryCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            ((family.directory bits).selectQueryCosted
                target occurrence).cost <= queryCost /\
              ((family.directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact (family.directory bits).profile

end CompressedBitVectorRankSelectFamily

/--
Family of compressed fixed-weight auxiliary directories.

This is the generic constant-query FID join layer: a concrete future
construction must supply the components, read schedules, and local evaluators;
this adapter then accounts for the fixed-weight packed payload plus `o(n)`
auxiliary bits and feeds the public compressed family theorem.
-/
structure FixedWeightCompressedAuxiliaryFamily
    (overhead : Nat -> Nat) (wordSize queryCost : Nat) where
  component :
    forall bits : List Bool,
      FixedWeightCompressedAuxiliaryData
        bits (overhead bits.length) wordSize queryCost
  overhead_littleO : SuccinctSpace.LittleOLinear overhead

namespace FixedWeightCompressedAuxiliaryFamily

def toCompressedFamily
    {overhead : Nat -> Nat} {wordSize queryCost : Nat}
    (family :
      FixedWeightCompressedAuxiliaryFamily overhead wordSize queryCost) :
    CompressedBitVectorRankSelectFamily overhead queryCost where
  directory bits := (family.component bits).toCompressedDirectory
  overhead_littleO := family.overhead_littleO

theorem constant_query_profile
    {overhead : Nat -> Nat} {wordSize queryCost : Nat}
    (family :
      FixedWeightCompressedAuxiliaryFamily overhead wordSize queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        (((family.toCompressedFamily).directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            (((family.toCompressedFamily).directory bits).accessQueryCosted
                i).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).accessQueryCosted
                i).erase = bits[i]?) /\
          (forall target pos,
            (((family.toCompressedFamily).directory bits).rankQueryCosted
                target pos).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((family.toCompressedFamily).directory bits).selectQueryCosted
                target occurrence).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact family.toCompressedFamily.fixed_weight_constant_query_profile

theorem toCompressedFamily_fixed_weight_constant_query_profile
    {overhead : Nat -> Nat} {wordSize queryCost : Nat}
    (family :
      FixedWeightCompressedAuxiliaryFamily overhead wordSize queryCost) :
    SuccinctSpace.LittleOLinear overhead /\
      forall bits : List Bool,
        (((family.toCompressedFamily).directory bits).payload.length <=
          fixedWeightPayloadBudget bits + overhead bits.length) /\
          (forall i,
            (((family.toCompressedFamily).directory bits).accessQueryCosted
                i).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).accessQueryCosted
                i).erase = bits[i]?) /\
          (forall target pos,
            (((family.toCompressedFamily).directory bits).rankQueryCosted
                target pos).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).rankQueryCosted
                target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (((family.toCompressedFamily).directory bits).selectQueryCosted
                target occurrence).cost <= queryCost /\
              (((family.toCompressedFamily).directory bits).selectQueryCosted
                target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact family.constant_query_profile

end FixedWeightCompressedAuxiliaryFamily

/-- Decode an optional one-bit table entry as bitvector access. -/
def tableBackedAccessAnswer : Option (Option Nat) -> Option Bool
  | some (some 0) => some false
  | some (some (_ + 1)) => some true
  | _ => none

/-- Decode a rank table miss as the default zero answer. -/
def tableBackedRankAnswer : Option Nat -> Nat
  | some rank => rank
  | none => 0

/-- Decode an optional select table read. -/
def tableBackedSelectAnswer : Option (Option Nat) -> Option Nat
  | some answer => answer
  | none => none

/--
Pointwise table-backed fixed-weight FID data.

Unlike `FixedWeightCompressedAuxiliaryData`, the query procedures here are not
abstract evaluator fields. Access, rank, and select are fixed-width table reads
from counted auxiliary payload, followed by small decoders. This is a concrete
payload-live query layer; its auxiliary tables may still be too large for an
`o(n)` family until a real RRR/FID table construction replaces the dense
entries.
-/
structure FixedWeightTableBackedFIDData
    (bits : List Bool) (overhead wordSize queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_machine : wordSize <= Nat.log2 bits.length + 1
  packedStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize
  accessWidth : Nat
  accessEntries : List (Option Nat)
  accessTable :
    SuccinctSpace.FixedWidthOptionNatTable accessEntries accessWidth
  rankWidth : Nat
  trueRankEntries : List Nat
  falseRankEntries : List Nat
  rankTables :
    SuccinctSpace.FixedWidthRankSampleTables
      trueRankEntries falseRankEntries rankWidth
  selectWidth : Nat
  trueSelectEntries : List (Option Nat)
  falseSelectEntries : List (Option Nat)
  trueSelectTable :
    SuccinctSpace.FixedWidthOptionNatTable trueSelectEntries selectWidth
  falseSelectTable :
    SuccinctSpace.FixedWidthOptionNatTable falseSelectEntries selectWidth
  access_word_width_le :
    SuccinctSpace.optionNatWordWidth accessWidth <= wordSize
  rank_word_width_le : rankWidth <= wordSize
  select_word_width_le :
    SuccinctSpace.optionNatWordWidth selectWidth <= wordSize
  aux_length_eq :
    accessTable.payload.length + rankTables.payload.length +
        trueSelectTable.payload.length + falseSelectTable.payload.length =
      overhead
  queryCost_ge_one : 1 <= queryCost
  access_exact :
    forall i : Nat,
      tableBackedAccessAnswer (accessEntries[i]?) = bits[i]?
  rank_exact :
    forall (target : Bool) (pos : Nat),
      tableBackedRankAnswer ((rankTables.entries target)[pos]?) =
        Succinct.rankPrefix target bits pos
  select_exact :
    forall (target : Bool) (occurrence : Nat),
      tableBackedSelectAnswer
          (match target with
          | true => trueSelectEntries[occurrence]?
          | false => falseSelectEntries[occurrence]?) =
        Succinct.select target bits occurrence

namespace FixedWeightTableBackedFIDData

def auxPayload
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    List Bool :=
  data.accessTable.payload ++ data.rankTables.payload ++
    data.trueSelectTable.payload ++ data.falseSelectTable.payload

def payload
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    List Bool :=
  fixedWeightPackedPayload bits ++ data.auxPayload

@[simp] theorem auxPayload_length
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    data.auxPayload.length = overhead := by
  have haux :
      data.accessTable.payload.length + data.rankTables.payload.length +
          data.trueSelectTable.payload.length +
            data.falseSelectTable.payload.length =
        overhead := data.aux_length_eq
  unfold auxPayload
  simp only [List.length_append]
  omega

@[simp] theorem payload_length
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    data.payload.length = fixedWeightPayloadBudget bits + overhead := by
  unfold payload
  simp [fixedWeightPackedPayload_length, data.auxPayload_length]

def selectEntries
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) : List (Option Nat) :=
  match target with
  | true => data.trueSelectEntries
  | false => data.falseSelectEntries

def selectTableReadCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    Costed (Option (Option Nat)) :=
  match target with
  | true => data.trueSelectTable.readCosted occurrence
  | false => data.falseSelectTable.readCosted occurrence

@[simp] theorem selectTableReadCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectTableReadCosted target occurrence).cost = 1 := by
  cases target <;> simp [selectTableReadCosted]

@[simp] theorem selectTableReadCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectTableReadCosted target occurrence).erase =
      (data.selectEntries target)[occurrence]? := by
  cases target <;> simp [selectTableReadCosted, selectEntries]

def accessCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) : Costed (Option Bool) :=
  Costed.map tableBackedAccessAnswer (data.accessTable.readCosted i)

@[simp] theorem accessCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost = 1 := by
  simp [accessCosted]

theorem accessCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).cost <= queryCost := by
  simp [data.queryCost_ge_one]

@[simp] theorem accessCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted, data.access_exact]

def rankCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.map tableBackedRankAnswer
    (data.rankTables.sampleCosted target pos)

@[simp] theorem rankCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost = 1 := by
  simp [rankCosted]

theorem rankCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= queryCost := by
  simp [data.queryCost_ge_one]

@[simp] theorem rankCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  simp [rankCosted, data.rank_exact]

def selectCosted
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.map tableBackedSelectAnswer
    (data.selectTableReadCosted target occurrence)

@[simp] theorem selectCosted_cost
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost = 1 := by
  simp [selectCosted]

theorem selectCosted_cost_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost <= queryCost := by
  simp [data.queryCost_ge_one]

@[simp] theorem selectCosted_erase
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  cases target
  · simpa [selectCosted, selectTableReadCosted, selectEntries]
      using data.select_exact false occurrence
  · simpa [selectCosted, selectTableReadCosted, selectEntries]
      using data.select_exact true occurrence

def toCompressedDirectory
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    CompressedBitVectorRankSelectDirectory bits overhead queryCost where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := data.accessCosted_cost_le
  rank_cost_le := data.rankCosted_cost_le
  select_cost_le := data.selectCosted_cost_le
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

theorem access_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.accessTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.accessTable.word_length_of_get? hword
  have hwidth := data.access_word_width_le
  omega

theorem rank_true_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.rankTables.trueTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.rankTables.trueTable.word_length_of_get? hword
  have hwidth := data.rank_word_width_le
  omega

theorem rank_false_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.rankTables.falseTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.rankTables.falseTable.word_length_of_get? hword
  have hwidth := data.rank_word_width_le
  omega

theorem select_true_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.trueSelectTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.trueSelectTable.word_length_of_get? hword
  have hwidth := data.select_word_width_le
  omega

theorem select_false_table_word_length_le
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost)
    {i : Nat} {word : List Bool}
    (hword : data.falseSelectTable.store.words[i]? = some word) :
    word.length <= wordSize := by
  have hlen := data.falseSelectTable.word_length_of_get? hword
  have hwidth := data.select_word_width_le
  omega

theorem directory_profile
    {bits : List Bool} {overhead wordSize queryCost : Nat}
    (data :
      FixedWeightTableBackedFIDData bits overhead wordSize queryCost) :
    (data.toCompressedDirectory).payload = data.payload /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits + overhead /\
      SuccinctSpace.flattenPayloadWords
          data.packedStore.store.words.toList =
        fixedWeightPackedPayload bits /\
      data.auxPayload.length = overhead /\
      SuccinctSpace.flattenPayloadWords
          data.accessTable.store.words.toList =
        data.accessTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.rankTables.trueTable.store.words.toList =
        data.rankTables.trueTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.rankTables.falseTable.store.words.toList =
        data.rankTables.falseTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.trueSelectTable.store.words.toList =
        data.trueSelectTable.payload /\
      SuccinctSpace.flattenPayloadWords
          data.falseSelectTable.store.words.toList =
        data.falseSelectTable.payload /\
      (forall (i : Nat) (word : List Bool),
        data.accessTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.rankTables.trueTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.rankTables.falseTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.trueSelectTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      (forall (i : Nat) (word : List Bool),
        data.falseSelectTable.store.words[i]? = some word ->
          word.length <= wordSize) /\
      wordSize <= Nat.log2 bits.length + 1 /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost <=
            queryCost /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost <=
            queryCost /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost <= queryCost /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · rfl
  constructor
  · exact data.payload_length
  constructor
  · exact data.packedStore.erases
  constructor
  · exact data.auxPayload_length
  constructor
  · exact data.accessTable.store.payload_eq_words_join
  constructor
  · exact data.rankTables.trueTable.store.payload_eq_words_join
  constructor
  · exact data.rankTables.falseTable.store.payload_eq_words_join
  constructor
  · exact data.trueSelectTable.store.payload_eq_words_join
  constructor
  · exact data.falseSelectTable.store.payload_eq_words_join
  constructor
  · intro i word hword
    exact data.access_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.rank_true_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.rank_false_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.select_true_table_word_length_le hword
  constructor
  · intro i word hword
    exact data.select_false_table_word_length_le hword
  constructor
  · exact data.wordSize_le_machine
  constructor
  · intro i
    exact ⟨data.accessCosted_cost_le i, data.accessCosted_erase i⟩
  constructor
  · intro target pos
    exact
      ⟨data.rankCosted_cost_le target pos,
        data.rankCosted_erase target pos⟩
  · intro target occurrence
    exact
      ⟨data.selectCosted_cost_le target occurrence,
        data.selectCosted_erase target occurrence⟩

end FixedWeightTableBackedFIDData

/-- Payload of the universal fixed-weight decoded-word table. -/
def fixedWeightDecodedWordTablePayload (n k : Nat) : List Bool :=
  SuccinctSpace.flattenPayloadWords (fixedWeightBitstrings n k)

/-- Bit cost of the universal fixed-weight decoded-word table. -/
def fixedWeightDecodedWordTableOverhead (n k : Nat) : Nat :=
  binomialCount n k * n

@[simp] theorem fixedWeightDecodedWordTablePayload_length
    (n k : Nat) :
    (fixedWeightDecodedWordTablePayload n k).length =
      fixedWeightDecodedWordTableOverhead n k := by
  unfold fixedWeightDecodedWordTablePayload
  unfold fixedWeightDecodedWordTableOverhead
  calc
    (SuccinctSpace.flattenPayloadWords (fixedWeightBitstrings n k)).length =
        (fixedWeightBitstrings n k).length * n := by
      exact SuccinctSpace.flattenPayloadWords_length_of_forall_length
        (by
          intro word hmem
          exact (fixedWeightBitstrings_mem_length_trueCount hmem).1)
    _ = binomialCount n k * n := by
      rw [fixedWeightBitstrings_length]

/-- Canonical payload store for the universal fixed-weight decoded-word table. -/
def fixedWeightDecodedWordStore (n k : Nat) :
    SuccinctSpace.PayloadWordStore
      (fixedWeightDecodedWordTablePayload n k) where
  words := (fixedWeightBitstrings n k).toArray
  erases := by
    simp [fixedWeightDecodedWordTablePayload]

/--
Canonical bounded payload store for the universal fixed-weight decoded-word
table.
-/
def fixedWeightDecodedWordBoundedStore
    (n k wordSize : Nat) (hn : n <= wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightDecodedWordTablePayload n k) wordSize where
  store := fixedWeightDecodedWordStore n k
  word_length_le := by
    intro word hmem
    have hlist : List.Mem word (fixedWeightBitstrings n k) := by
      simpa [fixedWeightDecodedWordStore] using hmem
    have hlen := (fixedWeightBitstrings_mem_length_trueCount hlist).1
    omega

theorem fixedWeightDecodedWordBoundedStore_get?_of_decode
    {n k code : Nat} {word : List Bool} {wordSize : Nat}
    (hn : n <= wordSize)
    (hdec : fixedWeightDecode? n k code = some word) :
    (fixedWeightDecodedWordBoundedStore n k wordSize hn).store.words[code]? =
      some word := by
  simpa [fixedWeightDecodedWordBoundedStore, fixedWeightDecodedWordStore,
    fixedWeightDecode?] using hdec

theorem fixedWeightDecodedWordBoundedStore_get?_fixedWeightCode
    (bits : List Bool) {wordSize : Nat}
    (hn : bits.length <= wordSize) :
    (fixedWeightDecodedWordBoundedStore
        bits.length (trueCount bits) wordSize hn).store.words[fixedWeightCode bits]? =
      some bits := by
  have hdec :
      fixedWeightDecode? bits.length (trueCount bits)
          (fixedWeightCode bits) = some bits := by
    simpa [fixedWeightPackedPayload_bitsToNatLE] using
      fixedWeightDecode?_packedPayload bits
  exact
    fixedWeightDecodedWordBoundedStore_get?_of_decode hn hdec

/-- Canonical one-word store for the packed fixed-weight code. -/
def fixedWeightPackedCodeBoundedStore
    (bits : List Bool) (wordSize : Nat)
    (hcode : fixedWeightPayloadBudget bits <= wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize where
  store :=
    { words := #[fixedWeightPackedPayload bits]
      erases := by
        simp [SuccinctSpace.flattenPayloadWords] }
  word_length_le := by
    intro word hmem
    have hword : word = fixedWeightPackedPayload bits := by
      change List.Mem word (#[fixedWeightPackedPayload bits].toList) at hmem
      cases hmem with
      | head => rfl
      | tail _ htail => cases htail
    rw [hword, fixedWeightPackedPayload_length]
    exact hcode

theorem fixedWeightPackedCodeBoundedStore_get?_zero
    (bits : List Bool) {wordSize : Nat}
    (hcode : fixedWeightPayloadBudget bits <= wordSize) :
    (fixedWeightPackedCodeBoundedStore bits wordSize hcode).store.words[0]? =
      some (fixedWeightPackedPayload bits) := by
  simp [fixedWeightPackedCodeBoundedStore]

/-- Decode the first charged packed-code word as a fixed-weight code. -/
def fixedWeightCodeFromReadValues :
    List (Option (List Bool)) -> Nat
  | some word :: _ => SuccinctSpace.bitsToNatLE word
  | _ => 0

@[simp] theorem fixedWeightCodeFromReadValues_singleton
    (bits : List Bool) :
    fixedWeightCodeFromReadValues [some (fixedWeightPackedPayload bits)] =
      fixedWeightCode bits := by
  simp [fixedWeightCodeFromReadValues, fixedWeightPackedPayload_bitsToNatLE]

/--
Explicit evaluator budget for computing one fixed-weight/RRR local block from
its packed code.

This is intentionally not a succinct-family budget. It records that the local
kernel is doing real finite-universe decoding work instead of reading a dense
decoded-word table or using proof-only decoded bits.
-/
def fixedWeightComputedRRRDecodeTicks (bits : List Bool) : Nat :=
  binomialCount bits.length (trueCount bits) + bits.length

/-- Uniform query cap for the computed local RRR block kernel. -/
def fixedWeightComputedRRRQueryCost (bits : List Bool) : Nat :=
  fixedWeightComputedRRRDecodeTicks bits + 2

/-- Decode a fixed-weight code for the block class determined by `bits`. -/
def fixedWeightDecodedWordFromCode (bits : List Bool) (code : Nat) :
    List Bool :=
  (fixedWeightDecode? bits.length (trueCount bits) code).getD []

@[simp] theorem fixedWeightDecodedWordFromCode_fixedWeightCode
    (bits : List Bool) :
    fixedWeightDecodedWordFromCode bits (fixedWeightCode bits) = bits := by
  have hdec :
      fixedWeightDecode? bits.length (trueCount bits)
          (fixedWeightCode bits) = some bits := by
    exact
      fixedWeightDecode?_fixedWeightEncode?
        (fixedWeightEncode?_eq_some_fixedWeightCode bits)
  simp [fixedWeightDecodedWordFromCode, hdec]

/--
Fixed computation over charged packed-code read values.

The only input is the word value returned by the counted packed payload read;
there is no auxiliary decoded-word table and no proof-only access to the block.
-/
def fixedWeightComputedRRRDecodeFromReadValuesCosted
    (bits : List Bool) (packedWords : List (Option (List Bool))) :
    Costed (List Bool) :=
  Costed.tickValue (fixedWeightComputedRRRDecodeTicks bits)
    (fixedWeightDecodedWordFromCode bits
      (fixedWeightCodeFromReadValues packedWords))

@[simp] theorem fixedWeightComputedRRRDecodeFromReadValuesCosted_cost
    (bits : List Bool) (packedWords : List (Option (List Bool))) :
    (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
        packedWords).cost =
      fixedWeightComputedRRRDecodeTicks bits := by
  simp [fixedWeightComputedRRRDecodeFromReadValuesCosted]

@[simp] theorem fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
    (bits : List Bool) :
    (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
        [some (fixedWeightPackedPayload bits)]).erase =
      bits := by
  simp [fixedWeightComputedRRRDecodeFromReadValuesCosted]

/--
Local fixed-weight/RRR block kernel computed from the packed code only.

The counted payload is just `fixedWeightPackedPayload bits`. Queries read that
code word, spend the explicit `fixedWeightComputedRRRDecodeTicks bits`
evaluator budget to reconstruct the local block, and then use fixed code for
access/rank/select. This avoids the dense
`fixedWeightDecodedWordTablePayload` auxiliary table used by
`FixedWeightTableRAMBlockData`.
-/
structure FixedWeightComputedRRRBlockData
    (ambientLength : Nat) (bits : List Bool) (wordSize : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 ambientLength + 1
  codeWidth_le_wordSize : fixedWeightPayloadBudget bits <= wordSize
  blockWidth_le_wordSize : bits.length <= wordSize

namespace FixedWeightComputedRRRBlockData

def packedStore
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize :=
  fixedWeightPackedCodeBoundedStore bits wordSize
    data.codeWidth_le_wordSize

def payload
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (_data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    List Bool :=
  fixedWeightPackedPayload bits

@[simp] theorem payload_length
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.payload.length = fixedWeightPayloadBudget bits := by
  simp [payload, fixedWeightPackedPayload_length]

theorem packed_read_values_zero
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    boundedPayloadWordReadValues data.packedStore [0] =
      [some (fixedWeightPackedPayload bits)] := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  simp [boundedPayloadWordReadValues, hpacked]

def readCodeCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Costed Nat :=
  Costed.bind (data.packedStore.store.readWordCosted 0) fun word? =>
    Costed.pure
      (match word? with
      | some word => SuccinctSpace.bitsToNatLE word
      | none => 0)

@[simp] theorem readCodeCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.readCodeCosted.cost = 1 := by
  simp [readCodeCosted]

@[simp] theorem readCodeCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.readCodeCosted.erase = fixedWeightCode bits := by
  simp [readCodeCosted, packedStore, fixedWeightPackedCodeBoundedStore,
    fixedWeightPackedPayload_bitsToNatLE]

def decodedWordCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Costed (List Bool) :=
  Costed.bind data.readCodeCosted fun code =>
    Costed.tickValue (fixedWeightComputedRRRDecodeTicks bits)
      (fixedWeightDecodedWordFromCode bits code)

@[simp] theorem decodedWordCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.decodedWordCosted.cost =
      fixedWeightComputedRRRDecodeTicks bits + 1 := by
  simp [decodedWordCosted, Nat.add_comm]

@[simp] theorem decodedWordCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.decodedWordCosted.erase = bits := by
  simp [decodedWordCosted]

def accessCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (i : Nat) : Costed (Option Bool) :=
  Costed.map (fun word => word[i]?) data.decodedWordCosted

@[simp] theorem accessCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (i : Nat) :
    (data.accessCosted i).cost =
      fixedWeightComputedRRRDecodeTicks bits + 1 := by
  simp [accessCosted]

@[simp] theorem accessCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted]

def rankCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.rankBoolWordPrefix target word pos).toCosted

@[simp] theorem rankCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost =
      fixedWeightComputedRRRQueryCost bits := by
  simp [rankCosted, fixedWeightComputedRRRQueryCost]

@[simp] theorem rankCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  unfold rankCosted
  simp only [Costed.erase_bind, decodedWordCosted_erase]
  change (RAM.rankBoolWordPrefix target bits pos).toCosted.value =
    Succinct.rankPrefix target bits pos
  have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
  simpa [Costed.run] using congrArg Prod.fst hrun

def selectCosted
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.selectBoolWord target word occurrence).toCosted

@[simp] theorem selectCosted_cost
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost =
      fixedWeightComputedRRRQueryCost bits := by
  simp [selectCosted, fixedWeightComputedRRRQueryCost]

@[simp] theorem selectCosted_erase
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  unfold selectCosted
  simp only [Costed.erase_bind, decodedWordCosted_erase]
  change (RAM.selectBoolWord target bits occurrence).toCosted.value =
    Succinct.select target bits occurrence
  have hrun := Succinct.selectBoolWord_toCosted_run target bits occurrence
  simpa [Costed.run] using congrArg Prod.fst hrun

def toDependentAuxiliaryData
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    FixedWeightDependentAuxiliaryData
      bits 0 wordSize (fixedWeightComputedRRRQueryCost bits) := by
  refine
    { wordSize_pos := data.wordSize_pos
      packedStore := data.packedStore
      auxPayload := []
      auxStore :=
        SuccinctSpace.BoundedPayloadWordStore.ofChunks []
          data.wordSize_pos
      aux_length_eq := ?_
      accessPackedReads := fun _ => [0]
      accessAuxReads := fun _ _ => []
      rankPackedReads := fun _ _ => [0]
      rankAuxReads := fun _ _ _ => []
      selectPackedReads := fun _ _ => [0]
      selectAuxReads := fun _ _ _ => []
      accessEvalCosted := fun i packedWords _ =>
        Costed.map (fun word => word[i]?)
          (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
            packedWords)
      rankEvalCosted := fun target pos packedWords _ =>
        Costed.bind
          (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
            packedWords) fun word =>
          (RAM.rankBoolWordPrefix target word pos).toCosted
      selectEvalCosted := fun target occurrence packedWords _ =>
        Costed.bind
          (fixedWeightComputedRRRDecodeFromReadValuesCosted bits
            packedWords) fun word =>
          (RAM.selectBoolWord target word occurrence).toCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · simp
  · intro i
    simp [data.packed_read_values_zero, fixedWeightComputedRRRQueryCost]
    omega
  · intro target pos
    simp [data.packed_read_values_zero, fixedWeightComputedRRRQueryCost]
    omega
  · intro target occurrence
    simp [data.packed_read_values_zero, fixedWeightComputedRRRQueryCost]
    omega
  · intro i
    simp [data.packed_read_values_zero]
  · intro target pos
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton bits
    have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
    simp only [data.packed_read_values_zero, Costed.erase_bind]
    rw [hdecode]
    change (RAM.rankBoolWordPrefix target bits pos).toCosted.value =
      Succinct.rankPrefix target bits pos
    simpa [Costed.run] using congrArg Prod.fst hrun
  · intro target occurrence
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton bits
    have hrun := Succinct.selectBoolWord_toCosted_run
      target bits occurrence
    simp only [data.packed_read_values_zero, Costed.erase_bind]
    rw [hdecode]
    change (RAM.selectBoolWord target bits occurrence).toCosted.value =
      Succinct.select target bits occurrence
    simpa [Costed.run] using congrArg Prod.fst hrun

def toCompressedDirectory
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    CompressedBitVectorRankSelectDirectory
      bits 0 (fixedWeightComputedRRRQueryCost bits) where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    rw [data.accessCosted_cost i]
    unfold fixedWeightComputedRRRQueryCost
    omega
  rank_cost_le := by
    intro target pos
    simp
  select_cost_le := by
    intro target occurrence
    simp
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

def toBoundedCompressedDirectory
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    {queryCost : Nat}
    (hquery : fixedWeightComputedRRRQueryCost bits <= queryCost) :
    CompressedBitVectorRankSelectDirectory bits 0 queryCost where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    rw [data.accessCosted_cost i]
    unfold fixedWeightComputedRRRQueryCost at hquery
    omega
  rank_cost_le := by
    intro target pos
    rw [data.rankCosted_cost target pos]
    exact hquery
  select_cost_le := by
    intro target occurrence
    rw [data.selectCosted_cost target occurrence]
    exact hquery
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

/--
Profile for the computed local fixed-weight/RRR block kernel.

There is no decoded auxiliary payload: all exactness comes from a charged read
of the packed fixed-weight code plus the explicit decode tick budget.
-/
def KernelProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Prop :=
  (data.toCompressedDirectory).payload = fixedWeightPackedPayload bits /\
    (data.toCompressedDirectory).payload.length =
      fixedWeightPayloadBudget bits /\
    (data.toCompressedDirectory).payload.length =
      fixedWeightPayloadBudget bits + 0 /\
    SuccinctSpace.flattenPayloadWords
        data.packedStore.store.words.toList =
      fixedWeightPackedPayload bits /\
    data.packedStore.store.words[0]? =
      some (fixedWeightPackedPayload bits) /\
    fixedWeightPayloadBudget bits <= wordSize /\
    bits.length <= wordSize /\
    wordSize <= Nat.log2 ambientLength + 1 /\
    data.readCodeCosted.cost = 1 /\
    data.readCodeCosted.erase = fixedWeightCode bits /\
    data.decodedWordCosted.cost =
      fixedWeightComputedRRRDecodeTicks bits + 1 /\
    data.decodedWordCosted.erase = bits /\
    (forall {word : List Bool},
      List.Mem word data.packedStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      ((data.toCompressedDirectory).accessQueryCosted i).cost <=
          fixedWeightComputedRRRQueryCost bits /\
        ((data.toCompressedDirectory).accessQueryCosted i).erase =
          bits[i]?) /\
    (forall target pos,
      ((data.toCompressedDirectory).rankQueryCosted target pos).cost =
          fixedWeightComputedRRRQueryCost bits /\
        ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
          Succinct.rankPrefix target bits pos) /\
    (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
          target occurrence).cost =
          fixedWeightComputedRRRQueryCost bits /\
        ((data.toCompressedDirectory).selectQueryCosted
          target occurrence).erase =
          Succinct.select target bits occurrence)

/--
The computed local fixed-weight/RRR kernel is an instance of the generic
dependent-read compressed/FID scaffold with zero auxiliary payload.
-/
theorem dependent_auxiliary_data_profile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    (data.toDependentAuxiliaryData).DirectoryProfile := by
  exact
    FixedWeightDependentAuxiliaryData.directory_profile
      data.toDependentAuxiliaryData

theorem bounded_compressed_directory_profile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize)
    {queryCost : Nat}
    (hquery : fixedWeightComputedRRRQueryCost bits <= queryCost) :
    let directory := data.toBoundedCompressedDirectory hquery
    directory.payload = fixedWeightPackedPayload bits /\
      directory.payload.length = fixedWeightPayloadBudget bits /\
      directory.payload.length <= fixedWeightPayloadBudget bits + 0 /\
      data.readCodeCosted.cost = 1 /\
      data.readCodeCosted.erase = fixedWeightCode bits /\
      data.decodedWordCosted.cost =
        fixedWeightComputedRRRDecodeTicks bits + 1 /\
      data.decodedWordCosted.erase = bits /\
      fixedWeightComputedRRRQueryCost bits <= queryCost /\
      (forall i,
        (directory.accessQueryCosted i).cost <= queryCost /\
          (directory.accessQueryCosted i).erase = bits[i]?) /\
      (forall target pos,
        (directory.rankQueryCosted target pos).cost <= queryCost /\
          (directory.rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        (directory.selectQueryCosted target occurrence).cost <=
            queryCost /\
          (directory.selectQueryCosted target occurrence).erase =
            Succinct.select target bits occurrence) := by
  let directory := data.toBoundedCompressedDirectory hquery
  have hprofile := directory.profile
  exact
    ⟨rfl,
      by
        change data.payload.length = fixedWeightPayloadBudget bits
        exact data.payload_length,
      hprofile.1,
      data.readCodeCosted_cost,
      data.readCodeCosted_erase,
      data.decodedWordCosted_cost,
      data.decodedWordCosted_erase,
      hquery,
      hprofile.2.1,
      hprofile.2.2.1,
      hprofile.2.2.2⟩

/--
The direct computed-RRR local directory and the generic dependent-auxiliary
adapter expose the same packed payload and charged query behavior.
-/
def DependentAuxiliaryBridgeProfile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    Prop :=
  ((data.toDependentAuxiliaryData).toCompressedDirectory).payload =
      (data.toCompressedDirectory).payload /\
    (forall i,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).accessQueryCosted
          i).cost =
          ((data.toCompressedDirectory).accessQueryCosted i).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).accessQueryCosted
          i).erase =
          ((data.toCompressedDirectory).accessQueryCosted i).erase) /\
    (forall target pos,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).rankQueryCosted
          target pos).cost =
          ((data.toCompressedDirectory).rankQueryCosted target pos).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).rankQueryCosted
          target pos).erase =
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase) /\
    (forall target occurrence,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).selectQueryCosted
          target occurrence).cost =
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).selectQueryCosted
          target occurrence).erase =
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase)

theorem dependent_auxiliary_bridge_profile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.DependentAuxiliaryBridgeProfile := by
  constructor
  · change (data.toDependentAuxiliaryData).payload = data.payload
    simp [toDependentAuxiliaryData,
      FixedWeightDependentAuxiliaryData.payload, payload]
  constructor
  · intro i
    constructor
    · change ((data.toDependentAuxiliaryData).accessCosted i).cost =
        (data.accessCosted i).cost
      simp [toDependentAuxiliaryData,
        FixedWeightDependentAuxiliaryData.accessCosted,
        data.packed_read_values_zero,
        fixedWeightComputedRRRQueryCost]
      omega
    · change ((data.toDependentAuxiliaryData).accessCosted i).erase =
        (data.accessCosted i).erase
      rw [(data.toDependentAuxiliaryData).accessCosted_erase i,
        data.accessCosted_erase i]
  constructor
  · intro target pos
    constructor
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).cost =
        (data.rankCosted target pos).cost
      simp [toDependentAuxiliaryData,
        FixedWeightDependentAuxiliaryData.rankCosted,
        data.packed_read_values_zero,
        fixedWeightComputedRRRQueryCost]
      omega
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).erase =
        (data.rankCosted target pos).erase
      rw [(data.toDependentAuxiliaryData).rankCosted_erase target pos,
        data.rankCosted_erase target pos]
  · intro target occurrence
    constructor
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).cost =
        (data.selectCosted target occurrence).cost
      simp [toDependentAuxiliaryData,
        FixedWeightDependentAuxiliaryData.selectCosted,
        data.packed_read_values_zero,
        fixedWeightComputedRRRQueryCost]
      omega
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).erase =
        (data.selectCosted target occurrence).erase
      rw [(data.toDependentAuxiliaryData).selectCosted_erase
          target occurrence,
        data.selectCosted_erase target occurrence]

theorem computed_rrr_block_kernel_profile
    {ambientLength : Nat} {bits : List Bool} {wordSize : Nat}
    (data :
      FixedWeightComputedRRRBlockData ambientLength bits wordSize) :
    data.KernelProfile := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  refine
    ⟨rfl,
      by
        change data.payload.length = fixedWeightPayloadBudget bits
        exact data.payload_length,
      by
        change data.payload.length = fixedWeightPayloadBudget bits + 0
        simp,
      data.packedStore.erases,
      hpacked,
      data.codeWidth_le_wordSize,
      data.blockWidth_le_wordSize,
      data.wordSize_le_ambient,
      data.readCodeCosted_cost,
      data.readCodeCosted_erase,
      data.decodedWordCosted_cost,
      data.decodedWordCosted_erase,
      (fun hmem => data.packedStore.word_length_le_of_mem hmem),
      ?_,
      ?_,
      ?_⟩
  · intro i
    exact
      ⟨by
        change (data.accessCosted i).cost <=
          fixedWeightComputedRRRQueryCost bits
        rw [data.accessCosted_cost i]
        unfold fixedWeightComputedRRRQueryCost
        omega,
        data.accessCosted_erase i⟩
  · intro target pos
    exact
      ⟨by
        change (data.rankCosted target pos).cost =
          fixedWeightComputedRRRQueryCost bits
        exact data.rankCosted_cost target pos,
        data.rankCosted_erase target pos⟩
  · intro target occurrence
    exact
      ⟨by
        change (data.selectCosted target occurrence).cost =
          fixedWeightComputedRRRQueryCost bits
        exact data.selectCosted_cost target occurrence,
        data.selectCosted_erase target occurrence⟩

end FixedWeightComputedRRRBlockData

/--
Access routing metadata for the ambient computed-RRR predecessor.

The metadata read list is charged through the ambient auxiliary store. The
semantic fields identify the routed block/offset; a later fully built FID
construction should derive these fields from concrete payload tables.
-/
structure FixedWeightAmbientComputedRRRAccessRoute
    (bits : List Bool) (blocks : List (List Bool)) (i : Nat) where
  blockIndex : Nat
  block : List Bool
  block_get : blocks[blockIndex]? = some block
  offset : Nat
  metadataReads : List Nat
  access_exact : block[offset]? = bits[i]?

/-- Rank routing metadata for the ambient computed-RRR predecessor. -/
structure FixedWeightAmbientComputedRRRRankRoute
    (bits : List Bool) (blocks : List (List Bool))
    (target : Bool) (pos : Nat) where
  blockIndex : Nat
  block : List Bool
  block_get : blocks[blockIndex]? = some block
  localLimit : Nat
  baseRank : Nat
  metadataReads : List Nat
  rank_exact :
    baseRank + Succinct.rankPrefix target block localLimit =
      Succinct.rankPrefix target bits pos

/-- Select routing metadata for the ambient computed-RRR predecessor. -/
structure FixedWeightAmbientComputedRRRSelectRoute
    (bits : List Bool) (blocks : List (List Bool))
    (target : Bool) (occurrence : Nat) where
  blockIndex : Nat
  block : List Bool
  block_get : blocks[blockIndex]? = some block
  localOccurrence : Nat
  blockStart : Nat
  metadataReads : List Nat
  select_exact :
    (Succinct.select target block localOccurrence).map
        (fun offset => blockStart + offset) =
      Succinct.select target bits occurrence

/--
Ambient/global block-composition data whose local block backend is the
computed packed-code-only fixed-weight/RRR kernel.

The primary payload is still `fixedWeightBlockCodePayload blocks`. Routing and
class metadata are charged by `metadataReads` through the auxiliary store; the
local block decoder is governed by the uniform `localQueryCost` bound. This is
the concrete predecessor needed before proving that a particular routing/class
table construction has `o(n)` payload and truly constant local decode cost.
-/
structure FixedWeightAmbientComputedRRRBlockData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
  blockSize : Nat
  blockSize_pos : 0 < blockSize
  blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits
  block_length_le :
    forall {block : List Bool}, List.Mem block blocks ->
      block.length <= blockSize
  blockSize_le_wordSize : blockSize <= wordSize
  block_code_width_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightPayloadBudget block <= wordSize
  codeStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload blocks) wordSize
  codeStore_aligned :
    codeStore.store.words.toList = fixedWeightBlockCodeWords blocks
  auxPayload : List Bool
  auxStore :
    SuccinctSpace.BoundedPayloadWordStore auxPayload wordSize
  aux_length_eq : auxPayload.length = overhead
  accessRoute :
    forall i,
      FixedWeightAmbientComputedRRRAccessRoute bits blocks i
  rankRoute :
    forall target pos,
      FixedWeightAmbientComputedRRRRankRoute bits blocks target pos
  selectRoute :
    forall target occurrence,
      FixedWeightAmbientComputedRRRSelectRoute
        bits blocks target occurrence
  access_metadata_reads_le :
    forall i, (accessRoute i).metadataReads.length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankRoute target pos).metadataReads.length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads.length <= routeCost
  local_query_cost_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost
  route_plus_local_le : routeCost + localQueryCost <= queryCost

namespace FixedWeightAmbientComputedRRRBlockData

def localBlockData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    FixedWeightComputedRRRBlockData bits.length block wordSize where
  wordSize_pos := data.wordSize_pos
  wordSize_le_ambient := data.wordSize_le_ambient
  codeWidth_le_wordSize :=
    data.block_code_width_le (List.mem_of_getElem? hblock)
  blockWidth_le_wordSize :=
    Nat.le_trans
      (data.block_length_le (List.mem_of_getElem? hblock))
      data.blockSize_le_wordSize

theorem code_read_values_singleton
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    boundedPayloadWordReadValues data.codeStore [blockIndex] =
      [some (fixedWeightPackedPayload block)] := by
  have hget :
      data.codeStore.store.words[blockIndex]? =
        some (fixedWeightPackedPayload block) :=
    fixedWeightAmbientBlockCodeStore_get?_of_aligned
      data.codeStore_aligned hblock
  simp [boundedPayloadWordReadValues, hget]

def accessEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) (codeWords auxWords : List (Option (List Bool))) :
    Costed (Option Bool) :=
  let route := data.accessRoute i
  ((data.localBlockData route.block_get).toDependentAuxiliaryData).accessEvalCosted
    route.offset codeWords auxWords

def rankEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat)
    (codeWords auxWords : List (Option (List Bool))) :
    Costed Nat :=
  let route := data.rankRoute target pos
  Costed.map (fun localRank => route.baseRank + localRank)
    (((data.localBlockData route.block_get).toDependentAuxiliaryData).rankEvalCosted
      target route.localLimit codeWords auxWords)

def selectEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat)
    (codeWords auxWords : List (Option (List Bool))) :
    Costed (Option Nat) :=
  let route := data.selectRoute target occurrence
  Costed.map (fun local? =>
      local?.map (fun offset => route.blockStart + offset))
    (((data.localBlockData route.block_get).toDependentAuxiliaryData).selectEvalCosted
      target route.localOccurrence codeWords auxWords)

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost := by
  refine
    { wordSize_pos := data.wordSize_pos
      wordSize_le_ambient := data.wordSize_le_ambient
      blockSize := data.blockSize
      blockSize_pos := data.blockSize_pos
      blocks_flatten := data.blocks_flatten
      block_length_le := data.block_length_le
      blockSize_le_wordSize := data.blockSize_le_wordSize
      block_code_width_le := data.block_code_width_le
      codeStore := data.codeStore
      auxPayload := data.auxPayload
      auxStore := data.auxStore
      aux_length_eq := data.aux_length_eq
      accessCodeReads := fun i => [(data.accessRoute i).blockIndex]
      accessAuxReads := fun i _ => (data.accessRoute i).metadataReads
      rankCodeReads := fun target pos =>
        [(data.rankRoute target pos).blockIndex]
      rankAuxReads := fun target pos _ =>
        (data.rankRoute target pos).metadataReads
      selectCodeReads := fun target occurrence =>
        [(data.selectRoute target occurrence).blockIndex]
      selectAuxReads := fun target occurrence _ =>
        (data.selectRoute target occurrence).metadataReads
      accessEvalCosted := data.accessEvalCosted
      rankEvalCosted := data.rankEvalCosted
      selectEvalCosted := data.selectEvalCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · intro i
    let route := data.accessRoute i
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hroute := data.access_metadata_reads_le i
    have hlocal := data.local_query_cost_le hmem
    have htotal := data.route_plus_local_le
    simp [accessEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      fixedWeightComputedRRRDecodeFromReadValuesCosted,
      fixedWeightComputedRRRQueryCost] at *
    omega
  · intro target pos
    let route := data.rankRoute target pos
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hroute := data.rank_metadata_reads_le target pos
    have hlocal := data.local_query_cost_le hmem
    have htotal := data.route_plus_local_le
    simp [rankEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      fixedWeightComputedRRRDecodeFromReadValuesCosted,
      fixedWeightComputedRRRQueryCost] at *
    omega
  · intro target occurrence
    let route := data.selectRoute target occurrence
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hroute := data.select_metadata_reads_le target occurrence
    have hlocal := data.local_query_cost_le hmem
    have htotal := data.route_plus_local_le
    simp [selectEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      fixedWeightComputedRRRDecodeFromReadValuesCosted,
      fixedWeightComputedRRRQueryCost] at *
    omega
  · intro i
    let route := data.accessRoute i
    have hread := data.code_read_values_singleton route.block_get
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
        route.block
    simp [accessEvalCosted, route,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData, hread,
      hdecode, route.access_exact]
  · intro target pos
    let route := data.rankRoute target pos
    have hread := data.code_read_values_singleton route.block_get
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
        route.block
    have hrun :=
      Succinct.rankBoolWordPrefix_toCosted_run
        target route.block route.localLimit
    simp only [rankEvalCosted, Costed.erase_map,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      Costed.erase_bind]
    change
      route.baseRank +
          (RAM.rankBoolWordPrefix target
              (fixedWeightComputedRRRDecodeFromReadValuesCosted
                route.block
                (boundedPayloadWordReadValues data.codeStore
                  [route.blockIndex])).erase
              route.localLimit).toCosted.erase =
        Succinct.rankPrefix target bits pos
    rw [hread]
    rw [hdecode]
    change
      route.baseRank +
          (RAM.rankBoolWordPrefix target route.block route.localLimit).toCosted.value =
        Succinct.rankPrefix target bits pos
    have hram :
        (RAM.rankBoolWordPrefix target route.block route.localLimit).toCosted.value =
          Succinct.rankPrefix target route.block route.localLimit := by
      simpa [Costed.run] using congrArg Prod.fst hrun
    rw [hram]
    exact route.rank_exact
  · intro target occurrence
    let route := data.selectRoute target occurrence
    have hread := data.code_read_values_singleton route.block_get
    have hdecode :=
      fixedWeightComputedRRRDecodeFromReadValuesCosted_erase_singleton
        route.block
    have hrun :=
      Succinct.selectBoolWord_toCosted_run
        target route.block route.localOccurrence
    simp only [selectEvalCosted, Costed.erase_map,
      FixedWeightComputedRRRBlockData.toDependentAuxiliaryData,
      Costed.erase_bind]
    change
      ((RAM.selectBoolWord target
              (fixedWeightComputedRRRDecodeFromReadValuesCosted
                route.block
                (boundedPayloadWordReadValues data.codeStore
                  [route.blockIndex])).erase
              route.localOccurrence).toCosted.erase).map
          (fun offset => route.blockStart + offset) =
        Succinct.select target bits occurrence
    rw [hread]
    rw [hdecode]
    change
      ((RAM.selectBoolWord target route.block route.localOccurrence).toCosted.value).map
          (fun offset => route.blockStart + offset) =
        Succinct.select target bits occurrence
    have hselect :
        (RAM.selectBoolWord target route.block route.localOccurrence).toCosted.value =
          Succinct.select target route.block route.localOccurrence := by
      simpa [Costed.run] using congrArg Prod.fst hrun
    rw [hselect]
    exact route.select_exact

def CompositionProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  (data.toAmbientBlockCompositionData).DirectoryProfile /\
    data.codeStore.store.words.toList = fixedWeightBlockCodeWords blocks /\
    (forall i,
      let route := data.accessRoute i
      boundedPayloadWordReadValues data.codeStore [route.blockIndex] =
          [some (fixedWeightPackedPayload route.block)] /\
        ((data.localBlockData route.block_get).toDependentAuxiliaryData).DirectoryProfile /\
        route.metadataReads.length <= routeCost) /\
    (forall target pos,
      let route := data.rankRoute target pos
      boundedPayloadWordReadValues data.codeStore [route.blockIndex] =
          [some (fixedWeightPackedPayload route.block)] /\
        ((data.localBlockData route.block_get).toDependentAuxiliaryData).DirectoryProfile /\
        route.metadataReads.length <= routeCost) /\
    (forall target occurrence,
      let route := data.selectRoute target occurrence
      boundedPayloadWordReadValues data.codeStore [route.blockIndex] =
          [some (fixedWeightPackedPayload route.block)] /\
        ((data.localBlockData route.block_get).toDependentAuxiliaryData).DirectoryProfile /\
        route.metadataReads.length <= routeCost) /\
    (forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost) /\
    routeCost + localQueryCost <= queryCost

theorem computed_rrr_block_composition_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRBlockData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.CompositionProfile := by
  refine
    ⟨data.toAmbientBlockCompositionData.directory_profile,
      data.codeStore_aligned,
      ?_,
      ?_,
      ?_,
      data.local_query_cost_le,
      data.route_plus_local_le⟩
  · intro i
    exact
      ⟨data.code_read_values_singleton (data.accessRoute i).block_get,
        FixedWeightComputedRRRBlockData.dependent_auxiliary_data_profile
          (data.localBlockData (data.accessRoute i).block_get),
        data.access_metadata_reads_le i⟩
  · intro target pos
    exact
      ⟨data.code_read_values_singleton
          (data.rankRoute target pos).block_get,
        FixedWeightComputedRRRBlockData.dependent_auxiliary_data_profile
          (data.localBlockData (data.rankRoute target pos).block_get),
        data.rank_metadata_reads_le target pos⟩
  · intro target occurrence
    exact
      ⟨data.code_read_values_singleton
          (data.selectRoute target occurrence).block_get,
        FixedWeightComputedRRRBlockData.dependent_auxiliary_data_profile
          (data.localBlockData
            (data.selectRoute target occurrence).block_get),
        data.select_metadata_reads_le target occurrence⟩

end FixedWeightAmbientComputedRRRBlockData

/--
Payload-backed route/class metadata tables for ambient computed-RRR blocks.

This layer owns the auxiliary route payload and bounded route store, then
instantiates `FixedWeightAmbientComputedRRRBlockData`. The route records still
carry the semantic facts needed to identify the chosen block and local query;
the important extra discipline here is that every such route is backed by a
counted metadata read schedule over this concrete payload store.
-/
structure FixedWeightAmbientComputedRRRRouteTableData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
  blockSize : Nat
  blockSize_pos : 0 < blockSize
  blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits
  block_length_le :
    forall {block : List Bool}, List.Mem block blocks ->
      block.length <= blockSize
  blockSize_le_wordSize : blockSize <= wordSize
  block_code_width_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightPayloadBudget block <= wordSize
  codeStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload blocks) wordSize
  codeStore_aligned :
    codeStore.store.words.toList = fixedWeightBlockCodeWords blocks
  routePayload : List Bool
  routeStore :
    SuccinctSpace.BoundedPayloadWordStore routePayload wordSize
  routePayload_length_eq : routePayload.length = overhead
  accessRoute :
    forall i,
      FixedWeightAmbientComputedRRRAccessRoute bits blocks i
  rankRoute :
    forall target pos,
      FixedWeightAmbientComputedRRRRankRoute bits blocks target pos
  selectRoute :
    forall target occurrence,
      FixedWeightAmbientComputedRRRSelectRoute
        bits blocks target occurrence
  access_metadata_reads_le :
    forall i, (accessRoute i).metadataReads.length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankRoute target pos).metadataReads.length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads.length <= routeCost
  local_query_cost_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost
  route_plus_local_le : routeCost + localQueryCost <= queryCost

namespace FixedWeightAmbientComputedRRRRouteTableData

def toComputedRRRBlockData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRBlockData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  wordSize_pos := data.wordSize_pos
  wordSize_le_ambient := data.wordSize_le_ambient
  blockSize := data.blockSize
  blockSize_pos := data.blockSize_pos
  blocks_flatten := data.blocks_flatten
  block_length_le := data.block_length_le
  blockSize_le_wordSize := data.blockSize_le_wordSize
  block_code_width_le := data.block_code_width_le
  codeStore := data.codeStore
  codeStore_aligned := data.codeStore_aligned
  auxPayload := data.routePayload
  auxStore := data.routeStore
  aux_length_eq := data.routePayload_length_eq
  accessRoute := data.accessRoute
  rankRoute := data.rankRoute
  selectRoute := data.selectRoute
  access_metadata_reads_le := data.access_metadata_reads_le
  rank_metadata_reads_le := data.rank_metadata_reads_le
  select_metadata_reads_le := data.select_metadata_reads_le
  local_query_cost_le := data.local_query_cost_le
  route_plus_local_le := data.route_plus_local_le

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toComputedRRRBlockData.toAmbientBlockCompositionData

def accessMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.accessRoute i).metadataReads

def rankMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.rankRoute target pos).metadataReads

def selectMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.selectRoute target occurrence).metadataReads

def RouteTableReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  (forall i,
    (data.accessMetadataReadsCosted i).cost <= routeCost /\
      (data.accessMetadataReadsCosted i).erase =
        boundedPayloadWordReadValues data.routeStore
          (data.accessRoute i).metadataReads) /\
    (forall target pos,
      (data.rankMetadataReadsCosted target pos).cost <= routeCost /\
        (data.rankMetadataReadsCosted target pos).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.rankRoute target pos).metadataReads) /\
    (forall target occurrence,
      (data.selectMetadataReadsCosted target occurrence).cost <=
          routeCost /\
        (data.selectMetadataReadsCosted target occurrence).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.selectRoute target occurrence).metadataReads)

theorem route_table_read_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.RouteTableReadProfile := by
  exact
    ⟨(fun i => by
        constructor
        · dsimp [accessMetadataReadsCosted]
          simpa using data.access_metadata_reads_le i
        · simp [accessMetadataReadsCosted]),
      (fun target pos => by
        constructor
        · dsimp [rankMetadataReadsCosted]
          simpa using data.rank_metadata_reads_le target pos
        · simp [rankMetadataReadsCosted]),
      (fun target occurrence => by
        constructor
        · dsimp [selectMetadataReadsCosted]
          simpa using data.select_metadata_reads_le target occurrence
        · simp [selectMetadataReadsCosted])⟩

def RouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toComputedRRRBlockData.CompositionProfile /\
    data.RouteTableReadProfile /\
    data.routePayload.length = overhead /\
    SuccinctSpace.flattenPayloadWords data.routeStore.store.words.toList =
      data.routePayload /\
    (forall {word : List Bool},
      List.Mem word data.routeStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      let route := data.accessRoute i
      (boundedPayloadWordReadValues
          data.routeStore route.metadataReads).length <= routeCost) /\
    (forall target pos,
      let route := data.rankRoute target pos
      (boundedPayloadWordReadValues
          data.routeStore route.metadataReads).length <= routeCost) /\
    (forall target occurrence,
      let route := data.selectRoute target occurrence
      (boundedPayloadWordReadValues
          data.routeStore route.metadataReads).length <= routeCost) /\
    (forall i, (data.accessRoute i).metadataReads.length <= routeCost) /\
    (forall target pos,
      (data.rankRoute target pos).metadataReads.length <= routeCost) /\
    (forall target occurrence,
      (data.selectRoute target occurrence).metadataReads.length <=
        routeCost) /\
    (forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost) /\
    routeCost + localQueryCost <= queryCost

theorem route_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.RouteTableProfile := by
  exact
    ⟨data.toComputedRRRBlockData.computed_rrr_block_composition_profile,
      data.route_table_read_profile,
      data.routePayload_length_eq,
      data.routeStore.erases,
      (fun hmem => data.routeStore.word_length_le_of_mem hmem),
      (fun i => by
        dsimp [boundedPayloadWordReadValues]
        simpa using data.access_metadata_reads_le i),
      (fun target pos => by
        dsimp [boundedPayloadWordReadValues]
        simpa using data.rank_metadata_reads_le target pos),
      (fun target occurrence => by
        dsimp [boundedPayloadWordReadValues]
        simpa using data.select_metadata_reads_le target occurrence),
      data.access_metadata_reads_le,
      data.rank_metadata_reads_le,
      data.select_metadata_reads_le,
      data.local_query_cost_le,
      data.route_plus_local_le⟩

end FixedWeightAmbientComputedRRRRouteTableData

/--
Family of ambient computed-RRR route/class metadata tables.

The family-level overhead is the ambient `o(n)` envelope; each pointwise
component stores the concrete route/class metadata payload in a bounded store
and consumes it through `FixedWeightAmbientComputedRRRBlockData`.
-/
structure FixedWeightAmbientComputedRRRRouteTableFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRRouteTableData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRRouteTableFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRRouteTableData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toAmbientBlockCompositionData

def toAmbientBlockCompositionFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionFamily slots queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := family.directory bits

theorem route_table_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.RouteTableProfile /\
          data.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    have hprofile := data.route_table_profile
    exact
      ⟨hprofile,
        data.routePayload_length_eq,
        (family.directory bits).payload_length,
        data.blocks_flatten,
        (fun i => (family.directory bits).accessCosted_cost_le i),
        (fun target pos =>
          (family.directory bits).rankCosted_cost_le target pos),
        (fun target occurrence =>
          (family.directory bits).selectCosted_cost_le
            target occurrence)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        let routeData := family.componentData bits
        let data := family.directory bits
        routeData.RouteTableProfile /\
          data.DirectoryProfile /\
          data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead slots primaryOverhead bits.length /\
          data.auxPayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word data.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word data.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (data.accessCosted i).cost <= queryCost /\
              (data.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (data.rankCosted target pos).cost <= queryCost /\
              (data.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (data.selectCosted target occurrence).cost <= queryCost /\
              (data.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  have hcompressed :=
    FixedWeightAmbientBlockCompositionFamily.word_bounded_compressed_profile_of_primary_budget
      family.toAmbientBlockCompositionFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead] using hcompressed.1
  · intro bits
    constructor
    · exact (family.componentData bits).route_table_profile
    · simpa [directory, toAmbientBlockCompositionFamily, componentData,
        compressedOverhead] using hcompressed.2 bits

end FixedWeightAmbientComputedRRRRouteTableFamily

/--
Decoded access route fields recovered from charged route metadata.

The semantic block witness remains in
`FixedWeightAmbientComputedRRRAccessRoute`; this record names the runtime route
fields that a concrete table decoder must produce from payload reads.
-/
structure FixedWeightAmbientComputedRRRDecodedAccessRoute where
  blockIndex : Nat
  offset : Nat

/-- Decoded rank route fields recovered from charged route metadata. -/
structure FixedWeightAmbientComputedRRRDecodedRankRoute where
  blockIndex : Nat
  localLimit : Nat
  baseRank : Nat

/-- Decoded select route fields recovered from charged route metadata. -/
structure FixedWeightAmbientComputedRRRDecodedSelectRoute where
  blockIndex : Nat
  localOccurrence : Nat
  blockStart : Nat

def fixedWeightAmbientComputedRRRAccessRouteDecoded
    {bits : List Bool} {blocks : List (List Bool)} {i : Nat}
    (route : FixedWeightAmbientComputedRRRAccessRoute bits blocks i) :
    FixedWeightAmbientComputedRRRDecodedAccessRoute where
  blockIndex := route.blockIndex
  offset := route.offset

def fixedWeightAmbientComputedRRRRankRouteDecoded
    {bits : List Bool} {blocks : List (List Bool)}
    {target : Bool} {pos : Nat}
    (route :
      FixedWeightAmbientComputedRRRRankRoute bits blocks target pos) :
    FixedWeightAmbientComputedRRRDecodedRankRoute where
  blockIndex := route.blockIndex
  localLimit := route.localLimit
  baseRank := route.baseRank

def fixedWeightAmbientComputedRRRSelectRouteDecoded
    {bits : List Bool} {blocks : List (List Bool)}
    {target : Bool} {occurrence : Nat}
    (route :
      FixedWeightAmbientComputedRRRSelectRoute
        bits blocks target occurrence) :
    FixedWeightAmbientComputedRRRDecodedSelectRoute where
  blockIndex := route.blockIndex
  localOccurrence := route.localOccurrence
  blockStart := route.blockStart

/--
Route/class table data whose runtime route fields are decoded from charged
metadata reads.

This strengthens `FixedWeightAmbientComputedRRRRouteTableData` without changing
its ambient consumer: the read schedules are explicit functions of the query,
the charged route-store words are read through bounded-store kernels, and the
decoder exactness fields connect those read values to the block index and
local route parameters consumed by the ambient computed-RRR evaluator.
-/
structure FixedWeightAmbientComputedRRRDecodedRouteTableData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
  blockSize : Nat
  blockSize_pos : 0 < blockSize
  blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits
  block_length_le :
    forall {block : List Bool}, List.Mem block blocks ->
      block.length <= blockSize
  blockSize_le_wordSize : blockSize <= wordSize
  block_code_width_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightPayloadBudget block <= wordSize
  codeStore :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockCodePayload blocks) wordSize
  codeStore_aligned :
    codeStore.store.words.toList = fixedWeightBlockCodeWords blocks
  routePayload : List Bool
  routeStore :
    SuccinctSpace.BoundedPayloadWordStore routePayload wordSize
  routePayload_length_eq : routePayload.length = overhead
  accessMetadataReads : Nat -> List Nat
  rankMetadataReads : Bool -> Nat -> List Nat
  selectMetadataReads : Bool -> Nat -> List Nat
  accessRouteDecoder :
    Nat -> List (Option (List Bool)) ->
      FixedWeightAmbientComputedRRRDecodedAccessRoute
  rankRouteDecoder :
    Bool -> Nat -> List (Option (List Bool)) ->
      FixedWeightAmbientComputedRRRDecodedRankRoute
  selectRouteDecoder :
    Bool -> Nat -> List (Option (List Bool)) ->
      FixedWeightAmbientComputedRRRDecodedSelectRoute
  accessRoute :
    forall i,
      FixedWeightAmbientComputedRRRAccessRoute bits blocks i
  rankRoute :
    forall target pos,
      FixedWeightAmbientComputedRRRRankRoute bits blocks target pos
  selectRoute :
    forall target occurrence,
      FixedWeightAmbientComputedRRRSelectRoute
        bits blocks target occurrence
  access_metadata_reads_le :
    forall i, (accessMetadataReads i).length <= routeCost
  rank_metadata_reads_le :
    forall target pos,
      (rankMetadataReads target pos).length <= routeCost
  select_metadata_reads_le :
    forall target occurrence,
      (selectMetadataReads target occurrence).length <= routeCost
  access_route_metadata_reads_eq :
    forall i, (accessRoute i).metadataReads = accessMetadataReads i
  rank_route_metadata_reads_eq :
    forall target pos,
      (rankRoute target pos).metadataReads = rankMetadataReads target pos
  select_route_metadata_reads_eq :
    forall target occurrence,
      (selectRoute target occurrence).metadataReads =
        selectMetadataReads target occurrence
  access_route_decode_exact :
    forall i,
      accessRouteDecoder i
          (boundedPayloadWordReadValues routeStore
            (accessMetadataReads i)) =
        fixedWeightAmbientComputedRRRAccessRouteDecoded (accessRoute i)
  rank_route_decode_exact :
    forall target pos,
      rankRouteDecoder target pos
          (boundedPayloadWordReadValues routeStore
            (rankMetadataReads target pos)) =
        fixedWeightAmbientComputedRRRRankRouteDecoded
          (rankRoute target pos)
  select_route_decode_exact :
    forall target occurrence,
      selectRouteDecoder target occurrence
          (boundedPayloadWordReadValues routeStore
            (selectMetadataReads target occurrence)) =
        fixedWeightAmbientComputedRRRSelectRouteDecoded
          (selectRoute target occurrence)
  local_query_cost_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost
  route_plus_local_le : routeCost + localQueryCost <= queryCost

namespace FixedWeightAmbientComputedRRRDecodedRouteTableData

def toRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  wordSize_pos := data.wordSize_pos
  wordSize_le_ambient := data.wordSize_le_ambient
  blockSize := data.blockSize
  blockSize_pos := data.blockSize_pos
  blocks_flatten := data.blocks_flatten
  block_length_le := data.block_length_le
  blockSize_le_wordSize := data.blockSize_le_wordSize
  block_code_width_le := data.block_code_width_le
  codeStore := data.codeStore
  codeStore_aligned := data.codeStore_aligned
  routePayload := data.routePayload
  routeStore := data.routeStore
  routePayload_length_eq := data.routePayload_length_eq
  accessRoute := data.accessRoute
  rankRoute := data.rankRoute
  selectRoute := data.selectRoute
  access_metadata_reads_le := by
    intro i
    rw [data.access_route_metadata_reads_eq i]
    exact data.access_metadata_reads_le i
  rank_metadata_reads_le := by
    intro target pos
    rw [data.rank_route_metadata_reads_eq target pos]
    exact data.rank_metadata_reads_le target pos
  select_metadata_reads_le := by
    intro target occurrence
    rw [data.select_route_metadata_reads_eq target occurrence]
    exact data.select_metadata_reads_le target occurrence
  local_query_cost_le := data.local_query_cost_le
  route_plus_local_le := data.route_plus_local_le

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toRouteTableData.toAmbientBlockCompositionData

def accessMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.accessMetadataReads i)

def rankMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.rankMetadataReads target pos)

def selectMetadataReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.routeStore
    (data.selectMetadataReads target occurrence)

def DecodedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toRouteTableData.RouteTableProfile /\
    data.routePayload.length = overhead /\
    SuccinctSpace.flattenPayloadWords data.routeStore.store.words.toList =
      data.routePayload /\
    (forall {word : List Bool},
      List.Mem word data.routeStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall i,
      (data.accessMetadataReadsCosted i).cost <= routeCost /\
        (data.accessMetadataReadsCosted i).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.accessMetadataReads i) /\
        data.accessRouteDecoder i
            (data.accessMetadataReadsCosted i).erase =
          fixedWeightAmbientComputedRRRAccessRouteDecoded
            (data.accessRoute i) /\
        (data.accessRoute i).metadataReads =
          data.accessMetadataReads i) /\
    (forall target pos,
      (data.rankMetadataReadsCosted target pos).cost <= routeCost /\
        (data.rankMetadataReadsCosted target pos).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.rankMetadataReads target pos) /\
        data.rankRouteDecoder target pos
            (data.rankMetadataReadsCosted target pos).erase =
          fixedWeightAmbientComputedRRRRankRouteDecoded
            (data.rankRoute target pos) /\
        (data.rankRoute target pos).metadataReads =
          data.rankMetadataReads target pos) /\
    (forall target occurrence,
      (data.selectMetadataReadsCosted target occurrence).cost <=
          routeCost /\
        (data.selectMetadataReadsCosted target occurrence).erase =
          boundedPayloadWordReadValues data.routeStore
            (data.selectMetadataReads target occurrence) /\
        data.selectRouteDecoder target occurrence
            (data.selectMetadataReadsCosted target occurrence).erase =
          fixedWeightAmbientComputedRRRSelectRouteDecoded
            (data.selectRoute target occurrence) /\
        (data.selectRoute target occurrence).metadataReads =
          data.selectMetadataReads target occurrence) /\
    (forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRQueryCost block <= localQueryCost) /\
    routeCost + localQueryCost <= queryCost

def DecodedMetadataReadProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  (forall i,
    (Costed.map (data.accessRouteDecoder i)
        (data.accessMetadataReadsCosted i)).cost <= routeCost /\
      (Costed.map (data.accessRouteDecoder i)
        (data.accessMetadataReadsCosted i)).erase =
        fixedWeightAmbientComputedRRRAccessRouteDecoded
          (data.accessRoute i)) /\
    (forall target pos,
      (Costed.map (data.rankRouteDecoder target pos)
          (data.rankMetadataReadsCosted target pos)).cost <=
          routeCost /\
        (Costed.map (data.rankRouteDecoder target pos)
          (data.rankMetadataReadsCosted target pos)).erase =
          fixedWeightAmbientComputedRRRRankRouteDecoded
            (data.rankRoute target pos)) /\
    (forall target occurrence,
      (Costed.map (data.selectRouteDecoder target occurrence)
          (data.selectMetadataReadsCosted target occurrence)).cost <=
          routeCost /\
        (Costed.map (data.selectRouteDecoder target occurrence)
          (data.selectMetadataReadsCosted target occurrence)).erase =
          fixedWeightAmbientComputedRRRSelectRouteDecoded
            (data.selectRoute target occurrence))

theorem decoded_metadata_read_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.DecodedMetadataReadProfile := by
  exact
    ⟨(fun i => by
        constructor
        · dsimp [accessMetadataReadsCosted]
          simpa using data.access_metadata_reads_le i
        · simp [accessMetadataReadsCosted,
            data.access_route_decode_exact i]),
      (fun target pos => by
        constructor
        · dsimp [rankMetadataReadsCosted]
          simpa using data.rank_metadata_reads_le target pos
        · simp [rankMetadataReadsCosted,
            data.rank_route_decode_exact target pos]),
      (fun target occurrence => by
        constructor
        · dsimp [selectMetadataReadsCosted]
          simpa using data.select_metadata_reads_le target occurrence
        · simp [selectMetadataReadsCosted,
            data.select_route_decode_exact target occurrence])⟩

theorem decoded_route_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.DecodedRouteTableProfile := by
  exact
    ⟨data.toRouteTableData.route_table_profile,
      data.routePayload_length_eq,
      data.routeStore.erases,
      (fun hmem => data.routeStore.word_length_le_of_mem hmem),
      (fun i => by
        exact
          ⟨by
            dsimp [accessMetadataReadsCosted]
            simpa using data.access_metadata_reads_le i,
            by simp [accessMetadataReadsCosted],
            by
              simpa [accessMetadataReadsCosted] using
                data.access_route_decode_exact i,
            data.access_route_metadata_reads_eq i⟩),
      (fun target pos => by
        exact
          ⟨by
            dsimp [rankMetadataReadsCosted]
            simpa using data.rank_metadata_reads_le target pos,
            by simp [rankMetadataReadsCosted],
            by
              simpa [rankMetadataReadsCosted] using
                data.rank_route_decode_exact target pos,
            data.rank_route_metadata_reads_eq target pos⟩),
      (fun target occurrence => by
        exact
          ⟨by
            dsimp [selectMetadataReadsCosted]
            simpa using data.select_metadata_reads_le
              target occurrence,
            by simp [selectMetadataReadsCosted],
            by
              simpa [selectMetadataReadsCosted] using
                data.select_route_decode_exact target occurrence,
            data.select_route_metadata_reads_eq target occurrence⟩),
      data.local_query_cost_le,
      data.route_plus_local_le⟩

end FixedWeightAmbientComputedRRRDecodedRouteTableData

/--
Family of decoded route/class metadata tables for ambient computed-RRR blocks.

This is the stricter route-table predecessor: it retains the same ambient
block-composition directory but additionally proves that route fields are
outputs of fixed decoders over charged metadata words.
-/
structure FixedWeightAmbientComputedRRRDecodedRouteTableFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRDecodedRouteTableData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRDecodedRouteTableFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRDecodedRouteTableData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toAmbientBlockCompositionData

def toAmbientBlockCompositionFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionFamily slots queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := family.directory bits

theorem decoded_route_table_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.DecodedRouteTableProfile /\
          data.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    exact
      ⟨data.decoded_route_table_profile,
        data.routePayload_length_eq,
        (family.directory bits).payload_length,
        data.blocks_flatten,
        (fun i => (family.directory bits).accessCosted_cost_le i),
        (fun target pos =>
          (family.directory bits).rankCosted_cost_le target pos),
        (fun target occurrence =>
          (family.directory bits).selectCosted_cost_le
            target occurrence)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        (family.componentData bits).DecodedRouteTableProfile /\
          let data := family.directory bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                compressedOverhead slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  have hcompressed :=
    FixedWeightAmbientBlockCompositionFamily.word_bounded_compressed_profile_of_primary_budget
      family.toAmbientBlockCompositionFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead] using hcompressed.1
  · intro bits
    constructor
    · exact (family.componentData bits).decoded_route_table_profile
    · simpa [directory, toAmbientBlockCompositionFamily, componentData,
        compressedOverhead] using hcompressed.2 bits

end FixedWeightAmbientComputedRRRDecodedRouteTableFamily

/-- Decode one fixed-width route metadata word read. -/
def fixedWeightRouteNatFromReadValue : Option (List Bool) -> Nat
  | some word => SuccinctSpace.bitsToNatLE word
  | none => 0

/-- Access-route decoder over two charged metadata words. -/
def fixedWeightPackedRouteAccessDecoder
    (readWords : List (Option (List Bool))) :
    FixedWeightAmbientComputedRRRDecodedAccessRoute :=
  match readWords with
  | block? :: offset? :: _ =>
      { blockIndex := fixedWeightRouteNatFromReadValue block?
        offset := fixedWeightRouteNatFromReadValue offset? }
  | _ => { blockIndex := 0, offset := 0 }

/-- Rank-route decoder over three charged metadata words. -/
def fixedWeightPackedRouteRankDecoder
    (readWords : List (Option (List Bool))) :
    FixedWeightAmbientComputedRRRDecodedRankRoute :=
  match readWords with
  | block? :: localLimit? :: baseRank? :: _ =>
      { blockIndex := fixedWeightRouteNatFromReadValue block?
        localLimit := fixedWeightRouteNatFromReadValue localLimit?
        baseRank := fixedWeightRouteNatFromReadValue baseRank? }
  | _ =>
      { blockIndex := 0, localLimit := 0, baseRank := 0 }

/-- Select-route decoder over three charged metadata words. -/
def fixedWeightPackedRouteSelectDecoder
    (readWords : List (Option (List Bool))) :
    FixedWeightAmbientComputedRRRDecodedSelectRoute :=
  match readWords with
  | block? :: localOccurrence? :: blockStart? :: _ =>
      { blockIndex := fixedWeightRouteNatFromReadValue block?
        localOccurrence :=
          fixedWeightRouteNatFromReadValue localOccurrence?
        blockStart := fixedWeightRouteNatFromReadValue blockStart? }
  | _ =>
      { blockIndex := 0, localOccurrence := 0, blockStart := 0 }

@[simp] theorem fixedWeightRouteNatFromReadValue_encoded
    {fieldWidth value : Nat} (hvalue : value < 2 ^ fieldWidth) :
    fixedWeightRouteNatFromReadValue
        (some (SuccinctSpace.natToBitsLE fieldWidth value)) =
      value := by
  simp [fixedWeightRouteNatFromReadValue,
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt hvalue]

/--
Packed fixed-width route metadata words for ambient computed-RRR blocks.

This is a concrete route/class metadata envelope: the route-store words read
by each query are fixed-width encodings of the route fields, and the decoder is
fixed code over the charged read values. It still relies on the semantic route
records for correctness of the chosen route, but not for recovering the route
fields from metadata reads.
-/
structure FixedWeightAmbientComputedRRRPackedRouteTableData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  routeData :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost
  fieldWidth : Nat
  fieldWidth_le_wordSize : fieldWidth <= wordSize
  accessBlockSlot : Nat -> Nat
  accessOffsetSlot : Nat -> Nat
  rankBlockSlot : Bool -> Nat -> Nat
  rankLocalLimitSlot : Bool -> Nat -> Nat
  rankBaseRankSlot : Bool -> Nat -> Nat
  selectBlockSlot : Bool -> Nat -> Nat
  selectLocalOccurrenceSlot : Bool -> Nat -> Nat
  selectBlockStartSlot : Bool -> Nat -> Nat
  access_metadata_reads_eq :
    forall i,
      (routeData.accessRoute i).metadataReads =
        [accessBlockSlot i, accessOffsetSlot i]
  rank_metadata_reads_eq :
    forall target pos,
      (routeData.rankRoute target pos).metadataReads =
        [rankBlockSlot target pos,
          rankLocalLimitSlot target pos,
          rankBaseRankSlot target pos]
  select_metadata_reads_eq :
    forall target occurrence,
      (routeData.selectRoute target occurrence).metadataReads =
        [selectBlockSlot target occurrence,
          selectLocalOccurrenceSlot target occurrence,
          selectBlockStartSlot target occurrence]
  access_block_lt :
    forall i, (routeData.accessRoute i).blockIndex < 2 ^ fieldWidth
  access_offset_lt :
    forall i, (routeData.accessRoute i).offset < 2 ^ fieldWidth
  rank_block_lt :
    forall target pos,
      (routeData.rankRoute target pos).blockIndex < 2 ^ fieldWidth
  rank_localLimit_lt :
    forall target pos,
      (routeData.rankRoute target pos).localLimit < 2 ^ fieldWidth
  rank_baseRank_lt :
    forall target pos,
      (routeData.rankRoute target pos).baseRank < 2 ^ fieldWidth
  select_block_lt :
    forall target occurrence,
      (routeData.selectRoute target occurrence).blockIndex < 2 ^ fieldWidth
  select_localOccurrence_lt :
    forall target occurrence,
      (routeData.selectRoute target occurrence).localOccurrence <
        2 ^ fieldWidth
  select_blockStart_lt :
    forall target occurrence,
      (routeData.selectRoute target occurrence).blockStart < 2 ^ fieldWidth
  access_block_word_eq :
    forall i,
      routeData.routeStore.store.words[accessBlockSlot i]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.accessRoute i).blockIndex)
  access_offset_word_eq :
    forall i,
      routeData.routeStore.store.words[accessOffsetSlot i]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.accessRoute i).offset)
  rank_block_word_eq :
    forall target pos,
      routeData.routeStore.store.words[rankBlockSlot target pos]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.rankRoute target pos).blockIndex)
  rank_localLimit_word_eq :
    forall target pos,
      routeData.routeStore.store.words[rankLocalLimitSlot target pos]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.rankRoute target pos).localLimit)
  rank_baseRank_word_eq :
    forall target pos,
      routeData.routeStore.store.words[rankBaseRankSlot target pos]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.rankRoute target pos).baseRank)
  select_block_word_eq :
    forall target occurrence,
      routeData.routeStore.store.words[selectBlockSlot target occurrence]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.selectRoute target occurrence).blockIndex)
  select_localOccurrence_word_eq :
    forall target occurrence,
      routeData.routeStore.store.words[
          selectLocalOccurrenceSlot target occurrence]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.selectRoute target occurrence).localOccurrence)
  select_blockStart_word_eq :
    forall target occurrence,
      routeData.routeStore.store.words[
          selectBlockStartSlot target occurrence]? =
        some (SuccinctSpace.natToBitsLE fieldWidth
          (routeData.selectRoute target occurrence).blockStart)

namespace FixedWeightAmbientComputedRRRPackedRouteTableData

def toDecodedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRDecodedRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  wordSize_pos := data.routeData.wordSize_pos
  wordSize_le_ambient := data.routeData.wordSize_le_ambient
  blockSize := data.routeData.blockSize
  blockSize_pos := data.routeData.blockSize_pos
  blocks_flatten := data.routeData.blocks_flatten
  block_length_le := data.routeData.block_length_le
  blockSize_le_wordSize := data.routeData.blockSize_le_wordSize
  block_code_width_le := data.routeData.block_code_width_le
  codeStore := data.routeData.codeStore
  codeStore_aligned := data.routeData.codeStore_aligned
  routePayload := data.routeData.routePayload
  routeStore := data.routeData.routeStore
  routePayload_length_eq := data.routeData.routePayload_length_eq
  accessMetadataReads := fun i =>
    (data.routeData.accessRoute i).metadataReads
  rankMetadataReads := fun target pos =>
    (data.routeData.rankRoute target pos).metadataReads
  selectMetadataReads := fun target occurrence =>
    (data.routeData.selectRoute target occurrence).metadataReads
  accessRouteDecoder := fun _ readWords =>
    fixedWeightPackedRouteAccessDecoder readWords
  rankRouteDecoder := fun _ _ readWords =>
    fixedWeightPackedRouteRankDecoder readWords
  selectRouteDecoder := fun _ _ readWords =>
    fixedWeightPackedRouteSelectDecoder readWords
  accessRoute := data.routeData.accessRoute
  rankRoute := data.routeData.rankRoute
  selectRoute := data.routeData.selectRoute
  access_metadata_reads_le := data.routeData.access_metadata_reads_le
  rank_metadata_reads_le := data.routeData.rank_metadata_reads_le
  select_metadata_reads_le := data.routeData.select_metadata_reads_le
  access_route_metadata_reads_eq := by intro i; rfl
  rank_route_metadata_reads_eq := by intro target pos; rfl
  select_route_metadata_reads_eq := by intro target occurrence; rfl
  access_route_decode_exact := by
    intro i
    simp [fixedWeightPackedRouteAccessDecoder,
      boundedPayloadWordReadValues,
      data.access_metadata_reads_eq i,
      data.access_block_word_eq i,
      data.access_offset_word_eq i,
      data.access_block_lt i,
      data.access_offset_lt i,
      fixedWeightAmbientComputedRRRAccessRouteDecoded]
  rank_route_decode_exact := by
    intro target pos
    simp [fixedWeightPackedRouteRankDecoder,
      boundedPayloadWordReadValues,
      data.rank_metadata_reads_eq target pos,
      data.rank_block_word_eq target pos,
      data.rank_localLimit_word_eq target pos,
      data.rank_baseRank_word_eq target pos,
      data.rank_block_lt target pos,
      data.rank_localLimit_lt target pos,
      data.rank_baseRank_lt target pos,
      fixedWeightAmbientComputedRRRRankRouteDecoded]
  select_route_decode_exact := by
    intro target occurrence
    simp [fixedWeightPackedRouteSelectDecoder,
      boundedPayloadWordReadValues,
      data.select_metadata_reads_eq target occurrence,
      data.select_block_word_eq target occurrence,
      data.select_localOccurrence_word_eq target occurrence,
      data.select_blockStart_word_eq target occurrence,
      data.select_block_lt target occurrence,
      data.select_localOccurrence_lt target occurrence,
      data.select_blockStart_lt target occurrence,
      fixedWeightAmbientComputedRRRSelectRouteDecoded]
  local_query_cost_le := data.routeData.local_query_cost_le
  route_plus_local_le := data.routeData.route_plus_local_le

def toAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks overhead wordSize queryCost :=
  data.toDecodedRouteTableData.toAmbientBlockCompositionData

theorem access_packed_metadata_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :
    boundedPayloadWordReadValues data.routeData.routeStore
        (data.routeData.accessRoute i).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.accessRoute i).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.accessRoute i).offset)] := by
  simp [boundedPayloadWordReadValues,
    data.access_metadata_reads_eq i,
    data.access_block_word_eq i,
    data.access_offset_word_eq i]

theorem rank_packed_metadata_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    boundedPayloadWordReadValues data.routeData.routeStore
        (data.routeData.rankRoute target pos).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).localLimit),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.rankRoute target pos).baseRank)] := by
  simp [boundedPayloadWordReadValues,
    data.rank_metadata_reads_eq target pos,
    data.rank_block_word_eq target pos,
    data.rank_localLimit_word_eq target pos,
    data.rank_baseRank_word_eq target pos]

theorem select_packed_metadata_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    boundedPayloadWordReadValues data.routeData.routeStore
        (data.routeData.selectRoute target occurrence).metadataReads =
      [some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).blockIndex),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).localOccurrence),
       some (SuccinctSpace.natToBitsLE data.fieldWidth
          (data.routeData.selectRoute target occurrence).blockStart)] := by
  simp [boundedPayloadWordReadValues,
    data.select_metadata_reads_eq target occurrence,
    data.select_block_word_eq target occurrence,
    data.select_localOccurrence_word_eq target occurrence,
    data.select_blockStart_word_eq target occurrence]

def PackedRouteTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toDecodedRouteTableData.DecodedRouteTableProfile /\
    data.toDecodedRouteTableData.DecodedMetadataReadProfile /\
    data.fieldWidth <= wordSize /\
    (forall i,
      (data.toDecodedRouteTableData.accessMetadataReadsCosted i).cost = 2 /\
        (Costed.map (fun words =>
            fixedWeightPackedRouteAccessDecoder words)
          (data.toDecodedRouteTableData.accessMetadataReadsCosted i)).erase =
          fixedWeightAmbientComputedRRRAccessRouteDecoded
            (data.routeData.accessRoute i)) /\
    (forall target pos,
      (data.toDecodedRouteTableData.rankMetadataReadsCosted
          target pos).cost = 3 /\
        (Costed.map (fun words =>
            fixedWeightPackedRouteRankDecoder words)
          (data.toDecodedRouteTableData.rankMetadataReadsCosted
            target pos)).erase =
          fixedWeightAmbientComputedRRRRankRouteDecoded
            (data.routeData.rankRoute target pos)) /\
    (forall target occurrence,
      (data.toDecodedRouteTableData.selectMetadataReadsCosted
          target occurrence).cost = 3 /\
        (Costed.map (fun words =>
            fixedWeightPackedRouteSelectDecoder words)
          (data.toDecodedRouteTableData.selectMetadataReadsCosted
            target occurrence)).erase =
          fixedWeightAmbientComputedRRRSelectRouteDecoded
            (data.routeData.selectRoute target occurrence))

theorem packed_route_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.PackedRouteTableProfile := by
  refine
    ⟨data.toDecodedRouteTableData.decoded_route_table_profile,
      data.toDecodedRouteTableData.decoded_metadata_read_profile,
      data.fieldWidth_le_wordSize,
      ?_,
      ?_,
      ?_⟩
  · intro i
    constructor
    · simp [toDecodedRouteTableData,
        FixedWeightAmbientComputedRRRDecodedRouteTableData.accessMetadataReadsCosted,
        data.access_metadata_reads_eq i]
    · simpa [toDecodedRouteTableData] using
        (data.toDecodedRouteTableData.decoded_metadata_read_profile.1 i).2
  · intro target pos
    constructor
    · simp [toDecodedRouteTableData,
        FixedWeightAmbientComputedRRRDecodedRouteTableData.rankMetadataReadsCosted,
        data.rank_metadata_reads_eq target pos]
    · simpa [toDecodedRouteTableData] using
        (data.toDecodedRouteTableData.decoded_metadata_read_profile.2.1
          target pos).2
  · intro target occurrence
    constructor
    · simp [toDecodedRouteTableData,
        FixedWeightAmbientComputedRRRDecodedRouteTableData.selectMetadataReadsCosted,
        data.select_metadata_reads_eq target occurrence]
    · simpa [toDecodedRouteTableData] using
        (data.toDecodedRouteTableData.decoded_metadata_read_profile.2.2
          target occurrence).2

end FixedWeightAmbientComputedRRRPackedRouteTableData

/-- Family of packed fixed-width route/class metadata tables. -/
structure FixedWeightAmbientComputedRRRPackedRouteTableFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRPackedRouteTableData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRPackedRouteTableFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRPackedRouteTableData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def toDecodedRouteTableFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRDecodedRouteTableFamily
      slots routeCost localQueryCost queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := (family.componentData bits).toDecodedRouteTableData

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toAmbientBlockCompositionData

theorem packed_route_table_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.PackedRouteTableProfile /\
          data.routeData.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    exact
      ⟨data.packed_route_table_profile,
        data.routeData.routePayload_length_eq,
        (family.directory bits).payload_length,
        data.routeData.blocks_flatten,
        (fun i => (family.directory bits).accessCosted_cost_le i),
        (fun target pos =>
          (family.directory bits).rankCosted_cost_le target pos),
        (fun target occurrence =>
          (family.directory bits).selectCosted_cost_le
            target occurrence)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRPackedRouteTableFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        (family.componentData bits).PackedRouteTableProfile /\
          let data := family.directory bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                compressedOverhead slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  have hcompressed :=
    FixedWeightAmbientComputedRRRDecodedRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family.toDecodedRouteTableFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead,
      FixedWeightAmbientComputedRRRDecodedRouteTableFamily.compressedOverhead]
      using hcompressed.1
  · intro bits
    constructor
    · exact (family.componentData bits).packed_route_table_profile
    · simpa [directory, toDecodedRouteTableFamily, componentData,
        FixedWeightAmbientComputedRRRDecodedRouteTableFamily.directory,
        FixedWeightAmbientComputedRRRDecodedRouteTableFamily.componentData,
        FixedWeightAmbientComputedRRRDecodedRouteTableFamily.compressedOverhead,
        compressedOverhead]
        using (hcompressed.2 bits).2

end FixedWeightAmbientComputedRRRPackedRouteTableFamily

/-- Decode the first charged decoded-table word as a local bit block. -/
def decodedWordFromReadValues :
    List (Option (List Bool)) -> List Bool
  | some word :: _ => word
  | _ => []

@[simp] theorem decodedWordFromReadValues_singleton
    (bits : List Bool) :
    decodedWordFromReadValues [some bits] = bits := by
  simp [decodedWordFromReadValues]


/--
Local RRR-style fixed-weight block data.

The query path is concrete and dependent-read: read the packed fixed-weight
code, use it as an address into the counted universal decode table for this
block length and weight, then run a RAM word primitive on the decoded block.
The decode table is dense and therefore not an `o(n)` family construction by
itself; it is the non-oracular local block kernel the later compressed/FID
directory should use under a smaller table/routing scheme.
-/
structure FixedWeightTableRAMBlockData
    (bits : List Bool) (wordSize : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_machine : wordSize <= Nat.log2 bits.length + 1
  codeWidth_le_wordSize : fixedWeightPayloadBudget bits <= wordSize
  blockWidth_le_wordSize : bits.length <= wordSize

namespace FixedWeightTableRAMBlockData

def decodedTableOverhead
    {bits : List Bool} {wordSize : Nat}
    (_data : FixedWeightTableRAMBlockData bits wordSize) : Nat :=
  fixedWeightDecodedWordTableOverhead bits.length (trueCount bits)

@[simp] theorem decodedTableOverhead_eq
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.decodedTableOverhead =
      fixedWeightDecodedWordTableOverhead bits.length (trueCount bits) := by
  rfl

def packedStore
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightPackedPayload bits) wordSize :=
  fixedWeightPackedCodeBoundedStore bits wordSize
    data.codeWidth_le_wordSize

def decodedStore
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightDecodedWordTablePayload bits.length (trueCount bits))
      wordSize :=
  fixedWeightDecodedWordBoundedStore bits.length (trueCount bits) wordSize
    data.blockWidth_le_wordSize

theorem packed_read_values_zero
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    boundedPayloadWordReadValues data.packedStore [0] =
      [some (fixedWeightPackedPayload bits)] := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  simp [boundedPayloadWordReadValues, hpacked]

theorem decoded_read_values_code
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    boundedPayloadWordReadValues data.decodedStore [fixedWeightCode bits] =
      [some bits] := by
  have hdecoded :
      data.decodedStore.store.words[fixedWeightCode bits]? = some bits := by
    simpa [decodedStore] using
      fixedWeightDecodedWordBoundedStore_get?_fixedWeightCode bits
        data.blockWidth_le_wordSize
  simp [boundedPayloadWordReadValues, hdecoded]

def payload
    {bits : List Bool} {wordSize : Nat}
    (_data : FixedWeightTableRAMBlockData bits wordSize) : List Bool :=
  fixedWeightPackedPayload bits ++
    fixedWeightDecodedWordTablePayload bits.length (trueCount bits)

@[simp] theorem payload_length
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.payload.length =
      fixedWeightPayloadBudget bits + data.decodedTableOverhead := by
  simp [payload, decodedTableOverhead, fixedWeightPackedPayload_length]

def readCodeCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Costed Nat :=
  Costed.bind (data.packedStore.store.readWordCosted 0) fun word? =>
    Costed.pure
      (match word? with
      | some word => SuccinctSpace.bitsToNatLE word
      | none => 0)

@[simp] theorem readCodeCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.readCodeCosted.cost = 1 := by
  simp [readCodeCosted]

@[simp] theorem readCodeCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.readCodeCosted.erase = fixedWeightCode bits := by
  simp [readCodeCosted, packedStore, fixedWeightPackedCodeBoundedStore,
    fixedWeightPackedPayload_bitsToNatLE]

def decodedWordCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    Costed (List Bool) :=
  Costed.bind data.readCodeCosted fun code =>
    Costed.bind (data.decodedStore.store.readWordCosted code) fun word? =>
      Costed.pure (word?.getD [])

@[simp] theorem decodedWordCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.decodedWordCosted.cost = 2 := by
  simp [decodedWordCosted]

@[simp] theorem decodedWordCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.decodedWordCosted.erase = bits := by
  have hdec :
      fixedWeightDecode? bits.length (trueCount bits)
          (fixedWeightCode bits) = some bits :=
    fixedWeightDecode?_fixedWeightEncode?
      (fixedWeightEncode?_eq_some_fixedWeightCode bits)
  have hget :
      data.decodedStore.store.words[fixedWeightCode bits]? = some bits :=
    fixedWeightDecodedWordBoundedStore_get?_of_decode
      data.blockWidth_le_wordSize hdec
  simp [decodedWordCosted, hget]

def accessCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (i : Nat) : Costed (Option Bool) :=
  Costed.map (fun word => word[i]?) data.decodedWordCosted

@[simp] theorem accessCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).cost = 2 := by
  simp [accessCosted]

@[simp] theorem accessCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (i : Nat) :
    (data.accessCosted i).erase = bits[i]? := by
  simp [accessCosted]

def rankCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (pos : Nat) : Costed Nat :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.rankBoolWordPrefix target word pos).toCosted

@[simp] theorem rankCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost = 3 := by
  simp [rankCosted]

@[simp] theorem rankCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      Succinct.rankPrefix target bits pos := by
  unfold rankCosted
  simp only [Costed.erase_bind, decodedWordCosted_erase]
  change (RAM.rankBoolWordPrefix target bits pos).toCosted.value =
    Succinct.rankPrefix target bits pos
  have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
  simpa [Costed.run] using congrArg Prod.fst hrun

def selectCosted
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (occurrence : Nat) : Costed (Option Nat) :=
  Costed.bind data.decodedWordCosted fun word =>
    (RAM.selectBoolWord target word occurrence).toCosted

@[simp] theorem selectCosted_cost
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).cost = 3 := by
  simp [selectCosted]

@[simp] theorem selectCosted_erase
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize)
    (target : Bool) (occurrence : Nat) :
    (data.selectCosted target occurrence).erase =
      Succinct.select target bits occurrence := by
  unfold selectCosted
  simp only [Costed.erase_bind, decodedWordCosted_erase]
  change (RAM.selectBoolWord target bits occurrence).toCosted.value =
    Succinct.select target bits occurrence
  have hrun := Succinct.selectBoolWord_toCosted_run target bits occurrence
  simpa [Costed.run] using congrArg Prod.fst hrun

def toDependentAuxiliaryData
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    FixedWeightDependentAuxiliaryData
      bits data.decodedTableOverhead wordSize 3 := by
  refine
    { wordSize_pos := data.wordSize_pos
      packedStore := data.packedStore
      auxPayload :=
        fixedWeightDecodedWordTablePayload bits.length (trueCount bits)
      auxStore := data.decodedStore
      aux_length_eq := ?_
      accessPackedReads := fun _ => [0]
      accessAuxReads := fun _ packedWords =>
        [fixedWeightCodeFromReadValues packedWords]
      rankPackedReads := fun _ _ => [0]
      rankAuxReads := fun _ _ packedWords =>
        [fixedWeightCodeFromReadValues packedWords]
      selectPackedReads := fun _ _ => [0]
      selectAuxReads := fun _ _ packedWords =>
        [fixedWeightCodeFromReadValues packedWords]
      accessEvalCosted := fun i _ auxWords =>
        Costed.pure ((decodedWordFromReadValues auxWords)[i]?)
      rankEvalCosted := fun target pos _ auxWords =>
        (RAM.rankBoolWordPrefix target
          (decodedWordFromReadValues auxWords) pos).toCosted
      selectEvalCosted := fun target occurrence _ auxWords =>
        (RAM.selectBoolWord target
          (decodedWordFromReadValues auxWords) occurrence).toCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · simp [decodedTableOverhead]
  · intro i
    have hpackedValues := data.packed_read_values_zero
    simp [hpackedValues]
  · intro target pos
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    simp [hpackedValues, hdecodedValues]
  · intro target occurrence
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    simp [hpackedValues, hdecodedValues]
  · intro i
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    simp [hpackedValues, hdecodedValues]
  · intro target pos
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    have hrun := Succinct.rankBoolWordPrefix_toCosted_run target bits pos
    simpa [Costed.erase, Costed.run, hpackedValues, hdecodedValues]
      using congrArg Prod.fst hrun
  · intro target occurrence
    have hpackedValues := data.packed_read_values_zero
    have hdecodedValues := data.decoded_read_values_code
    have hrun := Succinct.selectBoolWord_toCosted_run
      target bits occurrence
    simpa [Costed.erase, Costed.run, hpackedValues, hdecodedValues]
      using congrArg Prod.fst hrun

def toCompressedDirectory
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    CompressedBitVectorRankSelectDirectory
      bits data.decodedTableOverhead 3 where
  payload := data.payload
  payload_length_le := by
    simp
  accessCosted := data.accessCosted
  rankCosted := data.rankCosted
  selectCosted := data.selectCosted
  access_cost_le := by
    intro i
    rw [data.accessCosted_cost i]
    omega
  rank_cost_le := by
    intro target pos
    simp
  select_cost_le := by
    intro target occurrence
    simp
  access_exact := data.accessCosted_erase
  rank_exact := data.rankCosted_erase
  select_exact := data.selectCosted_erase

/--
The direct local table/RAM directory and the generic dependent-auxiliary
adapter expose the same charged query behavior.
-/
def DependentAuxiliaryBridgeProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Prop :=
  ((data.toDependentAuxiliaryData).toCompressedDirectory).payload =
      (data.toCompressedDirectory).payload /\
    (forall i,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).accessQueryCosted
          i).cost =
          ((data.toCompressedDirectory).accessQueryCosted i).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).accessQueryCosted
          i).erase =
          ((data.toCompressedDirectory).accessQueryCosted i).erase) /\
    (forall target pos,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).rankQueryCosted
          target pos).cost =
          ((data.toCompressedDirectory).rankQueryCosted target pos).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).rankQueryCosted
          target pos).erase =
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase) /\
    (forall target occurrence,
      (((data.toDependentAuxiliaryData).toCompressedDirectory).selectQueryCosted
          target occurrence).cost =
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost /\
        (((data.toDependentAuxiliaryData).toCompressedDirectory).selectQueryCosted
          target occurrence).erase =
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase)

theorem dependent_auxiliary_bridge_profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.DependentAuxiliaryBridgeProfile := by
  constructor
  · rfl
  constructor
  · intro i
    constructor
    · change ((data.toDependentAuxiliaryData).accessCosted i).cost =
        (data.accessCosted i).cost
      have hleft :
          ((data.toDependentAuxiliaryData).accessCosted i).cost = 2 := by
        simp [toDependentAuxiliaryData, FixedWeightDependentAuxiliaryData.accessCosted,
          data.packed_read_values_zero, data.decoded_read_values_code]
      rw [hleft, data.accessCosted_cost i]
    · change ((data.toDependentAuxiliaryData).accessCosted i).erase =
        (data.accessCosted i).erase
      simp
  constructor
  · intro target pos
    constructor
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).cost =
        (data.rankCosted target pos).cost
      have hleft :
          ((data.toDependentAuxiliaryData).rankCosted target pos).cost =
            3 := by
        simp [toDependentAuxiliaryData, FixedWeightDependentAuxiliaryData.rankCosted,
          data.packed_read_values_zero, data.decoded_read_values_code]
      rw [hleft, data.rankCosted_cost target pos]
    · change ((data.toDependentAuxiliaryData).rankCosted target pos).erase =
        (data.rankCosted target pos).erase
      simp
  · intro target occurrence
    constructor
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).cost =
        (data.selectCosted target occurrence).cost
      have hleft :
          ((data.toDependentAuxiliaryData).selectCosted
              target occurrence).cost = 3 := by
        simp [toDependentAuxiliaryData, FixedWeightDependentAuxiliaryData.selectCosted,
          data.packed_read_values_zero, data.decoded_read_values_code]
      rw [hleft, data.selectCosted_cost target occurrence]
    · change
        ((data.toDependentAuxiliaryData).selectCosted
          target occurrence).erase =
        (data.selectCosted target occurrence).erase
      simp

theorem directory_profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    (data.toCompressedDirectory).payload = data.payload /\
      (data.toCompressedDirectory).payload.length =
        fixedWeightPayloadBudget bits + data.decodedTableOverhead /\
      SuccinctSpace.flattenPayloadWords
          data.packedStore.store.words.toList =
        fixedWeightPackedPayload bits /\
      SuccinctSpace.flattenPayloadWords
          data.decodedStore.store.words.toList =
        fixedWeightDecodedWordTablePayload bits.length (trueCount bits) /\
      wordSize <= Nat.log2 bits.length + 1 /\
      (forall i,
        ((data.toCompressedDirectory).accessQueryCosted i).cost <= 3 /\
          ((data.toCompressedDirectory).accessQueryCosted i).erase =
            bits[i]?) /\
      (forall target pos,
        ((data.toCompressedDirectory).rankQueryCosted target pos).cost <=
            3 /\
          ((data.toCompressedDirectory).rankQueryCosted target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall target occurrence,
        ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).cost <= 3 /\
          ((data.toCompressedDirectory).selectQueryCosted
            target occurrence).erase =
            Succinct.select target bits occurrence) := by
  constructor
  · rfl
  constructor
  · exact data.payload_length
  constructor
  · exact data.packedStore.erases
  constructor
  · exact data.decodedStore.erases
  constructor
  · exact data.wordSize_le_machine
  constructor
  · intro i
    change (data.accessCosted i).cost <= 3 /\
      (data.accessCosted i).erase = bits[i]?
    exact ⟨by rw [data.accessCosted_cost i]; omega,
      data.accessCosted_erase i⟩
  constructor
  · intro target pos
    change (data.rankCosted target pos).cost <= 3 /\
      (data.rankCosted target pos).erase =
        Succinct.rankPrefix target bits pos
    exact ⟨by rw [data.rankCosted_cost target pos]; omega,
      data.rankCosted_erase target pos⟩
  · intro target occurrence
    change (data.selectCosted target occurrence).cost <= 3 /\
      (data.selectCosted target occurrence).erase =
        Succinct.select target bits occurrence
    exact ⟨by rw [data.selectCosted_cost target occurrence]; omega,
      data.selectCosted_erase target occurrence⟩

/--
Detailed dependent-read profile for the local fixed-weight table/RAM kernel.

This exposes the non-oracular route that the directory profile abstracts over:
the packed code is read from slot zero, the erased code chooses the decoded-word
table address, and rank/select then run fixed RAM word primitives on that
decoded word.  The decoded table is dense, so this is a local block profile
rather than a global `o(n)` FID family theorem.
-/
def DependentReadProfile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) : Prop :=
  data.payload.length =
      fixedWeightPayloadBudget bits + data.decodedTableOverhead /\
    data.decodedTableOverhead =
      fixedWeightDecodedWordTableOverhead bits.length (trueCount bits) /\
    SuccinctSpace.flattenPayloadWords
        data.packedStore.store.words.toList =
      fixedWeightPackedPayload bits /\
    data.packedStore.store.words[0]? =
      some (fixedWeightPackedPayload bits) /\
    fixedWeightPayloadBudget bits <= wordSize /\
    data.readCodeCosted.cost = 1 /\
    data.readCodeCosted.erase = fixedWeightCode bits /\
    SuccinctSpace.flattenPayloadWords
        data.decodedStore.store.words.toList =
      fixedWeightDecodedWordTablePayload bits.length (trueCount bits) /\
    data.decodedStore.store.words[fixedWeightCode bits]? = some bits /\
    bits.length <= wordSize /\
    (forall {word : List Bool},
      List.Mem word data.packedStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall {word : List Bool},
      List.Mem word data.decodedStore.store.words.toList ->
        word.length <= wordSize) /\
    data.decodedWordCosted.cost = 2 /\
    data.decodedWordCosted.erase = bits /\
    wordSize <= Nat.log2 bits.length + 1 /\
    (forall i,
      (data.accessCosted i).cost = 2 /\
        (data.accessCosted i).erase = bits[i]?) /\
    (forall target pos,
      (data.rankCosted target pos).cost = 3 /\
        (data.rankCosted target pos).erase =
          Succinct.rankPrefix target bits pos) /\
    (forall target occurrence,
      (data.selectCosted target occurrence).cost = 3 /\
        (data.selectCosted target occurrence).erase =
          Succinct.select target bits occurrence)

theorem dependent_read_profile
    {bits : List Bool} {wordSize : Nat}
    (data : FixedWeightTableRAMBlockData bits wordSize) :
    data.DependentReadProfile := by
  have hpacked :
      data.packedStore.store.words[0]? =
        some (fixedWeightPackedPayload bits) := by
    simpa [packedStore] using
      fixedWeightPackedCodeBoundedStore_get?_zero bits
        data.codeWidth_le_wordSize
  have hdecoded :
      data.decodedStore.store.words[fixedWeightCode bits]? = some bits := by
    simpa [decodedStore] using
      fixedWeightDecodedWordBoundedStore_get?_fixedWeightCode bits
        data.blockWidth_le_wordSize
  exact
    ⟨data.payload_length,
      data.decodedTableOverhead_eq,
      data.packedStore.erases,
      hpacked,
      data.codeWidth_le_wordSize,
      data.readCodeCosted_cost,
      data.readCodeCosted_erase,
      data.decodedStore.erases,
      hdecoded,
      data.blockWidth_le_wordSize,
      (fun hmem => data.packedStore.word_length_le_of_mem hmem),
      (fun hmem => data.decodedStore.word_length_le_of_mem hmem),
      data.decodedWordCosted_cost,
      data.decodedWordCosted_erase,
      data.wordSize_le_machine,
      (fun i => ⟨data.accessCosted_cost i, data.accessCosted_erase i⟩),
      (fun target pos =>
        ⟨data.rankCosted_cost target pos,
          data.rankCosted_erase target pos⟩),
      (fun target occurrence =>
        ⟨data.selectCosted_cost target occurrence,
          data.selectCosted_erase target occurrence⟩)⟩

end FixedWeightTableRAMBlockData

end RankSelectSpec

end RMQ
