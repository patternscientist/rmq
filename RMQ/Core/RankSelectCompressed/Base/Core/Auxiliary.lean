import RMQ.Core.RankSelectCompressed.Readback

namespace RMQ

namespace RankSelectSpec

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

/-- Per-block length entries for the ambient RRR class/length tables. -/
def fixedWeightBlockLengthEntries (blocks : List (List Bool)) :
    List Nat :=
  blocks.map List.length

/-- Per-block class entries (`trueCount`) for the ambient RRR class table. -/
def fixedWeightBlockClassEntries (blocks : List (List Bool)) :
    List Nat :=
  blocks.map trueCount

@[simp] theorem fixedWeightBlockLengthEntries_length
    (blocks : List (List Bool)) :
    (fixedWeightBlockLengthEntries blocks).length = blocks.length := by
  simp [fixedWeightBlockLengthEntries]

@[simp] theorem fixedWeightBlockClassEntries_length
    (blocks : List (List Bool)) :
    (fixedWeightBlockClassEntries blocks).length = blocks.length := by
  simp [fixedWeightBlockClassEntries]

theorem fixedWeightBlockLengthEntries_get?
    {blocks : List (List Bool)} {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    (fixedWeightBlockLengthEntries blocks)[blockIndex]? =
      some block.length := by
  simp [fixedWeightBlockLengthEntries, List.getElem?_map, hblock]

theorem fixedWeightBlockClassEntries_get?
    {blocks : List (List Bool)} {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    (fixedWeightBlockClassEntries blocks)[blockIndex]? =
      some (trueCount block) := by
  simp [fixedWeightBlockClassEntries, List.getElem?_map, hblock]

/-- Counted primary payload for a block-coded fixed-weight bitvector. -/
def fixedWeightBlockCodePayload (blocks : List (List Bool)) : List Bool :=
  SuccinctSpace.flattenPayloadWords (fixedWeightBlockCodeWords blocks)

/-- Sum of the fixed-weight code widths of all blocks. -/
def fixedWeightBlockPayloadBudget (blocks : List (List Bool)) : Nat :=
  (blocks.map fixedWeightPayloadBudget).sum

theorem fixedWeightBlockPayloadBudget_le_flatten_length_add_blocks
    (blocks : List (List Bool)) :
    fixedWeightBlockPayloadBudget blocks <=
      (SuccinctSpace.flattenPayloadWords blocks).length + blocks.length := by
  induction blocks with
  | nil =>
      simp [fixedWeightBlockPayloadBudget, SuccinctSpace.flattenPayloadWords]
  | cons block rest ih =>
      have hblock := fixedWeightPayloadBudget_le_length_add_one block
      have hrest :
          (rest.map fixedWeightPayloadBudget).sum <=
            (SuccinctSpace.flattenPayloadWords rest).length +
              rest.length := by
        simpa [fixedWeightBlockPayloadBudget] using ih
      simp [fixedWeightBlockPayloadBudget, SuccinctSpace.flattenPayloadWords]
      omega

theorem fixedWeightBlockPayloadBudget_le_payloadBudget_flatten_add_blocks
    (blocks : List (List Bool)) :
    fixedWeightBlockPayloadBudget blocks <=
      fixedWeightPayloadBudget (SuccinctSpace.flattenPayloadWords blocks) +
        blocks.length := by
  induction blocks with
  | nil =>
      simp [fixedWeightBlockPayloadBudget, SuccinctSpace.flattenPayloadWords,
        fixedWeightPayloadBudget]
  | cons block rest ih =>
      let flatRest := SuccinctSpace.flattenPayloadWords rest
      have hcountBlock : trueCount block <= block.length :=
        trueCount_le_length block
      have hcountRest : trueCount flatRest <= flatRest.length :=
        trueCount_le_length flatRest
      have hposBlock :
          0 < binomialCount block.length (trueCount block) :=
        binomialCount_pos_of_le hcountBlock
      have hposRest :
          0 < binomialCount flatRest.length (trueCount flatRest) :=
        binomialCount_pos_of_le hcountRest
      have hmul :
          binomialCount block.length (trueCount block) *
              binomialCount flatRest.length (trueCount flatRest) <=
            binomialCount (block.length + flatRest.length)
              (trueCount block + trueCount flatRest) :=
        binomialCount_mul_le_add _ _ _ _
      have hlog :
          Nat.log2 (binomialCount block.length (trueCount block)) +
              Nat.log2 (binomialCount flatRest.length (trueCount flatRest)) <=
            Nat.log2
              (binomialCount (block.length + flatRest.length)
                (trueCount block + trueCount flatRest)) :=
        log2_add_le_log2_mul_le hposBlock hposRest hmul
      have ih' :
          (rest.map fixedWeightPayloadBudget).sum <=
            Nat.log2 (binomialCount flatRest.length (trueCount flatRest)) + 1 +
              rest.length := by
        simpa [fixedWeightBlockPayloadBudget, fixedWeightPayloadBudget,
          flatRest] using ih
      dsimp [flatRest] at hlog ih'
      simp [fixedWeightBlockPayloadBudget, SuccinctSpace.flattenPayloadWords,
        fixedWeightPayloadBudget, trueCount_append]
      omega

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

end RankSelectSpec

end RMQ
