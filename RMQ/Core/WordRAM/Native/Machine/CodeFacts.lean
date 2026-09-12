import RMQ.Core.WordRAM.Native.Machine

/-! Converse instruction identities for an actual successful byte-code load. -/

namespace RMQ.SuccinctFinal.PackedNative.LimbMachine

open PackedWordRAM LimbWord

theorem decodeArithmetic_code (tag : Nat) (op : Arithmetic)
    (h : decodeArithmetic tag = some op) : op.code = tag := by
  unfold decodeArithmetic at h
  split at h <;> cases h <;> rfl

theorem decodeComparison_code (tag : Nat) (op : Comparison)
    (h : decodeComparison tag = some op) : op.code = tag := by
  unfold decodeComparison at h
  split at h <;> cases h <;> rfl

private theorem tag_cases (tag : Nat) :
    tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨
    tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ 9 ≤ tag := by omega

private theorem list_shapes (xs : List Nat) :
    xs = [] ∨ (∃ a, xs = [a]) ∨ (∃ a b, xs = [a,b]) ∨
    (∃ a b c, xs = [a,b,c]) ∨ (∃ a b c d, xs = [a,b,c,d]) ∨
    (∃ a b c d e tail, xs = a :: b :: c :: d :: e :: tail) :=
  match xs with
  | [] => .inl rfl
  | [a] => .inr (.inl ⟨a, rfl⟩)
  | [a,b] => .inr (.inr (.inl ⟨a,b,rfl⟩))
  | [a,b,c] => .inr (.inr (.inr (.inl ⟨a,b,c,rfl⟩)))
  | [a,b,c,d] => .inr (.inr (.inr (.inr (.inl ⟨a,b,c,d,rfl⟩))))
  | a :: b :: c :: d :: e :: tail => .inr (.inr (.inr (.inr (.inr ⟨a,b,c,d,e,tail,rfl⟩))))

theorem parseInstruction_success_encoding (fields : List Nat) (i : Instruction)
    (h : parseInstruction fields = .ok i) : i.encoding = fields := by
  cases fields with
  | nil => cases h
  | cons tag rest =>
      rcases tag_cases tag with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hlarge
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩ <;> cases h <;> rfl
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩ <;> cases h <;> rfl
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩ <;> cases h <;> rfl
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩
        · cases h
        · cases h
        · cases h
        · cases h
        · change (match decodeArithmetic a with
            | some op => Except.ok (Instruction.arithmetic op b c d)
            | none => Except.error "arithmetic tag") = .ok i at h
          cases hop : decodeArithmetic a with
          | none => rw [hop] at h; cases h
          | some op =>
              rw [hop] at h
              cases h
              simp [Instruction.encoding, Instruction.operands, decodeArithmetic_code _ _ hop]
        · cases h
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩
        · cases h
        · cases h
        · cases h
        · cases h
        · change (match decodeComparison a with
            | some op => Except.ok (Instruction.comparison op b c d)
            | none => Except.error "comparison tag") = .ok i at h
          cases hop : decodeComparison a with
          | none => rw [hop] at h; cases h
          | some op =>
              rw [hop] at h
              cases h
              simp [Instruction.encoding, Instruction.operands, decodeComparison_code _ _ hop]
        · cases h
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩ <;> cases h <;> rfl
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩ <;> cases h <;> rfl
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩ <;> cases h <;> rfl
      · rcases list_shapes rest with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩ |
          ⟨a,b,c,d,rfl⟩ | ⟨a,b,c,d,e,tail,rfl⟩ <;> cases h <;> rfl
      · obtain ⟨n, he⟩ := Nat.exists_eq_add_of_le' hlarge
        rw [he] at h
        cases h

/-- A successful parser certifies exact field identity, including all tags. -/
theorem decodeInstruction_success (width : Nat) (fields : Array Word) (i : Instruction)
    (h : decodeInstruction width fields = .ok i) :
    fields = encodeInstruction width i ∧ i.Fits width := by
  unfold decodeInstruction at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i hc
  have hcanonical : ∀ word ∈ fields.toList, LimbWord.Canonical width word := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hc
  have hencoding := parseInstruction_success_encoding _ _ h
  constructor
  · unfold encodeInstruction
    rw [hencoding, List.map_map]
    have he : fields.toList.map (LimbWord.encode width ∘ LimbWord.decode) = fields.toList := by
      calc
        _ = fields.toList.map id := List.map_congr_left fun word hw =>
          LimbWord.encode_decode _ _ (hcanonical word hw).1
        _ = _ := List.map_id _
    rw [he]
  · intro value hv
    rw [hencoding] at hv
    obtain ⟨word, hw, rfl⟩ := List.mem_map.1 hv
    exact (hcanonical word hw).2

theorem decodeInstruction_of_canonical (width : Nat) (fields : Array Word) (i : Instruction)
    (hs : fields.size ≤ 5)
    (hc : ∀ word ∈ fields.toList, LimbWord.Canonical width word)
    (hp : parseInstruction (fields.toList.map LimbWord.decode) = .ok i) :
    decodeInstruction width fields = .ok i := by
  simp [decodeInstruction, hs, List.all_eq_true, hc, hp]

/-- Successful decoded rows determine one same-order reference program.
The program here is a theorem witness, not a persistent machine cache. -/
theorem code_exists_program (width : Nat) (code : Code)
    (hc : ∀ fields ∈ code.toList, ∃ i, decodeInstruction width fields = .ok i) :
    ∃ program : Program, code = encodeCode width program ∧
      ∀ i ∈ program, i.Fits width := by
  have hlist : ∀ rows : List (Array Word),
      (∀ fields ∈ rows, ∃ i, decodeInstruction width fields = .ok i) →
      ∃ program : Program, rows = program.map (encodeInstruction width) ∧
        ∀ i ∈ program, i.Fits width := by
    intro rows
    induction rows with
    | nil => intro _; exact ⟨[], rfl, by simp⟩
    | cons row rows ih =>
        intro hrows
        obtain ⟨i, hi⟩ := hrows row (by simp)
        obtain ⟨program, he, hp⟩ := ih (by intro fields hf; exact hrows fields (by simp [hf]))
        have hf := decodeInstruction_success width row i hi
        refine ⟨i :: program, ?_, ?_⟩
        · simp [hf.1, he]
        · intro j hj
          rcases List.mem_cons.1 hj with rfl | hj
          · exact hf.2
          · exact hp j hj
  obtain ⟨program, he, hp⟩ := hlist code.toList hc
  refine ⟨program, ?_, hp⟩
  have ha := congrArg List.toArray he
  simpa [encodeCode] using ha

end RMQ.SuccinctFinal.PackedNative.LimbMachine
