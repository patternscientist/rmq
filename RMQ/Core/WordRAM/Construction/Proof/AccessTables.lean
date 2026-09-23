import RMQ.Core.WordRAM.Construction.Proof.AccessRelative

/-! # PRE-1 builder proofs: the sixteen fixed-width access tables (stage S5)

Outside the builder firewall. `AccessReady` collects what the access emissions
read after the occurrence and flag passes: the size-only registers, the array
bases, the six filled arrays below the extent and two numeric envelopes. From
such a state each of the sixteen fixed-width sources (the two final rank
tables, the four super fields, the four local fields, the long and effective
sparse flag-rank tables and the two raw flag vectors) is emitted exactly as its
reference `tableBits`, keeping the access state for the next emission.
-/

namespace RMQ.SuccinctFinal.PackedConstruction.Proof

open Structured Builder Spec RMQ.Cartesian SuccinctClose RMQ.GenericSelect SuccinctSpace

/-! ## The state the eighteen emissions share -/

/-- Registers no access-half emission writes (the two flag counts 177 and 178
included). -/
abbrev AccessFrame (r : Nat) : Prop :=
  ¬ TableScratch r ∧ ¬ (26 ≤ r ∧ r ≤ 28) ∧ r ≠ 108 ∧ ¬ (169 ≤ r ∧ r ≤ 176) ∧ ¬ (179 ≤ r ∧ r ≤ 189)

/-- Everything the eighteen access emissions read: the size-only registers, the
array bases, the six arrays filled by the passes (below the extent), and the
two numeric envelopes the entry arithmetic needs. -/
structure AccessReady (W : Nat) (shape : CartesianShape) (P0 R0 L0 C0 F0 G0 : Nat) (u : State) :
    Prop where
  run : u.status = .running
  r1 : u.regs 1 = shape.size
  r2 : u.regs 2 = 1
  r9 : u.regs 9 = 2
  r39 : u.regs 39 = wordBits shape.bpCode.length
  r40 : u.regs 40 = superStride shape.bpCode.length
  r42 : u.regs 42 = localStride shape.bpCode.length
  r43 : u.regs 43 = localSlotsPerSuper shape.bpCode.length
  r45 : u.regs 45 = superSlotCount shape.bpCode false
  r46 : u.regs 46 = localSlotCount shape.bpCode false
  r47 : u.regs 47 = (sparseExceptionEffectiveFlagBits shape.bpCode false).length
  r48 : u.regs 48 = SuccinctRank.machineWordBits
    (SuccinctRank.machineWordBits shape.bpCode.length * SuccinctRank.machineWordBits shape.bpCode.length)
  r49 : u.regs 49 = sparseExceptionRelativeWidth shape.bpCode
  r50 : u.regs 50 = SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length
  r51 : u.regs 51 = SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length
  r52 : u.regs 52 = shape.bpCode.length / SuccinctRank.machineWordBits shape.bpCode.length /
    SuccinctRank.machineWordBits shape.bpCode.length + 1
  r53 : u.regs 53 = shape.bpCode.length / SuccinctRank.machineWordBits shape.bpCode.length + 1
  r54 : u.regs 54 = (longSuperFlagBits shape.bpCode false).length /
    SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length + 1
  r55 : u.regs 55 = (sparseExceptionEffectiveFlagBits shape.bpCode false).length /
    SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length + 1
  r159 : u.regs 159 = P0
  r160 : u.regs 160 = R0
  r161 : u.regs 161 = L0
  r162 : u.regs 162 = C0
  r163 : u.regs 163 = F0
  r164 : u.regs 164 = G0
  pos : ∀ q, q ≤ shape.size → u.memory (P0 + q) = some (position shape.bpCode false q)
  rw : ∀ j, j ≤ shape.bpCode.length / wordBits shape.bpCode.length →
    u.memory (R0 + j) = some (RMQ.Succinct.rankPrefix false shape.bpCode (j * wordBits shape.bpCode.length))
  lf : ∀ k, k < superSlotCount shape.bpCode false →
    u.memory (L0 + k) = some (flagNat (superIsLong shape.bpCode false k))
  lfc : ∀ k, k ≤ superSlotCount shape.bpCode false →
    u.memory (C0 + k) = some (RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) k)
  sf : ∀ g, g < localSlotCount shape.bpCode false →
    u.memory (F0 + g) = some (flagNat (localIsSparseException shape.bpCode false g))
  sfc : ∀ g, g ≤ localSlotCount shape.bpCode false →
    u.memory (G0 + g) = some (RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) g)
  lay1 : P0 + shape.size + 1 ≤ R0
  lay2 : R0 + shape.bpCode.length / wordBits shape.bpCode.length + 1 ≤ L0
  lay3 : L0 + superSlotCount shape.bpCode false ≤ C0
  lay4 : C0 + superSlotCount shape.bpCode false + 1 ≤ F0
  lay5 : F0 + localSlotCount shape.bpCode false ≤ G0
  lay6 : G0 + localSlotCount shape.bpCode false + 1 ≤ u.extent
  capS : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length +
    localStride shape.bpCode.length < 2 ^ W
  lenW : shape.bpCode.length + 1 < 2 ^ W

/-- A later state that keeps the access frame, the memory below the extent and
does not shrink the extent keeps the access state. -/
theorem AccessReady.mono {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat} {u v : State}
    (h : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hr : v.status = .running) (hfr : ∀ r, AccessFrame r → v.regs r = u.regs r)
    (hm : ∀ a, a < u.extent → v.memory a = u.memory a) (hx : u.extent ≤ v.extent) :
    AccessReady W shape P0 R0 L0 C0 F0 G0 v := by
  have l6 := h.lay6
  have l5 := h.lay5
  have l4 := h.lay4
  have l3 := h.lay3
  have l2 := h.lay2
  have l1 := h.lay1
  obtain ⟨Lq, hLq⟩ : ∃ x, shape.bpCode.length / wordBits shape.bpCode.length = x := ⟨_, rfl⟩
  have l2' : R0 + Lq + 1 ≤ L0 := hLq ▸ l2
  exact {
    run := hr
    r1 := by rw [hfr 1 (by decide)]; exact h.r1
    r2 := by rw [hfr 2 (by decide)]; exact h.r2
    r9 := by rw [hfr 9 (by decide)]; exact h.r9
    r39 := by rw [hfr 39 (by decide)]; exact h.r39
    r40 := by rw [hfr 40 (by decide)]; exact h.r40
    r42 := by rw [hfr 42 (by decide)]; exact h.r42
    r43 := by rw [hfr 43 (by decide)]; exact h.r43
    r45 := by rw [hfr 45 (by decide)]; exact h.r45
    r46 := by rw [hfr 46 (by decide)]; exact h.r46
    r47 := by rw [hfr 47 (by decide)]; exact h.r47
    r48 := by rw [hfr 48 (by decide)]; exact h.r48
    r49 := by rw [hfr 49 (by decide)]; exact h.r49
    r50 := by rw [hfr 50 (by decide)]; exact h.r50
    r51 := by rw [hfr 51 (by decide)]; exact h.r51
    r52 := by rw [hfr 52 (by decide)]; exact h.r52
    r53 := by rw [hfr 53 (by decide)]; exact h.r53
    r54 := by rw [hfr 54 (by decide)]; exact h.r54
    r55 := by rw [hfr 55 (by decide)]; exact h.r55
    r159 := by rw [hfr 159 (by decide)]; exact h.r159
    r160 := by rw [hfr 160 (by decide)]; exact h.r160
    r161 := by rw [hfr 161 (by decide)]; exact h.r161
    r162 := by rw [hfr 162 (by decide)]; exact h.r162
    r163 := by rw [hfr 163 (by decide)]; exact h.r163
    r164 := by rw [hfr 164 (by decide)]; exact h.r164
    pos := fun q hq => by rw [hm _ (by omega)]; exact h.pos q hq
    rw := fun j hj => by
      have hj' : j ≤ Lq := hLq ▸ hj
      rw [hm _ (by omega)]; exact h.rw j hj
    lf := fun k hk => by rw [hm _ (by omega)]; exact h.lf k hk
    lfc := fun k hk => by rw [hm _ (by omega)]; exact h.lfc k hk
    sf := fun g hg => by rw [hm _ (by omega)]; exact h.sf g hg
    sfc := fun g hg => by rw [hm _ (by omega)]; exact h.sfc g hg
    lay1 := l1
    lay2 := l2
    lay3 := l3
    lay4 := l4
    lay5 := l5
    lay6 := by omega
    capS := h.capS
    lenW := h.lenW }

/-- An emission that keeps the access frame keeps the access state. -/
theorem AccessReady.step {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat} {u v : State}
    {vals : List Nat} (h : AccessReady W shape P0 R0 L0 C0 F0 G0 u) (hE : Emits u v vals)
    (hr : v.status = .running) (hfr : ∀ r, AccessFrame r → v.regs r = u.regs r) :
    AccessReady W shape P0 R0 L0 C0 F0 G0 v :=
  h.mono hr hfr (fun _ ha => hE.memory_below ha) (by rw [hE.1]; omega)

theorem accessFrame_of_table {r : Nat} (h : AccessFrame r) : ¬ AccessWrites r ∧ ¬ TableScratch r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun e => ?_, h1⟩
  rcases e with e | e | e | e
  · exact h3 e
  · exact h2 e
  · exact h4 ⟨by omega, by omega⟩
  · exact h5 e

theorem accessFrame_of_body {r : Nat} (h : AccessFrame r) : ¬ BodyWrites r ∧ r ≠ 173 ∧ r ≠ 174 ∧
    r ≠ 175 ∧ r ≠ 176 := by
  obtain ⟨a, b⟩ := accessFrame_of_table h
  obtain ⟨_, _, _, h4, _⟩ := h
  refine ⟨fun e => ?_, by omega, by omega, by omega, by omega⟩
  rcases e with e | e
  · exact b e
  · exact a e

theorem machineWordBits_le_succ (n : Nat) : SuccinctRank.machineWordBits n ≤ n + 1 := by
  show Nat.log2 n + 1 ≤ n + 1
  have := Nat.log2_le_self n
  omega

/-- Uniform cost of one table: `count * (J + 7 w + 7) + 3` is at most
`(J + 14) * bits + 3` when the width is positive. -/
theorem table_cost_le {count w J : Nat} (hw : 1 ≤ w) :
    count * (J + 7 * w + 7) + 3 ≤ (J + 14) * (count * w) + 3 := by
  have h1 : count ≤ count * w := Nat.le_mul_of_pos_right count hw
  have h2 : count * (J + 7 * w + 7) = count * J + 7 * (count * w) + 7 * count := by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm count (7 * w), Nat.mul_assoc, Nat.mul_comm w count,
      Nat.mul_comm count 7]
  have h3 : (J + 14) * (count * w) = J * (count * w) + 14 * (count * w) := Nat.add_mul _ _ _
  have h4 : count * J ≤ J * (count * w) := by
    rw [Nat.mul_comm count J]; exact Nat.mul_le_mul_left J h1
  omega

/-! ## One table emission from an access state -/

theorem AccessReady.lenW' {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat} {u : State}
    (h : AccessReady W shape P0 R0 L0 C0 F0 G0 u) : shape.bpCode.length < 2 ^ W := by
  have := h.lenW; omega

/-- An entry state inside a table emission started from an access state. -/
theorem AccessReady.entry {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat} {u x : State}
    {writes : Nat → Prop} (h : AccessReady W shape P0 R0 L0 C0 F0 G0 u) (hw : ∀ r, AccessFrame r → ¬ writes r)
    (hr : x.status = .running) (hfr : ∀ r, ¬ writes r → ¬ TableScratch r → x.regs r = u.regs r)
    (hm : ∀ a, a < u.extent → x.memory a = u.memory a) (hx : u.extent ≤ x.extent) :
    AccessReady W shape P0 R0 L0 C0 F0 G0 x :=
  h.mono hr (fun r hr' => hfr r (hw r hr') hr'.1) hm hx

/-- **Generic access table.** `emitTable` over an access state with a count
register holding `N`, a width register holding `wv ≥ 1`, and an entry block
that computes `f slot` from any access state emits `tableBits es wv` for
`es = (range N).map f`. -/
theorem accessTable_generic {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (count w : Operand) (entry : Block) (J : Nat) (writes : Nat → Prop)
    (hcount : ¬ TableScratch count) (hwreg : ¬ TableScratch w)
    (hwc : ¬ writes count) (hww : ¬ writes w) (hw2 : ¬ writes 2) (hw9 : ¬ writes 9) (hw14 : ¬ writes 14)
    (hframe : ∀ r, AccessFrame r → ¬ writes r)
    (N wv : Nat) (es : List Nat) (f : Nat → Nat)
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u) (hN : u.regs count = N)
    (hwv : u.regs w = wv) (hwpos : 1 ≤ wv) (hwvW : wv < 2 ^ W)
    (hes : (List.range N).map f = es)
    (hext : u.extent + (tableBits es wv).length < 2 ^ W)
    (hentry : ∀ x : State, AccessReady W shape P0 R0 L0 C0 F0 G0 x → x.status = .running →
      (∀ r, ¬ writes r → ¬ TableScratch r → x.regs r = u.regs r) → x.regs 14 < N →
      EntryOK W entry writes x (f (x.regs 14)) J) :
    ∃ v k, SafeEval W (emitTable count w entry) u v k ∧ k ≤ (J + 14) * (tableBits es wv).length + 3 ∧
      v.status = .running ∧ Emits u v ((tableBits es wv).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hlen : (tableBits es wv).length = N * wv := by
    rw [tableBits_length, ← hes, List.length_map, List.length_range]
  rw [hlen] at hext ⊢
  have hNw : N ≤ N * wv := Nat.le_mul_of_pos_right N hwpos
  have l6 := hA.lay6
  have h2W := two_le_two_pow hW
  obtain ⟨v, k, ev, hk, hr, hE, hfr, hkr, hks⟩ :=
    emitTable_spec hW count w entry f J writes hcount hwreg hwc hww hw2 hw9 hw14 u hA.run hA.r2 hA.r9
      (by rw [hN]; omega) (by rw [hwv]; exact hwvW) (by rw [hN, hwv]; exact hext)
      (by
        intro x hxr hxfr hxmem hxe hxk hxkr hslot
        have hx := hA.entry hframe hxr hxfr hxmem hxe
        exact hentry x hx hxr hxfr (by rw [← hN]; exact hslot))
  rw [hN, hwv, hes] at hE
  rw [hN, hwv] at hk
  refine ⟨v, k, ev, ?_, hr, hE, fun r h => hfr r (hframe r h) h.1, hkr, hks⟩
  have := table_cost_le (count := N) (J := J) hwpos
  omega

theorem accessWrites_frame : ∀ r, AccessFrame r → ¬ AccessWrites r :=
  fun _ h => (accessFrame_of_table h).1

/-! ## Sources 1 and 2: the final rank samples -/

theorem accessTable1_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SuccinctRank.canonicalSuperRankEntries false shape.bpCode
      (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
      (SuccinctRank.machineWordBits shape.bpCode.length)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rRSUP rWS rankSuperEntryBlock) u v k ∧
      k ≤ 17 * (tableBits (SuccinctRank.canonicalSuperRankEntries false shape.bpCode
        (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
        (SuccinctRank.machineWordBits shape.bpCode.length)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SuccinctRank.canonicalSuperRankEntries false shape.bpCode
        (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
        (SuccinctRank.machineWordBits shape.bpCode.length)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hws := wordBits_pos shape.bpCode.length
  obtain ⟨Lq, hLq⟩ : ∃ x, shape.bpCode.length / wordBits shape.bpCode.length = x := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ x, Lq / wordBits shape.bpCode.length = x := ⟨_, rfl⟩
  exact accessTable_generic hW rRSUP rWS rankSuperEntryBlock 3 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (Q + 1) (wordBits shape.bpCode.length) _
    (fun slot => RMQ.Succinct.rankPrefix false shape.bpCode
      (slot * wordBits shape.bpCode.length * wordBits shape.bpCode.length))
    u hA (by show u.regs 52 = Q + 1; rw [hA.r52, ← hQ, ← hLq]; rfl) hA.r39 hws
    (Nat.lt_of_le_of_lt (machineWordBits_le_succ _) hA.lenW) (by rw [← hQ, ← hLq]; rfl) hext
    (by
      intro x hx hxr _ hslot
      have hslot' : x.regs 14 ≤ Lq / wordBits shape.bpCode.length := by rw [hQ]; omega
      have hsw : x.regs 14 * wordBits shape.bpCode.length ≤ Lq := (Nat.le_div_iff_mul_le hws).1 hslot'
      have hx6 := hx.lay6
      have hx2 := hx.lay2
      have hx3 := hx.lay3
      have hx4 := hx.lay4
      have hx5 := hx.lay5
      rw [hLq] at hx2
      have hlenW := hx.lenW'
      have hu6 := hA.lay6
      exact flagRankEntry_spec hW rRWB rWS (by decide) x hxr R0 Lq (wordBits shape.bpCode.length) (x.regs 14)
        (fun j => RMQ.Succinct.rankPrefix false shape.bpCode (j * wordBits shape.bpCode.length)) rfl hx.r39
        hx.r160 hsw (fun j hj => hx.rw j (by rw [hLq]; exact hj)) (by omega) (by omega)
        (fun j _ => by
          show RMQ.Succinct.rankPrefix false shape.bpCode (j * wordBits shape.bpCode.length) < 2 ^ W
          have := RMQ.Succinct.rankPrefix_le_length false shape.bpCode (j * wordBits shape.bpCode.length)
          omega))

theorem AccessReady.wsW {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat} {u : State}
    (h : AccessReady W shape P0 R0 L0 C0 F0 G0 u) : wordBits shape.bpCode.length < 2 ^ W :=
  Nat.lt_of_le_of_lt (machineWordBits_le_succ _) h.lenW

theorem AccessReady.supS {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat} {u : State}
    (h : AccessReady W shape P0 R0 L0 C0 F0 G0 u) {k : Nat} (hk : k < superSlotCount shape.bpCode false) :
    k * superStride shape.bpCode.length < 2 ^ W := by
  have h1 : (k + 1) * superStride shape.bpCode.length ≤
      superSlotCount shape.bpCode false * superStride shape.bpCode.length := Nat.mul_le_mul_right _ hk
  have h2 : (k + 1) * superStride shape.bpCode.length =
      k * superStride shape.bpCode.length + superStride shape.bpCode.length := Nat.succ_mul _ _
  have h3 : (superSlotCount shape.bpCode false + 1) * superStride shape.bpCode.length =
      superSlotCount shape.bpCode false * superStride shape.bpCode.length + superStride shape.bpCode.length :=
    Nat.succ_mul _ _
  have := h.capS
  have := superStride_pos shape.bpCode.length
  omega

theorem rankBlock_mono (b : List Bool) (ws : Nat) :
    ∀ i j, i ≤ j → j ≤ b.length / ws →
      RMQ.Succinct.rankPrefix false b (i * ws) ≤ RMQ.Succinct.rankPrefix false b (j * ws) :=
  fun _ _ hij _ => RMQ.Succinct.rankPrefix_mono_limit false b (Nat.mul_le_mul_right ws hij)

theorem accessTable2_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
      (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
      (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
        SuccinctRank.machineWordBits shape.bpCode.length))).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rRBLK rRBW rankBlockEntryBlock) u v k ∧
      k ≤ 21 * (tableBits (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
        (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
        (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
          SuccinctRank.machineWordBits shape.bpCode.length))).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
        (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
        (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
          SuccinctRank.machineWordBits shape.bpCode.length))).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hws := wordBits_pos shape.bpCode.length
  have hrbw := SuccinctRank.machineWordBits_pos (SuccinctRank.machineWordBits shape.bpCode.length *
    SuccinctRank.machineWordBits shape.bpCode.length)
  obtain ⟨Lq, hLq⟩ : ∃ x, shape.bpCode.length / wordBits shape.bpCode.length = x := ⟨_, rfl⟩
  have hTlen : (tableBits (SuccinctRank.canonicalBlockRankEntries false shape.bpCode
      (SuccinctRank.machineWordBits shape.bpCode.length) (SuccinctRank.machineWordBits shape.bpCode.length))
      (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
        SuccinctRank.machineWordBits shape.bpCode.length))).length =
      (Lq + 1) * SuccinctRank.machineWordBits (SuccinctRank.machineWordBits shape.bpCode.length *
        SuccinctRank.machineWordBits shape.bpCode.length) := by
    rw [tableBits_length]; simp only [SuccinctRank.canonicalBlockRankEntries, List.length_map, List.length_range]
    rw [← hLq]; rfl
  have hwle := Nat.le_mul_of_pos_left (SuccinctRank.machineWordBits (SuccinctRank.machineWordBits
    shape.bpCode.length * SuccinctRank.machineWordBits shape.bpCode.length)) (show 0 < Lq + 1 by omega)
  exact accessTable_generic hW rRBLK rRBW rankBlockEntryBlock 7 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (Lq + 1) _ _
    (fun slot => RMQ.Succinct.rankPrefix false shape.bpCode (slot * wordBits shape.bpCode.length) -
      RMQ.Succinct.rankPrefix false shape.bpCode
        (slot / wordBits shape.bpCode.length * wordBits shape.bpCode.length * wordBits shape.bpCode.length))
    u hA (by show u.regs 53 = Lq + 1; rw [hA.r53, ← hLq]; rfl) hA.r48 hrbw (by omega)
    (by rw [← hLq]; rfl) hext
    (by
      intro x hx hxr _ hslot
      have hx6 := hx.lay6
      have hx2 := hx.lay2
      have hx3 := hx.lay3
      have hx4 := hx.lay4
      have hx5 := hx.lay5
      rw [hLq] at hx2
      have hlenW := hx.lenW'
      have hu6 := hA.lay6
      exact rankBlockEntry_spec hW x hxr R0 Lq (wordBits shape.bpCode.length) (x.regs 14)
        (fun j => RMQ.Succinct.rankPrefix false shape.bpCode (j * wordBits shape.bpCode.length)) rfl hx.r39
        hx.r160 hws (by omega) (fun j hj => hx.rw j (by rw [hLq]; exact hj))
        (fun i j hij hj => rankBlock_mono shape.bpCode _ i j hij (by rw [hLq]; exact hj))
        (by omega) (by omega)
        (fun j _ => by
          show RMQ.Succinct.rankPrefix false shape.bpCode (j * wordBits shape.bpCode.length) < 2 ^ W
          have := RMQ.Succinct.rankPrefix_le_length false shape.bpCode (j * wordBits shape.bpCode.length)
          omega))

/-! ## Sources 3 to 6: the super fields -/

theorem accessTable3_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences
      (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSUP rWS superOccEntryBlock) u v k ∧
      k ≤ 15 * (tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rSUP rWS superOccEntryBlock 1 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (superSlotCount shape.bpCode false) (wordBits shape.bpCode.length) _
    (fun slot => slot * superStride shape.bpCode.length)
    u hA hA.r45 hA.r39 (wordBits_pos _) hA.wsW
    (by simp only [SparseDenseSelectDenseLocalEntry.baseOccurrences, superEntries, List.map_map]; rfl) hext
    (fun x hx hxr _ hslot => superOccEntry_spec hW x hxr _ _ rfl hx.r40 (hx.supS (by
      have : x.regs 14 < superSlotCount shape.bpCode false := hslot; exact this)))

theorem AccessReady.posBounds {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat} {u x : State}
    (hu : AccessReady W shape P0 R0 L0 C0 F0 G0 u) (hx : AccessReady W shape P0 R0 L0 C0 F0 G0 x)
    {T : Nat} (hext : u.extent + T < 2 ^ W) :
    P0 + shape.size < x.extent ∧ P0 + shape.size < 2 ^ W ∧
      L0 + superSlotCount shape.bpCode false ≤ x.extent ∧ L0 + superSlotCount shape.bpCode false < 2 ^ W ∧
      F0 + localSlotCount shape.bpCode false ≤ x.extent ∧ F0 + localSlotCount shape.bpCode false < 2 ^ W ∧
      C0 + superSlotCount shape.bpCode false < x.extent ∧ C0 + superSlotCount shape.bpCode false < 2 ^ W ∧
      G0 + localSlotCount shape.bpCode false < x.extent ∧ G0 + localSlotCount shape.bpCode false < 2 ^ W := by
  have := hu.lay1
  have := hu.lay2
  have := hu.lay3
  have := hu.lay4
  have := hu.lay5
  have := hu.lay6
  have := hx.lay6
  obtain ⟨Lq, hLq⟩ : ∃ y, shape.bpCode.length / wordBits shape.bpCode.length = y := ⟨_, rfl⟩
  have l2 := hu.lay2
  rw [hLq] at l2
  omega

theorem accessTable4_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices
      (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSUP rWS superWordEntryBlock) u v k ∧
      k ≤ 23 * (tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rSUP rWS superWordEntryBlock 9 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (superSlotCount shape.bpCode false) (wordBits shape.bpCode.length) _
    (fun slot => position shape.bpCode false (slot * superStride shape.bpCode.length) /
      wordBits shape.bpCode.length)
    u hA hA.r45 hA.r39 (wordBits_pos _) hA.wsW
    (by simp only [SparseDenseSelectDenseLocalEntry.baseWordIndices, superEntries, List.map_map]; rfl) hext
    (fun x hx hxr _ hslot => by
      obtain ⟨b1, b2, _⟩ := hA.posBounds hx hext
      exact superWordEntry_spec hW shape x hxr hx.r2 P0 _ _ _ hx.r1 hx.r159 rfl hx.r40 hx.r39 (wordBits_pos _)
        (hx.supS hslot) hx.pos b1 b2 hx.lenW')

theorem accessTable5_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore
      (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSUP rWS superFlagEntryBlock) u v k ∧
      k ≤ 16 * (tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rSUP rWS superFlagEntryBlock 2 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (superSlotCount shape.bpCode false) (wordBits shape.bpCode.length) _
    (fun slot => flagNat (superIsLong shape.bpCode false slot))
    u hA hA.r45 hA.r39 (wordBits_pos _) hA.wsW
    (by simp only [SparseDenseSelectDenseLocalEntry.ranksBefore, superEntries, List.map_map]; rfl) hext
    (fun x hx hxr _ hslot => by
      obtain ⟨_, _, b3, b4, _⟩ := hA.posBounds hx hext
      have h2W := two_le_two_pow hW
      exact flagEntry_spec hW rLFB x hxr L0 (superSlotCount shape.bpCode false) (x.regs 14)
        (fun k => flagNat (superIsLong shape.bpCode false k)) rfl hx.r161 hslot hx.lf b3 b4
        (fun k _ => by
          show flagNat (superIsLong shape.bpCode false k) < 2 ^ W
          have := flagNat_le (superIsLong shape.bpCode false k); omega))

theorem accessTable6_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets
      (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSUP rWS superOffsetEntryBlock) u v k ∧
      k ≤ 23 * (tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets
        (superEntries shape.bpCode false)) (superFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rSUP rWS superOffsetEntryBlock 9 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (superSlotCount shape.bpCode false) (wordBits shape.bpCode.length) _
    (fun slot => position shape.bpCode false (slot * superStride shape.bpCode.length) %
      wordBits shape.bpCode.length)
    u hA hA.r45 hA.r39 (wordBits_pos _) hA.wsW
    (by
      simp only [SparseDenseSelectDenseLocalEntry.firstOffsets, superEntries, List.map_map]
      apply List.map_congr_left
      intro k _
      exact Nat.mod_eq_sub_div_mul) hext
    (fun x hx hxr _ hslot => by
      obtain ⟨b1, b2, _⟩ := hA.posBounds hx hext
      exact superOffsetEntry_spec hW shape x hxr hx.r2 P0 _ _ _ hx.r1 hx.r159 rfl hx.r40 hx.r39
        (wordBits_pos _) (hx.supS hslot) hx.pos b1 b2 hx.lenW')

/-! ## Sources 7 to 10: the local fields -/

theorem sparseExceptionRelativeWidth_W {W : Nat} {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    {u : State} (h : AccessReady W shape P0 R0 L0 C0 F0 G0 u) :
    sparseExceptionRelativeWidth shape.bpCode < 2 ^ W := by
  have h1 := machineWordBits_le_succ (Nat.min shape.bpCode.length (superLongSpan shape.bpCode.length))
  have h2 : Nat.min shape.bpCode.length (superLongSpan shape.bpCode.length) ≤ shape.bpCode.length :=
    Nat.min_le_left _ _
  have := h.lenW
  show SuccinctRank.machineWordBits (Nat.min shape.bpCode.length (superLongSpan shape.bpCode.length)) < 2 ^ W
  omega

theorem accessTable7_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences
      (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rLOC rLW localOccEntryBlock) u v k ∧
      k ≤ 25 * (tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.baseOccurrences
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rLOC rLW localOccEntryBlock 11 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (localSlotCount shape.bpCode false) (sparseExceptionRelativeWidth shape.bpCode) _
    (fun g => (localEntry shape.bpCode false g).baseOccurrence)
    u hA hA.r46 hA.r49 (sparseExceptionRelativeWidth_pos _) (sparseExceptionRelativeWidth_W hA)
    (by simp only [SparseDenseSelectDenseLocalEntry.baseOccurrences, localEntries, List.map_map]; rfl) hext
    (fun x hx hxr _ hslot => by
      obtain ⟨_, _, b3, b4, _⟩ := hA.posBounds hx hext
      exact localOccEntry_spec hW shape x hxr hx.r2 L0 _ hx.r1 hx.r161 rfl hx.r40 hx.r42 hx.r43 hslot hx.lf
        b3 b4 hx.capS)

theorem accessTable8_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices
      (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rLOC rLW localWordEntryBlock) u v k ∧
      k ≤ 42 * (tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.baseWordIndices
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rLOC rLW localWordEntryBlock 28 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (localSlotCount shape.bpCode false) (sparseExceptionRelativeWidth shape.bpCode) _
    (fun g => (localEntry shape.bpCode false g).baseWordIndex)
    u hA hA.r46 hA.r49 (sparseExceptionRelativeWidth_pos _) (sparseExceptionRelativeWidth_W hA)
    (by simp only [SparseDenseSelectDenseLocalEntry.baseWordIndices, localEntries, List.map_map]; rfl) hext
    (fun x hx hxr _ hslot => by
      obtain ⟨b1, b2, b3, b4, _⟩ := hA.posBounds hx hext
      exact localWordEntry_spec hW shape x hxr hx.r2 P0 L0 _ hx.r1 hx.r159 hx.r161 rfl hx.r39 hx.r40 hx.r42
        hx.r43 hslot hx.lf b3 b4 hx.capS hx.pos b1 b2 hx.lenW')

theorem accessTable9_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore
      (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rLOC rLW localFlagEntryBlock) u v k ∧
      k ≤ 27 * (tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.ranksBefore
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rLOC rLW localFlagEntryBlock 13 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (localSlotCount shape.bpCode false) (sparseExceptionRelativeWidth shape.bpCode) _
    (fun g => (localEntry shape.bpCode false g).rankBefore)
    u hA hA.r46 hA.r49 (sparseExceptionRelativeWidth_pos _) (sparseExceptionRelativeWidth_W hA)
    (by simp only [SparseDenseSelectDenseLocalEntry.ranksBefore, localEntries, List.map_map]; rfl) hext
    (fun x hx hxr _ hslot => by
      obtain ⟨_, _, b3, b4, b5, b6, _⟩ := hA.posBounds hx hext
      exact localFlagEntry_spec hW shape x hxr hx.r2 L0 F0 _ hx.r1 hx.r161 hx.r163 rfl hx.r40 hx.r42 hx.r43
        hslot hx.lf b3 b4 hx.sf b5 b6 hx.capS)

theorem accessTable10_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets
      (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rLOC rLW localOffsetEntryBlock) u v k ∧
      k ≤ 33 * (tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).length + 3 ∧ v.status = .running ∧
      Emits u v ((tableBits (SparseDenseSelectDenseLocalEntry.firstOffsets
        (localEntries shape.bpCode false)) (localFieldWidth shape.bpCode)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys :=
  accessTable_generic hW rLOC rLW localOffsetEntryBlock 19 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (localSlotCount shape.bpCode false) (sparseExceptionRelativeWidth shape.bpCode) _
    (fun g => (localEntry shape.bpCode false g).firstOffset)
    u hA hA.r46 hA.r49 (sparseExceptionRelativeWidth_pos _) (sparseExceptionRelativeWidth_W hA)
    (by simp only [SparseDenseSelectDenseLocalEntry.firstOffsets, localEntries, List.map_map]; rfl) hext
    (fun x hx hxr _ hslot => by
      obtain ⟨b1, b2, b3, b4, _⟩ := hA.posBounds hx hext
      exact localOffsetEntry_spec hW shape x hxr hx.r2 P0 L0 _ hx.r1 hx.r159 hx.r161 rfl hx.r39 hx.r40 hx.r42
        hx.r43 hslot hx.lf b3 b4 hx.capS hx.pos b1 b2 hx.lenW')

/-! ## Sources 11 to 13: the long flags -/

theorem flags_tableBits_one (bs : List Bool) :
    flattenPayloadWords ((bs.map flagNat).map (natToBitsLE 1)) = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
      simp only [List.map_cons, flattenPayloadWords]
      rw [ih]
      cases b <;> rfl

theorem flagTable_eq (f : Nat → Bool) (N : Nat) :
    tableBits ((List.range N).map (fun k => flagNat (f k))) 1 = (List.range N).map f := by
  unfold tableBits
  rw [show (List.range N).map (fun k => flagNat (f k)) = ((List.range N).map f).map flagNat by
    rw [List.map_map]; rfl]
  exact flags_tableBits_one _

theorem longFlagBits_length' (shape : CartesianShape) :
    (longSuperFlagBits shape.bpCode false).length = superSlotCount shape.bpCode false :=
  longSuperFlagBits_length _ _

theorem accessTable11_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SuccinctRank.canonicalSuperRankEntries true (longSuperFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rLFR rLFW (flagRankEntryBlock rLFCB rLFW)) u v k ∧
      k ≤ 17 * (tableBits (SuccinctRank.canonicalSuperRankEntries true (longSuperFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).length + 3 ∧
      v.status = .running ∧
      Emits u v ((tableBits (SuccinctRank.canonicalSuperRankEntries true (longSuperFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hw := SuccinctRank.machineWordBits_pos (longSuperFlagBits shape.bpCode false).length
  have hlen := longFlagBits_length' shape
  obtain ⟨Q, hQ⟩ : ∃ x, (longSuperFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length = x := ⟨_, rfl⟩
  have hTlen : (tableBits (SuccinctRank.canonicalSuperRankEntries true (longSuperFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).length =
      (Q + 1) * SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length := by
    rw [tableBits_length]
    simp only [SuccinctRank.canonicalSuperRankEntries, List.length_map, List.length_range, Nat.div_one, hQ]
  have hwle := Nat.le_mul_of_pos_left (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)
    (show 0 < Q + 1 by omega)
  exact accessTable_generic hW rLFR rLFW (flagRankEntryBlock rLFCB rLFW) 3 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (Q + 1) _ _
    (fun slot => RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false)
      (slot * SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length))
    u hA (by show u.regs 54 = Q + 1; rw [hA.r54, hQ]) hA.r50 hw (by omega)
    (by simp only [SuccinctRank.canonicalSuperRankEntries, Nat.div_one, Nat.mul_one, hQ]) hext
    (by
      intro x hx hxr _ hslot
      obtain ⟨_, _, _, _, _, _, b7, b8, _⟩ := hA.posBounds hx hext
      have hslot' : x.regs 14 ≤ (longSuperFlagBits shape.bpCode false).length /
          SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length := by rw [hQ]; omega
      have hsw := Nat.le_trans ((Nat.le_div_iff_mul_le hw).1 hslot') (Nat.le_of_eq hlen)
      exact flagRankEntry_spec hW rLFCB rLFW (by decide) x hxr C0 (superSlotCount shape.bpCode false) _
        (x.regs 14) (fun k => RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) k) rfl hx.r50
        hx.r162 hsw hx.lfc b7 b8
        (fun k _ => by
          show RMQ.Succinct.rankPrefix true (longSuperFlagBits shape.bpCode false) k < 2 ^ W
          have := RMQ.Succinct.rankPrefix_le_length true (longSuperFlagBits shape.bpCode false) k
          omega))

theorem accessTable12_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SuccinctRank.canonicalBlockRankEntries true (longSuperFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rLFR rLFW zeroEntryBlock) u v k ∧
      k ≤ 15 * (tableBits (SuccinctRank.canonicalBlockRankEntries true (longSuperFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).length + 3 ∧
      v.status = .running ∧
      Emits u v ((tableBits (SuccinctRank.canonicalBlockRankEntries true (longSuperFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hw := SuccinctRank.machineWordBits_pos (longSuperFlagBits shape.bpCode false).length
  obtain ⟨Q, hQ⟩ : ∃ x, (longSuperFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length = x := ⟨_, rfl⟩
  have hTlen : (tableBits (SuccinctRank.canonicalBlockRankEntries true (longSuperFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)).length =
      (Q + 1) * SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length := by
    rw [tableBits_length]
    simp only [SuccinctRank.canonicalBlockRankEntries, List.length_map, List.length_range, hQ]
  have hwle := Nat.le_mul_of_pos_left (SuccinctRank.machineWordBits (longSuperFlagBits shape.bpCode false).length)
    (show 0 < Q + 1 by omega)
  exact accessTable_generic hW rLFR rLFW zeroEntryBlock 1 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (Q + 1) _ _ (fun _ => 0)
    u hA (by show u.regs 54 = Q + 1; rw [hA.r54, hQ]) hA.r50 hw (by omega)
    (by
      simp only [SuccinctRank.canonicalBlockRankEntries, Nat.div_one, Nat.mul_one, Nat.sub_self, hQ])
    hext
    (fun x _ hxr _ _ => zeroEntry_spec hW x hxr)

theorem accessTable13_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (longSuperFlagBits shape.bpCode false).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSUP rONE (flagEntryBlock rLFB)) u v k ∧
      k ≤ 16 * (longSuperFlagBits shape.bpCode false).length + 3 ∧ v.status = .running ∧
      Emits u v ((longSuperFlagBits shape.bpCode false).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hT := flagTable_eq (superIsLong shape.bpCode false) (superSlotCount shape.bpCode false)
  have hL : longSuperFlagBits shape.bpCode false =
      (List.range (superSlotCount shape.bpCode false)).map (superIsLong shape.bpCode false) := rfl
  rw [← hL] at hT
  have h2W := two_le_two_pow hW
  obtain ⟨v, k, ev, hk, hr, hE, hfr, hkr, hks⟩ :=
    accessTable_generic hW rSUP rONE (flagEntryBlock rLFB) 2 AccessWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
      (superSlotCount shape.bpCode false) 1 _ (fun k => flagNat (superIsLong shape.bpCode false k))
      u hA hA.r45 hA.r2 (Nat.le_refl 1) (by omega) rfl (by rw [hT]; exact hext)
      (fun x hx hxr _ hslot => by
        obtain ⟨_, _, b3, b4, _⟩ := hA.posBounds hx hext
        exact flagEntry_spec hW rLFB x hxr L0 (superSlotCount shape.bpCode false) (x.regs 14)
          (fun k => flagNat (superIsLong shape.bpCode false k)) rfl hx.r161 hslot hx.lf b3 b4
          (fun k _ => by
            show flagNat (superIsLong shape.bpCode false k) < 2 ^ W
            have := flagNat_le (superIsLong shape.bpCode false k); omega))
  rw [hT] at hk hE
  exact ⟨v, k, ev, hk, hr, hE, hfr, hkr, hks⟩

/-! ## Sources 15 to 17: the effective sparse flags -/

theorem rank_flags_take (f : Nat → Bool) {M N : Nat} (hMN : M ≤ N) :
    ∀ k, k ≤ M → RMQ.Succinct.rankPrefix true ((List.range N).map f) k =
      RMQ.Succinct.rankPrefix true ((List.range M).map f) k
  | 0, _ => by rw [RMQ.Succinct.rankPrefix_zero, RMQ.Succinct.rankPrefix_zero]
  | k + 1, hk => by
      rw [rank_flags_succ (show k < N by omega), rank_flags_succ (show k < M by omega),
        rank_flags_take f hMN k (by omega)]

theorem sparseEff_le (shape : CartesianShape) :
    (sparseExceptionEffectiveFlagBits shape.bpCode false).length ≤ localSlotCount shape.bpCode false := by
  rw [sparseExceptionEffectiveFlagBits_length]
  exact sparseExceptionEffectiveLocalSlotCount_le_full _ _

theorem sparseEff_rank (shape : CartesianShape) {k : Nat}
    (hk : k ≤ (sparseExceptionEffectiveFlagBits shape.bpCode false).length) :
    RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) k =
      RMQ.Succinct.rankPrefix true (sparseExceptionEffectiveFlagBits shape.bpCode false) k := by
  have hl := sparseExceptionEffectiveFlagBits_length shape.bpCode false
  rw [hl] at hk
  exact rank_flags_take (localIsSparseException shape.bpCode false)
    (sparseExceptionEffectiveLocalSlotCount_le_full _ _) k hk

theorem accessTable15_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SuccinctRank.canonicalSuperRankEntries true
      (sparseExceptionEffectiveFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSFR rSFW (flagRankEntryBlock rSFCB rSFW)) u v k ∧
      k ≤ 17 * (tableBits (SuccinctRank.canonicalSuperRankEntries true
        (sparseExceptionEffectiveFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).length + 3 ∧
      v.status = .running ∧
      Emits u v ((tableBits (SuccinctRank.canonicalSuperRankEntries true
        (sparseExceptionEffectiveFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).map
          SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hw := SuccinctRank.machineWordBits_pos (sparseExceptionEffectiveFlagBits shape.bpCode false).length
  have hsp := sparseEff_le shape
  obtain ⟨Q, hQ⟩ : ∃ x, (sparseExceptionEffectiveFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length = x := ⟨_, rfl⟩
  have hTlen : (tableBits (SuccinctRank.canonicalSuperRankEntries true
      (sparseExceptionEffectiveFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).length =
      (Q + 1) * SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length := by
    rw [tableBits_length]
    simp only [SuccinctRank.canonicalSuperRankEntries, List.length_map, List.length_range, Nat.div_one, hQ]
  have hwle := Nat.le_mul_of_pos_left
    (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)
    (show 0 < Q + 1 by omega)
  exact accessTable_generic hW rSFR rSFW (flagRankEntryBlock rSFCB rSFW) 3 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (Q + 1) _ _
    (fun slot => RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false)
      (slot * SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length))
    u hA (by show u.regs 55 = Q + 1; rw [hA.r55, hQ]) hA.r51 hw (by omega)
    (by
      simp only [SuccinctRank.canonicalSuperRankEntries, Nat.div_one, Nat.mul_one, hQ]
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      apply sparseEff_rank
      have hi' : i ≤ (sparseExceptionEffectiveFlagBits shape.bpCode false).length /
          SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length := by
        rw [hQ]; omega
      exact (Nat.le_div_iff_mul_le hw).1 hi') hext
    (by
      intro x hx hxr _ hslot
      obtain ⟨_, _, _, _, _, _, _, _, b9, b10⟩ := hA.posBounds hx hext
      have hslot' : x.regs 14 ≤ (sparseExceptionEffectiveFlagBits shape.bpCode false).length /
          SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length := by
        rw [hQ]; omega
      have hsw := (Nat.le_div_iff_mul_le hw).1 hslot'
      exact flagRankEntry_spec hW rSFCB rSFW (by decide) x hxr G0
        (sparseExceptionEffectiveFlagBits shape.bpCode false).length _
        (x.regs 14) (fun k => RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) k) rfl
        hx.r51 hx.r164 hsw (fun k hk => hx.sfc k (by omega)) (by omega) (by omega)
        (fun k _ => by
          show RMQ.Succinct.rankPrefix true (sparseExceptionFlagBits shape.bpCode false) k < 2 ^ W
          have := RMQ.Succinct.rankPrefix_le_length true (sparseExceptionFlagBits shape.bpCode false) k
          rw [sparseExceptionFlagBits_length] at this
          omega))

theorem accessTable16_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (tableBits (SuccinctRank.canonicalBlockRankEntries true
      (sparseExceptionEffectiveFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSFR rSFW zeroEntryBlock) u v k ∧
      k ≤ 15 * (tableBits (SuccinctRank.canonicalBlockRankEntries true
        (sparseExceptionEffectiveFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).length + 3 ∧
      v.status = .running ∧
      Emits u v ((tableBits (SuccinctRank.canonicalBlockRankEntries true
        (sparseExceptionEffectiveFlagBits shape.bpCode false)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
        (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).map
          SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hw := SuccinctRank.machineWordBits_pos (sparseExceptionEffectiveFlagBits shape.bpCode false).length
  obtain ⟨Q, hQ⟩ : ∃ x, (sparseExceptionEffectiveFlagBits shape.bpCode false).length /
      SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length = x := ⟨_, rfl⟩
  have hTlen : (tableBits (SuccinctRank.canonicalBlockRankEntries true
      (sparseExceptionEffectiveFlagBits shape.bpCode false)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length) 1)
      (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)).length =
      (Q + 1) * SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length := by
    rw [tableBits_length]
    simp only [SuccinctRank.canonicalBlockRankEntries, List.length_map, List.length_range, hQ]
  have hwle := Nat.le_mul_of_pos_left
    (SuccinctRank.machineWordBits (sparseExceptionEffectiveFlagBits shape.bpCode false).length)
    (show 0 < Q + 1 by omega)
  exact accessTable_generic hW rSFR rSFW zeroEntryBlock 1 AccessWrites
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
    (Q + 1) _ _ (fun _ => 0)
    u hA (by show u.regs 55 = Q + 1; rw [hA.r55, hQ]) hA.r51 hw (by omega)
    (by
      simp only [SuccinctRank.canonicalBlockRankEntries, Nat.div_one, Nat.mul_one, Nat.sub_self, hQ])
    hext
    (fun x _ hxr _ _ => zeroEntry_spec hW x hxr)

theorem accessTable17_spec {W : Nat} (hW : 32 ≤ W) {shape : CartesianShape} {P0 R0 L0 C0 F0 G0 : Nat}
    (u : State) (hA : AccessReady W shape P0 R0 L0 C0 F0 G0 u)
    (hext : u.extent + (sparseExceptionEffectiveFlagBits shape.bpCode false).length < 2 ^ W) :
    ∃ v k, SafeEval W (emitTable rSP rONE (flagEntryBlock rSFB)) u v k ∧
      k ≤ 16 * (sparseExceptionEffectiveFlagBits shape.bpCode false).length + 3 ∧ v.status = .running ∧
      Emits u v ((sparseExceptionEffectiveFlagBits shape.bpCode false).map SuccinctSpace.bitToNat) ∧
      (∀ r, AccessFrame r → v.regs r = u.regs r) ∧ v.keyRegs = u.keyRegs ∧ v.keys = u.keys := by
  have hsp := sparseEff_le shape
  have hT := flagTable_eq (localIsSparseException shape.bpCode false)
    (sparseExceptionEffectiveFlagBits shape.bpCode false).length
  have hL : sparseExceptionEffectiveFlagBits shape.bpCode false =
      (List.range (sparseExceptionEffectiveFlagBits shape.bpCode false).length).map
        (localIsSparseException shape.bpCode false) := by
    rw [sparseExceptionEffectiveFlagBits_length]; rfl
  rw [← hL] at hT
  have h2W := two_le_two_pow hW
  obtain ⟨v, k, ev, hk, hr, hE, hfr, hkr, hks⟩ :=
    accessTable_generic hW rSP rONE (flagEntryBlock rSFB) 2 AccessWrites
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) accessWrites_frame
      (sparseExceptionEffectiveFlagBits shape.bpCode false).length 1 _
      (fun g => flagNat (localIsSparseException shape.bpCode false g))
      u hA hA.r47 hA.r2 (Nat.le_refl 1) (by omega) rfl (by rw [hT]; exact hext)
      (fun x hx hxr _ hslot => by
        obtain ⟨_, _, _, _, b5, b6, _⟩ := hA.posBounds hx hext
        exact flagEntry_spec hW rSFB x hxr F0 (sparseExceptionEffectiveFlagBits shape.bpCode false).length
          (x.regs 14) (fun g => flagNat (localIsSparseException shape.bpCode false g)) rfl hx.r163 hslot
          (fun g hg => hx.sf g (by omega)) (by omega) (by omega)
          (fun g _ => by
            show flagNat (localIsSparseException shape.bpCode false g) < 2 ^ W
            have := flagNat_le (localIsSparseException shape.bpCode false g); omega))
  rw [hT] at hk hE
  exact ⟨v, k, ev, hk, hr, hE, hfr, hkr, hks⟩

end RMQ.SuccinctFinal.PackedConstruction.Proof
