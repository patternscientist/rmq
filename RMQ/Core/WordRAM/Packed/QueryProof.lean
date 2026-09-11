import RMQ.Core.WordRAM.Packed.QuerySource
import RMQ.Core.WordRAM.Packed.LCAProof

/-! # Ordered primitive refinement of the complete packed controller -/

namespace RMQ.SuccinctFinal.PackedWordRAM

open Cartesian Structured SuccinctSpace PackedCellProbe SuccinctClose

private theorem eval_move (memory : Memory) (regs : Registers) (dst src : Nat) :
    (Block.action (.move dst src)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (regs src), .running⟩, []⟩ := rfl

private theorem eval_constant (memory : Memory) (regs : Registers) (dst value : Nat) :
    (Block.action (.constant dst value)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst value, .running⟩, []⟩ := rfl

private theorem eval_arithmetic (memory : Memory) (regs : Registers)
    (op : Arithmetic) (dst lhs rhs : Nat) :
    (Block.action (.arithmetic op dst lhs rhs)).eval memory ⟨regs, .running⟩ =
      ⟨⟨regs.write dst (op.eval (regs lhs) (regs rhs)), .running⟩, []⟩ := rfl

private theorem eval_skip (memory : Memory) (regs : Registers) :
    Block.skip.eval memory ⟨regs, .running⟩ = ⟨⟨regs, .running⟩, []⟩ := rfl

private theorem eval_ifZero (memory : Memory) (regs : Registers) (condition : Nat)
    (zero nonzero : Block) :
    (Block.ifZero condition zero nonzero).eval memory ⟨regs, .running⟩ =
      if regs condition = 0 then zero.eval memory ⟨regs, .running⟩
      else nonzero.eval memory ⟨regs, .running⟩ := rfl

private theorem eval_seq_of_results (memory : Memory) (first second : Block) (s : Data)
    (a b : Evaluation) (ha : first.eval memory s = a)
    (hb : second.eval memory a.final = b) :
    (Block.seq first second).eval memory s = ⟨b.final, a.reads ++ b.reads⟩ := by
  rw [Block.eval_seq, ha]
  simp only [Evaluation.bind, hb]

def queryAfterLCAReference (store : WordRAM.ReadStore) (n : Nat) :
    Option Nat → WordRAM.TraceResult (Option Nat)
  | none => WordRAM.TraceResult.pure none
  | some close => (packedRankCloseLeaf store n (close + 1)).map (fun rank => some (rank - 1))

def queryAfterSelectsReference (store : WordRAM.ReadStore) (n : Nat) :
    Option Nat → Option Nat → WordRAM.TraceResult (Option Nat)
  | some left, some right => (packedLcaCloseLeaf store n left right).bind (queryAfterLCAReference store n)
  | _, _ => WordRAM.TraceResult.pure none

def queryReadyReference (store : WordRAM.ReadStore) (n left right : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (packedSelectCloseLeaf store n left).bind fun lc =>
    (packedSelectCloseLeaf store n (right - 1)).bind (queryAfterSelectsReference store n lc)

theorem queryReadyReference_eq_packedWholeQueryRun (store : WordRAM.ReadStore) (n left right : Nat) :
    queryReadyReference store n left right = packedWholeQueryRun store n left right := by
  cases hl : (packedSelectCloseLeaf store n left).value with
  | none =>
      cases hr : (packedSelectCloseLeaf store n (right - 1)).value <;>
        simp [queryReadyReference, queryAfterSelectsReference,
          packedWholeQueryRun, concreteBPNativeSuccinctRMQWholeQueryProgram, packedProgramRun,
          packedInstrStep, WholeQueryState.empty, WholeQueryState.setOpt,
          WholeQueryState.opt, WholeQueryNatExpr.eval,
          WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
          hl, hr]
  | some lc =>
      cases hr : (packedSelectCloseLeaf store n (right - 1)).value with
      | none =>
          simp [queryReadyReference, queryAfterSelectsReference,
            packedWholeQueryRun, concreteBPNativeSuccinctRMQWholeQueryProgram, packedProgramRun,
            packedInstrStep, WholeQueryState.empty, WholeQueryState.setOpt,
            WholeQueryState.opt, WholeQueryNatExpr.eval,
            WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
            hl, hr]
      | some rc =>
          cases ha : (packedLcaCloseLeaf store n lc rc).value <;>
            simp [queryReadyReference, queryAfterSelectsReference, queryAfterLCAReference,
              packedWholeQueryRun, concreteBPNativeSuccinctRMQWholeQueryProgram, packedProgramRun,
              packedInstrStep, WholeQueryState.empty, WholeQueryState.setOpt, WholeQueryState.setNat,
              WholeQueryState.opt, WholeQueryState.nat, WholeQueryNatExpr.eval,
              WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
              hl, hr, ha]

theorem queryRankFinishBlock_writes : queryRankFinishBlock.WritesOnly (fun r => r = 3 ∨ r = 2051) := by
  simp [queryRankFinishBlock, natSubBlock, Block.WritesOnly, Action.destination]

theorem queryRankFinishBlock_source (memory : Memory) (regs : Registers) (hone : regs 2048 = 1) :
    let actual := queryRankFinishBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 3 = regs 360 - 1 + 1 := by
  have hsub (r : Registers) := natSubBlock_source 3 360 2048 2051 memory r (by decide) (by decide)
  simp [queryRankFinishBlock, Block.eval_seq, Evaluation.bind, hsub, eval_arithmetic,
    Arithmetic.eval, Registers.write, hone]

def QueryFinalRankWrites (r : Nat) : Prop := r = 352 ∨ RankWrapperWrites r ∨ r = 3 ∨ r = 2051

theorem queryFinalRankBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (queryFinalRankBlock reader).WritesOnly QueryFinalRankWrites := by
  refine ⟨Or.inl rfl, Block.WritesOnly.mono _ (rankCloseBlock_writes reader hwrites) ?_,
    Block.WritesOnly.mono _ queryRankFinishBlock_writes ?_⟩
  · intro r h; exact Or.inr (Or.inl h)
  · intro r h; exact Or.inr (Or.inr h)

theorem queryFinalRankBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 2048 = 1) :
    let expected := (packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1202)).map (fun rank => some (rank - 1))
    let actual := (queryFinalRankBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 352 (regs 1202)
  have hpm : MetadataMatches shape prepared := MetadataMatches.write shape regs hm 352 _ (Or.inr (by decide))
  have hr := rankCloseBlock_source shape memory reader hreader hwrites prepared hpm
  have hrf := rankCloseBlock_frame reader hwrites memory ⟨prepared, .running⟩ 2048
    (by simp [RankWrapperWrites])
  generalize her : (rankCloseBlock reader).eval memory ⟨prepared, .running⟩ = ranked at hr hrf
  rcases ranked with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr hrf
  obtain ⟨hrst, hrvalue, hrreads, hrreadonly⟩ := hr
  subst rst
  have hf := queryRankFinishBlock_source memory rr (hrf.trans hone)
  generalize hef : queryRankFinishBlock.eval memory ⟨rr, .running⟩ = finished at hf
  rcases finished with ⟨⟨fr, fst⟩, freads⟩
  dsimp only at hf
  obtain ⟨hfst, hfreads, hfvalue⟩ := hf
  subst fst
  subst freads
  have htail := eval_seq_of_results memory (rankCloseBlock reader) queryRankFinishBlock
    ⟨prepared, .running⟩ ⟨⟨rr, .running⟩, rreads⟩ ⟨⟨fr, .running⟩, []⟩ her hef
  simp only [List.append_nil] at htail
  have hwhole := eval_seq_of_results memory (.action (.move 352 1202))
    (.seq (rankCloseBlock reader) queryRankFinishBlock)
    ⟨regs, .running⟩ ⟨⟨prepared, .running⟩, []⟩ ⟨⟨fr, .running⟩, rreads⟩ rfl htail
  simp only [List.nil_append] at hwhole
  change (queryFinalRankBlock reader).eval memory ⟨regs, .running⟩ = _ at hwhole
  rw [hwhole]
  dsimp only
  simp only [prepared, Registers.write] at hrvalue hrreads hrreadonly
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa only [WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
      optionNatPacket, Option.map_some, Option.getD_some, hrvalue] using hfvalue
  · simpa only [WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
      List.append_nil] using hrreads
  · simpa only [WordRAM.TraceResult.map, WordRAM.TraceResult.bind, WordRAM.TraceResult.pure,
      List.append_nil] using hrreadonly

theorem queryAfterLCABlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 2048 = 1)
    (hzero : regs 3 = 0) (answer : Option Nat) (hanswer : regs 1202 = optionNatPacket answer) :
    let expected := queryAfterLCAReference (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size answer
    let actual := (queryAfterLCABlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  cases answer with
  | none =>
      simp only [optionNatPacket, Option.map_none, Option.getD_none] at hanswer
      simp [queryAfterLCABlock, eval_ifZero, hanswer, eval_skip, queryAfterLCAReference,
        WordRAM.TraceResult.pure, hzero, optionNatPacket, logicalTraceReads, ReadOnlyTrace]
  | some close =>
      have hs := queryFinalRankBlock_source shape memory reader hreader hwrites regs hm hone
      have heq : regs 1202 = close + 1 := hanswer
      have hn : regs 1202 ≠ 0 := by omega
      rw [queryAfterLCABlock, eval_ifZero, if_neg hn]
      simpa only [queryAfterLCAReference, heq] using hs

def LCACorrect (shape : CartesianShape) (memory : Memory) (lca : Block) : Prop :=
  ∀ regs : Registers, MetadataMatches shape regs →
    let expected := packedLcaCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 1200) (regs 1201)
    let actual := lca.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 1202 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace

private theorem lca_preserves_query (r : Nat)
    (hr : r < 190 ∨ r = 2048 ∨ r = 2049 ∨ r = 2050) : ¬ LCACloseWrites r := by
  unfold LCACloseWrites LCAChooseWrites LCACrossWrites LCALeftWrites LCAMiddleWrites
    LCAMergeSaveWrites LCARightWrites LCASameWrites LCAPrepareWrites LCAInteriorWrites
    FringeWrites FringeSeedWrites RankWrapperWrites FringeWindowWrites WindowWrites FringeFoldWrites
  omega

theorem queryAnswerPrepareBlock_writes :
    queryAnswerPrepareBlock.WritesOnly (fun r => r = 1200 ∨ r = 1201 ∨ r = 2051) := by
  simp [queryAnswerPrepareBlock, natSubBlock, Block.WritesOnly, Action.destination]

theorem queryAnswerPrepareBlock_source (memory : Memory) (regs : Registers) (hone : regs 2048 = 1) :
    let actual := queryAnswerPrepareBlock.eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.reads = [] ∧
      actual.final.regs 1200 = regs 2049 - 1 ∧ actual.final.regs 1201 = regs 2050 - 1 := by
  have ha (r : Registers) := natSubBlock_source 1200 2049 2048 2051 memory r (by decide) (by decide)
  have hb (r : Registers) := natSubBlock_source 1201 2050 2048 2051 memory r (by decide) (by decide)
  simp [queryAnswerPrepareBlock, Block.eval_seq, Evaluation.bind, ha, hb, Registers.write, hone]

def QueryAnswerWrites (r : Nat) : Prop :=
  r = 1200 ∨ r = 1201 ∨ r = 2051 ∨ LCACloseWrites r ∨ QueryFinalRankWrites r

theorem queryAnswerProgram_writes (reader lca : Block) (hwrites : ReaderWrites reader)
    (hlwrites : lca.WritesOnly LCACloseWrites) :
    (queryAnswerProgram reader lca).WritesOnly QueryAnswerWrites := by
  refine ⟨Block.WritesOnly.mono _ queryAnswerPrepareBlock_writes ?_,
    Block.WritesOnly.mono _ hlwrites ?_, True.intro,
    Block.WritesOnly.mono _ (queryFinalRankBlock_writes reader hwrites) ?_⟩
  · intro r h; unfold QueryAnswerWrites; omega
  · intro r h; exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · intro r h; exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem queryAnswerProgram_source (shape : CartesianShape) (memory : Memory) (reader lca : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hlca : LCACorrect shape memory lca) (hlwrites : lca.WritesOnly LCACloseWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 2048 = 1) (hzero : regs 3 = 0)
    (left right : Nat) (hleft : regs 2049 = left + 1) (hright : regs 2050 = right + 1) :
    let expected := (packedLcaCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size left right).bind (queryAfterLCAReference (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size)
    let actual := (queryAnswerProgram reader lca).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hp := queryAnswerPrepareBlock_source memory regs hone
  have hpf (r : Nat) (ho : r ≠ 1200 ∧ r ≠ 1201 ∧ r ≠ 2051) :=
    Block.eval_frame memory _ _ queryAnswerPrepareBlock_writes r (by omega) ⟨regs, .running⟩
  generalize hep : queryAnswerPrepareBlock.eval memory ⟨regs, .running⟩ = prepared at hp hpf
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hpf
  obtain ⟨hpst, hpreads, hpl, hpr⟩ := hp
  subst pst
  subst preads
  have hpl' : pr 1200 = left := by simpa only [hleft, Nat.add_sub_cancel] using hpl
  have hpr' : pr 1201 = right := by simpa only [hright, Nat.add_sub_cancel] using hpr
  have hpm : MetadataMatches shape pr := by
    intro i hi; rw [hpf _ (by omega)]; exact hm i hi
  have hl := hlca pr hpm
  have hlf (r : Nat) (hr : r < 190 ∨ r = 2048 ∨ r = 2049 ∨ r = 2050) :=
    Block.eval_frame memory lca _ hlwrites r (lca_preserves_query r hr) ⟨pr, .running⟩
  generalize hel : lca.eval memory ⟨pr, .running⟩ = lcaRun at hl hlf
  rcases lcaRun with ⟨⟨lr, lst⟩, lreads⟩
  dsimp only at hl hlf
  obtain ⟨hlst, hlvalue, hlreads, hlreadonly⟩ := hl
  subst lst
  have hlm : MetadataMatches shape lr := by
    intro i hi; rw [hlf _ (Or.inl (by omega))]; exact hpm i hi
  have ha := queryAfterLCABlock_source shape memory reader hreader hwrites lr hlm
    ((hlf 2048 (by simp)).trans ((hpf 2048 (by decide)).trans hone))
    ((hlf 3 (by decide)).trans ((hpf 3 (by decide)).trans hzero))
    _ hlvalue
  generalize hea : (queryAfterLCABlock reader).eval memory ⟨lr, .running⟩ = answered at ha
  rcases answered with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha
  obtain ⟨hast, havalue, hareads, hareadonly⟩ := ha
  subst ast
  have htail := eval_seq_of_results memory lca (queryAfterLCABlock reader)
    ⟨pr, .running⟩ ⟨⟨lr, .running⟩, lreads⟩ ⟨⟨ar, .running⟩, areads⟩ hel hea
  have hwhole := eval_seq_of_results memory queryAnswerPrepareBlock (.seq lca (queryAfterLCABlock reader))
    ⟨regs, .running⟩ ⟨⟨pr, .running⟩, []⟩ ⟨⟨ar, .running⟩, lreads ++ areads⟩ hep htail
  simp only [List.nil_append] at hwhole
  change (queryAnswerProgram reader lca).eval memory ⟨regs, .running⟩ = _ at hwhole
  rw [hwhole]
  dsimp only
  simp only [hpl', hpr'] at havalue hlreads hareads hlreadonly hareadonly
  refine ⟨rfl, havalue, ?_, ?_⟩
  · simp only [WordRAM.TraceResult.bind, rank_logicalTraceReads_append]
    rw [hlreads, hareads]
  · simp only [WordRAM.TraceResult.bind, ReadOnlyTrace, List.mem_append]
    intro e he
    rcases he with he | he
    · exact hlreadonly e he
    · exact hareadonly e he

theorem queryAfterSelectsProgram_source (shape : CartesianShape) (memory : Memory) (reader lca : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hlca : LCACorrect shape memory lca) (hlwrites : lca.WritesOnly LCACloseWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 2048 = 1) (hzero : regs 3 = 0)
    (left right : Option Nat) (hleft : regs 2049 = optionNatPacket left)
    (hright : regs 2050 = optionNatPacket right) :
    let expected := queryAfterSelectsReference (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size left right
    let actual := (queryAfterSelectsProgram reader lca).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  cases left with
  | none =>
      cases right <;>
        simp [queryAfterSelectsProgram, eval_ifZero, hleft, optionNatPacket, eval_skip,
          queryAfterSelectsReference, WordRAM.TraceResult.pure, hzero, logicalTraceReads, ReadOnlyTrace]
  | some lc =>
      have hl : regs 2049 = lc + 1 := hleft
      have hln : regs 2049 ≠ 0 := by omega
      cases right with
      | none =>
          simp [queryAfterSelectsProgram, eval_ifZero, hln, hright, optionNatPacket, eval_skip,
            queryAfterSelectsReference, WordRAM.TraceResult.pure, hzero, logicalTraceReads, ReadOnlyTrace]
      | some rc =>
          have hr : regs 2050 = rc + 1 := hright
          have hrn : regs 2050 ≠ 0 := by omega
          rw [queryAfterSelectsProgram, eval_ifZero, if_neg hln, eval_ifZero, if_neg hrn]
          exact queryAnswerProgram_source shape memory reader lca hreader hwrites hlca hlwrites
            regs hm hone hzero lc rc hl hr

def QuerySelectPrepareWrites (r : Nat) : Prop := r = 512 ∨ r = 2051

private theorem preparedSelect_source (shape : CartesianShape) (memory : Memory) (reader prepare : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hpwrites : prepare.WritesOnly QuerySelectPrepareWrites) (regs : Registers)
    (hm : MetadataMatches shape regs) (request output : Nat)
    (hp : let actual := prepare.eval memory ⟨regs, .running⟩
      actual.final.status = .running ∧ actual.reads = [] ∧ actual.final.regs 512 = request) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size request
    let actual := (Block.seq prepare (.seq (selectCloseBlock reader) (.action (.move output 513)))).eval
      memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs output = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hpf (r : Nat) (ho : ¬ QuerySelectPrepareWrites r) :=
    Block.eval_frame memory prepare _ hpwrites r ho ⟨regs, .running⟩
  generalize hep : prepare.eval memory ⟨regs, .running⟩ = prepared at hp hpf
  rcases prepared with ⟨⟨pr, pst⟩, preads⟩
  dsimp only at hp hpf
  obtain ⟨hpst, hpreads, hpindex⟩ := hp
  subst pst
  subst preads
  have hpm : MetadataMatches shape pr := by
    intro i hi; rw [hpf _ (by unfold QuerySelectPrepareWrites; omega)]; exact hm i hi
  have hs := selectCloseBlock_source shape memory reader hreader hwrites pr hpm
  generalize hes : (selectCloseBlock reader).eval memory ⟨pr, .running⟩ = selected at hs
  rcases selected with ⟨⟨sr, sst⟩, sreads⟩
  dsimp only at hs
  obtain ⟨hsst, hsvalue, hsreads, hsreadonly⟩ := hs
  subst sst
  rw [Block.eval_seq, hep]
  dsimp only [Evaluation.bind]
  rw [Block.eval_seq, hes]
  simp only [Evaluation.bind, eval_move, Registers.write, List.nil_append, List.append_nil]
  simp only [hpindex] at hsvalue hsreads hsreadonly
  exact ⟨True.intro, hsvalue, hsreads, hsreadonly⟩

def QueryLeftSelectWrites (r : Nat) : Prop := r = 512 ∨ SelectWrites r ∨ r = 2049

theorem queryLeftSelectBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (queryLeftSelectBlock reader).WritesOnly QueryLeftSelectWrites :=
  ⟨Or.inl rfl, Block.WritesOnly.mono _ (selectCloseBlock_writes reader hwrites)
    (by intro r h; exact Or.inr (Or.inl h)), Or.inr (Or.inr rfl)⟩

theorem queryLeftSelectBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 0)
    let actual := (queryLeftSelectBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 2049 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace :=
  preparedSelect_source shape memory reader (.action (.move 512 0)) hreader hwrites (Or.inl rfl)
    regs hm (regs 0) 2049 (by simp [eval_move, Registers.write])

def QueryRightSelectWrites (r : Nat) : Prop := r = 512 ∨ r = 2051 ∨ SelectWrites r ∨ r = 2050

theorem queryRightSelectBlock_writes (reader : Block) (hwrites : ReaderWrites reader) :
    (queryRightSelectBlock reader).WritesOnly QueryRightSelectWrites := by
  refine ⟨?_, Block.WritesOnly.mono _ (selectCloseBlock_writes reader hwrites) ?_, ?_⟩
  · simp [natSubBlock, Block.WritesOnly, Action.destination, QueryRightSelectWrites]
  · intro r h; exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem queryRightSelectBlock_source (shape : CartesianShape) (memory : Memory) (reader : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 2048 = 1) :
    let expected := packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 1 - 1)
    let actual := (queryRightSelectBlock reader).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 2050 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  apply preparedSelect_source shape memory reader (natSubBlock 512 1 2048 2051) hreader hwrites
    (by simp [natSubBlock, Block.WritesOnly, Action.destination, QuerySelectPrepareWrites])
    regs hm (regs 1 - 1) 2050
  rw [natSubBlock_source 512 1 2048 2051 memory regs (by decide) (by decide)]
  simp [Registers.write, hone]

theorem querySelectedProgram_source (shape : CartesianShape) (memory : Memory) (reader lca : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hlca : LCACorrect shape memory lca) (hlwrites : lca.WritesOnly LCACloseWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hone : regs 2048 = 1) (hzero : regs 3 = 0) :
    let expected := queryReadyReference (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 0) (regs 1)
    let actual := (querySelectedProgram reader lca).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hl := queryLeftSelectBlock_source shape memory reader hreader hwrites regs hm
  have hlf (r : Nat) (ho : ¬ QueryLeftSelectWrites r) :=
    Block.eval_frame memory _ _ (queryLeftSelectBlock_writes reader hwrites) r ho ⟨regs, .running⟩
  generalize hel : (queryLeftSelectBlock reader).eval memory ⟨regs, .running⟩ = leftRun at hl hlf
  rcases leftRun with ⟨⟨lr, lst⟩, lreads⟩
  dsimp only at hl hlf
  obtain ⟨hlst, hlvalue, hlreads, hlreadonly⟩ := hl
  subst lst
  have hlkeep (r : Nat) (hr : r < 190 ∨ r = 2048) : lr r = regs r :=
    hlf r (by unfold QueryLeftSelectWrites SelectWrites; omega)
  have hlm : MetadataMatches shape lr := by
    intro i hi; rw [hlkeep _ (Or.inl (by omega))]; exact hm i hi
  have hr := queryRightSelectBlock_source shape memory reader hreader hwrites lr hlm
    ((hlkeep 2048 (by simp)).trans hone)
  have hrf (r : Nat) (ho : ¬ QueryRightSelectWrites r) :=
    Block.eval_frame memory _ _ (queryRightSelectBlock_writes reader hwrites) r ho ⟨lr, .running⟩
  generalize her : (queryRightSelectBlock reader).eval memory ⟨lr, .running⟩ = rightRun at hr hrf
  rcases rightRun with ⟨⟨rr, rst⟩, rreads⟩
  dsimp only at hr hrf
  obtain ⟨hrst, hrvalue, hrreads, hrreadonly⟩ := hr
  subst rst
  have hrkeep (r : Nat) (hr : r < 190 ∨ r = 2048) : rr r = regs r :=
    (hrf r (by unfold QueryRightSelectWrites SelectWrites; omega)).trans (hlkeep r hr)
  have hrm : MetadataMatches shape rr := by
    intro i hi; rw [hrkeep _ (Or.inl (by omega))]; exact hm i hi
  have hrleft : rr 2049 = optionNatPacket
      (packedSelectCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 0)).value :=
    (hrf 2049 (by simp [QueryRightSelectWrites, SelectWrites])).trans hlvalue
  have ha := queryAfterSelectsProgram_source shape memory reader lca hreader hwrites hlca hlwrites rr hrm
    ((hrkeep 2048 (by simp)).trans hone) ((hrkeep 3 (by decide)).trans hzero)
    _ _ hrleft hrvalue
  generalize hea : (queryAfterSelectsProgram reader lca).eval memory ⟨rr, .running⟩ = answered at ha
  rcases answered with ⟨⟨ar, ast⟩, areads⟩
  dsimp only at ha
  obtain ⟨hast, havalue, hareads, hareadonly⟩ := ha
  subst ast
  have htail := eval_seq_of_results memory (queryRightSelectBlock reader) (queryAfterSelectsProgram reader lca)
    ⟨lr, .running⟩ ⟨⟨rr, .running⟩, rreads⟩ ⟨⟨ar, .running⟩, areads⟩ her hea
  have hwhole := eval_seq_of_results memory (queryLeftSelectBlock reader)
    (.seq (queryRightSelectBlock reader) (queryAfterSelectsProgram reader lca))
    ⟨regs, .running⟩ ⟨⟨lr, .running⟩, lreads⟩ ⟨⟨ar, .running⟩, rreads ++ areads⟩ hel htail
  change (querySelectedProgram reader lca).eval memory ⟨regs, .running⟩ = _ at hwhole
  rw [hwhole]
  dsimp only
  simp only [hlkeep 1 (by decide)] at hrreads hrreadonly havalue hareads hareadonly
  refine ⟨rfl, havalue, ?_, ?_⟩
  · simp only [queryReadyReference, WordRAM.TraceResult.bind, rank_logicalTraceReads_append]
    rw [hlreads, hrreads, hareads]
  · simp only [queryReadyReference, WordRAM.TraceResult.bind, ReadOnlyTrace, List.mem_append]
    intro e he
    rcases he with he | he | he
    · exact hlreadonly e he
    · exact hrreadonly e he
    · exact hareadonly e he

theorem queryReadyProgram_source (shape : CartesianShape) (memory : Memory) (reader lca : Block)
    (hreader : ReaderCorrect shape memory reader) (hwrites : ReaderWrites reader)
    (hlca : LCACorrect shape memory lca) (hlwrites : lca.WritesOnly LCACloseWrites)
    (regs : Registers) (hm : MetadataMatches shape regs) (hzero : regs 3 = 0) :
    let expected := packedWholeQueryRun (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 0) (regs 1)
    let actual := (queryReadyProgram reader lca).eval memory ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := regs.write 2048 1
  have h := querySelectedProgram_source shape memory reader lca hreader hwrites hlca hlwrites
    prepared (MetadataMatches.write shape regs hm 2048 1 (Or.inr (by decide))) rfl hzero
  generalize he : (querySelectedProgram reader lca).eval memory ⟨prepared, .running⟩ = selected at h
  rcases selected with ⟨⟨sr, sst⟩, sreads⟩
  dsimp only at h
  have hwhole := eval_seq_of_results memory (.action (.constant 2048 1)) (querySelectedProgram reader lca)
    ⟨regs, .running⟩ ⟨⟨prepared, .running⟩, []⟩ ⟨⟨sr, sst⟩, sreads⟩ rfl he
  simp only [List.nil_append] at hwhole
  change (queryReadyProgram reader lca).eval memory ⟨regs, .running⟩ = _ at hwhole
  rw [hwhole]
  simpa only [prepared, Registers.write, reduceIte, queryReadyReference_eq_packedWholeQueryRun] using h

theorem queryBody_source_with_lca (shape : CartesianShape)
    (hlca : LCACorrect shape (shapeMemory shape) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (regs : Registers) (hzero : regs 3 = 0) :
    let expected := packedWholeQueryRun (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 0) (regs 1)
    let actual := queryBody.eval (shapeMemory shape) ⟨regs, .running⟩
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
        logicalTraceReads shape (shapeMemory shape) expected.trace ∧ ReadOnlyTrace expected.trace := by
  have hs := shapeMemory_setup shape ⟨regs, .running⟩ rfl
  generalize hes : metadataSetupBlock.eval (shapeMemory shape) ⟨regs, .running⟩ = setupRun at hs
  rcases setupRun with ⟨⟨sr, sst⟩, sreads⟩
  dsimp only at hs
  obtain ⟨hsst, hsm, _, hsf, hsreads⟩ := hs
  subst sst
  have hq := queryReadyProgram_source shape (shapeMemory shape) logicalReadBlock (lcaCloseBlock logicalReadBlock)
    (logicalReadBlock_correct shape) logicalReadBlock_writesOnly hlca hlwrites sr hsm
    ((hsf 3 (by decide) (Or.inl (by decide))).trans hzero)
  generalize heq : (queryReadyProgram logicalReadBlock (lcaCloseBlock logicalReadBlock)).eval
    (shapeMemory shape) ⟨sr, .running⟩ = queried at hq
  rcases queried with ⟨⟨qr, qst⟩, qreads⟩
  dsimp only at hq
  obtain ⟨hqst, hqvalue, hqreads, hqreadonly⟩ := hq
  subst qst
  have heval := eval_seq_of_results (shapeMemory shape) metadataSetupBlock
    (queryReadyProgram logicalReadBlock (lcaCloseBlock logicalReadBlock))
    ⟨regs, .running⟩ ⟨⟨sr, .running⟩, sreads⟩ ⟨⟨qr, .running⟩, qreads⟩ hes heq
  change queryBody.eval (shapeMemory shape) ⟨regs, .running⟩ = _ at heval
  rw [heval]
  dsimp only
  simp only [hsf 0 (by decide) (Or.inl (by decide)), hsf 1 (by decide) (Or.inl (by decide))]
    at hqvalue hqreads hqreadonly
  exact ⟨rfl, hqvalue, by rw [hsreads, hqreads], hqreadonly⟩

theorem guardedBlock_valid_source (body : Block) (memory : Memory) (regs : Registers)
    (hlt : regs 0 < regs 1) (hle : regs 1 ≤ regs 2) :
    (guardedBlock body).eval memory ⟨regs, .running⟩ =
      body.eval memory ⟨((regs.write 3 0).write 4 1).write 5 1, .running⟩ := by
  have hcmp (r : Registers) (op : Comparison) (dst lhs rhs : Nat) :
      (Block.action (.comparison op dst lhs rhs)).eval memory ⟨r, .running⟩ =
        ⟨⟨r.write dst (op.eval (r lhs) (r rhs)), .running⟩, []⟩ := rfl
  simp [guardedBlock, Block.eval_seq, eval_constant, eval_ifZero, hcmp, Evaluation.bind,
    Comparison.eval, Registers.write, hlt, hle]

theorem querySource_valid_with_lca (shape : CartesianShape)
    (hlca : LCACorrect shape (shapeMemory shape) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (left right : Nat) (hlt : left < right) (hle : right ≤ shape.size) :
    let expected := packedWholeQueryRun (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size left right
    let actual := querySource.eval (shapeMemory shape) (Data.ofState (initialState shape.size left right))
    actual.final.status = .running ∧ actual.final.regs 3 = optionNatPacket expected.value ∧
      actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
        logicalTraceReads shape (shapeMemory shape) expected.trace ∧ ReadOnlyTrace expected.trace := by
  let prepared := (((inputRegisters shape.size left right).write 3 0).write 4 1).write 5 1
  have h := queryBody_source_with_lca shape hlca hlwrites prepared (by simp [prepared, Registers.write])
  have heval : querySource.eval (shapeMemory shape) (Data.ofState (initialState shape.size left right)) =
      queryBody.eval (shapeMemory shape) ⟨prepared, .running⟩ :=
    guardedBlock_valid_source queryBody (shapeMemory shape) (inputRegisters shape.size left right)
      (by simpa using hlt) (by simpa using hle)
  rw [heval]
  have hlp : prepared 0 = left := by simp [prepared, Registers.write]
  have hrp : prepared 1 = right := by simp [prepared, Registers.write]
  simpa only [hlp, hrp] using h

theorem queryRun_valid_with_lca (shape : CartesianShape)
    (hlca : LCACorrect shape (shapeMemory shape) (lcaCloseBlock logicalReadBlock))
    (hlwrites : (lcaCloseBlock logicalReadBlock).WritesOnly LCACloseWrites)
    (left right : Nat) (hlt : left < right) (hle : right ≤ shape.size) :
    let expected := packedWholeQueryRun (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size left right
    let actual := queryRun (shapeMemory shape) shape.size left right
    actual.result = some (optionNatPacket expected.value) ∧
      actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
        logicalTraceReads shape (shapeMemory shape) expected.trace ∧
      actual.steps ≤ queryBudget ∧ ReadOnlyTrace expected.trace := by
  have hs := querySource_valid_with_lca shape hlca hlwrites left right hlt hle
  have hc := queryRun_refines_source (shapeMemory shape) shape.size left right
  dsimp only at hs hc ⊢
  rw [hs.1] at hc
  exact ⟨hc.1.trans (congrArg some hs.2.1), hc.2.1.trans hs.2.2.1, hc.2.2, hs.2.2.2⟩

end RMQ.SuccinctFinal.PackedWordRAM
