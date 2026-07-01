# Word-RAM Register/Control-Flow Plan

Snapshot: 2026-07-01.

This note records the next hardening step after the current leaf-interpreted
Word-RAM capstones.  The goal is not a broad compiler project.  The goal is a
minimal first-order register/control-flow layer that can express dynamic query
addresses for compact BP close/LCA, then climb toward a flatter final RMQ
capstone and the compressed/FID rank/select surface.

## Current State

The existing `RMQ.WordRAM.Program` is already a useful anti-oracle layer:

- programs are first-order syntax;
- evaluation computes value and trace together;
- `Result.toCosted` derives cost from trace length;
- every `readWord` event agrees with `Store.readWord?`;
- word-bound facts propagate from payload memory to trace events; and
- program evaluation is extensional in the payload-read interface.

The current public interpreted RMQ and rank/select theorem surfaces are
leaf-interpreted.  Payload table reads, stored-word rank leaves, and word-local
select leaves run through `WordRAM.Program`, but the outer query shape is still
sequenced by Lean-level `Costed.bind` and `match`.

The specific missing pattern is dynamic addressing:

1. read or compute a query value;
2. store it in a register;
3. branch on whether it exists;
4. compute a later payload address from it; and
5. perform the later payload read inside the same first-order syntax.

## Minimal Core Extension

Add a separate role module, rather than widening the existing expression-like
`Program` in place immediately:

```text
RMQ/Core/WordRAM/Register.lean
```

The first version should be deliberately small.

### Register State

Use a typed but simple register file:

```lean
structure RegFile where
  natRegs : Array Nat
  boolRegs : Array Bool
  optNatRegs : Array (Option Nat)
  optWordRegs : Array (Option Word)
```

Missing register reads should return a fixed default (`0`, `false`, or `none`)
so evaluation is total.  The default behavior must be documented and reflected
in the refinement theorems.

### First-Order Expressions

Use syntax, not Lean callbacks:

```lean
inductive NatExpr
  | const : Nat -> NatExpr
  | reg : Nat -> NatExpr
  | add : NatExpr -> NatExpr -> NatExpr
  | sub : NatExpr -> NatExpr -> NatExpr
  | mul : NatExpr -> NatExpr -> NatExpr
  | div : NatExpr -> NatExpr -> NatExpr
  | min : NatExpr -> NatExpr -> NatExpr

inductive BoolExpr
  | const : Bool -> BoolExpr
  | eq : NatExpr -> NatExpr -> BoolExpr
  | lt : NatExpr -> NatExpr -> BoolExpr

inductive OptNatExpr
  | const : Option Nat -> OptNatExpr
  | reg : Nat -> OptNatExpr
```

Arithmetic is zero-cost in the first pass, matching the current model
convention for index arithmetic.  If we later want counted arithmetic, this
layer is the right place to add it.

### Commands

The command language should have no loops and no higher-order continuations:

```lean
inductive Cmd
  | setNat : Nat -> NatExpr -> Cmd
  | setBool : Nat -> BoolExpr -> Cmd
  | setOptNat : Nat -> OptNatExpr -> Cmd
  | readWord : Nat -> Nat -> NatExpr -> Cmd
  | readNat : Nat -> Nat -> Nat -> NatExpr -> Cmd
  | readOptionNat : Nat -> Nat -> Nat -> NatExpr -> Cmd
  | readJoinedOptionNat : Nat -> Nat -> Nat -> NatExpr -> Cmd
  | wordRank : Nat -> Bool -> NatExpr -> Nat -> Cmd
  | wordSelect : Nat -> Bool -> NatExpr -> Nat -> Cmd
  | ifBool : BoolExpr -> List Cmd -> List Cmd -> Cmd
  | ifSomeNat : Nat -> List Cmd -> List Cmd -> Cmd
```

Here `readWord dst segment indexExpr` writes `optWordRegs[dst]`.
`readNat dst segment width indexExpr` reads a payload word, decodes it as a
fixed-width natural, and writes `optNatRegs[dst]`.
`readOptionNat` writes an `Option (Option Nat)` only if the register universe
is extended for it; otherwise the first pass can use `readJoinedOptionNat`,
which decodes a fixed-width optional natural and joins the outer indexed-read
option into an `Option Nat`.  This is a decoding instruction, not a semantic
query primitive.

Do not add:

- whole-bitvector rank/select;
- BP close, LCA, rmM, or RMQ primitives;
- `scanWindow`;
- Cartesian-shape lookup;
- arbitrary callbacks;
- proof-field reads; or
- `bind : Program Nat -> (Nat -> Program ty) -> Program ty`.

The last item is the main trap.  It stores a Lean function in the syntax tree
and weakens the first-order anti-oracle story.

### Program

```lean
structure RegProgram where
  body : List Cmd
  output : OptNatExpr
```

The initial consumer can return only `Option Nat`.  Generalize the output type
after the first theorem lands, not before.

Evaluation should be:

```lean
def RegProgram.eval :
    RegProgram -> Store -> RegFile -> Result .optNat
```

The result trace should reuse `TraceEvent`.  Branches and arithmetic do not
need trace events in the first pass; their cost convention should be stated as
zero-cost control/index arithmetic.  If we later count them, add explicit
`TraceEvent.branch` and `TraceEvent.arith` constructors and update the cost
theorems.

## Anti-Oracle Theorems

The register layer is not closed by syntax alone.  It must reprove the same
reviewer-facing invariants as `Program`, plus a static bound theorem.

Core surfaces:

```lean
theorem RegProgram.eval_toCosted_cost_eq_trace_length ...
theorem RegProgram.eval_reads_subset_payload ...
theorem RegProgram.eval_readWord_event_eq_store ...
theorem RegProgram.eval_word_reads_length_le_machine ...
theorem RegProgram.eval_eq_of_readWord_eq ...
theorem RegProgram.eval_toCosted_eq_of_readWord_eq ...
theorem RegProgram.eval_trace_length_le_staticBound ...
```

The static-bound theorem can initially be syntactic:

```lean
def Cmd.readCount : Cmd -> Nat
def RegProgram.readCount : RegProgram -> Nat

theorem RegProgram.eval_trace_length_le_readCount
    (program : RegProgram) (store : Store) (regs : RegFile) :
    (program.eval store regs).trace.length <= program.readCount
```

This is enough for constant-query use because the final programs have fixed
small command lists.

## First Consumed Theorem

The first consumer should be narrow and meaningful: replace the Lean-side
handoff from optional endpoint-close values to the BP close/LCA payload-table
read.

Target module:

```text
RMQ/Core/SuccinctSpace/BPCloseLCARegisterRAM.lean
```

Target definitions:

```lean
def PayloadLiveBPCloseLCADirectory.lcaCloseFromEndpointRegsProgram
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux)
    (slotExpr : NatExpr -> NatExpr -> NatExpr)
    (hslot :
      forall regs leftClose rightClose,
        regs.optNatRegs[0]? = some (some leftClose) ->
        regs.optNatRegs[1]? = some (some rightClose) ->
        (slotExpr (.const leftClose) (.const rightClose)).eval regs =
          directory.slotIndex leftClose rightClose) :
    RegProgram
```

The proof should quickly specialize this to concrete directories whose
`slotIndex` has an explicit first-order expression.  The generic `hslot`
argument is acceptable only as a bridge; it should not be the final capstone
surface.

Theorem shape:

```lean
theorem PayloadLiveBPCloseLCADirectory
    .lcaCloseFromEndpointRegsProgram_refines_lcaCloseProgram_glue
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux)
    (leftClose? rightClose? : Option Nat) :
    ((directory.lcaCloseFromEndpointRegsProgram aux ...).eval
        (directory.lcaCloseWordRAMStore aux)
        (RegFile.withOptNat2 leftClose? rightClose?)).toCosted =
      match leftClose?, rightClose? with
      | some leftClose, some rightClose =>
          ((directory.lcaCloseProgram aux leftClose rightClose).eval
            (directory.lcaCloseWordRAMStore aux)).toCosted
      | _, _ => Costed.pure none
```

This theorem is the first real dynamic-address checkpoint: the payload read
address is produced by earlier register values inside first-order syntax.

## Hardening Ladder

1. Core register layer:
   `RMQ/Core/WordRAM/Register.lean` with anti-oracle and static-bound theorems.

2. Narrow BP close/LCA dynamic-address consumer:
   `BPCloseLCARegisterRAM.lean`, proving endpoint-register-to-table-read
   refinement.

3. BP close-navigation query step:
   replace the current Lean-side LCA handoff in
   `PayloadLiveBPCloseRMQNavigationDirectory.queryBuiltInterpretedCosted` with
   the register consumer, while keeping select/rank leaves as existing
   interpreted calls.

4. Concrete compact close/LCA:
   registerize the rank-seeded same-block/cross-block dispatch enough to prove
   a theorem like:

```lean
theorem ConcreteCompactBPCloseLCADirectory
    .lcaCloseRegProgram_refines_lcaCloseCostedWithInterpretedRankSeed ...
```

This is the first point where local BP seeds, endpoint fringes, and the
relative-rmM interior navigator must all be represented by payload reads or
first-order arithmetic, not callbacks.

5. Final RMQ capstone:
   add `SuccinctFinalRegRAM.lean` with a theorem such as:

```lean
theorem concreteBPNativeSuccinctRMQQueryRegInterpreted_refines_queryCosted ...
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily
    .total_two_sided_doubled_catalan_slack_reg_interpreted_profile ...
```

6. Rank/select replay:
   use the same register layer for compressed/FID access, rank, and packed
   Clark select routing.  Public target:

```lean
theorem RankSelect.compressedFIDFixedWeightRegisterInterpretedFamilyProfile ...
```

This should be parallelizable after the core layer lands: access, rank, local
select, and packed-Clark routing are separate enough to assign to different
workers.

## Fixedpoint Verdict

The architecture does not need another broad redesign.  It needs one small,
generic, first-order register/control-flow layer with the same anti-oracle
theorems as the current `WordRAM.Program` plus a syntactic trace bound.  The
first consumed theorem should be the endpoint-close-register to LCA-table-read
handoff.  That theorem is small enough to prove next, but strong enough to keep
the whole hardening ladder honest.

## 2026-07-01 Initial Rung Landed

The first register/control rung has landed in:

```text
RMQ/Core/WordRAM/Register.lean
RMQ/Core/SuccinctSpace/BPCloseLCARegisterRAM.lean
```

Core theorem surfaces:

```lean
RMQ.WordRAM.Register.RegProgram.eval_toCosted_cost_eq_trace_length
RMQ.WordRAM.Register.RegProgram.eval_reads_subset_payload
RMQ.WordRAM.Register.RegProgram.eval_readWord_event_eq_store
RMQ.WordRAM.Register.RegProgram.eval_word_reads_length_le_machine
RMQ.WordRAM.Register.RegProgram.eval_eq_of_readWord_eq
RMQ.WordRAM.Register.RegProgram.eval_toCosted_eq_of_readWord_eq
RMQ.WordRAM.Register.RegProgram.eval_trace_length_le_readCount
```

First consumed theorem surfaces:

```lean
RMQ.SuccinctSpace.PayloadLiveBPCloseLCADirectory
  .lcaCloseFromEndpointRegsProgram_refines_lcaCloseProgram_glue
RMQ.SuccinctSpace.PayloadLiveBPCloseLCADirectory
  .lcaCloseFromEndpointRegsProgram_cost_le_one
RMQ.SuccinctSpace.PayloadLiveBPCloseLCADirectory
  .lcaCloseFromEndpointRegsProgram_reads_subset_payload
```

This closes the first dynamic-address handoff: optional endpoint-close values
can live in registers, the program branches on their presence, computes a table
slot from a first-order `NatExpr`, and performs the payload read inside the
register interpreter.

## 2026-07-01 Dynamic Rank Rung Landed

The register layer now also has natural-valued programs in
`RMQ.Core.WordRAM.Register`.  The key constructor for the current hardening
ladder is `NatProgram.twoLevelSampledRank`: it reads a super sample, block
sample, and packed bit word from register-computed addresses, then records the
word-local rank event in the same interpreted trace.

Core theorem surfaces:

```lean
RMQ.WordRAM.Register.NatProgram.eval_toCosted_cost_eq_trace_length
RMQ.WordRAM.Register.NatProgram.eval_reads_subset_payload
RMQ.WordRAM.Register.NatProgram.eval_readWord_event_eq_store
RMQ.WordRAM.Register.NatProgram.eval_word_reads_length_le_machine
RMQ.WordRAM.Register.NatProgram.eval_eq_of_readWord_eq
RMQ.WordRAM.Register.NatProgram.eval_toCosted_eq_of_readWord_eq
RMQ.WordRAM.Register.NatProgram.eval_trace_length_le_stepCount
```

Consumed rank surfaces:

```lean
RMQ.SuccinctSpace.PayloadLiveStoredWordRankData
  .rankRegProgram_refines_rankCostedClamped
RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
  .rankRegisterProgram_refines_rankInterpretedCosted
RMQ.SuccinctRank.TwoLevelPayloadLiveStoredWordRankData
  .rankRegisterInterpretedCosted_refines_rankInterpretedCosted
```

The final interpreted RMQ query in `RMQ.Core.SuccinctFinalRAM` now uses the
two-level register-backed rank surface for the answer-rank leg.  In plain
English: the dynamic position `answerClose + 1` is still produced by the outer
query glue, but once it is supplied as a register input, all two-level rank
addresses and payload reads are handled by first-order register syntax.

## 2026-07-01 Whole-Query Capstone Landed

The final interpreted RMQ query in `RMQ.Core.SuccinctFinalRAM` now also has a
closed outer control program:

```lean
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram
RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
```

The program selects the two endpoint closes, branches into compact BP
close/LCA, uses the answer close to compute the rank position, and writes the
final array index.  Its key bridge theorem is:

```lean
RMQ.SuccinctFinal
  .concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted_refines_queryInterpretedCosted
```

The consumed public profile is:

```lean
RMQ.SuccinctFinal
  .builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
```

In plain English: the remaining Lean-side query glue has been replaced by a
first-order instruction list with optional/natural registers.  The component
leaves are still the already interpreted close-select, compact close/LCA, and
two-level register-backed rank operations.  The next hardening frontier is not
the outer controller anymore; it is an even lower-level unified payload-store
trace where those component leaves and the controller share one interpreter
state.
