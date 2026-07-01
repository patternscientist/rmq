import RMQ.Core.SuccinctSpace.BPCloseLCARAM
import RMQ.Core.WordRAM.Register

/-!
# Register-level dynamic addressing for BP close/LCA table reads

This module consumes the `WordRAM.Register` layer at the first dynamic-address
handoff: optional endpoint-close values are placed in registers, the program
branches on their presence, computes the LCA-table slot as a first-order
expression, and performs the payload table read inside the register
interpreter.
-/

namespace RMQ

namespace SuccinctSpace

namespace PayloadLiveBPCloseLCADirectory

open RMQ.WordRAM.Register

/--
Register program for the BP close/LCA table handoff.

Register `0` stores the optional left endpoint close and register `1` stores
the optional right endpoint close.  If both are present, the program reads the
joined optional-close table cell at `slotExpr`; otherwise it returns `none`
without a payload read.
-/
def lcaCloseFromEndpointRegsProgram
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (_aux : directory.Aux)
    (slotExpr : NatExpr) :
    RegProgram :=
  RegProgram.ifSomeNat 0
    (RegProgram.ifSomeNat 1
      (RegProgram.readJoinedOptionNat 0 directory.fieldWidth slotExpr)
      (RegProgram.pureOpt (OptNatExpr.const none)))
    (RegProgram.pureOpt (OptNatExpr.const none))

theorem lcaCloseFromEndpointRegsProgram_refines_lcaCloseProgram_glue
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux)
    (slotExpr : NatExpr)
    (hslot :
      forall leftClose rightClose,
        slotExpr.eval
            (RegFile.withOptNat2 (some leftClose) (some rightClose)) =
          directory.slotIndex leftClose rightClose)
    (leftClose? rightClose? : Option Nat) :
    ((directory.lcaCloseFromEndpointRegsProgram aux slotExpr).eval
        (directory.lcaCloseWordRAMStore aux)
        (RegFile.withOptNat2 leftClose? rightClose?)).toCosted =
      match leftClose?, rightClose? with
      | some leftClose, some rightClose =>
          ((directory.lcaCloseProgram aux leftClose rightClose).eval
            (directory.lcaCloseWordRAMStore aux)).toCosted
      | _, _ => Costed.pure none := by
  cases leftClose? with
  | none =>
      rfl
  | some leftClose =>
      cases rightClose? with
      | none =>
          rfl
      | some rightClose =>
          unfold lcaCloseFromEndpointRegsProgram lcaCloseProgram
          have hslot' :
              slotExpr.eval { optNatRegs := #[some leftClose, some rightClose] } =
                directory.slotIndex leftClose rightClose := by
            simpa [RegFile.withOptNat2] using hslot leftClose rightClose
          simp [WordRAM.Register.RegProgram.eval, RegFile.withOptNat2,
            RegFile.optNat]
          rw [hslot']
          rfl

theorem lcaCloseFromEndpointRegsProgram_cost_le_one
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (slotExpr : NatExpr)
    (leftClose? rightClose? : Option Nat) :
    ((directory.lcaCloseFromEndpointRegsProgram aux slotExpr).eval
        (directory.lcaCloseWordRAMStore aux)
        (RegFile.withOptNat2 leftClose? rightClose?)).toCosted.cost <= 1 := by
  have hcount :=
    WordRAM.Register.RegProgram.eval_trace_length_le_readCount
      (directory.lcaCloseFromEndpointRegsProgram aux slotExpr)
      (directory.lcaCloseWordRAMStore aux)
      (RegFile.withOptNat2 leftClose? rightClose?)
  simpa [WordRAM.Result.toCosted, WordRAM.Result.steps,
    lcaCloseFromEndpointRegsProgram, WordRAM.Register.RegProgram.readCount]
    using hcount

theorem lcaCloseFromEndpointRegsProgram_reads_subset_payload
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (slotExpr : NatExpr)
    (leftClose? rightClose? : Option Nat) :
    forall event : WordRAM.TraceEvent,
      event ∈
          ((directory.lcaCloseFromEndpointRegsProgram aux slotExpr).eval
            (directory.lcaCloseWordRAMStore aux)
            (RegFile.withOptNat2 leftClose? rightClose?)).trace ->
        event.matchesStore (directory.lcaCloseWordRAMStore aux) := by
  exact
    WordRAM.Register.RegProgram.eval_reads_subset_payload
      (directory.lcaCloseFromEndpointRegsProgram aux slotExpr)
      (directory.lcaCloseWordRAMStore aux)
      (RegFile.withOptNat2 leftClose? rightClose?)

end PayloadLiveBPCloseLCADirectory

end SuccinctSpace

end RMQ
