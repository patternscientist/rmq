import RMQ.Core.SuccinctSpace.BPCloseLCA
import RMQ.Core.SuccinctSpace.TablesRAM

/-!
# Word-RAM interpretation for BP close/LCA table reads

This is the first BP-navigation interpreter skeleton: a payload-live BP
close/LCA directory query reads one fixed-width optional-natural table cell
through `WordRAM`, then joins the outer indexed-read option with the stored
optional close value.
-/

namespace RMQ

namespace SuccinctSpace

namespace PayloadLiveBPCloseLCADirectory

/-- First-order program for the payload-live BP close/LCA table query. -/
def lcaCloseProgram
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    RMQ.WordRAM.Program .optNat :=
  RMQ.WordRAM.Program.joinOptOptNat
    ((directory.table aux).readProgram
      (directory.slotIndex leftClose rightClose))

/-- The Word-RAM store used by the built auxiliary table. -/
def lcaCloseWordRAMStore
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) : RMQ.WordRAM.Store :=
  (directory.table aux).wordRAMStore

theorem lcaCloseProgram_refines_lcaCloseCosted
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    ((directory.lcaCloseProgram aux leftClose rightClose).eval
        (directory.lcaCloseWordRAMStore aux)).toCosted =
      directory.lcaCloseCosted aux leftClose rightClose := by
  unfold lcaCloseProgram lcaCloseWordRAMStore lcaCloseCosted
  rw [RMQ.WordRAM.Program.eval_joinOptOptNat_toCosted_eq_map]
  rw [FixedWidthOptionNatTable.readProgram_refines_readCosted]
  apply Costed.ext
  · cases
      (((directory.table aux).readCosted
        (directory.slotIndex leftClose rightClose)).value) <;> rfl
  · rfl

theorem lcaCloseProgram_cost_le_one
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    ((directory.lcaCloseProgram aux leftClose rightClose).eval
        (directory.lcaCloseWordRAMStore aux)).toCosted.cost <= 1 := by
  rw [directory.lcaCloseProgram_refines_lcaCloseCosted aux leftClose
    rightClose]
  exact directory.lcaCloseCosted_cost_le_one aux leftClose rightClose

theorem lcaCloseProgram_exact
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len leftClose rightClose : Nat}
    (hlen : 0 < len) (hbound : left + len <= n)
    (hleftClose : bpCloseOfInorder? shape left = some leftClose)
    (hrightClose :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose) :
    ((directory.lcaCloseProgram (directory.buildAux shape)
        leftClose rightClose).eval
        (directory.lcaCloseWordRAMStore
          (directory.buildAux shape))).toCosted.erase =
        bpCloseOfInorder? shape
          (scanWindow shape.representative left len) := by
  rw [directory.lcaCloseProgram_refines_lcaCloseCosted
    (directory.buildAux shape) leftClose rightClose]
  exact directory.lcaCloseCosted_exact hshape hlen hbound hleftClose
    hrightClose

theorem lcaCloseProgram_profile
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.encodeAux (directory.buildAux shape)).length =
          overhead) /\
      (forall aux leftClose rightClose,
        ((directory.lcaCloseProgram aux leftClose rightClose).eval
          (directory.lcaCloseWordRAMStore aux)).toCosted.cost <= 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    ((directory.lcaCloseProgram
                        (directory.buildAux shape)
                        leftClose rightClose).eval
                        (directory.lcaCloseWordRAMStore
                          (directory.buildAux shape))).toCosted.erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.aux_length_eq hshape
  · constructor
    · intro aux leftClose rightClose
      exact directory.lcaCloseProgram_cost_le_one aux leftClose rightClose
    · intro shape hshape left len leftClose rightClose
        hlen hbound hleftClose hrightClose
      exact directory.lcaCloseProgram_exact hshape hlen hbound hleftClose
        hrightClose

end PayloadLiveBPCloseLCADirectory

end SuccinctSpace

end RMQ
