import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.WordRAM.E1RouteDecomposition

/-!
# E1 whole-query glue: the route objects in MACHINE form

## What this module is, and what it deliberately is NOT

This lane was briefed to BUILD two object reconciliations - the rank leg's
seed-store/global-store mismatch, and the close/LCA arm's
`AtSegment`/`AtSegmentWithStore` mismatch - from their ingredients, in a new
module.

**Both reconciliations already exist in the tree.**  Grepped and read before
acting, per the rule that a claim about what the tree contains gets checked
first:

* RANK - `concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq`
  (`SuccinctFinalRAM.lean:1550`) states, as a FULL `TraceResult` equality,
  that at the canonical base `17` the route's seed-store rank leg IS the
  global-store one.  Its proof is precisely the prescribed route:
  `bpChunkedRankTraceResultWithStore_store_parametric` discharged by the four
  seed witnesses and the four global witnesses, with the `17 + 4 = 21` chunk
  bridge by `rfl`.
* LCA -
  `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore`
  (`SuccinctFinalStoreParam.lean:1633`) glues the store-parametric close/LCA
  arm at the global store to the canonical arm the route names, routing the
  rank seed through the theorem above.

Rebuilding either would duplicate frozen machinery and would be a witness
CONSTRUCTED for a premise rather than FOUND at the target.  So this module
APPLIES them at the whole-query route objects instead, which is the part that
was genuinely missing: the glue needs the route's branch receipt written in
the objects the machine's own leg theorems produce, and no statement did
that.

Nothing here is a reconciliation proof.  Every proof below is a rewrite by an
existing theorem, and each cites the theorem it uses.
-/

namespace RMQ
namespace SuccinctFinal

/-! ## The rank leg

`rankCloseBlock_runsTo_canonical` (`E1RankCanonical.lean:257`) produces
receipts `(concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape pos).trace`,
while the route's `.full` branch names
`concreteBPNativeRankCloseWordTraceResultAtSegment shape 17 pos`.  These are
the same object.
-/

/-- The route's `.full`-branch receipt, with the rank leg written in the
GLOBAL form the machine's canonical rank block produces.

Proved by rewriting with `concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq`
(`SuccinctFinalRAM.lean:1550`) - a full `TraceResult` equality, so the receipt
survives the swap.  Routing this through a `toCosted` or `_refines` form
instead would discard the receipt, which is the entire content of the
composition. -/
theorem wholeQueryBranchTrace_full_eq_globalRank
    (shape : Cartesian.CartesianShape)
    (left right leftClose rightClose answerClose : Nat) :
    wholeQueryBranchTrace shape left right
        (.full leftClose rightClose answerClose) =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace ++
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (answerClose + 1)).trace := by
  show
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace ++
        (concreteBPNativeRankCloseWordTraceResultAtSegment shape
          concreteBPNativeRankCloseTraceSegmentBase
          (answerClose + 1)).trace = _
  rw [concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq]

/-- The route's `.full`-branch value, likewise in global rank form. -/
theorem wholeQueryBranchValue_full_eq_globalRank
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose answerClose : Nat) :
    wholeQueryBranchValue shape (.full leftClose rightClose answerClose) =
      some
        ((concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (answerClose + 1)).value - 1) := by
  show
      some
        ((concreteBPNativeRankCloseWordTraceResultAtSegment shape
          concreteBPNativeRankCloseTraceSegmentBase
          (answerClose + 1)).value - 1) = _
  rw [concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq]

/-! ## The close/LCA arm

The machine's close/LCA composition works against the store-parametric
`...WithStore` arm at the global store; the route names the canonical arm.
-/

/-- The route's close/LCA leg, written in the store-parametric form at the
global store.  Proved by
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore`
(`SuccinctFinalStoreParam.lean:1633`). -/
theorem lcaLeg_eq_withStore_at_globalReadStore
    (shape : Cartesian.CartesianShape) (leftClose rightClose : Nat) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape leftClose rightClose =
      concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        leftClose rightClose :=
  (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore
    shape leftClose rightClose).symm

/-! ## Both swaps at once

The single statement the whole-query glue consumes: the route's `.full`
receipt entirely in the objects the machine's leg theorems produce.
-/

/-- The `.full`-branch receipt with BOTH legs in machine form. -/
theorem wholeQueryBranchTrace_full_machineObjects
    (shape : Cartesian.CartesianShape)
    (left right leftClose rightClose answerClose : Nat) :
    wholeQueryBranchTrace shape left right
        (.full leftClose rightClose answerClose) =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
          shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          leftClose rightClose).trace ++
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (answerClose + 1)).trace := by
  rw [wholeQueryBranchTrace_full_eq_globalRank,
    ← lcaLeg_eq_withStore_at_globalReadStore]

/-- The `.lcaNone`-branch receipt in machine form.  The rank leg does not
appear, so only the close/LCA swap is needed - which is the whole point of
keeping the branches apart. -/
theorem wholeQueryBranchTrace_lcaNone_machineObjects
    (shape : Cartesian.CartesianShape)
    (left right leftClose rightClose : Nat) :
    wholeQueryBranchTrace shape left right
        (.lcaNone leftClose rightClose) =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
          shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          leftClose rightClose).trace := by
  show
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape leftClose rightClose).trace = _
  rw [← lcaLeg_eq_withStore_at_globalReadStore]

/-- The two select-miss receipts need NO swap at all: the select legs are
already named in global form by the route, and neither the close/LCA leg nor
the rank leg appears.  Recorded so the glue does not go looking for a
reconciliation that is not needed there. -/
theorem wholeQueryBranchTrace_selectNone_needs_no_swap
    (shape : Cartesian.CartesianShape) (left right leftClose : Nat) :
    wholeQueryBranchTrace shape left right .leftSelectNone =
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape
            (right - 1)).trace ∧
      wholeQueryBranchTrace shape left right (.rightSelectNone leftClose) =
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape
            (right - 1)).trace :=
  ⟨rfl, rfl⟩

end SuccinctFinal
end RMQ
