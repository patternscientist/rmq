import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Executable differential test: two DISTINCT shapes of the SAME size (5), hence
the same `bpCode.length` (10). Anything the instrument called "length-only,
derivable from n" must return EQUAL values on both. Anything that differs is
content-dependent, and the label is wrong.
-/

open RMQ
open RMQ.Cartesian

namespace ZZDiff

--
def shapeL : CartesianShape :=
  .node (.node (.node (.node (.node .empty .empty) .empty) .empty) .empty) .empty

--
def shapeR : CartesianShape :=
  .node .empty (.node .empty (.node .empty (.node .empty (.node .empty .empty))))

#eval (shapeL.size, shapeR.size)
#eval (shapeL.bpCode.length, shapeR.bpCode.length)
#eval shapeL.bpCode
#eval shapeR.bpCode

--
#eval (SuccinctFinal.builtRelativeSplitBPCloseRankWordSize shapeL,
       SuccinctFinal.builtRelativeSplitBPCloseRankWordSize shapeR)

--
#eval (SuccinctClose.localBPWindowBase shapeL 2 3,
       SuccinctClose.localBPWindowBase shapeR 2 3)

--
#eval (SuccinctClose.bpBlockArgMinPrefixPos shapeL 2 1,
       SuccinctClose.bpBlockArgMinPrefixPos shapeR 2 1)

--
#eval (SuccinctClose.bpBlockMinExcess shapeL 2 1,
       SuccinctClose.bpBlockMinExcess shapeR 2 1)

--
#eval ((List.range 5).map (fun b => SuccinctClose.bpBlockMinExcess shapeL 2 b),
       (List.range 5).map (fun b => SuccinctClose.bpBlockMinExcess shapeR 2 b))

--
#eval ((List.range 5).map (fun b => SuccinctClose.bpBlockArgMinPrefixPos shapeL 2 b),
       (List.range 5).map (fun b => SuccinctClose.bpBlockArgMinPrefixPos shapeR 2 b))

--
#eval ((List.range 11).map (fun p => SuccinctClose.bpExcessAt shapeL p),
       (List.range 11).map (fun p => SuccinctClose.bpExcessAt shapeR p))

--
#eval (SuccinctClose.bpBetterArgMinBlock shapeL 2 0 2,
       SuccinctClose.bpBetterArgMinBlock shapeR 2 0 2)

--
#eval (SuccinctClose.bpBlockExcessSamples shapeL 2 1,
       SuccinctClose.bpBlockExcessSamples shapeR 2 1)

--
#eval (SuccinctClose.bpSuperblockBaselineEntries shapeL 2 2 2,
       SuccinctClose.bpSuperblockBaselineEntries shapeR 2 2 2)

--
#eval (SuccinctClose.bpRelativeExcessEntry shapeL 2 2 1 7,
       SuccinctClose.bpRelativeExcessEntry shapeR 2 2 1 7)

end ZZDiff
