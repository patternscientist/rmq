import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
Refutation by execution of the coordinator's LENGTHONLY bucket.

The instrument classified 19 constants as "every `bpCode` occurrence sits under
`List.length`, therefore they consume only 2n and are derivable from n".
That inference is a syntactic-occurrence test, not a taint analysis: a constant
can receive shape CONTENT by CALLING another content-dependent constant without
mentioning `bpCode` outside a `List.length`.

Test: two shapes of the SAME size (hence identical `bpCode.length`). Anything
truly derivable from n MUST agree on both.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctFinal

namespace AtkLen

/-- Right-leaning chain of size 3: bpCode = [T,F,T,F,T,F]. -/
def rightChain3 : CartesianShape :=
  .node .empty (.node .empty (.node .empty .empty))

/-- Left-leaning chain of size 3: bpCode = [T,T,T,F,F,F]. -/
def leftChain3 : CartesianShape :=
  .node (.node (.node .empty .empty) .empty) .empty

/-- A balanced shape of size 3: bpCode = [T,T,F,F,T,F]. -/
def balanced3 : CartesianShape :=
  .node (.node .empty .empty) (.node .empty .empty)

def all3 : List (String × CartesianShape) :=
  [("rightChain", rightChain3), ("leftChain", leftChain3), ("balanced", balanced3)]

#eval show IO Unit from do
  IO.println "=== same-size shapes: size and bpCode.length must agree ==="
  for (nm, s) in all3 do
    IO.println s!"  {nm}: size={s.size} bpLen={s.bpCode.length} bp={s.bpCode}"

  IO.println ""
  IO.println "=== bpExcessAt (acknowledged CONTENT user F5) ==="
  for (nm, s) in all3 do
    IO.println s!"  {nm}: excess@0..6 = {(List.range 7).map (fun p => bpExcessAt s p)}"

  IO.println ""
  IO.println "=== bpBlockMinExcess -- coordinator bucket: LENGTHONLY (derivable from n) ==="
  for (nm, s) in all3 do
    IO.println s!"  {nm}: blockSize=2 blocks 0,1,2 = {(List.range 3).map (fun b => bpBlockMinExcess s 2 b)}"

  IO.println ""
  IO.println "=== bpBlockArgMinPrefixPos -- coordinator bucket: LENGTHONLY ==="
  for (nm, s) in all3 do
    IO.println s!"  {nm}: blockSize=2 blocks 0,1,2 = {(List.range 3).map (fun b => bpBlockArgMinPrefixPos s 2 b)}"

  IO.println ""
  IO.println "=== bpBlockArgMinPrefixPosFrom -- coordinator bucket: LENGTHONLY ==="
  for (nm, s) in all3 do
    IO.println s!"  {nm}: from pos=0 steps=6 best=0 -> {bpBlockArgMinPrefixPosFrom s 0 6 0}"

  IO.println ""
  IO.println "=== localBPWindowBase -- coordinator bucket: LENGTHONLY ==="
  for (nm, s) in all3 do
    IO.println s!"  {nm}: blockSize=2 close 0..3 = {(List.range 4).map (fun c => localBPWindowBase s 2 c)}"

  IO.println ""
  IO.println "=== builtRelativeSplitBPCloseRankWordSize -- coordinator bucket: LENGTHONLY ==="
  for (nm, s) in all3 do
    IO.println s!"  {nm}: {builtRelativeSplitBPCloseRankWordSize s}"

end AtkLen
