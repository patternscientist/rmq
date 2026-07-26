import RMQ.Core.SuccinctRMQClassic
import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL, part 2.  The defender proved `L3_leaf_size_only` only for the
STORE-PARAMETRIC leaf, at one store shared by both shapes.  The PRIMARY public
route (`RMQ.SuccinctClassic.queryTraceResult`) uses the NON-store leaf
`concreteBPNativeRankCloseWordTraceResultAtSegment`, whose store
(`concreteBPNativeChunkedRankCloseSeedReadStore shape base`) is SHAPE-DERIVED.
Their theorem does not cover that instantiation.

So: execute the non-store leaf across all shapes of a fixed size at several
sizes and inspect the ADDRESS stream.  Under F03 an address is benign iff it
factors through n, endpoints, header, or PRIOR PROBE REPLIES.  A differing
address that is NOT preceded by a probe carrying the difference would be X.
-/

namespace AdvF2NS

open RMQ
open RMQ.SuccinctFinal
open RMQ.Cartesian

/-- all Cartesian shapes of a given size -/
partial def shapesOfSize : Nat -> List CartesianShape
  | 0 => [CartesianShape.empty]
  | n + 1 =>
      (List.range (n + 1)).flatMap fun k =>
        (shapesOfSize k).flatMap fun l =>
          (shapesOfSize (n - k)).map fun r => CartesianShape.node l r

def addrs (t : WordRAM.TraceResult Nat) : List (Nat × Nat) :=
  t.trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord s i _ => some (s, i)
    | _ => none

/-- the raw word replies, in order -/
def replies (t : WordRAM.TraceResult Nat) : List (Option (List Bool)) :=
  t.trace.filterMap fun e =>
    match e with
    | WordRAM.TraceEvent.readWord _ _ w => some w
    | _ => none

def leafNS (s : CartesianShape) (pos : Nat) : WordRAM.TraceResult Nat :=
  concreteBPNativeRankCloseWordTraceResultAtSegment s 17 pos

/-! ## Sanity: shape enumeration -/
#eval (shapesOfSize 3).length          -- expect 5
#eval (shapesOfSize 4).length          -- expect 14
#eval (shapesOfSize 5).length          -- expect 42
#eval ((shapesOfSize 5).map (·.size)).eraseDups
#eval ((shapesOfSize 5).map (·.bpCode)).eraseDups.length   -- all distinct?

/-! ## Q: is the NON-store leaf's address stream size-only? -/

def addrProfiles (n pos : Nat) : List (List (Nat × Nat)) :=
  ((shapesOfSize n).map fun s => addrs (leafNS s pos)).eraseDups

-- size 3
#eval (addrProfiles 3 5)
-- size 4
#eval (addrProfiles 4 5)
-- size 5, several positions
#eval (addrProfiles 5 5)
#eval (addrProfiles 5 7)
#eval (addrProfiles 5 9)
-- size 6, 7, 8 (geometry crosses a machineWordBits boundary here)
#eval (addrProfiles 6 9)
#eval (addrProfiles 7 11)
#eval (addrProfiles 8 13)
#eval (addrProfiles 8 15)

/-! ## Q: do the VALUES differ across same-size shapes on the non-store route?
(They must: the leaf reads the real bp code.  If they did NOT, the leaf would be
vacuous.) -/
#eval ((shapesOfSize 5).map fun s => (leafNS s 7).value).eraseDups
#eval ((shapesOfSize 8).map fun s => (leafNS s 13).value).eraseDups

/-! ## The decisive locality question.
If two same-size shapes produce DIFFERENT address streams, is the first point of
divergence preceded by a probe whose REPLY already differs?  If yes, the address
is prior-probe-derived (benign).  If the very FIRST address differs, that is X.
-/

def firstAddrDiverge (n pos : Nat) : Option Nat :=
  match (shapesOfSize n) with
  | [] => none
  | s0 :: rest =>
      let a0 := addrs (leafNS s0 pos)
      rest.foldl (fun acc s =>
        let a := addrs (leafNS s pos)
        let k := ((a0.zip a).takeWhile (fun p => p.1 == p.2)).length
        match acc with
        | none => if a == a0 then none else some k
        | some m => if a == a0 then some m else some (Nat.min m k)) none

/-- index of the first differing REPLY between shape 0 and any other -/
def firstReplyDiverge (n pos : Nat) : Option Nat :=
  match (shapesOfSize n) with
  | [] => none
  | s0 :: rest =>
      let r0 := replies (leafNS s0 pos)
      rest.foldl (fun acc s =>
        let r := replies (leafNS s pos)
        let k := ((r0.zip r).takeWhile (fun p => p.1 == p.2)).length
        match acc with
        | none => if r == r0 then none else some k
        | some m => if r == r0 then some m else some (Nat.min m k)) none

#eval (firstAddrDiverge 5 7, firstReplyDiverge 5 7)
#eval (firstAddrDiverge 8 13, firstReplyDiverge 8 13)
#eval (firstAddrDiverge 8 15, firstReplyDiverge 8 15)
#eval (firstAddrDiverge 7 11, firstReplyDiverge 7 11)

/-! ## The first three addresses are the size-only ones. Check explicitly. -/
#eval ((shapesOfSize 8).map fun s => (addrs (leafNS s 13)).take 3).eraseDups
#eval ((shapesOfSize 7).map fun s => (addrs (leafNS s 11)).take 3).eraseDups

end AdvF2NS
