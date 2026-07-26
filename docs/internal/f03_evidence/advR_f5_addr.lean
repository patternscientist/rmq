import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM
import Lean

/-!
ADVERSARIAL F5, attack 2: the ADDRESS channel.

`canonicalRelativeRmmInteriorComponentOffsets` is consumed by six query-time
computations as the BASE ADDRESS of every counted probe, and it is computed as
  (table.machineStore hword).store.words.size
over tables literally built out of `bpExcessAt` VALUES.  The benign verdict's
own evidence never covers this link (its lemma covers only
`machineReadComputationAt`, whose table argument is erased).

If `.words.size` depended on entry VALUES, a bpExcessAt value would reach an
ADDRESS without passing a probe => CHECKED_OBSTRUCTION (X).

Attack: perturb the ENTRIES directly (not the shape) with equal-length,
maximally divergent value vectors and compare the executed word counts.
-/

open RMQ RMQ.Cartesian RMQ.SuccinctClose RMQ.SuccinctSpace

namespace AdvAddr

/-- The exact executed word-count formula used by the offsets. -/
def wordsSizeOf (entries : List Nat) (width wordSize : Nat) : Nat :=
  ((entries.map (natToBitsLE width)).flatMap (chunkPayloadWords wordSize)).length

/-- Per-entry encoded word length: if this is ever /= width, offsets leak. -/
def encodedLens (entries : List Nat) (width : Nat) : List Nat :=
  (entries.map (natToBitsLE width)).map List.length

def allEq {a : Type} [BEq a] : List a -> Bool
  | [] => true
  | x :: xs => xs.all (fun y => y == x)

/-- Maximally divergent equal-length entry vectors, including saturating ones. -/
def probeVectors (len width : Nat) : List (List Nat) :=
  let maxV := 2 ^ width - 1
  [ List.replicate len 0
  , List.replicate len maxV
  , (List.range len).map (fun i => i % (maxV + 1))
  , (List.range len).map (fun i => (maxV - (i % (maxV + 1))))
  , (List.range len).map (fun i => if i % 2 == 0 then 0 else maxV)
  , (List.range len).map (fun i => (i * 7 + 3) % (maxV + 1)) ]

#eval show IO Unit from do
  let mut bad := 0
  let mut rows := 0
  for width in [1,2,3,4,5,6,7,8,11,16,17,32] do
    for wordSize in [1,2,3,4,5,8,13,16,64] do
      for len in [0,1,2,3,5,8,13,64] do
        let vs := probeVectors len width
        let sizes := vs.map (fun e => wordsSizeOf e width wordSize)
        let lens := vs.map (fun e => encodedLens e width)
        rows := rows + 1
        if !(allEq sizes) then
          bad := bad + 1
          IO.println s!"  VALUE-DEPENDENT words.size! width={width} wordSize={wordSize} len={len} sizes={sizes}"
        if !(lens.all (fun l => l.all (fun x => x == width))) then
          bad := bad + 1
          IO.println s!"  ENCODED WORD LENGTH /= width! width={width} wordSize={wordSize} len={len}"
  IO.println s!"ADDR_ATTACK rows={rows} violations={bad}"

/-- Out-of-range entries (forbidden by ofEntries' proof, but check the encoder). -/
#eval show IO Unit from do
  let mut bad := 0
  for width in [1,2,3,4,8] do
    for v in [0, 1, 2^width - 1, 2^width, 2^width + 1, 2^(width+3)] do
      let l := (natToBitsLE width v).length
      if l != width then
        bad := bad + 1
        IO.println s!"  natToBitsLE width={width} v={v} length={l} (/= width)"
  IO.println s!"ENCODER_TOTALITY violations={bad}"

end AdvAddr
