import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
ADVERSARIAL E: THE DEGENERACY ATTACK.

Every executed test in the S dossier lives at bit-length <= 10.
`superStride n = wordBits n ^ 2` and `wordBits n = Nat.log2 n + 1`, so at
length 10 the super stride is 16 while `occurrenceCount` is at most 10:
`selectSuperSlot q superStride = q / 16 = 0` ALWAYS.  The whole super level -
multi-super-slot addressing, `super.baseOccurrence` subtraction, the long
compact slot `exceptionRank * superStride + localOccurrence` - is never
exercised.  If shape content leaks through super-level arithmetic, no prior
experiment could have seen it.

E0 : parameter table - locate the degeneracy boundary.
E1 : bitvectors at a length/count where superSlotCount >= 2.
E2 : real BP shapes big enough to leave the degenerate regime.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace Adv6D

def L1raw (bits : List Bool) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  (GenericSelect.sparseExceptionSelectData bits false)
    |>.bpChunkedSelectTraceResultWithStore
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeFringeChunkTraceSegment
      concreteBPNativeSelectChunkTraceSegment store
      (SuccinctClose.bpFringeChunkBits bits.length) idx

theorem L1raw_eq (shape : CartesianShape) (store : WordRAM.ReadStore)
    (idx : Nat) :
    L1raw shape.bpCode store idx =
      concreteBPNativeSelectCloseGlobalWordTraceResultWithStore
        shape store idx := rfl

def leaf (shape : CartesianShape) (store : WordRAM.ReadStore) (idx : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  concreteBPNativeSelectCloseGlobalWordTraceResultWithStore shape store idx

def zeroW : List Bool := List.replicate 16 false
def noiseW (salt seg idx : Nat) : List Bool :=
  (List.range 16).map fun k =>
    (salt + seg * 7919 + idx * 104729 + k * 1299709) % 3 == 0

def noiseStore (salt : Nat) : WordRAM.ReadStore where
  readWord? segment index := some (noiseW salt segment index)

def craft (salt : Nat) (superMark localMark : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    if segment == 3 then
      some (if superMark then noiseW salt 3 index else zeroW)
    else if segment == 7 then
      some (if localMark then noiseW salt 7 index else zeroW)
    else
      some (noiseW salt segment index)

def wordStr : Option (List Bool) -> String
  | none => "-"
  | some w => String.mk (w.map fun b => if b then '1' else '0')

def evKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i w? => s!"R({s},{i})->{wordStr w?}"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def key (r : WordRAM.TraceResult (Option Nat)) : String :=
  s!"{repr r.value}|" ++ String.intercalate ";" (r.trace.map evKey)

def addrKey : WordRAM.TraceEvent -> String
  | WordRAM.TraceEvent.readWord s i _ => s!"({s},{i})"
  | WordRAM.TraceEvent.wordRank t l r => s!"WR({t},{l},{r})"
  | WordRAM.TraceEvent.wordSelect t o r => s!"WS({t},{o},{r})"
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => "SYN"

def addrTrace (r : WordRAM.TraceResult (Option Nat)) : String :=
  String.intercalate ";" (r.trace.map addrKey)

/-! ### E0: where does degeneracy end? -/

#eval show IO Unit from do
  IO.println "== E0. slot parameters: superSlotCount = ceil(occ / wordBits(len)^2) =="
  IO.println "  len wordBits superStride localStride localSlotsPerSuper | occ=len/2 -> superSlots | occ=len -> superSlots"
  for len in [6, 8, 10, 20, 40, 80, 100, 128, 130, 140, 256, 260] do
    let wb := GenericSelect.wordBits len
    let ss := GenericSelect.superStride len
    let ls := GenericSelect.localStride len
    let lsps := GenericSelect.localSlotsPerSuper len
    let sHalf := GenericSelect.selectCeilDiv (len / 2) ss
    let sFull := GenericSelect.selectCeilDiv len ss
    IO.println s!"  {len}  wb={wb} superStride={ss} localStride={ls} localSlotsPerSuper={lsps} | half:{sHalf} | full:{sFull}"

/-! ### E1: bitvectors with superSlotCount >= 2 -/

def hash (s i : Nat) : Nat := (s * 2654435761 + i * 40503 + i * i * 97 + s * i + 11) % 1000003

/-- Deterministic bitvector of length `len` with EXACTLY `k` `false` bits. -/
def genBits (len k seed : Nat) : List Bool :=
  let trues := len - k
  let st := (List.range len).foldl
    (fun (s : Nat × Nat × List Bool) i =>
      let r := s.1
      let t := s.2.1
      let acc := s.2.2
      let pick := if r == 0 then false else (hash seed i) % r < t
      (r - 1, (if pick then t - 1 else t), pick :: acc))
    (len, trues, ([] : List Bool))
  st.2.2.reverse

def falses (bits : List Bool) : Nat := (bits.filter (fun b => !b)).length

def probe (label : String) (len k : Nat) (seeds : List Nat)
    (store : WordRAM.ReadStore) (idxs : List Nat) : IO Unit := do
  let bs := (seeds.map (genBits len k)).eraseDups
  let counts := (bs.map falses).eraseDups
  let occ := GenericSelect.occurrenceCount (bs.headD []) false
  let sc := GenericSelect.superSlotCount (bs.headD []) false
  let mut worst := 0
  let mut witness := ""
  for idx in idxs do
    let ks := (bs.map (fun b => key (L1raw b store idx))).eraseDups
    if ks.length > worst then
      worst := ks.length
      witness := s!"idx={idx}"
  IO.println s!"  {label} len={len} k={k} distinctBitvectors={bs.length} falseCounts={counts} occ={occ} superSlotCount={sc} MAXDISTINCTOUTCOMES={worst} {witness}"

#eval show IO Unit from do
  IO.println "== E1. NON-DEGENERATE super level: superSlotCount >= 2 =="
  let seeds := List.range 24
  for (lbl, st) in [("noise(11) ", noiseStore 11),
                    ("LONG      ", craft 11 true true),
                    ("SPARSE    ", craft 11 false true),
                    ("DENSE     ", craft 11 false false)] do
    probe lbl 40 38 seeds st [0, 1, 30, 36, 37]
    probe lbl 40 40 seeds st [0, 1, 30, 39]
    probe lbl 40 20 seeds st [0, 1, 10, 19]

#eval show IO Unit from do
  IO.println "== E1b. anti-vacuity at len=40: do the sampled bitvectors differ internally? =="
  let seeds := List.range 24
  for k in [38, 40, 20] do
    let bs := (seeds.map (genBits 40 k)).eraseDups
    let ints := (bs.map (fun b =>
      let se := (GenericSelect.superEntries b false).map
        (fun e => s!"({e.baseOccurrence},{e.baseWordIndex},{e.rankBefore},{e.firstOffset})")
      let le := (GenericSelect.localEntries b false).map
        (fun e => s!"({e.baseOccurrence},{e.baseWordIndex},{e.rankBefore},{e.firstOffset})")
      String.intercalate ";" (se ++ le))).eraseDups
    let ovh := (bs.map (fun b =>
      s!"{GenericSelect.sparseExceptionEffectiveFlagRankSuperOverhead b false}/{GenericSelect.sparseExceptionEffectiveFlagRankBlockOverhead b false}")).eraseDups
    IO.println s!"  len=40 k={k} bitvectors={bs.length} distinctSuper+LocalEntryTables={ints.length} distinctOverheads={ovh.length} values={ovh}"

end Adv6D
