import RMQ.Core.SuccinctFinal
import RMQ.Core.SuccinctRMQClassic

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal

namespace AdvF34b

abbrev Sh := Cartesian.CartesianShape

/-! ## Attack A: does the bpCode "exactly half true" invariant mask a
    content-dependence?  Feed the SAME table builders arbitrary bit lists of
    equal length but wildly different densities. -/

def w (L : Nat) : Nat := SuccinctRank.machineWordBits L
def bw (L : Nat) : Nat := SuccinctRank.machineWordBits (w L * w L)

def supOf (bits : List Bool) (hw : bits.length < 2 ^ w bits.length) : Nat :=
  (SuccinctRank.canonicalSuperRankSampleTables
      bits (w bits.length) (w bits.length) (w bits.length) hw).payload.length

def rawSup (bits : List Bool) : Nat :=
  supOf bits (by
    simpa [w, SuccinctRank.machineWordBits] using
      (Nat.lt_log2_self (n := bits.length)))

def rawBlk (bits : List Bool) : Nat :=
  (SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan
      bits (w bits.length) (w bits.length) (bw bits.length)
      (by simpa [w] using SuccinctRank.machineWordBits_pos bits.length)
      (by
        simpa [w, bw, SuccinctRank.machineWordBits] using
          (Nat.lt_log2_self
            (n := SuccinctRank.machineWordBits bits.length *
              SuccinctRank.machineWordBits bits.length)))).payload.length

def lcg (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

def randBits (seed L : Nat) : List Bool :=
  (List.range L).map (fun i =>
    (Nat.rec (motive := fun _ => Nat) seed (fun _ s => lcg s) (i + 1)) % 2 == 0)

def densityFamily (L : Nat) : List (List Bool) :=
  [ List.replicate L true
  , List.replicate L false
  , (List.range L).map (fun i => i % 2 == 0)
  , (List.range L).map (fun i => i < L / 2)
  , (List.range L).map (fun i => i % 7 == 0)
  , (List.range L).map (fun i => i % 13 < 2)
  , randBits 3 L
  , randBits 4242 L ]

#eval do
  IO.println "== ARBITRARY-DENSITY BITS (not bpCodes): L, distinct rawSup, distinct rawBlk, #distinct bitlists, popcounts =="
  for L in [0,1,2,3,4,7,8,15,16,17,31,32,33,63,64,100,127,128,200,255,256,400] do
    let fam := densityFamily L
    let sups := (fam.map rawSup).eraseDups
    let blks := (fam.map rawBlk).eraseDups
    let dist := fam.eraseDups.length
    let pops := (fam.map (fun (b : List Bool) => (b.filter id).length)).eraseDups
    IO.println s!"{L} {sups} {blks} {dist} pops={pops}"

/-! ## Attack B: same length, ADVERSARIAL entry values.
    Print the actual sample ENTRY lists for two same-length bit vectors to
    confirm the samples really differ in value while the payload length does not. -/

#eval do
  let L := 32
  let a := List.replicate L true
  let b := (List.range L).map (fun i => i % 2 == 0)
  let ea := SuccinctRank.canonicalSuperRankEntries true a (w L) (w L)
  let eb := SuccinctRank.canonicalSuperRankEntries true b (w L) (w L)
  let ba := SuccinctRank.canonicalBlockRankEntries true a (w L) (w L)
  let bb := SuccinctRank.canonicalBlockRankEntries true b (w L) (w L)
  IO.println s!"L=32 superEntries all-true={ea} alternating={eb} equal?={ea == eb}"
  IO.println s!"L=32 blockEntries all-true={ba} alternating={bb} equal?={ba == bb}"
  IO.println s!"lengths: {ea.length} {eb.length} {ba.length} {bb.length}"
  IO.println s!"rawSup: {rawSup a} {rawSup b}   rawBlk: {rawBlk a} {rawBlk b}"

/-! ## Attack C: universalize the size->n bridge on the shape-quantified
    theorem surface actually used by the headline theorems. -/

def sup' (s : Sh) : Nat := builtRelativeSplitBPCloseRankSuperOverhead s
def blk' (s : Sh) : Nat := builtRelativeSplitBPCloseRankBlockOverhead s

def predSup (n : Nat) : Nat :=
  let ww := SuccinctRank.machineWordBits (2 * n)
  (2 * n / ww / ww + 1) * ww + (2 * n / ww / ww + 1) * ww

def predBlk (n : Nat) : Nat :=
  let ww := SuccinctRank.machineWordBits (2 * n)
  let bb := SuccinctRank.machineWordBits (ww * ww)
  (2 * n / ww + 1) * bb + (2 * n / ww + 1) * bb

theorem adv_sup_closed (s : Sh) : sup' s = predSup s.size := by
  unfold sup' predSup builtRelativeSplitBPCloseRankSuperOverhead
  rw [SuccinctRank.canonicalSuperRankSampleTables_payload_length,
    canonicalSuperRankEntries_length, canonicalSuperRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    Cartesian.CartesianShape.bpCode_length]

theorem adv_blk_closed (s : Sh) : blk' s = predBlk s.size := by
  unfold blk' predBlk builtRelativeSplitBPCloseRankBlockOverhead
  rw [SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan_payload_length,
    canonicalBlockRankEntries_length, canonicalBlockRankEntries_length]
  simp [builtRelativeSplitBPCloseRankWordSize,
    builtRelativeSplitBPCloseRankBlockWidth,
    Cartesian.CartesianShape.bpCode_length]

/-- On the exact universe the headline theorems quantify over
    (`shape ∈ Cartesian.shapesOfSize n`), both overheads are literally
    `predSup n` / `predBlk n` -- no shape appears on the right. -/
theorem adv_shapesOfSize_closed_form {n : Nat} {s : Sh}
    (h : s ∈ Cartesian.shapesOfSize n) :
    sup' s = predSup n /\ blk' s = predBlk n := by
  have hsize : s.size = n :=
    Cartesian.ShapeOfSize.size_eq (Cartesian.mem_shapesOfSize_shapeOfSize h)
  constructor
  · rw [adv_sup_closed, hsize]
  · rw [adv_blk_closed, hsize]

#print axioms adv_shapesOfSize_closed_form

end AdvF34b
