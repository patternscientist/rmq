import RMQ.Core.SuccinctSpace.Asymptotics
import RMQ.Core.SuccinctSpace.WordStore

/-!
# Two-level reconstruction machinery

This module isolates the small arithmetic and table substrate used by concrete
compressed/FID route directories.  A wide, sparse superblock table stores an
absolute cumulative value; a narrow per-block table stores the relative
increment since that superblock boundary.  One read from each reconstructs the
absolute cumulative value.
-/

namespace RMQ

namespace SuccinctSpace

theorem superblock_decompose (superSize i : Nat) :
    i / superSize * superSize + i % superSize = i := by
  rw [Nat.mul_comm (i / superSize) superSize]
  exact Nat.div_add_mod i superSize

theorem superblock_offset_lt (superSize i : Nat) (hS : 0 < superSize) :
    i % superSize < superSize :=
  Nat.mod_lt i hS

theorem superblock_boundary_le (superSize i : Nat) :
    i / superSize * superSize <= i :=
  Nat.div_mul_le_self i superSize

def twoLevelRelative (f : Nat -> Nat) (superSize i : Nat) : Nat :=
  f i - f (i / superSize * superSize)

theorem twoLevelRelative_add (f : Nat -> Nat) (superSize i : Nat)
    (hle : f (i / superSize * superSize) <= f i) :
    f (i / superSize * superSize) + twoLevelRelative f superSize i = f i := by
  unfold twoLevelRelative
  omega

theorem twoLevelRelative_le (f : Nat -> Nat) (superSize i : Nat) :
    twoLevelRelative f superSize i <= f i := by
  unfold twoLevelRelative
  omega

def cumSum (g : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | j + 1 => cumSum g j + g j

@[simp] theorem cumSum_zero (g : Nat -> Nat) : cumSum g 0 = 0 := rfl

@[simp] theorem cumSum_succ (g : Nat -> Nat) (j : Nat) :
    cumSum g (j + 1) = cumSum g j + g j := rfl

theorem cumSum_le_add (g : Nat -> Nat) (a d : Nat) :
    cumSum g a <= cumSum g (a + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have heq : cumSum g (a + (d + 1)) = cumSum g (a + d) + g (a + d) := by
        rw [show a + (d + 1) = (a + d) + 1 from by omega]
        rfl
      omega

theorem cumSum_add_sub_le (g : Nat -> Nat) (M : Nat)
    (hg : forall k, g k <= M) (a d : Nat) :
    cumSum g (a + d) - cumSum g a <= d * M := by
  induction d with
  | zero => simp
  | succ d ih =>
      have heq : cumSum g (a + (d + 1)) = cumSum g (a + d) + g (a + d) := by
        rw [show a + (d + 1) = (a + d) + 1 from by omega]
        rfl
      have hmono : cumSum g a <= cumSum g (a + d) :=
        cumSum_le_add g a d
      calc
        cumSum g (a + (d + 1)) - cumSum g a
            = (cumSum g (a + d) - cumSum g a) + g (a + d) := by
              rw [heq]
              omega
        _ <= d * M + M := Nat.add_le_add ih (hg (a + d))
        _ = (d + 1) * M := (Nat.succ_mul d M).symm

theorem twoLevelRelative_cumSum_le (g : Nat -> Nat) (M superSize i : Nat)
    (hg : forall k, g k <= M) :
    twoLevelRelative (cumSum g) superSize i <= (i % superSize) * M := by
  unfold twoLevelRelative
  have hdecomp : i = i / superSize * superSize + i % superSize :=
    (superblock_decompose superSize i).symm
  have hsub :=
    cumSum_add_sub_le g M hg (i / superSize * superSize) (i % superSize)
  rw [<- hdecomp] at hsub
  exact hsub

def twoLevelReadCosted {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize)
    (superIdx blockIdx : Nat) : Costed Nat :=
  Costed.bind (store.store.readWordCosted superIdx) fun base? =>
    Costed.bind (store.store.readWordCosted blockIdx) fun rel? =>
      Costed.pure (bitsToNatLE (base?.getD []) + bitsToNatLE (rel?.getD []))

theorem twoLevelReadCosted_cost {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize) (superIdx blockIdx : Nat) :
    (twoLevelReadCosted store superIdx blockIdx).cost = 2 := by
  simp [twoLevelReadCosted]

theorem twoLevelReadCosted_erase {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize) (superIdx blockIdx : Nat) :
    (twoLevelReadCosted store superIdx blockIdx).erase =
      bitsToNatLE ((store.store.words[superIdx]?).getD []) +
        bitsToNatLE ((store.store.words[blockIdx]?).getD []) := by
  simp [twoLevelReadCosted]

theorem twoLevelReadCosted_erase_eq {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize)
    (superIdx blockIdx width base rel : Nat)
    (hbase : store.store.words[superIdx]? = some (natToBitsLE width base))
    (hrel : store.store.words[blockIdx]? = some (natToBitsLE width rel))
    (hb : base < 2 ^ width) (hr : rel < 2 ^ width) :
    (twoLevelReadCosted store superIdx blockIdx).erase = base + rel := by
  rw [twoLevelReadCosted_erase, hbase, hrel]
  simp only [Option.getD_some]
  rw [bitsToNatLE_natToBitsLE_of_lt hb,
    bitsToNatLE_natToBitsLE_of_lt hr]

theorem twoLevelReadCosted_reconstruct {payload : List Bool} {wordSize : Nat}
    (store : BoundedPayloadWordStore payload wordSize)
    (superIdx blockIdx width : Nat) (f : Nat -> Nat) (superSize i : Nat)
    (hbase :
      store.store.words[superIdx]? =
        some (natToBitsLE width (f (i / superSize * superSize))))
    (hrel :
      store.store.words[blockIdx]? =
        some (natToBitsLE width (twoLevelRelative f superSize i)))
    (hb : f (i / superSize * superSize) < 2 ^ width)
    (hr : twoLevelRelative f superSize i < 2 ^ width)
    (hle : f (i / superSize * superSize) <= f i) :
    (twoLevelReadCosted store superIdx blockIdx).erase = f i := by
  rw [twoLevelReadCosted_erase_eq store superIdx blockIdx width
    (f (i / superSize * superSize)) (twoLevelRelative f superSize i)
    hbase hrel hb hr]
  exact twoLevelRelative_add f superSize i hle

def twoLevelReadCosted2 {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat} (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx : Nat) : Costed Nat :=
  Costed.bind (superStore.store.readWordCosted superIdx) fun base? =>
    Costed.bind (blockStore.store.readWordCosted blockIdx) fun rel? =>
      Costed.pure (bitsToNatLE (base?.getD []) + bitsToNatLE (rel?.getD []))

theorem twoLevelReadCosted2_cost {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat} (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx : Nat) :
    (twoLevelReadCosted2 superStore blockStore superIdx blockIdx).cost = 2 := by
  simp [twoLevelReadCosted2]

theorem twoLevelReadCosted2_erase {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat} (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx : Nat) :
    (twoLevelReadCosted2 superStore blockStore superIdx blockIdx).erase =
      bitsToNatLE ((superStore.store.words[superIdx]?).getD []) +
        bitsToNatLE ((blockStore.store.words[blockIdx]?).getD []) := by
  simp [twoLevelReadCosted2]

theorem twoLevelReadCosted2_erase_eq {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat} (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx wsuper wblock base rel : Nat)
    (hbase : superStore.store.words[superIdx]? =
      some (natToBitsLE wsuper base))
    (hrel : blockStore.store.words[blockIdx]? =
      some (natToBitsLE wblock rel))
    (hb : base < 2 ^ wsuper) (hr : rel < 2 ^ wblock) :
    (twoLevelReadCosted2 superStore blockStore superIdx blockIdx).erase =
      base + rel := by
  rw [twoLevelReadCosted2_erase, hbase, hrel]
  simp only [Option.getD_some]
  rw [bitsToNatLE_natToBitsLE_of_lt hb,
    bitsToNatLE_natToBitsLE_of_lt hr]

theorem twoLevelReadCosted2_reconstruct {ps : List Bool} {ws : Nat}
    (superStore : BoundedPayloadWordStore ps ws)
    {pb : List Bool} {wb : Nat} (blockStore : BoundedPayloadWordStore pb wb)
    (superIdx blockIdx wsuper wblock : Nat) (f : Nat -> Nat)
    (superSize i : Nat)
    (hbase :
      superStore.store.words[superIdx]? =
        some (natToBitsLE wsuper (f (i / superSize * superSize))))
    (hrel :
      blockStore.store.words[blockIdx]? =
        some (natToBitsLE wblock (twoLevelRelative f superSize i)))
    (hb : f (i / superSize * superSize) < 2 ^ wsuper)
    (hr : twoLevelRelative f superSize i < 2 ^ wblock)
    (hle : f (i / superSize * superSize) <= f i) :
    (twoLevelReadCosted2 superStore blockStore superIdx blockIdx).erase = f i := by
  rw [twoLevelReadCosted2_erase_eq superStore blockStore superIdx blockIdx
    wsuper wblock (f (i / superSize * superSize))
    (twoLevelRelative f superSize i) hbase hrel hb hr]
  exact twoLevelRelative_add f superSize i hle

def fixedWidthTableWords (width : Nat) (entries : List Nat) :
    List (List Bool) :=
  entries.map (natToBitsLE width)

theorem fixedWidthTableWords_get? (width : Nat) (entries : List Nat) (j : Nat) :
    (fixedWidthTableWords width entries)[j]? =
      (entries[j]?).map (natToBitsLE width) := by
  simp [fixedWidthTableWords]

theorem fixedWidthTableWords_length_le {width : Nat} {entries : List Nat}
    {word : List Bool}
    (hmem : List.Mem word (fixedWidthTableWords width entries)) :
    word.length <= width := by
  unfold fixedWidthTableWords at hmem
  cases List.mem_map.mp hmem with
  | intro e hrest =>
      cases hrest with
      | intro _ hword =>
          rw [<- hword]
          exact Nat.le_of_eq (natToBitsLE_length width e)

def fixedWidthTableStore (width : Nat) (entries : List Nat) :
    BoundedPayloadWordStore
      (flattenPayloadWords (fixedWidthTableWords width entries)) width where
  store :=
    { words := (fixedWidthTableWords width entries).toArray
      erases := by rw [List.toList_toArray] }
  word_length_le := by
    intro word hmem
    rw [List.toList_toArray] at hmem
    exact fixedWidthTableWords_length_le hmem

theorem fixedWidthTableStore_get? (width : Nat) (entries : List Nat)
    {j e : Nat} (hj : entries[j]? = some e) :
    (fixedWidthTableStore width entries).store.words[j]? =
      some (natToBitsLE width e) := by
  show ((fixedWidthTableWords width entries).toArray)[j]? =
    some (natToBitsLE width e)
  rw [List.getElem?_toArray, fixedWidthTableWords_get?, hj]
  rfl

end SuccinctSpace

end RMQ
