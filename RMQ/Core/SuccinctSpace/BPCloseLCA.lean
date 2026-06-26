import RMQ.Core.SuccinctSpace.BroadwordRMQ

namespace RMQ

namespace SuccinctSpace

/--
Stored one-read directory for the BP LCA-close primitive.

Given the close positions of two inorder endpoints, this component reads a
stored navigation table and returns the close position of their BP LCA.  The
table is intentionally separated from the select/rank plumbing below: stored
rank/select now has its own faithful component theorem, while this table is the
remaining navigation slot for the broadword/microtable implementation.
-/
structure StoredBPCloseLCADirectory
    (n overhead : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  encodeAux : Aux -> List Bool
  decodeTable : List Bool -> TableModel.IndexedSeq (Option Nat)
  slotIndex : Nat -> Nat -> Nat
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (encodeAux (buildAux shape)).length = overhead
  entry_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len leftClose rightClose : Nat},
          0 < len ->
            left + len <= n ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  (decodeTable
                    (shape.bpCode ++ encodeAux (buildAux shape))).get?
                      (slotIndex leftClose rightClose) =
                    some
                      (bpCloseOfInorder? shape
                        (scanWindow shape.representative left len))

namespace StoredBPCloseLCADirectory

def lcaCloseCosted
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    (payload : List Bool) (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    ((directory.decodeTable payload).getCosted
      (directory.slotIndex leftClose rightClose))

theorem lcaCloseCosted_cost
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    (payload : List Bool) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted payload leftClose rightClose).cost =
      TableModel.indexedReadCost := by
  simp [lcaCloseCosted, Costed.map_cost,
    TableModel.IndexedSeq.getCosted_cost]

theorem lcaCloseCosted_cost_le_one
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    (payload : List Bool) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted payload leftClose rightClose).cost <= 1 := by
  simp [directory.lcaCloseCosted_cost payload leftClose rightClose,
    TableModel.indexedReadCost]

theorem lcaCloseCosted_exact
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len leftClose rightClose : Nat}
    (hlen : 0 < len) (hbound : left + len <= n)
    (hleftClose : bpCloseOfInorder? shape left = some leftClose)
    (hrightClose :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose) :
    (directory.lcaCloseCosted
      (shape.bpCode ++ directory.encodeAux (directory.buildAux shape))
      leftClose rightClose).erase =
        bpCloseOfInorder? shape
          (scanWindow shape.representative left len) := by
  have hentry :=
    directory.entry_exact hshape hlen hbound hleftClose hrightClose
  simp [lcaCloseCosted, TableModel.IndexedSeq.getCosted,
    TableModel.IndexedSeq.toAccess, TableModel.IndexedAccess.getCosted,
    Costed.map, hentry]

theorem profile
    {n overhead : Nat}
    (directory : StoredBPCloseLCADirectory n overhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.encodeAux (directory.buildAux shape)).length =
          overhead) /\
      (forall payload leftClose rightClose,
        (directory.lcaCloseCosted payload leftClose rightClose).cost <= 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (directory.lcaCloseCosted
                      (shape.bpCode ++
                        directory.encodeAux (directory.buildAux shape))
                      leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.aux_length_eq hshape
  · constructor
    · intro payload leftClose rightClose
      exact directory.lcaCloseCosted_cost_le_one payload leftClose rightClose
    · intro shape hshape left len leftClose rightClose
        hlen hbound hleftClose hrightClose
      exact directory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose

end StoredBPCloseLCADirectory

/--
Payload-live one-read directory for the BP LCA-close primitive.

This is the representation-refinement version of `StoredBPCloseLCADirectory`:
the built auxiliary state carries a fixed-width optional-Nat table, and the
query reads that table directly.  It still leaves the asymptotically succinct
construction of the table to the final navigation implementation.
-/
structure PayloadLiveBPCloseLCADirectory
    (n overhead : Nat) where
  Aux : Type
  buildAux : Cartesian.CartesianShape -> Aux
  fieldWidth : Nat
  entries : Aux -> List (Option Nat)
  table : (aux : Aux) -> FixedWidthOptionNatTable (entries aux) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  aux_length_eq :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        ((table (buildAux shape)).payload).length = overhead
  entry_exact :
    forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        forall {left len leftClose rightClose : Nat},
          0 < len ->
            left + len <= n ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  ((table (buildAux shape)).readCosted
                    (slotIndex leftClose rightClose)).erase =
                    some
                      (bpCloseOfInorder? shape
                        (scanWindow shape.representative left len))

namespace PayloadLiveBPCloseLCADirectory

def encodeAux
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) : List Bool :=
  (directory.table aux).payload

def lcaCloseCosted
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    ((directory.table aux).readCosted
      (directory.slotIndex leftClose rightClose))

theorem lcaCloseCosted_cost
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted aux leftClose rightClose).cost = 1 := by
  simp [lcaCloseCosted, Costed.map_cost]

theorem lcaCloseCosted_cost_le_one
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    (aux : directory.Aux) (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted aux leftClose rightClose).cost <= 1 := by
  simp [directory.lcaCloseCosted_cost aux leftClose rightClose]

theorem lcaCloseCosted_exact
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead)
    {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len leftClose rightClose : Nat}
    (hlen : 0 < len) (hbound : left + len <= n)
    (hleftClose : bpCloseOfInorder? shape left = some leftClose)
    (hrightClose :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose) :
    (directory.lcaCloseCosted (directory.buildAux shape)
      leftClose rightClose).erase =
        bpCloseOfInorder? shape
          (scanWindow shape.representative left len) := by
  have hentry :=
    directory.entry_exact hshape hlen hbound hleftClose hrightClose
  simp [lcaCloseCosted, Costed.erase_map, hentry]

theorem profile
    {n overhead : Nat}
    (directory : PayloadLiveBPCloseLCADirectory n overhead) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        (directory.encodeAux (directory.buildAux shape)).length =
          overhead) /\
      (forall aux leftClose rightClose,
        (directory.lcaCloseCosted aux leftClose rightClose).cost <= 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (directory.lcaCloseCosted
                      (directory.buildAux shape)
                      leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)) := by
  constructor
  · intro shape hshape
    exact directory.aux_length_eq hshape
  · constructor
    · intro aux leftClose rightClose
      exact directory.lcaCloseCosted_cost_le_one aux leftClose rightClose
    · intro shape hshape left len leftClose rightClose
        hlen hbound hleftClose hrightClose
      exact directory.lcaCloseCosted_exact hshape hlen hbound
        hleftClose hrightClose

/--
Build a payload-live BP LCA-close directory from fixed-width optional entries.

This is only a representation constructor: the caller still supplies the actual
navigation entries, their field-width bound, and the semantic exactness proof.
It keeps the one-read query path tied to the counted fixed-width payload table.
-/
def ofEntries
    (n overhead fieldWidth : Nat)
    (Aux : Type)
    (buildAux : Cartesian.CartesianShape -> Aux)
    (entries : Aux -> List (Option Nat))
    (slotIndex : Nat -> Nat -> Nat)
    (hentryBound :
      forall (aux : Aux) {entry : Option Nat} {value : Nat},
        List.Mem entry (entries aux) ->
          entry = some value -> value < 2 ^ fieldWidth)
    (hlength :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (entries (buildAux shape)).length *
              optionNatWordWidth fieldWidth =
            overhead)
    (hentryExact :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (entries (buildAux shape))[
                        slotIndex leftClose rightClose]? =
                      some
                        (bpCloseOfInorder? shape
                          (scanWindow shape.representative left len))) :
    PayloadLiveBPCloseLCADirectory n overhead where
  Aux := Aux
  buildAux := buildAux
  fieldWidth := fieldWidth
  entries := entries
  table aux :=
    FixedWidthOptionNatTable.ofEntries
      (entries aux) fieldWidth (hentryBound aux)
  slotIndex := slotIndex
  aux_length_eq := by
    intro shape hshape
    simpa [FixedWidthOptionNatTable.payload_length]
      using hlength hshape
  entry_exact := by
    intro shape hshape left len leftClose rightClose
      hlen hbound hleftClose hrightClose
    simpa using
      hentryExact hshape hlen hbound hleftClose hrightClose

theorem ofEntries_profile
    (n overhead fieldWidth : Nat)
    (Aux : Type)
    (buildAux : Cartesian.CartesianShape -> Aux)
    (entries : Aux -> List (Option Nat))
    (slotIndex : Nat -> Nat -> Nat)
    (hentryBound :
      forall (aux : Aux) {entry : Option Nat} {value : Nat},
        List.Mem entry (entries aux) ->
          entry = some value -> value < 2 ^ fieldWidth)
    (hlength :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          (entries (buildAux shape)).length *
              optionNatWordWidth fieldWidth =
            overhead)
    (hentryExact :
      forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    (entries (buildAux shape))[
                        slotIndex leftClose rightClose]? =
                      some
                        (bpCloseOfInorder? shape
                          (scanWindow shape.representative left len))) :
    (forall {shape : Cartesian.CartesianShape},
      List.Mem shape (Cartesian.shapesOfSize n) ->
        ((ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
          hentryBound hlength hentryExact).encodeAux
            ((ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
              hentryBound hlength hentryExact).buildAux shape)).length =
          overhead) /\
      (forall aux leftClose rightClose,
        ((ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
          hentryBound hlength hentryExact).lcaCloseCosted
            aux leftClose rightClose).cost <= 1) /\
      (forall {shape : Cartesian.CartesianShape},
        List.Mem shape (Cartesian.shapesOfSize n) ->
          forall {left len leftClose rightClose : Nat},
            0 < len ->
              left + len <= n ->
                bpCloseOfInorder? shape left = some leftClose ->
                  bpCloseOfInorder? shape (left + len - 1) =
                      some rightClose ->
                    ((ofEntries n overhead fieldWidth Aux buildAux entries
                      slotIndex hentryBound hlength hentryExact).lcaCloseCosted
                        ((ofEntries n overhead fieldWidth Aux buildAux entries
                          slotIndex hentryBound hlength hentryExact).buildAux
                            shape)
                        leftClose rightClose).erase =
                      bpCloseOfInorder? shape
                        (scanWindow shape.representative left len)) := by
  exact
    (ofEntries n overhead fieldWidth Aux buildAux entries slotIndex
      hentryBound hlength hentryExact).profile

end PayloadLiveBPCloseLCADirectory

/-- Family of stored one-read BP LCA-close directories. -/
structure StoredBPCloseLCAFamily
    (overhead : Nat -> Nat) where
  directory :
    forall n : Nat, StoredBPCloseLCADirectory n (overhead n)
  overhead_littleO : LittleOLinear overhead

namespace StoredBPCloseLCAFamily

theorem constant_lca_close_profile
    {overhead : Nat -> Nat}
    (family : StoredBPCloseLCAFamily overhead) :
    LittleOLinear overhead /\
      forall n : Nat,
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            ((family.directory n).encodeAux
              ((family.directory n).buildAux shape)).length =
              overhead n) /\
        (forall payload leftClose rightClose,
          ((family.directory n).lcaCloseCosted
            payload leftClose rightClose).cost <= 1) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len leftClose rightClose : Nat},
              0 < len ->
                left + len <= n ->
                  bpCloseOfInorder? shape left = some leftClose ->
                    bpCloseOfInorder? shape (left + len - 1) =
                        some rightClose ->
                      ((family.directory n).lcaCloseCosted
                        (shape.bpCode ++
                          (family.directory n).encodeAux
                            ((family.directory n).buildAux shape))
                        leftClose rightClose).erase =
                        bpCloseOfInorder? shape
                          (scanWindow shape.representative left len)) := by
  constructor
  · exact family.overhead_littleO
  · intro n
    exact (family.directory n).profile

end StoredBPCloseLCAFamily

end SuccinctSpace

end RMQ
