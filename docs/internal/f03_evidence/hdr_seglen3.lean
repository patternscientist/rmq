import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
HEADER-SCHEMA part C' -- same question as part C, but the access directory is
built ONCE per shape and every select-side component length is read off that one
build (part C rebuilt it 29 times per shape and did not terminate).

Question: which packed-layout component lengths are size-only, and which vary with
CONTENT at equal size?  A component whose length varies at equal size has a base
offset that is NOT computable from n, so it must become a header field.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose
open RMQ.BPNavigation

namespace HdrC3

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

def cliff (n : Nat) : CartesianShape :=
  .node (leftSpine (n / 2)) (rightSpine (n - n / 2 - 1))

/-- ONE directory build per shape; all select component payload lengths from it. -/
def selLens (s : CartesianShape) : List (String × Nat) :=
  let d := concreteBPCloseNavigationRelativeSplitAccessFamily.directory s
  let sd := d.selectData
  [ ("dirPayloadTotal",   d.payload.length)
  , ("rankAux",           d.rankData.auxPayload.length)
  , ("selectPayload",     sd.payload.length)
  , ("selSuperBaseOcc",   sd.superTable.baseOccurrenceTable.payload.length)
  , ("selSuperBaseWIdx",  sd.superTable.baseWordIndexTable.payload.length)
  , ("selSuperRankBefore",sd.superTable.rankBeforeTable.payload.length)
  , ("selSuperFirstOff",  sd.superTable.firstOffsetTable.payload.length)
  , ("selLocalBaseOcc",   sd.localTable.baseOccurrenceTable.payload.length)
  , ("selLocalBaseWIdx",  sd.localTable.baseWordIndexTable.payload.length)
  , ("selLocalRankBefore",sd.localTable.rankBeforeTable.payload.length)
  , ("selLocalFirstOff",  sd.localTable.firstOffsetTable.payload.length)
  , ("selLongFlagBits",   sd.longFlagBits.length)
  , ("selLongRelative",   sd.longSuperRelativeTable.payload.length)
  , ("selSparseFlagBits", sd.sparseDirectory.flagBits.length)
  , ("selSparseRelative", sd.sparseDirectory.relativeTable.payload.length)
  ]

/-- The n-only space BUDGETS the layout pads these regions up to. -/
def budgets (n : Nat) : List (String × Nat) :=
  [ ("accessOverheadBudget", relativeSplitSparseExceptionBPCloseAccessOverhead n)
  , ("closeOverheadBudget",  compactBPCloseOverhead n)
  , ("rankOverheadBudget",   relativeSplitSparseExceptionBPCloseRankOverhead n)
  , ("selectOverheadBudget",
      SuccinctSelect.canonicalRelativeSplitSparseExceptionFalseSelectOverhead n)
  , ("longRelTableBudget",
      SuccinctSelect.compactLongSuperRelativeTableOverhead n)
  ]

def go (n : Nat) : String :=
  let a := selLens (leftSpine n)
  let b := selLens (rightSpine n)
  let c := selLens (cliff n)
  let rows := a.map (fun (nm, v) =>
    let vb := (b.find? (fun q => q.1 = nm)).map (·.2) |>.getD 0
    let vc := (c.find? (fun q => q.1 = nm)).map (·.2) |>.getD 0
    s!"  {nm}: L={v} R={vb} C={vc}  agree={v = vb && v = vc}")
  let bs := (budgets n).map (fun (nm, v) => s!"  BUDGET {nm} = {v}")
  s!"n={n}\n" ++ String.intercalate "\n" (rows ++ bs)

#eval IO.println (go 32)
#eval IO.println (go 64)
#eval IO.println (go 128)


end HdrC3
