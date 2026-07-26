import RMQ.Core.SuccinctFinalStoreParam
import RMQ.Core.BPNavigationRAM

/-!
HEADER-SCHEMA part C -- THE PACKED-LAYOUT LENGTH INVENTORY.

For the packed target the header must supply exactly those component BASE OFFSETS
that are not computable from n. Base offsets are prefix sums of component LENGTHS.
So: measure the length of EVERY constructor of
`ConcreteBPNativeSuccinctRMQFlatPayloadSource` (all 29 -- exhaustive, not
representative) on structurally extreme shapes of equal size.

length agrees across shapes at equal size  => base is size-only => S, no header field.
length varies                              => base must be an H header field.
-/

open RMQ
open RMQ.Cartesian
open RMQ.SuccinctFinal
open RMQ.SuccinctClose
open RMQ.BPNavigation

namespace HdrC

instance : Inhabited CartesianShape := ⟨CartesianShape.empty⟩

def leftSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (leftSpine n) .empty

def rightSpine : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node .empty (rightSpine n)

partial def balanced : Nat -> CartesianShape
  | 0 => .empty
  | Nat.succ n => .node (balanced (n / 2)) (balanced (n - n / 2))

def cliff (n : Nat) : CartesianShape :=
  .node (leftSpine (n / 2)) (rightSpine (n - n / 2 - 1))

/-- ALL 29 constructors of the flat payload source. -/
def allSources : List (String × ConcreteBPNativeSuccinctRMQFlatPayloadSource) :=
  [ ("bpCode", .bpCode)
  , ("selSuperBaseOcc", .selectSuperBaseOccurrence)
  , ("selSuperBaseWordIdx", .selectSuperBaseWordIndex)
  , ("selSuperRankBefore", .selectSuperRankBefore)
  , ("selSuperFirstOffset", .selectSuperFirstOffset)
  , ("selLocalBaseOcc", .selectLocalBaseOccurrence)
  , ("selLocalBaseWordIdx", .selectLocalBaseWordIndex)
  , ("selLocalRankBefore", .selectLocalRankBefore)
  , ("selLocalFirstOffset", .selectLocalFirstOffset)
  , ("selLongFlagRankSuperT", .selectLongFlagRankSuperTrue)
  , ("selLongFlagRankBlockT", .selectLongFlagRankBlockTrue)
  , ("selLongFlagBits", .selectLongFlagBits)
  , ("selLongRelative", .selectLongRelative)
  , ("selSparseRankSuperT", .selectSparseRankSuperTrue)
  , ("selSparseRankBlockT", .selectSparseRankBlockTrue)
  , ("selSparseFlagBits", .selectSparseFlagBits)
  , ("selSparseRelative", .selectSparseRelative)
  , ("finalRankSuperFalse", .finalRankSuperFalse)
  , ("finalRankBlockFalse", .finalRankBlockFalse)
  , ("finalRankBPCodeAlias", .finalRankBPCodeAlias)
  , ("closeSummaryBaseline", .closeSummaryBaseline)
  , ("closeSummaryMinRel", .closeSummaryMinRel)
  , ("closeSummaryMaxRel", .closeSummaryMaxRel)
  , ("closeSummaryArgOffset", .closeSummaryArgOffset)
  , ("closeInteriorLocal", .closeInteriorLocal)
  , ("closeInteriorGlobal", .closeInteriorGlobal)
  , ("closeFSInteriorMin", .closeFiniteSmallInteriorMin)
  , ("closeFSInteriorArg", .closeFiniteSmallInteriorArg)
  , ("closeFSSameBlock", .closeFiniteSmallSameBlock)
  ]

/-- (words, payloadBits) for one component. -/
def measure (s : CartesianShape)
    (src : ConcreteBPNativeSuccinctRMQFlatPayloadSource) : Nat × Nat :=
  ( (concreteBPCloseNavigationPayloadSourceWords s src).size
  , (concreteBPCloseNavigationPayloadSourcePayload s src).length )

def go (n : Nat) : String :=
  let shapes := [("L", leftSpine n), ("R", rightSpine n), ("C", cliff n)]
  String.intercalate "\n"
    (allSources.map (fun (nm, src) =>
      let ms := shapes.map (fun p => measure p.2 src)
      let agree := ms.all (fun m => m = ms.headD (0,0))
      s!"  {nm}: {ms}  agree={agree}"))

#eval IO.println s!"===== n=384 (summary INACTIVE) =====\n{go 384}"
#eval IO.println s!"===== n=512 (summary ACTIVE) =====\n{go 512}"

end HdrC
