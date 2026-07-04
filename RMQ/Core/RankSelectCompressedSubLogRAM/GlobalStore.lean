import RMQ.Core.RankSelectCompressedSubLogRAM.Select

namespace RMQ

namespace RankSelectSpec

open GenericSelect

/-! ### Combined global payload-store replay -/

def subLogCompressedFIDGlobalAccessSegmentMap : Nat -> Nat
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | _ + 4 => 31

def subLogCompressedFIDGlobalRankSegmentMap : Nat -> Nat
  | 0 => 32
  | 1 => 33
  | 2 => 34
  | 3 => 35
  | 4 => 36
  | 5 => 37
  | _ + 6 => 63

def subLogCompressedFIDGlobalSelectSegmentMap : Nat -> Nat
  | 0 => 64
  | 1 => 65
  | 2 => 66
  | 3 => 67
  | 4 => 68
  | 5 => 69
  | 6 => 70
  | 7 => 71
  | 8 => 72
  | 9 => 73
  | 10 => 74
  | 11 => 75
  | 12 => 76
  | 13 => 77
  | 14 => 78
  | 15 => 79
  | 16 => 80
  | 17 => 81
  | 18 => 82
  | 19 => 83
  | _ + 20 => 95

/--
One target-indexed global store for the compressed/FID trace packets.

The access, rank, and select trace packets are relabeled into disjoint segment
ranges of this store.  The store is target-indexed because the current rank and
Clark-select routing payloads are target-specific.  The target-independent
global packet below keeps access shared and duplicates the true/false target
ranges in one store; this target-indexed packet remains useful as a lower-level
component theorem.
-/
def subLogCompressedFIDTargetGlobalTraceReadStore
    (bits : List Bool) (target : Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    match segment with
    | 0 => (subLogAccessTraceReadStore bits).readWord? 0 index
    | 1 => (subLogAccessTraceReadStore bits).readWord? 1 index
    | 2 => (subLogAccessTraceReadStore bits).readWord? 2 index
    | 3 => (subLogAccessTraceReadStore bits).readWord? 3 index
    | 31 => none
    | 32 => (subLogRankTraceReadStore bits target).readWord? 0 index
    | 33 => (subLogRankTraceReadStore bits target).readWord? 1 index
    | 34 => (subLogRankTraceReadStore bits target).readWord? 2 index
    | 35 => (subLogRankTraceReadStore bits target).readWord? 3 index
    | 36 => (subLogRankTraceReadStore bits target).readWord? 4 index
    | 37 => (subLogRankTraceReadStore bits target).readWord? 5 index
    | 63 => none
    | 64 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 0 index
    | 65 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 1 index
    | 66 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 2 index
    | 67 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 3 index
    | 68 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 4 index
    | 69 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 5 index
    | 70 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 6 index
    | 71 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 7 index
    | 72 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 8 index
    | 73 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 9 index
    | 74 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 10 index
    | 75 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 11 index
    | 76 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 12 index
    | 77 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 13 index
    | 78 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 14 index
    | 79 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 15 index
    | 80 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 16 index
    | 81 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 17 index
    | 82 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 18 index
    | 83 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? 19 index
    | 95 => none
    | _ => none

private theorem subLogCompressedFIDTargetGlobalTraceReadStore_access_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDTargetGlobalTraceReadStore bits target).readWord?
          (subLogCompressedFIDGlobalAccessSegmentMap segment) index =
        (subLogAccessTraceReadStore bits).readWord? segment index := by
  intro segment index
  match segment with
  | 0 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | 1 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | 2 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | 3 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap]
  | _ + 4 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalAccessSegmentMap,
        subLogAccessTraceReadStore]

private theorem subLogCompressedFIDTargetGlobalTraceReadStore_rank_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDTargetGlobalTraceReadStore bits target).readWord?
          (subLogCompressedFIDGlobalRankSegmentMap segment) index =
        (subLogRankTraceReadStore bits target).readWord? segment index := by
  intro segment index
  match segment with
  | 0 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 1 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 2 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 3 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 4 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | 5 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap]
  | _ + 6 =>
      simp [subLogCompressedFIDTargetGlobalTraceReadStore,
        subLogCompressedFIDGlobalRankSegmentMap,
        subLogRankTraceReadStore]

private theorem subLogCompressedFIDTargetGlobalTraceReadStore_select_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDTargetGlobalTraceReadStore bits target).readWord?
          (subLogCompressedFIDGlobalSelectSegmentMap segment) index =
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? segment index := by
  intro segment index
  match segment with
  | 0 =>
      rfl
  | 1 =>
      rfl
  | 2 =>
      rfl
  | 3 =>
      rfl
  | 4 =>
      rfl
  | 5 =>
      rfl
  | 6 =>
      rfl
  | 7 =>
      rfl
  | 8 =>
      rfl
  | 9 =>
      rfl
  | 10 =>
      rfl
  | 11 =>
      rfl
  | 12 =>
      rfl
  | 13 =>
      rfl
  | 14 =>
      rfl
  | 15 =>
      rfl
  | 16 =>
      rfl
  | 17 =>
      rfl
  | 18 =>
      rfl
  | 19 =>
      rfl
  | _ + 20 =>
      rfl

def subLogCompressedFIDGlobalAccessTraceResult
    (bits : List Bool) (i : Nat) : WordRAM.TraceResult (Option Bool) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    subLogCompressedFIDGlobalAccessSegmentMap
    (subLogAccessTraceResult bits i)

def subLogCompressedFIDGlobalRankTraceResult
    (bits : List Bool) (target : Bool) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    subLogCompressedFIDGlobalRankSegmentMap
    (subLogRankTraceResult bits target pos)

def subLogCompressedFIDGlobalSelectTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    subLogCompressedFIDGlobalSelectSegmentMap
    (subLogSelectFromPackedClarkRouteTraceResult bits target occurrence)

theorem subLogCompressedFIDTargetGlobalPayloadStore_execution_story
    (bits : List Bool) (target : Bool) :
    (forall i,
      (subLogCompressedFIDGlobalAccessTraceResult bits i).toCosted =
          subLogAccessInterpretedCosted bits i /\
        (subLogCompressedFIDGlobalAccessTraceResult bits i).toCosted =
          subLogAccessCosted bits i /\
        (forall event,
          event ∈ (subLogCompressedFIDGlobalAccessTraceResult bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈ (subLogCompressedFIDGlobalAccessTraceResult bits i).trace ->
            event.matchesReadStore
              (subLogCompressedFIDTargetGlobalTraceReadStore bits target))) /\
      (forall pos,
        (subLogCompressedFIDGlobalRankTraceResult
          bits target pos).toCosted =
            subLogRankInterpretedCosted bits target pos /\
          (subLogCompressedFIDGlobalRankTraceResult
            bits target pos).toCosted =
            subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (subLogCompressedFIDTargetGlobalTraceReadStore
                  bits target))) /\
      forall occurrence,
        (subLogCompressedFIDGlobalSelectTraceResult
          bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteInterpretedCosted
              bits target occurrence /\
          (subLogCompressedFIDGlobalSelectTraceResult
            bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteCosted bits target occurrence /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (subLogCompressedFIDTargetGlobalTraceReadStore
                  bits target)) := by
  constructor
  · intro i
    constructor
    · simp [subLogCompressedFIDGlobalAccessTraceResult,
        subLogAccessTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDGlobalAccessTraceResult,
        subLogAccessTraceResult_refines_interpretedCosted,
        subLogAccessInterpretedCosted_refines_subLogAccessCosted]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogAccessTraceResult bits i)
          (subLogAccessTraceReadStore bits)
          (subLogCompressedFIDTargetGlobalTraceReadStore bits target)
          subLogCompressedFIDGlobalAccessSegmentMap
          (subLogCompressedFIDTargetGlobalTraceReadStore_access_read
            bits target)
          (subLogAccessTraceResult_matchesReadStore bits i)
  constructor
  · intro pos
    constructor
    · simp [subLogCompressedFIDGlobalRankTraceResult,
        subLogRankTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDGlobalRankTraceResult,
        subLogRankTraceResult_refines_interpretedCosted,
        subLogRankInterpretedCosted_refines_subLogRankCosted]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogRankTraceResult bits target pos)
          (subLogRankTraceReadStore bits target)
          (subLogCompressedFIDTargetGlobalTraceReadStore bits target)
          subLogCompressedFIDGlobalRankSegmentMap
          (subLogCompressedFIDTargetGlobalTraceReadStore_rank_read
            bits target)
          (subLogRankTraceResult_matchesReadStore bits target pos)
  · intro occurrence
    constructor
    · simp [subLogCompressedFIDGlobalSelectTraceResult,
        subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDGlobalSelectTraceResult,
        subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted,
        subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence)
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (subLogCompressedFIDTargetGlobalTraceReadStore bits target)
          subLogCompressedFIDGlobalSelectSegmentMap
          (subLogCompressedFIDTargetGlobalTraceReadStore_select_read
            bits target)
          (subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
            bits target occurrence)

def subLogCompressedFIDAllTargetsGlobalRankSegmentMap
    (target : Bool) : Nat -> Nat :=
  match target with
  | false =>
      fun
        | 0 => 32
        | 1 => 33
        | 2 => 34
        | 3 => 35
        | 4 => 36
        | 5 => 37
        | _ + 6 => 63
  | true =>
      fun
        | 0 => 64
        | 1 => 65
        | 2 => 66
        | 3 => 67
        | 4 => 68
        | 5 => 69
        | _ + 6 => 95

def subLogCompressedFIDAllTargetsGlobalSelectSegmentMap
    (target : Bool) : Nat -> Nat :=
  match target with
  | false =>
      fun
        | 0 => 96
        | 1 => 97
        | 2 => 98
        | 3 => 99
        | 4 => 100
        | 5 => 101
        | 6 => 102
        | 7 => 103
        | 8 => 104
        | 9 => 105
        | 10 => 106
        | 11 => 107
        | 12 => 108
        | 13 => 109
        | 14 => 110
        | 15 => 111
        | 16 => 112
        | 17 => 113
        | 18 => 114
        | 19 => 115
        | _ + 20 => 127
  | true =>
      fun
        | 0 => 128
        | 1 => 129
        | 2 => 130
        | 3 => 131
        | 4 => 132
        | 5 => 133
        | 6 => 134
        | 7 => 135
        | 8 => 136
        | 9 => 137
        | 10 => 138
        | 11 => 139
        | 12 => 140
        | 13 => 141
        | 14 => 142
        | 15 => 143
        | 16 => 144
        | 17 => 145
        | 18 => 146
        | 19 => 147
        | _ + 20 => 159

/--
One target-independent global store for compressed/FID access/rank/select
trace packets.

The access payload range is shared once. Rank and select use disjoint
false/true target ranges, so one read store supports access, rank false,
rank true, select false, and select true simultaneously.
-/
def subLogCompressedFIDGlobalTraceReadStore
    (bits : List Bool) : WordRAM.ReadStore where
  readWord? segment index :=
    match segment with
    | 0 => (subLogAccessTraceReadStore bits).readWord? 0 index
    | 1 => (subLogAccessTraceReadStore bits).readWord? 1 index
    | 2 => (subLogAccessTraceReadStore bits).readWord? 2 index
    | 3 => (subLogAccessTraceReadStore bits).readWord? 3 index
    | 31 => none
    | 32 => (subLogRankTraceReadStore bits false).readWord? 0 index
    | 33 => (subLogRankTraceReadStore bits false).readWord? 1 index
    | 34 => (subLogRankTraceReadStore bits false).readWord? 2 index
    | 35 => (subLogRankTraceReadStore bits false).readWord? 3 index
    | 36 => (subLogRankTraceReadStore bits false).readWord? 4 index
    | 37 => (subLogRankTraceReadStore bits false).readWord? 5 index
    | 63 => none
    | 64 => (subLogRankTraceReadStore bits true).readWord? 0 index
    | 65 => (subLogRankTraceReadStore bits true).readWord? 1 index
    | 66 => (subLogRankTraceReadStore bits true).readWord? 2 index
    | 67 => (subLogRankTraceReadStore bits true).readWord? 3 index
    | 68 => (subLogRankTraceReadStore bits true).readWord? 4 index
    | 69 => (subLogRankTraceReadStore bits true).readWord? 5 index
    | 95 => none
    | 96 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 0 index
    | 97 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 1 index
    | 98 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 2 index
    | 99 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 3 index
    | 100 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 4 index
    | 101 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 5 index
    | 102 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 6 index
    | 103 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 7 index
    | 104 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 8 index
    | 105 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 9 index
    | 106 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 10 index
    | 107 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 11 index
    | 108 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 12 index
    | 109 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 13 index
    | 110 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 14 index
    | 111 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 15 index
    | 112 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 16 index
    | 113 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 17 index
    | 114 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 18 index
    | 115 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits false).readWord? 19 index
    | 127 => none
    | 128 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 0 index
    | 129 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 1 index
    | 130 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 2 index
    | 131 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 3 index
    | 132 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 4 index
    | 133 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 5 index
    | 134 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 6 index
    | 135 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 7 index
    | 136 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 8 index
    | 137 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 9 index
    | 138 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 10 index
    | 139 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 11 index
    | 140 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 12 index
    | 141 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 13 index
    | 142 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 14 index
    | 143 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 15 index
    | 144 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 16 index
    | 145 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 17 index
    | 146 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 18 index
    | 147 =>
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits true).readWord? 19 index
    | 159 => none
    | _ => none

inductive SubLogCompressedFIDGlobalPayloadComponent where
  | access
  | rank (target : Bool)
  | select (target : Bool)

namespace SubLogCompressedFIDGlobalPayloadComponent

def readStore
    (bits : List Bool) :
    SubLogCompressedFIDGlobalPayloadComponent -> WordRAM.ReadStore
  | access => subLogAccessTraceReadStore bits
  | rank target => subLogRankTraceReadStore bits target
  | select target => subLogSelectFromPackedClarkRouteTraceReadStore bits target

def segmentMap :
    SubLogCompressedFIDGlobalPayloadComponent -> Nat -> Nat
  | access => subLogCompressedFIDGlobalAccessSegmentMap
  | rank target => subLogCompressedFIDAllTargetsGlobalRankSegmentMap target
  | select target => subLogCompressedFIDAllTargetsGlobalSelectSegmentMap target

end SubLogCompressedFIDGlobalPayloadComponent

/--
Successful read events in the all-target global trace are backed by a concrete
component store and local segment.  Non-read events and failed reads are inert
for this predicate; it deliberately does not claim that padding is read.
-/
def subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked
    (bits : List Bool) : WordRAM.TraceEvent -> Prop
  | WordRAM.TraceEvent.readWord segment index (some word) =>
      exists component localSegment,
        SubLogCompressedFIDGlobalPayloadComponent.segmentMap component
            localSegment = segment /\
          (SubLogCompressedFIDGlobalPayloadComponent.readStore bits
            component).readWord? localSegment index = some word
  | WordRAM.TraceEvent.readWord _ _ none => True
  | WordRAM.TraceEvent.wordRank _ _ _ => True
  | WordRAM.TraceEvent.wordSelect _ _ _ => True
  | WordRAM.TraceEvent.syntheticCostOnlyPrimitive => True

private theorem subLogCompressedFIDGlobalTraceReadStore_access_read
    (bits : List Bool) :
    forall segment index,
      (subLogCompressedFIDGlobalTraceReadStore bits).readWord?
          (subLogCompressedFIDGlobalAccessSegmentMap segment) index =
        (subLogAccessTraceReadStore bits).readWord? segment index := by
  intro segment index
  match segment with
  | 0 =>
      rfl
  | 1 =>
      rfl
  | 2 =>
      rfl
  | 3 =>
      rfl
  | _ + 4 =>
      rfl

private theorem subLogCompressedFIDGlobalTraceReadStore_rank_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDGlobalTraceReadStore bits).readWord?
          (subLogCompressedFIDAllTargetsGlobalRankSegmentMap
            target segment) index =
        (subLogRankTraceReadStore bits target).readWord? segment index := by
  cases target <;> intro segment index
  · match segment with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | _ + 6 => rfl
  · match segment with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | _ + 6 => rfl

private theorem subLogCompressedFIDGlobalTraceReadStore_select_read
    (bits : List Bool) (target : Bool) :
    forall segment index,
      (subLogCompressedFIDGlobalTraceReadStore bits).readWord?
          (subLogCompressedFIDAllTargetsGlobalSelectSegmentMap
            target segment) index =
        (subLogSelectFromPackedClarkRouteTraceReadStore
          bits target).readWord? segment index := by
  cases target <;> intro segment index
  · match segment with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | 6 => rfl
    | 7 => rfl
    | 8 => rfl
    | 9 => rfl
    | 10 => rfl
    | 11 => rfl
    | 12 => rfl
    | 13 => rfl
    | 14 => rfl
    | 15 => rfl
    | 16 => rfl
    | 17 => rfl
    | 18 => rfl
    | 19 => rfl
    | _ + 20 => rfl
  · match segment with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | 6 => rfl
    | 7 => rfl
    | 8 => rfl
    | 9 => rfl
    | 10 => rfl
    | 11 => rfl
    | 12 => rfl
    | 13 => rfl
    | 14 => rfl
    | 15 => rfl
    | 16 => rfl
    | 17 => rfl
    | 18 => rfl
    | 19 => rfl
    | _ + 20 => rfl

def subLogCompressedFIDAllTargetsGlobalAccessTraceResult
    (bits : List Bool) (i : Nat) : WordRAM.TraceResult (Option Bool) :=
  subLogCompressedFIDGlobalAccessTraceResult bits i

def subLogCompressedFIDAllTargetsGlobalRankTraceResult
    (bits : List Bool) (target : Bool) (pos : Nat) :
    WordRAM.TraceResult Nat :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (subLogCompressedFIDAllTargetsGlobalRankSegmentMap target)
    (subLogRankTraceResult bits target pos)

def subLogCompressedFIDAllTargetsGlobalSelectTraceResult
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  WordRAM.TraceResult.relabelReadSegmentsWith
    (subLogCompressedFIDAllTargetsGlobalSelectSegmentMap target)
    (subLogSelectFromPackedClarkRouteTraceResult bits target occurrence)

theorem subLogCompressedFIDGlobalAccessTraceResult_successful_reads_backed
    (bits : List Bool) (i : Nat) :
    forall event,
      event ∈
          (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
            bits i).trace ->
        subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked bits event := by
  unfold subLogCompressedFIDAllTargetsGlobalAccessTraceResult
    subLogCompressedFIDGlobalAccessTraceResult
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, hlocal, rfl⟩
  cases localEvent with
  | readWord localSegment index word? =>
      cases word? with
      | none =>
          simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
            WordRAM.TraceEvent.relabelReadSegmentWith]
      | some word =>
          refine
            ⟨SubLogCompressedFIDGlobalPayloadComponent.access,
              localSegment, rfl, ?_⟩
          have hmatch :=
            subLogAccessTraceResult_matchesReadStore bits i
              (WordRAM.TraceEvent.readWord
                localSegment index (some word)) hlocal
          simpa [SubLogCompressedFIDGlobalPayloadComponent.readStore,
            WordRAM.TraceEvent.matchesReadStore] using hmatch
  | wordRank target limit result =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]
  | wordSelect target occurrence result =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]
  | syntheticCostOnlyPrimitive =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]

theorem subLogCompressedFIDGlobalRankTraceResult_successful_reads_backed
    (bits : List Bool) (target : Bool) (pos : Nat) :
    forall event,
      event ∈
          (subLogCompressedFIDAllTargetsGlobalRankTraceResult
            bits target pos).trace ->
        subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked bits event := by
  unfold subLogCompressedFIDAllTargetsGlobalRankTraceResult
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, hlocal, rfl⟩
  cases localEvent with
  | readWord localSegment index word? =>
      cases word? with
      | none =>
          simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
            WordRAM.TraceEvent.relabelReadSegmentWith]
      | some word =>
          refine
            ⟨SubLogCompressedFIDGlobalPayloadComponent.rank target,
              localSegment, rfl, ?_⟩
          have hmatch :=
            subLogRankTraceResult_matchesReadStore bits target pos
              (WordRAM.TraceEvent.readWord
                localSegment index (some word)) hlocal
          simpa [SubLogCompressedFIDGlobalPayloadComponent.readStore,
            WordRAM.TraceEvent.matchesReadStore] using hmatch
  | wordRank rankTarget limit result =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]
  | wordSelect selectTarget occurrence result =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]
  | syntheticCostOnlyPrimitive =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]

theorem subLogCompressedFIDGlobalSelectTraceResult_successful_reads_backed
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    forall event,
      event ∈
          (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
            bits target occurrence).trace ->
        subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked bits event := by
  unfold subLogCompressedFIDAllTargetsGlobalSelectTraceResult
  intro event hmem
  rcases List.mem_map.mp hmem with ⟨localEvent, hlocal, rfl⟩
  cases localEvent with
  | readWord localSegment index word? =>
      cases word? with
      | none =>
          simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
            WordRAM.TraceEvent.relabelReadSegmentWith]
      | some word =>
          refine
            ⟨SubLogCompressedFIDGlobalPayloadComponent.select target,
              localSegment, rfl, ?_⟩
          have hmatch :=
            subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
              bits target occurrence
              (WordRAM.TraceEvent.readWord
                localSegment index (some word)) hlocal
          simpa [SubLogCompressedFIDGlobalPayloadComponent.readStore,
            WordRAM.TraceEvent.matchesReadStore] using hmatch
  | wordRank rankTarget limit result =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]
  | wordSelect selectTarget occurrence result =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]
  | syntheticCostOnlyPrimitive =>
      simp [subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked,
        WordRAM.TraceEvent.relabelReadSegmentWith]

theorem subLogCompressedFIDGlobalPayloadStore_execution_story
    (bits : List Bool) :
    (forall i,
      (subLogCompressedFIDAllTargetsGlobalAccessTraceResult bits i).toCosted =
          subLogAccessInterpretedCosted bits i /\
        (subLogCompressedFIDAllTargetsGlobalAccessTraceResult bits i).toCosted =
          subLogAccessCosted bits i /\
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
                bits i).trace ->
            event.isReadWord \/ event.isWordPrimitive) /\
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
                bits i).trace ->
            event.matchesReadStore
              (subLogCompressedFIDGlobalTraceReadStore bits))) /\
      (forall target pos,
        (subLogCompressedFIDAllTargetsGlobalRankTraceResult
          bits target pos).toCosted =
            subLogRankInterpretedCosted bits target pos /\
          (subLogCompressedFIDAllTargetsGlobalRankTraceResult
            bits target pos).toCosted =
            subLogRankCosted bits target pos /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                  bits target pos).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                  bits target pos).trace ->
              event.matchesReadStore
                (subLogCompressedFIDGlobalTraceReadStore bits))) /\
      forall target occurrence,
        (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
          bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteInterpretedCosted
              bits target occurrence /\
          (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
            bits target occurrence).toCosted =
            subLogSelectFromPackedClarkRouteCosted bits target occurrence /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.isReadWord \/ event.isWordPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                  bits target occurrence).trace ->
              event.matchesReadStore
                (subLogCompressedFIDGlobalTraceReadStore bits)) := by
  constructor
  · intro i
    constructor
    · simp [subLogCompressedFIDAllTargetsGlobalAccessTraceResult,
        subLogCompressedFIDGlobalAccessTraceResult,
        subLogAccessTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDAllTargetsGlobalAccessTraceResult,
        subLogCompressedFIDGlobalAccessTraceResult,
        subLogAccessTraceResult_refines_interpretedCosted,
        subLogAccessInterpretedCosted_refines_subLogAccessCosted]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogAccessTraceResult bits i)
          (subLogAccessTraceReadStore bits)
          (subLogCompressedFIDGlobalTraceReadStore bits)
          subLogCompressedFIDGlobalAccessSegmentMap
          (subLogCompressedFIDGlobalTraceReadStore_access_read bits)
          (subLogAccessTraceResult_matchesReadStore bits i)
  constructor
  · intro target pos
    constructor
    · simp [subLogCompressedFIDAllTargetsGlobalRankTraceResult,
        subLogRankTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDAllTargetsGlobalRankTraceResult,
        subLogRankTraceResult_refines_interpretedCosted,
        subLogRankInterpretedCosted_refines_subLogRankCosted]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogRankTraceResult bits target pos)
          (subLogRankTraceReadStore bits target)
          (subLogCompressedFIDGlobalTraceReadStore bits)
          (subLogCompressedFIDAllTargetsGlobalRankSegmentMap target)
          (subLogCompressedFIDGlobalTraceReadStore_rank_read bits target)
          (subLogRankTraceResult_matchesReadStore bits target pos)
  · intro target occurrence
    constructor
    · simp [subLogCompressedFIDAllTargetsGlobalSelectTraceResult,
        subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted]
    constructor
    · simp [subLogCompressedFIDAllTargetsGlobalSelectTraceResult,
        subLogSelectFromPackedClarkRouteTraceResult_refines_interpretedCosted,
        subLogSelectFromPackedClarkRouteInterpretedCosted_refines]
    constructor
    · intro event _hmem
      exact WordRAM.TraceEvent.isReadWord_or_isWordPrimitive event
    · exact
        WordRAM.TraceResult.relabelReadSegmentsWith_matchesReadStore
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence)
          (subLogSelectFromPackedClarkRouteTraceReadStore bits target)
          (subLogCompressedFIDGlobalTraceReadStore bits)
          (subLogCompressedFIDAllTargetsGlobalSelectSegmentMap target)
          (subLogCompressedFIDGlobalTraceReadStore_select_read bits target)
          (subLogSelectFromPackedClarkRouteTraceResult_matchesReadStore
            bits target occurrence)

theorem subLogCompressedFIDGlobalPayloadStore_noSynthetic_execution_story
    (bits : List Bool) :
    (forall i,
      (forall event,
        event ∈
            (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
              bits i).trace ->
          ¬ event.isSyntheticCostOnlyPrimitive) /\
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalAccessTraceResult
                bits i).trace ->
            subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked
              bits event)) /\
      (forall target pos,
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                bits target pos).trace ->
            ¬ event.isSyntheticCostOnlyPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalRankTraceResult
                  bits target pos).trace ->
              subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked
                bits event)) /\
      forall target occurrence,
        (forall event,
          event ∈
              (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                bits target occurrence).trace ->
            ¬ event.isSyntheticCostOnlyPrimitive) /\
          (forall event,
            event ∈
                (subLogCompressedFIDAllTargetsGlobalSelectTraceResult
                  bits target occurrence).trace ->
              subLogCompressedFIDGlobalTraceEventSuccessfulReadBacked
                bits event) := by
  constructor
  · intro i
    constructor
    · unfold subLogCompressedFIDAllTargetsGlobalAccessTraceResult
        subLogCompressedFIDGlobalAccessTraceResult
      exact
        WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
          subLogCompressedFIDGlobalAccessSegmentMap
          (subLogAccessTraceResult bits i)
          (subLogAccessTraceResult_no_syntheticCostOnlyPrimitive bits i)
    · exact
        subLogCompressedFIDGlobalAccessTraceResult_successful_reads_backed
          bits i
  constructor
  · intro target pos
    constructor
    · unfold subLogCompressedFIDAllTargetsGlobalRankTraceResult
      exact
        WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
          (subLogCompressedFIDAllTargetsGlobalRankSegmentMap target)
          (subLogRankTraceResult bits target pos)
          (subLogRankTraceResult_no_syntheticCostOnlyPrimitive
            bits target pos)
    · exact
        subLogCompressedFIDGlobalRankTraceResult_successful_reads_backed
          bits target pos
  · intro target occurrence
    constructor
    · unfold subLogCompressedFIDAllTargetsGlobalSelectTraceResult
      exact
        WordRAM.TraceResult.relabelReadSegmentsWith_no_syntheticCostOnlyPrimitive
          (subLogCompressedFIDAllTargetsGlobalSelectSegmentMap target)
          (subLogSelectFromPackedClarkRouteTraceResult
            bits target occurrence)
          (subLogSelectFromPackedClarkRouteTraceResult_no_syntheticCostOnlyPrimitive
            bits target occurrence)
    · exact
        subLogCompressedFIDGlobalSelectTraceResult_successful_reads_backed
          bits target occurrence


end RankSelectSpec

end RMQ
