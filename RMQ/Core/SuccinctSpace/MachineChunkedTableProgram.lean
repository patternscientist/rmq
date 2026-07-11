import RMQ.Core.SuccinctSpace.MachineChunkedTable

namespace RMQ
namespace SuccinctSpace

/--
One evaluation of a flat supplied word store. The read log is operational:
each entry records the physical address requested and the word returned there.
-/
structure FlatStoreExecution (alpha : Type u) where
  value : alpha
  reads : List (Prod Nat (Option (List Bool)))

namespace FlatStoreExecution

def footprint (execution : FlatStoreExecution alpha) : List Nat :=
  execution.reads.map Prod.fst

def toCosted (execution : FlatStoreExecution alpha) : Costed alpha where
  value := execution.value
  cost := execution.reads.length

def append (first : FlatStoreExecution alpha)
    (second : FlatStoreExecution beta) : FlatStoreExecution beta where
  value := second.value
  reads := first.reads ++ second.reads

@[simp] theorem toCosted_erase (execution : FlatStoreExecution alpha) :
    execution.toCosted.erase = execution.value := rfl

@[simp] theorem toCosted_cost (execution : FlatStoreExecution alpha) :
    execution.toCosted.cost = execution.reads.length := rfl

@[simp] theorem footprint_length (execution : FlatStoreExecution alpha) :
    execution.footprint.length = execution.reads.length := by
  simp [footprint]

@[simp] theorem append_footprint
    (first : FlatStoreExecution alpha)
    (second : FlatStoreExecution beta) :
    (append first second).footprint =
      first.footprint ++ second.footprint := by
  simp [append, footprint]

end FlatStoreExecution

/--
A computation over one flat array of machine words. Agreement on the addresses
actually read determines the whole execution, and every recorded read is the
supplied-store lookup at that address.
-/
structure FlatStoreComputation (alpha : Type u) where
  run : Array (List Bool) -> FlatStoreExecution alpha
  footprint_determines :
    forall storeA storeB,
      (forall address,
        List.Mem address (run storeA).footprint ->
          storeA[address]? = storeB[address]?) ->
        run storeA = run storeB
  reads_match_store :
    forall store address word,
      List.Mem (address, word) (run store).reads ->
        store[address]? = word

namespace FlatStoreComputation

def pure (value : alpha) : FlatStoreComputation alpha where
  run := fun _ => { value := value, reads := [] }
  footprint_determines := by
    intro storeA storeB hagree
    rfl
  reads_match_store := by
    intro store address word hmem
    cases hmem

def read (address : Nat) :
    FlatStoreComputation (Option (List Bool)) where
  run := fun store =>
    { value := store[address]?
      reads := [(address, store[address]?)] }
  footprint_determines := by
    intro storeA storeB hagree
    have hread : storeA[address]? = storeB[address]? :=
      hagree address (by
        exact List.Mem.head [])
    simp [hread]
  reads_match_store := by
    intro store readAddress word hmem
    have hpair :
        (readAddress, word) = (address, store[address]?) := by
      change List.Mem (readAddress, word)
        [(address, store[address]?)] at hmem
      rcases List.mem_cons.mp hmem with hpair | hnil
      case inl => exact hpair
      case inr =>
        cases hnil
    have haddress : readAddress = address :=
      congrArg Prod.fst hpair
    have hword : word = store[address]? :=
      congrArg Prod.snd hpair
    subst readAddress
    exact hword.symm

def bind (computation : FlatStoreComputation alpha)
    (next : alpha -> FlatStoreComputation beta) :
    FlatStoreComputation beta where
  run := fun store =>
    FlatStoreExecution.append
      (computation.run store)
      ((next (computation.run store).value).run store)
  footprint_determines := by
    intro storeA storeB hagree
    let firstA := computation.run storeA
    let firstB := computation.run storeB
    let secondA := (next firstA.value).run storeA
    have hfirstAgree :
        forall address,
          List.Mem address firstA.footprint ->
            storeA[address]? = storeB[address]? := by
      intro address hmem
      apply hagree address
      simpa only [FlatStoreExecution.append_footprint] using
        (List.mem_append_left secondA.footprint hmem)
    have hfirst : firstA = firstB :=
      computation.footprint_determines storeA storeB hfirstAgree
    have hsecondAgree :
        forall address,
          List.Mem address secondA.footprint ->
            storeA[address]? = storeB[address]? := by
      intro address hmem
      apply hagree address
      simpa only [FlatStoreExecution.append_footprint] using
        (List.mem_append_right firstA.footprint hmem)
    have hsecond :
        secondA = (next firstA.value).run storeB :=
      (next firstA.value).footprint_determines
        storeA storeB hsecondAgree
    change FlatStoreExecution.append firstA secondA =
      FlatStoreExecution.append firstB ((next firstB.value).run storeB)
    calc
      FlatStoreExecution.append firstA secondA =
          FlatStoreExecution.append firstA
            ((next firstA.value).run storeB) := by rw [hsecond]
      _ = FlatStoreExecution.append firstB
            ((next firstB.value).run storeB) := by rw [hfirst]
  reads_match_store := by
    intro store address word hmem
    change List.Mem (address, word)
      ((computation.run store).reads ++
        ((next (computation.run store).value).run store).reads) at hmem
    rcases List.mem_append.mp hmem with hfirst | hsecond
    case inl =>
      exact computation.reads_match_store store address word hfirst
    case inr =>
      exact
        (next (computation.run store).value).reads_match_store
          store address word hsecond

def map (f : alpha -> beta) (computation : FlatStoreComputation alpha) :
    FlatStoreComputation beta :=
  computation.bind (fun value => pure (f value))

def readMany : List Nat ->
    FlatStoreComputation (List (Option (List Bool)))
  | [] => pure []
  | address :: rest =>
      bind (read address) fun word =>
        map (fun words => word :: words) (readMany rest)

@[simp] theorem pure_run (value : alpha) (store : Array (List Bool)) :
    (pure value).run store = { value := value, reads := [] } := rfl

@[simp] theorem read_run (address : Nat) (store : Array (List Bool)) :
    (read address).run store =
      { value := store[address]?, reads := [(address, store[address]?)] } := rfl

@[simp] theorem bind_run (computation : FlatStoreComputation alpha)
    (next : alpha -> FlatStoreComputation beta)
    (store : Array (List Bool)) :
    (bind computation next).run store =
      FlatStoreExecution.append
        (computation.run store)
        ((next (computation.run store).value).run store) := rfl

@[simp] theorem map_run_value (f : alpha -> beta)
    (computation : FlatStoreComputation alpha)
    (store : Array (List Bool)) :
    ((map f computation).run store).value =
      f (computation.run store).value := by
  rfl

@[simp] theorem map_run_reads (f : alpha -> beta)
    (computation : FlatStoreComputation alpha)
    (store : Array (List Bool)) :
    ((map f computation).run store).reads =
      (computation.run store).reads := by
  simp [map, bind, pure, FlatStoreExecution.append]

@[simp] theorem readMany_run_value
    (addresses : List Nat) (store : Array (List Bool)) :
    ((readMany addresses).run store).value =
      addresses.map fun address => store[address]? := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp [readMany, ih, FlatStoreExecution.append]

@[simp] theorem readMany_run_reads
    (addresses : List Nat) (store : Array (List Bool)) :
    ((readMany addresses).run store).reads =
      addresses.map fun address => (address, store[address]?) := by
  induction addresses with
  | nil => rfl
  | cons address rest ih =>
      simp [readMany, ih, FlatStoreExecution.append]



@[simp] theorem pure_run_toCosted
    (value : alpha) (store : Array (List Bool)) :
    ((pure value).run store).toCosted = Costed.pure value := rfl

@[simp] theorem bind_run_toCosted
    (computation : FlatStoreComputation alpha)
    (next : alpha -> FlatStoreComputation beta)
    (store : Array (List Bool)) :
    ((bind computation next).run store).toCosted =
      Costed.bind ((computation.run store).toCosted)
        (fun value => ((next value).run store).toCosted) := by
  apply Costed.ext
  case hvalue => rfl
  case hcost =>
    simp [bind, FlatStoreExecution.append,
      FlatStoreExecution.toCosted, Costed.bind]

@[simp] theorem map_run_toCosted
    (f : alpha -> beta) (computation : FlatStoreComputation alpha)
    (store : Array (List Bool)) :
    ((map f computation).run store).toCosted =
      Costed.map f ((computation.run store).toCosted) := by
  apply Costed.ext
  case hvalue => rfl
  case hcost =>
    simp [map, bind, pure, FlatStoreExecution.append,
      FlatStoreExecution.toCosted, Costed.map, Costed.bind]
end FlatStoreComputation

theorem List.getElem?_append_middle_of_lt
    {alpha : Type} (pre mid post : List alpha)
    (i : Nat) (hlocal : i < mid.length) :
    (pre ++ mid ++ post)[pre.length + i]? = mid[i]? := by
  have hpreMid :
      pre.length + i < (pre ++ mid).length := by
    simp
    omega
  rw [List.getElem?_append_left hpreMid]
  rw [List.getElem?_append_right (by omega)]
  rw [Nat.add_sub_cancel_left]

/-- Shift one table-local machine footprint into the flat component store. -/
def fixedWidthNatTableMachineFootprintAt
    (base width wordSize i : Nat) : List Nat :=
  (fixedWidthNatTableMachineFootprint width wordSize i).map
    (fun address => base + address)

namespace FixedWidthNatTable

/--
Load-bearing flat-store adapter for a fixed-width table. Valid cells read all
machine chunks at the supplied base; invalid cells read the shared dead address.
-/
def machineReadComputationAt
    {entries : List Nat} {width : Nat}
    (_table : FixedWidthNatTable entries width)
    (wordSize base deadAddress i : Nat) :
    FlatStoreComputation (Option Nat) :=
  let addresses :=
    if i < entries.length then
      fixedWidthNatTableMachineFootprintAt base width wordSize i
    else
      [deadAddress]
  FlatStoreComputation.map fixedWidthNatTableMachineDecode
    (FlatStoreComputation.readMany addresses)

theorem machineReadComputationAt_footprint_determines
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    (wordSize base deadAddress i : Nat)
    (storeA storeB : Array (List Bool))
    (hagrees :
      forall address,
        List.Mem address
            ((table.machineReadComputationAt
              wordSize base deadAddress i).run storeA).footprint ->
          storeA[address]? = storeB[address]?) :
    (table.machineReadComputationAt
        wordSize base deadAddress i).run storeA =
      (table.machineReadComputationAt
        wordSize base deadAddress i).run storeB :=
  (table.machineReadComputationAt
    wordSize base deadAddress i).footprint_determines
      storeA storeB hagrees

theorem machineReadComputationAt_reads_match_store
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    (wordSize base deadAddress i : Nat)
    (store : Array (List Bool))
    {address : Nat} {word : Option (List Bool)}
    (hmem :
      List.Mem (address, word)
        ((table.machineReadComputationAt
          wordSize base deadAddress i).run store).reads) :
    store[address]? = word :=
  (table.machineReadComputationAt
    wordSize base deadAddress i).reads_match_store
      store address word hmem


/--
The flat offset adapter refines the accepted per-table machine adapter whenever
its component slice and dead address agree with the canonical table store.
-/
theorem machineReadComputationAt_refines_machineReadCosted
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hwordSize : 0 < wordSize)
    (store : Array (List Bool)) (base deadAddress i : Nat)
    (hsegment :
      forall localAddress,
        localAddress < (table.machineStore hwordSize).store.words.size ->
        store[base + localAddress]? =
          (table.machineStore hwordSize).store.words[localAddress]?)
    (hdead : store[deadAddress]? = none) :
    ((table.machineReadComputationAt
        wordSize base deadAddress i).run store).toCosted =
      table.machineReadCosted hwordSize i := by
  apply Costed.ext
  case hvalue =>
    unfold machineReadComputationAt
    unfold FixedWidthNatTable.machineReadCosted
    unfold FixedWidthNatTable.machineReadCostedWithStore
    by_cases hvalid : i < entries.length
    case pos =>
      simp only [hvalid, if_true]
      simp only [FlatStoreExecution.toCosted,
        FlatStoreComputation.map_run_value, Costed.map,
        Costed.bind, Costed.pure]
      rw [show
        (boundedPayloadWordReadsCosted (table.machineStore hwordSize)
          (fixedWidthNatTableMachineFootprint width wordSize i)).value =
            boundedPayloadWordReadValues (table.machineStore hwordSize)
              (fixedWidthNatTableMachineFootprint width wordSize i) by
        exact boundedPayloadWordReadsCosted_erase _ _]
      change fixedWidthNatTableMachineDecode
          ((FlatStoreComputation.readMany
            (fixedWidthNatTableMachineFootprintAt
              base width wordSize i)).run store).value =
        fixedWidthNatTableMachineDecode
          (boundedPayloadWordReadValues (table.machineStore hwordSize)
            (fixedWidthNatTableMachineFootprint width wordSize i))
      rw [FlatStoreComputation.readMany_run_value]
      unfold boundedPayloadWordReadValues
      apply congrArg fixedWidthNatTableMachineDecode
      unfold fixedWidthNatTableMachineFootprintAt
      rw [List.map_map]
      apply List.map_congr_left
      intro localAddress hmem
      exact hsegment localAddress
        (table.machineFootprint_address_lt
          hwordSize hvalid hmem)
    case neg =>
      simp only [hvalid, if_false]
      change fixedWidthNatTableMachineDecode
          ((FlatStoreComputation.readMany [deadAddress]).run store).value =
        none
      rw [FlatStoreComputation.readMany_run_value]
      simp [hdead, fixedWidthNatTableMachineDecode, collectPayloadWords]
  case hcost =>
    unfold machineReadComputationAt
    unfold FixedWidthNatTable.machineReadCosted
    rw [FixedWidthNatTable.machineReadCostedWithStore_cost]
    by_cases hvalid : i < entries.length
    case pos =>
      simp [hvalid, FlatStoreExecution.toCosted,
        FlatStoreComputation.map_run_reads,
        FlatStoreComputation.readMany_run_reads,
        fixedWidthNatTableMachineFootprintAt]
    case neg =>
      simp [hvalid, FlatStoreExecution.toCosted,
        FlatStoreComputation.map_run_reads,
        FlatStoreComputation.readMany_run_reads]

end FixedWidthNatTable

namespace BoundedPayloadWordStore

/-- Concatenate two bounded counted-payload stores without changing word order. -/
def append
    {payloadA payloadB : List Bool} {wordSize : Nat}
    (left : BoundedPayloadWordStore payloadA wordSize)
    (right : BoundedPayloadWordStore payloadB wordSize) :
    BoundedPayloadWordStore (payloadA ++ payloadB) wordSize where
  store :=
    { words := (left.store.words.toList ++ right.store.words.toList).toArray
      erases := by
        rw [List.toList_toArray, flattenPayloadWords_append,
          left.erases, right.erases] }
  word_length_le := by
    intro word hmem
    change List.Mem word
      (left.store.words.toList ++ right.store.words.toList) at hmem
    rcases List.mem_append.mp hmem with hleft | hright
    case inl => exact left.word_length_le hleft
    case inr => exact right.word_length_le hright

@[simp] theorem append_words_toList
    {payloadA payloadB : List Bool} {wordSize : Nat}
    (left : BoundedPayloadWordStore payloadA wordSize)
    (right : BoundedPayloadWordStore payloadB wordSize) :
    (append left right).store.words.toList =
      left.store.words.toList ++ right.store.words.toList := by
  simp [append]

@[simp] theorem append_erases
    {payloadA payloadB : List Bool} {wordSize : Nat}
    (left : BoundedPayloadWordStore payloadA wordSize)
    (right : BoundedPayloadWordStore payloadB wordSize) :
    flattenPayloadWords (append left right).store.words.toList =
      payloadA ++ payloadB :=
  (append left right).erases


@[simp] theorem append_getElem?_left
    {payloadA payloadB : List Bool} {wordSize : Nat}
    (left : BoundedPayloadWordStore payloadA wordSize)
    (right : BoundedPayloadWordStore payloadB wordSize)
    (i : Nat) :
    (append left right).store.words[i]? =
      if i < left.store.words.size then
        left.store.words[i]?
      else
        right.store.words[i - left.store.words.size]? := by
  simp [append, List.getElem?_append, Array.getElem?_toList]

@[simp] theorem append_getElem?_right
    {payloadA payloadB : List Bool} {wordSize : Nat}
    (left : BoundedPayloadWordStore payloadA wordSize)
    (right : BoundedPayloadWordStore payloadB wordSize)
    (i : Nat) :
    (append left right).store.words[left.store.words.size + i]? =
      right.store.words[i]? := by
  simp [append, List.getElem?_append, Array.getElem?_toList] <;> omega
end BoundedPayloadWordStore
end SuccinctSpace
end RMQ
