import RMQ.Impl.FischerHeun
import RMQ.Impl.LCACost

/-!
# Fischer-Heun-backed LCA adapters

This module instantiates the existing RMQ-to-LCA reduction with the verified
Fischer-Heun RMQ backends.  It does not introduce new tree semantics; it names
the exact LCA backends obtained by composing:

* generated Euler depths,
* the exact Fischer-Heun RMQ backend over those depths, and
* the verified trace/path agreement LCA reduction.

The costed wrappers use the `LCACost` indexed-access query model.  The supplied
RMQ query remains a model-level backend tick here; concrete Fischer-Heun
preprocessing and supplied-query cost profiles stay in `Impl.FischerHeun`.
-/

namespace RMQ

namespace LCAFischerHeun

/-- Canonical Fischer-Heun RMQ backend over the generated Euler depth trace. -/
def canonicalRMQBackend (tree : RoseTree) :
    RMQBackend tree.eulerTrace.depths :=
  FischerHeun.backend tree.eulerTrace.depths

/-- All-input Fischer-Heun RMQ backend with linear-scan fallback. -/
def allInputRMQBackend (tree : RoseTree) :
    RMQBackend tree.eulerTrace.depths :=
  FischerHeun.allInputBackend tree.eulerTrace.depths

/-- LCA backend obtained from the canonical Fischer-Heun RMQ backend. -/
def canonicalBackend
    (tree : RoseTree) (hagreement : tree.TracePathAgreement) :
    LCABackend tree :=
  tree.lcaBackendOfRMQBackend (canonicalRMQBackend tree) hagreement

/-- Unique-label wrapper for the canonical Fischer-Heun LCA backend. -/
def canonicalBackendUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique) :
    LCABackend tree :=
  canonicalBackend tree (tree.tracePathAgreement_of_labelsUnique hunique)

/-- LCA backend obtained from the all-input Fischer-Heun RMQ backend. -/
def allInputBackend
    (tree : RoseTree) (hagreement : tree.TracePathAgreement) :
    LCABackend tree :=
  tree.lcaBackendOfRMQBackend (allInputRMQBackend tree) hagreement

/-- Unique-label wrapper for the all-input Fischer-Heun LCA backend. -/
def allInputBackendUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique) :
    LCABackend tree :=
  allInputBackend tree (tree.tracePathAgreement_of_labelsUnique hunique)

/-- Query candidate induced by the canonical Fischer-Heun RMQ backend. -/
def canonicalCandidate (tree : RoseTree) (u v : Nat) : Option Nat :=
  tree.lcaCandidate (canonicalRMQBackend tree) u v

/-- Query candidate induced by the all-input Fischer-Heun RMQ backend. -/
def allInputCandidate (tree : RoseTree) (u v : Nat) : Option Nat :=
  tree.lcaCandidate (allInputRMQBackend tree) u v

theorem canonicalCandidate_eq_queryBuilt
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    LCABackend.queryBuilt (canonicalBackend tree hagreement) u v =
      canonicalCandidate tree u v := by
  rfl

theorem allInputCandidate_eq_queryBuilt
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    LCABackend.queryBuilt (allInputBackend tree hagreement) u v =
      allInputCandidate tree u v := by
  rfl

theorem canonicalCandidate_isPathLCA_of_tracePathAgreement
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    {u v node : Nat}
    (hquery : canonicalCandidate tree u v = some node) :
    tree.IsPathLCA u v node := by
  exact tree.lcaCandidate_isPathLCA_of_tracePathAgreement
    (canonicalRMQBackend tree) hagreement hquery

theorem canonicalCandidate_isPathLCA_of_labelsUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique)
    {u v node : Nat}
    (hquery : canonicalCandidate tree u v = some node) :
    tree.IsPathLCA u v node := by
  exact canonicalCandidate_isPathLCA_of_tracePathAgreement tree
    (tree.tracePathAgreement_of_labelsUnique hunique) hquery

theorem allInputCandidate_isPathLCA_of_tracePathAgreement
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    {u v node : Nat}
    (hquery : allInputCandidate tree u v = some node) :
    tree.IsPathLCA u v node := by
  exact tree.lcaCandidate_isPathLCA_of_tracePathAgreement
    (allInputRMQBackend tree) hagreement hquery

theorem allInputCandidate_isPathLCA_of_labelsUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique)
    {u v node : Nat}
    (hquery : allInputCandidate tree u v = some node) :
    tree.IsPathLCA u v node := by
  exact allInputCandidate_isPathLCA_of_tracePathAgreement tree
    (tree.tracePathAgreement_of_labelsUnique hunique) hquery

theorem canonicalRMQBackend_queryBuilt
    (tree : RoseTree) (left right : Nat) :
    RMQBackend.queryBuilt (canonicalRMQBackend tree) left right =
      FischerHeun.query tree.eulerTrace.depths left right := by
  rfl

theorem fischerHeunQueryCosted_cost_le_thirteen_of_large
    (tree : RoseTree)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (left right : Nat) :
    (FischerHeun.queryCosted tree.eulerTrace.depths left right).cost <= 13 := by
  unfold FischerHeun.queryCosted
  exact FischerHeun.queryWithStateCosted_built_cost_le_thirteen_of_large
    hlarge left right

/--
Concrete Fischer-Heun version of the trace-window step: query the built
canonical Fischer-Heun state over Euler depths, then read the returned Euler
node through the indexed node view.
-/
def canonicalMinDepthNodeCosted
    (tree : RoseTree) (left right : Nat) : Costed (Option Nat) :=
  Costed.bind
    (FischerHeun.queryCosted tree.eulerTrace.depths left right) fun
  | none => Costed.pure none
  | some idx => LCACost.nodeAtCosted tree.eulerTrace idx

@[simp] theorem canonicalMinDepthNodeCosted_erase
    (tree : RoseTree) (left right : Nat) :
    (canonicalMinDepthNodeCosted tree left right).erase =
      tree.eulerTrace.minDepthNodeInWindow
        (canonicalRMQBackend tree) left right := by
  unfold canonicalMinDepthNodeCosted EulerTrace.minDepthNodeInWindow
  rw [canonicalRMQBackend_queryBuilt]
  cases hquery : FischerHeun.query tree.eulerTrace.depths left right <;>
    simp [Costed.bind, FischerHeun.queryCosted_value, hquery]

@[simp] theorem canonicalMinDepthNodeCosted_value
    (tree : RoseTree) (left right : Nat) :
    (canonicalMinDepthNodeCosted tree left right).value =
      tree.eulerTrace.minDepthNodeInWindow
        (canonicalRMQBackend tree) left right :=
  canonicalMinDepthNodeCosted_erase tree left right

theorem canonicalMinDepthNodeCosted_cost_le_fourteen_of_large
    (tree : RoseTree)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (left right : Nat) :
    (canonicalMinDepthNodeCosted tree left right).cost <= 14 := by
  unfold canonicalMinDepthNodeCosted
  have hquery :
      (FischerHeun.queryCosted tree.eulerTrace.depths left right).cost <= 13 :=
    fischerHeunQueryCosted_cost_le_thirteen_of_large tree hlarge left right
  cases hres : FischerHeun.query tree.eulerTrace.depths left right with
  | none =>
      simp [Costed.bind, FischerHeun.queryCosted_value, hres]
      omega
  | some idx =>
      simp [Costed.bind, FischerHeun.queryCosted_value, hres,
        LCACost.nodeAtCosted_cost,
        TableModel.indexedReadCost]
      omega

/--
Concrete large-regime Fischer-Heun LCA query model: two first-occurrence indexed
reads, a concrete supplied-state Fischer-Heun query over Euler depths, and a
node indexed read when the RMQ query returns an index.
-/
def canonicalConcreteQueryCosted
    (tree : RoseTree) (u v : Nat) : Costed (Option Nat) :=
  Costed.bind (LCACost.firstOccurrenceCosted tree.eulerTrace u) fun
  | none =>
      Costed.bind (LCACost.firstOccurrenceCosted tree.eulerTrace v) fun _ =>
        Costed.pure none
  | some i =>
      Costed.bind (LCACost.firstOccurrenceCosted tree.eulerTrace v) fun
      | none => Costed.pure none
      | some j =>
          let window := EulerTrace.occurrenceWindow i j
          canonicalMinDepthNodeCosted tree window.1 window.2

@[simp] theorem canonicalConcreteQueryCosted_erase
    (tree : RoseTree) (u v : Nat) :
    (canonicalConcreteQueryCosted tree u v).erase =
      canonicalCandidate tree u v := by
  unfold canonicalConcreteQueryCosted canonicalCandidate RoseTree.lcaCandidate
    EulerTrace.lcaCandidate
    LCACost.firstOccurrenceCosted LCACost.firstOccurrenceIndex
  cases hu : tree.eulerTrace.firstOccurrence? u <;>
    cases hv : tree.eulerTrace.firstOccurrence? v <;>
    simp [hu, hv, Costed.bind, Costed.pure]

@[simp] theorem canonicalConcreteQueryCosted_value
    (tree : RoseTree) (u v : Nat) :
    (canonicalConcreteQueryCosted tree u v).value =
      canonicalCandidate tree u v :=
  canonicalConcreteQueryCosted_erase tree u v

theorem canonicalConcreteQueryCosted_cost_le_sixteen_of_firstOccurrences
    (tree : RoseTree)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    {u v i j : Nat}
    (hu : tree.eulerTrace.firstOccurrence? u = some i)
    (hv : tree.eulerTrace.firstOccurrence? v = some j) :
    (canonicalConcreteQueryCosted tree u v).cost <= 16 := by
  unfold canonicalConcreteQueryCosted
    LCACost.firstOccurrenceCosted LCACost.firstOccurrenceIndex
  simp [hu, hv, Costed.bind,
    TableModel.IndexedAccess.getCosted, TableModel.indexedReadCost]
  have hwindow :=
    canonicalMinDepthNodeCosted_cost_le_fourteen_of_large tree hlarge
    (EulerTrace.occurrenceWindow i j).1 (EulerTrace.occurrenceWindow i j).2
  omega

theorem canonicalConcreteQueryCosted_cost_le_sixteen_of_large
    (tree : RoseTree)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    (canonicalConcreteQueryCosted tree u v).cost <= 16 := by
  unfold canonicalConcreteQueryCosted
    LCACost.firstOccurrenceCosted LCACost.firstOccurrenceIndex
  cases hu : tree.eulerTrace.firstOccurrence? u with
  | none =>
      cases hv : tree.eulerTrace.firstOccurrence? v with
      | none =>
          simp [hu, hv, Costed.bind,
            TableModel.IndexedAccess.getCosted, TableModel.indexedReadCost]
      | some j =>
          simp [hu, hv, Costed.bind,
            TableModel.IndexedAccess.getCosted, TableModel.indexedReadCost]
  | some i =>
      cases hv : tree.eulerTrace.firstOccurrence? v with
      | none =>
          simp [hu, hv, Costed.bind,
            TableModel.IndexedAccess.getCosted, TableModel.indexedReadCost]
      | some j =>
          simp [hu, hv, Costed.bind,
            TableModel.IndexedAccess.getCosted, TableModel.indexedReadCost]
          have hwindow :=
            canonicalMinDepthNodeCosted_cost_le_fourteen_of_large tree hlarge
              (EulerTrace.occurrenceWindow i j).1
              (EulerTrace.occurrenceWindow i j).2
          omega

/--
Query-side concrete Fischer-Heun LCA capstone.

The costed concrete path returns only path-level LCA answers, and its query cost
is constant in the large canonical Fischer-Heun regime. Preprocessing for the
first-occurrence/node/depth tables remains a separate build-state target.
-/
theorem canonicalConcreteQueryCosted_refines_with_steps_of_tracePathAgreement
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    (forall {node},
      (canonicalConcreteQueryCosted tree u v).value = some node ->
        tree.IsPathLCA u v node) ∧
      (canonicalConcreteQueryCosted tree u v).cost <= 16 := by
  constructor
  · intro node hvalue
    rw [canonicalConcreteQueryCosted_value] at hvalue
    exact canonicalCandidate_isPathLCA_of_tracePathAgreement
      tree hagreement hvalue
  · exact canonicalConcreteQueryCosted_cost_le_sixteen_of_large
      tree hlarge u v

theorem canonicalConcreteQueryCosted_run
    (tree : RoseTree) (u v : Nat) :
    (canonicalConcreteQueryCosted tree u v).run =
      (canonicalCandidate tree u v,
        (canonicalConcreteQueryCosted tree u v).cost) := by
  simp [Costed.run]

/--
Concrete LCA query state: a Fischer-Heun RMQ state over Euler depths, a
first-occurrence access table, and a node indexed view.

This is a query-state assembly layer.  The dense cost-headline state below uses
direct-address first-occurrence and Euler-node stores built by counted
preprocessing.
-/
structure ConcreteQueryState (tree : RoseTree) where
  rmqState : FischerHeun.State
  firstOccurrences : TableModel.IndexedAccess Nat Nat
  nodes : TableModel.IndexedSeq Nat

/--
Dense-label concrete query state over the generated Euler trace.  First
occurrences are stored in a direct-address table indexed by the node label.
-/
def buildDenseConcreteQueryState (tree : RoseTree) :
    ConcreteQueryState tree where
  rmqState := FischerHeun.build tree.eulerTrace.depths
  firstOccurrences := LCACost.builtFirstOccurrenceDirectIndex tree
  nodes := LCACost.builtNodeIndex tree.eulerTrace

@[simp] theorem buildDenseConcreteQueryState_rmqState
    (tree : RoseTree) :
    (buildDenseConcreteQueryState tree).rmqState =
      FischerHeun.build tree.eulerTrace.depths := by
  rfl

@[simp] theorem buildDenseConcreteQueryState_firstOccurrences
    (tree : RoseTree) :
    (buildDenseConcreteQueryState tree).firstOccurrences =
      LCACost.builtFirstOccurrenceDirectIndex tree := by
  rfl

@[simp] theorem buildDenseConcreteQueryState_nodes
    (tree : RoseTree) :
    (buildDenseConcreteQueryState tree).nodes =
      LCACost.builtNodeIndex tree.eulerTrace := by
  rfl

/-- Costed first-occurrence read from a concrete LCA query state. -/
def stateFirstOccurrenceCosted
    {tree : RoseTree} (state : ConcreteQueryState tree) (label : Nat) :
    Costed (Option Nat) :=
  state.firstOccurrences.getCosted label

/-- Costed Euler-node read from a concrete LCA query state. -/
def stateNodeAtCosted
    {tree : RoseTree} (state : ConcreteQueryState tree) (idx : Nat) :
    Costed (Option Nat) :=
  state.nodes.getCosted idx

/-- Query-state version of the minimum-depth Euler-node read. -/
def stateMinDepthNodeCosted
    (tree : RoseTree) (state : ConcreteQueryState tree)
    (left right : Nat) : Costed (Option Nat) :=
  Costed.bind
    (FischerHeun.queryWithStateCosted tree.eulerTrace.depths
      state.rmqState left right) fun
  | none => Costed.pure none
  | some idx => stateNodeAtCosted state idx

/-- Query through an explicit concrete LCA query state. -/
def queryWithConcreteStateCosted
    (tree : RoseTree) (state : ConcreteQueryState tree)
    (u v : Nat) : Costed (Option Nat) :=
  Costed.bind (stateFirstOccurrenceCosted state u) fun
  | none =>
      Costed.bind (stateFirstOccurrenceCosted state v) fun _ =>
        Costed.pure none
  | some i =>
      Costed.bind (stateFirstOccurrenceCosted state v) fun
      | none => Costed.pure none
      | some j =>
        let window := EulerTrace.occurrenceWindow i j
        stateMinDepthNodeCosted tree state window.1 window.2

theorem stateMinDepthNodeCosted_denseBuilt_eq
    (tree : RoseTree) (left right : Nat) :
    stateMinDepthNodeCosted tree
        (buildDenseConcreteQueryState tree) left right =
      canonicalMinDepthNodeCosted tree left right := by
  unfold stateMinDepthNodeCosted canonicalMinDepthNodeCosted
    buildDenseConcreteQueryState stateNodeAtCosted LCACost.nodeAtCosted
    FischerHeun.queryCosted
  cases hquery :
      FischerHeun.queryWithStateCosted tree.eulerTrace.depths
        (FischerHeun.build tree.eulerTrace.depths) left right with
  | mk value cost =>
      cases value with
      | none =>
          simp [Costed.bind]
      | some idx =>
          simp [Costed.bind,
            LCACost.builtNodeIndex_getCosted_eq_nodeIndex
              tree.eulerTrace idx]

theorem stateFirstOccurrenceCosted_denseBuilt_eq
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (label : Nat) :
    stateFirstOccurrenceCosted
        (buildDenseConcreteQueryState tree) label =
      LCACost.firstOccurrenceCosted tree.eulerTrace label := by
  unfold stateFirstOccurrenceCosted buildDenseConcreteQueryState
  exact LCACost.builtFirstOccurrenceDirectCosted_eq_firstOccurrenceCosted_of_bounded
    tree hbounded label

theorem queryWithBuiltDenseConcreteStateCosted_eq
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (u v : Nat) :
    queryWithConcreteStateCosted tree
        (buildDenseConcreteQueryState tree) u v =
      canonicalConcreteQueryCosted tree u v := by
  unfold queryWithConcreteStateCosted canonicalConcreteQueryCosted
  rw [stateFirstOccurrenceCosted_denseBuilt_eq tree hbounded u]
  cases hu : tree.eulerTrace.firstOccurrence? u with
  | none =>
      simp [LCACost.firstOccurrenceCosted, LCACost.firstOccurrenceIndex,
        stateFirstOccurrenceCosted_denseBuilt_eq tree hbounded v,
        stateMinDepthNodeCosted_denseBuilt_eq]
  | some i =>
      simp [LCACost.firstOccurrenceCosted, LCACost.firstOccurrenceIndex,
        stateFirstOccurrenceCosted_denseBuilt_eq tree hbounded v,
        stateMinDepthNodeCosted_denseBuilt_eq]

@[simp] theorem queryWithBuiltDenseConcreteStateCosted_value
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (u v : Nat) :
    (queryWithConcreteStateCosted tree
        (buildDenseConcreteQueryState tree) u v).value =
      canonicalCandidate tree u v := by
  rw [queryWithBuiltDenseConcreteStateCosted_eq tree hbounded]
  exact canonicalConcreteQueryCosted_value tree u v

theorem queryWithBuiltDenseConcreteStateCosted_cost_le_sixteen_of_large
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    (queryWithConcreteStateCosted tree
        (buildDenseConcreteQueryState tree) u v).cost <= 16 := by
  rw [queryWithBuiltDenseConcreteStateCosted_eq tree hbounded]
  exact canonicalConcreteQueryCosted_cost_le_sixteen_of_large
    tree hlarge u v

/--
Dense built-query-state LCA capstone.

The first-occurrence reads are direct-address indexed reads under
`LabelsBoundedBySize`.
-/
theorem queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_tracePathAgreement
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (hbounded : tree.LabelsBoundedBySize)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    (forall {node},
      (queryWithConcreteStateCosted tree
          (buildDenseConcreteQueryState tree) u v).value =
          some node ->
        tree.IsPathLCA u v node) ∧
      (queryWithConcreteStateCosted tree
          (buildDenseConcreteQueryState tree) u v).cost <= 16 := by
  constructor
  · intro node hvalue
    rw [queryWithBuiltDenseConcreteStateCosted_value
      tree hbounded] at hvalue
    exact canonicalCandidate_isPathLCA_of_tracePathAgreement
      tree hagreement hvalue
  · exact queryWithBuiltDenseConcreteStateCosted_cost_le_sixteen_of_large
      tree hbounded hlarge u v

theorem queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_denseNatLabels
    (tree : RoseTree) (hdense : tree.DenseNatLabels)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    (forall {node},
      (queryWithConcreteStateCosted tree
          (buildDenseConcreteQueryState tree) u v).value =
          some node ->
        tree.IsPathLCA u v node) ∧
      (queryWithConcreteStateCosted tree
          (buildDenseConcreteQueryState tree) u v).cost <= 16 := by
  exact
    queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_tracePathAgreement
      tree (tree.tracePathAgreement_of_labelsUnique hdense.1)
      hdense.2 hlarge u v

/--
First-occurrence preprocessing plus dense LCA query capstone.

This composes the counted dense first-occurrence-table builder with the
builder-backed dense query state.  It is not yet the full LCA preprocessing
profile: Euler-trace construction, Euler node/depth view construction, and the
Fischer-Heun RMQ state build remain separate costs.
-/
theorem firstOccurrenceBuildAndDenseQuery_refines_with_steps_of_denseNatLabels
    (tree : RoseTree) (hdense : tree.DenseNatLabels)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    (LCACost.buildFirstOccurrenceDirectArray tree).value.toList =
        LCACost.firstOccurrenceDirectRows tree ∧
      (LCACost.buildFirstOccurrenceDirectArray tree).steps <=
        tree.labelsPreorder.length + 1 + 3 * tree.eulerTrace.nodes.length ∧
      (forall {node},
        (queryWithConcreteStateCosted tree
            (buildDenseConcreteQueryState tree) u v).value =
            some node ->
          tree.IsPathLCA u v node) ∧
        (queryWithConcreteStateCosted tree
            (buildDenseConcreteQueryState tree) u v).cost <= 16 := by
  rcases LCACost.buildFirstOccurrenceDirectArray_refines_with_steps tree with
    ⟨hbuildValue, hbuildSteps⟩
  rcases
    queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_denseNatLabels
      tree hdense hlarge u v with
    ⟨hqueryValue, hquerySteps⟩
  exact ⟨hbuildValue, hbuildSteps, hqueryValue, hquerySteps⟩

/-- Component cost charged to assemble the dense/preindexed LCA query state. -/
def densePreprocessBuildCost (tree : RoseTree) : Nat :=
  LCACost.eulerTraceBuildCost tree +
    (LCACost.buildNodeArray tree.eulerTrace).steps +
    (LCACost.buildDepthArray tree.eulerTrace).steps +
    (LCACost.buildFirstOccurrenceDirectArray tree).steps +
    (FischerHeun.buildCosted tree.eulerTrace.depths).cost

/-- Coarse symbolic budget for dense/preindexed LCA preprocessing. -/
def densePreprocessBuildBudget (tree : RoseTree) : Nat :=
  LCACost.eulerTraceBuildCost tree +
    (tree.eulerTrace.nodes.length + 1) +
    (tree.eulerTrace.depths.length + 1) +
    (tree.labelsPreorder.length + 1 +
      3 * tree.eulerTrace.nodes.length) +
    15 * tree.eulerTrace.depths.length

theorem fischerHeunBuildCosted_cost_le_fifteen_mul_depths
    (tree : RoseTree)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths) :
    (FischerHeun.buildCosted tree.eulerTrace.depths).cost <=
      15 * tree.eulerTrace.depths.length := by
  rw [FischerHeun.buildCosted_cost]
  have hb16 : 16 <=
      FischerHeun.canonicalBlockSize tree.eulerTrace.depths := by
    simpa [FischerHeun.canonicalReady] using hlarge
  have hpos :=
    FischerHeun.canonicalBlockSize_pos_length_of_ge_sixteen
      (xs := tree.eulerTrace.depths) hb16
  have hmicro :=
    FischerHeun.rawMicrotableSlotBudget_canonical_le_length
      tree.eulerTrace.depths hpos
  have hsummary :=
    FischerHeun.summaryLog_canonical_le_four_mul
      tree.eulerTrace.depths hb16
  exact
    FischerHeun.buildCost_le_fifteen_mul_length
      tree.eulerTrace.depths
      (FischerHeun.canonicalBlockSize tree.eulerTrace.depths)
      hmicro hsummary

theorem densePreprocessBuildCost_le_budget
    (tree : RoseTree)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths) :
    densePreprocessBuildCost tree <= densePreprocessBuildBudget tree := by
  unfold densePreprocessBuildCost densePreprocessBuildBudget
  rw [LCACost.buildNodeArray_steps, LCACost.buildDepthArray_steps]
  have hfirst :=
    LCACost.buildFirstOccurrenceDirectArray_steps_le tree
  have hfh :=
    fischerHeunBuildCosted_cost_le_fifteen_mul_depths tree hlarge
  omega

/-- Normalized linear budget for dense/preindexed LCA preprocessing. -/
def densePreprocessLinearBudget (tree : RoseTree) : Nat :=
  22 * tree.eulerTrace.nodes.length + 3

theorem densePreprocessBuildBudget_le_linearBudget
    (tree : RoseTree) :
    densePreprocessBuildBudget tree <=
      densePreprocessLinearBudget tree := by
  unfold densePreprocessBuildBudget densePreprocessLinearBudget
    LCACost.eulerTraceBuildCost
  have hlabels :
      tree.labelsPreorder.length <= tree.eulerTrace.nodes.length := by
    simpa [RoseTree.eulerTrace, RoseTree.eulerTraceAt] using
      RoseTree.labelsPreorder_length_le_eulerNodes_length tree
  have hlen := tree.eulerTrace.length_eq
  omega

theorem densePreprocessBuildCost_le_linearBudget
    (tree : RoseTree)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths) :
    densePreprocessBuildCost tree <=
      densePreprocessLinearBudget tree := by
  exact Nat.le_trans (densePreprocessBuildCost_le_budget tree hlarge)
    (densePreprocessBuildBudget_le_linearBudget tree)

/--
Dense/preindexed LCA preprocessing plus query capstone.

This records every currently assembled preprocessing component: Euler-trace
materialization in the existing tick model, counted stored node/depth views,
the counted dense first-occurrence table, and the canonical Fischer-Heun RMQ
state build.  The query consumes the built dense state and returns only
path-level LCA answers with the constant large-regime query bound.
-/
theorem densePreprocessAndQuery_refines_with_steps_of_denseNatLabels
    (tree : RoseTree) (hdense : tree.DenseNatLabels)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    (LCACost.eulerTraceCosted tree).value = tree.eulerTrace ∧
      (LCACost.buildNodeArray tree.eulerTrace).value.toList =
        tree.eulerTrace.nodes ∧
      (LCACost.buildDepthArray tree.eulerTrace).value.toList =
        tree.eulerTrace.depths ∧
      (LCACost.buildFirstOccurrenceDirectArray tree).value.toList =
        LCACost.firstOccurrenceDirectRows tree ∧
      (FischerHeun.buildCosted tree.eulerTrace.depths).value =
        FischerHeun.build tree.eulerTrace.depths ∧
      densePreprocessBuildCost tree <= densePreprocessBuildBudget tree ∧
      (forall {node},
        (queryWithConcreteStateCosted tree
            (buildDenseConcreteQueryState tree) u v).value =
            some node ->
          tree.IsPathLCA u v node) ∧
        (queryWithConcreteStateCosted tree
            (buildDenseConcreteQueryState tree) u v).cost <= 16 := by
  have hcost := densePreprocessBuildCost_le_budget tree hlarge
  rcases LCACost.buildFirstOccurrenceDirectArray_refines_with_steps tree with
    ⟨hfirstValue, _hfirstSteps⟩
  rcases
    queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_denseNatLabels
      tree hdense hlarge u v with
    ⟨hqueryValue, hquerySteps⟩
  exact ⟨rfl, LCACost.buildNodeArray_value_toList tree.eulerTrace,
    LCACost.buildDepthArray_value_toList tree.eulerTrace,
    hfirstValue, FischerHeun.buildCosted_value tree.eulerTrace.depths,
    hcost, hqueryValue, hquerySteps⟩

/--
Demo-facing dense/preindexed LCA profile.

Under dense natural node labels and the canonical Fischer-Heun large-input
regime over the generated Euler-depth trace, the assembled preprocessing cost is
linear in the Euler-tour length, the built-state query is path-LCA correct, and
the query cost is bounded by a fixed constant in the RAM/unit-indexed-access
model used throughout the cost layer.
-/
theorem denseLCA_linearBuild_constantQuery_profile
    (tree : RoseTree) (hdense : tree.DenseNatLabels)
    (hlarge : FischerHeun.canonicalReady tree.eulerTrace.depths)
    (u v : Nat) :
    densePreprocessBuildCost tree <=
        densePreprocessLinearBudget tree ∧
      (forall {node},
        (queryWithConcreteStateCosted tree
            (buildDenseConcreteQueryState tree) u v).value =
            some node ->
          tree.IsPathLCA u v node) ∧
      (queryWithConcreteStateCosted tree
          (buildDenseConcreteQueryState tree) u v).cost <= 16 ∧
      densePreprocessBuildCost tree +
          (queryWithConcreteStateCosted tree
            (buildDenseConcreteQueryState tree) u v).cost <=
        densePreprocessLinearBudget tree + 16 := by
  have hbuild := densePreprocessBuildCost_le_linearBudget tree hlarge
  rcases
    queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_denseNatLabels
      tree hdense hlarge u v with
    ⟨hqueryValue, hquerySteps⟩
  have htotal :
      densePreprocessBuildCost tree +
          (queryWithConcreteStateCosted tree
            (buildDenseConcreteQueryState tree) u v).cost <=
        densePreprocessLinearBudget tree + 16 := by
    omega
  exact ⟨hbuild, hqueryValue, hquerySteps, htotal⟩

theorem queryWithBuiltDenseConcreteStateCosted_run
    (tree : RoseTree) (hbounded : tree.LabelsBoundedBySize)
    (u v : Nat) :
    (queryWithConcreteStateCosted tree
        (buildDenseConcreteQueryState tree) u v).run =
      (canonicalCandidate tree u v,
        (queryWithConcreteStateCosted tree
          (buildDenseConcreteQueryState tree) u v).cost) := by
  rw [Costed.run,
    queryWithBuiltDenseConcreteStateCosted_value tree hbounded]

/-- Indexed-cost LCA query through the canonical Fischer-Heun RMQ backend. -/
def canonicalQueryCosted
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) : Costed (Option Nat) :=
  LCACost.queryViaRMQIndexedCosted tree
    (canonicalRMQBackend tree) hagreement u v

/-- Cost expression for `canonicalQueryCosted`. -/
def canonicalQueryCost
    (tree : RoseTree) (u v : Nat) : Nat :=
  LCACost.queryViaRMQIndexedCost tree (canonicalRMQBackend tree) u v

@[simp] theorem canonicalQueryCosted_erase
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (canonicalQueryCosted tree hagreement u v).erase =
      canonicalCandidate tree u v := by
  unfold canonicalQueryCosted canonicalCandidate
  exact LCACost.queryViaRMQIndexedCosted_erase tree
    (canonicalRMQBackend tree) hagreement u v

theorem canonicalQueryCosted_cost
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (canonicalQueryCosted tree hagreement u v).cost =
      canonicalQueryCost tree u v := by
  unfold canonicalQueryCosted canonicalQueryCost
  exact LCACost.queryViaRMQIndexedCosted_cost tree
    (canonicalRMQBackend tree) hagreement u v

theorem canonicalQueryCosted_cost_of_firstOccurrences
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    {u v i j : Nat}
    (hu : tree.eulerTrace.firstOccurrence? u = some i)
    (hv : tree.eulerTrace.firstOccurrence? v = some j) :
    (canonicalQueryCosted tree hagreement u v).cost =
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (LCACost.suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  exact LCACost.queryViaRMQIndexedCosted_cost_of_firstOccurrences tree
    (canonicalRMQBackend tree) hagreement hu hv

theorem canonicalQueryCosted_cost_le
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (canonicalQueryCosted tree hagreement u v).cost <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (LCACost.suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  exact LCACost.queryViaRMQIndexedCosted_cost_le tree
    (canonicalRMQBackend tree) hagreement u v

theorem canonicalQueryCosted_cost_le_four
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (canonicalQueryCosted tree hagreement u v).cost <= 4 := by
  have h := canonicalQueryCosted_cost_le tree hagreement u v
  simpa [LCACost.suppliedRMQQueryCost, LCACost.suppliedQueryCost,
    TableModel.indexedReadCost] using h

theorem canonicalQueryCosted_run
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (canonicalQueryCosted tree hagreement u v).run =
      (canonicalCandidate tree u v, canonicalQueryCost tree u v) := by
  unfold canonicalQueryCosted canonicalQueryCost canonicalCandidate
  exact LCACost.queryViaRMQIndexedCosted_run tree
    (canonicalRMQBackend tree) hagreement u v

/-- Indexed-cost LCA query through the all-input Fischer-Heun RMQ backend. -/
def allInputQueryCosted
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) : Costed (Option Nat) :=
  LCACost.queryViaRMQIndexedCosted tree
    (allInputRMQBackend tree) hagreement u v

/-- Cost expression for `allInputQueryCosted`. -/
def allInputQueryCost
    (tree : RoseTree) (u v : Nat) : Nat :=
  LCACost.queryViaRMQIndexedCost tree (allInputRMQBackend tree) u v

@[simp] theorem allInputQueryCosted_erase
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (allInputQueryCosted tree hagreement u v).erase =
      allInputCandidate tree u v := by
  unfold allInputQueryCosted allInputCandidate
  exact LCACost.queryViaRMQIndexedCosted_erase tree
    (allInputRMQBackend tree) hagreement u v

theorem allInputQueryCosted_cost
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (allInputQueryCosted tree hagreement u v).cost =
      allInputQueryCost tree u v := by
  unfold allInputQueryCosted allInputQueryCost
  exact LCACost.queryViaRMQIndexedCosted_cost tree
    (allInputRMQBackend tree) hagreement u v

theorem allInputQueryCosted_cost_of_firstOccurrences
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    {u v i j : Nat}
    (hu : tree.eulerTrace.firstOccurrence? u = some i)
    (hv : tree.eulerTrace.firstOccurrence? v = some j) :
    (allInputQueryCosted tree hagreement u v).cost =
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (LCACost.suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  exact LCACost.queryViaRMQIndexedCosted_cost_of_firstOccurrences tree
    (allInputRMQBackend tree) hagreement hu hv

theorem allInputQueryCosted_cost_le
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (allInputQueryCosted tree hagreement u v).cost <=
      TableModel.indexedReadCost +
        (TableModel.indexedReadCost +
          (LCACost.suppliedRMQQueryCost + TableModel.indexedReadCost)) := by
  exact LCACost.queryViaRMQIndexedCosted_cost_le tree
    (allInputRMQBackend tree) hagreement u v

theorem allInputQueryCosted_cost_le_four
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (allInputQueryCosted tree hagreement u v).cost <= 4 := by
  have h := allInputQueryCosted_cost_le tree hagreement u v
  simpa [LCACost.suppliedRMQQueryCost, LCACost.suppliedQueryCost,
    TableModel.indexedReadCost] using h

theorem allInputQueryCosted_run
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (allInputQueryCosted tree hagreement u v).run =
      (allInputCandidate tree u v, allInputQueryCost tree u v) := by
  unfold allInputQueryCosted allInputQueryCost allInputCandidate
  exact LCACost.queryViaRMQIndexedCosted_run tree
    (allInputRMQBackend tree) hagreement u v

end LCAFischerHeun

end RMQ
