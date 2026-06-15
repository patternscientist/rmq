import RMQ.Core.LCA

/-!
# RMQ/LCA reductions

This module packages the two standard reduction directions at the contract
boundary.

* A certified generated Euler trace turns any exact RMQ backend over depths
  into an exact LCA backend.
* Any certified encoding of RMQ intervals as LCA queries turns any exact LCA
  backend into an exact RMQ backend.

The second direction is intentionally certificate-shaped: a future Cartesian
tree construction can discharge `RMQToLCAReduction`, while the theorem here
keeps the backend equivalence independent of that representation choice.
-/

namespace RMQ

/-- Explicit exact LCA backend for a fixed rose tree. -/
structure LCABackend (tree : RoseTree) where
  State : Type
  build : State
  query : State -> Nat -> Nat -> Option Nat
  sound :
    forall {u v ancestor},
      query build u v = some ancestor ->
        tree.IsPathLCA u v ancestor
  complete :
    forall {u v ancestor},
      tree.pathLCA? u v = some ancestor ->
        query build u v = some ancestor

namespace LCABackend

/-- Query an LCA backend using its canonical built state. -/
def queryBuilt {tree : RoseTree} (backend : LCABackend tree) (u v : Nat) :
    Option Nat :=
  backend.query backend.build u v

end LCABackend

namespace RoseTree

theorem pathLCA?_eq_of_isPathLCA
    {tree : RoseTree} {u v ancestor : Nat}
    (h : tree.IsPathLCA u v ancestor) :
    tree.pathLCA? u v = some ancestor := by
  rcases h with ⟨pathU, pathV, hu, hv, hlca, _hcommon⟩
  unfold pathLCA?
  rw [hu, hv]
  exact hlca

theorem leftmostMinNode?_eq_pathLCA_of_labelPairAgreement
    (tree : RoseTree)
    (hcheck : tree.labelPairAgreement = true)
    {u v : Nat}
    (hu : u ∈ tree.labelsPreorder)
    (hv : v ∈ tree.labelsPreorder) :
    tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v := by
  have hall_u :
      (tree.labelsPreorder.all fun v =>
        decide (tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v)) =
        true := by
    exact (List.all_eq_true.mp hcheck) u hu
  have hagree_decide :
      decide (tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v) =
        true := by
    exact (List.all_eq_true.mp hall_u) v hv
  exact of_decide_eq_true hagree_decide

end RoseTree

namespace EulerTrace

theorem lcaCandidate_eq_leftmostMinNode?
    (trace : EulerTrace) (backend : RMQBackend trace.depths) (u v : Nat) :
    trace.lcaCandidate backend u v = trace.leftmostMinNode? u v := by
  unfold lcaCandidate leftmostMinNode?
  cases hu : trace.firstOccurrence? u with
  | none =>
      simp
  | some i =>
      cases hv : trace.firstOccurrence? v with
      | none =>
          simp
      | some j =>
          simp
          let window := occurrenceWindow i j
          let len := window.2 - window.1
          have hValid :
              ValidRange trace.depths window.1 window.2 := by
            simpa [window] using trace.occurrenceWindow_valid hu hv
          have hlen : 0 < len := by
            unfold len
            omega
          have hbound : window.1 + len <= trace.depths.length := by
            unfold len
            omega
          have hright : window.1 + len = window.2 := by
            unfold len
            omega
          have hscan :
              LeftmostArgMin trace.depths window.1 window.2
                (scanWindow trace.depths window.1 len) := by
            simpa [hright] using
              scanWindow_leftmost trace.depths window.1 len hlen hbound
          have hquery :
              RMQBackend.queryBuilt backend window.1 window.2 =
                some (scanWindow trace.depths window.1 len) :=
            backend.complete hscan
          unfold minDepthNodeInWindow
          rw [hquery]

end EulerTrace

namespace RoseTree

/--
Certified Euler reduction from LCA to RMQ: an exact RMQ backend over the
generated depth trace induces an exact LCA backend over the tree labels.
-/
def lcaBackendOfRMQBackend
    (tree : RoseTree)
    (backend : RMQBackend tree.eulerTrace.depths)
    (hexact : tree.TracePathExactOnLabels) :
    LCABackend tree where
  State := Unit
  build := ()
  query := fun _ u v => tree.lcaCandidate backend u v
  sound := by
    intro u v ancestor hresult
    exact tree.lcaCandidate_isPathLCA_of_tracePathExactOnLabels
      backend hexact hresult
  complete := by
    intro u v ancestor hpath
    rcases labels_mem_of_pathLCA?_some hpath with ⟨hu, hv⟩
    have hagree :
        tree.eulerTrace.leftmostMinNode? u v = tree.pathLCA? u v :=
      hexact hu hv
    have hcand :
        tree.lcaCandidate backend u v =
          tree.eulerTrace.leftmostMinNode? u v := by
      exact EulerTrace.lcaCandidate_eq_leftmostMinNode?
        tree.eulerTrace backend u v
    rw [hcand, hagree, hpath]

/--
Boolean-check wrapper for the generated Euler reduction. The core reduction
above depends only on the semantic exactness contract, while this wrapper keeps
the existing finite certificate entry point available.
-/
def lcaBackendOfRMQBackendChecked
    (tree : RoseTree)
    (backend : RMQBackend tree.eulerTrace.depths)
    (hcheck : tree.labelPairAgreement = true) :
    LCABackend tree :=
  tree.lcaBackendOfRMQBackend backend
    (tree.tracePathExactOnLabels_of_labelPairAgreement hcheck)

end RoseTree

/--
A certificate that an RMQ problem can be represented by LCA queries.

`leftLabel left` and `rightLabel right` choose the two LCA labels for the
half-open RMQ range `[left, right)`. `decode` maps the returned LCA label back
to an RMQ index.
-/
structure RMQToLCAReduction (xs : List Int) where
  tree : RoseTree
  leftLabel : Nat -> Nat
  rightLabel : Nat -> Nat
  decode : Nat -> Option Nat
  exists_lca :
    forall {left right},
      ValidRange xs left right ->
        exists ancestor,
          tree.pathLCA? (leftLabel left) (rightLabel right) = some ancestor
  sound :
    forall {left right ancestor idx},
      ValidRange xs left right ->
        tree.pathLCA? (leftLabel left) (rightLabel right) = some ancestor ->
          decode ancestor = some idx ->
            LeftmostArgMin xs left right idx
  complete :
    forall {left right idx},
      LeftmostArgMin xs left right idx ->
        exists ancestor,
          tree.pathLCA? (leftLabel left) (rightLabel right) = some ancestor /\
            decode ancestor = some idx

namespace RMQToLCAReduction

/-- Query an RMQ interval through an LCA backend and decode the LCA answer. -/
def queryWithLCABackend
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (backend : LCABackend reduction.tree) (left right : Nat) : Option Nat :=
  if _h : ValidRange xs left right then
    match LCABackend.queryBuilt backend
        (reduction.leftLabel left) (reduction.rightLabel right) with
    | none => none
    | some ancestor => reduction.decode ancestor
  else
    none

theorem queryWithLCABackend_sound
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (backend : LCABackend reduction.tree)
    {left right idx : Nat}
    (hquery : reduction.queryWithLCABackend backend left right = some idx) :
    LeftmostArgMin xs left right idx := by
  unfold queryWithLCABackend at hquery
  by_cases hValid : ValidRange xs left right
  · simp at hquery
    cases hlca :
        LCABackend.queryBuilt backend
          (reduction.leftLabel left) (reduction.rightLabel right) with
    | none =>
        simp [hlca] at hquery
    | some ancestor =>
        cases hdecode : reduction.decode ancestor with
        | none =>
            simp [hlca, hdecode] at hquery
        | some decodedIdx =>
            simp [hlca, hdecode] at hquery
            rcases hquery with ⟨_hValid', hidx⟩
            cases hidx
            have hisLCA :
                reduction.tree.IsPathLCA
                  (reduction.leftLabel left) (reduction.rightLabel right)
                  ancestor :=
              backend.sound hlca
            have hpath :
                reduction.tree.pathLCA?
                  (reduction.leftLabel left) (reduction.rightLabel right) =
                    some ancestor :=
              RoseTree.pathLCA?_eq_of_isPathLCA hisLCA
            exact reduction.sound hValid hpath hdecode
  · simp [hValid] at hquery

theorem queryWithLCABackend_complete
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (backend : LCABackend reduction.tree)
    {left right idx : Nat}
    (harg : LeftmostArgMin xs left right idx) :
    reduction.queryWithLCABackend backend left right = some idx := by
  have hValid : ValidRange xs left right := LeftmostArgMin.valid harg
  rcases reduction.complete harg with ⟨ancestor, hpath, hdecode⟩
  have hquery :
      LCABackend.queryBuilt backend
        (reduction.leftLabel left) (reduction.rightLabel right) =
          some ancestor :=
    backend.complete hpath
  unfold queryWithLCABackend
  simp [hValid, hquery, hdecode]

theorem queryWithLCABackend_invalid_none
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (backend : LCABackend reduction.tree)
    {left right : Nat}
    (hbad : Not (ValidRange xs left right)) :
    reduction.queryWithLCABackend backend left right = none := by
  unfold queryWithLCABackend
  simp [hbad]

/--
Certified LCA reduction from RMQ: any exact LCA backend over the reduction tree
induces an exact RMQ backend over `xs`.
-/
def rmqBackendOfLCABackend
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (backend : LCABackend reduction.tree) :
    RMQBackend xs where
  State := Unit
  build := ()
  query := fun _ left right => reduction.queryWithLCABackend backend left right
  sound := by
    intro left right idx hquery
    exact reduction.queryWithLCABackend_sound backend hquery
  complete := by
    intro left right idx harg
    exact reduction.queryWithLCABackend_complete backend harg
  invalid_none := by
    intro left right hbad
    exact reduction.queryWithLCABackend_invalid_none backend hbad

end RMQToLCAReduction

/--
Contract-level RMQ/LCA equivalence.

The left projection is the RMQ-from-LCA direction for any certified interval
encoding. The right projection is the LCA-from-RMQ direction for any certified
generated Euler trace.
-/
def rmq_lca_reduction_equiv
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (tree : RoseTree) (hexact : tree.TracePathExactOnLabels) :
    (LCABackend reduction.tree -> RMQBackend xs) ×
      (RMQBackend tree.eulerTrace.depths -> LCABackend tree) :=
  (fun backend => reduction.rmqBackendOfLCABackend backend,
    fun backend => tree.lcaBackendOfRMQBackend backend hexact)

theorem rmq_lca_reduction_equiv_exists
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (tree : RoseTree) (hexact : tree.TracePathExactOnLabels) :
    Nonempty ((LCABackend reduction.tree -> RMQBackend xs) ×
      (RMQBackend tree.eulerTrace.depths -> LCABackend tree)) := by
  exact ⟨rmq_lca_reduction_equiv reduction tree hexact⟩

/-- Backward-compatible boolean-check entry point for the equivalence wrapper. -/
def rmq_lca_reduction_equiv_checked
    {xs : List Int} (reduction : RMQToLCAReduction xs)
    (tree : RoseTree) (hcheck : tree.labelPairAgreement = true) :
    (LCABackend reduction.tree -> RMQBackend xs) ×
      (RMQBackend tree.eulerTrace.depths -> LCABackend tree) :=
  rmq_lca_reduction_equiv reduction tree
    (tree.tracePathExactOnLabels_of_labelPairAgreement hcheck)

end RMQ
