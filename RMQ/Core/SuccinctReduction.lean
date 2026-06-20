import RMQ.Core.Succinct
import RMQ.Core.Reduction

/-!
# Succinct RMQ/LCA reduction adapters

This module connects the succinct Euler-parentheses layer to the existing
RMQ-to-LCA reduction boundary.  The bit and parenthesis primitives remain in
`Core.Succinct`; the reduction-facing wrappers live here to avoid making the
succinct primitive layer depend directly on LCA backend packaging.
-/

namespace RMQ

namespace Succinct

/--
Forget a plus-minus-one backend over generated Euler-tour parentheses to the
ordinary RMQ backend expected by the tree LCA reduction.
-/
def rmqBackendOfEulerParensBackend
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree)) :
    RMQBackend tree.eulerTrace.depths where
  State := backend.rmq.State
  build := backend.rmq.build
  query := backend.rmq.query
  sound := by
    intro left right idx hres
    have hsound : LeftmostArgMin
        (plusMinusOneInputOfEulerParens tree).depths left right idx :=
      backend.rmq.sound hres
    simpa [RMQ.Succinct.plusMinusOneInputOfEulerParens_depths_eq_trace tree]
      using hsound
  complete := by
    intro left right idx harg
    have harg' : LeftmostArgMin
        (plusMinusOneInputOfEulerParens tree).depths left right idx := by
      simpa [RMQ.Succinct.plusMinusOneInputOfEulerParens_depths_eq_trace tree]
        using harg
    exact backend.rmq.complete harg'
  invalid_none := by
    intro left right hbad
    have hbad' :
        Not (ValidRange (plusMinusOneInputOfEulerParens tree).depths
          left right) := by
      intro hvalid
      apply hbad
      simpa [RMQ.Succinct.plusMinusOneInputOfEulerParens_depths_eq_trace tree]
        using hvalid
    exact backend.rmq.invalid_none hbad'

theorem rmqBackendOfEulerParensBackend_queryBuilt
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree))
    (left right : Nat) :
    RMQBackend.queryBuilt
        (rmqBackendOfEulerParensBackend tree backend) left right =
      PlusMinusOne.Backend.queryBuilt backend left right := by
  rfl

/-- LCA backend obtained from a plus-minus-one backend over Euler parentheses. -/
def lcaBackendOfEulerParensBackend
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement) :
    LCABackend tree :=
  tree.lcaBackendOfRMQBackend
    (rmqBackendOfEulerParensBackend tree backend) hagreement

/--
Unique labels discharge the trace/path agreement side condition for the
Euler-parentheses plus-minus-one LCA backend.
-/
def lcaBackendOfEulerParensBackendUnique
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree))
    (hunique : tree.LabelsUnique) :
    LCABackend tree :=
  lcaBackendOfEulerParensBackend tree backend
    (tree.tracePathAgreement_of_labelsUnique hunique)

/-- Query candidate induced by the Euler-parentheses plus-minus-one backend. -/
def lcaCandidateOfEulerParensBackend
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree))
    (u v : Nat) : Option Nat :=
  tree.lcaCandidate (rmqBackendOfEulerParensBackend tree backend) u v

theorem lcaCandidateOfEulerParensBackend_eq_queryBuilt
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    LCABackend.queryBuilt
        (lcaBackendOfEulerParensBackend tree backend hagreement) u v =
      lcaCandidateOfEulerParensBackend tree backend u v := by
  rfl

theorem lcaCandidateOfEulerParensBackend_isPathLCA_of_tracePathAgreement
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree))
    (hagreement : tree.TracePathAgreement)
    {u v node : Nat}
    (hquery : lcaCandidateOfEulerParensBackend tree backend u v = some node) :
    tree.IsPathLCA u v node := by
  exact tree.lcaCandidate_isPathLCA_of_tracePathAgreement
    (rmqBackendOfEulerParensBackend tree backend) hagreement hquery

theorem lcaCandidateOfEulerParensBackend_isPathLCA_of_labelsUnique
    (tree : RoseTree)
    (backend : PlusMinusOne.Backend (plusMinusOneInputOfEulerParens tree))
    (hunique : tree.LabelsUnique)
    {u v node : Nat}
    (hquery : lcaCandidateOfEulerParensBackend tree backend u v = some node) :
    tree.IsPathLCA u v node := by
  exact lcaCandidateOfEulerParensBackend_isPathLCA_of_tracePathAgreement
    tree backend (tree.tracePathAgreement_of_labelsUnique hunique) hquery

/--
Concrete LCA backend obtained from the packed Euler-parentheses
plus-minus-one RMQ model.
-/
def packedEulerParensLCABackend
    (tree : RoseTree) (hagreement : tree.TracePathAgreement) :
    LCABackend tree :=
  lcaBackendOfEulerParensBackend tree
    (packedEulerParensBackend tree) hagreement

/--
Concrete packed-Euler-parentheses LCA backend in the common unique-label
regime.
-/
def packedEulerParensLCABackendUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique) :
    LCABackend tree :=
  packedEulerParensLCABackend tree
    (tree.tracePathAgreement_of_labelsUnique hunique)

/-- Candidate query induced by the packed Euler-parentheses PM1 backend. -/
def packedEulerParensLCACandidate
    (tree : RoseTree) (u v : Nat) : Option Nat :=
  lcaCandidateOfEulerParensBackend tree
    (packedEulerParensBackend tree) u v

theorem packedEulerParensLCACandidate_eq_queryBuilt
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    LCABackend.queryBuilt
        (packedEulerParensLCABackend tree hagreement) u v =
      packedEulerParensLCACandidate tree u v := by
  rfl

theorem packedEulerParensLCACandidate_isPathLCA_of_tracePathAgreement
    (tree : RoseTree) (hagreement : tree.TracePathAgreement)
    {u v node : Nat}
    (hquery : packedEulerParensLCACandidate tree u v = some node) :
    tree.IsPathLCA u v node := by
  exact lcaCandidateOfEulerParensBackend_isPathLCA_of_tracePathAgreement
    tree (packedEulerParensBackend tree) hagreement hquery

theorem packedEulerParensLCACandidate_isPathLCA_of_labelsUnique
    (tree : RoseTree) (hunique : tree.LabelsUnique)
    {u v node : Nat}
    (hquery : packedEulerParensLCACandidate tree u v = some node) :
    tree.IsPathLCA u v node := by
  exact packedEulerParensLCACandidate_isPathLCA_of_tracePathAgreement
    tree (tree.tracePathAgreement_of_labelsUnique hunique) hquery

end Succinct

end RMQ
