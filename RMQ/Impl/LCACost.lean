import RMQ.Core.Cost
import RMQ.Core.Reduction

/-!
# Costed LCA bridge scaffolding

This module gives the first costed wrapper around the existing LCA-via-RMQ
correctness layer.  The costs are model-level charges: building an Euler trace
is charged by the depth-list length, and a supplied LCA backend query is charged
as one abstract backend query.
-/

namespace RMQ

namespace LCACost

/-- Model cost charged to materialize a generated Euler trace. -/
def eulerTraceBuildCost (tree : RoseTree) : Nat :=
  tree.eulerTrace.depths.length

/-- Costed generated Euler-trace construction. -/
def eulerTraceCosted (tree : RoseTree) : Costed EulerTrace :=
  Costed.tickValue (eulerTraceBuildCost tree) tree.eulerTrace

theorem eulerTraceCosted_erase (tree : RoseTree) :
    (eulerTraceCosted tree).erase = tree.eulerTrace := by
  rfl

theorem eulerTraceCosted_cost (tree : RoseTree) :
    (eulerTraceCosted tree).cost = eulerTraceBuildCost tree := by
  rfl

theorem eulerTraceCosted_run (tree : RoseTree) :
    (eulerTraceCosted tree).run =
      (tree.eulerTrace, eulerTraceBuildCost tree) := by
  rfl

/-- Supplied-backend LCA query cost in the abstract RAM/backend model. -/
def suppliedQueryCost : Nat := 1

/-- Costed query through an already-built exact LCA backend. -/
def queryCosted
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    Costed (Option Nat) :=
  Costed.tickValue suppliedQueryCost
    (LCABackend.queryBuilt backend u v)

theorem queryCosted_erase
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    (queryCosted tree backend u v).erase =
      LCABackend.queryBuilt backend u v := by
  rfl

theorem queryCosted_cost
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    (queryCosted tree backend u v).cost = suppliedQueryCost := by
  rfl

theorem queryCosted_run
    (tree : RoseTree) (backend : LCABackend tree) (u v : Nat) :
    (queryCosted tree backend u v).run =
      (LCABackend.queryBuilt backend u v, suppliedQueryCost) := by
  rfl

/--
Costed query through the structural Euler reduction from a supplied RMQ backend.
The correctness theorem is inherited from `RoseTree.lcaBackendOfRMQBackend`.
-/
def queryViaRMQCosted
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) : Costed (Option Nat) :=
  queryCosted tree
    (tree.lcaBackendOfRMQBackend rmqBackend hagreement) u v

theorem queryViaRMQCosted_erase
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQCosted tree rmqBackend hagreement u v).erase =
      tree.lcaCandidate rmqBackend u v := by
  rfl

theorem queryViaRMQCosted_cost
    (tree : RoseTree)
    (rmqBackend : RMQBackend tree.eulerTrace.depths)
    (hagreement : tree.TracePathAgreement)
    (u v : Nat) :
    (queryViaRMQCosted tree rmqBackend hagreement u v).cost =
      suppliedQueryCost := by
  rfl

end LCACost

end RMQ
