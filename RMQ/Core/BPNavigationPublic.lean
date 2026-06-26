import RMQ.Core.BPCloseNavigation

/-!
Public facade for the balanced-parentheses close-navigation spoke.

The construction modules keep the detailed `SuccinctClose` names. This module
provides shorter downstream names for compact BP close/LCA navigation over
Cartesian-shape balanced-parentheses encodings. This is not yet a full tree
navigation API; it is the reusable close/LCA navigation layer consumed by the
succinct RMQ capstone.
-/

namespace RMQ.BPNavigation

/-- Compact BP close/LCA directory shape for one Cartesian shape. -/
abbrev CompactCloseDirectory :=
  RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-- Auxiliary-overhead budget for the compact BP close/LCA directory. -/
abbrev compactCloseOverhead :=
  RMQ.SuccinctClose.compactBPCloseOverhead

/-- Uniform modeled query cost for unseeded compact BP close/LCA queries. -/
abbrev compactCloseQueryCost :=
  RMQ.SuccinctClose.concreteCompactBPCloseQueryCost

/--
Uniform modeled query cost when endpoint-local BP decoding receives rank-close
seeds from a supplied rank/select layer.
-/
abbrev compactCloseQueryCostWithRankSeed :=
  RMQ.SuccinctClose.concreteCompactBPCloseQueryCostWithRankSeed

/-- Concrete compact BP close/LCA directory for one Cartesian shape. -/
abbrev compactCloseDirectory :=
  RMQ.SuccinctClose.concreteCompactBPCloseLCADirectory

/--
Public profile for the concrete compact BP close/LCA directory: `o(n)`
auxiliary payload, constant modeled query cost, exact answer-close semantics,
and machine-word-bounded payload reads.
-/
abbrev compactCloseDirectoryProfile :=
  RMQ.SuccinctClose.concreteCompactBPCloseLCADirectory_profile

/-- Large-regime version of `compactCloseDirectoryProfile`. -/
abbrev compactCloseDirectoryProfileOfSizeGe :=
  RMQ.SuccinctClose.concreteCompactBPCloseLCADirectory_profile_of_size_ge

/-- Generic payload-live BP close-navigation family shape. -/
abbrev MacroMicroCloseNavigationFamily :=
  RMQ.SuccinctClose.PayloadLiveMacroMicroBPCloseNavigationFamily

/--
Generic `2*n + o(n)`, constant-query profile for payload-live BP close
navigation families.
-/
abbrev macroMicroTwoNPlusOBuiltQueryProfile
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (family :
      MacroMicroCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) :=
  RMQ.SuccinctClose.PayloadLiveMacroMicroBPCloseNavigationFamily.two_n_plus_o_built_query_profile
    family

end RMQ.BPNavigation
