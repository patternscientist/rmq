import RMQBPNavigation

/-!
# Minimal BP-navigation import example

This is the small reusable spoke surface for compact balanced-parentheses
close/LCA navigation over Cartesian-shape BP encodings.
-/

namespace RMQ.Examples.BPNavigationImport

abbrev CompactCloseDirectory :=
  RMQ.BPNavigation.CompactCloseDirectory

abbrev compactCloseDirectory :=
  RMQ.BPNavigation.compactCloseDirectory

abbrev compactCloseProfile :=
  RMQ.BPNavigation.compactCloseDirectoryProfile

abbrev macroMicroProfile
    {rankOverhead selectOverhead codeOverhead codeCount
      microTableOverhead macroOverhead : Nat -> Nat}
    {lcaQueryCost : Nat}
    (family :
      RMQ.BPNavigation.MacroMicroCloseNavigationFamily
        rankOverhead selectOverhead codeOverhead codeCount
        microTableOverhead macroOverhead lcaQueryCost) :=
  RMQ.BPNavigation.macroMicroTwoNPlusOBuiltQueryProfile family

end RMQ.Examples.BPNavigationImport
