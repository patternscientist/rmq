import RMQBPNavigation

/-!
Focused trust-base check for the standalone balanced-parentheses navigation
spoke.

The full RMQ gate still runs `scripts/axiom_check.lean`. This smaller check is
for the public BP close/LCA navigation facade: compact close-directory profile,
large-regime profile, and the generic payload-live macro/micro family profile.
-/

#print axioms RMQ.BPNavigation.compactCloseDirectoryProfile
#print axioms RMQ.BPNavigation.compactCloseDirectoryProfileOfSizeGe
#print axioms RMQ.BPNavigation.macroMicroTwoNPlusOBuiltQueryProfile
#print axioms RMQ.SuccinctClose.PayloadLiveMacroMicroBPCloseNavigationFamily.two_n_plus_o_built_query_profile
