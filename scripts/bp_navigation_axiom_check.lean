import RMQBPNavigation

/-!
Focused trust-base check for the standalone balanced-parentheses navigation
spoke.

The full RMQ gate still runs `scripts/axiom_check.lean`. This smaller check is
for the public BP navigation facade: the close/rank bridge, compact
close-directory profile, subtree interval navigation profile, large-regime
profile, and the generic payload-live macro/micro family profile.
-/

#print axioms RMQ.BPNavigation.closeOfInorderCosted_erase
#print axioms RMQ.BPNavigation.inorderOfCloseCosted_erase_of_bpCloseOfInorder?
#print axioms RMQ.BPNavigation.excessAtCosted_erase
#print axioms RMQ.BPNavigation.closeRank_le_openRank_of_le
#print axioms RMQ.BPNavigation.closeRankPrefix_le_openRankPrefix_of_le
#print axioms RMQ.BPNavigation.closeExcessOfInorderCosted_erase
#print axioms RMQ.BPNavigation.closeExcessOfInorderCosted_erase_of_bpCloseOfInorder?
#print axioms RMQ.BPNavigation.matchingOpenSearchCosted_erase
#print axioms RMQ.BPNavigation.subtreeIntervalOfInorderCosted_erase
#print axioms RMQ.BPNavigation.subtreeIntervalOfInorderCosted_cost_le
#print axioms RMQ.BPNavigation.shapeAccessCloseRankProfile
#print axioms RMQ.BPNavigation.shapeAccessCloseRankExcessProfile
#print axioms RMQ.BPNavigation.shapeAccessSubtreeIntervalProfile
#print axioms RMQ.BPNavigation.compactCloseDirectoryProfile
#print axioms RMQ.BPNavigation.compactCloseDirectoryProfileOfSizeGe
#print axioms RMQ.BPNavigation.macroMicroTwoNPlusOBuiltQueryProfile
#print axioms RMQ.SuccinctClose.PayloadLiveMacroMicroBPCloseNavigationFamily.two_n_plus_o_built_query_profile
