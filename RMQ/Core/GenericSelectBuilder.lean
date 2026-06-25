import RMQ.Core.GenericSelect.Family
import RMQ.Core.GenericSelectLegacy

/-!
# Generic select builder compatibility barrel

The former monolithic builder module has been split behind role-named modules:
`GenericSelect.LowLevel` and its submodules, `GenericSelect.Params`,
`GenericSelect.Primitives`, `GenericSelect.Slots`, `GenericSelect.Entries`,
`GenericSelect.FlagRank`,
`GenericSelect.RelativeTables`, `GenericSelect.Directory`,
`GenericSelect.SelectSource`, `GenericSelect.Source`, and
`GenericSelect.Family`. This file remains as a compatibility import for older
downstream modules, including the older false-named aliases.
-/
