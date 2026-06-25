import RMQ.Core.GenericSelect.LowLevel
import RMQ.Core.GenericSelect.Params
import RMQ.Core.GenericSelect.Primitives
import RMQ.Core.GenericSelect.Slots
import RMQ.Core.GenericSelect.Entries
import RMQ.Core.GenericSelect.FlagRank
import RMQ.Core.GenericSelect.RelativeTables
import RMQ.Core.GenericSelect.Directory
import RMQ.Core.GenericSelect.SelectSource
import RMQ.Core.GenericSelect.Source
import RMQ.Core.GenericSelect.Family

/-!
# Generic select implementation barrel

This module is the role-named import surface for the target-parametric
rank/select construction. It re-exports the split parameter, primitive,
slot/span, entry, flag-rank, relative-table, directory, charged-source,
select-source, and family layers. Legacy false-named aliases and BP
compatibility bridges live in separate terminal roots.
-/
