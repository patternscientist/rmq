import RMQ.Core.GenericSelect.Entries
import RMQ.Core.GenericSelect.FlagRank
import RMQ.Core.GenericSelect.RelativeTables

/-!
# Generic select table-layer compatibility barrel

The table layer is split by role into Entries, FlagRank, and
RelativeTables.  This module re-exports those pieces for older imports.
-/