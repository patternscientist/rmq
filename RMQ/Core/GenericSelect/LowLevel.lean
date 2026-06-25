import RMQ.Core.GenericSelect.SelectFacts
import RMQ.Core.GenericSelect.Arithmetic
import RMQ.Core.GenericSelect.DenseEntryTable
import RMQ.Core.GenericSelect.DenseWord
import RMQ.Core.GenericSelect.RelativeSplit

/-!
# Generic select low-level helpers

Compatibility barrel for shape-free select facts, arithmetic, dense-entry table,
aligned payload-word, and relative-split helpers shared by the generic select
construction. Legacy false-named aliases and BP-shaped compatibility facts live
above this pure generic layer.
-/
