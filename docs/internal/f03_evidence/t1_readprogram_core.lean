import RMQ.Core.SuccinctSpace.TablesRAM
import RMQ.Core.SuccinctSpace.WordStoreRAM

/-!
T1 reusable core: table read PROGRAMS are content-blind at the root.

`RMQ/Core/SuccinctSpace/WordStoreRAM.lean:26-29`

    def readProgram {payload : List Bool} (_store : PayloadWordStore payload)
        (i : Nat) : WordRAM.Program .optWord :=
      WordRAM.Program.readWord 0 i

The store argument is bound as `_store` -- unused -- so the emitted program is
literally `readWord 0 i` regardless of the payload. Every fixed-width table read
funnels through it (`TablesRAM.lean:53-57`, `:145-149`), so no table's CONTENTS
can influence an issued address. This is the same mechanism that closed the
interior cone via `machineReadComputationAt`'s unused `_table`, and it is the
reusable core for T1's table-reader obligations.

Widths still matter for DECODING (`FixedWidthOptionNatTable` maps with `width`),
which is why the option-table statement below is quantified over a shared width.
-/

namespace T1Core

open RMQ
open RMQ.SuccinctSpace

/-- Two payload word stores over DIFFERENT payloads emit the identical read
    program. -/
theorem payloadWordStore_readProgram_content_irrelevant
    {p1 p2 : List Bool}
    (s1 : PayloadWordStore p1) (s2 : PayloadWordStore p2) (i : Nat) :
    s1.readProgram i = s2.readProgram i := rfl

/-- Fixed-width `Nat` tables over different entry lists AND different widths
    emit the identical read program. Note the width is not even needed here. -/
theorem fixedWidthNatTable_readProgram_content_irrelevant
    {e1 e2 : List Nat} {w1 w2 : Nat}
    (t1 : FixedWidthNatTable e1 w1)
    (t2 : FixedWidthNatTable e2 w2) (i : Nat) :
    t1.readProgram i = t2.readProgram i := rfl

/-- Fixed-width `Option Nat` tables over different entry lists emit the
    identical read program, provided the decoding width agrees. -/
theorem fixedWidthOptionNatTable_readProgram_content_irrelevant
    {e1 e2 : List (Option Nat)} {w : Nat}
    (t1 : FixedWidthOptionNatTable e1 w)
    (t2 : FixedWidthOptionNatTable e2 w) (i : Nat) :
    t1.readProgram i = t2.readProgram i := rfl

/-- Anti-vacuity: the hypotheses are satisfiable by genuinely different
    payloads, so the theorems above are not vacuous. -/
example : ([true, false] : List Bool) ≠ ([false, true] : List Bool) := by decide

#print axioms payloadWordStore_readProgram_content_irrelevant
#print axioms fixedWidthNatTable_readProgram_content_irrelevant
#print axioms fixedWidthOptionNatTable_readProgram_content_irrelevant

end T1Core
