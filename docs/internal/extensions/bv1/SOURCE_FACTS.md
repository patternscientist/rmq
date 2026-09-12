# BV-1 source facts

Baseline: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Two independent read-only
explorers inspected the semantic/directory and physical/compiler boundaries.
These are source facts, not acceptance of the new construction.

| Source | Exact useful proposition or boundary |
| --- | --- |
| `GenericSelect/Family.lean:32,40,57,242` | Overhead is Jacobson rank plus two canonical select overheads; it is LittleOLinear. For every List Bool, abstract payload is n+overhead, access equals list optional lookup, rank equals rankPrefix for all prefixes, select equals select for both targets/all occurrences. |
| `GenericSelect/Source.lean:1693,1812,1911` | SparseExceptionSelectData carries arbitrary bits/target and bounded rank/word stores. `payload_length_le_canonical` bounds its payload by canonicalSparseExceptionSelectOverhead bits.length. No Cartesian shape is required. |
| `SuccinctClose/RelativeRmmMacro/ChargedRankSelectLeaves.lean:666` | `bpChunkedSelectCosted_exact data hc hbw hlf hsd idx` concludes `(data.bpChunkedSelectCosted c idx).erase = Succinct.select target bits idx` under c>0 and each of the data/long-flag/sparse-flag word sizes <=8*c. |
| `SuccinctFinal/RAM/PackedCellProbe/ReadProgram.lean:608,686` | packedSelectCloseRead takes target, occurrence count and all geometry as numeric parameters. The supplied-store data algorithm equals that program by rfl for any SparseExceptionSelectData. |
| `SuccinctClose/RelativeRmmMacro/ChargedRankSelectLeafTrace.lean:1227` | Supplied-store trace-to-costed refinement is available under agreement with the same data tables. It is a logical-read result, requiring new physical reader/controller composition. |
| `SuccinctFinal/RAM/FlatPayload.lean:535` and `Segments.lean:174` | Exact mapping from select source segments to directory word arrays. The new experiment uses the same segment numbering for the unchanged source. |
| `SuccinctSpace/WordStore.lean:504` | `store.payload_eq_words_join` identifies each table/flag payload with its word-array erasure. Selected flag-rank tables omit their unused false sample tables; their total is bounded by the original payload, not equal to it by definition. |
| `SuccinctClose/RelativeRmmMacro/ChargedWordChunks.lean:39,647,652` | `machineWordBits_le_8_mul_bpFringeChunkBits` supplies complete eight-copy coverage. bpChunkSelectTableOverhead is LittleOLinear at chunk width bpFringeChunkBits(2*n). |
| `SuccinctClose/RelativeRmmMacro/ChargedFringeTableFacts.lean:98,103` | bpFringeTableOverhead supplies the corresponding LittleOLinear rank-chunk table envelope. |
| `WordRAM/Packed/DensePacking.lean:109,201` | denseWords capacity <= bit length + width; repackWords capacity <= old count*oldWidth + (header length+1)*width under each old cell length=oldWidth. Both are generic and preserve the leading payload coefficient. |
| `WordRAM/Packed/Span.lean:84,129` | decodeSpanNat_uniform recovers a bit slice from uniform physical cells under positive width, len<=width and in-bounds span. append_shift translates the same span behind an arbitrary numeric header. |
| `WordRAM/Packed/RegularLocate.lean:56` | `regularLocateBlock_source` proves LocatedSpan regularSpan and no reads for arbitrary numeric descriptors. Exact source size19. Logical count remains separate from bit length to preserve empty sentinel presence. |
| `WordRAM/Packed/SpanAssembly.lean:72` | `spanBlock_source` gives SpanOutcome decodeSpanNat and exact ordered spanAttemptReceipts for arbitrary memory/width/position/length and the corresponding input registers. Source size22. Missing loads fault and retain receipts; len0 performs no payload load. |
| `WordRAM/Packed/LoadSafety.lean:329` | spanBlock_safe requires width>=2, fitting memory/initial data, position<2^width and strict len<width, then proves source safety including failed loads. |
| `WordRAM/Packed/Frame.lean:32` | Constructor-derived WritesOnly yields eval_frame for arbitrary data, including stopped/faulting paths. |
| `WordRAM/Packed/Safety.lean:577` | compile_with_halt_safe relates one source evaluation to the actual run of compileAt0++halt, preserving result and ordered reads, bounding steps, proving every indexed instruction safe and every fuel prefix fitting. |
| `WordRAM/Packed/Calculus.lean:109,186,240` | Actual transitions partition all six cost categories; run_read_at preserves occurrence/pre-state/instruction/evaluated address/backing; run_eq_of_agree gives whole-run equality from agreement on attempted addresses including none replies. |
| `WordRAM/Packed/ArrayRun.lean:45` | runArray_toArray equates array-code fetching to the entire primitive run, including all transitions, receipts, values and counts. |

## Specialization boundaries

`Packed/ReadInterface.lean:75` is shape-indexed and uses shape metadata plus
concreteBPNativeSuccinctRMQGlobalReadStore. `Packed/PhysicalRead.lean` fixes the
174-word RMQ header/reviewer layout. `Packed/Allocation.lean` counts a different
shape allocation with leading 2*shape.size. None supplies the generic client's
allocation or reader theorem by instantiation.

The select source is a genuine reusable Block parameterized by its reader;
its outer guard uses register16, dense in-word select chooses false bits, and
flag rank chooses true. Generic target counts must be loaded independently of
length-based geometry. Normalize only raw segment0 words, never flag segments
11/15, and preserve actual logical length before padding. All scalar blocks
and final compilation remain the accepted shared definitions.

The source inventories found no necessary shared-module edit. The selected
route remains subject to execution evidence and the contract review. No
proof-side shape witness may constrain arbitrary input in the new capstone.
