# Frozen inherited invariant blocks

- `INV-STORE-IDENTITY`: the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;

- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;

- `INV-SEMANTIC-NONVACUITY`: semantic coverage, liveness, ownership, and
  refinement predicates are derived from the operational construction they
  describe. A predicate defined to be `True`, an enumeration restated as
  membership, or a separately hand-written consumer label does not establish
  operational liveness by itself;

- `INV-TRACE-EXECUTION`: traces and footprints are derived from the execution
  they describe;

- `INV-STORE-AGREEMENT`: supplied-store agreement determines result, cost, and
  the relevant trace;

- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;

- `INV-WORD-WIDTH`: stored and returned words fit one declared modeled
  machine word;

- `INV-ADDRESS-WIDTH`: every executed address, dead/sentinel address, and
  encoded instruction operand fits the modeled machine word, not merely the
  host array bounds. Constructor-exhaustive evidence must include register
  identifiers, branch/jump targets, dormant code, and arithmetic operands;

- `INV-INSTRUCTION-ATOMICITY`: each modeled small step performs the familiar
  primitive operation it advertises. A constructor whose evaluator body hides
  recursion, a variable-length scan, repeated rank/select work, decoding, or
  several arithmetic categories is a macro-step unless that work is expanded
  into charged transitions or bounded by an explicitly accepted primitive;

- `INV-PROGRAM-ACCOUNTING`: input-dependent constants and metadata carried by
  executable code are counted machine data or are derived uniformly from
  counted/public inputs. Calling shape-specialized data "program code" does
  not remove it from the payload/state accounting obligation;

- `INV-ORACLE-INDEPENDENCE`: executable fixtures and edge-case expected values
  come from an independent specification or a theorem already connected to it,
  never from the implementation result being tested;

- `INV-VALIDATION-REACH`: executable validation imports and runs the new
  semantic layer. A validator for the predecessor implementation is regression
  evidence only and does not validate the new machine;

- `INV-ALL-SIZE`: exactness covers all assigned sizes and edge cases without
  hidden readiness or compatibility dispatch;

- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;

- `INV-NO-SYNTHETIC`: synthetic events, decorative rereads, and post-hoc replay
  do not support the execution claim;

- `INV-CATEGORY-SEPARATION`: payload bits, proof fields, model ticks, machine
  state, Lean runtime, and measured performance remain distinct.

- `INV-PUBLIC-COMPOSITION`: a theorem combining space, exactness, cost,
  provenance, or machine claims proves them about the same construction and
  execution and over the same validity domain. Conjoining true theorems about
  different payloads or guarded and unguarded executions is not closure.

- `INV-CERTIFICATE-ANTI-BYPASS`: every mandatory field advertised by a public
  certificate is projected by a checked typed consumer at the exact proposition
  and object arguments required by the acceptance contract. Deleting or
  weakening a field, or replacing it with a sibling fact, must break that
  consumer rather than leave only constructor initializers and prose unchanged.

- `INV-MUTATION-REPRODUCIBILITY`: when acceptance relies on an exhaustive,
  production, or public-dependency mutation campaign, the candidate contains a
  versioned runner or fixtures that replay every claimed case, check the exact
  expected failure/acceptance surface, restore tracked state, and leave the tree
  clean. Report prose, copied terminal output, and dangling Git objects are not
  replayable evidence. A public theorem additionally has a checked exact-type
  consumer that fails when the advertised dependency is removed; `#print
  axioms` over the theorem's current type is not such a consumer.

- `INV-GLOBAL-PHYSICAL-MACHINE`: a physical-machine claim supplies one
  pre-execution store/word array and a checked address translation for every
  executed segment, including failed/dead accesses. A theorem for one suffix or
  component is not a whole-machine embedding.

- `INV-WIDTH-SCALING`: one query-independent word-width declaration bounds all
  stored words, addresses, sentinels, operands, and primitive results, and its
  capacity/width is related to input size in the form required by the public
  word-RAM claim. A standalone asymptotic fact about an unconstrained width
  function is insufficient.
