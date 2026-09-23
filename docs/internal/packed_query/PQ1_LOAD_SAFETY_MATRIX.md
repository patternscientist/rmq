# PQ1-LW frozen acceptance matrix

Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`. Exact base: `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`. Shared checkout; no staging/commits. Preflight PASS. Frozen before source edits.

| ID | Verbatim requirement | Status/evidence |
| --- | --- | --- |
| REQ-LW-SPAN | For width>=2, arbitrary numeric memory whose every stored word is<2^width, and source Data.Fits width with registers base=width, base+1=position<2^width, base+2=len<width, prove (spanBlock base).Safe memory width data. Cover running/stopped data, len0, contained and crossing spans, missing first/second cells. Explicitly discharge subtraction non-underflow, positive divisors, both shift amounts<width, result fit and next-address fit. No successful-read premise. If a precise width>=2 edge is impossible, give the formal obstruction and tighten only the minimum constant; canonical wordWidth>=32 remains mandatory and unconditional. | CLOSED: `spanBlock_safe` concludes `(spanBlock base).Safe memory width s` from exactly the assigned numeric-memory, entry-fit, width/input and length hypotheses. Full proposition E1 below and report. Five actual source paths plus stopped data are checked; no read-presence premise. Challenges: width-2 zero, all-ones crossing, missing first/second. |
| REQ-LW-SETUP | Prove metadataSetupBlock.Safe on arbitrary fitting numeric memory and fitting source Data, for a sufficient fixed minimum width (e.g.8 so0..173 fit). Include failed early loads/stopped states; canonical buildMemory/wordWidth theorem must discharge all memory/minimum hypotheses without readiness/presence assumptions. Every loaded word remains the actual raw reply. | CLOSED: `metadataSetupBlock_safe` concludes `metadataSetupBlock.Safe memory width s` for `8 ≤ width`, arbitrary fitting memory and fitting Data. `buildMemory_setup_safe` discharges canonical memory/minimum width. Full propositions E2; `failed_setup` pins the first failed raw load and every later prefix. |
| REQ-LW-RUN | For the same actual standalone/hosted span run as its value/receipt theorem, combine explicit source safety and static code/end-PC fit to obtain each executed Instruction.Safe and every prefix State.Fits, retaining actual result/status/ordered receipts/fixed budget. Provide analogous canonical metadata-run consumer retaining installed fields/receipts/budget. Static field/end-PC premises are allowed on generic hosted blocks but must be discharged for fixed base8192 spanBlock at canonical wordWidth and standalone metadata block when giving their canonical consumers. | CLOSED: full hosted/standalone/canonical propositions E3–E4 retain value/status, ordered receipts, budget, each indexed `Instruction.Safe` and every prefix `State.Fits` on one actual run. Canonical span uses a bounded fixed base covering 8192 and 8256; setup uses the actual 348-fuel canonical run. No separate existential witnesses are combined. |
| CHK-LW-LEAN | Narrow checks and exact expected types. Symbolic arbitrary-memory theorem, all-ones/crossing/missing boundary consumers, empty/singleton canonical setup. No native_decide or hidden assumptions on a read that is not actually available. | CLOSED: exact clean-source -o/-i PASS 9.3711686 s; imported expected source types and five axiom inventories PASS 2.1893894 s. Symbolic and boundary consumers are in the checked module. All trust/whitespace scans pass. Final identity is recorded below; no replay campaign is claimed. |
| INV-WORD-WIDTH | stored and returned words fit one declared modeled machine word; | CLOSED: `actual.final.Fits width`, indexed post-state fit and all prefix fits are retained in E3–E4, with `run_read_fits` also proving every successful raw reply is below the same capacity. `MemoryWordsFit` supplies stored-word fit without invented replies. |
| INV-ADDRESS-WIDTH | every executed address, dead/sentinel address, and encoded instruction operand fits the modeled machine word, not merely the host array bounds. Constructor-exhaustive evidence must include register identifiers, branch/jump targets, dormant code, and arithmetic operands; | CLOSED: `span_next_address_fit` proves `position / width + 1 < 2 ^ width` before lookup, including failures. `spanRun_safe_read` gives actual receipt address fit. `spanBlock_fieldsFit` and canonical setup fields include dormant encodings/tags/registers; compiler safety includes actual PC/next-PC. Canonical memory length/sentinel capacity is retained in E5. |
| INV-WIDTH-SCALING | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | CLOSED: canonical execution, memory and code all use exactly `wordWidth xs.length`; E5 gives `(buildMemory xs).length < 2 ^ wordWidth xs.length` and `wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)`. These are the objects passed to E3–E4, not an unrelated width parameter. |
| INV-TRACE-EXECUTION | traces and footprints are derived from the execution they describe; | CLOSED: E3–E4 use `run memory program used initial`, `spanRun ...` or the actual 348-fuel setup run; each indexed transition and each prefix belongs to that execution. Read equality is transported from compiler source equality at the same fuel. Failed-read fixtures require actual fault status and ordered None replies. |
| INV-READ-BACKING | every successful read is backed positionally by the counted store; | CLOSED: `spanRun_safe_read` concludes `receipt.reply = memory[receipt.address]?` for an actual transition occurrence, retaining address/reply bounds. Canonical instances use the exact counted `buildMemory xs`; setup installed fields and receipt index 0 are tied through the existing metadata-prefix equality. Full object chain in report. |
| INV-PROOF-SEPARATION | proof-only fields never carry answers or uncharged routing information; | CLOSED: new predicates/proofs contain no runtime answer fields. `MemoryWordsFit` is only a bound on actual numeric cells; source evaluation performs all loads/arithmetic, and compiler preservation transfers it to actual instructions. No runtime loader, payload, width function or ISA was changed. |


## Verification ledger

| Command | Role/coverage | Tree/runtime/deadline | Outcome |
| --- | --- | --- | --- |
| Direct Lean LoadSafety.lean and exact consumers | Development/final; all Lean acceptance rows; elaboration and dependency types | Scoped dirty file on exact base; expected 5–20 s, 60 s wrapper margin | PASS; see final ledger |
| Scoped hygiene and git diff --check | Final; trust footprint and whitespace | Owned files only | PASS; see final ledger |

Broad Lake/gate/design certification is owned by root; no duplicate broad run for this narrow leaf.

## Final identity and checks

Source SHA256: `26b32ef5d4c651b4862b555326a3a8c027219ed7ac2f9c7591202146861909d8`. Exact assigned base remains `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`; shared HEAD at closure is `067b6ffd350aee08f1496335ce957895f0da3fcc`. No staging/commits. All 10 rows are closed for the bounded leaf; coordinator acceptance is pending.

- Final direct local Lean -o/-i: PASS cleanly, 9.3711686 seconds, chunks `beffad`/`072175`.
- Final imported exact source types and five axiom inventories: PASS, 2.1893894 seconds. Only propext, Classical.choice and Quot.sound occur; generic setup source omits Classical.choice.
- Repository-wide proof/runtime hygiene and native-decision scans: no matches.
- Scoped/untracked whitespace checks: PASS after trimming one source EOF blank line, followed by the final identity compile/import above.
- No source edit followed final verification. Full development outcomes, scope boundary, design proposal and digestion are in the report.

## E1: scalar span source and numeric bounds

```lean
theorem spanBlock_safe (base width position len : Nat) (memory : Memory)
    (s : Data) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (fit : s.Fits width) (hwreg : s.regs base = width)
    (hpreg : s.regs (base + 1) = position) (hlreg : s.regs (base + 2) = len)
    (hp : position < 2 ^ width) (hl : len < width) :
    (spanBlock base).Safe memory width s
```

```lean
theorem span_offset_sum_fit (width offset len : Nat) (hw : 2 ≤ width)
    (ho : offset < width) (hl : len < width) : offset + len < 2 ^ width
```

```lean
theorem span_next_address_fit (width position : Nat) (hw : 2 ≤ width)
    (hp : position < 2 ^ width) : position / width + 1 < 2 ^ width
```

```lean
theorem span_crossing_bounds (width offset len first second : Nat)
    (ho : offset < width) (hl : len < width) (cross : width < offset + len)
    (hf : first < 2 ^ width) :
    0 < offset ∧ 0 < width - offset ∧ width - offset < width ∧
    width - offset ≤ len ∧ len - (width - offset) < width ∧
    first / 2 ^ offset < 2 ^ (width - offset) ∧
    second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) < 2 ^ len ∧
    first / 2 ^ offset +
      second % 2 ^ (len - (width - offset)) * 2 ^ (width - offset) < 2 ^ len
```


## E2: arbitrary-memory and canonical setup source

```lean
theorem metadataSetupBlock_safe (memory : Memory) (width : Nat)
    (hw : 8 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (s : Data) (fit : s.Fits width) : metadataSetupBlock.Safe memory width s
```

```lean
theorem buildMemory_setup_safe (xs : List Int) (s : Data)
    (fit : s.Fits (wordWidth xs.length)) :
    metadataSetupBlock.Safe (buildMemory xs) (wordWidth xs.length) s
```


## E3: same hosted/standalone/canonical span runs

```lean
theorem spanBlock_machine_safe (base codeStart width position len : Nat)
    (memory : Memory) (program : Program) (regs : Registers)
    (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (host : HostedAt program codeStart ((spanBlock base).compileAt codeStart))
    (fields : (spanBlock base).FieldsFit width) (endFit : codeStart + 22 < 2 ^ width) :
    ∃ used, used ≤ 22 ∧
      let actual
```

```lean
theorem spanRun_safe (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (codeFit : base + 23 < 2 ^ width) :
    let actual
```

```lean
theorem spanRun_canonical_safe (xs : List Int) (base position len : Nat)
    (baseFit : base + 23 < 2 ^ 32) (hp : position < 2 ^ wordWidth xs.length)
    (hl : len < wordWidth xs.length) :
    let width
```

```lean
theorem spanRun_safe_read (base width position len : Nat) (memory : Memory)
    (regs : Registers) (hw : 2 ≤ width) (memoryFit : MemoryWordsFit memory width)
    (registerFit : ∀ r, regs r < 2 ^ width)
    (hwreg : regs base = width) (hpreg : regs (base + 1) = position)
    (hlreg : regs (base + 2) = len) (hp : position < 2 ^ width) (hl : len < width)
    (codeFit : base + 23 < 2 ^ width) (index : Nat) (t : Transition) (receipt : Receipt)
    (occurrence : (spanRun base memory regs).transitions[index]? = some t)
    (read : t.receipt = some receipt) :
    receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width)
```


## E4: same canonical and arbitrary-memory hosted setup runs

```lean
theorem buildMemory_setup_run_safe (xs : List Int) (s : State)
    (hpc : s.pc = 0) (hs : s.status = .running)
    (registerFit : ∀ r, s.regs r < 2 ^ wordWidth xs.length) :
    let width
```

```lean
theorem metadataSetupBlock_hosted_safe (memory : Memory) (program : Program)
    (width base : Nat) (s : State) (hw : 8 ≤ width)
    (memoryFit : MemoryWordsFit memory width) (fit : s.Fits width)
    (hpc : s.pc = base) (host : HostedAt program base (metadataSetupBlock.compileAt base))
    (fields : metadataSetupBlock.FieldsFit width) (endFit : base + 348 < 2 ^ width) :
    ∃ used, used ≤ 348 ∧
      Data.ofState (run memory program used s).final =
        (metadataSetupBlock.eval memory (Data.ofState s)).final ∧
      (run memory program used s).reads = (metadataSetupBlock.eval memory (Data.ofState s)).reads ∧
      (run memory program used s).steps = used ∧
      ((run memory program used s).final.status = .running →
        (run memory program used s).final.pc = base + 348) ∧
      (run memory program used s).final.Fits width ∧
      (∀ (index : Nat) (t : Transition), (run memory program used s).transitions[index]? = some t →
        Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
      (∀ index, index ≤ used → (run memory program index s).final.Fits width)
```

```lean
theorem failed_setup :
    let width
```


## E5: same canonical width/memory and concrete bank/metadata consumers

```lean
theorem canonical_width_and_memory (xs : List Int) :
    MemoryWordsFit (buildMemory xs) (wordWidth xs.length) ∧
    (buildMemory xs).length < 2 ^ wordWidth xs.length ∧
    wordWidth xs.length ≤ 192 * (Nat.log2 (xs.length + 2) + 1)
```

```lean
theorem canonical_banks (xs : List Int) (position len : Nat)
    (hp : position < 2 ^ wordWidth xs.length) (hl : len < wordWidth xs.length) :
    (spanRun 8192 (buildMemory xs)
      (spanInputRegisters 8192 (wordWidth xs.length) position len)).final.Fits (wordWidth xs.length) ∧
    (spanRun 8256 (buildMemory xs)
      (spanInputRegisters 8256 (wordWidth xs.length) position len)).final.Fits (wordWidth xs.length)
```

```lean
theorem canonical_setup_size_installed (xs : List Int) :
    let initial : State
```
