# BV-1 checkout-byte scope disposition — 2026-09-12

Decision: APPROVE_EXACT_ADDITIVE_SCOPE_EXTENSION.

The coordinator read CHECKOUT_BYTES_PATCH.diff and the current root .gitattributes at BV-1 source base 645a0502b9da9ad6444edbe44759e1c2c5661f25. The requested four -text rules are confined to the existing BV-1 owned modules, validator, scripts and evidence directory. They preserve bytes rather than rewriting the frozen matrix or widening a checker allowance. The design checker already classifies .gitattributes as neutral; no classifier edit is authorized or needed.

Extend BV-1 write scope to .gitattributes solely for those four additive rules:
- RMQ/Core/WordRAM/Bitvector/** -text
- RMQ/Validation/PackedBitvector.lean -text
- scripts/packed_bitvector_* -text
- docs/internal/extensions/bv1/** -text

Preserve all other attributes and all 30 frozen theorem requirements. Append the rationale and exact fresh-checkout measurement to the already-owned WORKFLOW_DESIGN_DECISIONS.md. Verify the prospective/final committed blobs and a fresh isolated checkout retain every identity on which replay relies, including the frozen matrix and binary evidence; compare hashes rather than relying on the attribute declaration. Do not renormalize or rewrite existing evidence to make a hash pass. Continue the current proof/replay campaign and the original final checks. No theorem/model, main integration or aggregate-slot disposition changes.

Classification: necessary artifact-reproducibility prerequisite within the authorized extension, not an implementation defect or a new architecture choice. Durable layer: exact attributes plus measured byte round-trip. Owner: BV-1. Status: implementation/verification pending.


## Approved fifth rule: build manifest

The coordinator inspected CHECKOUT_BYTES_LAKEFILE_PATCH.diff and checkout-lakefile-observation.json, and independently verified the current manifest and preserved checkout output. Current691 bytes hash66F2730CC65D0A796A6595D230B18C0554826DFEE9407799F64D0F744D3D823A becomes696 bytes hash5CFC20B6F1A9BED1EEF7CD96DADAFED6286C1147F22EA4F42DC19915AD4E2298 under the existing core.autocrlf=true index checkout. The current text attribute is unspecified.

APPROVE adding solely lakefile.toml -text and the proposed explanatory comment to root .gitattributes. lakefile.toml was already in BV-1's owned scope for its validation target; this rule closes the measured replay-byte prerequisite. No global Git setting change, renormalization, checker allowance or theorem/model change is authorized. Preserve the actual manifest bytes and all frozen rows. Record the amendment in the already-owned workflow ledger. Verify final Git blob and fresh autoCRLF checkout hashes after staging/committing the attributes and manifest; adding an attribute alone does not prove that the index now holds the intended bytes. Confirm the parsed manifest still changes only the owned validation target. Continue the existing campaign without a new checkpoint or duplicate unchanged run.

