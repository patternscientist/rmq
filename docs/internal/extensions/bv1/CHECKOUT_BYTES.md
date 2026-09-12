# BV-1 exact byte preservation

Status: INCOMPLETE — actual committed-blob and fresh-checkout replay is pending
the coordinated candidate commit.

The original four-rule authorization is retained verbatim in
[CHECKOUT_BYTES_DISPOSITION.md](CHECKOUT_BYTES_DISPOSITION.md), SHA256
`7F8810E67213EE3071044DFE1E72F354B52D3C6C2D90D1D1A56462B9E2926396`.
The subsequent build-manifest approval is retained separately in
[CHECKOUT_BYTES_LAKEFILE_DISPOSITION.md](CHECKOUT_BYTES_LAKEFILE_DISPOSITION.md),
SHA256 `F43488628BCDBDED05BC7139719F6E9CCFF3B5272BB138B14B14EB316101F512`.
Both exact reviewed patches are retained alongside those dispositions.

All five approved -text rules are applied: the Bitvector source directory,
its validator, packed_bitvector scripts, this evidence directory and
lakefile.toml. They preserve the bytes already used by checked proofs and
replays, including existing mixed line endings and binary archives. No global
Git setting, source payload, prior fixture or frozen requirement was changed.

The measured prerequisite was concrete. Of 230 public replay dependencies
outside the first four groups, only lakefile.toml was not already CRLF. Its
691-byte working copy has SHA256
`66F2730CC65D0A796A6595D230B18C0554826DFEE9407799F64D0F744D3D823A`.
An actual isolated index checkout with core.autocrlf=true produced 696 bytes,
SHA256 `5CFC20B6F1A9BED1EEF7CD96DADAFED6286C1147F22EA4F42DC19915AD4E2298`.
[checkout-lakefile-observation.json](commands/checkout-lakefile-observation.json)
retains that failed identity observation and exact command. The coordinator
independently confirmed both files before approving the fifth rule.

[manifest-semantics-v1.json](commands/manifest-semantics-v1.json) records the
independent standard-library TOML parse: removing exactly the owned
rmq_packed_bitvector_validate target makes the complete parsed object equal to
the governance blob. That target has only its expected name and root. The
691-byte hash remains unchanged after applying the attribute. An attribute
alone does not establish that Git's index now stores those bytes.

## Required committed-candidate check

[check_checkout_bytes.ps1](check_checkout_bytes.ps1) requires the exact current
commit, a fresh stage name and one or more passing retained replay records.
Pass the final public summary, main and validation selector records, and
machine/exception records to cover every actual replay dependency. The runner:

1. Requires all protected source paths, the attributes and manifest to be
   clean, including untracked files; per-command exclusions prevent a user
   global ignore file from hiding an omitted artifact.
2. Reads actual Git blob IDs for every committed protected file, requiring a
   nonempty set, named mandatory artifacts and binary gzip evidence.
3. Creates a separate shallow local clone without local object sharing and
   checks out the exact commit with core.autocrlf=true. It never renormalizes,
   rewrites or deletes the original source or the isolated checkout.
4. Compares raw source and fresh-checkout Git blob identities and SHA256
   values for every protected file. It separately compares every replay's
   retained dependency hash, including imported files outside these scopes.
5. Requires the frozen matrix's exact known hash and a clean fresh checkout,
   then writes the exact paths/counts, identities and bounded Git outcomes.

Git stdout is parsed independently of recorded stderr diagnostics. SHA-1 blob
identity uses Git's actual NUL-terminated blob header and raw bytes; binary
content never passes through a text conversion. SHA256 supplies the replay
identity as a second comparison. The source/committed path checks and external
dependency comparison were added after independent read-only review.

[check_frozen_rows.ps1](check_frozen_rows.ps1) also independently reads the
frozen Git blob, checks all 30 ordered literal IDs and compares every entire
row's UTF-8 bytes without normalization. Its current records pass all 30 with
zero changed rows and the original complete-file hash. Final evidence must
retain the actual byte-round-trip result after staging and committing; the
prepared runner and these attribute declarations do not substitute for it.

## Staged whitespace and index correction

The first staged check found 303202 CR-at-EOL reports and 38 recorded final
blank lines. The diagnostic inventory is
[staged-whitespace-diagnostic-v1.json](commands/staged-whitespace-diagnostic-v1.json).
The coordinator independently checked all 38 paths and approved exactly
[CHECKOUT_WHITESPACE_PATCH.diff](CHECKOUT_WHITESPACE_PATCH.diff), SHA256
8ADDBDB7B260ACEB3712CE30D59E066A2144C01013164F4E52352F1D464B057E.
The applied rules recognize CRLF on the five protected groups and allow only
the recorded EOF blanks on seven exact artifact patterns; ordinary trailing
space and indentation checks remain enabled. The normal staged check then
passed without a command-level override. Earlier working-tree checks did not
cover these new staged files and are not presented as equivalent evidence.

The verbatim approval is retained in
[CHECKOUT_WHITESPACE_DISPOSITION.md.gz](CHECKOUT_WHITESPACE_DISPOSITION.md.gz).
Its decompressed 3517 bytes have SHA256 89358C85F25104EC65BCFCAC6B812F9F168774C73D756F751E87E25FB5C54B25; the archive SHA256 is
1E5B6C40E1D751154DE9BE02201FB0B26054A2DF69CFF54CF426C178ECF7D011. Compression preserves its own exact final newline bytes without
adding another whitespace exception. WDD-20260912-BV1-006 records the rationale.

[manifest-raw-staging-v1.json](commands/manifest-raw-staging-v1.json) verifies
that the manifest's staged raw blob is now
fa57dac01b0a2a3217fe359402ac88c88709d8dc and its 691 bytes/SHA256 are unchanged.
This deliberately corrects an old cached normalized index entry without
rewriting the working file. Committed and fresh-checkout equality are still
pending the candidate commit; no completed round trip is inferred here.
