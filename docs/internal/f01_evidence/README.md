# EG-CP-F01 campaign evidence — UNVETTED working artifacts

Preserved 2026-07-26 from the F01 header-schema campaign, at governed base
`1490c97`.

**These are not acceptance evidence.** They have not been reviewed
declaration-by-declaration by the coordinator, they are in no build target, and
no claim may cite them as established. They are kept because the campaign's
definitions live only here — `RMQ/` contains none of them — and a porting worker
should start here rather than re-derive.

Read `../E1_ENDGAME_F01_HEADER_SCHEMA_RESULT.md` first. It states the frozen
schema, the `K = 1` decision and its one open gap, two corrections to the
coordinator's own briefing, and three owner decisions the campaign raised.

Run one with:

    cd <the session worktree, which carries its own .lake build>
    lake env lean docs/internal/f01_evidence/<file>.lean

Files are prefixed by lane (`dpw_f01_*` width, `zqh*` header definition, `zkd*`
K decision, `qvz*` verification, `vf01_*` adjudication, and others).
