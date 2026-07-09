# Internal Audit Reports

This directory stores durable reports from external auditors and coordinator
audit dispositions that materially affect roadmap, theorem-surface, artifact,
or workflow decisions.

Reports in this directory are process evidence. They can explain what was
checked, which findings were accepted or rejected, and what work was launched
next. They are not proof of mathematical, cost-model, or executable claims.
Those claims still require checked Lean source, reproducible commands, theorem
maps, and artifact evidence.

Use filenames of the form:

```text
YYYY-MM-DD_HANDLE_target.md
```

Each stored report should include:

- target branch, commit, base, and scope;
- auditor handle and whether the report came from an external chat or local
  coordinator run;
- verdict and severity-ordered findings;
- verification commands run or skipped;
- coordinator disposition, including accepted findings, rejected findings, and
  next action.
