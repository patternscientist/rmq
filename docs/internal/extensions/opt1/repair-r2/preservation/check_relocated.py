"""OPT-1-R2 relocation-aware preservation run and unchanged-checker controlled difference.

Use check_relocated.ps1: its owned supervisor covers this process and every Git
descendant. This module imports the byte-identical OPT-1-R1 checker
(repair-r1/preservation/check.py) and calls its own comparison functions, Git
capture class and 17-case control registry; nothing in that checker is copied
or edited.

--mode relocated applies the coordinator amendment REQ-OPT-R2-PRESERVATION-
AMENDMENT. The manifest mapping (each archive replaced by its original path
carrying the blob id recomputed from the decompressed archive bytes), the
new files under repair-r2/ and the append-only attributes entry are the only
admitted differences. After mapping, the candidate protected map must equal
the protected map of 4cc9501 exactly, and every OPT-1-R1 check is reproduced.

--mode controlled-difference runs the unchanged R1 comparisons without the
mapping and records every difference they report, neutralizing only the
reported paths to reach the next fail-fast category. It passes only when the
complete difference equals the enumerated admitted set; its status is never
PASS, because an unmapped protected difference is not preservation.
"""
from __future__ import annotations

import argparse
import contextlib
import copy
import importlib.util
import io
import json
from pathlib import Path
import re
import sys
import time

sys.dont_write_bytecode = True

R2_BASE = "4cc95012a31cda9459d06d87b3371c8c172bb973"
HISTORY = "docs/internal/extensions/opt1/"
R1_CHECKER = HISTORY + "repair-r1/preservation/check.py"
R1_REGISTRY = HISTORY + "repair-r1/preservation/registry.json"
R2_ROOT = HISTORY + "repair-r2/"
VERIFIER = R2_ROOT + "verify_receipt_archives.py"
MANIFEST = R2_ROOT + "RECEIPT_ARCHIVES.json"
ATTRIBUTES = HISTORY + ".gitattributes"
CONTROL_REGISTRY = "relocation_controls.json"
CONTROL_VERSION = "opt1-r2-relocation-controls-v1"
CONTROL_IDS = (
    "X01-EXACT-RELOCATION", "X02-UNENUMERATED-DELETION", "X03-OTHER-BLOB-CHANGED",
    "X04-ADDITION-OUTSIDE-R2", "X05-ORIGINAL-BESIDE-ARCHIVE", "X06-ARCHIVE-WRONG-BYTES",
    "X07-ATTRIBUTES-NOT-APPEND-ONLY", "X08-ARCHIVE-MISSING", "X09-PACKED-MODE-CHANGED",
    "X10-ADDITION-UNDER-REPAIR-R1",
)


def load(repo: Path, rel: str, name: str):
    spec = importlib.util.spec_from_file_location(name, repo / rel)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class Relocation:
    """The admitted difference between the 4cc9501 protected map and a candidate map."""

    def __init__(self, r1, verifier, manifest: dict, r2_base: dict, base_attributes: bytes):
        self.r1, self.v, self.manifest = r1, verifier, manifest
        self.r2_base, self.base_attributes = r2_base, base_attributes
        lines = manifest["attributes"]["appendedLines"]
        self.attribute_suffix = ("\n".join(lines) + "\n").encode("utf-8")

    def apply(self, candidate: dict, read_blob, attributes: bytes) -> tuple[dict, dict]:
        require = self.r1.require
        mapped = dict(candidate)
        record = {"relocations": [], "repair_r2_additions": [], "attributes": None}
        for entry in self.manifest["archives"]:
            original, archive = entry["originalPath"], entry["archivePath"]
            require(original not in candidate, "RELOCATION_ORIGINAL_PRESENT", original)
            require(archive in candidate, "RELOCATION_ARCHIVE_MISSING", archive)
            base_entry = self.r2_base.get(original)
            require(base_entry is not None, "RELOCATION_BASE_MISSING", original)
            mode, kind, oid = candidate[archive]
            require(kind == "blob" and mode == base_entry[0], "RELOCATION_MODE", {"archive": archive, "mode": mode})
            try:
                recovered = self.v.decompress_single_member(read_blob(oid))
            except Exception as exc:  # any undecodable archive is a rejected relocation
                raise self.r1.Rejected("RELOCATION_BYTES", {"archive": archive, "error": str(exc)}) from exc
            recovered_oid = self.v.git_blob_id(recovered)
            require(recovered_oid == base_entry[2] == entry["baseBlobId"], "RELOCATION_BYTES",
                    {"archive": archive, "recovered": recovered_oid, "base": base_entry[2]})
            del mapped[archive]
            mapped[original] = base_entry
            record["relocations"].append({
                "original": original, "archive": archive, "archive_blob": oid, "archive_mode": mode,
                "recovered_blob": recovered_oid, "recovered_bytes": len(recovered),
                "recovered_sha256": self.r1.sha(recovered), "base_blob": base_entry[2]})
        for path in sorted(candidate):
            if path.startswith(R2_ROOT):
                require(path not in self.r2_base, "REPAIR_R2_NOT_NEW", path)
                del mapped[path]
                record["repair_r2_additions"].append({"path": path, "mode": candidate[path][0], "blob": candidate[path][2]})
        require(ATTRIBUTES in candidate, "GITATTRIBUTES_APPEND", "attributes blob missing")
        require(attributes == self.base_attributes + self.attribute_suffix, "GITATTRIBUTES_APPEND",
                {"candidate_sha256": self.r1.sha(attributes), "expected_sha256": self.r1.sha(self.base_attributes + self.attribute_suffix)})
        require(candidate[ATTRIBUTES][0] == self.r2_base[ATTRIBUTES][0], "GITATTRIBUTES_APPEND", "attributes mode changed")
        mapped[ATTRIBUTES] = self.r2_base[ATTRIBUTES]
        record["attributes"] = {"candidate_blob": candidate[ATTRIBUTES][2], "base_blob": self.r2_base[ATTRIBUTES][2],
                                "appended_bytes": len(self.attribute_suffix), "appended_sha256": self.r1.sha(self.attribute_suffix)}
        return mapped, record

    def identity(self, mapped: dict) -> dict:
        missing = sorted(set(self.r2_base) - set(mapped))
        extra = sorted(set(mapped) - set(self.r2_base))
        changed = sorted(p for p in set(mapped) & set(self.r2_base) if mapped[p] != self.r2_base[p])
        self.r1.require(not missing and not extra and not changed, "AMENDMENT_IDENTITY",
                        {"missing": missing, "extra": extra, "changed": changed})
        return {"protected_entries": len(mapped), "equal_to": R2_BASE}


R2_MATRIX = R2_ROOT + "ACCEPTANCE_MATRIX.md"
R2_IDS = ("REQ-OPT-R2-SELFTEST", "REQ-OPT-R2-HISTORY", "REQ-OPT-R2-PRESERVATION-AMENDMENT",
          "CHK-OPT-R2-VERIFICATION")


def matrix_rows(r1, data: bytes, label: str) -> dict:
    """Row-content byte strings of the R2 matrix, keyed by stable ID, LF/CRLF excluded."""
    result: dict[str, bytes] = {}
    r1.strict_text(data, label)
    for line in data.split(b"\n"):
        content = line[:-1] if line.endswith(b"\r") else line
        match = re.match(rb"^\| `((?:REQ|CHK|REPLAY|INV)-[^`]+)` \|", content)
        if not match:
            continue
        key = r1.strict_text(match.group(1), label)
        r1.require(key not in result, "R2_ROW_DUPLICATE", {"label": label, "id": key})
        result[key] = content
    r1.require(all(rid in result for rid in R2_IDS), "R2_ROW_IDS",
               {"label": label, "missing": [rid for rid in R2_IDS if rid not in result]})
    return result


R1_REQUIREMENT_FREEZE = "f7cf20da8ae52c1f8295e5cedd4326bb8d44cbb3"


def r1_requirement_cells(r1, data: bytes, label: str) -> dict:
    """Second cell of each OPT-1-R1 repair row; rows must be unambiguous 8-cell rows."""
    result = {}
    for line in data.split(b"\n"):
        content = line[:-1] if line.endswith(b"\r") else line
        for rid in r1.REPAIR_IDS:
            if content.startswith(("| `" + rid + "` |").encode("ascii")):
                r1.require(rid not in result, "R1_REQUIREMENT_ROW_DUPLICATE", {"label": label, "id": rid})
                r1.require(content.count(b"|") == 9 and b"\\|" not in content, "R1_REQUIREMENT_ROW_SHAPE",
                           {"label": label, "id": rid})
                result[rid] = content.split(b" | ")[1]
    r1.require(set(result) == set(r1.REPAIR_IDS), "R1_REQUIREMENT_ROW_IDS", {"label": label, "found": sorted(result)})
    return result


def index_map(r1, raw: bytes) -> dict:
    result = {}
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        header, path = entry.split(b"\t", 1)
        mode, oid, stage = header.decode("ascii").split()
        name = r1.strict_text(path, "index")
        r1.require(stage == "0" and name not in result, "INDEX_STAGE", name)
        result[name] = (mode, "blob", oid)
    return result


def run_relocation_controls(r1, relocation: Relocation, candidate: dict, read_blob, attributes: bytes,
                            here: Path) -> list[dict]:
    registry = r1.read_json((here / CONTROL_REGISTRY).read_bytes(), CONTROL_REGISTRY)
    r1.require(registry["version"] == CONTROL_VERSION, "CONTROL_VERSION", registry["version"])
    r1.require(tuple(c["id"] for c in registry["cases"]) == CONTROL_IDS, "CONTROL_REGISTRY", registry)
    expected = {c["id"]: c for c in registry["cases"]}
    results = []
    first = relocation.manifest["archives"][0]
    forged_bytes = relocation.v.decompress_single_member(read_blob(candidate[first["archivePath"]][2]))
    forged_bytes = forged_bytes[:-2] + (b"X" if forged_bytes[-2:-1] != b"X" else b"Y") + forged_bytes[-1:]
    import gzip
    forged_archive = gzip.compress(forged_bytes, compresslevel=9, mtime=0)
    forged_oid = relocation.v.git_blob_id(forged_archive)

    def blob_with_forgery(oid):
        return forged_archive if oid == forged_oid else read_blob(oid)

    fields = "docs/internal/extensions/opt1/certificate-replay/FIELDS.json"
    packed = sorted(p for p in candidate if p.startswith(r1.PACKED))[0]

    def attempt(key, cand, attrs=attributes, reader=read_blob):
        exp = expected[key]
        try:
            mapped, _ = relocation.apply(cand, reader, attrs)
            relocation.identity(mapped)
            actual, code = "ACCEPT", None
        except r1.Rejected as exc:
            actual, code = "REJECT", exc.code
        r1.require(actual == exp["verdict"] and code == exp["code"], "RELOCATION_CONTROL_VERDICT",
                   {"id": key, "actual": actual, "code": code, "expected": exp})
        results.append({"id": key, "verdict": actual, "code": code, "passed": True})

    attempt(CONTROL_IDS[0], dict(candidate))
    c = dict(candidate); del c[fields]
    attempt(CONTROL_IDS[1], c)
    c = dict(candidate); c[fields] = (c[fields][0], "blob", "0" * 40)
    attempt(CONTROL_IDS[2], c)
    c = dict(candidate); c[HISTORY + "unauthorized-r2-control.json"] = ("100644", "blob", "0" * 40)
    attempt(CONTROL_IDS[3], c)
    c = dict(candidate); c[first["originalPath"]] = relocation.r2_base[first["originalPath"]]
    attempt(CONTROL_IDS[4], c)
    c = dict(candidate); c[first["archivePath"]] = (c[first["archivePath"]][0], "blob", forged_oid)
    attempt(CONTROL_IDS[5], c, reader=blob_with_forgery)
    attempt(CONTROL_IDS[6], dict(candidate), attrs=b"#" + attributes)
    c = dict(candidate); del c[first["archivePath"]]
    attempt(CONTROL_IDS[7], c)
    c = dict(candidate); c[packed] = ("100755" if c[packed][0] != "100755" else "100644", *c[packed][1:])
    attempt(CONTROL_IDS[8], c)
    c = dict(candidate); c[r1.REPAIR_ROOT + "r2-control-addition.txt"] = ("100644", "blob", "0" * 40)
    attempt(CONTROL_IDS[9], c)
    r1.require(tuple(r["id"] for r in results) == CONTROL_IDS, "RELOCATION_CONTROL_EXECUTED", results)
    return results


def neutralize_until_accept(r1, baseline: dict, candidate: dict, surface: str) -> list[dict]:
    """Call the unchanged check_protected repeatedly, restoring only the paths it reports."""
    work = dict(candidate)
    found = []
    for _ in range(8):
        try:
            r1.check_protected(baseline, work)
            return found
        except r1.Rejected as exc:
            paths = list(exc.detail)
            found.append({"surface": surface, "code": exc.code, "paths": paths})
            for path in paths:
                if exc.code == "PROTECTED_ADDITION":
                    del work[path]
                else:
                    work[path] = baseline[path]
    raise r1.Rejected("DIFFERENCE_NOT_EXHAUSTED", {"surface": surface, "found": found})


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate-ref", required=True)
    parser.add_argument("--repo-root", required=True, type=Path)
    parser.add_argument("--output-directory", required=True, type=Path)
    parser.add_argument("--mode", required=True, choices=("relocated", "controlled-difference"))
    parser.add_argument("--freeze-ref", default=None,
                        help="commit that froze the R2 matrix; its four R2 requirement rows must be byte-identical "
                             "in the candidate")
    args = parser.parse_args()
    repo, output = args.repo_root.resolve(), args.output_directory.resolve()
    output.mkdir(parents=True, exist_ok=True)
    here = Path(__file__).resolve().parent
    r1 = load(repo, R1_CHECKER, "opt1_r1_preservation_check")
    v = load(repo, VERIFIER, "opt1_r2_verify_receipt_archives")
    report = {"version": "opt1-r2-preservation-v1", "mode": args.mode, "r2_base": R2_BASE, "r1_base": r1.BASE,
              "freeze": r1.FREEZE, "governance": r1.GOVERNANCE, "candidate": args.candidate_ref,
              "repo_root": str(repo), "status": "INCOMPLETE",
              "r1_checker": R1_CHECKER, "r1_checker_import": "importlib from the live byte-identical file"}
    git = r1.Git(repo, output / "git")
    before = index_before = None
    watched: list[str] = []
    started = time.monotonic()
    try:
        r1.require(re.fullmatch(r"[0-9a-f]{40}", args.candidate_ref) is not None, "CANDIDATE_REF", args.candidate_ref)
        cand = args.candidate_ref
        resolved = r1.strict_text(git.run(["rev-parse", "--verify", cand + "^{commit}"]), "candidate").strip()
        r1.require(resolved == cand, "CANDIDATE_REF", resolved)
        for ancestor in (r1.GOVERNANCE, r1.BASE, R2_BASE):
            git.run(["merge-base", "--is-ancestor", ancestor, cand])
        # The R1 checker and its registry must be the unchanged 4cc9501 blobs, live and at the candidate.
        identity = {}
        for rel in (R1_CHECKER, R1_REGISTRY):
            live = (repo / rel).read_bytes()
            base_oid = r1.strict_text(git.run(["rev-parse", R2_BASE + ":" + rel]), rel).strip()
            cand_oid = r1.strict_text(git.run(["rev-parse", cand + ":" + rel]), rel).strip()
            r1.require(v.git_blob_id(live) == base_oid == cand_oid, "R1_CHECKER_CHANGED", rel)
            identity[rel] = {"blob": base_oid, "live_sha256": r1.sha(live)}
        report["r1_checker_identity"] = identity

        baseline = git.tree(r1.BASE)
        r1.require(sum(p.startswith(r1.OPTIMIZATION) for p in baseline) == 12, "BASE_OPTIMIZATION_COUNT", None)
        r1.require(sum(p.startswith(r1.PACKED) for p in baseline) == 55, "BASE_PACKED_COUNT", None)
        r1.require(sum(p.startswith(r1.HISTORY) for p in baseline) == 439, "BASE_HISTORY_COUNT", None)
        r1.require(all(p in baseline for p in r1.AXIOM_FILES + (r1.VALIDATOR,)), "BASE_REQUIRED_PATHS", None)
        r2_base = git.tree(R2_BASE)
        candidate = git.tree(cand)
        report["protected_counts"] = {"r1_baseline": len(baseline), "r2_base": len(r2_base), "candidate": len(candidate)}

        manifest = r1.read_json(git.blob(cand, MANIFEST), MANIFEST)
        shape = v.Reporter()
        with contextlib.redirect_stdout(io.StringIO()) as shape_out:
            shape_ok = v.validate_manifest_shape(manifest, shape)
        r1.require(shape_ok, "MANIFEST_SCHEMA", shape_out.getvalue())
        verifier_out = io.StringIO()
        with contextlib.redirect_stdout(verifier_out):
            verifier_exit = v.main(["--committed", cand, "--tree", str(repo), "--repo", str(repo)])
        report["receipt_archive_verifier"] = {"exit": verifier_exit, "stdout": verifier_out.getvalue().splitlines()}
        r1.require(verifier_exit == 0, "RECEIPT_ARCHIVES", verifier_out.getvalue())

        def read_blob(oid):
            return git.run(["cat-file", "blob", oid])

        base_attributes = git.blob(R2_BASE, ATTRIBUTES)
        cand_attributes = git.blob(cand, ATTRIBUTES)
        relocation = Relocation(r1, v, manifest, r2_base, base_attributes)
        relocated_originals = {e["originalPath"]: e["archivePath"] for e in manifest["archives"]}

        if args.mode == "controlled-difference":
            enumerated = {
                "PROTECTED_OMISSION": sorted(relocated_originals),
                "PROTECTED_ADDITION": sorted(set(relocated_originals.values()) |
                                             {p for p in candidate if p.startswith(R2_ROOT)}),
                "PROTECTED_IDENTITY": [ATTRIBUTES],
            }
            differences = neutralize_until_accept(r1, baseline, candidate, "candidate-tree")
            live_missing = []
            for name in sorted(baseline) + [r1.NEW_MATRIX, r1.PROOF_IDENTITY]:
                try:
                    r1.source_snapshot(repo, [name])
                except r1.Rejected as exc:
                    live_missing.append({"code": exc.code, "path": exc.detail})
            index_differences = neutralize_until_accept(
                r1, baseline, index_map(r1, git.run(["ls-files", "--stage", "-z", "--", *r1.PROTECTED_SCOPES])), "index")
            report["unchanged_checker_differences"] = {"candidate_tree": differences, "index": index_differences,
                                                       "live_snapshot": live_missing}
            report["enumerated_admitted_difference"] = enumerated
            found = {}
            for item in differences:
                found.setdefault(item["code"], set()).update(item["paths"])
            found = {k: sorted(s) for k, s in found.items()}
            index_found = {}
            for item in index_differences:
                index_found.setdefault(item["code"], set()).update(item["paths"])
            index_found = {k: sorted(s) for k, s in index_found.items()}
            live_expected = [{"code": "LIVE_PROTECTED_MISSING", "path": p} for p in sorted(relocated_originals)]
            report["difference_equals_enumeration"] = {
                "candidate_tree": found == enumerated, "index": index_found == enumerated,
                "live_snapshot": live_missing == live_expected}
            r1.require(found == enumerated and index_found == enumerated and live_missing == live_expected,
                       "UNEXPECTED_DIFFERENCE", {"candidate_tree": found, "index": index_found, "live": live_missing})
            # The frozen rows and field types are outside the admitted difference; the unchanged
            # functions must still accept them without any mapping.
            frozen = r1.rows(git.blob(r1.FREEZE, r1.OLD_MATRIX), r1.INHERITED_IDS, "freeze matrix")
            report["freeze_to_candidate_old"] = r1.compare_rows(
                frozen, r1.rows(git.blob(cand, r1.OLD_MATRIX), r1.INHERITED_IDS, "candidate old matrix"), "candidate old")
            report["freeze_to_candidate_repair"] = r1.compare_rows(
                frozen, r1.rows(git.blob(cand, r1.NEW_MATRIX), r1.INHERITED_IDS + r1.REPAIR_IDS, "candidate repair matrix"),
                "candidate repair")
            report["status"] = "EXPECTED_CONTROLLED_DIFFERENCE"
        else:
            watched = sorted(baseline) + [r1.NEW_MATRIX, r1.PROOF_IDENTITY]

            def snapshot():
                result = {}
                for name in watched:
                    if name in relocated_originals:
                        archive_path = repo / relocated_originals[name]
                        r1.require(archive_path.is_file() and not (repo / name).exists(), "LIVE_RELOCATION", name)
                        archive = archive_path.read_bytes()
                        recovered = v.decompress_single_member(archive)
                        result[name] = {"bytes": len(recovered), "sha256": r1.sha(recovered),
                                        "relocated_from": relocated_originals[name], "archive_sha256": r1.sha(archive)}
                    else:
                        result.update(r1.source_snapshot(repo, [name]))
                return result

            before = snapshot()
            report["live_before"] = before
            index_before = git.run(["ls-files", "--stage", "-z", "--", *r1.PROTECTED_SCOPES])
            report["index_before_sha256"] = r1.sha(index_before)

            mapped, record = relocation.apply(candidate, read_blob, cand_attributes)
            report["relocation"] = record
            report["amendment_identity"] = relocation.identity(mapped)
            report["protected_identity"] = r1.check_protected(baseline, mapped)

            frozen = r1.rows(git.blob(r1.FREEZE, r1.OLD_MATRIX), r1.INHERITED_IDS, "freeze matrix")
            baseline_blob = git.blob(r1.BASE, r1.OLD_MATRIX)
            report["freeze_to_base"] = r1.compare_rows(frozen, r1.rows(baseline_blob, r1.INHERITED_IDS, "base matrix"), "base")
            old_live, new_live = (repo / r1.OLD_MATRIX).read_bytes(), (repo / r1.NEW_MATRIX).read_bytes()
            report["freeze_to_live_old"] = r1.compare_rows(frozen, r1.rows(old_live, r1.INHERITED_IDS, "live old matrix"), "live old")
            report["freeze_to_live_repair"] = r1.compare_rows(
                frozen, r1.rows(new_live, r1.INHERITED_IDS + r1.REPAIR_IDS, "live repair matrix"), "live repair")
            proof = (repo / r1.PROOF_IDENTITY).read_bytes()
            fields = r1.read_json(git.blob(r1.BASE, r1.FIELDS), r1.FIELDS)
            consumers = git.blob(r1.BASE, r1.OPTIMIZATION + "Consumers.lean")
            report["field_types"] = r1.check_field_inventory(fields, proof, consumers)
            roots = r1.read_json(git.blob(r1.BASE, r1.ROOTS), r1.ROOTS)
            r1.require(len(roots["Names"]) == 93 and len(set(roots["Names"])) == 93, "AXIOM_ROOTS", None)
            report["axiom_root_count"] = 93
            report["r1_controls"] = r1.run_controls(frozen, old_live, new_live, baseline, fields, proof, consumers)
            report["r1_expected_controls"] = list(r1.CONTROL_IDS)
            report["r1_executed_controls"] = [c["id"] for c in report["r1_controls"]]

            candidate_old = git.blob(cand, r1.OLD_MATRIX)
            r1.require(candidate_old == baseline_blob, "OLD_MATRIX_BLOB_BYTES", r1.OLD_MATRIX)
            report["old_matrix_entire_blob_equal"] = True
            report["freeze_to_candidate_old"] = r1.compare_rows(
                frozen, r1.rows(candidate_old, r1.INHERITED_IDS, "candidate old matrix"), "candidate old")
            candidate_new = git.blob(cand, r1.NEW_MATRIX)
            candidate_rows = r1.rows(candidate_new, r1.INHERITED_IDS + r1.REPAIR_IDS, "candidate repair matrix")
            report["freeze_to_candidate_repair"] = r1.compare_rows(frozen, candidate_rows, "candidate repair")
            live_rows = r1.rows(new_live, r1.INHERITED_IDS + r1.REPAIR_IDS, "live repair matrix")
            r1.require(all(candidate_rows[k] == live_rows[k] for k in r1.INHERITED_IDS + r1.REPAIR_IDS),
                       "CANDIDATE_LIVE_ROW_BYTES", "candidate/live repair rows differ")
            report["candidate_field_types"] = r1.check_field_inventory(fields, git.blob(cand, r1.PROOF_IDENTITY), consumers)
            git.run(["merge-base", "--is-ancestor", R1_REQUIREMENT_FREEZE, cand])
            frozen_cells = r1_requirement_cells(r1, git.blob(R1_REQUIREMENT_FREEZE, r1.NEW_MATRIX), "R1 matrix at f7cf20d")
            candidate_cells = r1_requirement_cells(r1, candidate_new, "R1 matrix at candidate")
            live_cells = r1_requirement_cells(r1, new_live, "live R1 matrix")
            changed_cells = [rid for rid in r1.REPAIR_IDS
                             if not (frozen_cells[rid] == candidate_cells[rid] == live_cells[rid])]
            r1.require(not changed_cells, "R1_REQUIREMENT_CELL_BYTES", changed_cells)
            report["r1_requirement_cells"] = [{"id": rid, "freeze": R1_REQUIREMENT_FREEZE, "bytes": len(frozen_cells[rid]),
                                               "sha256": r1.sha(frozen_cells[rid]), "byte_equal": True}
                                              for rid in r1.REPAIR_IDS]

            dirty = git.run(["diff", "--no-ext-diff", "--name-only", "-z", cand, "--", *r1.PROTECTED_SCOPES])
            dirty_paths = [r1.strict_text(p, "protected diff") for p in dirty.split(b"\0") if p]
            r1.require(not [p for p in dirty_paths if not p.startswith(r1.REPAIR_ROOT)], "LIVE_PROTECTED_DIFF", dirty_paths)
            r1.require(not dirty_paths, "LIVE_PROTECTED_DIFF_ANY", dirty_paths)
            untracked = git.run(["ls-files", "--others", "--exclude-standard", "-z", "--", *r1.PROTECTED_SCOPES])
            untracked_paths = [r1.strict_text(p, "untracked protected") for p in untracked.split(b"\0") if p]
            r1.require(not [p for p in untracked_paths if not p.startswith(r1.REPAIR_ROOT)], "LIVE_PROTECTED_ADDITION", untracked_paths)
            r1.require(not untracked_paths, "LIVE_PROTECTED_ADDITION_ANY", untracked_paths)
            index_live = index_map(r1, git.run(["ls-files", "--stage", "-z", "--", *r1.PROTECTED_SCOPES]))
            mapped_index, index_record = relocation.apply(index_live, read_blob, cand_attributes)
            report["index_amendment_identity"] = relocation.identity(mapped_index)
            report["index_protected_identity"] = r1.check_protected(baseline, mapped_index)
            report["index_relocation_equal_to_candidate"] = index_record == record
            r1.require(index_record == record, "INDEX_RELOCATION", "index relocation record differs from the candidate")
            report["relocation_controls"] = run_relocation_controls(r1, relocation, candidate, read_blob, cand_attributes, here)
            if args.freeze_ref is not None:
                r1.require(re.fullmatch(r"[0-9a-f]{40}", args.freeze_ref) is not None, "FREEZE_REF", args.freeze_ref)
                git.run(["merge-base", "--is-ancestor", args.freeze_ref, cand])
                frozen_r2 = matrix_rows(r1, git.blob(args.freeze_ref, R2_MATRIX), "R2 matrix at freeze")
                candidate_r2 = matrix_rows(r1, git.blob(cand, R2_MATRIX), "R2 matrix at candidate")
                changed_r2 = [rid for rid in R2_IDS if frozen_r2[rid] != candidate_r2[rid]]
                r1.require(not changed_r2, "R2_ROW_BYTES", changed_r2)
                report["r2_matrix_rows"] = {"freeze_ref": args.freeze_ref, "rows": [
                    {"id": rid, "bytes": len(frozen_r2[rid]), "sha256": r1.sha(frozen_r2[rid]), "byte_equal": True}
                    for rid in R2_IDS]}
            else:
                report["r2_matrix_rows"] = "not checked (no --freeze-ref)"
            report["candidate_receipt_scope"] = ("Committed candidate Git blobs with the enumerated relocation applied, "
                                                 "plus live row, field-type, index and restoration checks")
            report["status"] = "PASS"
    except Exception as exc:
        report["status"] = "FAIL"
        report["failure"] = {"code": getattr(exc, "code", type(exc).__name__), "detail": str(exc)[:4000]}
    finally:
        if before is not None:
            try:
                after = snapshot()
                report["live_after"] = after
                report["live_bytes_unchanged"] = before == after
                if before != after:
                    report["status"] = "FAIL"
                    report["restoration_failure"] = [n for n in before if before[n] != after.get(n)]
            except Exception as exc:
                report["status"] = "FAIL"
                report["restoration_failure"] = str(exc)
        if index_before is not None:
            try:
                index_after = git.run(["ls-files", "--stage", "-z", "--", *r1.PROTECTED_SCOPES])
                report["index_after_sha256"] = r1.sha(index_after)
                report["index_bytes_unchanged"] = index_before == index_after
                if index_before != index_after:
                    report["status"] = "FAIL"
            except Exception as exc:
                report["status"] = "FAIL"
                report["index_restoration_failure"] = str(exc)
        report["git_processes"] = git.receipts
        report["duration_seconds"] = time.monotonic() - started
        report["checker_sha256"] = r1.sha(Path(__file__).read_bytes())
        report["relocation_registry_sha256"] = r1.sha((here / CONTROL_REGISTRY).read_bytes())
        (output / "result.json").write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    counts = (f"r1-controls={len(report.get('r1_controls', []))}/{len(r1.CONTROL_IDS)} "
              f"relocation-controls={len(report.get('relocation_controls', []))}/{len(CONTROL_IDS)}")
    print(f"OPT1-R2-PRESERVATION {report['status']} mode={args.mode} {counts}")
    if report["status"] not in ("PASS", "EXPECTED_CONTROLLED_DIFFERENCE"):
        print(json.dumps(report.get("failure") or report.get("restoration_failure"), ensure_ascii=False), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
