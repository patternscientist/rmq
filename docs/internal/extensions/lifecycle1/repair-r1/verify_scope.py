#!/usr/bin/env python3
"""Verify raw launch-file preservation and exact-base Git scope without edits.

The receipt separates raw initial working bytes, Git's source comparison, and
the older contract checker's exact raw-byte pins. A preserved CRLF checkout is
not silently converted to, or certified as equal to, a frozen LF Git blob.
Only the requested JSON receipt is written. No restoration is attempted.
Use --check to emit the same full verification receipt to stdout without any
file write; the committed SCOPE_VERIFICATION.json is not refreshed in that mode.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import time


BASE = "12bd7f0fc2c87f2c9bdef3825bd92477e48e3433"
GOVERNANCE = "7b227c49ef2ec044b702126cc41c9add847eed01"
REPAIR = "docs/internal/extensions/lifecycle1/repair-r1/"
MANIFEST = REPAIR + "INITIAL_WORKING_FILES.json"
MANIFEST_PIN = {"bytes": 692757, "sha256": "7568f90a8e594b79e707d0df575bb998feb5843e544c756b353764710decf806"}
EDITABLE = {"scripts/lifecycle_validator.ps1", "scripts/lifecycle_dependency_replay.ps1"}
APPEND_ONLY = {
    "docs/internal/WORKFLOW_DESIGN_DECISIONS.md",
    "docs/internal/extensions/lifecycle1/VERIFICATION_PLAN.md",
}
NEW_ADAPTER = "scripts/lifecycle_validator_environment.ps1"
ORIGINAL_FROZEN = "docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.frozen.md"
ORIGINAL_CONTRACT = "docs/internal/extensions/lifecycle1/CONTRACT_REQUIREMENTS.json"
ORIGINAL_ACTIVE = "docs/internal/extensions/lifecycle1/ACCEPTANCE_MATRIX.md"
ORIGINAL_RAW_PINS = {
    ORIGINAL_FROZEN: "8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7",
    ORIGINAL_CONTRACT: "5bd95d24b6cffaf9fb39abb2aa04cca9743aed7884b3f87d03d7428e6b9cd8eb",
}
EXECUTABLE = ".lake/build/bin/rmq_lifecycle_validate.exe"
EXECUTABLE_SHA = "4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c"
HELPER = "scripts/owned_process_tree.ps1"
HELPER_SHA = "6690ad4f9e3aee9596e53e89d3d242e4be59c0a04733bc50184ae35b292ff90e"
CANONICAL_SKILLS = ("rmq-audit-prompt", "rmq-coordinator", "rmq-proof-sprint")


def identity(data: bytes) -> dict:
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def map_identity(value: dict) -> dict:
    return identity(json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode("utf-8"))


def no_duplicate_keys(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def strict_json(data: bytes) -> dict:
    text = data.decode("utf-8", errors="strict")
    if text.startswith("\ufeff"):
        raise ValueError("unexpected UTF-8 BOM")
    return json.loads(text, object_pairs_hook=no_duplicate_keys)


def safe_relative(value: str) -> str:
    path = PurePosixPath(value)
    if path.is_absolute() or not value or ".." in path.parts or "\\" in value or str(path) != value:
        raise ValueError(f"unsafe or noncanonical repository path: {value!r}")
    return value


def git(root: Path, arguments: list[str], receipts: list[dict], acceptable: tuple = (0,)) -> bytes:
    command = ["git", *arguments]
    started = time.monotonic()
    try:
        result = subprocess.run(command, cwd=root, capture_output=True, check=False, timeout=30)
    except subprocess.TimeoutExpired as error:
        receipts.append({"command": command, "deadlineSeconds": 30, "timedOut": True,
                         "stdout": identity(error.stdout or b""), "stderr": identity(error.stderr or b"")})
        raise RuntimeError(f"bounded Git command timed out: {arguments[0]}") from error
    receipts.append({"command": command, "deadlineSeconds": 30, "timedOut": False,
                     "exitCode": result.returncode, "elapsedSeconds": round(time.monotonic() - started, 6),
                     "stdout": identity(result.stdout), "stderr": identity(result.stderr),
                     "stderrText": result.stderr.decode("utf-8", errors="replace")})
    if result.returncode not in acceptable:
        raise RuntimeError(f"Git command failed with exit {result.returncode}: {arguments[0]}")
    return result.stdout


def newline_profile(data: bytes) -> dict:
    return {"crlf": data.count(b"\r\n"), "lf": data.count(b"\n"), "bareCr": data.count(b"\r") - data.count(b"\r\n")}


def allowed_new(path: str) -> bool:
    return path.startswith(REPAIR) or path == NEW_ADAPTER


def verify(root: Path, output: Path | None, receipt: dict) -> None:
    calls = receipt["gitCommands"]
    baseline_bytes = (root / MANIFEST).read_bytes()
    if identity(baseline_bytes) != MANIFEST_PIN:
        raise ValueError("exact launch raw-file manifest identity changed")
    baseline = strict_json(baseline_bytes)
    if not isinstance(baseline, dict) or not baseline:
        raise ValueError("launch raw-file manifest is not a nonempty object")
    for path, pin in baseline.items():
        safe_relative(path)
        if set(pin) != {"bytes", "sha256"} or not isinstance(pin["bytes"], int) or pin["bytes"] < 0:
            raise ValueError(f"invalid launch identity for {path}")
    receipt["manifest"] = {"path": MANIFEST, **identity(baseline_bytes), "initialTrackedCount": len(baseline),
                           "initialRawBytes": sum(pin["bytes"] for pin in baseline.values())}
    receipt["head"] = git(root, ["rev-parse", "HEAD"], calls).decode("ascii").strip()
    receipt["branch"] = git(root, ["branch", "--show-current"], calls).decode("utf-8").strip()
    git(root, ["merge-base", "--is-ancestor", BASE, "HEAD"], calls)
    git(root, ["merge-base", "--is-ancestor", GOVERNANCE, "HEAD"], calls)
    tree_output = git(root, ["ls-tree", "-r", "-z", "--full-tree", BASE], calls)
    base_tree = {}
    for record in tree_output.split(b"\0"):
        if not record:
            continue
        descriptor, encoded_path = record.split(b"\t", 1)
        mode, kind, oid = descriptor.decode("ascii").split()
        path = safe_relative(encoded_path.decode("utf-8", errors="strict"))
        if path in base_tree or kind != "blob" or mode not in ("100644", "100755"):
            raise ValueError(f"unexpected or duplicate base tree entry: {path}")
        base_tree[path] = {"mode": mode, "oid": oid}
    base_paths = set(base_tree)
    manifest_paths = set(baseline)
    receipt["manifestExactBaseInventory"] = {
        "equal": manifest_paths == base_paths, "baseCount": len(base_paths),
        "missingManifestPaths": sorted(base_paths - manifest_paths), "unknownManifestPaths": sorted(manifest_paths - base_paths),
        "baseTreeEnumeration": identity(tree_output),
    }

    current = {}
    inaccessible = []
    for path in sorted(baseline):
        try:
            file = root / path
            if file.is_symlink() or not file.is_file():
                raise ValueError("not a regular, non-symlink file")
            current[path] = identity(file.read_bytes())
        except (OSError, ValueError) as error:
            inaccessible.append({"path": path, "error": str(error)})
    protected = sorted(manifest_paths - EDITABLE - APPEND_ONLY)
    protected_changes = [path for path in protected if current.get(path) != baseline[path]]
    all_raw_changed = [path for path in sorted(baseline) if current.get(path) != baseline[path]]
    initial_protected = {path: baseline[path] for path in protected}
    current_protected = {path: current.get(path) for path in protected}
    receipt["rawProtectedWorkingFiles"] = {
        "status": "PASS" if not protected_changes else "FAIL", "count": len(protected),
        "equalCount": len(protected) - len(protected_changes),
        "initialBytes": sum(baseline[path]["bytes"] for path in protected),
        "currentBytes": sum(current[path]["bytes"] for path in protected if path in current),
        "initialIdentityMap": map_identity(initial_protected), "currentIdentityMap": map_identity(current_protected),
        "changedPaths": protected_changes, "inaccessible": inaccessible,
    }
    receipt["rawInitiallyTrackedChangedPaths"] = all_raw_changed
    receipt["allowedProductionEdits"] = [
        {"path": path, "initial": baseline[path], "current": current.get(path),
         "exists": path in current, "changed": current.get(path) != baseline[path]}
        for path in sorted(EDITABLE)
    ]
    prefixes = []
    for path in sorted(APPEND_ONLY):
        raw = (root / path).read_bytes()
        length = baseline[path]["bytes"]
        prefix = identity(raw[:length])
        item = {"path": path, "initial": baseline[path], "current": identity(raw),
                "originalPrefix": prefix, "prefixEqual": len(raw) >= length and prefix == baseline[path],
                "appended": identity(raw[length:]) if len(raw) >= length else None}
        if path.endswith("/VERIFICATION_PLAN.md"):
            item["appendedText"] = raw[length:].decode("utf-8", errors="strict")
        prefixes.append(item)
    receipt["appendOnlyDocuments"] = prefixes

    # Git's registered worktree/index comparison is a separate observation.
    # It is not used to replace or normalize the raw comparisons above.
    diff_bytes = git(root, ["diff", "--name-status", "-z", "--no-renames", "--no-ext-diff", "--no-textconv", BASE, "--"], calls)
    diff_parts = diff_bytes.split(b"\0")
    if diff_parts[-1] != b"" or (len(diff_parts) - 1) % 2:
        raise ValueError("unexpected NUL-delimited Git name-status output")
    changes = []
    for index in range(0, len(diff_parts) - 1, 2):
        status = diff_parts[index].decode("ascii")
        path = safe_relative(diff_parts[index + 1].decode("utf-8", errors="strict"))
        accepted = (status == "M" and path in EDITABLE | APPEND_ONLY) or (status == "A" and allowed_new(path))
        changes.append({"path": path, "status": status, "allowed": accepted})
    untracked_bytes = git(root, ["ls-files", "--others", "--exclude-standard", "-z"], calls)
    untracked = sorted(safe_relative(value.decode("utf-8", errors="strict")) for value in untracked_bytes.split(b"\0") if value)
    new_paths = sorted(set(untracked) | {item["path"] for item in changes if item["status"] == "A"})
    illegal_new = [path for path in new_paths if not allowed_new(path)]
    illegal_changes = [item for item in changes if not item["allowed"]]
    protected_git_changed = sorted(item["path"] for item in changes if item["path"] in protected)
    receipt["gitBaseToWorking"] = {
        "status": "PASS" if not illegal_changes and not illegal_new else "FAIL",
        "comparison": "Git base-to-index/worktree diff; attributes remain in effect; no script byte normalization",
        "trackedChanges": changes, "protectedEqualCount": len(protected) - len(protected_git_changed),
        "protectedChangedPaths": protected_git_changed, "newPaths": new_paths,
        "illegalChanges": illegal_changes, "illegalNewPaths": illegal_new,
        "ignoredFiles": "Generated ignored build/cache/evidence files are excluded from trackable source scope.",
    }
    if output is not None:
        relative_output = output.resolve().relative_to(root).as_posix()
        receipt["selfReceipt"] = {"path": relative_output, "existedAtScan": output.exists(),
                                  "newPathAllowed": allowed_new(relative_output),
                                  "identity": "This receipt is written after scanning and cannot contain its own final hash."}
        if not allowed_new(relative_output):
            raise ValueError("scope receipt destination must be inside the assigned repair directory")
        receipt["exactChangedFileListIncludingReceipt"] = sorted(set(all_raw_changed) | set(new_paths) | {relative_output})
    else:
        receipt["exactChangedFileListIncludingReceipt"] = sorted(set(all_raw_changed) | set(new_paths))

    category_rules = {
        "canonicalProjectSkills": lambda path: path.startswith(".agents/skills/"),
        "allLeanSource": lambda path: path.endswith(".lean"),
        "originalLifecycleEvidence": lambda path: path.startswith("docs/internal/extensions/lifecycle1/"),
        "originalJsonRegistriesAndCases": lambda path: path.endswith(".json") and ("registry" in path.lower() or "cases" in path.lower()),
        "protectedScriptsPoliciesAndGates": lambda path: path.startswith("scripts/"),
        "nativeSources": lambda path: path.startswith("native/") or "/native/" in path,
        "buildToolchain": lambda path: path in {"lean-toolchain", "lakefile.toml", "lake-manifest.json"},
        "ownedProcessHelper": lambda path: path == HELPER,
    }
    categories = {}
    for label, predicate in category_rules.items():
        paths = [path for path in protected if predicate(path)]
        categories[label] = {"count": len(paths), "equalCount": sum(current.get(path) == baseline[path] for path in paths),
                             "initialBytes": sum(baseline[path]["bytes"] for path in paths),
                             "initialIdentityMap": map_identity({path: baseline[path] for path in paths}),
                             "currentIdentityMap": map_identity({path: current.get(path) for path in paths})}
    receipt["protectedCategoriesMayOverlap"] = categories
    skill_paths = [f".agents/skills/{name}/SKILL.md" for name in CANONICAL_SKILLS]
    skills_equal = all(path in baseline and current.get(path) == baseline[path] for path in skill_paths)
    receipt["canonicalSkillSet"] = {"names": list(CANONICAL_SKILLS), "allPresentAndRawUnchanged": skills_equal}
    helper_equal = current.get(HELPER, {}).get("sha256") == HELPER_SHA
    receipt["ownedHelper"] = {"path": HELPER, "requiredSha256": HELPER_SHA, "current": current.get(HELPER), "equal": helper_equal}

    start = strict_json((root / REPAIR / "START.json").read_bytes())
    if start["base"] != BASE or start["governance"] != GOVERNANCE:
        raise ValueError("launch metadata base/governance differs")
    tools = []
    for path, expected in start["shells"].items():
        try:
            observed = identity(Path(path).read_bytes())
            tools.append({"path": path, "expected": expected, "current": observed, "equal": expected == observed})
        except OSError as error:
            tools.append({"path": path, "expected": expected, "equal": False, "error": str(error)})
    binary = root / EXECUTABLE
    binary_identity = identity(binary.read_bytes()) if binary.is_file() else None
    tools.append({"path": EXECUTABLE, "requiredSha256": EXECUTABLE_SHA, "current": binary_identity,
                  "equal": binary_identity is not None and binary_identity["sha256"] == EXECUTABLE_SHA})
    receipt["runtimeAndExecutableRawPins"] = tools

    originals = []
    for path in (ORIGINAL_FROZEN, ORIGINAL_CONTRACT, ORIGINAL_ACTIVE):
        working = (root / path).read_bytes()
        blob = git(root, ["cat-file", "blob", f"{BASE}:{path}"], calls)
        required_sha = ORIGINAL_RAW_PINS.get(path)
        originals.append({"path": path, "initialWorking": baseline[path], "currentWorking": identity(working),
                          "rawInitialEqual": identity(working) == baseline[path], "baseGitBlob": identity(blob),
                          "rawWorkingEqualsBaseGitBlob": working == blob, "workingNewlines": newline_profile(working),
                          "baseGitNewlines": newline_profile(blob), "requiredOriginalRawSha256": required_sha,
                          "requiredRawPinSatisfied": identity(working)["sha256"] == required_sha if required_sha else None})
    original_pins_equal = all(item["requiredRawPinSatisfied"] is not False for item in originals)
    receipt["originalContractSerialization"] = {
        "status": "PASS" if original_pins_equal else "FAIL",
        "files": originals,
        "disposition": ("Required original raw pins satisfied." if original_pins_equal else
                        "Original working files remain equal to launch bytes, but inherited CRLF serialization differs from required original raw pins/Git blobs. No normalization or restoration was performed; coordinator direction is still required."),
    }
    scope_passed = (manifest_paths == base_paths and not inaccessible and not protected_changes and
                    all(item["prefixEqual"] for item in prefixes) and all(path in current for path in EDITABLE) and
                    not illegal_changes and not illegal_new and skills_equal and helper_equal and
                    all(item["equal"] for item in tools))
    receipt["scopeStatus"] = "PASS" if scope_passed else "FAIL"
    receipt["status"] = ("PASS" if scope_passed and original_pins_equal else
                         "INCOMPLETE_ORIGINAL_CONTRACT_SERIALIZATION" if scope_passed else "FAIL")
    receipt["limitations"] = [
        "Raw source preservation and path scope do not certify semantics of the two allowed script edits or new repair files.",
        "Append-only checks establish exact initial prefix preservation; review of appended content remains separate.",
        "Git source comparison is not a claim of raw Git-blob equality for CRLF working files.",
        "Shell/executable hashes establish file identity, not fresh compilation, runtime execution, or compiler provenance.",
        "This snapshot neither locks the worktree nor covers later edits; rerun on final submitted content.",
        "No source or installed tool was normalized, restored, overwritten, or deleted by this verifier.",
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--repository-root", type=Path, default=Path(__file__).resolve().parents[5])
    parser.add_argument("--check", action="store_true", help="read-only verification; full receipt to stdout, no receipt file write")
    args = parser.parse_args()
    root = args.repository_root.resolve()
    output = None if args.check else root / REPAIR / "SCOPE_VERIFICATION.json"
    # Keep the sole write fixed to this task's receipt, including on failure.
    # A rejected output path must never become a failure-report destination.
    if output is not None and (output.is_symlink() or not output.parent.resolve().is_relative_to(root)):
        parser.error("scope receipt must remain a regular file in the repository repair directory")
    started = time.monotonic()
    receipt = {"schema": "life1-r1-raw-scope-verification-v1", "base": BASE, "governance": GOVERNANCE,
               "repositoryRoot": str(root), "startedUtc": datetime.now(timezone.utc).isoformat(), "gitCommands": []}
    try:
        verify(root, output, receipt)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        receipt["status"] = "FAIL"
        receipt["error"] = {"type": type(error).__name__, "detail": str(error)}
    receipt["elapsedSeconds"] = round(time.monotonic() - started, 6)
    receipt["verifier"] = {"path": str(Path(__file__).resolve()), **identity(Path(__file__).read_bytes())}
    receipt["python"] = {"path": sys.executable, "version": sys.version, **identity(Path(sys.executable).read_bytes())}
    if args.check:
        receipt["executionMode"] = "read-only --check; full receipt emitted to stdout; no receipt file written"
        print(json.dumps(receipt, indent=2, ensure_ascii=True))
        return 0 if receipt["status"] == "PASS" else 1
    output.write_bytes((json.dumps(receipt, indent=2, ensure_ascii=True) + "\n").encode("utf-8"))
    print(json.dumps({"status": receipt["status"], "scopeStatus": receipt.get("scopeStatus"),
                      "receipt": str(output), "receiptIdentity": identity(output.read_bytes()),
                      "protectedCount": receipt.get("rawProtectedWorkingFiles", {}).get("count"),
                      "protectedEqualCount": receipt.get("rawProtectedWorkingFiles", {}).get("equalCount"),
                      "rawChangedPaths": receipt.get("rawInitiallyTrackedChangedPaths"),
                      "newPathCount": len(receipt.get("gitBaseToWorking", {}).get("newPaths", [])),
                      "originalContractSerialization": receipt.get("originalContractSerialization", {}).get("status"),
                      "error": receipt.get("error"), "elapsedSeconds": receipt["elapsedSeconds"]}, indent=2))
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
