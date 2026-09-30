"""Reproduce the source/tool/build identity packet without executing build tools.

Only read-only Git object queries are subprocesses (each bounded to 60 seconds).
Lean, Lake, PowerShell and the validator are hashed, never launched here.
The generator and its output are intentionally outside the identity set.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = "12bd7f0fc2c87f2c9bdef3825bd92477e48e3433"
PRODUCTION_FREEZE = "122a6bedb086d1de1df8dec167c890f887a72cc2"
FREEZE = "7c406b15bdc12333d323c92641ab6c6dad6af7a2"
PREFIX = "docs/internal/extensions/lifecycle1/"
REPAIR = PREFIX + "repair-r1/"
PRODUCTION_CHANGES = {
    "scripts/lifecycle_validator.ps1",
    "scripts/lifecycle_dependency_replay.ps1",
    "scripts/lifecycle_validator_environment.ps1",
}
PACKAGING_EXCLUSIONS = {
    REPAIR + "source_manifest.py", REPAIR + "SOURCE_FREEZE.json",
    REPAIR + "ACCEPTANCE_MATRIX.md", REPAIR + "SCOPE_VERIFICATION.json",
    REPAIR + "contract_verification.json", REPAIR + "REPORT.md",
    REPAIR + "collect_evidence.py", REPAIR + "FINAL_RECEIPTS.json",
    REPAIR + "VERIFICATION_PLAN.md",
    "docs/internal/WORKFLOW_DESIGN_DECISIONS.md",
    PREFIX + "VERIFICATION_PLAN.md",
}
PINNED_EXE = "4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c"
TOOLROOT = Path("C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def identity(path: Path) -> dict:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(block)
            digest.update(block)
    return {"path": path.as_posix(), "bytes": size, "sha256": digest.hexdigest()}


def relative_identity(name: str) -> dict:
    item = identity(ROOT / name)
    item["path"] = name
    return item


def read_json(path: Path) -> dict:
    return json.loads(path.read_bytes().decode("utf-8-sig"))


def git(*arguments: str, input_bytes: bytes | None = None) -> bytes:
    result = subprocess.run(
        ["git", "-c", "safe.directory=" + ROOT.as_posix(),
         "-c", "core.excludesFile=", *arguments],
        cwd=ROOT, input=input_bytes, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, timeout=60, check=True,
    )
    if result.stderr:
        raise RuntimeError("Git object query emitted stderr: " +
                           result.stderr.decode("utf-8", errors="strict"))
    return result.stdout


def tree(commit: str) -> dict[str, str]:
    entries = {}
    for entry in git("ls-tree", "-r", "-z", commit).split(b"\0"):
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        _, kind, oid = metadata.decode("ascii").split()
        if kind == "blob":
            entries[name.decode("utf-8", errors="strict")] = oid
    return entries


def read_blobs(oids: set[str]) -> dict[str, bytes]:
    ordered = sorted(oids)
    payload = git("cat-file", "--batch",
                  input_bytes=("".join(oid + "\n" for oid in ordered)).encode("ascii"))
    result = {}
    offset = 0
    for requested in ordered:
        header_end = payload.index(b"\n", offset)
        oid, kind, size_text = payload[offset:header_end].decode("ascii").split()
        if oid != requested or kind != "blob":
            raise ValueError("Exact Git blob response mismatch: " + requested)
        size = int(size_text)
        offset = header_end + 1
        result[oid] = payload[offset:offset + size]
        offset += size
        if payload[offset:offset + 1] != b"\n":
            raise ValueError("Git blob boundary mismatch")
        offset += 1
    if offset != len(payload):
        raise ValueError("Unexpected trailing Git blob data")
    return result


def blob_identity(oid: str | None, blobs: dict[str, bytes]) -> dict | None:
    if oid is None:
        return None
    contents = blobs[oid]
    return {"oid": oid, "bytes": len(contents), "sha256": sha(contents)}


def receipt(name: str, expected_exit: int) -> dict:
    directory = ROOT / ".lake/repair-r1/checks" / name
    document = read_json(directory / "result.json")
    result = document["result"]
    if result["ExitCode"] != expected_exit or result["TimedOut"] or result["OutputLimitExceeded"]:
        raise ValueError("Receipt has an unexpected ordinary/timeout/overflow result: " + name)
    if result["Ownership"] != "kill-on-close-job":
        raise ValueError("Receipt ownership differs: " + name)
    source_agreement = {}
    for path, recorded in document["sources"].items():
        actual = relative_identity(path)
        source_agreement[path] = actual["sha256"] == recorded.lower()
    if not all(source_agreement.values()):
        raise ValueError("Receipt source binding differs: " + name)
    files = [relative_identity((directory / leaf).relative_to(ROOT).as_posix())
             for leaf in ("result.json", "stdout.txt", "stderr.txt")]
    return {
        "name": name, "specification": document["spec"],
        "ordinaryExit": result["ExitCode"], "timedOut": result["TimedOut"],
        "outputLimitExceeded": result["OutputLimitExceeded"],
        "durationSeconds": result["DurationSeconds"],
        "deadlineSeconds": result["DeadlineSeconds"], "ownership": result["Ownership"],
        "terminatedIds": result["TerminatedIds"],
        "shell": document["shell"], "shellVersion": document["version"],
        "dotnetVersion": document["dotnet"],
        "stdoutReturnedLineCount": len(result["StandardOutput"]),
        "stderrReturnedLineCount": len(result["StandardError"]),
        "lastStdoutLine": (result["StandardOutput"] or [None])[-1],
        "recordedSourceCount": len(source_agreement),
        "allRecordedSourceHashesEqualCurrentBytes": all(source_agreement.values()),
        "files": files,
        "streamInterpretation": document["streamRepresentation"],
    }


def build_manifest() -> dict:
    base_tree, freeze_tree = tree(BASE), tree(FREEZE)
    production_tree = tree(PRODUCTION_FREEZE)
    for name in PRODUCTION_CHANGES:
        if production_tree[name] != freeze_tree[name]:
            raise ValueError("Production source changed after its separate freeze: " + name)
    historical_path = PREFIX + "SOURCE_MANIFEST.json"
    historical = read_json(ROOT / historical_path)
    historical_rows = {row["path"]: row for row in historical["files"]}
    initial = read_json(HERE / "INITIAL_WORKING_FILES.json")
    selected: dict[str, list[str]] = {}
    for name in sorted(freeze_tree):
        if name in PACKAGING_EXCLUSIONS:
            continue
        categories = []
        if name in historical_rows:
            categories.append("original-source-manifest")
        if name.startswith("scripts/"):
            categories.append("scripts-gates-registries-policies-consumers")
        if name.startswith(PREFIX) and not name.startswith(REPAIR):
            categories.append("original-lifecycle-evidence")
        if name.startswith(REPAIR):
            categories.append("frozen-repair-code-contract-or-input")
        if name.startswith(".agents/") or name == "AGENTS.md":
            categories.append("canonical-governance")
        if name.startswith(".github/") or name in {
                ".gitattributes", ".gitignore", "lakefile.toml",
                "lean-toolchain", "lake-manifest.json"}:
            categories.append("build-toolchain-attributes-ci")
        if name.startswith("docs/internal/") and any(
                word in name.lower() for word in ("policy", "allowlist", "preflight", "gate")):
            categories.append("governance-policy")
        if categories:
            selected[name] = categories
    if not historical_rows.keys() <= selected.keys():
        raise ValueError("An original source-manifest row was omitted")
    object_ids = {freeze_tree[name] for name in selected}
    object_ids.update(base_tree[name] for name in selected if name in base_tree)
    append_only_path = PREFIX + "VERIFICATION_PLAN.md"
    object_ids.update((base_tree[append_only_path], freeze_tree[append_only_path]))
    blobs = read_blobs(object_ids)
    source_rows = []
    for name, categories in selected.items():
        current = (ROOT / name).read_bytes()
        original = historical_rows.get(name)
        before = initial.get(name)
        base_oid, freeze_oid = base_tree.get(name), freeze_tree[name]
        base_blob = blob_identity(base_oid, blobs)
        frozen_blob = blob_identity(freeze_oid, blobs)
        if base_oid != freeze_oid and not name.startswith(REPAIR) and name not in PRODUCTION_CHANGES:
            raise ValueError("Protected selected Git source changed: " + name)
        if before and name not in PRODUCTION_CHANGES and sha(current) != before["sha256"]:
            raise ValueError("Protected selected raw working bytes changed: " + name)
        row = {
            "path": name, "categories": categories,
            "workingBytes": len(current), "workingSha256": sha(current),
            "baseGitBlob": base_blob, "freezeGitBlob": frozen_blob,
            "baseEqualsFreezeGitBlob": base_oid == freeze_oid,
            "workingEqualsFreezeRawBytes": current == blobs[freeze_oid],
            "workingEqualsFreezeAfterCRLFToLFOnly":
                current.replace(b"\r\n", b"\n") == blobs[freeze_oid].replace(b"\r\n", b"\n"),
            "initialWorkingIdentity": before,
            "initialWorkingBytesUnchanged": None if before is None else (
                len(current) == before["bytes"] and sha(current) == before["sha256"]),
        }
        if not row["workingEqualsFreezeAfterCRLFToLFOnly"]:
            raise ValueError("Working source is not the frozen source serialization: " + name)
        if original:
            row["historicalSourceManifestIdentity"] = original
            row["historicalWorkingBytesEqualCurrent"] = (
                original["sha256"] == sha(current) and original["bytes"] == len(current))
            row["historicalGitBlobEqualsFreeze"] = (
                original["gitBlobOid"] == freeze_oid and
                original["gitBlobSha256"] == frozen_blob["sha256"] and
                original["gitBlobBytes"] == frozen_blob["bytes"])
        source_rows.append(row)

    cache_receipt = read_json(HERE / "CACHE_PROVENANCE.json")
    cache_path = Path(cache_receipt["manifest"])
    cache_identity = identity(cache_path)
    if (cache_identity["bytes"], cache_identity["sha256"]) != (
            cache_receipt["manifestBytes"], cache_receipt["manifestSha256"]):
        raise ValueError("Copied cache manifest identity differs")
    cache = read_json(cache_path)
    copied_source_checks = []
    for name, captured in sorted(cache["sources"].items()):
        actual = relative_identity(name)
        unchanged = (
            actual["sha256"] == captured["targetWorking"] and
            base_tree[name] == freeze_tree[name] == captured["gitBlob"])
        if not unchanged:
            raise ValueError("Copied-cache source applicability differs: " + name)
        copied_source_checks.append({"path": name, "workingSha256": actual["sha256"],
                                     "baseAndFreezeGitBlobOid": freeze_tree[name]})
    cache_artifacts = {key.replace("\\", "/"): value for key, value in cache["artifacts"].items()}
    artifacts = []
    lean_sources = sorted({name for name in historical_rows if name.startswith("RMQ/") and name.endswith(".lean")} | {"RMQ.lean"})
    for source in lean_sources:
        artifact_stem = ".lake/build/lib/lean/" + source[:-5]
        for suffix in (".olean", ".ilean", ".trace"):
            artifact_name = artifact_stem + suffix
            item = relative_identity(artifact_name)
            item["sourcePath"] = source
            item["sourceFreezeGitBlobOid"] = freeze_tree[source]
            copied = cache_artifacts.get(artifact_name)
            item["copiedCacheIdentity"] = copied
            item["unchangedFromCopiedCache"] = copied is not None and all(
                item[field] == copied[field] for field in ("bytes", "sha256"))
            artifacts.append(item)
    executable = relative_identity(".lake/build/bin/rmq_lifecycle_validate.exe")
    if executable["sha256"] != PINNED_EXE:
        raise ValueError("Original pinned lifecycle executable differs")
    executable["sourceModule"] = "RMQ/Validation/PackedLifecycle.lean"
    executable["lakeTarget"] = "rmq_lifecycle_validate"
    executable["unchangedOriginalPinnedExecutable"] = True
    executable["copiedCacheIdentity"] = cache_artifacts[executable["path"]]

    version_receipts = [receipt("pinned-lean-version", 0), receipt("pinned-lake-version", 0)]
    builds = [receipt("final-default-build-pinned", 0), receipt("final-named-build-pinned", 0)]
    for build in builds:
        if build["lastStdoutLine"] != "Build completed successfully." or build["stderrReturnedLineCount"]:
            raise ValueError("Successful build terminal/stream verdict differs")
    production_replays = [
        receipt("final-validator-pwsh-full", 0),
        receipt("final-validator-winps-full", 0),
        receipt("final-dependency-full", 0),
    ]
    failed_shim = receipt("final-default-build", 1)
    shells = []
    for profile in ("pwsh", "winps"):
        evidence_name = ".lake/repair-r1/old-environment-" + profile + "/summary.json"
        observation = read_json(ROOT / evidence_name)
        item = identity(Path(observation["shell"]))
        item.update(profile=profile, observedVersion=observation["version"],
                    observedDotnet=observation["dotnet"],
                    observationReceipt=relative_identity(evidence_name))
        shells.append(item)
    tools = []
    for filename in ("lean.exe", "lake.exe", "libInit_shared.dll",
                     "libleanshared.dll", "libleanshared_1.dll", "libLake_shared.dll"):
        item = identity(TOOLROOT / "bin" / filename)
        if filename in ("lean.exe", "lake.exe"):
            observed = version_receipts[0 if filename == "lean.exe" else 1]
            item["observedVersionLine"] = observed["lastStdoutLine"]
            item["versionReceipt"] = observed["files"][0]
        else:
            item["role"] = "Installed runtime shared library identity; hashing is not dynamic-loader attestation"
        tools.append(item)
    tools.append(identity(TOOLROOT / "include/lean/version.h"))
    tools.append({**identity(Path(failed_shim["specification"]["file"])),
                  "role": "Failed elan shim attempt; not the executable used by successful builds"})

    final_receipts = read_json(ROOT / (PREFIX + "FINAL_RECEIPTS.json"))
    inventory_artifacts = []
    for recorded in final_receipts["artifacts"]:
        if Path(recorded["path"]).name not in {
                "inventory.result.json", "inventory.stdout.txt", "inventory.stderr.txt"}:
            continue
        actual = identity(Path(recorded["path"]))
        if any(actual[field] != recorded[field] for field in ("bytes", "sha256")):
            raise ValueError("Retained original inventory artifact differs: " + recorded["path"])
        inventory_artifacts.append({"recorded": recorded, "actual": actual, "exactMatch": True})
    if len(inventory_artifacts) != 3:
        raise ValueError("Exact original inventory artifact triple is unavailable")
    inventory_record = final_receipts["inventory"]
    if inventory_record["exitCode"] != 0 or inventory_record["timedOut"] or inventory_record["outputLimitExceeded"]:
        raise ValueError("Historical inventory was not a successful bounded run")
    append_only_baseline = initial[append_only_path]
    append_only_prefix = (ROOT / append_only_path).read_bytes()[:append_only_baseline["bytes"]]
    if (len(append_only_prefix), sha(append_only_prefix)) != (
            append_only_baseline["bytes"], append_only_baseline["sha256"]):
        raise ValueError("Original verification-plan byte prefix changed")

    return {
        "schema": 1, "baseCommit": BASE, "sourceFreezeCommit": FREEZE,
        "productionFreezeCommit": PRODUCTION_FREEZE,
        "productionGitBlobsUnchangedAcrossControlFreeze": True,
        "worktree": ROOT.as_posix(), "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "interpretation": {
            "working": "Actual raw working bytes. CRLF-to-LF comparison is separately labeled and never substitutes for raw identity.",
            "git": "Exact base/freeze blob bytes, SHA-256 and Git OID obtained with bounded read-only Git object queries.",
            "historical": "Old manifests/receipts retain their historical source identities; explicit equality fields state reuse applicability.",
            "cache": "Independent copied warm artifacts, followed by successful bounded Lake verification; retained trace paths can name the original cache checkout.",
            "streams": "Inherited helper returned nonempty lines; receipt files preserve that returned representation, not raw original process stream bytes.",
            "limits": "No new theorem, changed trust assumption, native allocator proof, full dependency platform claim, aggregate result or campaign acceptance follows from this identity packet.",
        },
        "selection": {
            "rules": ["All original SOURCE_MANIFEST paths", "All frozen scripts/", "All original lifecycle evidence except authorized append-only verification-plan citation",
                      "Frozen repair files except packaging/evolving evidence outputs", "All canonical .agents governance, AGENTS.md, CI, attributes and build/toolchain files",
                      "Internal filenames containing policy, allowlist, preflight or gate"],
            "excludedPackagingPaths": sorted(PACKAGING_EXCLUSIONS),
            "selfHashAvoidance": "This generator and its output are excluded; final package delivery binds their identities separately.",
        },
        "counts": {
            "sources": len(source_rows), "originalSourceManifestRows": len(historical_rows),
            "originalLifecycleEvidence": sum("original-lifecycle-evidence" in row["categories"] for row in source_rows),
            "repairFrozenInputs": sum("frozen-repair-code-contract-or-input" in row["categories"] for row in source_rows),
            "artifacts": len(artifacts), "shells": len(shells), "toolFiles": len(tools),
            "historicalInventoryArtifacts": len(inventory_artifacts),
        },
        "sources": source_rows, "artifacts": artifacts, "executable": executable,
        "appendOnlyHistoricalEvidence": {
            "path": append_only_path,
            "initialWorkingProtectedPrefix": append_only_baseline,
            "actualProtectedPrefixBytes": len(append_only_prefix),
            "actualProtectedPrefixSha256": sha(append_only_prefix),
            "baseGitBlob": blob_identity(base_tree[append_only_path], blobs),
            "freezeGitBlob": blob_identity(freeze_tree[append_only_path], blobs),
            "interpretation": "Only the immutable original raw working-byte prefix is pinned here; the separately authorized minimal report citation remains packaging.",
        },
        "directElaborationConsumers": [
            {"path": name, "freezeGitBlobOid": freeze_tree[name],
             "artifactInterpretation": "Source script elaborated directly by retained inventory or dependency replay; no persistent named-build .olean is inferred."}
            for name in sorted(historical_rows)
            if name.endswith(".lean") and not name.startswith("RMQ/")
        ],
        "shells": shells, "toolFiles": tools, "versionReceipts": version_receipts,
        "cache": {"receipt": relative_identity(REPAIR + "CACHE_PROVENANCE.json"),
                  "manifest": cache_identity, "sourceCount": len(cache["sources"]),
                  "artifactCount": len(cache["artifacts"]), "independentFiles": cache_receipt["independentFiles"],
                  "allCopiedSourcesMatchTargetWorkingAndBaseAndFreezeGitBlobs": True,
                  "copiedSourceCheckCount": len(copied_source_checks),
                  "orderedCopiedSourceCheckSha256": sha(json.dumps(
                      copied_source_checks, sort_keys=True, separators=(",", ":")).encode("utf-8")),
                  "sourceCheckInterpretation": "Every source named by the separately byte-pinned cache manifest was compared, not only sampled; that manifest retains the full per-file records."},
        "successfulBuilds": builds,
        "unchangedProductionReplayReceipts": production_replays,
        "productionReplayReceiptInterpretation": "These pins establish unchanged source applicability for the completed production full16/full26 invocations across the later control-harness freeze. Exact case cardinality and inner verdict coverage remain recorded by their full receipts and the final evidence packet.",
        "failedElanShimAttempt": {
            "receipt": failed_shim,
            "disposition": "Ordinary exit 1 during attempted download; retained as failure. Existing pinned direct Lake binary used thereafter. No installation or upgrade was performed by this manifest generator.",
        },
        "historicalInventoryReuse": {
            "originalManifest": relative_identity(historical_path),
            "originalFinalReceipts": relative_identity(PREFIX + "FINAL_RECEIPTS.json"),
            "sourceCommit": final_receipts["sourceCommit"], "run": inventory_record,
            "artifacts": inventory_artifacts,
            "justification": "The inventory source, formal producers and checked consumer Git blobs are explicitly compared above. The two repaired wrappers are not theorem definitions. Historical compiler output is reused as original source-bound type/axiom evidence, not as a newly executed proof check.",
        },
    }


def encoded(document: dict) -> bytes:
    text = json.dumps(document, indent=2, ensure_ascii=True) + "\n"
    # Keep source/receipt objects readable and avoid giant nonempty paragraphs.
    text = re.sub(r"(?m)^(\s*\},?)\n(?=\s*[\{\"])", r"\1\n\n", text)
    return text.encode("utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Compare the deterministic packet without writing.")
    arguments = parser.parse_args()
    document = build_manifest()
    data = encoded(document)
    target = HERE / "SOURCE_FREEZE.json"
    if arguments.check:
        if target.read_bytes() != data:
            raise ValueError("SOURCE_FREEZE.json differs from actual frozen sources/evidence")
    else:
        target.write_bytes(data)
    print(json.dumps({"mode": "check" if arguments.check else "write",
                      "counts": document["counts"], "path": target.as_posix(),
                      "bytes": len(data), "sha256": sha(data)}, separators=(",", ":")))


if __name__ == "__main__":
    main()
