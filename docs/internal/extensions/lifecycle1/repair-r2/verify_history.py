"""Resolve immutable R1 evidence first; separately check R2 consumer applicability.

This does not invoke or port R1's current-checkout manifest predicate. Historical
Git bytes, historical raw checkout profiles and current consumed bytes are
separate objects. No Lean, Lake, PowerShell, compiler or semantic replay runs.
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
R1 = ROOT / "docs/internal/extensions/lifecycle1/repair-r1"
PREFIX = "docs/internal/extensions/lifecycle1/"
BASE = "0485a64920a273d0830b926ee46275085222819d"
R1_BASE = "12bd7f0fc2c87f2c9bdef3825bd92477e48e3433"
PRODUCTION = "122a6bedb086d1de1df8dec167c890f887a72cc2"
CONTROL = "7c406b15bdc12333d323c92641ab6c6dad6af7a2"
ORIGINAL = "299ec6527ca2fbcf73cfc34e9de75f4a1f34140c"
DEP = "scripts/lifecycle_dependency_replay.ps1"
WDD = "docs/internal/WORKFLOW_DESIGN_DECISIONS.md"
CONTRACTS = {PREFIX + name for name in (
    "CONTRACT_REQUIREMENTS.json", "ACCEPTANCE_MATRIX.frozen.md", "ACCEPTANCE_MATRIX.md")}
REVIEW = Path("C:/Users/poin/Documents/RMQ/lifecycle-implementation-20260920/life1-r1-review")
REVIEW_PINS = {
    "EVIDENCE_LEAF_PIN_MANIFEST.json": {"bytes": 5653285, "sha256": "a14c74398f31afb7a19b4c5494b6e4d72ae43b964664d9f2d0afa4add65ca346"},
    "DISPOSITION.md": {"bytes": 17832, "sha256": "520d24e435ab007ee84a58ca6d0c36a93aca950ec998190d4e44535c89af4a79"},
    "R2_PROMPT_REVIEW.md": {"bytes": 13569, "sha256": "78b4a9f8304f4df0188112931d2ecc407b5b5e99ab83d6174b6638d7f5512ee8"},
}
IDS = [
    "L01-W-EMPTY", "L02-C-EMPTY", "L03-W-SINGLE", "L04-C-SINGLE",
    "L05-W-REPEAT", "L06-C-REPEAT", "L07-W-TIE", "L08-C-TIE",
    "L09-W-INVALID", "L10-C-INVALID", "L11-W-DIRTY", "L12-C-DIRTY",
    "L13-W-N24", "L14-C-N24", "L15-W-N83", "L16-C-N83",
]
STAGES = ["registry", "startup", "focused", "reject-empty", "reject-whitespace",
          "reject-unknown", "reject-duplicate", "reject-channels", "full"]
ERRORS = ["empty-selector", "whitespace-selector", "unknown-selector",
          "duplicate-selector", "duplicate-selector-channel"]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def ident(raw: bytes) -> dict:
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def normalized_pin(pin: dict) -> dict:
    return {key: (str(value).lower() if key == "sha256" else value)
            for key, value in pin.items() if key in ("bytes", "sha256")}


def satisfies(actual: dict, expected: dict) -> bool:
    return all(actual[key] == value for key, value in normalized_pin(expected).items())


def read(path: Path) -> dict:
    return json.loads(path.read_bytes().decode("utf-8-sig"))


def git(*arguments: str, input_bytes: bytes | None = None) -> bytes:
    result = subprocess.run(
        ["git", "-c", "safe.directory=" + ROOT.as_posix(),
         "-c", "core.excludesFile=", *arguments],
        cwd=ROOT, input=input_bytes, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, timeout=60, check=True,
    )
    require(not result.stderr, "Read-only Git query emitted stderr")
    return result.stdout


def tree(commit: str) -> dict:
    result = {}
    for entry in git("ls-tree", "-r", "-z", commit).split(b"\0"):
        if entry:
            meta, path = entry.split(b"\t", 1)
            mode, kind, oid = meta.decode("ascii").split()
            require(kind == "blob", "Unexpected non-blob tree leaf")
            result[path.decode("utf-8")] = {"object": oid, "mode": mode}
    return result


def blobs(oids: set[str]) -> dict:
    ordered = sorted(oids)
    data = git("cat-file", "--batch",
               input_bytes=("\n".join(ordered) + "\n").encode("ascii"))
    offset, result = 0, {}
    for requested in ordered:
        end = data.index(b"\n", offset)
        oid, kind, length = data[offset:end].decode("ascii").split()
        require(oid == requested and kind == "blob", "Git blob identity mismatch")
        offset = end + 1
        result[oid] = data[offset:offset + int(length)]
        offset += int(length)
        require(data[offset:offset + 1] == b"\n", "Git blob boundary mismatch")
        offset += 1
    require(offset == len(data), "Unexpected trailing Git bytes")
    return result


def encoded(document: dict) -> bytes:
    text = json.dumps(document, indent=2, ensure_ascii=True) + "\n"
    return re.sub(r"(?m)^(\s*\},?)\n(?=\s*[\{\"])", r"\1\n\n", text).encode("utf-8")


class Audit:
    def __init__(self):
        self.initial = read(HERE / "INITIAL_FILES.json")
        self.protected = read(HERE / "PROTECTED_BASELINE.json")
        self.materialization = read(HERE / "MATERIALIZATION.json")
        self.source_freeze = read(R1 / "SOURCE_FREEZE.json")
        self.original_manifest = read(ROOT / (PREFIX + "SOURCE_MANIFEST.json"))
        self.original_receipts = read(ROOT / (PREFIX + "FINAL_RECEIPTS.json"))
        self.index = read(R1 / "EVIDENCE_INDEX.json")
        self.delivery = read(ROOT / ".lake/repair-r1/delivery.json")
        self.review = read(REVIEW / "EVIDENCE_LEAF_PIN_MANIFEST.json")
        self.cache_receipt = read(R1 / "CACHE_PROVENANCE.json")
        self.cache = read(Path(self.cache_receipt["manifest"]))
        self.refs = (BASE, R1_BASE, PRODUCTION, CONTROL, ORIGINAL)
        self.trees = {ref: tree(ref) for ref in self.refs}
        require(set(self.initial) == set(self.trees[BASE]), "Initial snapshot path set differs from exact R2 base")
        require(set(self.protected) == set(self.initial), "Protected baseline omitted/added a startup path")
        require(self.source_freeze["sourceFreezeCommit"] == CONTROL and
                self.source_freeze["productionFreezeCommit"] == PRODUCTION, "R1 producer commits differ")
        require(self.delivery["packageCommit"] == BASE, "R1 delivery is not the assigned exact base")
        needed = set(self.cache["sources"])
        needed.update(row["path"] for row in self.source_freeze["sources"])
        needed.update(name for name in self.initial if name.startswith(PREFIX))
        needed.update((DEP, WDD))
        needed.update(path for row in self.index["checks"] for path in row["sourcePins"]
                      if not path.startswith(".lake/"))
        for file in self.review["files"]:
            relative = self.relative(Path(file["path"]))
            if relative and relative in self.initial:
                # Exact old profiles may be needed even when a current raw file
                # has been explicitly materialized or appended.
                if relative in CONTRACTS | {DEP, WDD} or any(
                        ref.get("equal") is False for ref in file["references"]):
                    needed.add(relative)
        objects = {mapping[name]["object"] for mapping in self.trees.values()
                   for name in needed if name in mapping}
        self.blobs = blobs(objects)
        self.files = {}
        self.bindings = []
        self.profiles = {}
        self.profile_cache = {}

    def relative(self, path: Path) -> str | None:
        if not path.is_absolute():
            return path.as_posix()
        for root in (ROOT, Path(self.cache_receipt["source"])):
            try:
                return path.relative_to(root).as_posix()
            except ValueError:
                pass
        return None

    def absolute(self, path: str | Path) -> Path:
        path = Path(path)
        return path if path.is_absolute() else ROOT / path

    def actual(self, path: str | Path) -> dict:
        path = self.absolute(path)
        key = path.as_posix().casefold()
        if key not in self.files:
            before = path.stat()
            digest, size = hashlib.sha256(), 0
            with path.open("rb") as stream:
                for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                    digest.update(chunk)
                    size += len(chunk)
            after = path.stat()
            require((before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns),
                    "File changed during read: " + str(path))
            self.files[key] = {"path": path.as_posix(), "bytes": size, "sha256": digest.hexdigest()}
        return self.files[key]

    def committed_profile(self, relative: str, expected: dict) -> dict:
        expected = normalized_pin(expected)
        key = (relative, expected.get("bytes"), expected.get("sha256"))
        if key in self.profile_cache:
            return self.profile_cache[key]
        matches = []
        for commit, mapping in self.trees.items():
            if relative not in mapping:
                continue
            oid = mapping[relative]["object"]
            if oid not in self.blobs:
                continue
            raw = self.blobs[oid]
            variants = [("exact-git-bytes", raw)]
            if b"\r\n" not in raw and b"\n" in raw:
                variants.append(("explicit-LF-to-CRLF-checkout-profile", raw.replace(b"\n", b"\r\n")))
            for serialization, candidate in variants:
                if satisfies(ident(candidate), expected):
                    matches.append({"commit": commit, "gitObject": oid,
                                    "gitBytes": ident(raw), "rawSerialization": serialization,
                                    "historicalRawBytes": ident(candidate)})
        if not matches and relative in self.cache["sources"]:
            retained = Path(self.cache_receipt["source"]) / relative
            cache_pin = self.cache["sources"][relative]
            retained_identity = self.actual(retained)
            if satisfies(retained_identity, expected):
                require(retained_identity["sha256"] == cache_pin["sourceWorking"],
                        "Retained historical snapshot differs from original cache receipt")
                oid = self.trees[R1_BASE][relative]["object"]
                require(oid == cache_pin["gitBlob"], "Retained raw snapshot's producer Git object differs")
                require(retained.read_bytes().replace(b"\r\n", b"\n") == self.blobs[oid],
                        "Retained raw snapshot has no recorded producer content correspondence")
                matches.append({"commit": R1_BASE, "gitObject": oid,
                                "gitBytes": ident(self.blobs[oid]),
                                "rawSerialization": "exact-retained-raw-snapshot",
                                "retainedSnapshot": retained_identity,
                                "historicalRawBytes": {k: retained_identity[k] for k in ("bytes", "sha256")},
                                "rawEqualsGit": satisfies(ident(self.blobs[oid]), expected)})
        if not matches and relative in self.initial and satisfies(self.initial[relative]["raw"], expected):
            # R1's append-only process log contains historical mixed newline
            # serialization. Its protected initial prefix is itself the raw
            # snapshot; Git content and raw identity remain distinct.
            retained = ROOT / relative
            candidate = retained.read_bytes()
            if relative == WDD:
                candidate = candidate[:self.initial[relative]["raw"]["bytes"]]
            if satisfies(ident(candidate), expected):
                oid = self.trees[BASE][relative]["object"]
                require(candidate.replace(b"\r\n", b"\n") == self.blobs[oid],
                        "Protected startup raw profile differs from committed source content")
                matches.append({"commit": BASE, "gitObject": oid,
                                "gitBytes": ident(self.blobs[oid]),
                                "rawSerialization": "exact-protected-startup-prefix" if relative == WDD else "exact-retained-raw-snapshot",
                                "retainedSnapshot": {"path": retained.as_posix(), **ident(candidate)},
                                "historicalRawBytes": ident(candidate),
                                "rawEqualsGit": ident(candidate) == ident(self.blobs[oid])})
        if not matches:
            retained_pins = [row for row in self.index["files"] if satisfies(row, expected)]
            for retained_pin in retained_pins:
                retained = Path(retained_pin["path"])
                if not satisfies(self.actual(retained), expected):
                    continue
                candidate = retained.read_bytes()
                for commit, mapping in self.trees.items():
                    if relative not in mapping or mapping[relative]["object"] not in self.blobs:
                        continue
                    oid = mapping[relative]["object"]
                    if candidate.replace(b"\r\n", b"\n") == self.blobs[oid]:
                        matches.append({"commit": commit, "gitObject": oid,
                                        "gitBytes": ident(self.blobs[oid]),
                                        "rawSerialization": "exact-retained-raw-snapshot",
                                        "retainedSnapshot": self.actual(retained),
                                        "historicalRawBytes": ident(candidate),
                                        "rawEqualsGit": candidate == self.blobs[oid],
                                        "checkoutContentCorrespondence": "CRLF-to-LF relation only; raw identities are not equated"})
                if matches:
                    break
        require(bool(matches), "Historical source pin has no exact immutable producer profile: " + relative + " " + str(expected))
        result = {"path": relative, "recorded": expected, "matchingProducerProfiles": matches}
        profile_key = relative + ":" + expected["sha256"]
        self.profiles[profile_key] = result
        self.profile_cache[key] = result
        return result

    def bind(self, path: str | Path, expected: dict, origin: str, *, historical=True) -> dict:
        path = self.absolute(path)
        actual = self.actual(path)
        expected = normalized_pin(expected)
        relative = self.relative(path)
        equal = satisfies(actual, expected)
        proof = None
        if relative and any(relative in mapping and mapping[relative]["object"] in self.blobs
                            for mapping in self.trees.values()):
            proof = self.committed_profile(relative, expected)
        if not equal:
            require(historical and proof is not None,
                    "Retained artifact/current consumed bytes changed: " + str(path) + " at " + origin)
        disposition = "current-exact" if equal else "historical-producer-resolved-current-bytes-distinct"
        row = {"path": path.as_posix(), "origin": origin, "expected": expected,
               "actual": {key: actual[key] for key in ("bytes", "sha256")},
               "disposition": disposition,
               "retainedRawSnapshotExact": equal,
               "producerProfileKey": None if proof is None else relative + ":" + expected["sha256"]}
        self.bindings.append(row)
        return row

    def walk_pins(self, value, origin: str):
        if isinstance(value, dict):
            if {"path", "bytes", "sha256"} <= value.keys() and isinstance(value["path"], str):
                self.bind(value["path"], value, origin)
            for key, item in value.items():
                self.walk_pins(item, origin + "/" + str(key))
        elif isinstance(value, list):
            for index, item in enumerate(value):
                self.walk_pins(item, origin + "/" + str(index))

    def immutable_history(self):
        for name in sorted(self.initial):
            if name.startswith(PREFIX + "repair-r1/") or name.startswith(PREFIX) and name not in CONTRACTS:
                self.bind(name, self.initial[name]["raw"], "immutable-history/" + name, historical=False)
        for label, document in (("R1_SOURCE_FREEZE", self.source_freeze),
                                ("R1_EVIDENCE_INDEX", self.index), ("R1_delivery", self.delivery),
                                ("original_SOURCE_MANIFEST", self.original_manifest),
                                ("original_FINAL_RECEIPTS", self.original_receipts)):
            self.walk_pins(document, label)
        require(self.original_manifest["sourceCommit"] == self.original_receipts["sourceCommit"] == ORIGINAL,
                "Original producer commit differs")
        for row in self.original_manifest["files"]:
            oid = self.trees[ORIGINAL][row["path"]]["object"]
            require(oid == row["gitBlobOid"] and ident(self.blobs[oid]) == {
                "bytes": row["gitBlobBytes"], "sha256": row["gitBlobSha256"].lower()},
                "Original manifest's immutable producer bytes differ: " + row["path"])
        for row in self.source_freeze["sources"]:
            path = row["path"]
            self.bind(path, {"bytes": row["workingBytes"], "sha256": row["workingSha256"]},
                      "R1_SOURCE_FREEZE/recorded-working/" + path)
            for label, commit in (("baseGitBlob", R1_BASE), ("freezeGitBlob", CONTROL)):
                pin = row[label]
                if pin is None:
                    require(path not in self.trees[commit], "Recorded absent Git blob exists")
                else:
                    require(self.trees[commit][path]["object"] == pin["oid"], "R1 source Git OID mismatch: " + path)
                    require(satisfies(ident(self.blobs[pin["oid"]]), pin), "R1 source exact Git bytes differ: " + path)
        require(len(self.review["files"]) == self.review["uniqueFiles"], "Review pin inventory cardinality differs")
        reference_count = 0
        seen = set()
        for file in self.review["files"]:
            key = Path(file["path"]).as_posix().casefold()
            require(key not in seen, "Duplicate review pin file")
            seen.add(key)
            self.bind(file["path"], file, "review-index/recorded-current-profile")
            for ref in file["references"]:
                reference_count += 1
                if "expected" in ref:
                    require(satisfies(file, ref["expected"]) == ref["equal"],
                            "Review's historical equality relation was changed")
                    self.bind(file["path"], ref["expected"], "review-reference/" + ref["origin"])
        require(reference_count == self.review["references"], "Review reference count differs")
        # Independently validate embedded summaries, not only file-count pins.
        for row in self.index["checks"]:
            receipt = read(Path(row["receipt"]["path"]))
            require(receipt["sources"] == row["sourcePins"], "Indexed source pins differ from receipt")
            result = receipt["result"]
            for field, result_field in (("exit", "ExitCode"), ("seconds", "DurationSeconds"),
                                        ("deadline", "DeadlineSeconds"), ("timeout", "TimedOut"),
                                        ("overflow", "OutputLimitExceeded"), ("ownership", "Ownership"),
                                        ("terminatedIds", "TerminatedIds")):
                require(row[field] == result[result_field], "Indexed process summary differs: " + row["name"])
            require(row["spec"] == receipt["spec"] and
                    row["stdoutLines"] == len(result["StandardOutput"]) and
                    row["stderrLines"] == len(result["StandardError"]), "Indexed invocation/stream cardinality differs")
            for path, digest in row["sourcePins"].items():
                self.bind(path, {"sha256": digest}, "R1-check-source/" + row["name"])
        for row in self.index["campaigns"]:
            require(read(Path(row["receipt"]["path"])) == row["summary"], "Indexed campaign summary differs")
        for row in self.index["native"]:
            directory = Path(row["path"])
            require(read(directory / "processes.json") == row["processes"], "Indexed native processes differ")
            require(read(directory / "PASS.json") == row["pass"], "Indexed native PASS packet differs")
        return {"indexedRetainedFiles": len(self.index["files"]),
                "indexedChecks": len(self.index["checks"]), "indexedNativeRuns": len(self.index["native"]),
                "indexedCampaignSummaries": len(self.index["campaigns"]),
                "reviewFiles": len(seen), "reviewReferences": reference_count,
                "originalProducerManifestFiles": len(self.original_manifest["files"]),
                "originalRetainedArtifacts": len(self.original_receipts["artifacts"])}

    def current_consumed_inputs(self):
        for name, initial in self.initial.items():
            require(initial["git"]["object"] == self.trees[BASE][name]["object"], "Startup Git object differs: " + name)
            expected = self.protected[name]
            if name not in CONTRACTS:
                require(expected == initial["raw"], "Undisclosed baseline materialization: " + name)
            if name not in {DEP, WDD}:
                require(satisfies(self.actual(name), expected), "Protected current input changed: " + name)
        materialized = []
        for name in sorted(CONTRACTS):
            oid = self.trees[BASE][name]["object"]
            raw = self.blobs[oid]
            old = raw.replace(b"\n", b"\r\n")
            require(b"\r\n" not in raw and ident(old) == self.initial[name]["raw"],
                    "Reviewed original contract profile is not the exact disclosed CRLF transform")
            require((ROOT / name).read_bytes() == raw, "Materialized contract is not exact Git bytes: " + name)
            require(self.protected[name] == ident(raw), "Materialized protected baseline differs")
            recorded = self.materialization["files"][name]
            require(recorded["initial"] == ident(old) and recorded["git"] == ident(raw) and recorded["gitObject"] == oid,
                    "Materialization receipt's old/new profiles differ")
            materialized.append({"path": name, "historicalRaw": ident(old), "currentExactGit": ident(raw),
                                 "gitObject": oid, "rawEquality": False,
                                 "classification": "authorized startup materialization; historical pin preserved, never normalized into current equality"})
        old_dep = self.historical_raw(DEP, self.initial[DEP]["raw"])
        current_dep = (ROOT / DEP).read_bytes()
        pattern = rb"(function Hash-Bytes\(\[byte\[\]\]\$bytes\) \{\r?\n)(.*?)(\r?\n\}\r?\nfunction Hash-File)"
        old_match, current_match = re.search(pattern, old_dep, re.S), re.search(pattern, current_dep, re.S)
        require(old_match is not None and current_match is not None, "Hash-Bytes source boundary unavailable")
        old_outside = old_dep[:old_match.start(2)] + old_dep[old_match.end(2):]
        current_outside = current_dep[:current_match.start(2)] + current_dep[current_match.end(2):]
        require(old_outside == current_outside, "Dependency bytes changed outside the authorized Hash-Bytes body")
        wdd = (ROOT / WDD).read_bytes()
        require(ident(wdd[:self.initial[WDD]["raw"]["bytes"]]) == self.initial[WDD]["raw"],
                "Original WDD raw prefix changed")
        cache_sources = []
        for name, pin in sorted(self.cache["sources"].items()):
            require(self.trees[R1_BASE][name]["object"] == pin["gitBlob"] == self.trees[BASE][name]["object"],
                    "Formal/cache producer Git content changed: " + name)
            self.bind(name, {"sha256": pin["targetWorking"]}, "current-cache-source/" + name, historical=False)
            cache_sources.append(name)
        artifact_count = 0
        for name, pin in sorted(self.cache["artifacts"].items()):
            name = name.replace("\\", "/")
            self.bind(name, pin, "current-copied-artifact/" + name, historical=False)
            artifact_count += 1
        for row in self.source_freeze["artifacts"]:
            self.bind(row["path"], row, "current-named-consumer-artifact", historical=False)
        for label in ("shells", "toolFiles"):
            for row in self.source_freeze[label]:
                self.bind(row["path"], row, "current-runtime/" + label, historical=False)
        exe = self.source_freeze["executable"]
        self.bind(exe["path"], exe, "current-native-executable", historical=False)
        for name in ("scripts/lifecycle_validator.ps1", "scripts/lifecycle_validator_environment.ps1",
                     "scripts/owned_process_tree.ps1"):
            self.bind(name, self.initial[name]["raw"], "current-validator-call-chain", historical=False)
        inventory = self.source_freeze["historicalInventoryReuse"]
        require(inventory["run"]["exitCode"] == 0 and not inventory["run"]["timedOut"] and
                not inventory["run"]["outputLimitExceeded"], "Historical type/axiom inventory was not successful")
        for row in inventory["artifacts"]:
            require(row["recorded"] == row["actual"], "R1 inventory recorded/actual profile differs")
            self.bind(row["recorded"]["path"], row["recorded"], "current-retained-type-axiom-output", historical=False)
        result_path = Path(inventory["artifacts"][0]["recorded"]["path"])
        require(read(result_path) == inventory["run"] == self.original_receipts["inventory"],
                "Historical type/axiom process record differs from producer receipts")
        return {
            "protectedStartupPaths": len(self.initial), "currentProtectedRawPathsChecked": len(self.initial) - 2,
            "formalAndBuildCacheSourceCount": len(cache_sources), "copiedArtifactCount": artifact_count,
            "namedConsumerArtifacts": len(self.source_freeze["artifacts"]),
            "materializedContracts": materialized,
            "dependency": {"path": DEP, "historicalRaw": ident(old_dep), "currentRaw": ident(current_dep),
                           "rawBytesChanged": old_dep != current_dep, "outsideHashBytesBodyExact": True,
                           "historicalBody": ident(old_match.group(2)), "currentBody": ident(current_match.group(2)),
                           "classification": "incidental capture for old validator/build receipts; load-bearing change for dependency/control receipts"},
            "typeAxiomInventory": inventory,
            "historicalBuilds": self.builds(),
            "warmCacheLimit": "All copied artifacts and source identities are checked; this is not a cold rebuild or dynamic-loader attestation.",
        }

    def builds(self) -> list[dict]:
        result = []
        for row in self.source_freeze["successfulBuilds"]:
            path = self.absolute(row["files"][0]["path"])
            outer = read(path)
            self.process(outer["result"], 0)
            require(outer["spec"] == row["specification"], "Historical build actual invocation differs")
            require(outer["result"]["StandardOutput"][-1] == "Build completed successfully." and
                    not outer["result"]["StandardError"], "Historical build terminal differs")
            for stream, key in (("stdout", "StandardOutput"), ("stderr", "StandardError")):
                require((path.parent / (stream + ".txt")).read_bytes() ==
                        "\n".join(outer["result"][key]).encode("utf-8"), "Historical build returned streams differ")
            for name, digest in outer["sources"].items():
                self.bind(name, {"sha256": digest}, row["name"] + "/source", historical=name == DEP)
            runtime = next(tool for tool in self.source_freeze["toolFiles"]
                           if Path(tool["path"]) == Path(outer["spec"]["file"]))
            self.bind(runtime["path"], runtime, row["name"] + "/actual-runtime", historical=False)
            result.append({"name": row["name"], "receipt": row["files"][0],
                           "sourceCommit": PRODUCTION, "seconds": outer["result"]["DurationSeconds"],
                           "actualCommand": outer["spec"], "historicalVerdict": "PASS",
                           "unchangedBuildInputsVerified": True,
                           "incidentalDependencyCapture": DEP,
                           "applicability": "retained build provenance only; R2 still requires its own final build"})
        return result

    def historical_raw(self, name: str, expected: dict) -> bytes:
        profile = self.committed_profile(name, expected)["matchingProducerProfiles"][0]
        raw = (Path(profile["retainedSnapshot"]["path"]).read_bytes()
               if profile["rawSerialization"] == "exact-retained-raw-snapshot"
               else self.blobs[profile["gitObject"]])
        if profile["rawSerialization"] == "explicit-LF-to-CRLF-checkout-profile":
            raw = raw.replace(b"\n", b"\r\n")
        require(satisfies(ident(raw), expected), "Resolved raw profile differs")
        return raw

    def full16(self, profile: str) -> dict:
        name = "final-validator-" + profile + "-full"
        indexed = next(row for row in self.index["checks"] if row["name"] == name)
        outer = read(Path(indexed["receipt"]["path"]))
        self.process(outer["result"], 0)
        require(not outer["result"]["StandardError"] and len(outer["result"]["StandardOutput"]) == 1,
                "Full16 outer streams differ")
        native = next(row for row in self.index["native"] if row["check"] == name)
        directory = Path(native["path"])
        require(outer["result"]["StandardOutput"] == [
            "LIFE1-VALIDATOR PASS stage=full processes=9 logs=" + str(directory)],
            "Full16 outer terminal/path differs")
        require(outer["spec"]["arguments"][-4:] == [
            "-Stage", "full", "-DeadlineSeconds", "1800"], "Full16 actual invocation differs")
        before, after = read(directory / "identity-before.json"), read(directory / "identity-after.json")
        require(before == after, "Full16 producing source changed during historical run")
        actual_inputs = []
        for path, digest in before.items():
            binding = self.bind(path, {"sha256": digest}, name + "/actual-consumed-input", historical=False)
            actual_inputs.append({"path": path, "historicalAndCurrentSha256": digest.lower(),
                                  "historicalProducerProfile": binding["producerProfileKey"]})
        incidental = []
        for path, digest in outer["sources"].items():
            historical = self.bind(path, {"sha256": digest}, name + "/outer-source-capture")
            if path == DEP:
                incidental.append(historical)
            else:
                self.bind(path, {"sha256": digest}, name + "/unchanged-additional-input", historical=False)
        require(len(incidental) == 1 and DEP not in before, "Incidental dependency classification changed")
        validator = self.historical_raw("scripts/lifecycle_validator.ps1", self.initial["scripts/lifecycle_validator.ps1"]["raw"])
        require(b"lifecycle_dependency_replay.ps1" not in validator, "Validator acquired a dependency-runner call")
        pass_packet, stages = native["pass"], native["processes"]
        require(pass_packet["cases"] == IDS and pass_packet["processCount"] == 9 and
                pass_packet["identityPreserved"] is True and pass_packet["stage"] == "full" and
                pass_packet["expectedVerdict"] == "PASS", "Full16 pass packet differs")
        require([row["name"] for row in stages] == STAGES, "Full16 exact ordered process registry differs")
        registry_lines = ["LIFE1-REGISTRY|" + key + "|" +
                          ("word" if "-W-" in key else "comparison") + "|" +
                          ("dirty-entry" if "DIRTY" in key else "lifecycle") + "|PASS" for key in IDS]
        for stage in stages:
            rejecting = stage["name"].startswith("reject-")
            self.process(stage["result"], int(rejecting))
            require(stage["exitCode"] == stage["expectedExit"] == int(rejecting), "Full16 process exit mapping differs")
            for stream, key in (("stdout", "StandardOutput"), ("stderr", "StandardError")):
                require((directory / (stage["name"] + "." + stream + ".txt")).read_bytes() ==
                        "\n".join(stage["result"][key]).encode("utf-8"), "Full16 returned-line stream file differs")
        require(stages[0]["result"]["StandardOutput"] == registry_lines and not stages[0]["result"]["StandardError"],
                "Full16 native IDs/models/kinds differ")
        require(stages[1]["result"]["StandardOutput"] == ["LIFE1-STARTUP|PASS|cases=16"] and
                not stages[1]["result"]["StandardError"], "Full16 startup differs")
        require(len(stages[2]["result"]["StandardOutput"]) == 2 and
                stages[2]["result"]["StandardOutput"][1] == "LIFE1-PASS|mode=single|cases=1" and
                not stages[2]["result"]["StandardError"], "Full16 focused positive differs")
        self.case_line(IDS[0], stages[2]["result"]["StandardOutput"][0])
        for stage, error in zip(stages[3:8], ERRORS):
            require(stage["result"]["StandardOutput"] == [] and
                    stage["result"]["StandardError"] == ["LIFE1-FAIL|" + error], "Full16 exact selector rejection differs")
        full = stages[-1]["result"]
        require(len(full["StandardOutput"]) == 17 and not full["StandardError"] and
                full["StandardOutput"][-1] == "LIFE1-PASS|mode=full|cases=16", "Full16 exact terminal/cardinality differs")
        for key, line in zip(IDS, full["StandardOutput"]):
            self.case_line(key, line)
        shell = next(row for row in self.source_freeze["shells"] if row["profile"] == profile)
        require(Path(outer["spec"]["file"]) == Path(shell["path"]), "Full16 actual shell differs")
        self.bind(shell["path"], shell, name + "/actual-runtime", historical=False)
        return {
            "check": name, "applicableToCurrentUnchangedValidator": True,
            "producingProductionCommit": PRODUCTION, "producingPackageCommit": BASE,
            "receipt": indexed["receipt"], "directory": directory.as_posix(),
            "seconds": outer["result"]["DurationSeconds"], "deadline": outer["result"]["DeadlineSeconds"],
            "runtime": shell, "exactOrderedNativeIds": IDS, "processes": 9,
            "exactReturnedStreamsAndSelectorsVerified": True, "actualConsumedInputs": actual_inputs,
            "incidentalDependencyPin": incidental[0],
            "incidentalJustification": "The immutable validator imports the adapter/helper and invokes the pinned native executable; it never executes the dependency replay script. Its own before/after identity set excludes that outer administrative capture.",
        }

    @staticmethod
    def process(result: dict, expected_exit: int):
        require(result["ExitCode"] == expected_exit and not result["TimedOut"] and
                not result["OutputLimitExceeded"] and result["DeadlineSeconds"] > 0 and
                result["Ownership"] == "kill-on-close-job" and result["TerminatedIds"] == [],
                "Historical bounded process disposition differs")

    @staticmethod
    def case_line(key: str, line: str):
        pattern = r"LIFE1-CASE\|" + re.escape(key) + r"\|PASS\|steps=\d+\|queries=\d+\|querySteps=\d+\|extent=\d+\|peak=\d+\|release=\d+\|dirty=" + ("400" if "DIRTY" in key else "0")
        require(re.fullmatch(pattern, line) is not None, "Native exact case record differs: " + key)

    def run(self):
        for name, pin in REVIEW_PINS.items():
            self.bind(REVIEW / name, pin, "frozen-coordinator-review", historical=False)
        historical = self.immutable_history()
        current = self.current_consumed_inputs()
        native = [self.full16(profile) for profile in ("pwsh", "winps")]
        # Bind the verifier's source documents explicitly without including the
        # verifier/output themselves (final delivery owns their hashes).
        inputs = []
        for path in (HERE / "INITIAL_FILES.json", HERE / "PROTECTED_BASELINE.json", HERE / "MATERIALIZATION.json",
                     R1 / "SOURCE_FREEZE.json", R1 / "EVIDENCE_INDEX.json", R1 / "REPORT.md",
                     ROOT / ".lake/repair-r1/delivery.json", REVIEW / "DISPOSITION.md",
                     REVIEW / "R2_PROMPT_REVIEW.md", REVIEW / "FINAL_REVIEW_VERIFIED.json",
                     REVIEW / "EVIDENCE_LEAF_PIN_MANIFEST.json"):
            inputs.append(self.actual(path))
        inventory = {
            "schema": 1, "historicalPackageCommit": BASE,
            "files": sorted(self.files.values(), key=lambda row: row["path"].casefold()),
            "bindings": self.bindings,
            "historicalProducerProfiles": [self.profiles[key] for key in sorted(self.profiles)],
        }
        inventory_bytes = encoded(inventory)
        inventory_path = ROOT / ".lake/repair-r2/history-binding-inventory.json"
        distinct = [row for row in self.bindings if row["disposition"] != "current-exact"]
        differences = {}
        for row in distinct:
            key = (row["path"], row["expected"].get("sha256"))
            if key not in differences:
                differences[key] = {**row, "origins": []}
                differences[key].pop("origin")
            differences[key]["origins"].append(row["origin"])
        report = {
            "schema": 1, "status": "PASS", "r2Base": BASE,
            "historicalProductionCommit": PRODUCTION, "historicalControlCommit": CONTROL,
            "interpretation": "Historical receipt/source identities are resolved to immutable producers first. Actual current consumed inputs are checked separately. Distinct old/current raw bytes remain distinct.",
            "inputs": inputs, "historicalEvidenceBindings": historical,
            "currentApplicability": current, "reusedFull16": native,
            "historicalRawProfilesDistinctFromCurrent": list(differences.values()),
            "counts": {"distinctFilesRehashed": len(self.files), "bindingsVerified": len(self.bindings),
                       "historicalProducerProfiles": len(self.profiles),
                       "rawDifferenceProfiles": len(differences),
                       "rawDifferenceReferences": len(distinct)},
            "fullInventory": {"path": inventory_path.as_posix(), **ident(inventory_bytes)},
            "notReusedForR2Closure": [
                "R1 full26 and dependency/control results remain historical because Hash-Bytes is load-bearing there.",
                "The R1 Windows positive failed before capture; an empty baseline is not an intact-pin positive.",
                "The old contract failure remains valid for its exact CRLF source profile.",
                "The R1 default/named builds retain historical validity, but R2 requires its own final default build.",
            ],
            "limits": [
                "Read-only identity and retained-verdict verification; no theorem reproof, semantic rerun, fresh process-lifetime observation or campaign acceptance.",
                "Exact LF/CRLF historical profiles are reconstructed from immutable blobs and hash-compared; this is not normalization-as-equality.",
                "Returned nonblank helper lines remain distinct from complete original raw process streams; exceptional overflow/output-loss limits remain.",
                "Hashing installed runtime files is not dynamic-loader attestation; copied warm cache verification is not a cold build.",
            ],
        }
        return report, inventory_path, inventory_bytes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Recompute and compare both existing outputs without writing.")
    parser.add_argument("--output", type=Path, default=HERE / "HISTORY_APPLICABILITY.json")
    arguments = parser.parse_args()
    output = arguments.output.resolve()
    require(output.is_relative_to(HERE) or output.is_relative_to(ROOT / ".lake/repair-r2"),
            "Output must be owned R2 evidence, never R1/history")
    report, inventory_path, inventory_bytes = Audit().run()
    result_bytes = encoded(report)
    if arguments.check:
        require(output.read_bytes() == result_bytes, "Compact historical applicability packet differs")
        require(inventory_path.read_bytes() == inventory_bytes, "Complete historical binding inventory differs")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        inventory_path.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(result_bytes)
        inventory_path.write_bytes(inventory_bytes)
    print(json.dumps({"status": "PASS", "mode": "check" if arguments.check else "write",
                      "output": output.as_posix(), **ident(result_bytes),
                      "counts": report["counts"]}, separators=(",", ":")))


if __name__ == "__main__":
    main()
