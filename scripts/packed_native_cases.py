"""Independent binary-native fixture specifications and bounded byte capture.

No RMQ algorithm is implemented here. Microcase results are literal arithmetic
facts and instruction/category counts; PQ1 expectations come only from the
original pinned exports. The root-owned exporter serializes declared cells.
The capture subcommand runs the delivered artifact without changing its output.
"""
from __future__ import annotations

import argparse
import base64
import copy
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time
import uuid

sys.dont_write_bytecode = True

ROOT = Path(__file__).resolve().parent.parent
SOURCE_COMMIT = "0e6a00f654abc64f8b68988fa9675b9a839dca2f"
SCHEMA = "native1-binary-cases-v1"
MAX_FILE_BYTES = 134_217_728
CONSUMERS = ["packed-rmq-native.exe", "packed-rmq-native-cpp.exe"]
ORIGINAL_IDS = ["n9-full", "n9-empty", "n9-range", "n9-corrupt", "n9-missing",
                "n12-interior", "n12-same", "n12-adjacent"]
WITNESS_IDS = ["canonical-select-left", "canonical-select-right", "canonical-left-fringe",
               "canonical-right-fringe", "canonical-interior", "canonical-rank-final", "canonical-cross-cell"]
# Direct semantic challenges use the same checks as production preparation.
# The caller requires a successful unchanged check before accepting rejection.
WITNESS_CHALLENGES = {
    "stage": ("canonical-select-left", "canonical occurrence belongs to the wrong actual source stage"),
    "ordinal": ("canonical-cross-cell", "canonical occurrence ordinal/transition mismatch"),
    "transition": ("canonical-cross-cell", "canonical occurrence ordinal/transition mismatch"),
    "pc": ("canonical-cross-cell", "canonical occurrence PC does not fetch the declared load"),
    "load-register": ("canonical-cross-cell", "canonical occurrence PC does not fetch the declared load"),
    "prestate-pc": ("canonical-cross-cell", "canonical occurrence prestate/address disagreement"),
    "prestate-address": ("canonical-cross-cell", "canonical occurrence prestate/address disagreement"),
    "address": ("canonical-cross-cell", "canonical occurrence differs from exact ordered expected read"),
    "reply": ("canonical-cross-cell", "canonical occurrence differs from exact ordered expected read"),
    "memory": ("canonical-cross-cell", "canonical occurrence reply differs from exact loaded memory"),
    "span": ("canonical-cross-cell", "canonical logical span/physical embedding mismatch"),
    "logical-reply": ("canonical-cross-cell", "canonical logical reply does not reconstruct from physical cells"),
    "crossing": ("canonical-cross-cell", "canonical cross-cell witness does not cross two cells"),
    "empty-physical": ("canonical-cross-cell", "empty canonical physical occurrence witness"),
    "missing-second-cell": ("canonical-cross-cell", "canonical logical span physical count mismatch"),
    "oracle": ("canonical-cross-cell", "independent leftmost RMQ witness answer mismatch"),
    "program": ("canonical-cross-cell", "canonical/independent original program identity mismatch"),
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def utc() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="microseconds")


def strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON field: {key}")
        result[key] = value
    return result


def load_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=strict_object)


def encoder():
    path = ROOT / "scripts/packed_native_image.py"
    spec = importlib.util.spec_from_file_location("native1_image_encoder", path)
    if spec is None or spec.loader is None:
        raise ValueError("image encoder unavailable")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def observation(status: str, counts: list[int], reads=()) -> str:
    if len(counts) != 6 or any(n < 0 for n in counts):
        raise ValueError("six independent nonnegative category counts required")
    lines = [status, str(sum(counts)), " ".join(map(str, counts))]
    lines.extend(f"{address} {'none' if value is None else value}" for address, value in reads)
    # Runtime.nativeObservationText always has a final receipt separator,
    # including an empty line when no reads are present.
    return "\n".join(lines[:3]) + "\n" + "\n".join(lines[3:]) + "\n"


def image(width: int, code: list[list[int]], memory=(), n=0, registers=16):
    return {"kind": "literal", "width": width, "inputLength": str(n),
            "registerCount": registers, "code": [[str(x) for x in fields] for fields in code],
            "memory": [str(x) for x in memory]}


def endpoint(width: int, value: int) -> str:
    if value < 0 or value.bit_length() > width:
        raise ValueError("endpoint outside declared word")
    return value.to_bytes((width + 7) // 8, "little").hex()


def native_case(case_id, spec, arguments, stdout, stderr="", exit_code=0, coverage=()):
    return {"id": case_id, "kind": "native", "operation": "exact-cli-observation",
            "consumers": list(CONSUMERS), "image": spec, "arguments": arguments,
            "expectedExit": exit_code, "expectedStdout": stdout, "expectedStderr": stderr,
            "deadlineSeconds": 180, "coverage": list(coverage)}


def query(case_id, spec, status, counts, reads=(), left=0, right=0, fuel=100,
          observe=True, repeat=None, coverage=()):
    width = spec["width"]
    args = ["query", "{image}", endpoint(width, left), endpoint(width, right), str(fuel),
            "1" if observe else "0"]
    if repeat is not None:
        args.append(str(repeat))
    text = observation(status, counts, reads if observe else ()) * (repeat or 1)
    return native_case(case_id, spec, args, text, coverage=coverage)


def draft_cases():
    """Authoring-time case data. Never consume native output as an oracle."""
    cases = []
    smoke = image(168, [[1, 3, 8], [8, 3]])
    cases.append(native_case("load-smoke", smoke, ["load", "{image}"], "loaded 21\n",
                             coverage=["valid binary framing", "word byte count"]))
    cases.append(query("query-smoke", smoke, "halted 8", [0, 1, 0, 0, 0, 1],
                       coverage=["actual entry", "constant", "halt"]))
    cases.append(query("fuel-zero", smoke, "running", [0] * 6, fuel=0,
                       coverage=["zero fuel", "no synthetic steps"]))
    cases.append(query("fuel-one", smoke, "running", [0, 1, 0, 0, 0, 0], fuel=1,
                       coverage=["fuel boundary", "partial running result"]))
    cases.append(query("missing-fetch", image(168, []), "running", [0] * 6,
                       coverage=["missing fetch leaves status and counts unchanged"]))
    left, right = (1 << 167) + 5, (1 << 166) + 1
    cases.append(query("endpoint-order-168", image(168, [[3, 1, 3, 0, 1], [8, 3]]),
                       f"halted {(1 << 166) + 4}", [0, 0, 1, 0, 0, 1], left=left, right=right,
                       coverage=["168-bit endpoints", "left/right ABI order", "subtraction"]))
    value = (1 << 175) + 167
    cases.append(query("memory-identity-176", image(176, [[1, 3, 2], [0, 4, 3], [8, 4]],
                                                  [17, 23, value], n=3),
                       f"halted {value}", [1, 1, 0, 0, 0, 1], [(2, value)],
                       coverage=["176-bit cells", "exact loaded memory", "physical indexed read"]))
    v0, v1 = (1 << 167) + 3, (1 << 166) + 5
    ordered = image(168, [[1, 3, 1], [0, 4, 3], [1, 3, 0], [0, 5, 3],
                          [1, 3, 1], [0, 6, 3], [8, 6]], [v0, v1], n=2)
    reads = [(1, v1), (0, v0), (1, v1)]
    cases.append(query("ordered-repeated-reads", ordered, f"halted {v1}", [3, 3, 0, 0, 0, 1], reads,
                       coverage=["read order", "read multiplicity", "reply values"]))
    cases.append(query("quiet-read-projection", ordered, f"halted {v1}", [3, 3, 0, 0, 0, 1], reads,
                       observe=False, coverage=["read log erasure", "unchanged category counts"]))
    cases.append(query("repeat-owned-image", ordered, f"halted {v1}", [3, 3, 0, 0, 0, 1], reads,
                       repeat=3, coverage=["single loaded image", "repeat query ownership", "immutable store"]))
    mixed_value = (1 << 168) + 7
    mixed = image(176, [[1, 3, 0], [0, 4, 3], [2, 5, 4], [1, 6, 1],
                        [3, 0, 7, 5, 6], [4, 0, 8, 5, 7], [7, 8, 9], [5, 8], [8, 7], [8, 0]],
                  [mixed_value], n=1)
    cases.append(query("all-six-categories", mixed, f"halted {mixed_value + 1}",
                       [1, 3, 1, 1, 2, 1], [(0, mixed_value)],
                       coverage=["all six categories", "move", "comparison", "not-taken branch", "jump"]))
    cases.append(query("taken-branch", image(168, [[7, 0, 2], [8, 1], [8, 2]], n=9),
                       "halted 9", [0, 0, 0, 0, 1, 1], left=0, right=7,
                       coverage=["taken branch", "initial n register"]))
    cases.append(query("jump-register", image(168, [[1, 3, 2], [6, 3], [8, 0]]),
                       f"halted {left}", [0, 1, 0, 0, 1, 1], left=left,
                       coverage=["indirect branch", "full-width packet"]))
    cases.append(query("high-address-missing", image(168, [[1, 3, left], [0, 4, 3], [8, 4]], [3]),
                       "fault", [1, 1, 0, 0, 0, 0], [(left, None)],
                       coverage=["address beyond usize", "no address truncation", "failed attempted load"]))
    cases.append(query("missing-memory", image(168, [[0, 3, 0], [8, 3]]),
                       "fault", [1, 0, 0, 0, 0, 0], [(0, None)], coverage=["missing memory fault"]))
    cases.append(query("jump-missing-fetch", image(168, [[5, left]]), "running", [0, 0, 0, 0, 1, 0],
                       coverage=["high canonical PC", "missing fetch after branch"]))
    cases.append(query("destination-fault", image(168, [[1, 3, 1], [8, 0]], registers=3),
                       "fault", [0, 1, 0, 0, 0, 0], coverage=["finite register destination guard"]))
    cases.append(query("absent-source-register", image(168, [[8, 999]], registers=3),
                       "halted 0", [0, 0, 0, 0, 0, 1], coverage=["total zero source-register policy"]))
    pc_code = [[5, 255]] + [[8, 0]] * 254 + [[1, 0, 1]]
    cases.append(query("pc-overflow", image(8, pc_code, registers=3), "fault", [0, 1, 0, 0, 1, 0],
                       coverage=["word-width PC increment overflow"]))
    top = (1 << 4095) + 5
    cases.append(query("supported-width-4096", image(4096, [[8, 0]], registers=3),
                       f"halted {top}", [0, 0, 0, 0, 0, 1], left=top,
                       coverage=["supported host width maximum", "512-byte endpoint"]))
    # Each result below is the stated arithmetic expression, not an interpreter
    # run. Three setup/operation instructions and one halt fix the counts.
    x, y = (1 << 160) + (1 << 64) + 255, (1 << 128) + 17
    operations = [
        ("add", 0, x, y, x + y), ("sub", 1, x, y, x - y),
        ("mul", 2, (1 << 80) + 1, (1 << 64) + 3, ((1 << 80) + 1) * ((1 << 64) + 3)),
        ("div", 3, x, y, x // y), ("mod", 4, x, y, x % y),
        ("shl", 5, (1 << 128) + 3, 31, ((1 << 128) + 3) << 31),
        ("shr", 6, x, 65, x >> 65), ("band", 7, x, y, x & y),
        ("bor", 8, x, y, x | y), ("bxor", 9, x, y, x ^ y)]
    for name, tag, a, b, result in operations:
        spec = image(176, [[1, 3, a], [1, 4, b], [3, tag, 5, 3, 4], [8, 5]])
        cases.append(query("arithmetic-" + name, spec, f"halted {result}", [0, 2, 1, 0, 0, 1],
                           coverage=["multi-limb " + name, "primitive operation count"]))
    faults = [("underflow", 1, 1, 2), ("zero-divisor", 3, x, 0), ("zero-remainder", 4, x, 0),
              ("add-overflow", 0, (1 << 168) - 1, 1),
              ("mul-overflow", 2, 1 << 100, 1 << 100),
              ("shift-overflow", 5, 1 << 167, 1),
              ("left-shift-width", 5, 1, 168), ("right-shift-width", 6, x, 168),
              ("hostile-shift-count", 5, 1, 1 << 167)]
    for name, tag, a, b in faults:
        spec = image(168, [[1, 3, a], [1, 4, b], [3, tag, 5, 3, 4], [8, 5]])
        cases.append(query("fault-" + name, spec, "fault", [0, 2, 1, 0, 0, 0],
                           coverage=["checked " + name, "fault differs from raw unsafe arithmetic"]))
    for name, tag, a, b, result in [("lt-true", 0, y, x, 1), ("lt-false", 0, x, y, 0),
                                   ("le-equal", 1, x, x, 1), ("eq-true", 2, x, x, 1),
                                   ("eq-false", 2, x, y, 0)]:
        spec = image(176, [[1, 3, a], [1, 4, b], [4, tag, 5, 3, 4], [8, 5]])
        cases.append(query("comparison-" + name, spec, f"halted {result}", [0, 2, 0, 1, 0, 1],
                           coverage=["multi-limb comparison " + name]))
    return cases


def read_pq1_source(fixture_id: str):
    if fixture_id not in ORIGINAL_IDS:
        raise ValueError("unknown original PQ1 fixture")
    directory = ROOT / "native/packed-rmq/fixtures"
    manifest = load_json(directory / "manifest.json")
    if manifest["schema"] != "native1-fixtures-v1" or manifest["sourceCommit"] != SOURCE_COMMIT:
        raise ValueError("original fixture source identity")
    pins = {entry["name"]: entry["sha256"] for entry in manifest["files"]}
    raw_fixture = (directory / (fixture_id + ".fixture")).read_bytes()
    raw_expected = (directory / (fixture_id + ".expected")).read_bytes()
    if sha(raw_fixture) != pins[fixture_id + ".fixture"] or sha(raw_expected) != pins[fixture_id + ".expected"]:
        raise ValueError("original fixture/expectation changed")
    header, *cells = raw_fixture.decode("ascii").splitlines()
    n, left, right, width, fuel = map(int, header.split())
    memory = [int(line) for line in cells if line]
    packet_steps, categories, *receipt_lines = raw_expected.decode("ascii").splitlines()
    packet, steps = packet_steps.split()
    counts = list(map(int, categories.split()))
    if sum(counts) != int(steps):
        raise ValueError("original six categories do not equal steps")
    reads = []
    for line in receipt_lines:
        if not line:
            continue
        address, reply = line.split()
        reads.append((int(address), None if reply == "none" else int(reply)))
    if packet == "none":
        if fixture_id != "n9-missing" or reads != [(0, None)]:
            raise ValueError("unproved raw no-result status conversion")
        status = "fault"  # The actual raw missing-load rule faults on this sole failed read.
    else:
        status = "halted " + packet
    image_spec = {"kind": "pq1", "fixture": fixture_id, "width": width,
                  "sourceCommit": SOURCE_COMMIT, "programSha256": manifest["programSha256"],
                  "fixtureSha256": sha(raw_fixture), "expectedSha256": sha(raw_expected)}
    return image_spec, (n, left, right, width, fuel, memory), status, counts, reads


def pq1_cases():
    cases = []
    for fixture_id in ORIGINAL_IDS:
        spec, (_, left, right, _, fuel, _), status, counts, reads = read_pq1_source(fixture_id)
        cases.append(query("pq1-" + fixture_id, spec, status, counts, reads, left, right, fuel,
                           coverage=["original exported PQ1 " + fixture_id, "full ordered original observations"]))
    spec, (_, left, right, _, fuel, _), status, counts, reads = read_pq1_source("n9-full")
    cases.append(query("pq1-n9-full-quiet", spec, status, counts, reads, left, right, fuel,
                       observe=False, coverage=["canonical read-log erasure"]))
    return cases


def rejection_cases():
    cases = []
    base = image(169, [[1, 3, 8], [8, 3]], [17], n=1)
    malformed = ["magic", "version", "empty-file", "truncated-header", "truncated-word",
                 "trailing-byte", "scalar-bad-prefix", "scalar-zero-digits", "scalar-nonminimal",
                 "width-zero", "width-over-limit", "input-length-overflow", "register-cap",
                 "register-word-overflow", "instruction-cap", "memory-cap", "field-cap",
                 "word-length-over", "word-length-under", "word-padding", "unknown-instruction",
                 "unknown-arithmetic", "unknown-comparison", "missing-operand", "empty-instruction"]
    for mutation in malformed:
        spec = {"kind": "malformed", "base": base, "mutation": mutation}
        cases.append(native_case("reject-image-" + mutation, spec, ["load", "{image}"], "",
                                 "invalid or unsupported binary image\n", 1,
                                 ["binary rejection", mutation]))
    cases.append(native_case("reject-file-cap", {"kind": "oversized", "bytes": MAX_FILE_BYTES + 1},
                             ["load", "{image}"], "", "image byte limit\n", 1,
                             ["host file bound before allocation"]))
    smoke = image(168, [[8, 0]], registers=3)
    normal = ["query", "{image}", endpoint(168, 0), endpoint(168, 0), "1", "1"]
    invalid_args = [("odd-hex", 2, "0", "invalid endpoint hex"),
                    ("nonhex", 2, "zz", "invalid endpoint hex"),
                    ("hex-over-limit", 2, "00" * 513, "invalid endpoint hex"),
                    ("empty-left", 2, "", "noncanonical query word"),
                    ("short-left", 2, "00", "noncanonical query word"),
                    ("long-right", 3, "00" * 22, "noncanonical query word"),
                    ("negative-fuel", 4, "-1", "invalid fuel"),
                    ("empty-fuel", 4, "", "invalid fuel"),
                    ("overflow-fuel", 4, "18446744073709551616", "invalid fuel"),
                    ("fuel-cap", 4, "1000001", "query host limit"),
                    ("reads-value", 5, "2", "reads must be 0 or 1")]
    for name, index, value, reason in invalid_args:
        arguments = normal.copy()
        arguments[index] = value
        cases.append(native_case("reject-query-" + name, smoke, arguments, "", reason + "\n", 1,
                                 ["CLI/API rejection", name]))
    for name, value, reason in [("zero", "0", "repeat must be between 1 and 16"),
                                ("large", "17", "repeat must be between 1 and 16"),
                                ("negative", "-1", "invalid repeat")]:
        cases.append(native_case("reject-repeat-" + name, smoke, normal + [value], "", reason + "\n", 1,
                                 ["bounded repeated ownership", name]))
    padded = ["query", "{image}", (b"\0" * 21 + b"\x80").hex(), endpoint(169, 0), "1", "1"]
    cases.append(native_case("reject-query-padding", base, padded, "", "noncanonical query word\n", 1,
                             ["endpoint high padding before use"]))
    small_regs = {"kind": "small-register-bank", "width": 168}
    cases.append(native_case("load-small-register-bank", small_regs, ["load", "{image}"],
                             "loaded 21\n", coverage=["image validity differs from query register minimum"]))
    cases.append(native_case("reject-query-register-minimum", small_regs, normal, "",
                             "unsupported query domain\n", 1, ["query register minimum before allocation"]))
    cases.append(query("repeat-maximum", smoke, "halted 0", [0, 0, 0, 0, 0, 1], repeat=16,
                       coverage=["maximum repeated ownership", "all 16 independent observations"]))
    return cases


def source_cases():
    runtime = "RMQ/Core/WordRAM/Native/Runtime.lean"
    entry = "RMQ/Core/WordRAM/Native/Entry.lean"
    def mutation(case_id, source, anchor, replacement, proof_line, diagnostic, surface):
        return {"id": case_id, "kind": "source-mutation", "operation": "lean-type-rejection",
                "source": source, "anchor": anchor, "replacement": replacement,
                "proofLine": proof_line, "expectedDiagnostic": diagnostic,
                "expectedExit": "nonzero", "surface": surface, "deadlineSeconds": 180}
    return [
        mutation("source-core-fuel", runtime,
                 "  LimbMachine.runThin observeReads image.width image.memory image.code fuel",
                 "  LimbMachine.runThin observeReads image.width image.memory image.code 0",
                 "  LimbMachine.runThin_projection observeReads image.width image.memory image.code fuel",
                 "type mismatch", "nativeCore_source"),
        mutation("source-loader-bytes", entry,
                 "  match BinaryCursor.decodeSupported nativeLimits bytes with",
                 "  match BinaryCursor.decodeSupported nativeLimits ByteArray.empty with",
                 '      | none => .error "invalid or unsupported binary image" := by',
                 "unsolved goals", "nativeLoadEntry_source"),
        mutation("source-query-order", entry,
                 "  nativeEvaluate image left right fuel observeReads",
                 "  nativeEvaluate image right left fuel observeReads",
                 "  nativeEvaluate_source image left right fuel observeReads h",
                 "type mismatch", "nativeQueryEntry_source"),
        {"id": "stale-source-rejection", "kind": "source-pin", "operation": "source-identity-rejection",
         "source": runtime, "append": "\n-- native binary source-pin positive control\n",
         "expectedExit": "rejection", "expectedDiagnostic": "stale native source: " + runtime,
         "surface": "Assert-BinaryBuildIdentity", "deadlineSeconds": 30}]


def ffi_mutation_case():
    left, right = (1 << 167) + 5, (1 << 166) + 1
    base = query("source-ffi-order", image(168, [[3, 1, 3, 0, 1], [8, 3]]),
                 f"halted {(1 << 166) + 4}", [0, 0, 1, 0, 0, 1], left=left, right=right,
                 coverage=["actual C shim argument marshaling", "independent asymmetric arithmetic challenge"])
    base.update({"kind": "ffi-mutation", "operation": "rebuild-shim-and-challenge",
                 "source": "native/packed-rmq/native_shim.c",
                 "anchor": "        copy_bytes(left, left_length), copy_bytes(right, right_length), lean_usize_to_nat(fuel), reads);",
                 "replacement": "        copy_bytes(right, right_length), copy_bytes(left, left_length), lean_usize_to_nat(fuel), reads);",
                 "mutantExpectedExit": 0, "mutantExpectedStdout": observation("fault", [0, 0, 1, 0, 0, 0]),
                 "mutantExpectedStderr": "", "compileDeadlineSeconds": 300,
                 "surface": "independent asymmetric subtraction observation rejects swapped C arguments"})
    return base


def read_witness_source(path: Path):
    fixture = load_json(path)
    if fixture["schema"] != "native1-canonical-witness-v1" or fixture["id"] not in WITNESS_IDS:
        raise ValueError("unknown canonical witness schema/identity")
    if path.name != fixture["id"] + ".fixture":
        raise ValueError("canonical witness file identity")
    program = fixture["program"]
    if program["path"] != "program.txt.gz":
        raise ValueError("canonical witness program source path")
    original = load_json(ROOT / "native/packed-rmq/fixtures/manifest.json")
    if program["uncompressedSha256"] != original["programSha256"]:
        raise ValueError("canonical/independent original program identity mismatch")
    # The baseline exporter receipt proves its actual plaintext equals this
    # already committed gzip's decompressed bytes. Replays consume that exact
    # gzip below; a task-local second plaintext is not a durable input.
    sources = ["RMQ/Core/WordRAM/Native/Witnesses.lean", "RMQ/Core/WordRAM/Native/WitnessExport.lean"]
    spec = {"kind": "canonical-witness", "width": fixture["width"],
            "fixturePath": path.resolve().relative_to(ROOT).as_posix(),
            "fixtureSha256": sha(path.read_bytes()), "programSha256": original["programSha256"],
            "sourcePins": [{"path": source, "sha256": sha((ROOT / source).read_bytes())} for source in sources]}
    validate_witness_expectation(fixture)
    return spec, fixture


def validate_witness_expectation(fixture):
    original = load_json(ROOT / "native/packed-rmq/fixtures/manifest.json")
    if fixture["program"]["uncompressedSha256"] != original["programSha256"]:
        raise ValueError("canonical/independent original program identity mismatch")
    evidence, expected = fixture["witnessEvidence"], fixture["expected"]
    values = list(map(int, evidence["input"]))
    left, right, n = int(fixture["left"]), int(fixture["right"]), int(fixture["inputLength"])
    if len(values) != n or not 0 <= left < right <= n:
        raise ValueError("canonical witness input/range")
    answer = min(range(left, right), key=lambda index: (values[index], index))
    if answer != int(evidence["expectedLeftmost"]) or expected["status"] != f"halted {answer + 1}":
        raise ValueError("independent leftmost RMQ witness answer mismatch")
    counts = expected["categories"]
    if len(counts) != 6 or any(type(value) is not int or value < 0 for value in counts):
        raise ValueError("canonical category shape")
    if sum(counts) != expected["steps"] or counts[0] != len(expected["reads"]):
        raise ValueError("canonical category/receipt accounting")


def witness_cases(directory: Path):
    cases = []
    for case_id in WITNESS_IDS:
        spec, fixture = read_witness_source(directory / (case_id + ".fixture"))
        expected = fixture["expected"]
        receipts = [(int(item["address"]), None if item["reply"] is None else int(item["reply"]))
                    for item in expected["reads"]]
        cases.append(query(case_id, spec, expected["status"], expected["categories"], receipts,
                           int(fixture["left"]), int(fixture["right"]), fixture["fuel"],
                           coverage=["checked canonical stage occurrence", case_id,
                                     "independent leftmost integer-range answer", "exact raw query receipts/categories"]))
    return cases


def inspect_witness_occurrence(fixture, code, memory):
    occurrence = fixture["witnessEvidence"]["occurrence"]
    expected_stages = {"canonical-select-left": "select-left", "canonical-select-right": "select-right",
                       "canonical-left-fringe": "left-fringe-window", "canonical-right-fringe": "right-fringe-window",
                       "canonical-interior": "interior", "canonical-rank-final": "final-rank"}
    if fixture["id"] in expected_stages and occurrence["stage"] != expected_stages[fixture["id"]]:
        raise ValueError("canonical occurrence belongs to the wrong actual source stage")
    physical = occurrence["physical"]
    if not physical:
        raise ValueError("empty canonical physical occurrence witness")
    last_transition = -1
    for offset, item in enumerate(physical):
        ordinal, transition, pc = item["physicalOrdinal"], item["transitionIndex"], int(item["pc"])
        address, reply = int(item["address"]), None if item["reply"] is None else int(item["reply"])
        if ordinal != occurrence["physicalOrdinal"] + offset or not last_transition < transition < fixture["expected"]["steps"]:
            raise ValueError("canonical occurrence ordinal/transition mismatch")
        last_transition = transition
        if fixture["expected"]["reads"][ordinal] != {"address": str(address), "reply": None if reply is None else str(reply)}:
            raise ValueError("canonical occurrence differs from exact ordered expected read")
        if not 0 <= address < len(memory) or memory[address] != reply:
            raise ValueError("canonical occurrence reply differs from exact loaded memory")
        registers, prestate = item["loadRegisters"], item["prestate"]
        if not 0 <= pc < len(code) or code[pc] != [0, registers["destination"], registers["address"]]:
            raise ValueError("canonical occurrence PC does not fetch the declared load")
        if prestate["status"] != "running" or int(prestate["pc"]) != pc or int(prestate["addressValue"]) != address:
            raise ValueError("canonical occurrence prestate/address disagreement")
    span, logical = occurrence["span"], occurrence["logicalReply"]
    if span is not None and logical is not None:
        width, length, position = span["width"], int(span["length"]), int(span["absolutePosition"])
        if width != fixture["width"] or position != 174 * width + int(span["position"]) or span["offset"] != position % width:
            raise ValueError("canonical logical span/physical embedding mismatch")
        if length < 0 or length > width or logical["bitLength"] != length:
            raise ValueError("canonical logical field width mismatch")
        expected_cells = 0 if length == 0 else 1 + (span["offset"] + length - 1) // width
        if len(physical) != expected_cells:
            raise ValueError("canonical logical span physical count mismatch")
        combined = sum(int(item["reply"]) << (index * width) for index, item in enumerate(physical))
        actual_value = (combined >> span["offset"]) & ((1 << length) - 1)
        if actual_value != int(logical["value"]):
            raise ValueError("canonical logical reply does not reconstruct from physical cells")
        if any(int(item["address"]) != position // width + index for index, item in enumerate(physical)):
            raise ValueError("canonical span uses wrong physical cells")
    if fixture["id"] == "canonical-cross-cell":
        if span is None or logical is None or not occurrence["crossCell"] or len(physical) != 2 or not span["width"] < span["offset"] + int(span["length"]):
            raise ValueError("canonical cross-cell witness does not cross two cells")


def read_pinned_program(program_sha256):
    with gzip.open(ROOT / "native/packed-rmq/fixtures/program.txt.gz", "rb") as stream:
        raw = stream.read(50_000_001)
    if len(raw) > 50_000_000 or sha(raw) != program_sha256:
        raise ValueError("original program source changed")
    return [[int(x) for x in line.split()] for line in raw.decode("ascii").splitlines() if line]


def witness_challenge(spec, mutation: str, output: Path):
    case_id, diagnostic = WITNESS_CHALLENGES[mutation]
    current, original = read_witness_source(ROOT / spec["fixturePath"])
    if spec != current or original["id"] != case_id:
        raise ValueError("pinned witness challenge source changed")
    code = read_pinned_program(spec["programSha256"])
    inspect_witness_occurrence(original, code, list(map(int, original["memory"])))
    # This marker is emitted only after every unchanged production check passes.
    print("NATIVE1-WITNESS-BASELINE PASS " + case_id, flush=True)
    changed = copy.deepcopy(original)
    occurrence = changed["witnessEvidence"]["occurrence"]
    first = occurrence["physical"][0]
    target = first
    if mutation == "stage": target, key, value = occurrence, "stage", "incorrect-stage"
    elif mutation == "ordinal": key, value = "physicalOrdinal", first["physicalOrdinal"] + 1
    elif mutation == "transition": key, value = "transitionIndex", changed["expected"]["steps"]
    elif mutation == "pc": key, value = "pc", str(len(code))
    elif mutation == "load-register": target, key, value = first["loadRegisters"], "destination", first["loadRegisters"]["destination"] + 1
    elif mutation == "prestate-pc": target, key, value = first["prestate"], "pc", str(int(first["pc"]) + 1)
    elif mutation == "prestate-address": target, key, value = first["prestate"], "addressValue", str(int(first["address"]) + 1)
    elif mutation == "address": key, value = "address", str(int(first["address"]) + 1)
    elif mutation == "reply": key, value = "reply", str(int(first["reply"]) + 1)
    elif mutation == "memory": target, key, value = changed["memory"], int(first["address"]), str(int(first["reply"]) + 1)
    elif mutation == "span": target, key, value = occurrence["span"], "absolutePosition", str(int(occurrence["span"]["absolutePosition"]) + 1)
    elif mutation == "logical-reply": target, key, value = occurrence["logicalReply"], "value", str(int(occurrence["logicalReply"]["value"]) + 1)
    elif mutation == "crossing": target, key, value = occurrence, "crossCell", False
    elif mutation == "empty-physical": target, key, value = occurrence, "physical", []
    elif mutation == "missing-second-cell": target, key, value = occurrence, "physical", occurrence["physical"][:1]
    elif mutation == "oracle": target, key, value = changed["witnessEvidence"], "expectedLeftmost", str(int(changed["witnessEvidence"]["expectedLeftmost"]) + 1)
    elif mutation == "program": target, key, value = changed["program"], "uncompressedSha256", "0" * 64
    else: raise ValueError("unknown witness semantic mutation")
    before = target[key]
    target[key] = value
    if changed == original: raise ValueError("vacuous witness semantic mutation")
    output.write_text(json.dumps(changed, separators=(",", ":")) + "\n", encoding="utf-8", newline="\n")
    if load_json(output) != changed: raise ValueError("witness mutation serialization mismatch")
    print(json.dumps({"mutation": mutation, "case": case_id, "oldValue": before, "newValue": value,
                      "baselineFixtureSha256": spec["fixtureSha256"], "mutatedFixtureSha256": sha(output.read_bytes()),
                      "expectedDiagnostic": diagnostic}, separators=(",", ":")), flush=True)
    validate_witness_expectation(changed)
    inspect_witness_occurrence(changed, code, list(map(int, changed["memory"])))
    raise ValueError("witness semantic mutation unexpectedly accepted")


class IndependentImageReader:
    """Separate bounded framing checker, used to inspect exporter output.

    It reads offsets into the original bytes and compares each decoded cell to
    the literal declaration. It does not execute instructions or create expected
    observations. Header/word spans also identify exact malformed mutations.
    """
    def __init__(self, data):
        if len(data) > MAX_FILE_BYTES:
            raise ValueError("independent reader file cap")
        self.data, self.offset, self.spans = data, 0, {}

    def scalar(self, label):
        start, digits = self.offset, 0
        while self.offset < len(self.data) and self.data[self.offset] == 1:
            digits += 1
            self.offset += 1
            if digits > len(self.data):
                raise ValueError("prefix exceeds file")
        if not digits or self.offset >= len(self.data) or self.data[self.offset] != 0:
            raise ValueError("noncanonical scalar prefix")
        self.offset += 1
        end = self.offset + digits
        if end > len(self.data):
            raise ValueError("truncated scalar")
        value = int.from_bytes(self.data[self.offset:end], "little")
        if max(1, (value.bit_length() + 7) // 8) != digits:
            raise ValueError("nonminimal scalar digits")
        self.offset = end
        if label:
            self.spans[label] = (start, end)
        return value

    def word(self, width, expected, label):
        length = self.scalar(label + "-length" if label else None)
        count = (width + 7) // 8
        end = self.offset + length
        if length != count or end > len(self.data):
            raise ValueError("word length mismatch")
        value = int.from_bytes(self.data[self.offset:end], "little")
        if value.bit_length() > width or value != expected:
            raise ValueError("declared cell/value/padding mismatch")
        if label:
            self.spans[label] = (self.offset, end)
        self.offset = end

    def compare(self, width, n, registers, code, memory):
        if self.data[:5] != b"RMQN\x01":
            raise ValueError("binary magic/version")
        self.offset = 5
        if [self.scalar("width"), self.scalar("inputLength"), self.scalar("registerCount")] != [width, n, registers]:
            raise ValueError("declared header mismatch")
        if self.scalar("instruction-count") != len(code):
            raise ValueError("declared code count mismatch")
        for index, fields in enumerate(code):
            label = "first-fields" if index == 0 else None
            if self.scalar(label) != len(fields):
                raise ValueError("declared instruction field count mismatch")
            for field, value in enumerate(fields):
                self.word(width, value, "first-word" if index == field == 0 else None)
        if self.scalar("memory-count") != len(memory):
            raise ValueError("declared memory count mismatch")
        for index, value in enumerate(memory):
            self.word(width, value, "first-memory" if index == 0 else None)
        if self.offset != len(self.data):
            raise ValueError("trailing image bytes")
        return self.spans


def malformed_image(base, mutation):
    module = encoder()
    width, n, registers = base["width"], int(base["inputLength"]), base["registerCount"]
    code = [[int(x) for x in fields] for fields in base["code"]]
    memory = [int(x) for x in base["memory"]]
    data = module.encode_image(width, n, registers, code, memory)
    spans = IndependentImageReader(data).compare(width, n, registers, code, memory)
    def replace(label, replacement):
        start, end = spans[label]
        return data[:start] + replacement + data[end:]
    header_changes = {"width-zero": ("width", 0), "width-over-limit": ("width", 4097),
                      "input-length-overflow": ("inputLength", 1 << width),
                      "register-cap": ("registerCount", 65537),
                      "instruction-cap": ("instruction-count", 1000001),
                      "memory-cap": ("memory-count", 1000001), "field-cap": ("first-fields", 6),
                      "word-length-over": ("first-word-length", (width + 7) // 8 + 1),
                      "word-length-under": ("first-word-length", (width + 7) // 8 - 1)}
    if mutation in header_changes:
        label, value = header_changes[mutation]
        return replace(label, module.scalar(value))
    if mutation == "magic": return b"BAD!" + data[4:]
    if mutation == "version": return data[:4] + b"\x02" + data[5:]
    if mutation == "empty-file": return b""
    if mutation == "truncated-header": return data[:7]
    if mutation == "truncated-word": return data[:spans["first-word"][1] - 1]
    if mutation == "trailing-byte": return data + b"\x00"
    if mutation == "scalar-bad-prefix": return replace("width", b"\x02\x00\xa9")
    if mutation == "scalar-zero-digits": return replace("width", b"\x00")
    if mutation == "scalar-nonminimal": return replace("width", b"\x01\x01\x00\xa9\x00")
    if mutation == "word-padding":
        a, b = spans["first-memory"]
        return data[:b-1] + b"\x80" + data[b:]
    if mutation == "register-word-overflow":
        return b"RMQN\x01" + module.scalar(1) + module.scalar(0) + module.scalar(3) + module.scalar(0) * 2
    changed = {"unknown-instruction": [[99]], "unknown-arithmetic": [[3, 10, 3, 0, 1]],
               "unknown-comparison": [[4, 3, 3, 0, 1]], "missing-operand": [[0, 3]],
               "empty-instruction": [[]]}
    if mutation in changed:
        fields = changed[mutation][0]
        return (b"RMQN\x01" + module.scalar(width) + module.scalar(n) + module.scalar(registers)
                + module.scalar(1) + module.scalar(len(fields))
                + b"".join(module.word(width, x) for x in fields) + module.scalar(0))
    raise ValueError("unknown malformed byte operation")


def materialize_image(spec: dict, output: Path) -> dict:
    module = encoder()
    output.parent.mkdir(parents=True, exist_ok=True)
    if spec["kind"] == "malformed":
        data = malformed_image(spec["base"], spec["mutation"])
        output.write_bytes(data)
        return {"imageSha256": sha(data), "imageBytes": len(data), "mutation": spec["mutation"],
                "independentBaseInspection": True}
    if spec["kind"] == "oversized":
        if spec["bytes"] != MAX_FILE_BYTES + 1:
            raise ValueError("exact file cap mutation")
        with output.open("wb") as stream:
            stream.seek(spec["bytes"] - 1)
            stream.write(b"\0")
        with output.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest().upper()
        return {"imageSha256": digest, "imageBytes": output.stat().st_size, "mutation": "file-byte-cap"}
    if spec["kind"] == "small-register-bank":
        width, n, registers, code, memory = spec["width"], 0, 1, [], []
        data = b"RMQN\x01" + module.scalar(width) + module.scalar(n) + module.scalar(registers) + module.scalar(0) * 2
        IndependentImageReader(data).compare(width, n, registers, code, memory)
        output.write_bytes(data)
        return {"imageSha256": sha(data), "imageBytes": len(data), "width": width,
                "independentImageInspection": True}
    if spec["kind"] == "literal":
        width, n, registers = spec["width"], int(spec["inputLength"]), spec["registerCount"]
        code = [[int(x) for x in fields] for fields in spec["code"]]
        memory = [int(x) for x in spec["memory"]]
    elif spec["kind"] in ("pq1", "canonical-witness"):
        witness = None
        if spec["kind"] == "pq1":
            current, header, _, _, _ = read_pq1_source(spec["fixture"])
            n, _, _, width, _, memory = header
            registers = 8271
        else:
            current, witness = read_witness_source(ROOT / spec["fixturePath"])
            width, n, registers = witness["width"], int(witness["inputLength"]), witness["registerCount"]
            memory = list(map(int, witness["memory"]))
        if current != spec:
            raise ValueError("pinned independent fixture contract changed")
        code = read_pinned_program(spec["programSha256"])
        if witness is not None:
            inspect_witness_occurrence(witness, code, memory)
    else:
        raise ValueError("unsupported image producer kind")
    data = module.encode_image(width, n, registers, code, memory)
    IndependentImageReader(data).compare(width, n, registers, code, memory)
    output.write_bytes(data)
    return {"imageSha256": sha(data), "imageBytes": len(data), "width": width,
            "instructions": len(code), "memoryWords": len(memory),
            "declaredNumericWords": sum(map(len, code)) + len(memory), "independentImageInspection": True}


def capture(executable: Path, arguments: list[str], scratch: Path, deadline: float, limit: int) -> int:
    """Capture raw streams without the shared line reader's empty-line erasure.

    This process and its native descendant remain inside the caller's existing
    owned job/process group. The native deadline/output cap is also checked
    while it runs. The caller must reject every incomplete flag in the JSON.
    """
    if deadline <= 0 or not 0 < limit <= 4_194_304:
        raise ValueError("capture limits")
    scratch = scratch.resolve()
    if not scratch.is_relative_to(ROOT / ".lake/native1"):
        raise ValueError("capture scratch outside task cache")
    scratch.mkdir(parents=True, exist_ok=True)
    stem = "native-capture-" + uuid.uuid4().hex
    out_path, err_path = scratch / (stem + ".stdout"), scratch / (stem + ".stderr")
    started = utc()
    watch = time.monotonic()
    timed_out = output_limit = False
    result = None
    process = None
    try:
        with out_path.open("wb") as out, err_path.open("wb") as err:
            process = subprocess.Popen([str(executable), *arguments], stdout=out, stderr=err)
            while process.poll() is None:
                if time.monotonic() - watch >= deadline:
                    timed_out = True
                    process.kill()
                    break
                if out_path.stat().st_size + err_path.stat().st_size > limit:
                    output_limit = True
                    process.kill()
                    break
                time.sleep(0.02)
            process.wait(timeout=10)
        size = out_path.stat().st_size + err_path.stat().st_size
        output_limit = output_limit or size > limit
        stdout = out_path.read_bytes() if not output_limit else b""
        stderr = err_path.read_bytes() if not output_limit else b""
        result = {"schema": "native1-raw-process-v1", "startedUtc": started,
                  "completedUtc": utc(), "durationSeconds": time.monotonic() - watch,
                  "deadlineSeconds": deadline, "outputLimitBytes": limit,
                  "executable": str(executable), "arguments": arguments,
                  "exitCode": process.returncode, "timedOut": timed_out,
                  "outputLimitExceeded": output_limit,
                  "stdoutBase64": base64.b64encode(stdout).decode("ascii"),
                  "stderrBase64": base64.b64encode(stderr).decode("ascii")}
    finally:
        if process is not None and process.poll() is None:
            process.kill()
            process.wait(timeout=10)
        for path in (out_path, err_path):
            if path.parent.resolve() != scratch or not path.name.startswith(stem):
                raise ValueError("capture cleanup path escaped owned files")
            path.unlink(missing_ok=True)
    print(json.dumps(result, separators=(",", ":")))
    return 124 if timed_out or output_limit else 0


def mutate_property(path: Path, case_id: str, field_path: str, action: str, value, output: Path):
    """Change only one JSON property span, independently check resulting object.

    Empty case selects a top-level field. Dotted paths descend into image specs.
    The original object comparison proves that no other field was reformatted
    or semantically changed; raw prefix/suffix stay byte-for-byte identical.
    """
    raw = path.read_text(encoding="utf-8")
    original = json.loads(raw, object_pairs_hook=strict_object)
    expected = json.loads(raw, object_pairs_hook=strict_object)
    decoder = json.JSONDecoder(object_pairs_hook=strict_object)
    if case_id:
        selected = [case for case in expected["cases"] if case["id"] == case_id]
        if len(selected) != 1:
            raise ValueError("mutation case selector")
        target = selected[0]
        marker = '{"id":' + json.dumps(case_id) + ','
        start = raw.find(marker)
        if start < 0 or raw.find(marker, start + 1) >= 0:
            raise ValueError("mutation case span not unique")
    else:
        target, start = expected, raw.index("{")
    keys = field_path.split(".")
    for key in keys[:-1]:
        target = target[int(key)] if isinstance(target, list) else target[key]

    def properties(offset):
        if raw[offset] == "[":
            pos, index = offset + 1, 0
            while True:
                while raw[pos].isspace(): pos += 1
                if raw[pos] == "]": return
                value_start = pos
                _, pos = decoder.raw_decode(raw, pos)
                value_end = pos
                while raw[pos].isspace(): pos += 1
                yield str(index), value_start, value_start, value_end, pos
                if raw[pos] == "]": return
                if raw[pos] != ",": raise ValueError("array separator")
                pos, index = pos + 1, index + 1
        if raw[offset] != "{":
            raise ValueError("mutation field parent not object")
        pos = offset + 1
        while True:
            while raw[pos].isspace(): pos += 1
            if raw[pos] == "}": return
            key_start = pos
            key, pos = decoder.raw_decode(raw, pos)
            while raw[pos].isspace(): pos += 1
            if raw[pos] != ":": raise ValueError("property colon")
            pos += 1
            while raw[pos].isspace(): pos += 1
            value_start = pos
            _, pos = decoder.raw_decode(raw, pos)
            value_end = pos
            while raw[pos].isspace(): pos += 1
            yield key, key_start, value_start, value_end, pos
            if raw[pos] == "}": return
            if raw[pos] != ",": raise ValueError("property separator")
            pos += 1

    for depth, key in enumerate(keys):
        matches = [span for span in properties(start) if span[0] == key]
        if len(matches) != 1:
            raise ValueError("mutation field span not unique")
        _, key_start, value_start, value_end, after = matches[0]
        if depth != len(keys) - 1:
            start = value_start
    if action == "delete":
        del target[int(keys[-1]) if isinstance(target, list) else keys[-1]]
        a, b, replacement = key_start, value_end, ""
        if raw[after] == ",": b = after + 1
        else:
            before = a - 1
            while raw[before].isspace(): before -= 1
            if raw[before] != ",": raise ValueError("cannot remove sole property")
            a = before
    elif action == "change":
        target[int(keys[-1]) if isinstance(target, list) else keys[-1]] = value
        a, b, replacement = value_start, value_end, json.dumps(value, separators=(",", ":"))
    else:
        raise ValueError("mutation action")
    changed = raw[:a] + replacement + raw[b:]
    if json.loads(changed, object_pairs_hook=strict_object) != expected or original == expected:
        raise ValueError("mutation did not change only intended semantic field")
    output.write_text(changed, encoding="utf-8", newline="\n")
    print(json.dumps({"case": case_id, "field": field_path, "action": action,
                      "oldByteSpan": [a, b], "newSpanLength": len(replacement),
                      "onlyIntendedSemanticChange": True, "beforeSha256": sha(raw.encode()),
                      "afterSha256": sha(changed.encode())}, separators=(",", ":")))


def write_draft(path: Path, frozen: bool = False, witness_directory: Path | None = None) -> None:
    cases = draft_cases() + pq1_cases() + rejection_cases()
    if witness_directory is not None:
        cases += witness_cases(witness_directory)
    cases += [ffi_mutation_case()] + source_cases()
    record = {"schema": SCHEMA, "status": "FROZEN" if frozen else "DRAFT_NO_EXECUTION",
              "producerSha256": sha(Path(__file__).read_bytes()),
              "encoderSha256": sha((ROOT / "scripts/packed_native_image.py").read_bytes()),
              "cases": cases}
    if len({case["id"] for case in cases}) != len(cases):
        raise ValueError("duplicate authored case identity")
    # One entry per physical line supports minimal single-property mutation
    # controls without globally reformatting the registry.
    head = json.dumps({k: v for k, v in record.items() if k != "cases"}, indent=2)[:-2]
    text = head + ',\n  "cases": [\n' + ",\n".join(
        "    " + json.dumps(case, separators=(",", ":")) for case in cases) + "\n  ]\n}\n"
    path.write_text(text, encoding="utf-8", newline="\n")
    print(json.dumps({"schema": SCHEMA, "status": record["status"], "count": len(cases),
                      "registrySha256": sha(path.read_bytes())}, separators=(",", ":")))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="operation", required=True)
    draft = sub.add_parser("draft")
    draft.add_argument("--output", type=Path, required=True)
    draft.add_argument("--freeze", action="store_true",
                       help="authoring only: freeze inspected independent expectations for execution")
    draft.add_argument("--witness-directory", type=Path)
    prepare = sub.add_parser("prepare")
    prepare.add_argument("--registry", type=Path, required=True)
    prepare.add_argument("--case", required=True)
    prepare.add_argument("--output", type=Path, required=True)
    run = sub.add_parser("capture")
    run.add_argument("--executable", type=Path, required=True)
    run.add_argument("--scratch", type=Path, required=True)
    run.add_argument("--deadline", type=float, required=True)
    run.add_argument("--output-limit", type=int, default=4_194_304)
    run.add_argument("arguments", nargs=argparse.REMAINDER)
    mutate = sub.add_parser("mutate-property")
    mutate.add_argument("--registry", type=Path, required=True)
    mutate.add_argument("--case", default="")
    mutate.add_argument("--field", required=True)
    mutate.add_argument("--action", choices=["change", "delete"], required=True)
    mutate.add_argument("--value-json", default="null")
    mutate.add_argument("--output", type=Path, required=True)
    challenge = sub.add_parser("witness-challenge")
    challenge.add_argument("--registry", type=Path, required=True)
    challenge.add_argument("--mutation", choices=list(WITNESS_CHALLENGES), required=True)
    challenge.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.operation == "draft":
        write_draft(args.output, args.freeze, args.witness_directory)
    elif args.operation in ("prepare", "witness-challenge"):
        registry = load_json(args.registry)
        if registry["schema"] != SCHEMA or registry["producerSha256"] != sha(Path(__file__).read_bytes()):
            raise ValueError("case producer identity changed")
        if registry["encoderSha256"] != sha((ROOT / "scripts/packed_native_image.py").read_bytes()):
            raise ValueError("image encoder identity changed")
        case_id = args.case if args.operation == "prepare" else WITNESS_CHALLENGES[args.mutation][0]
        selected = [case for case in registry["cases"] if case["id"] == case_id]
        if len(selected) != 1 or selected[0]["kind"] not in ("native", "ffi-mutation"):
            raise ValueError("exact native fixture selector")
        if args.operation == "prepare":
            print(json.dumps(materialize_image(selected[0]["image"], args.output), separators=(",", ":")))
        else:
            witness_challenge(selected[0]["image"], args.mutation, args.output)
    elif args.operation == "mutate-property":
        mutate_property(args.registry, args.case, args.field, args.action,
                        json.loads(args.value_json, object_pairs_hook=strict_object), args.output)
    else:
        native_args = args.arguments[1:] if args.arguments[:1] == ["--"] else args.arguments
        return capture(args.executable, native_args, args.scratch, args.deadline, args.output_limit)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
