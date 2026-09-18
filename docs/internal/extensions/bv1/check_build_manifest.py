"""Compare parsed TOML with the exact governance blob without rewriting bytes."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import tomllib

root = Path(__file__).resolve().parents[4]
stage = sys.argv[1] if len(sys.argv) == 2 else "manifest-semantics-v1"
if not re.fullmatch(r"[a-z0-9-]+", stage):
    raise SystemExit("Invalid evidence stage")
record_path = Path(__file__).parent / "commands" / f"{stage}.json"
if record_path.exists():
    raise SystemExit("Evidence already exists")
base = "0e6a00f654abc64f8b68988fa9675b9a839dca2f"
base_bytes = subprocess.run(
    ["git", "cat-file", "blob", f"{base}:lakefile.toml"],
    cwd=root, capture_output=True, check=True, timeout=30,
).stdout
current_bytes = (root / "lakefile.toml").read_bytes()
before = tomllib.loads(base_bytes.decode("utf-8"))
after = tomllib.loads(current_bytes.decode("utf-8"))
expected = {"name": "rmq_packed_bitvector_validate", "root": "RMQ.Validation.PackedBitvector"}
matches = [entry for entry in after.get("lean_exe", []) if entry.get("name") == expected["name"]]
remaining = dict(after)
remaining["lean_exe"] = [entry for entry in after.get("lean_exe", []) if entry.get("name") != expected["name"]]
hash_before = hashlib.sha256(base_bytes).hexdigest().upper()
hash_after = hashlib.sha256(current_bytes).hexdigest().upper()
byte_identity = hash_after == "66F2730CC65D0A796A6595D230B18C0554826DFEE9407799F64D0F744D3D823A"
passed = matches == [expected] and remaining == before and byte_identity
record = {
    "version": 1, "stage": stage, "base": base, "path": "lakefile.toml",
    "parser": "Python standard-library tomllib", "baseBytes": len(base_bytes),
    "sourceBytes": len(current_bytes), "baseSHA256": hash_before, "sourceSHA256": hash_after,
    "expectedOnlyAddedTarget": expected, "observedTargetsWithThatName": matches,
    "remainingParsedManifestEqualsBase": remaining == before,
    "recordedSourceBytesUnchanged": byte_identity, "passed": passed,
}
record_path.write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8", newline="\n")
print(f"BV1-MANIFEST-SEMANTICS passed={passed} targetCount={len(matches)} remainingEqual={remaining == before}")
raise SystemExit(0 if passed else 1)
