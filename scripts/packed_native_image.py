"""Serialize the committed PQ1 numeric fixtures using StorageImage format 1.

This is a reproducible fixture/export convenience, not a compiler theorem.
The Lean codec defines the format and the delivered loader validates it.
No RMQ answer is computed here and no native output becomes an expectation.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path

MAGIC = b"RMQN\x01"
MAX_FILE_BYTES = 134_217_728


def scalar(value: int) -> bytes:
    if value < 0:
        raise ValueError("negative scalar")
    count = max(1, (value.bit_length() + 7) // 8)
    return b"\x01" * count + b"\x00" + value.to_bytes(count, "little")


def word(width: int, value: int) -> bytes:
    if width <= 0 or value < 0 or value.bit_length() > width:
        raise ValueError("word outside declared width")
    count = (width + 7) // 8
    return scalar(count) + value.to_bytes(count, "little")


def encode_image(width: int, input_length: int, registers: int,
                 code: list[list[int]], memory: list[int]) -> bytes:
    if not 0 < width <= 4096 or not 3 <= registers <= 65536:
        raise ValueError("unsupported image header")
    if input_length < 0 or input_length.bit_length() > width:
        raise ValueError("input length outside declared width")
    if len(code) > 1_000_000 or len(memory) > 1_000_000:
        raise ValueError("image count limit")
    result = bytearray(MAGIC)
    result.extend(scalar(width))
    result.extend(scalar(input_length))
    result.extend(scalar(registers))
    result.extend(scalar(len(code)))
    for fields in code:
        if not 1 <= len(fields) <= 5:
            raise ValueError("instruction field count")
        result.extend(scalar(len(fields)))
        for value in fields:
            result.extend(word(width, value))
        if len(result) > MAX_FILE_BYTES:
            raise ValueError("image byte limit")
    result.extend(scalar(len(memory)))
    for value in memory:
        result.extend(word(width, value))
    if len(result) > MAX_FILE_BYTES:
        raise ValueError("image byte limit")
    return bytes(result)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--program-gzip", required=True, type=Path)
    parser.add_argument("--fixture", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--program-sha256", required=True)
    parser.add_argument("--fixture-sha256", required=True)
    args = parser.parse_args()
    with gzip.open(args.program_gzip, "rb") as source:
        raw_code = source.read(50_000_001)
    raw_fixture = args.fixture.read_bytes()
    if len(raw_code) > 50_000_000 or len(raw_fixture) > 1_000_000:
        raise ValueError("fixture source size limit")
    if digest(raw_code) != args.program_sha256.upper():
        raise ValueError("program source identity mismatch")
    if digest(raw_fixture) != args.fixture_sha256.upper():
        raise ValueError("fixture source identity mismatch")
    code = [[int(value) for value in line.split()] for line in raw_code.decode("ascii").splitlines() if line]
    fixture_lines = [line for line in raw_fixture.decode("ascii").splitlines() if line]
    header = [int(value) for value in fixture_lines[0].split()]
    if len(header) != 5:
        raise ValueError("fixture header")
    input_length, left, right, width, fuel = header
    memory = [int(value) for value in fixture_lines[1:]]
    if not 0 <= fuel <= 1_000_000:
        raise ValueError("fixture fuel limit")
    endpoint_bytes = (width + 7) // 8
    if left < 0 or right < 0 or left.bit_length() > width or right.bit_length() > width:
        raise ValueError("fixture endpoint width")
    encoded = encode_image(width, input_length, 8271, code, memory)
    words = sum(map(len, code)) + len(memory)
    framing = len(encoded) - words * endpoint_bytes
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(encoded)
    record = {
        "schema": "native1-image-export-v1", "format": 1,
        "programSHA256": digest(raw_code), "fixtureSHA256": digest(raw_fixture),
        "imageSHA256": digest(encoded), "imageBytes": len(encoded),
        "width": width, "inputLength": input_length, "registerCount": 8271,
        "instructions": len(code), "memoryWords": len(memory),
        "wordCount": words, "numericBits": words * width,
        "roundingBits": words * (8 * endpoint_bytes - width),
        "framingBytes": framing, "fuel": fuel,
        "leftHex": left.to_bytes(endpoint_bytes, "little").hex(),
        "rightHex": right.to_bytes(endpoint_bytes, "little").hex(),
    }
    if 8 * len(encoded) != record["numericBits"] + record["roundingBits"] + 8 * framing:
        raise AssertionError("exact file accounting")
    args.output.with_suffix(args.output.suffix + ".json").write_text(
        json.dumps(record, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(record, separators=(",", ":")))


if __name__ == "__main__":
    main()
