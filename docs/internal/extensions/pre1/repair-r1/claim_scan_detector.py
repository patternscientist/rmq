#!/usr/bin/env python3
"""Order-independent detector for claim-scanner summary text in scanner output.

PRE-1-R1. The unchanged self-test of scripts/claim_drift_scan.ps1 reads each
run's hit count from the FIRST output line that matches its summary regex,
anywhere in the output. An emitted result line that quotes a scanned document
line holding an earlier scanner summary therefore supplies a wrong count, and
which of several such lines comes first depends on ripgrep's file order.

This detector does not depend on that order. For a default-root strict log
and an -IncludeProcessRecords strict log it counts, over ALL lines:
  * emitted result lines (prefix plus three bracketed fields);
  * emitted result lines that contain the scanner summary pattern, with the
    rule id and the cited path and line of each;
  * all lines that contain the pattern, and the lines that are exactly the
    scanner's own final summary line.
It also emulates the unchanged first-match parser, so the mechanism of a
failure can be named, and parses the self-test log's exclusion line.

Verdict CLEAN requires, for both strict logs, zero emitted result lines with
the pattern, exactly one pattern line, that line being the scanner's own
summary and the last nonempty line, and zero strict failures; and for the
self-test log exactly one PASS result, the probe and record-path lines, and an
exclusion line whose two parsed counts equal the two strict summaries. Any
supplied exit code must be 0. Otherwise the verdict is DEFECT.

Exit codes: 0 CLEAN; 1 DEFECT; 2 usage error; 3 unreadable input.
Output and the result JSON carry counts, rule ids and cited paths only; they
never repeat scanner text, so this tool's own log is not a claim surface.
"""

import argparse
import hashlib
import json
import re
import sys

SCHEMA = "rmq.pre1.repair-r1.claim-scan-detector.v1"
# The scanner summary pattern: the words, an opening parenthesis, digits, the
# word hits. The self-test matches with PowerShell -match, which ignores case.
SUMMARY_PATTERN_REGEX = r"scan complete \([0-9]+ hits"
SUMMARY_PATTERN = re.compile(SUMMARY_PATTERN_REGEX, re.IGNORECASE)
# The parser of the unchanged self-test (first match wins), with its capture.
PARSER_REGEX = re.compile(r"scan complete \(([0-9]+) hits", re.IGNORECASE)
# The scanner's own final line on success.
SUMMARY_LINE = re.compile(r"^CLAIM-DRIFT: scan complete \(([0-9]+) hits, ([0-9]+) strict failures\)$")
STRICT_FAIL_LINE = re.compile(r"^CLAIM-DRIFT: strict mode found ([0-9]+) unapproved sensitive matches$")
RESULT_LINE = re.compile(r"^CLAIM-DRIFT\[([^\]]*)\]\[([^\]]*)\]\[([^\]]*)\]")
CITED = re.compile(r"^CLAIM-DRIFT\[[^\]]*\]\[[^\]]*\]\[[^\]]*\] (.+?):([0-9]+): ")
ST_PROBES = re.compile(r"^CLAIM-DRIFT SELFTEST: ok -- ([0-9]+) protected probes rejected and ([0-9]+) attributed probes accepted$")
ST_RECORDS = re.compile(r"^CLAIM-DRIFT SELFTEST: ok -- no emitted line cites a process-record path$")
ST_OK = re.compile(r"^CLAIM-DRIFT SELFTEST: ok -- exclusion removed ([0-9]+) hits \(([0-9]+) -> ([0-9]+)\)$")
ST_NOTHING = re.compile(r"^CLAIM-DRIFT SELFTEST: FAIL -- exclusion removed nothing \(([0-9]+) hits with records, ([0-9]+) without\)")
ST_UNREADABLE = re.compile(r"^CLAIM-DRIFT SELFTEST: FAIL -- could not read a hit count from both runs$")
ST_RESULT = re.compile(r"^CLAIM-DRIFT SELFTEST: RESULT: (PASS|FAIL)$")
ST_ANY = re.compile(r"^CLAIM-DRIFT SELFTEST: ")


class InputFailure(Exception):
    pass


def read_lines(path):
    try:
        with open(path, "rb") as handle:
            data = handle.read()
    except OSError as exc:
        raise InputFailure(f"cannot read {path}: {exc}")
    text = data.decode("utf-8", errors="replace")
    return data, text.count("\ufffd"), re.split(r"\r?\n", text)


def analyse_strict(label, path, exit_code):
    data, replacements, lines = read_lines(path)
    nonempty = [i for i, line in enumerate(lines) if line.strip() != ""]
    result_lines, pattern_result, pattern_lines, summaries, fails = 0, [], [], [], []
    first_parser = None
    for index, line in enumerate(lines):
        is_result = RESULT_LINE.match(line) is not None
        if is_result:
            result_lines += 1
        if SUMMARY_PATTERN.search(line):
            pattern_lines.append(index + 1)
            if is_result:
                rule = RESULT_LINE.match(line).group(1)
                cited = CITED.match(line)
                pattern_result.append({
                    "logLine": index + 1, "rule": rule,
                    "citedPath": cited.group(1).replace("\\", "/") if cited else None,
                    "citedLine": int(cited.group(2)) if cited else None})
        if first_parser is None:
            parsed = PARSER_REGEX.search(line)
            if parsed:
                first_parser = {"logLine": index + 1, "value": int(parsed.group(1)),
                                "source": "scanner summary line" if SUMMARY_LINE.match(line)
                                else ("emitted result line" if is_result else "other line")}
        summary = SUMMARY_LINE.match(line)
        if summary:
            summaries.append({"logLine": index + 1, "hits": int(summary.group(1)),
                              "strictFailures": int(summary.group(2))})
        failed = STRICT_FAIL_LINE.match(line)
        if failed:
            fails.append({"logLine": index + 1, "strictFailures": int(failed.group(1))})
    last_nonempty = nonempty[-1] + 1 if nonempty else None
    report = {
        "label": label, "path": path, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest().upper(),
        "decodeReplacements": replacements, "lines": len(nonempty), "exit": exit_code,
        "resultLines": result_lines, "resultLinesWithPattern": pattern_result,
        "patternLines": len(pattern_lines), "summaryLines": summaries, "strictFailureLines": fails,
        "lastNonemptyLogLine": last_nonempty, "firstParserMatch": first_parser,
    }
    problems = []
    if exit_code is not None and exit_code != 0:
        problems.append(f"{label}: exit {exit_code}")
    if pattern_result:
        problems.append(f"{label}: {len(pattern_result)} emitted result line(s) contain the summary pattern")
    if len(summaries) != 1:
        problems.append(f"{label}: {len(summaries)} scanner summary lines, expected 1")
    if len(pattern_lines) != 1:
        problems.append(f"{label}: {len(pattern_lines)} lines contain the summary pattern, expected 1")
    if len(summaries) == 1 and (summaries[0]["logLine"] != last_nonempty or pattern_lines != [summaries[0]["logLine"]]):
        problems.append(f"{label}: the scanner summary is not the sole pattern line on the last nonempty line")
    if len(summaries) == 1 and summaries[0]["strictFailures"] != 0:
        problems.append(f"{label}: {summaries[0]['strictFailures']} strict failures")
    if fails:
        problems.append(f"{label}: strict failure line present")
    if replacements:
        problems.append(f"{label}: {replacements} undecodable byte sequences")
    report["problems"] = problems
    return report


def analyse_selftest(path, exit_code, default_report, records_report):
    data, replacements, lines = read_lines(path)
    probes = [ST_PROBES.match(l) for l in lines if ST_PROBES.match(l)]
    record_ok = sum(1 for l in lines if ST_RECORDS.match(l))
    ok = [ST_OK.match(l) for l in lines if ST_OK.match(l)]
    nothing = [ST_NOTHING.match(l) for l in lines if ST_NOTHING.match(l)]
    unreadable = sum(1 for l in lines if ST_UNREADABLE.match(l))
    results = [ST_RESULT.match(l).group(1) for l in lines if ST_RESULT.match(l)]
    selftest_lines = sum(1 for l in lines if ST_ANY.match(l))
    pattern_lines = sum(1 for l in lines if SUMMARY_PATTERN.search(l))
    exclusion = None
    if len(ok) == 1 and not nothing and not unreadable:
        exclusion = {"form": "ok", "removed": int(ok[0].group(1)), "withRecords": int(ok[0].group(2)),
                     "withoutRecords": int(ok[0].group(3))}
    elif len(nothing) == 1 and not ok and not unreadable:
        exclusion = {"form": "fail-removed-nothing", "removed": None, "withRecords": int(nothing[0].group(1)),
                     "withoutRecords": int(nothing[0].group(2))}
    elif unreadable == 1 and not ok and not nothing:
        exclusion = {"form": "fail-unreadable", "removed": None, "withRecords": None, "withoutRecords": None}
    report = {
        "label": "selftest", "path": path, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest().upper(),
        "decodeReplacements": replacements, "exit": exit_code, "selftestLines": selftest_lines,
        "probeLines": [{"protected": int(p.group(1)), "attributed": int(p.group(2))} for p in probes],
        "recordPathOkLines": record_ok, "exclusion": exclusion, "results": results, "patternLines": pattern_lines,
    }
    problems = []
    if exit_code is not None and exit_code != 0:
        problems.append(f"selftest: exit {exit_code}")
    if results != ["PASS"]:
        problems.append(f"selftest: result lines {results}, expected exactly one PASS")
    if len(probes) != 1 or record_ok != 1:
        problems.append("selftest: probe or record-path line missing or repeated")
    if exclusion is None or exclusion["form"] != "ok":
        problems.append(f"selftest: exclusion line form {exclusion['form'] if exclusion else 'missing/ambiguous'}")
    else:
        d = default_report["summaryLines"][0]["hits"] if len(default_report["summaryLines"]) == 1 else None
        r = records_report["summaryLines"][0]["hits"] if len(records_report["summaryLines"]) == 1 else None
        report["separateRuns"] = {"withRecords": r, "withoutRecords": d}
        if exclusion["withRecords"] != r or exclusion["withoutRecords"] != d:
            problems.append(f"selftest: parsed counts {exclusion['withRecords']}/{exclusion['withoutRecords']} "
                            f"!= separate summaries {r}/{d}")
        if exclusion["removed"] != exclusion["withRecords"] - exclusion["withoutRecords"]:
            problems.append("selftest: removed count is not the difference of its two counts")
    if replacements:
        problems.append(f"selftest: {replacements} undecodable byte sequences")
    report["problems"] = problems
    return report


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--default", required=True, help="stdout log of the -Strict default-root run")
    parser.add_argument("--records", required=True, help="stdout log of the -Strict -IncludeProcessRecords run")
    parser.add_argument("--selftest", default=None, help="stdout log of the -SelfTest run")
    parser.add_argument("--default-exit", type=int, default=None)
    parser.add_argument("--records-exit", type=int, default=None)
    parser.add_argument("--selftest-exit", type=int, default=None)
    parser.add_argument("--result-json", default=None)
    args = parser.parse_args(argv)
    try:
        default_report = analyse_strict("default", args.default, args.default_exit)
        records_report = analyse_strict("records", args.records, args.records_exit)
        selftest_report = (analyse_selftest(args.selftest, args.selftest_exit, default_report, records_report)
                           if args.selftest else None)
    except InputFailure as exc:
        print(f"CLAIM-SCAN-DETECTOR: ERROR {exc}", flush=True)
        return 3
    problems = default_report["problems"] + records_report["problems"]
    if selftest_report is not None:
        problems += selftest_report["problems"]
    else:
        problems.append("selftest: no self-test log supplied")
    for rep in (default_report, records_report):
        summary = rep["summaryLines"][0] if len(rep["summaryLines"]) == 1 else None
        print(f"CLAIM-SCAN-DETECTOR: {rep['label']}: {rep['lines']} nonempty lines; {rep['resultLines']} result lines; "
              f"{len(rep['resultLinesWithPattern'])} result lines with the pattern; {rep['patternLines']} pattern lines; "
              f"{len(rep['summaryLines'])} summary lines"
              + (f" (hits {summary['hits']}, strict failures {summary['strictFailures']}, log line {summary['logLine']} "
                 f"of last {rep['lastNonemptyLogLine']})" if summary else "")
              + (f"; first parser match value {rep['firstParserMatch']['value']} from {rep['firstParserMatch']['source']} "
                 f"at log line {rep['firstParserMatch']['logLine']}" if rep["firstParserMatch"] else "; no parser match"),
              flush=True)
        for hit in rep["resultLinesWithPattern"]:
            print(f"CLAIM-SCAN-DETECTOR: {rep['label']}: pattern in result line {hit['logLine']}: rule {hit['rule']} "
                  f"cites {hit['citedPath']}:{hit['citedLine']}", flush=True)
    if selftest_report is not None:
        ex = selftest_report["exclusion"]
        print(f"CLAIM-SCAN-DETECTOR: selftest: results {selftest_report['results']}; exclusion "
              + (f"{ex['form']} with-records {ex['withRecords']} without-records {ex['withoutRecords']} removed {ex['removed']}"
                 if ex else "missing/ambiguous") + f"; pattern lines {selftest_report['patternLines']}", flush=True)
    for problem in problems:
        print(f"CLAIM-SCAN-DETECTOR: finding {problem}", flush=True)
    verdict = "CLEAN" if not problems else "DEFECT"
    result = {"schema": SCHEMA, "summaryPatternRegex": SUMMARY_PATTERN_REGEX, "summaryPatternFlags": "IGNORECASE",
              "default": default_report, "records": records_report, "selftest": selftest_report,
              "problems": problems, "verdict": verdict}
    if args.result_json:
        with open(args.result_json, "w", encoding="utf-8", newline="\n") as handle:
            json.dump(result, handle, indent=2, ensure_ascii=True)
            handle.write("\n")
    print(f"CLAIM-SCAN-DETECTOR: RESULT: {verdict} ({len(problems)} findings)", flush=True)
    return 0 if verdict == "CLEAN" else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
