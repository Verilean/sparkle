#!/usr/bin/env python3
"""Judge one measurement of scripts/research/ux_measure.sh.

Collection and verification are separate: ux_measure.sh runs every step to the end
and records each step's exit code; this script then decides, from the TSV and the
per-step logs, whether the measurement is valid, and exits non-zero if it is not.

Policy (applies to any revision):
  * every REQUIRED step must be present with rc 0;
  * a proof step (d2, e2) is
      accepted  iff rc == 0, the log has "VED U1 OK", and no Lean error line;
      refused   iff rc != 0 and the log has "VED U1 REFUSED";
      anything else (e.g. OK printed but rc 1, or rc 0 with an error) is
      INCONSISTENT and always fails;
    its outcome must equal the expectation: "accepted" by default, or what
    --expect STEP=refused says (e.g. the baseline that predates the proof);
  * an x_* CI-check step is optional: "absent at this revision" is allowed and
    reported, but a present one must have rc 0.

Usage: ux_verdict.py TSV [--logs DIR] [--expect STEP=accepted|refused ...]
       [--skip-elan] [--self-test]
"""
import argparse
import csv
import os
import re
import sys
import tempfile

REQUIRED = ["a_clone", "a0", "a1", "a2", "a3", "b1", "c1", "c2a", "c2", "c3",
            "d0", "d1", "d2", "e1", "e2"]
PROOF = {"d2", "e2"}
# with --usecases (UX_USECASES=1): use cases B and D, all required
USECASES = ["u_soc", "u_test", "u_deep", "u_hier", "u_chk_hier", "u_chk_write",
            "u_pre1", "u_edit1", "u_post1", "u_pre2", "u_edit2", "u_post2"]
# an edit step counts only if its log shows these modules really rebuilt
REBUILT = {"u_edit1": ["Tools.VedU1WireShare", "Tests.Ved.U1EntryCheck"],
           "u_edit2": ["Tools.VedU1Contract", "Tests.Ved.U1EntryCheck"]}
ERROR_LINE = re.compile(r":\d+:\d+: error|^(?:[0-9.]+ )?error:", re.M)


def proof_outcome(rc, log_text):
    ok = "VED U1 OK" in log_text
    refused = "VED U1 REFUSED" in log_text
    err = bool(ERROR_LINE.search(log_text))
    if rc == 0 and ok and not err and not refused:
        return "accepted"
    if rc != 0 and refused and not ok:
        return "refused"
    return "inconsistent"


def parse_expect(items):
    """STEP=OUTCOME pairs: STEP in PROOF, OUTCOME accepted|refused, each step once."""
    expect = {}
    for e in items:
        for item in e.split():
            step, sep, val = item.partition("=")
            if not sep or step not in PROOF or val not in ("accepted", "refused"):
                raise ValueError(f"--expect {item!r}: want STEP=accepted|refused with STEP in {sorted(PROOF)}")
            if step in expect:
                raise ValueError(f"--expect {item!r}: step {step} given twice")
            expect[step] = val
    return expect


def judge(tsv, logs, expect, skip_elan, usecases=False):
    rows = {r["step"]: r for r in csv.DictReader(open(tsv), delimiter="\t")}
    label = next(iter(rows.values()))["label"] if rows else "?"
    problems, lines = [], []
    required = [s for s in REQUIRED if not (skip_elan and s in ("a0", "a1"))]
    if usecases:
        required += USECASES
    for s in required:
        r = rows.get(s)
        if r is None or r["rc"] == "":
            problems.append(f"{s}: missing")
            continue
        rc = int(r["rc"])
        if s in PROOF:
            log = os.path.join(logs, f"{label}-{s}.log")
            text = open(log, errors="replace").read() if os.path.exists(log) else ""
            got = proof_outcome(rc, text) if text else "inconsistent (no log)"
            want = expect.get(s, "accepted")
            lines.append(f"{s}: {got} (expected {want}, rc {rc})")
            if got != want:
                problems.append(f"{s}: {got}, expected {want}")
        elif rc != 0:
            problems.append(f"{s}: rc {rc}")
        elif s in REBUILT:
            log = os.path.join(logs, f"{label}-{s}.log")
            text = open(log, errors="replace").read() if os.path.exists(log) else ""
            gone = [m for m in REBUILT[s] if not re.search(rf"Built {re.escape(m)} \(", text)]
            if gone:
                problems.append(f"{s}: no rebuild of {', '.join(gone)} in the log")
            else:
                lines.append(f"{s}: rebuilt {', '.join(REBUILT[s])}")
    for s, r in sorted(rows.items()):
        if not s.startswith("x_"):
            continue
        if "absent at this revision" in r["note"]:
            lines.append(f"{s}: absent at this revision (optional)")
        elif r["rc"] != "0":
            problems.append(f"{s}: rc {r['rc']}")
        else:
            lines.append(f"{s}: rc 0")
    return problems, lines


def self_test():
    """Fake controls: each must give the stated verdict."""
    hdr = "label\tstep\tdescription\twall_s\tuser_s\tsys_s\tpeak_rss_mb\trc\tnote\n"

    built = {s: "".join(f"1.0 \u2714 [1/2] Built {m} (1.0s)\n" for m in ms)
             for s, ms in REBUILT.items()}

    def case(rcs, logs, expect=None, absent=(), usecases=False):
        d = tempfile.mkdtemp()
        with open(os.path.join(d, "ux-t.tsv"), "w") as f:
            f.write(hdr)
            for s in REQUIRED + (USECASES if usecases else []):
                if s in rcs and rcs[s] is None:
                    continue
                f.write(f"t\t{s}\td\t1\t1\t0\t1\t{rcs.get(s, 0)}\t\n")
            for s in absent:
                f.write(f"t\t{s}\td\t\t\t\t\t\tabsent at this revision\n")
        for s in PROOF:
            with open(os.path.join(d, f"t-{s}.log"), "w") as f:
                f.write(logs.get(s, "1.0 VED U1 OK x.ved_u1: [propext]\n"))
        for s in REBUILT:
            with open(os.path.join(d, f"t-{s}.log"), "w") as f:
                f.write(logs.get(s, built[s]))
        return judge(os.path.join(d, "ux-t.tsv"), d, expect or {}, False, usecases)[0]

    refusal = "1.0 VED U1 REFUSED x [proof]: timeout\n"
    checks = [
        ("all accepted", case({}, {}), True),
        ("required build failed (a3 rc 1)", case({"a3": 1}, {}), False),
        ("OK printed but rc 1", case({"e2": 1}, {}), False),
        ("rc 0 with an error line", case({}, {"e2": "1.0 VED U1 OK x\n1.1 f.lean:3:0: error: boom\n"}), False),
        ("expected baseline refusal", case({"e2": 1}, {"e2": refusal}, {"e2": "refused"}), True),
        ("refusal not declared", case({"e2": 1}, {"e2": refusal}), False),
        ("declared refusal but accepted", case({}, {}, {"e2": "refused"}), False),
        ("required step missing (d0)", case({"d0": None}, {}), False),
        ("optional check absent", case({}, {}, absent=["x_U1KeccakRcCheck"]), True),
        ("use cases: all steps, rebuilds logged", case({}, {}, usecases=True), True),
        ("use cases: lake test failed", case({"u_test": 1}, {}, usecases=True), False),
        ("use cases: step missing (u_post2)", case({"u_post2": None}, {}, usecases=True), False),
        ("use cases: edit 1 shows no rebuild (Replayed only)",
         case({}, {"u_edit1": "1.0 \u26a0 [1/2] Replayed Tools.VedU1WireShare\n"}, usecases=True), False),
        ("use cases: edit 2 rebuilt the module but not the check",
         case({}, {"u_edit2": "1.0 \u2714 [1/2] Built Tools.VedU1Contract (1.0s)\n"}, usecases=True), False),
        ("use cases off: u_* rows not required", case({}, {}), True),
    ]
    for name, items, ok in [("valid e2=refused", ["e2=refused"], True),
                            ("value inconsistent", ["e2=inconsistent"], False),
                            ("unknown step", ["a3=refused"], False),
                            ("duplicate step", ["e2=refused", "e2=accepted"], False),
                            ("missing '='", ["e2"], False)]:
        try:
            parse_expect(items)
            checks.append((f"--expect {name}", [], ok))
        except ValueError as ex:
            checks.append((f"--expect {name}", [str(ex)], ok))
    bad = 0
    for name, problems, should_pass in checks:
        passed = not problems
        mark = "ok" if passed == should_pass else "WRONG"
        bad += mark == "WRONG"
        print(f"[{mark}] {name}: {'pass' if passed else 'fail: ' + '; '.join(problems)}")
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("tsv", nargs="?")
    ap.add_argument("--logs")
    ap.add_argument("--expect", action="append", default=[])
    ap.add_argument("--skip-elan", action="store_true")
    ap.add_argument("--usecases", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        return self_test()
    try:
        expect = parse_expect(a.expect)
    except ValueError as ex:
        print(f"input error: {ex}", file=sys.stderr)
        return 2
    problems, lines = judge(a.tsv, a.logs or os.path.dirname(os.path.abspath(a.tsv)),
                            expect, a.skip_elan, a.usecases)
    for l in lines:
        print(l)
    if problems:
        print("VERDICT: FAIL (measurement collected, verification failed)")
        for p in problems:
            print("  " + p)
        return 1
    print("VERDICT: PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
