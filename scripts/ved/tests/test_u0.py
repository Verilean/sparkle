#!/usr/bin/env python3
"""Unit tests / controls for the U0 harness (scripts/ved/u0_gen.py, u0_run.py).

No Lean, no cluster: `kjob lake env lean` is replaced by tests/fake_lean.py,
and the inventory/source tree is a throw-away git repository built here.
Run:  MEM=4G memlimit python3 -I scripts/ved/tests/test_u0.py -v
"""
import csv
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
VED = os.path.dirname(HERE)
GEN = os.path.join(VED, "u0_gen.py")
RUN = os.path.join(VED, "u0_run.py")
FAKE = os.path.join(HERE, "fake_lean.py")
sys.dont_write_bytecode = True  # nothing written into the source tree
sys.path.insert(0, VED)
import u0_gen  # noqa: E402

INV_HDR = ["file", "line", "command", "ns", "top", "qualified", "params", "options", "args",
           "in_alltests_closure", "area"]


def sh(cmd, cwd=None, env=None, check=True):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, check=check)


class Fixture:
    """A git repo with a 327-row inventory and two source files."""

    SPECIAL = {
        2: dict(top="bar2"),
        3: dict(top="baz3", private=True),
        4: dict(top="symb4", command="#synthesizeParameterizedVerilog", params="W := 8",
                options="symbolicMode=true"),
        13: dict(top="wd13", command="#writeDesign", args='"out.sv" "out.h"'),
        # like 245 real rows: `ns` empty and a scope-relative name, although the
        # source file has a namespace (used by the U1 decl-check test)
        300: dict(ns="", qualified="foo300"),
    }

    def __init__(self, base):
        self.repo = os.path.join(base, "repo")
        os.makedirs(os.path.join(self.repo, "scripts/gen5/fgc_baseline"))
        os.makedirs(os.path.join(self.repo, "Src"))
        open(os.path.join(self.repo, "lean-toolchain"), "w").write("leanprover/lean4:v4.32.1\n")
        a = ["/- a block comment\n   #synthesizeVerilog notMe\n-/", "import Foo", "",
             "set_option maxHeartbeats 400000", "", "namespace Outer", ""]
        rows = []
        for k in range(1, 328):
            sp = self.SPECIAL.get(k, {})
            top = sp.get("top", f"foo{k}")
            cmd = sp.get("command", "#synthesizeVerilog")
            a.append(("private " if sp.get("private") else "") + f"def {top} : Nat := {k}")
            a.append(f"{cmd} {top}" + (f" {sp['args']}" if sp.get("args") else ""))
            rows.append({"file": "Src/A.lean", "line": str(len(a)), "command": cmd, "ns": sp.get("ns", "Outer"),
                         "top": top, "qualified": sp.get("qualified", f"Outer.{top}"), "params": sp.get("params", ""),
                         "options": sp.get("options", ""), "args": sp.get("args", ""),
                         "in_alltests_closure": "N", "area": "Src"})
        a.append("end Outer")
        open(os.path.join(self.repo, "Src/A.lean"), "w").write("\n".join(a) + "\n")
        with open(os.path.join(self.repo, u0_gen.INV_PATH), "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=INV_HDR, delimiter="\t", lineterminator="\n")
            w.writeheader()
            w.writerows(rows)
        sh(["git", "init", "-q"], cwd=self.repo)
        sh(["git", "-c", "user.email=t@t", "-c", "user.name=t", "add", "-A"], cwd=self.repo)
        sh(["git", "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "fixture"], cwd=self.repo)
        self.commit = sh(["git", "rev-parse", "HEAD"], cwd=self.repo).stdout.strip()
        self.blob = sh(["git", "rev-parse", f"HEAD:{u0_gen.INV_PATH}"], cwd=self.repo).stdout.strip()

    def commit_change(self, path, text):
        open(os.path.join(self.repo, path), "w").write(text)
        sh(["git", "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qam", "change"], cwd=self.repo)
        return sh(["git", "rev-parse", "HEAD"], cwd=self.repo).stdout.strip()


def ok(*axs):
    return ["OK", list(axs)]


class U0Harness(unittest.TestCase):
    def setUp(self):
        self.base = tempfile.mkdtemp(prefix="u0test-")
        self.fx = Fixture(self.base)
        self.out = os.path.join(self.base, "out")
        self.plan_path = os.path.join(self.base, "plan.json")
        self.log = os.path.join(self.base, "fake.log")
        self.pids = os.path.join(self.base, "pids.txt")
        self.plan = {}

    def tearDown(self):
        shutil.rmtree(self.base, ignore_errors=True)

    def env(self, **extra):
        e = {k: v for k, v in os.environ.items() if not k.startswith("SPARKLE_")}
        e.update(U0_LEAN=f"{sys.executable} -I {FAKE}", U0_INV_COMMIT=self.fx.commit,
                 U0_INV_BLOB=self.fx.blob, FAKE_PLAN=self.plan_path, FAKE_LOG=self.log,
                 FAKE_PIDS=self.pids, U0_TMO="30", U0_GRACE="1")
        e.update(extra)
        return e

    def run_u0(self, *args, **extra):
        json.dump(self.plan, open(self.plan_path, "w"))
        return subprocess.run([sys.executable, "-I", RUN, "--repo", self.fx.repo, "--out", self.out, *args],
                              env=self.env(**extra), capture_output=True, text=True, timeout=120)

    def results(self, name="results.tsv"):
        rid = open(os.path.join(self.out, "CURRENT_RUN_ID")).read().strip()
        with open(os.path.join(self.out, "results", rid, name)) as f:
            return list(csv.DictReader(f, delimiter="\t"))

    def fake_calls(self, key=None):
        if not os.path.exists(self.log):
            return []
        calls = [json.loads(ln) for ln in open(self.log)]
        return [c for c in calls if key is None or c["key"] == key]

    def single_ok(self, k, **over):
        p = {"top": f"foo{k}", "ret": "signal", "outputs": ["out"], "body": "match",
             "theorems": {f"foo{k}_deep_trace": ok("propext"), f"foo{k}_deep_signal_run": ok("propext")}}
        p.update(over)
        self.plan[str(k)] = p

    # ------------------------------------------------------------ P1-1
    def test_single_output_observed_never_strict_yes(self):
        self.single_ok(1)
        r = self.run_u0("case", "1", "default")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        [row] = self.results()
        self.assertEqual(row["invocation"], "deep-in-file")
        self.assertEqual((row["src_expected"], row["src_found"], row["src_closure"]), ("1", "1", "ok"))
        self.assertEqual((row["ir_expected"], row["ir_found"], row["ir_closure"]), ("1", "1", "ok"))
        self.assertEqual(row["opt_closure"], "not-in-route")
        self.assertEqual(row["observed_against_second_run"], "match")
        self.assertEqual(row["strict_counted"], "unknown")
        self.assertIn("artifact-identity-not-probed", row["strict_blockers"])
        self.assertIn("theorem-types-not-checked", row["strict_blockers"])
        self.assertEqual(row["decl_check"], "match")

    def test_multi_output_missing_one(self):
        self.plan["2"] = {"top": "bar2", "ret": "struct", "outputs": ["a", "b"], "body": "match",
                          "theorems": {"bar2_a_deep_trace": ok(), "bar2_a_deep_signal_run": ok(),
                                       "bar2_b_deep_trace": ok()}}
        self.run_u0("case", "2", "default")
        [row] = self.results()
        self.assertEqual((row["src_expected"], row["src_found"], row["src_closure"]), ("2", "2", "ok"))
        self.assertEqual((row["ir_expected"], row["ir_found"], row["ir_closure"]), ("2", "1", "missing"))
        self.assertEqual(row["missing_theorems"], "bar2_b_deep_signal_run")
        self.assertEqual(row["strict_counted"], "no")

    def test_body_mismatch_is_not_reordered(self):
        self.single_ok(5, body="mismatch")
        self.run_u0("case", "5", "default")
        [row] = self.results()
        self.assertEqual(row["observed_against_second_run"], "mismatch")
        self.assertNotIn("reorder", "\t".join(row.values()))
        self.assertIn(row["strict_counted"], ("no", "unknown"))
        self.assertIn("body-vs-second-run:mismatch", row["strict_blockers"])

    def test_body_absent_is_unknown(self):
        self.single_ok(5, body="absent")
        self.run_u0("case", "5", "default")
        [row] = self.results()
        self.assertEqual(row["observed_against_second_run"], "unknown")

    def test_extra_theorem_nonstandard_axiom_does_not_fail_ir(self):
        self.single_ok(8, theorems={"foo8_deep_trace": ok(), "foo8_deep_signal_run": ok("propext"),
                                    "foo8_deep_coneEval_r0": ["REJECTED", ["x._native.native_decide.ax_1_1"]]})
        self.run_u0("case", "8", "default")
        [row] = self.results()
        self.assertEqual(row["ir_closure"], "ok")
        self.assertEqual(row["ir_axioms"], "propext")
        self.assertEqual((row["n_extra"], row["extra_rejected"]), ("1", "1"))
        self.assertIn("x._native.native_decide.ax_1_1", row["raw_axioms"])

    def test_required_theorem_rejected_fails_its_stage(self):
        self.single_ok(8, theorems={"foo8_deep_trace": ok(),
                                    "foo8_deep_signal_run": ["REJECTED", ["y._native.native_decide.ax_1_1"]]})
        self.run_u0("case", "8", "default")
        [row] = self.results()
        self.assertEqual((row["src_closure"], row["ir_closure"]), ("ok", "rejected"))
        self.assertEqual(row["strict_counted"], "no")

    def test_sv_stages_split(self):
        self.plan["11"] = {"top": "foo11", "ret": "signal", "outputs": ["out"], "body": "match",
                           "theorems": {n: ok() for n in ["foo11_sdeep_trace", "foo11_sdeep_signal_run",
                                                          "foo11_sdeep_signal_runOpt", "foo11_sdeep_text_parses"]}}
        self.run_u0("case", "11", "shared")
        [row] = self.results()
        self.assertEqual(row["opt_closure"], "ok")
        self.assertEqual(row["sv_parse_closure"], "ok")
        self.assertEqual(row["sv_roundtrip_closure"], "missing")
        self.assertEqual(row["sv_meaning_closure"], "missing")   # text_parses never makes it yes

    def test_probe_missing_gives_unknown_stages(self):
        self.single_ok(1)
        del self.plan["1"]["ret"]
        self.run_u0("case", "1", "default")
        [row] = self.results()
        self.assertEqual((row["src_expected"], row["src_closure"]), ("?", "unknown"))
        self.assertEqual(row["strict_counted"], "no")

    # ------------------------------------------------------------ P1-2
    def test_params_and_args_not_run_but_kept(self):
        r = self.run_u0("case", "4", "default")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        r = self.run_u0("case", "13", "default")
        rows = {x["row"]: x for x in self.results()}
        self.assertEqual(rows["4"]["invocation"], "unsupported-invocation")
        self.assertIn("W := 8", rows["4"]["invocation_detail"])
        self.assertIn("symbolicMode", rows["4"]["invocation_detail"])
        self.assertEqual(rows["13"]["invocation"], "unsupported-invocation")
        self.assertEqual((rows["4"]["ran"], rows["4"]["strict_counted"]), ("no", "no"))
        self.assertEqual(self.fake_calls("4") + self.fake_calls("13"), [])

    def test_case_is_in_file_copy_with_scope(self):
        self.single_ok(3, top="baz3")
        self.run_u0("case", "3", "default")
        [row] = self.results()
        a = sorted(os.listdir(os.path.join(self.out, "cases", "R003_default")))[-1]
        text = open(os.path.join(self.out, "cases", "R003_default", a, "Case.lean")).read()
        lines = text.splitlines()
        self.assertIn("private def baz3 : Nat := 3", text)
        self.assertIn("set_option maxHeartbeats 400000", text)       # scoped option kept by the copy
        self.assertLess(lines.index("import Tools.DeepElab"), lines.index("namespace Outer"))
        i = lines.index("#synthesizeVerilog baz3")
        self.assertTrue(lines[i + 2].startswith("-- ===== VED U0 BEGIN row 3"))
        self.assertIn("#verify_elab_deep baz3", text)               # the command's own identifier
        self.assertIn("declaration is private", row["invocation_detail"])
        meta = json.load(open(os.path.join(self.out, "cases", "R003_default", a, "meta.json")))
        self.assertEqual(lines[meta["block_begin"]], "-- ===== VED U0 BEGIN row 3 setting default (inventory f694355f) =====")

    def test_decl_absent(self):
        self.single_ok(9, decl="absent")
        self.plan["3"] = {"top": "baz3", "decl": "absent"}
        self.run_u0("case", "9", "default")
        self.run_u0("case", "3", "default")
        rows = {x["row"]: x for x in self.results()}
        self.assertEqual(rows["9"]["invocation"], "unresolved-name")
        self.assertEqual(rows["3"]["invocation"], "unresolved-private")
        self.assertEqual(rows["9"]["strict_counted"], "no")

    def test_decl_qualified_mismatch_recorded(self):
        self.single_ok(1)
        self.plan["1"]["stdout"] = []
        self.plan["1"]["decl"] = "found"
        self.plan["1"]["qualified"] = "Other.foo1"
        self.run_u0("case", "1", "default")
        [row] = self.results()
        self.assertEqual(row["decl_check"], "match")  # fake prints match for its own value
        # classifier reads the probe's verdict; a mismatch line is reported as mismatch
        d = os.path.join(self.out, "cases", "R001_default", "attempt-001")
        with open(os.path.join(d, "stdout.txt"), "a") as f:
            f.write("x:1:0: info: VED DECL resolved=A.b user=A.b inventory=Outer.foo1 mismatch\n")
        r2 = u0_gen.classify_dir(d)
        self.assertEqual(r2["decl_check"], "match")  # the FIRST probe line wins
        open(os.path.join(d, "stdout.txt"), "w").write(
            "x:1:0: info: VED DECL resolved=A.b user=A.b inventory=Outer.foo1 mismatch\n")
        self.assertEqual(u0_gen.classify_dir(d)["decl_check"], "mismatch")

    def test_smoke_split_separate_tables_and_risks(self):
        f = os.path.join(self.fx.repo, "Src/Deep.lean")
        open(f, "w").write("import Foo\nnamespace T\n#verify_elab_deep a\nset_option sparkle.deepShare true in\n"
                           "#verify_elab_deep b\n#check a_deep_trace\nend T\n")
        self.plan["smoke:0"] = {"ret": "signal", "error_outside_line": 9}
        self.plan["smoke:1"] = {}
        self.plan["asis"] = {"stdout": ["#verify_elab_deep T.a: PROVEN via x"]}
        r1 = self.run_u0("smoke-split", "Src/Deep.lean")
        r2 = self.run_u0("smoke-file", "Src/Deep.lean")
        self.assertEqual(r2.returncode, 0, r2.stdout + r2.stderr)
        split = self.results("results_smoke_split.tsv")
        asis = self.results("results_smoke_asis.tsv")
        self.assertEqual(len(split), 2)
        self.assertEqual(len(asis), 1)
        self.assertEqual(self.results(), [])
        self.assertEqual(asis[0]["n_proven_msgs_observation"], "1")
        v0 = [x for x in split if x["row"] == "smoke:Deep:0"][0]
        self.assertIn("split-harness", v0["harness_error"])
        self.assertEqual(r1.returncode, 3)          # the split-harness failure makes the run INCOMPLETE
        rep = open(os.path.join(self.out, "cases", "S_Deep_00",
                                sorted(os.listdir(os.path.join(self.out, "cases", "S_Deep_00")))[0],
                                "split_report.txt")).read()
        self.assertIn("references a_deep_trace", rep)
        case1 = open(os.path.join(self.out, "cases", "S_Deep_01", "attempt-001", "Case.lean")).read()
        self.assertIn("-- U0 split: #verify_elab_deep a", case1)
        self.assertIn("namespace VedU0Smoke01\nset_option sparkle.deepShare true in\n#verify_elab_deep b", case1)

    def test_coded_error_lines_counted(self):
        # smoke2-4d1e: Lean v4.32 prints `error(lean.unknownIdentifier): ...`; such lines
        # were not matched, so a split variant failed with errors_outside_block=0.
        f = os.path.join(self.fx.repo, "Src/Deep.lean")
        open(f, "w").write("import Foo\nnamespace T\n#verify_elab_deep a\n#verify_elab_deep b\n"
                           "#check a_deep_trace\nend T\n")
        self.plan["smoke:0"] = {"ret": "signal", "coded_error_outside_line": 9}
        self.plan["smoke:1"] = {"ret": "signal"}
        self.plan["asis"] = {"coded_error_outside_line": 5}
        r1 = self.run_u0("smoke-split", "Src/Deep.lean")
        self.run_u0("smoke-file", "Src/Deep.lean")
        v0 = [x for x in self.results("results_smoke_split.tsv") if x["row"] == "smoke:Deep:0"][0]
        self.assertEqual(v0["errors_outside_block"], "1")
        self.assertIn("split-harness", v0["harness_error"])
        self.assertEqual(r1.returncode, 3)
        self.assertEqual(self.results("results_smoke_asis.tsv")[0]["n_errors"], "1")

    # ------------------------------------------------------------ P1-3 a
    def test_environment_pollution_cleared(self):
        self.single_ok(1)
        r = self.run_u0("case", "1", "default", SPARKLE_DEEP_SHARE="1", SPARKLE_DEEP_TRACE_ONLY="1",
                        SPARKLE_DEEP_NOTHM="1", SPARKLE_PROFILE="1", SPARKLE_NO_REGDEDUP="1")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        [call] = self.fake_calls("1")
        self.assertEqual([e.split("=")[0] for e in call["env"]], ["SPARKLE_DEEP_TRACE"])
        [row] = self.results()
        self.assertEqual(row["effective_env"], "SPARKLE_DEEP_TRACE=<case>/stages.log")
        self.assertEqual(row["cleared_env"], "SPARKLE_DEEP_NOTHM;SPARKLE_DEEP_SHARE;SPARKLE_DEEP_TRACE_ONLY;"
                                             "SPARKLE_NO_REGDEDUP;SPARKLE_PROFILE")
        self.assertEqual(row["trace_only"], "no")

    def test_profile_setting_explicit(self):
        self.single_ok(1)
        self.run_u0("case", "1", "profile", SPARKLE_DEEP_SHARE="1")
        [call] = self.fake_calls("1")
        self.assertEqual(sorted(e.split("=")[0] for e in call["env"]),
                         ["SPARKLE_DEEP_DEBUG", "SPARKLE_DEEP_TRACE", "SPARKLE_PROFILE"])

    # ------------------------------------------------------------ P1-3 b
    def test_resume_same_sha_reuses_other_sha_new_attempt(self):
        self.single_ok(1)
        self.run_u0("case", "1", "default")
        rid_a = open(os.path.join(self.out, "CURRENT_RUN_ID")).read().strip()
        r = self.run_u0("case", "1", "default")
        self.assertIn("reuse R001_default attempt-001", r.stdout)
        self.assertEqual(len(self.fake_calls("1")), 1)
        sha_b = self.fx.commit_change("lean-toolchain", "leanprover/lean4:v4.32.1\n\n")   # unrelated change
        self.run_u0("case", "1", "default")
        rid_b = open(os.path.join(self.out, "CURRENT_RUN_ID")).read().strip()
        self.assertNotEqual(rid_a, rid_b)
        self.assertEqual(len(self.fake_calls("1")), 2)
        self.assertEqual(sorted(os.listdir(os.path.join(self.out, "cases", "R001_default"))),
                         ["attempt-001", "attempt-002"])
        rows_b = self.results()
        self.assertEqual([x["src_sha"] for x in rows_b], [sha_b])
        with open(os.path.join(self.out, "results", rid_a, "results.tsv")) as f:
            rows_a = list(csv.DictReader(f, delimiter="\t"))
        self.assertEqual([x["src_sha"] for x in rows_a], [self.fx.commit])
        # REDO at the same SHA: a third attempt, still exactly one row
        self.run_u0("case", "1", "default", REDO="1")
        self.assertEqual(len(self.results()), 1)
        self.assertEqual(self.results()[0]["attempt"], "attempt-003")

    def test_unfinished_attempt_not_reused(self):
        self.single_ok(1)
        self.run_u0("case", "1", "default")
        d = os.path.join(self.out, "cases", "R001_default", "attempt-001")
        os.remove(os.path.join(d, "done"))
        os.remove(os.path.join(d, "run.txt"))
        r = self.run_u0("case", "1", "default")
        self.assertNotIn("reuse R001", r.stdout)
        [row] = self.results()
        self.assertEqual(row["attempt"], "attempt-002")

    def test_source_change_changes_case_hash(self):
        self.single_ok(1)
        self.run_u0("case", "1", "default")
        h1 = self.results()[0]["case_hash"]
        src = open(os.path.join(self.fx.repo, "Src/A.lean")).read().replace("set_option maxHeartbeats 400000",
                                                                             "set_option maxHeartbeats 800000")
        self.fx.commit_change("Src/A.lean", src)
        self.run_u0("case", "1", "default")
        self.assertNotEqual(self.results()[0]["case_hash"], h1)

    # ------------------------------------------------------------ P1-3 c
    def alive(self, pid):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        st = open(f"/proc/{pid}/stat").read() if os.path.exists(f"/proc/{pid}/stat") else ""
        return not st or st[st.rfind(")") + 2] != "Z"

    def test_timeout_kills_and_reaps_whole_tree(self):
        self.single_ok(6, sleep=120, children=2, setsid_child=True, orphan_child=True)
        t0 = time.monotonic()
        r = self.run_u0("case", "6", "default", U0_TMO="2", U0_GRACE="1")
        self.assertLess(time.monotonic() - t0, 30)
        [row] = self.results()
        self.assertEqual(row["timeout"], "yes")
        self.assertTrue(row["term"].startswith("timeout("), row["term"])
        self.assertEqual(row["reaped"], "yes")
        self.assertEqual(row["mem_evidence"], "")
        pids = [int(x) for x in open(self.pids).read().split()]
        self.assertEqual(len(pids), 4)
        time.sleep(0.2)
        self.assertEqual([p for p in pids if self.alive(p)], [])
        self.assertEqual(r.returncode, 0)

    def test_strays_after_normal_exit_killed(self):
        self.single_ok(6, children=1, orphan_child=True)
        self.run_u0("case", "6", "default")
        [row] = self.results()
        self.assertEqual((row["term"], row["reaped"]), ("exit_0", "yes"))
        pids = [int(x) for x in open(self.pids).read().split()]
        time.sleep(0.2)
        self.assertEqual([p for p in pids if self.alive(p)], [])

    def test_signal_not_called_oom(self):
        self.single_ok(10, self_signal=signal.SIGKILL)
        self.single_ok(12, exit=137)
        self.run_u0("case", "10", "default")
        self.run_u0("case", "12", "default")
        rows = {x["row"]: x for x in self.results()}
        self.assertEqual(rows["10"]["term"], "signal_9")
        self.assertEqual(rows["12"]["term"], "exit_137(signal_unknown)")
        self.assertEqual((rows["10"]["mem_evidence"], rows["12"]["mem_evidence"]), ("", ""))
        self.assertNotIn("oom", "\t".join(rows["10"].values()).lower())

    def test_peak_rss_counts_child_not_wrapper(self):
        self.single_ok(7, mem_mb=200)
        self.single_ok(1)
        self.run_u0("case", "7", "default")
        self.run_u0("case", "1", "default")
        rows = {x["row"]: x for x in self.results()}
        big, small = int(rows["7"]["peak_rss_kb"]), int(rows["1"]["peak_rss_kb"])
        self.assertGreater(big, 190 * 1024, rows["7"])     # the grandchild's 200 MB is seen
        self.assertLess(small, 120 * 1024, rows["1"])       # and a case without it is small (per case, not cumulative)
        self.assertIn("largest single", rows["7"]["peak_rss_source"])

    # ------------------------------------------------------------ P1-3 d
    def test_harness_errors_continue_and_report_incomplete(self):
        self.single_ok(1)
        self.single_ok(5)
        self.single_ok(3, top="baz3")
        wrapper = os.path.join(self.base, "gen_wrapper.py")
        open(wrapper, "w").write(
            "import os, sys, runpy\n"
            "if 'classify' in sys.argv and any('R003' in a for a in sys.argv):\n"
            "    sys.exit('injected classifier failure')\n"
            f"sys.argv[0] = {GEN!r}\n"
            f"runpy.run_path({GEN!r}, run_name='__main__')\n")
        lst = os.path.join(self.base, "rows.txt")
        open(lst, "w").write("1 default\n999 default\nabc\n3 default\n5 default\n")
        r = self.run_u0("list", lst, U0_GEN_PY=wrapper)
        self.assertEqual(r.returncode, 3, r.stdout + r.stderr)
        self.assertIn("INCOMPLETE", r.stdout.splitlines()[-1])
        rows = {x["row"]: x for x in self.results()}
        self.assertEqual(set(rows), {"1", "999", "3", "5"})
        self.assertEqual(rows["999"]["invocation"], "harness-error")
        self.assertIn("generator failed", rows["999"]["harness_error"])
        self.assertEqual(rows["3"]["invocation"], "harness-error")
        self.assertIn("classifier failed", rows["3"]["harness_error"])
        self.assertEqual(rows["5"]["invocation"], "deep-in-file")
        self.assertEqual(rows["1"]["invocation"], "deep-in-file")
        self.assertIn("harness_error=3", r.stdout)   # 999, abc, 3

    def test_runner_cannot_start_is_harness_error(self):
        self.single_ok(1)
        r = self.run_u0("case", "1", "default", U0_LEAN="/nonexistent/lean")
        self.assertEqual(r.returncode, 3)
        [row] = self.results()
        self.assertEqual(row["invocation"], "harness-error")
        self.assertIn("could not start", row["harness_error"])

    def test_missing_run_txt_is_harness_error(self):
        d = os.path.join(self.base, "case")
        os.makedirs(d)
        json.dump({"row": "1", "setting": "default", "invocation": "deep-in-file", "run": True,
                   "kind": "row", "base": "foo1", "route": "default"}, open(os.path.join(d, "meta.json"), "w"))
        row = u0_gen.classify_dir(d)
        self.assertEqual((row["invocation"], row["harness_error"]), ("harness-error", "run.txt missing"))

    def test_shell_wrapper_exit_status(self):
        lst = os.path.join(self.base, "rows.txt")
        open(lst, "w").write("999 default\n")
        json.dump(self.plan, open(self.plan_path, "w"))
        # u0_case.sh must not turn the incomplete run into success
        r = subprocess.run(["bash", os.path.join(VED, "u0_case.sh"), self.out, "--list", lst],
                           cwd=self.fx.repo, env=self.env(), capture_output=True, text=True)
        self.assertEqual(r.returncode, 3, r.stdout + r.stderr)


class ScanSource(unittest.TestCase):
    def test_comment_is_not_the_command(self):
        t = "/- #synthesizeVerilog f -/\nimport X\n#synthesizeVerilog f\n"
        s = u0_gen.scan_source(t, 99, "#synthesizeVerilog", "f")
        self.assertEqual((s["cmd_index"], s.get("uncertain_note")), (2, "line-moved 99->3"))

    def test_ambiguous_not_located(self):
        t = "import X\n#synthesizeVerilog f\n#synthesizeVerilog f\n"
        s = u0_gen.scan_source(t, 99, "#synthesizeVerilog", "f")
        self.assertIn("command-not-located(2 matches)", s["uncertain"])

    def test_unbalanced_end(self):
        t = "import X\nend Foo\n#synthesizeVerilog f\n"
        self.assertIn("unbalanced-end", u0_gen.scan_source(t, 3, "#synthesizeVerilog", "f")["uncertain"])

    def test_private_and_continuation(self):
        t = "import X\nnamespace N\nprivate def f := 1\n#writeDesign f\n  \"a\"\n#check 1\n"
        s = u0_gen.scan_source(t, 4, "#writeDesign", "f")
        self.assertTrue(s["private"])
        self.assertEqual(s["end_index"], 5)
        self.assertEqual(s["ns_stack"], ["N"])


if __name__ == "__main__":
    unittest.main()
