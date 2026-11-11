#!/usr/bin/env python3
"""Unit tests / false-success controls for the U1 measurement harness
(scripts/ved/u1_gen.py, u1_run.py).  No Lean: `kjob lake env lean` is replaced
by tests/fake_lean_u1.py; the inventory/source tree is a throw-away git repo
(the U0 test fixture).
Run:  python3 -I -m pytest scripts/ved/tests   (or plain unittest)
"""
import csv
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
VED = os.path.dirname(HERE)
RUN = os.path.join(VED, "u1_run.py")
GEN = os.path.join(VED, "u1_gen.py")
FAKE = os.path.join(HERE, "fake_lean_u1.py")
sys.dont_write_bytecode = True
sys.path.insert(0, VED)
sys.path.insert(0, HERE)
import u1_gen  # noqa: E402
from test_u0 import Fixture, sh  # noqa: E402


class U1Harness(unittest.TestCase):
    def setUp(self):
        self.base = tempfile.mkdtemp(prefix="u1test-")
        self.fx = Fixture(self.base)
        self.out = os.path.join(self.base, "out")
        self.plan_path = os.path.join(self.base, "plan.json")
        self.log = os.path.join(self.base, "fake.log")
        self.plan = {}

    def tearDown(self):
        shutil.rmtree(self.base, ignore_errors=True)

    def env(self, **extra):
        e = {k: v for k, v in os.environ.items() if not k.startswith(("SPARKLE_", "U0_", "U1_"))}
        e.update(U1_LEAN=f"{sys.executable} -I {FAKE}", U1_INV_COMMIT=self.fx.commit,
                 U1_INV_BLOB=self.fx.blob, FAKE_PLAN=self.plan_path, FAKE_LOG=self.log,
                 U1_TMO="30", U1_GRACE="1")
        e.update(extra)
        return e

    def run_u1(self, *args, out=None, **extra):
        json.dump(self.plan, open(self.plan_path, "w"))
        return subprocess.run([sys.executable, "-I", RUN, "--repo", self.fx.repo, "--out", out or self.out, *args],
                              env=self.env(**extra), capture_output=True, text=True, timeout=180)

    def results(self, name="results.tsv", out=None):
        out = out or self.out
        rid = open(os.path.join(out, "CURRENT_RUN_ID")).read().strip()
        with open(os.path.join(out, "results", rid, name)) as f:
            return list(csv.DictReader(f, delimiter="\t"))

    def one(self, row, route, **plan):
        if plan:
            self.plan[f"{row}:{route}"] = plan
        r = self.run_u1("case", str(row), route, REDO="1")
        self.assertIn(r.returncode, (0, 3), r.stdout + r.stderr)
        [rec] = [x for x in self.results() if x["row"] == str(row) and x["setting"] == route]
        return rec

    # ------------------------------------------------------------ happy path
    def test_u1_strict_yes_all_conditions(self):
        r = self.one(1, "u1")
        self.assertEqual(r["strict_counted"], "yes", r["strict_blockers"])
        self.assertEqual(r["strict_label"], "returned-IR strict: U1, reset=0, order-free")
        self.assertEqual((r["u1_status"], r["first_cause"], r["prep_status"]), ("ok", "none", "n/a"))
        self.assertEqual((r["probe_thm"], r["probe_type"], r["probe_outputs"], r["probe_axioms_std3"]),
                         ("theorem", "exact", "1", "yes"))
        self.assertEqual(r["kernel_sync"], "yes")
        self.assertEqual(r["opt_sv"], "not connected")
        self.assertEqual((r["t_u1_combined"], r["t_synthesis"], r["t_elab_kernel"]), ("2000", "combined", "combined"))
        self.assertEqual(r["t_deep_prep"], "n/a")
        self.assertEqual(r["decl_check"], "match")
        for c in ("src_sha", "toolchain", "case_hash", "harness_hash", "run_id", "attempt", "inv_commit"):
            self.assertTrue(r[c], c)

    def test_u1_deep_strict_and_prep_columns(self):
        r = self.one(1, "u1_deep", ms={"prep": 700, "u1": 300})
        self.assertEqual(r["strict_counted"], "yes", r["strict_blockers"])
        self.assertEqual((r["prep_status"], r["t_deep_prep"], r["t_u1_combined"]), ("ok", "700", "300"))

    # ------------------------------------------------------- false-success controls
    def test_a_ok_line_but_extra_axiom(self):
        r = self.one(1, "u1", probe={"axioms": ["propext", "Lean.ofReduceBool"]})
        self.assertEqual(r["u1_ok_line"], "yes")
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("axioms:Lean.ofReduceBool", r["strict_blockers"])
        self.assertEqual(r["first_cause"], "probe-rejected")

    def test_a2_sorry_and_trust_compiler(self):
        for ax in ("sorryAx", "Lean.trustCompiler"):
            r = self.one(2, "u1", probe={"axioms": ["propext", ax]})
            self.assertEqual(r["strict_counted"], "no", ax)

    def test_b_theorem_type_differs(self):
        r = self.one(1, "u1", probe={"type": "differs"})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("type:differs", r["strict_blockers"])

    def test_b2_mvars_or_levels(self):
        r = self.one(1, "u1", probe={"mvars": "type=false value=true fvars=false"})
        self.assertIn("mvars:yes", r["strict_blockers"])
        r = self.one(2, "u1", probe={"levels": "1"})
        self.assertEqual(r["strict_counted"], "no")

    def test_c_theorem_missing(self):
        r = self.one(1, "u1", probe={"thm": "absent"})
        self.assertEqual((r["u1_ok_line"], r["strict_counted"]), ("yes", "no"))
        self.assertIn("thm:absent", r["strict_blockers"])

    def test_c2_not_a_theorem(self):
        r = self.one(1, "u1", probe={"thm": "not-a-theorem"})
        self.assertEqual(r["strict_counted"], "no")

    def test_c3_mod_not_closed_or_contract_unbound(self):
        r = self.one(1, "u1", probe={"mod": "closed=false type=true"})
        self.assertEqual(r["strict_counted"], "no")
        r = self.one(2, "u1", probe={"contract": "other"})
        self.assertEqual(r["strict_counted"], "no")

    def test_d_multi_output_refused(self):
        r = self.one(3, "u1", u1=["refused", "multi-output", "2 output projections; refused"],
                     probe={"thm": "absent", "outs": "2"})
        self.assertEqual((r["u1_status"], r["first_cause"], r["refusal_stage"]), ("refused", "multi-output", "multi-output"))
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("synthesis", r["later_stages_not_reached"])

    def test_d2_multi_output_ok_line_still_not_strict(self):
        r = self.one(2, "u1", probe={"outs": "2"})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("outputs:2", r["strict_blockers"])

    def test_e_prep_failure_u1_not_reached(self):
        r = self.one(1, "u1_deep", prep_error="deep failed: something")   # fake still prints U1 OK
        self.assertEqual(r["prep_status"], "failed")
        self.assertEqual(r["u1_status"], "not-reached(prep failed)")
        self.assertEqual((r["first_cause"], r["strict_counted"]), ("prep", "no"))
        self.assertIn("deep failed", r["prep_error"])
        self.assertIn("proof", r["later_stages_not_reached"])

    def test_f_timeout(self):
        r = self.one_tmo(1, "u1", sleep=20)
        self.assertEqual((r["first_cause"], r["timeout"]), ("external-timeout", "yes"))

    def one_tmo(self, row, route, **plan):
        self.plan[f"{row}:{route}"] = plan
        out = os.path.join(self.base, "out_tmo")
        self.run_u1("case", str(row), route, out=out, U1_TMO="1", REDO="1")
        [rec] = self.results(out=out)
        return rec

    def test_f_self_sigkill_is_signal_not_oom(self):
        r = self.one(1, "u1", self_signal=9)
        self.assertEqual(r["first_cause"], "signal", r["term"])
        self.assertNotEqual(r["first_cause"], "oom")
        self.assertEqual(r["strict_counted"], "no")

    def _synthetic(self, run_txt, stdout=None, stderr=""):
        d = os.path.join(self.base, "syn")
        shutil.rmtree(d, ignore_errors=True)
        sh([sys.executable, "-I", GEN, "--repo", self.fx.repo, "--commit", self.fx.commit, "--blob", self.fx.blob,
            "gen", "--row", "1", "--setting", "u1", "--dir", d])
        open(os.path.join(d, "run.txt"), "w").write("".join(f"{k}={v}\n" for k, v in run_txt.items()))
        open(os.path.join(d, "stdout.txt"), "w").write(stdout or "")
        open(os.path.join(d, "stderr.txt"), "w").write(stderr)
        return u1_gen.classify_dir(d)

    def test_f_oom_requires_evidence(self):
        base = {"rc": "-9", "term": "signal_9", "timeout": "no", "wall_s": "1", "harness_error": ""}
        self.assertEqual(self._synthetic(dict(base, mem_evidence=""))["first_cause"], "signal")
        self.assertEqual(self._synthetic(dict(base, mem_evidence="cgroup_oom_kill+1"))["first_cause"], "oom")
        r = self._synthetic({"rc": "134", "term": "exit_134(signal_unknown)", "timeout": "no", "wall_s": "1",
                             "mem_evidence": "allocator_text", "harness_error": ""})
        self.assertEqual(r["first_cause"], "oom")
        # allocator text from a normal exit is NOT oom
        r = self._synthetic({"rc": "1", "term": "exit_1", "timeout": "no", "wall_s": "1",
                             "mem_evidence": "allocator_text", "harness_error": ""},
                            stdout="Case.lean:1:0: error: something\n")
        self.assertNotEqual(r["first_cause"], "oom")

    def test_missing_run_txt_is_harness_error(self):
        d = os.path.join(self.base, "syn2")
        sh([sys.executable, "-I", GEN, "--repo", self.fx.repo, "--commit", self.fx.commit, "--blob", self.fx.blob,
            "gen", "--row", "1", "--setting", "u1", "--dir", d])
        r = u1_gen.classify_dir(d)
        self.assertEqual((r["invocation"], r["first_cause"], r["strict_counted"]), ("harness-error", "harness-error", "no"))

    # ------------------------------------------------------- refusal classes
    def test_refusal_classes(self):
        cases = [("table", "table"), ("synthesis", "synthesis"), ("order", "order"), ("type", "type"),
                 ("proof", "proof"), ("kernel", "kernel"), ("audit", "audit"), ("checker", "checker")]
        for i, (stage, want) in enumerate(cases):
            r = self.one(40 + i, "u1", u1=["refused", stage, "boom"], probe={"thm": "absent"})
            self.assertEqual((r["first_cause"], r["refusal_stage"]), (want, stage))
            self.assertEqual(r["strict_counted"], "no")
        r = self.one(30, "u1", u1=["refused", "proof", "x"], probe={"thm": "absent"})
        self.assertEqual(r["later_stages_not_reached"], "kernel;audit")

    def test_missing_cases_and_runCircuitH_are_own_causes(self):
        r = self.one(20, "u1", u1=["refused", "synthesis", "Missing cases:\n(Prod.mk _ _)"], probe={"thm": "absent"})
        self.assertEqual((r["first_cause"], r["refusal_stage"]), ("missing-cases", "synthesis"))
        r = self.one(21, "u1", u1=["refused", "synthesis", "cannot find runCircuitH location"], probe={"thm": "absent"})
        self.assertEqual(r["first_cause"], "runCircuitH-location")
        r = self.one(22, "u1", u1=["error", "(deterministic) timeout at whnf, maximum number of heartbeats"],
                     probe={"thm": "absent"})
        self.assertEqual((r["u1_status"], r["first_cause"]), ("error", "uncaught-heartbeat"))

    def test_error_outside_block_is_separate(self):
        # reviewer P2-1: an error outside the block or a non-zero exit blocks strict
        r = self.one(1, "u1", exit=1, outside_error="unknown identifier 'zzz'")
        self.assertEqual((r["errors_outside_block"], r["first_cause"]), ("1", "case-error"))
        self.assertIn("zzz", r["errors_outside_first"])
        self.assertEqual(r["refusal_msg"], "")
        self.assertEqual((r["strict_counted"], r["case_ok"], r["probe_type"]), ("no", "no", "exact"))
        self.assertIn("rc:1", r["strict_blockers"])
        self.assertIn("outside-errors:1", r["strict_blockers"])

    def test_p2_ok_and_good_probe_but_case_failed(self):
        # VED U1 OK + a fully correct probe, then only a non-zero exit
        r = self.one(1, "u1", exit=1)
        self.assertEqual((r["u1_ok_line"], r["probe_type"], r["probe_axioms_std3"]), ("yes", "exact", "yes"))
        self.assertEqual((r["strict_counted"], r["case_ok"], r["strict_blockers"]), ("no", "no", "rc:1"))
        self.assertEqual((r["u1_status"], r["first_cause"]), ("ok-but-case-failed", "case-error"))
        # ... or only an error outside the block with exit 0
        r = self.one(2, "u1", outside_error="unknown identifier 'zzz'")
        self.assertEqual((r["strict_counted"], r["case_ok"], r["strict_blockers"]), ("no", "no", "outside-errors:1"))
        # the clean case stays strict
        r = self.one(5, "u1")
        self.assertEqual((r["strict_counted"], r["case_ok"]), ("yes", "yes"))

    def test_decl_mismatch_preexisting_and_ok_name(self):
        r = self.one(1, "u1", qualified="Other.foo1")
        self.assertIn("decl:mismatch", r["strict_blockers"])
        r = self.one(2, "u1", pre={"thm": True})
        self.assertIn("preexisting:yes", r["strict_blockers"])
        r = self.one(5, "u1", ok_thm="Outer.other.ved_u1")
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("ok-thm-name", r["strict_blockers"])

    def test_decl_scope_relative_inventory_name(self):
        # inventory `ns` empty + scope-relative name: a suffix match is the same
        # identifier resolved in the original scope (counterCdo in a namespace)
        r = self.one(300, "u1", resolved="Outer.foo300", qualified="foo300")
        self.assertEqual(r["decl_check"], "match-scoped")
        self.assertNotIn("decl:", r["strict_blockers"])
        r = self.one(300, "u1", resolved="Outer.foo3000", qualified="foo300")
        self.assertEqual(r["decl_check"], "mismatch")
        # with `ns` given the inventory name is fully qualified: no suffix rule
        r = self.one(1, "u1", resolved="X.Outer.foo1", qualified="Outer.foo1")
        self.assertEqual(r["decl_check"], "mismatch")

    def test_staged_refusal_keeps_stage_despite_text(self):
        # an unsolved-goal text that mentions runCircuitH / Missing cases is still [proof]
        r = self.one(23, "u1", u1=["refused", "proof", "unsolved goals\n⊢ runCircuitH (Missing cases:) x"],
                     probe={"thm": "absent"})
        self.assertEqual((r["first_cause"], r["refusal_stage"]), ("proof", "proof"))

    def test_case_text_u1_deep_runs_in_original_scope(self):
        # #verify_elab_deep names facts in the current namespace and #ved_u1_deep
        # reads them under the declaration's prefix: both must be outside the case namespace
        text, meta = self.gen_case(1, "u1_deep")
        i, j = text.index("#verify_elab_deep foo1"), text.index("#ved_u1_deep foo1")
        ends = [k for k in range(len(text)) if text.startswith("end VedU1Case_R1", k)]
        opens = [k for k in range(len(text)) if text.startswith("namespace VedU1Case_R1", k)]
        self.assertEqual(len(ends), 2); self.assertEqual(len(opens), 2)
        self.assertTrue(opens[0] < ends[0] < i < j < opens[1] < ends[1])
        self.assertLess(text.index("#vedu1_t \"probe_end\""), ends[1])
        text1, _ = self.gen_case(1, "u1")
        k = text1.index("#ved_u1 foo1")
        self.assertTrue(text1.index("namespace VedU1Case_R1") < k < text1.index("end VedU1Case_R1"))

    def test_probe_crash_not_strict_unresolved(self):
        r = self.one(1, "u1", probe_fail="boom")
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("probe-missing", r["strict_blockers"])
        r = self.one(2, "u1", decl="absent", u1=["error", "unknown identifier 'foo2'"])
        self.assertEqual((r["invocation"], r["first_cause"], r["u1_status"]), ("unresolved-name", "unresolved", "unresolved"))

    def test_ok_without_probe_confirmation_never_strict_yes(self):
        """exhaustive: any single probe field deviating from the good value blocks strict"""
        good = {"thm": "theorem", "type": "exact", "mvars": "type=false value=false fvars=false", "levels": "0",
                "mod": "closed=true type=true", "contract": "bound-to-mod", "outs": "1", "axioms": ["propext"]}
        bad = {"thm": "absent", "type": "differs", "mvars": "type=true value=false fvars=false", "levels": "2",
               "mod": "absent", "contract": "absent", "outs": "0", "axioms": ["propext", "Lean.ofReduceBool"]}
        for k, v in bad.items():
            r = self.one(7, "u1", probe=dict(good, **{k: v}))
            self.assertEqual(r["strict_counted"], "no", k)
        self.assertEqual(self.one(7, "u1", probe=good)["strict_counted"], "yes")

    # ------------------------------------------------------- unsupported rows & case text
    def test_unsupported_rows_kept_not_run(self):
        for row in (4, 13):
            r = self.one(row, "u1")
            self.assertEqual((r["invocation"], r["ran"], r["strict_counted"]), ("unsupported-invocation", "no", "no"))
            self.assertEqual(r["first_cause"], "unsupported-invocation")
        self.assertFalse(os.path.exists(self.log))

    def test_source_missing_row_kept_not_harness_error(self):
        sh(["git", "rm", "-q", "Src/A.lean"], cwd=self.fx.repo)
        r = self.one(1, "u1")
        self.assertEqual((r["invocation"], r["ran"], r["first_cause"], r["harness_error"]),
                         ("source-missing", "no", "source-missing", ""))

    def test_inventory_327(self):
        out = sh([sys.executable, "-I", GEN, "--repo", self.fx.repo, "--commit", self.fx.commit,
                  "--blob", self.fx.blob, "rows"]).stdout
        self.assertEqual(len(out.splitlines()), 327)
        bad = subprocess.run([sys.executable, "-I", GEN, "--repo", self.fx.repo, "--commit", self.fx.commit,
                              "--blob", "0" * 40, "rows"], capture_output=True, text=True)
        self.assertNotEqual(bad.returncode, 0)

    def gen_case(self, row, route):
        d = os.path.join(self.base, f"g{row}{route}")
        sh([sys.executable, "-I", GEN, "--repo", self.fx.repo, "--commit", self.fx.commit, "--blob", self.fx.blob,
            "gen", "--row", str(row), "--setting", route, "--dir", d])
        return open(os.path.join(d, "Case.lean")).read(), json.load(open(os.path.join(d, "meta.json")))

    def test_case_text_u1(self):
        text, meta = self.gen_case(3, "u1")
        orig = open(os.path.join(self.fx.repo, "Src/A.lean")).read().splitlines()
        lines = text.splitlines()
        b, e = meta["block_begin"], meta["block_end"]
        self.assertTrue(lines[b - 1 + 1].startswith("-- ===== VED U1 BEGIN") or lines[b - 1].startswith("-- ====="))
        stripped = lines[:b - 2] + lines[e:]       # blank separator line precedes the block
        stripped = [ln for ln in stripped if not ln.startswith(("import Tools.VedU1Entry", "import Tools.VedStrictAudit"))]
        self.assertEqual(stripped, orig)
        # block sits right after the original command
        k = lines.index("#synthesizeVerilog baz3")
        self.assertTrue(lines[k + 1] == "" and lines[k + 2].startswith("-- ===== VED U1 BEGIN row 3 route u1"))
        self.assertIn("set_option Elab.async false in\n#ved_u1 baz3\n", text)
        self.assertNotIn("#ved_u1_deep", text)
        self.assertNotIn("#verify_elab_deep", text)
        self.assertIn("import Tools.VedU1Entry", text)
        self.assertNotIn("import Tools.DeepElab", text)
        self.assertIn("namespace VedU1Case_R3\n", text)
        self.assertTrue(meta["scan_private"])

    def test_case_text_u1_deep_order(self):
        text, meta = self.gen_case(1, "u1_deep")
        i = text.index("#verify_elab_deep foo1")
        j = text.index("#ved_u1_deep foo1")
        self.assertLess(i, j)
        self.assertIn("set_option Elab.async false in\n#verify_elab_deep foo1\n", text)
        self.assertIn("set_option Elab.async false in\n#ved_u1_deep foo1\n", text)
        self.assertIn("import Tools.VedU1Deep", text)
        self.assertEqual(set(meta["segs"]), {"pre", "prep", "u1", "probe"})
        lines = text.splitlines()
        lo, hi = meta["segs"]["prep"]
        self.assertTrue(any(l.startswith("#verify_elab_deep") for l in lines[lo - 1:hi]))

    def test_case_text_u1_deep_ns_in_decl_namespace(self):
        text, meta = self.gen_case(1, "u1_deep_ns")
        self.assertIn('elab "#vedu1_in_declns "', text)
        self.assertIn("withNamespace scope do", text)
        self.assertIn("#vedu1_in_declns foo1\nset_option Elab.async false in\n#verify_elab_deep foo1\n", text)
        self.assertIn("#vedu1_in_declns foo1\nset_option Elab.async false in\n#ved_u1_deep foo1\n", text)
        ends = [k for k in range(len(text)) if text.startswith("end VedU1Case_R1", k)]
        i = text.index("#verify_elab_deep foo1")
        self.assertTrue(ends[0] < i)
        self.assertEqual(set(meta["segs"]), {"pre", "prep", "u1", "probe"})

    def test_u1_deep_ns_is_its_own_route_in_union(self):
        self.plan["1:u1"] = {"u1": ["refused", "proof", "x"], "probe": {"thm": "absent"}}
        self.plan["1:u1_deep"] = {"u1": ["refused", "proof", "foo1_deep missing"], "probe": {"thm": "absent"}}
        self.plan["1:u1_deep_ns"] = {}
        lst = os.path.join(self.base, "l.txt")
        open(lst, "w").write("1 u1\n1 u1_deep\n1 u1_deep_ns\n")
        r = self.run_u1("list", lst)
        self.assertIn(r.returncode, (0, 3), r.stdout + r.stderr)
        [u] = self.results("union.tsv")
        self.assertEqual((u["u1_strict"], u["u1_deep_strict"], u["u1_deep_ns_strict"], u["union_std_strict"],
                          u["union_strict"], u["union_strict_routes"]), ("no", "no", "yes", "no", "yes", "u1_deep_ns"))

    def test_u1_deep_ns_requires_same_constant_inside_namespace(self):
        r = self.one(1, "u1_deep_ns")
        self.assertEqual((r["strict_counted"], r["ns_check"]), ("yes", "same"))
        self.assertEqual(r["ns_scope"], "Outer")
        self.assertTrue(r["prep_command"].startswith("#vedu1_in_declns #verify_elab_deep"))
        # the bare name picks another constant inside the namespace: never strict
        r = self.one(2, "u1_deep_ns", ns_inner="Outer.Other.bar2")
        self.assertEqual((r["strict_counted"], r["ns_check"]), ("no", "differs"))
        self.assertIn("ns:differs", r["strict_blockers"])
        r = self.one(5, "u1")
        self.assertEqual(r["ns_check"], "n/a")

    def test_specialised_statement(self):
        # reviewer 2026-11-10: `@decl defaultDomain` statements; the OK line's
        # "specialised" claim must match the statement the probe rebuilt
        r = self.one(1, "u1", ok_specialised=True, domains=1)
        self.assertEqual((r["strict_counted"], r["u1_ok_specialised"], r["probe_domains"]), ("yes", "yes", "1"))
        r = self.one(2, "u1", ok_specialised=True, domains=0)
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("specialised-mismatch:ok=yes,domains=0", r["strict_blockers"])
        r = self.one(5, "u1", domains=1)
        self.assertIn("specialised-mismatch:ok=no,domains=1", r["strict_blockers"])
        # the stored type over the unapplied constant (old expected type): differs
        r = self.one(1, "u1", ok_specialised=True, domains=1, probe={"type": "differs"})
        self.assertIn("type:differs", r["strict_blockers"])
        # no STMT line from the probe: never strict
        r = self.one(2, "u1", domains=None)
        self.assertIn("stmt-domains:unknown", r["strict_blockers"])

    def test_u1_deep_ns_root_level_declaration(self):
        # reviewer P1-1: a root-level name opens no namespace (the u1_deep command)
        r = self.one(1, "u1_deep_ns", resolved="foo1", qualified="foo1")
        self.assertEqual((r["strict_counted"], r["ns_check"], r["ns_scope"], r["ns_mode"]),
                         ("yes", "same", "_root_", "root"))
        r = self.one(2, "u1_deep_ns")
        self.assertEqual(r["ns_mode"], "ns")

    def test_u1_deep_ns_wrapper_failure_is_harness_error(self):
        # `invalid scope` (harness before 2026-11-10) and the wrapper's own
        # HARNESS-FAIL line: undetermined, never a prep refusal
        for msg in ("invalid scope", "VED U1N HARNESS-FAIL foo1 scope=X: invalid scope"):
            r = self.one(1, "u1_deep_ns", ns_wrapper_fail=msg, prep_error="no registers")
            self.assertEqual((r["first_cause"], r["strict_counted"]), ("harness-error(ns-wrapper)", "no"), msg)
            self.assertIn("namespace wrapper failed", r["harness_error"])
            self.assertIn("harness-error", r["strict_blockers"])
        # the same message on another route is not a wrapper failure
        r = self.one(1, "u1_deep", prep_error="invalid scope")
        self.assertEqual(r["first_cause"], "prep")

    def test_case_text_u1_deep_ns_root_and_private(self):
        text, _ = self.gen_case(1, "u1_deep_ns")
        self.assertIn("privateToUserName? n", text)
        self.assertIn("if scope.isAnonymous then", text)
        self.assertIn("VED U1N HARNESS-FAIL", text)

    # ------------------------------------------------------- u1_packed route
    def test_packed_strict(self):
        r = self.one(1, "u1_packed")
        self.assertEqual(r["strict_counted"], "yes", r["strict_blockers"])
        self.assertEqual((r["u1_status"], r["first_cause"], r["prep_status"]), ("ok", "none", "n/a"))
        self.assertEqual((r["probe_type"], r["probe_outputs"], r["u1_ok_line"]), ("exact", "2", "yes"))
        self.assertTrue(r["probe_slices"].startswith("equal expected=[(4,8),(0,4)]"), r["probe_slices"])
        self.assertTrue(r["probe_port"].startswith("match module=[(out, 12)]"), r["probe_port"])
        self.assertEqual(r["u1_command"], "#ved_u1_packed foo1")
        # three leaves, specialised statement
        r = self.one(2, "u1_packed", ok_specialised=True, domains=1, probe={"leaves": "8,1,4"})
        self.assertEqual(r["strict_counted"], "yes", r["strict_blockers"])
        self.assertIn("expected=[(5,8),(4,1),(0,4)]", r["probe_slices"])

    def test_packed_case_text(self):
        text, meta = self.gen_case(1, "u1_packed")
        self.assertIn("set_option Elab.async false in\n#ved_u1_packed foo1\n", text)
        self.assertIn("import Tools.VedU1PackedEntry", text)
        self.assertNotIn("\n#ved_u1 foo1", text)
        self.assertIn("#vedu1_packed_probe foo1", text)
        self.assertIn("PackedStmt", text)
        self.assertEqual(set(meta["segs"]), {"pre", "u1", "probe"})
        lo, hi = meta["segs"]["probe"]
        self.assertIn("#vedu1_packed_probe foo1", "\n".join(text.splitlines()[lo - 1:hi]))

    def test_packed_probe_type_mismatch_not_strict(self):
        r = self.one(1, "u1_packed", probe={"type": "differs"})
        self.assertEqual((r["u1_ok_line"], r["strict_counted"]), ("yes", "no"))
        self.assertIn("type:differs", r["strict_blockers"])
        self.assertEqual(r["first_cause"], "probe-rejected")

    def test_packed_slice_map_mismatch_not_strict(self):
        r = self.one(1, "u1_packed", probe={"slices": "differs"})
        self.assertEqual((r["u1_ok_line"], r["strict_counted"]), ("yes", "no"))
        self.assertIn("slices:differs", r["strict_blockers"])
        r = self.one(2, "u1_packed", probe={"port": "differs"})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("port:differs", r["strict_blockers"])

    def test_packed_missing_probe_line_not_strict(self):
        # the probe crashes: nothing parsed
        r = self.one(1, "u1_packed", probe_fail="boom")
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("probe-missing", r["strict_blockers"])
        # ... or only the packed-specific lines are absent (an old probe): never strict
        d = os.path.join(self.base, "synp")
        shutil.rmtree(d, ignore_errors=True)
        sh([sys.executable, "-I", GEN, "--repo", self.fx.repo, "--commit", self.fx.commit, "--blob", self.fx.blob,
            "gen", "--row", "1", "--setting", "u1_packed", "--dir", d])
        meta = json.load(open(os.path.join(d, "meta.json")))
        out = open(os.path.join(self.base, "fake.out"), "w")
        json.dump({"1:u1_packed": {}}, open(self.plan_path, "w"))
        res = subprocess.run([sys.executable, "-I", FAKE, os.path.join(d, "Case.lean")], capture_output=True, text=True,
                             env=dict(os.environ, FAKE_PLAN=self.plan_path, FAKE_LOG=self.log))
        keep = [ln for ln in res.stdout.splitlines()
                if not ln.startswith(("VED U1P SLICES", "VED U1P PORT", "VED U1P LEAVES"))]
        open(os.path.join(d, "stdout.txt"), "w").write("\n".join(keep) + "\n")
        open(os.path.join(d, "stderr.txt"), "w").write("")
        open(os.path.join(d, "run.txt"), "w").write("rc=0\nterm=exit_0\ntimeout=no\nwall_s=1\nharness_error=\n")
        row = u1_gen.classify_dir(d)
        self.assertEqual(row["strict_counted"], "no")
        for b in ("leaves:unknown", "slices:unknown", "port:unknown"):
            self.assertIn(b, row["strict_blockers"])
        # a plain `VED U1 OK` line (the #ved_u1 tool) is not the packed OK line
        txt = "\n".join(keep).replace("VED U1 PACKED OK", "VED U1 OK")
        open(os.path.join(d, "stdout.txt"), "w").write(txt + "\n")
        row = u1_gen.classify_dir(d)
        self.assertIn("no-VED-U1-PACKED-OK-line", row["strict_blockers"])
        del meta, out

    def test_packed_rc_nonzero_not_strict(self):
        r = self.one(1, "u1_packed", exit=1)
        self.assertEqual((r["u1_ok_line"], r["probe_type"], r["strict_counted"], r["strict_blockers"]),
                         ("yes", "exact", "no", "rc:1"))
        self.assertEqual(r["u1_status"], "ok-but-case-failed")

    def test_packed_single_output_or_too_few_leaves_not_strict(self):
        r = self.one(1, "u1_packed", probe={"leaves": "8"})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("leaves:1", r["strict_blockers"])
        r = self.one(2, "u1_packed", probe={"outs": "3"})      # output count differs from the probe's own leaves
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("leaves:2 outputs=3", r["strict_blockers"])

    def test_packed_refusal_stages(self):
        r = self.one(1, "u1_packed", u1=["refused", "packed", "not a packed result"], probe={"thm": "absent"})
        self.assertEqual((r["u1_status"], r["first_cause"], r["refusal_stage"]), ("refused", "packed", "packed"))
        self.assertEqual(r["strict_counted"], "no")
        self.assertEqual(r["later_stages_not_reached"], "synthesis;artifact;order;type;proof;kernel;audit")

    def test_packed_specialised_flag_checked(self):
        r = self.one(1, "u1_packed", ok_specialised=True, domains=0)
        self.assertIn("specialised-mismatch:ok=yes,domains=0", r["strict_blockers"])
        self.assertEqual(r["strict_counted"], "no")

    def test_packed_probe_in_control_matches_generator(self):
        # the Lean control embeds the generator's probe definition verbatim
        ctl = open(os.path.join(VED, "controls", "U1PackedControls.lean")).read()
        self.assertIn(u1_gen.PACKED_PROBE_DEF, ctl)

    def test_packed_own_route_and_separate_union(self):
        lst = os.path.join(self.base, "l.txt")
        open(lst, "w").write("1 u1\n1 u1_deep\n1 u1_packed\n2 u1_packed\n3 u1\n")
        self.plan["1:u1"] = {"u1": ["refused", "multi-output", "2 output projections"], "probe": {"thm": "absent"}}
        self.plan["1:u1_deep"] = {"u1": ["refused", "proof", "x"], "probe": {"thm": "absent"}}
        r = self.run_u1("list", lst)
        self.assertIn(r.returncode, (0, 3), r.stdout + r.stderr)
        un = {u["row"]: u for u in self.results("union.tsv")}
        # row 1: only u1_packed strict -> not in the old unions, in standard + packed
        self.assertEqual((un["1"]["u1_packed_strict"], un["1"]["union_std_strict"], un["1"]["union_strict"],
                          un["1"]["union_strict_routes"], un["1"]["union_std_packed_strict"],
                          un["1"]["union_std_packed_routes"]), ("yes", "no", "no", "", "yes", "u1_packed"))
        self.assertEqual((un["2"]["union_strict"], un["2"]["union_std_packed_strict"]), ("no", "yes"))
        self.assertEqual((un["3"]["u1_packed_strict"], un["3"]["union_std_packed_strict"]), ("missing", "yes"))
        rid = open(os.path.join(self.out, "CURRENT_RUN_ID")).read().strip()
        summ = open(os.path.join(self.out, "results", rid, "summary.txt")).read()
        self.assertIn("route u1_packed: records=2 strict_counted_yes=2", summ)
        self.assertIn("union (standard routes u1, u1_deep): distinct_rows=3 returned_IR_strict_rows=1", summ)
        self.assertIn("returned_IR_strict_rows_incl_namespace_assisted=1", summ)
        self.assertIn("returned_IR_strict_rows_std_plus_packed=3 strict_by_u1_packed=2", summ)

    # ------------------------------------------------------- union & runner
    def test_g_union_counting(self):
        lst = os.path.join(self.base, "rows.txt")
        open(lst, "w").write("1 u1\n1 u1_deep\n2 u1\n2 u1_deep\n5 u1\n5 u1_deep\n4 u1\n4 u1_deep\n")
        self.plan["2:u1"] = {"probe": {"thm": "absent"}}            # row 2: only deep strict
        self.plan["5:u1_deep"] = {"prep_error": "x"}                 # row 5: only u1 strict
        r = self.run_u1("list", lst)
        self.assertIn(r.returncode, (0, 3), r.stdout + r.stderr)
        recs = self.results()
        self.assertEqual(len(recs), 8)
        un = {u["row"]: u for u in self.results("union.tsv")}
        self.assertEqual(len(un), 4)
        self.assertEqual((un["1"]["u1_strict"], un["1"]["u1_deep_strict"], un["1"]["union_strict"]), ("yes", "yes", "yes"))
        self.assertEqual((un["2"]["u1_strict"], un["2"]["u1_deep_strict"], un["2"]["union_strict"]), ("no", "yes", "yes"))
        self.assertEqual((un["5"]["u1_strict"], un["5"]["u1_deep_strict"], un["5"]["union_strict"]), ("yes", "no", "yes"))
        self.assertEqual(un["4"]["union_strict"], "no")
        rid = open(os.path.join(self.out, "CURRENT_RUN_ID")).read().strip()
        summ = open(os.path.join(self.out, "results", rid, "summary.txt")).read()
        self.assertIn("route u1: records=4 strict_counted_yes=2", summ)
        self.assertIn("route u1_deep: records=4 strict_counted_yes=2", summ)
        self.assertIn("union (standard routes u1, u1_deep): distinct_rows=4 returned_IR_strict_rows=3", summ)

    # ------------------------------------------------------------ u1_hier route
    def test_hier_strict_yes_and_columns(self):
        r = self.one(1, "u1_hier")
        self.assertEqual(r["strict_counted"], "yes", r["strict_blockers"])
        self.assertEqual((r["u1_status"], r["first_cause"], r["prep_status"]), ("ok", "none", "n/a"))
        self.assertEqual((r["probe_design"], r["probe_hier_top"], r["probe_hier_modules"], r["probe_ports"]),
                         ("closed=true type=true", "ok", "2", "ok"))
        self.assertEqual(r["probe_hier_children"], "kidA;kidB")
        self.assertEqual(r["probe_hier_child_thms"], "kidA=theorem;kidB=theorem")
        self.assertIn("synth_ms=14", r["tool_reported"])
        self.assertEqual(r["u1_command"], "#ved_u1_hier foo1")

    def test_hier_case_text_runs_in_original_scope_with_hier_probe(self):
        d = os.path.join(self.base, "c")
        sh([sys.executable, "-I", GEN, "--repo", self.fx.repo, "--commit", self.fx.commit, "--blob", self.fx.blob,
            "gen", "--row", "1", "--setting", "u1_hier", "--dir", d])
        text = open(os.path.join(d, "Case.lean")).read()
        self.assertIn("import Tools.VedU1HierEntry", text)
        self.assertIn("#ved_u1_hier foo1", text)
        self.assertNotIn("#verify_elab_deep", text)
        self.assertIn("Tools.VedU1Hier.U1HStmt", text)
        self.assertLess(text.index("#ved_u1_hier foo1"), text.index("VED U1P HIERTOP"))

    def test_hier_type_mismatch(self):
        r = self.one(1, "u1_hier", probe={"type": "differs"})
        self.assertEqual((r["u1_ok_line"], r["strict_counted"], r["first_cause"]), ("yes", "no", "probe-rejected"))
        self.assertIn("type:differs", r["strict_blockers"])

    def test_hier_missing_child_theorem(self):
        r = self.one(1, "u1_hier", hier={"child_thms": {"kidB": "absent"}})
        self.assertEqual((r["u1_ok_line"], r["strict_counted"], r["first_cause"]), ("yes", "no", "probe-rejected"))
        self.assertIn("child-thm:kidB=absent", r["strict_blockers"])
        r = self.one(2, "u1_hier", hier={"child_thms": {"kidA": "not-a-theorem"}})
        self.assertEqual(r["strict_counted"], "no")

    def test_hier_topmodule_mismatch(self):
        r = self.one(1, "u1_hier", hier={"top": "differs", "top_design": "Other"})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("topModule:differs(design=Other,mod=Top)", r["strict_blockers"])

    def test_hier_rc_nonzero(self):
        r = self.one(1, "u1_hier", exit=1)
        self.assertEqual((r["strict_counted"], r["u1_status"], r["first_cause"]), ("no", "ok-but-case-failed", "case-error"))
        self.assertIn("rc:1", r["strict_blockers"])

    def test_hier_missing_probe_line(self):
        for k in ("design", "ports"):
            r = self.one(1, "u1_hier", hier={k: None})
            self.assertEqual(r["strict_counted"], "no", k)
        r = self.one(1, "u1_hier", hier={"top": None})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("topModule:unknown", r["strict_blockers"])
        self.assertIn("children:unknown", r["strict_blockers"])
        r = self.one(1, "u1_hier", probe_fail="boom")
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("probe-missing", r["strict_blockers"])

    def test_hier_no_children_or_missing_instance_child(self):
        r = self.one(1, "u1_hier", hier={"mods": [0, "false", "true"], "children": [], "insts": ["bad", 0, "[]"]})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("modules:empty", r["strict_blockers"])
        r = self.one(2, "u1_hier", hier={"insts": ["bad", 2, "[kidC]"]})
        self.assertEqual(r["strict_counted"], "no")
        self.assertIn("instances:n=2,missing=[kidC]", r["strict_blockers"])

    def test_hier_preexisting_design_or_child(self):
        for k in ("design", "child"):
            r = self.one(1, "u1_hier", pre={k: True})
            self.assertEqual(r["strict_counted"], "no", k)
            self.assertIn("preexisting:yes", r["strict_blockers"])

    def test_hier_refusal_stage(self):
        r = self.one(1, "u1_hier", u1=["refused", "hier-shape", "no instance"], probe={"thm": "absent"})
        self.assertEqual((r["u1_status"], r["first_cause"], r["strict_counted"]), ("refused", "hier-shape", "no"))
        self.assertEqual(r["later_stages_not_reached"], "order;child;type;proof;kernel;audit")

    def test_hier_union_is_separate_from_standard_and_namespace_unions(self):
        for rt, plan in (("u1", {"u1": ["refused", "synthesis", "x"], "probe": {"thm": "absent"}}),
                         ("u1_deep", {"u1": ["refused", "proof", "x"], "probe": {"thm": "absent"}}),
                         ("u1_deep_ns", {"u1": ["refused", "proof", "x"], "probe": {"thm": "absent"}}),
                         ("u1_hier", {})):
            self.plan[f"1:{rt}"] = plan
        lst = os.path.join(self.base, "l.txt")
        open(lst, "w").write("1 u1\n1 u1_deep\n1 u1_deep_ns\n1 u1_hier\n")
        r = self.run_u1("list", lst)
        self.assertIn(r.returncode, (0, 3), r.stdout + r.stderr)
        [u] = self.results("union.tsv")
        self.assertEqual((u["u1_hier_strict"], u["union_std_strict"], u["union_strict"], u["union_strict_routes"],
                          u["union_std_hier_strict"]), ("yes", "no", "no", "", "yes"))
        rid = open(os.path.join(self.out, "CURRENT_RUN_ID")).read().strip()
        summ = open(os.path.join(self.out, "results", rid, "summary.txt")).read()
        self.assertIn("route u1_hier: records=1 strict_counted_yes=1", summ)
        self.assertIn("union (standard routes u1, u1_deep): distinct_rows=1 returned_IR_strict_rows=0", summ)
        self.assertIn("returned_IR_strict_rows_incl_namespace_assisted=0", summ)
        self.assertIn("returned_IR_strict_rows_std_plus_hier=1 hier_adds_over_standard=1", summ)

    def test_hier_lean_control_embeds_the_harness_probe(self):
        """controls/U1HierControls.lean is generated from the harness's own probe text: no drift."""
        sys.path.insert(0, os.path.join(VED, "controls"))
        import gen_u1hier_controls
        want = gen_u1hier_controls.render()
        have = open(os.path.join(VED, "controls", "U1HierControls.lean")).read()
        self.assertEqual(have, want, "regenerate: python3 -I scripts/ved/controls/gen_u1hier_controls.py "
                                     "scripts/ved/controls/U1HierControls.lean")
        self.assertIn(u1_gen.EVAL_HELP, have)

    def test_malformed_list_line_is_harness_error(self):
        lst = os.path.join(self.base, "rows.txt")
        open(lst, "w").write("1\n1 bogus_route\n")
        r = self.run_u1("list", lst)
        self.assertEqual(r.returncode, 3)
        self.assertIn("INCOMPLETE", r.stdout)

    def test_reuse_same_identity_new_attempt_on_redo(self):
        self.one(1, "u1")
        n1 = len(open(self.log).read().splitlines())
        self.run_u1("case", "1", "u1")
        self.assertEqual(len(open(self.log).read().splitlines()), n1)     # reused
        self.run_u1("case", "1", "u1", REDO="1")
        self.assertEqual(len(open(self.log).read().splitlines()), n1 + 1)
        self.assertEqual(len(self.results()), 1)                           # not double-counted

    def test_env_cleared_and_output_outside_tree(self):
        r = subprocess.run([sys.executable, "-I", RUN, "--repo", self.fx.repo, "--out",
                            os.path.join(self.fx.repo, "inside"), "case", "1", "u1"],
                           env=self.env(), capture_output=True, text=True)
        self.assertNotEqual(r.returncode, 0)
        rec = self.one(1, "u1", exit=0)
        self.assertNotIn("SPARKLE_FOO", rec["effective_env"])
        self.run_u1("case", "6", "u1", SPARKLE_FOO="1")
        rec = [x for x in self.results() if x["row"] == "6"][0]
        self.assertIn("SPARKLE_FOO", rec["cleared_env"])
        self.assertNotIn("SPARKLE_FOO", rec["effective_env"])

    def test_merge_shards(self):
        s1, s2 = os.path.join(self.base, "s1"), os.path.join(self.base, "s2")
        self.run_u1("case", "1", "u1", out=s1)
        self.run_u1("case", "1", "u1_deep", out=s2)
        m = os.path.join(self.base, "m")
        r = subprocess.run([sys.executable, "-I", RUN, "--out", m, "merge", s1, s2], capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("union (standard routes u1, u1_deep): distinct_rows=1 returned_IR_strict_rows=1", r.stdout)


if __name__ == "__main__":
    unittest.main()
