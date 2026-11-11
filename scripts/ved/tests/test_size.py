#!/usr/bin/env python3
"""Unit tests for the circuit-size harness (scripts/ved/size_gen.py, size_run.py).  No Lean and no
yosys: `kjob lake env lean` is tests/fake_lean_size.py, yosys is tests/fake_yosys.py; the
inventory/source tree is the U0 test fixture (a throw-away git repo).
Run:  python3 -I -m unittest discover -s scripts/ved/tests -p 'test_size.py'
"""
import csv
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
VED = os.path.dirname(HERE)
RUN = os.path.join(VED, "size_run.py")
FAKE_LEAN = os.path.join(HERE, "fake_lean_size.py")
FAKE_YS = os.path.join(HERE, "fake_yosys.py")
sys.dont_write_bytecode = True
sys.path.insert(0, VED)
sys.path.insert(0, HERE)
import size_gen  # noqa: E402
import size_run  # noqa: E402
from test_u0 import Fixture  # noqa: E402

# real `yosys 0.70` stat texts (trimmed)
GEN_FLAT = """
4. Printing statistics.

=== top ===

        +----------Local Count, excluding submodules.
        | 
     3767 wires
     5601 wire bits
        4 ports
     5576 cells
       72   $_ANDNOT_
     2048   $_DFFE_PP_
        8   $_DFF_P_
       13   $_XOR_

"""
GEN_HIER = """
=== top ===

        +----------Local Count, excluding submodules.
        | 
        4 wires
        2 submodules
        2   sub

=== sub ===

        +----------Local Count, excluding submodules.
        | 
        7 wires
       10 cells
        4   $_DFF_P_
        6   $_XOR_

=== design hierarchy ===

        +----------Count including submodules.
        | 
       20 top
       10 sub

        +----------Count including submodules.
        | 
       18 wires
        - memories
       20 cells
        8   $_DFF_P_
       12   $_XOR_
        2 submodules
        2   sub

"""
FPGA = """
=== top ===

        +----------Local Count, excluding submodules.
        | 
      294 wires
      328 cells
        8   ALU
        8   DFF
        2   DFFE
        1   GND
        7   LUT1
       27   LUT3
      142   LUT4
       50   MUX2_LUT5
        4   SP
       32   RAM16SDP4
        1   VCC

"""


ELAB = """namespace Sparkle.Compiler.Elab
elab "#synthesizeVerilog" id:ident : command => do
  let (module, _) ← synthesizeCombinational declName
  let optimized := Sparkle.IR.Optimize.optimizeModule module
  let verilog := toVerilog optimized
  IO.println verilog
/-- doc -/
elab "#synthesizeVerilogDesign" id:ident : command => do
  let design ← synthesizeHierarchical declName
  IO.println (toVerilogDesign design)

elab "#writeVerilogDesign" id:ident str:str : command => do
  let design ← synthesizeHierarchical declName
  IO.FS.writeFile path (toVerilogDesign design)

private def writeDesignCore (declName : Name) : TermElabM Unit := do
  let design ← synthesizeHierarchical declName
  let verilog := toVerilogDesign design

elab "#writeDesign" id:ident svPath:str cppPath:str : command => do
  writeDesignCore declName svPath.getString cppPath.getString none
end Sparkle.Compiler.Elab
"""


class ParseStat(unittest.TestCase):
    def test_generic_flat(self):
        st = size_gen.parse_stat(GEN_FLAT, "top")
        self.assertEqual(st["cells"], 5576)
        self.assertEqual(size_gen.generic_numbers(st), {"cells": 5576, "dff": 2056, "unresolved": 0})

    def test_generic_hierarchy_uses_totals_including_submodules(self):
        st = size_gen.parse_stat(GEN_HIER, "top")
        self.assertEqual(st["cells"], 20)
        self.assertEqual(st["types"], {"$_DFF_P_": 8, "$_XOR_": 12})
        self.assertEqual(size_gen.generic_numbers(st)["dff"], 8)

    def test_fpga(self):
        st = size_gen.parse_stat(FPGA, "top")
        n = size_gen.fpga_numbers(st)
        self.assertEqual(n, {"cells": 328, "lut": 7 + 27 + 142, "ff": 10, "bram": 4, "lutram": 32})

    def test_unresolved_instances_are_counted(self):
        st = size_gen.parse_stat(GEN_FLAT.replace("13   $_XOR_", "13   $_XOR_\n        2   kid"), "top")
        self.assertEqual(size_gen.generic_numbers(st)["unresolved"], 2)

    def test_garbage_and_wrong_top(self):
        self.assertIsNone(size_gen.parse_stat("nothing useful\n", "top"))
        self.assertIsNone(size_gen.parse_stat(GEN_FLAT, "other"))

    def test_empty_design_is_zero_cells_not_missing(self):
        t = "=== top ===\n\n        +----------Local Count, excluding submodules.\n        | \n        4 wires\n"
        self.assertEqual(size_gen.parse_stat(t, "top")["cells"], 0)


class SizeHarness(unittest.TestCase):
    def setUp(self):
        self.base = tempfile.mkdtemp(prefix="sizetest-")
        self.fx = Fixture(self.base)
        self.plan_path = os.path.join(self.base, "plan.json")
        self.log = os.path.join(self.base, "fake.log")
        self.ys_log = os.path.join(self.base, "ys.log")
        self.plan, self.ys = {}, {}
        self.write_elab(ELAB)

    def tearDown(self):
        shutil.rmtree(self.base, ignore_errors=True)

    def write_elab(self, text):
        path = os.path.join(self.fx.repo, "Sparkle/Compiler/Elab.lean")
        os.makedirs(os.path.dirname(path), exist_ok=True)
        open(path, "w").write(text)

    def env(self, **extra):
        e = {k: v for k, v in os.environ.items() if not k.startswith(("SPARKLE_", "U0_", "U1_", "SIZE_"))}
        e.update(SIZE_LEAN=f"{sys.executable} -I {FAKE_LEAN}", SIZE_YOSYS=f"{sys.executable} -I {FAKE_YS}",
                 SIZE_INV_COMMIT=self.fx.commit, SIZE_INV_BLOB=self.fx.blob, FAKE_PLAN=self.plan_path,
                 FAKE_LOG=self.log, FAKE_YS=json.dumps(self.ys), FAKE_YS_LOG=self.ys_log,
                 SIZE_TMO="30", SIZE_GRACE="1", SIZE_YOSYS_TMO="30")
        e.update(extra)
        return e

    def run_size(self, *args, out=None, **extra):
        json.dump(self.plan, open(self.plan_path, "w"))
        return subprocess.run([sys.executable, "-I", RUN, "--repo", self.fx.repo, "--out", out or self.out(), *args],
                              env=self.env(**extra), capture_output=True, text=True, timeout=180)

    def out(self, name="out"):
        return os.path.join(self.base, name)

    def results(self, out=None):
        out = out or self.out()
        rid = open(os.path.join(out, "CURRENT_RUN_ID")).read().strip()
        with open(os.path.join(out, "results", rid, "results.tsv")) as f:
            return list(csv.DictReader(f, delimiter="\t"))

    def one(self, row, out=None, **extra):
        r = self.run_size("case", str(row), out=out, REDO="1", **extra)
        self.assertIn(r.returncode, (0, 3), r.stdout + r.stderr)
        [rec] = [x for x in self.results(out) if x["row"] == str(row)]
        return rec

    # -------------------------------------------------------------- the record
    def test_module_row_record(self):
        sv = "module foo1();\n  wire w;\nendmodule\n"
        self.plan["1"] = {"sv": sv, "mods": [{"name": "foo1", "regs": 2, "stmts": 5, "wires": 3, "regbits": 16, "mems": 1,
                                              "membits": 64}], "kids": ["kidA"]}
        r = self.one(1)
        self.assertEqual((r["invocation"], r["size_status"], r["cmd_kind"]), ("size-in-file", "ok", "module"))
        self.assertEqual(r["sv_sha256"], hashlib.sha256(sv.encode()).hexdigest())
        kid = "module kidA(); endmodule\n"
        self.assertEqual(r["children_sha256"], hashlib.sha256(kid.encode()).hexdigest())
        self.assertEqual(r["sv_identity"], hashlib.sha256(sv.encode() + b"\0" + kid.encode()).hexdigest())
        self.assertEqual((r["ir_regs"], r["ir_mems"], r["ir_stmts"], r["ir_wires"], r["ir_regbits"], r["ir_membits"]),
                         ("2", "1", "5", "3", "16", "64"))
        self.assertEqual((r["ir_modules"], r["sv_modules"], r["children_modules"]), ("2", "1", "1"))
        self.assertEqual((r["irtop_regs"], r["irtop_regbits"]), ("2", "16"))
        self.assertEqual((r["g_status"], r["f_status"]), ("ok", "ok"))
        n = len(sv)
        self.assertEqual((r["g_cells"], r["g_dff"], r["f_lut"], r["f_ff"], r["f_bram"]), (str(n + 10), "6", str(n + 3), "6", "1"))
        self.assertEqual(r["ys_files"], "size_sv.sv;size_children.sv")
        self.assertIn("Yosys 0.70", r["ys_version"])
        self.assertEqual(r["g_script"], "read_verilog -sv size_sv.sv size_children.sv; hierarchy -top foo1; synth -top foo1; stat")
        self.assertEqual(r["f_script"], "read_verilog -sv size_sv.sv size_children.sv; hierarchy -top foo1; synth_gowin -top foo1; stat")

    def test_design_row_args_waived_and_every_module_hashed(self):
        self.plan["13"] = {"mods": [{"name": "wd13", "regs": 1}, {"name": "sub13", "regs": 3}]}
        r = self.one(13)
        self.assertEqual((r["invocation"], r["args_waived"], r["cmd_kind"]), ("size-in-file", "yes", "design"))
        self.assertEqual(r["sv_modules"], "2")
        self.assertEqual(r["sv_join_check"], "yes")
        self.assertEqual([x.split(":")[0] for x in r["sv_module_sha256"].split(";")], ["wd13", "sub13"])
        self.assertEqual(r["ir_regs"], "4")           # every module of the hierarchy
        self.assertEqual(r["irtop_regs"], "1")        # the top alone
        text = open(os.path.join(self.out(), "cases", "R013_size", "attempt-001", "size_sv.sv")).read()
        self.assertEqual(r["sv_sha256"], hashlib.sha256(text.encode()).hexdigest())

    def test_unsupported_and_source_missing_stay_in_the_set(self):
        r = self.one(4)
        self.assertEqual((r["invocation"], r["size_status"], r["g_status"], r["f_status"]),
                         ("unsupported-invocation", "not-run", "not-run", "not-run"))
        self.assertEqual((r["sv_sha256"], r["g_cells"], r["f_lut"], r["ir_regs"]), ("", "", "", ""))
        os.remove(os.path.join(self.fx.repo, "Src/A.lean"))
        r = self.one(2, out=self.out("out2"))
        self.assertEqual((r["invocation"], r["size_status"]), ("source-missing", "not-run"))

    def test_case_is_a_copy_with_a_block_after_the_command(self):
        self.one(1)
        text = open(os.path.join(self.out(), "cases", "R001_size", "attempt-001", "Case.lean")).read()
        src = open(os.path.join(self.fx.repo, "Src/A.lean")).read()
        self.assertTrue(text.startswith("/- a block comment"))
        i = text.index("-- ===== VED SIZE BEGIN row 1 ")
        self.assertIn("#synthesizeVerilog foo1\n", text[:i])
        self.assertEqual(text[:i].count("#synthesizeVerilog foo1"), 1)
        self.assertEqual(text[i:text.index("-- ===== VED SIZE END")].count("#synthesizeVerilog"), 0)   # the block does not re-run the command
        self.assertTrue(text.endswith(src[src.index("end Outer"):]))   # the rest of the file is untouched

    def test_synthesis_error_is_a_status_and_yosys_is_not_run(self):
        self.plan["1"] = {"err": "unknown constant 'foo1'"}
        r = self.one(1)
        self.assertEqual((r["size_status"], r["g_status"], r["f_status"]), ("synthesis-error", "not-run", "not-run"))
        self.assertIn("unknown constant", r["size_error"])
        self.assertEqual((r["sv_sha256"], r["g_cells"], r["ir_regs"]), ("", "", ""))
        self.assertFalse(os.path.exists(self.ys_log))

    def test_no_output_when_lean_writes_nothing(self):
        self.plan["1"] = {"nofiles": True}
        r = self.one(1)
        self.assertEqual(r["size_status"], "no-output")
        self.assertEqual(r["g_cells"], "")

    # ------------------------------------------------------------------ yosys
    def test_yosys_timeout_is_a_status_never_zero(self):
        self.ys = {"timeout": ["generic"]}
        r = self.one(1, SIZE_YOSYS_TMO="1")
        self.assertEqual(r["g_status"], "timeout")
        self.assertEqual((r["g_cells"], r["g_dff"]), ("", ""))
        self.assertIn("timeout", r["g_error"])
        self.assertEqual(r["f_status"], "ok")                 # the other flow is independent
        self.assertEqual(r["size_status"], "ok")

    def test_yosys_missing_top(self):
        self.ys = {"missing": ["foo1"]}
        r = self.one(1)
        self.assertEqual((r["g_status"], r["f_status"]), ("top-missing", "top-missing"))
        self.assertIn("not found", r["g_error"])
        self.assertEqual((r["g_cells"], r["f_lut"]), ("", ""))

    def test_yosys_error_nostat_garbage(self):
        self.ys = {"fail": ["generic"], "nostat": ["fpga"]}
        r = self.one(1)
        self.assertEqual((r["g_status"], r["f_status"]), ("error", "no-stat"))
        self.assertEqual((r["g_cells"], r["f_cells"], r["f_lut"]), ("", "", ""))
        self.ys = {"garbage": ["generic"]}
        r = self.one(1)
        self.assertEqual(r["g_status"], "no-stat")

    def test_yosys_missing_binary_is_an_error_status(self):
        r = self.one(1, SIZE_YOSYS="/nonexistent/yosys")
        self.assertEqual((r["g_status"], r["f_status"]), ("error", "error"))
        self.assertIn("cannot start", r["g_error"])

    def test_hierarchy_stat_is_used(self):
        self.ys = {"hier": ["generic"]}
        r = self.one(1)
        n = len("module foo1(); endmodule\n")
        self.assertEqual((r["g_status"], r["g_cells"], r["g_dff"]), ("ok", str(2 * n), "8"))

    def test_yosys_options_are_recorded_and_part_of_the_run_identity(self):
        r = self.one(1)
        self.assertEqual(r["ys_timeout_s"], "30")
        self.assertIn("fake_yosys.py", r["ys_cmd"])
        a = self.run_size("case", "1", out=self.out("o3"), SIZE_YOSYS_TMO="30")
        b = self.run_size("case", "1", out=self.out("o3"), SIZE_YOSYS_TMO="31")
        ids = {line.split()[2] for line in (a.stdout + b.stdout).splitlines() if line.startswith("SIZE SUMMARY")}
        self.assertEqual(len(ids), 2)

    # ---------------------------------------------------------------- compare
    def compare(self, a, b, out):
        return subprocess.run([sys.executable, "-I", RUN, "compare", a, b, "--out", out], capture_output=True, text=True)

    def test_compare_table(self):
        lst = os.path.join(self.base, "rows.txt")
        open(lst, "w").write("1\n2\n")
        self.plan = {"1": {"sv": "module foo1(); endmodule\n", "mods": [{"name": "foo1", "regs": 1}]},
                     "2": {"sv": "module bar2(); endmodule\n", "mods": [{"name": "bar2", "regs": 2}]}}
        self.assertIn(self.run_size("list", lst, out=self.out("A")).returncode, (0, 3))
        # B: row 1 unchanged, row 2 changed (longer SV, one more register)
        self.plan["2"] = {"sv": "module bar2(); wire x; endmodule\n", "mods": [{"name": "bar2", "regs": 3}]}
        self.assertIn(self.run_size("list", lst, out=self.out("B")).returncode, (0, 3))
        o = self.out("cmp")
        c = self.compare(self.out("A"), self.out("B"), o)
        self.assertEqual(c.returncode, 0, c.stdout + c.stderr)
        self.assertIn("SV identical => size identical (same backend)", c.stdout)
        rows = {r["row"]: r for r in csv.DictReader(open(os.path.join(o, "compare.tsv")), delimiter="\t")}
        self.assertEqual((rows["1"]["sv_identical"], rows["1"]["class"]), ("yes", "identical"))
        self.assertEqual((rows["1"]["ir_regs_A"], rows["1"]["ir_regs_B"], rows["1"]["ir_regs_delta"]), ("1", "1", "0"))
        self.assertEqual((rows["2"]["sv_identical"], rows["2"]["class"]), ("no", "different"))
        self.assertEqual((rows["2"]["ir_regs_A"], rows["2"]["ir_regs_B"], rows["2"]["ir_regs_delta"]), ("2", "3", "1"))
        n0, n1 = len("module bar2(); endmodule\n"), len("module bar2(); wire x; endmodule\n")
        self.assertEqual((rows["2"]["g_cells_A"], rows["2"]["g_cells_B"], rows["2"]["g_cells_delta"]),
                         (str(n0 + 10), str(n1 + 10), str(n1 - n0)))
        txt = open(os.path.join(o, "compare.txt")).read()
        self.assertIn("row classes: identical=1 different=1 not-comparable=0 incomplete=0", txt)
        self.assertIn("RESULT: every row comparable (exit 0)", txt)

    def test_unmeasured_rows_are_never_a_pass(self):
        lst = os.path.join(self.base, "rows.txt")
        open(lst, "w").write("1\n4\n")        # row 4 is unsupported on both sides
        self.assertIn(self.run_size("list", lst, out=self.out("A")).returncode, (0, 3))
        self.assertIn(self.run_size("list", lst, out=self.out("B")).returncode, (0, 3))
        c = self.compare(self.out("A"), self.out("B"), self.out("cmp"))
        self.assertEqual(c.returncode, 2, c.stdout)
        self.assertIn("incomplete=1", c.stdout)
        self.assertIn("unsupported/not-run on both sides: 1", c.stdout)
        self.assertIn("NOT A PASS", c.stdout)

    # compare: records built directly --------------------------------------------------------
    BASE = {"row": "1", "file": "f", "command": "#synthesizeVerilog", "top": "t", "sv_top": "t", "size_status": "ok",
            "sv_identity": "abc", "sv_sha256": "abc", "ir_regs": "1", "ir_stmts": "5", "opt_regs": "1", "opt_stmts": "4",
            "ir_modules": "1", "ir_mems": "0", "ir_insts": "0", "ir_wires": "2", "ir_regbits": "8", "ir_membits": "0",
            "opt_mems": "0", "opt_insts": "0", "opt_wires": "2", "opt_regbits": "8",
            "g_status": "ok", "f_status": "ok", "g_cells": "10", "g_dff": "2", "f_cells": "9", "f_lut": "4", "f_ff": "2",
            "f_bram": "0", "ys_version": "Yosys 0.70", "ys_cmd": "y", "ys_timeout_s": "5", "ys_files": "size_sv.sv",
            "g_script": "g", "f_script": "f", "src_sha": "1" * 12, "sv_origin_check": "same"}

    def rec(self, **kw):
        return dict(self.BASE, **kw)

    def cls(self, a, b):
        rows, S = size_run.compare_rows(a, b)
        return rows, S

    def test_identical_sv_with_different_raw_ir_is_reported_not_derived(self):
        # P1-1 control: same SV, raw and optimised IR differ -> reported as different IR, not a violation
        a, b = self.rec(), self.rec(ir_stmts="9", ir_regs="3", opt_stmts="6")
        rows, S = self.cls([a], [b])
        r = rows[0]
        self.assertEqual(r["sv_identical"], "yes")
        self.assertEqual((r["class_ir"], r["class_opt"], r["class_g"], r["class_f"]), ("different", "different", "identical", "identical"))
        self.assertEqual((r["ir_stmts_delta"], r["opt_stmts_delta"], r["violation"]), ("4", "2", ""))
        self.assertEqual((S["ir_differs_same_sv"], S["opt_differs_same_sv"], S["violations"]), (1, 1, 0))
        # and different IR with different SV is reported the same way
        rows, _ = self.cls([a], [dict(b, sv_identity="zzz")])
        self.assertEqual(rows[0]["class_ir"], "different")

    def test_identical_sv_same_backend_other_yosys_numbers_is_a_violation(self):
        rows, S = self.cls([self.rec()], [self.rec(g_cells="11", src_sha="2" * 12)])
        self.assertEqual((rows[0]["violation"], S["violations"], rows[0]["class_g"]), ("g_cells", 1, "different"))

    def test_sv_differs_yosys_delta_is_filled_when_comparable(self):
        rows, S = self.cls([self.rec()], [self.rec(sv_identity="x", g_cells="12")])
        self.assertEqual((rows[0]["g_cells_delta"], rows[0]["violation"], S["violations"]), ("2", "", 0))

    def test_both_yosys_numbers_blank_is_incomplete_not_equal(self):
        blank = dict(g_cells="", g_dff="", g_status="timeout")
        rows, S = self.cls([self.rec(**blank)], [self.rec(**blank)])   # both sides timed out
        self.assertEqual((rows[0]["class_g"], rows[0]["class"], rows[0]["g_cells_delta"]), ("incomplete", "incomplete", ""))
        self.assertEqual(rows[0]["class_f"], "identical")
        self.assertEqual(S["row_class"]["incomplete"], 1)

    def test_one_side_failed_is_incomplete(self):
        rows, _ = self.cls([self.rec()], [self.rec(size_status="synthesis-error", sv_identity="", g_cells="")])
        self.assertEqual((rows[0]["sv_identical"], rows[0]["class"]), ("n/a", "incomplete"))
        rows, _ = self.cls([self.rec()], [self.rec(f_status="error", f_cells="", f_lut="", f_ff="", f_bram="")])
        self.assertEqual((rows[0]["class_f"], rows[0]["class_g"]), ("incomplete", "identical"))
        rows, _ = self.cls([self.rec()], [])
        self.assertEqual(rows[0]["class"], "incomplete")

    def test_version_missing_is_not_comparable(self):
        rows, S = self.cls([self.rec(ys_version="")], [self.rec(ys_version="")])
        self.assertEqual((rows[0]["class_g"], rows[0]["class_f"], rows[0]["class"]), ("not-comparable",) * 3)
        self.assertEqual(rows[0]["g_cells_delta"], "")
        self.assertFalse(size_run.backend_check([self.rec(ys_version="")], [self.rec(ys_version="")])[0])
        # IR is still compared (independent of the backend)
        self.assertEqual(rows[0]["class_ir"], "identical")

    def test_versions_swapped_between_rows_is_not_comparable(self):
        a = [self.rec(row="1", ys_version="Yosys 0.70"), self.rec(row="2", ys_version="Yosys 0.71")]
        b = [self.rec(row="1", ys_version="Yosys 0.71"), self.rec(row="2", ys_version="Yosys 0.70")]
        rows, S = self.cls(a, b)
        self.assertEqual([r["class"] for r in rows], ["not-comparable"] * 2)
        same, notes = size_run.backend_check(a, b)
        self.assertFalse(same)
        self.assertIn("rows 1,2", notes[0])

    def test_different_backend_is_not_comparable_and_no_delta(self):
        for kw in (dict(ys_version="Yosys 0.71"), dict(ys_cmd="other"), dict(g_script="g2", f_script="f2"), dict(sv_top="u")):
            rows, _ = self.cls([self.rec()], [self.rec(sv_identity="x", g_cells="12", f_lut="9", **kw)])
            self.assertEqual(rows[0]["class_g"], "not-comparable", kw)
            self.assertEqual((rows[0]["g_cells_delta"], rows[0]["f_lut_delta"]), ("", ""), kw)

    def test_duplicate_row_in_one_input_is_not_comparable(self):
        rows, S = self.cls([self.rec(), self.rec()], [self.rec()])
        self.assertEqual((len(rows), rows[0]["class"], S["duplicate_rows"]), (1, "not-comparable", 1))

    def run_compare_dirs(self, ra, rb):
        dirs = []
        for n, rs in (("cA", ra), ("cB", rb)):
            d = self.out(n)
            shutil.rmtree(d, ignore_errors=True)
            os.makedirs(d)
            with open(os.path.join(d, "results.tsv"), "w") as f:
                w = csv.DictWriter(f, fieldnames=sorted({k for r in rs for k in r}), delimiter="\t")
                w.writeheader()
                w.writerows(rs)
            dirs.append(d)
        return self.compare(dirs[0], dirs[1], self.out("cmpd"))

    def test_exit_status_distinguishes_violation_not_comparable_and_pass(self):
        c = self.run_compare_dirs([self.rec()], [self.rec()])
        self.assertEqual(c.returncode, 0, c.stdout)
        c = self.run_compare_dirs([self.rec()], [self.rec(g_cells="11")])
        self.assertEqual(c.returncode, 1)
        c = self.run_compare_dirs([self.rec(ys_version="")], [self.rec(ys_version="")])
        self.assertEqual(c.returncode, 2)
        self.assertIn("violations=0 not-comparable=1", c.stdout)     # violations 0 alone is not a pass
        c = self.run_compare_dirs([self.rec(g_cells="", g_status="timeout")], [self.rec(g_cells="", g_status="timeout")])
        self.assertEqual(c.returncode, 2)

    # -------------------------------------------------- P2-1: success vs observed artifacts
    def test_files_then_exit_1_is_observed_not_ok(self):
        self.plan["1"] = {"exit_after": 1}
        r = self.one(1)
        self.assertEqual(r["size_status"], "failed-observed")
        self.assertEqual(r["size_observed"], "yes")
        self.assertIn("rc=1", r["size_error"])
        self.assertNotEqual(r["sv_sha256"], "")             # kept as an observation
        self.assertEqual(r["g_status"], "ok")
        rows, _ = size_run.compare_rows([r], [r])
        self.assertEqual(rows[0]["class"], "incomplete")    # never a formal measurement

    def test_files_then_signal_is_observed_not_ok(self):
        self.plan["1"] = {"signal_after": True}
        r = self.one(1)
        self.assertEqual((r["size_status"], r["size_observed"]), ("failed-observed", "yes"))
        self.assertIn("signal", r["size_error"])

    def test_join_check_no_is_not_ok(self):
        self.plan["1"] = {"join_bad": True}
        r = self.one(1)
        self.assertEqual((r["sv_join_check"], r["size_status"], r["size_observed"]), ("no", "failed-observed", "yes"))
        self.assertIn("sv_join_check=no", r["size_error"])

    def test_success_has_no_observed_flag(self):
        r = self.one(1)
        self.assertEqual((r["size_status"], r["size_observed"], r["sv_join_check"]), ("ok", "", "yes"))

    # ------------------------------------------------------------ P1-3: origin of the SV
    def test_origin_same_when_the_command_printed_the_same_sv(self):
        r = self.one(1)
        self.assertEqual(r["sv_origin_check"], "same")

    def test_origin_differ_when_the_command_printed_something_else(self):
        self.plan["1"] = {"orig_sv": "module something_else(); endmodule\n"}
        r = self.one(1)
        self.assertEqual(r["sv_origin_check"], "differ")
        self.assertEqual(r["size_status"], "ok")            # recorded, not hidden
        rows, S = size_run.compare_rows([r], [r])
        self.assertEqual(S["origin_differ"], 2)
        # P1-3a: never a formal comparison, never exit 0
        self.assertEqual((rows[0]["class"], rows[0]["sv_identical"]), ("not-comparable", "n/a"))
        self.assertEqual(rows[0]["obs_class"], "identical")          # only an observation
        c = self.run_compare_dirs([r], [r])
        self.assertEqual(c.returncode, 2, c.stdout)

    def test_origin_not_checked_when_nothing_was_captured(self):
        self.plan["1"] = {"orig_skip": True}
        r = self.one(1)
        self.assertEqual(r["sv_origin_check"], "not-checked")
        self.assertIn("not found", r["sv_origin_reason"])
        c = self.run_compare_dirs([r], [r])
        self.assertEqual(c.returncode, 2, c.stdout)

    def test_origin_of_a_write_command_reads_the_capture_of_this_attempt(self):
        r = self.one(13)
        self.assertEqual(r["sv_origin_check"], "same")
        self.plan["13"] = {"mods": [{"name": "wd13"}, {"name": "sub13"}], "orig_sv": "module stale(); endmodule\n"}
        r = self.one(13)      # the re-synthesis differs from the file the original wrote
        self.assertEqual(r["sv_origin_check"], "differ")
        self.plan["13"] = {"orig_skip": True}
        self.assertEqual(self.one(13)["sv_origin_check"], "not-checked")

    # P1-3a: the origin condition in the comparison
    def test_compare_requires_origin_same_on_both_sides(self):
        for kw in (dict(sv_origin_check="differ"), dict(sv_origin_check="not-checked"), dict(sv_origin_check="")):
            for side in (0, 1):
                recs = [self.rec(), self.rec()]
                recs[side] = self.rec(**kw)
                rows, S = self.cls([recs[0]], [recs[1]])
                want = "incomplete" if kw["sv_origin_check"] == "" else "not-comparable"
                self.assertEqual(rows[0]["class"], want, (kw, side))
                self.assertTrue(all(rows[0]["class_" + sec] == want for sec in ("ir", "opt", "g", "f")), (kw, side))
                self.assertEqual((rows[0]["sv_identical"], rows[0]["ir_regs_delta"], rows[0]["violation"]), ("n/a", "", ""))
                self.assertEqual(rows[0]["obs_class"], "identical")     # the observation stays, separately
                self.assertEqual(rows[0]["obs_sv_identical"], "yes")
                c = self.run_compare_dirs([recs[0]], [recs[1]])
                self.assertEqual(c.returncode, 2, (kw, side, c.stdout))
                self.assertIn("OBSERVATION", c.stdout)

    def test_origin_not_same_cannot_hide_a_difference_or_make_a_pass(self):
        # even identical numbers: not a pass; different numbers: not a violation either (observation only)
        a, b = self.rec(sv_origin_check="differ"), self.rec(g_cells="99")
        rows, S = self.cls([a], [b])
        self.assertEqual((rows[0]["class"], rows[0]["violation"], S["violations"]), ("not-comparable", "", 0))
        self.assertEqual(rows[0]["obs_class_g"], "different")
        self.assertEqual(self.run_compare_dirs([a], [b]).returncode, 2)

    def test_origin_same_on_both_sides_is_the_formal_comparison(self):
        rows, _ = self.cls([self.rec()], [self.rec(g_cells="12", sv_identity="x")])
        self.assertEqual((rows[0]["class"], rows[0]["sv_identical"], rows[0]["g_cells_delta"]), ("different", "no", "2"))

    # P1-3b: full-text origin identity, stdout rows
    def test_capture_wraps_the_original_command_with_attempt_markers(self):
        self.one(1)
        d = os.path.join(self.out(), "cases", "R001_size", "attempt-001")
        text = open(os.path.join(d, "Case.lean")).read()
        i, j = text.index("VED SIZE CAP BEGIN"), text.index("#synthesizeVerilog foo1\n")
        k, m = text.index("VED SIZE CAP END"), text.index("-- ===== VED SIZE BEGIN")
        self.assertTrue(i < j < k < m)                       # before the command / after it / before the size block
        tok = open(os.path.join(d, "size_token.txt")).read()
        out = open(os.path.join(d, "stdout.txt")).read()
        self.assertEqual((out.count(f"VED SIZE CAP BEGIN {tok}"), out.count(f"VED SIZE CAP END {tok}")), (1, 1))

    def test_origin_top_module_missing_from_the_resynthesis_is_differ(self):
        # the command printed module A + module B (hierarchy), the re-synthesis is module B only
        a, b = "module A(); endmodule\n", "module B(); endmodule\n"
        self.plan["1"] = {"sv": b, "orig_sv": a + b}
        r = self.one(1)
        self.assertEqual(r["sv_origin_check"], "differ")

    def test_origin_previous_command_with_the_same_tail_does_not_count(self):
        prev = "module foo1(); endmodule\n\n\n-- Verilog successfully generated!"
        self.plan["1"] = {"prev_out": prev, "orig_skip": True}      # the command itself emitted nothing
        r = self.one(1)
        self.assertEqual(r["sv_origin_check"], "not-checked")
        self.assertIn("not found", r["sv_origin_reason"])

    def test_origin_marker_missing_or_text_around_the_sv_is_not_same(self):
        self.plan["1"] = {"no_end_marker": True}
        r = self.one(1)
        self.assertEqual(r["sv_origin_check"], "not-checked")
        self.assertIn("markers", r["sv_origin_reason"])
        self.plan["1"] = {"orig_sv": "extra\nmodule foo1(); endmodule\n"}      # something printed before the SV
        self.assertEqual(self.one(1)["sv_origin_check"], "differ")

    def test_origin_check_direct_rules(self):
        d = os.path.join(self.base, "direct")
        os.makedirs(d)
        open(os.path.join(d, "size_token.txt"), "w").write("T1")
        meta = {"command": "#synthesizeVerilog"}
        sv = "module m(); endmodule\n"
        good = f"x\nVED SIZE CAP BEGIN T1\n{sv}\n\n-- Verilog successfully generated!\nVED SIZE CAP END T1\n"
        self.assertEqual(size_gen.origin_check(meta, good, sv, d)[0], "same")
        # a stale marker of ANOTHER attempt does not count
        self.assertEqual(size_gen.origin_check(meta, good.replace("T1", "T0"), sv, d)[0], "not-checked")
        # messages the command logged after its tail line are not SV
        warn = good.replace("\nVED SIZE CAP END", "\nf.lean:3:0: warning: w\nVED SIZE CAP END")
        self.assertEqual(size_gen.origin_check(meta, warn, sv, d)[0], "same")
        # SV with a prefix / suffix / other text is not the same
        self.assertEqual(size_gen.origin_check(meta, good, "module n();\n" + sv, d)[0], "differ")
        self.assertEqual(size_gen.origin_check(meta, good, sv[:-1], d)[0], "differ")
        self.assertEqual(size_gen.origin_check(meta, None, sv, d)[0], "not-checked")

    # P1-3b: write rows
    def test_write_row_captures_this_attempts_write(self):
        r = self.one(13)
        self.assertEqual(r["sv_origin_check"], "same")
        d = os.path.join(self.out(), "cases", "R013_size", "attempt-001")
        text = open(os.path.join(d, "Case.lean")).read()
        self.assertLess(text.index("size_wpre.txt"), text.index("#writeDesign wd13"))
        self.assertLess(text.index("#writeDesign wd13"), text.index("size_wpost.txt"))
        self.assertLess(text.index("size_wpost.txt"), text.index("-- ===== VED SIZE BEGIN"))

    def test_write_path_is_read_from_continuation_lines_when_args_column_is_empty(self):
        r = {"command": "#writeDesign", "args": ""}
        code = '#writeDesign top\n  ".lake/build/gen/a b.sv"\n  "x.h"'
        self.assertEqual(size_gen.origin_arg(r, code), ".lake/build/gen/a b.sv")
        pre, post = size_gen.capture_blocks(dict(r, args=""), code)
        self.assertIn('let p : System.FilePath := ".lake/build/gen/a b.sv"', pre)
        self.assertIn('".lake/build/gen/a b.sv"', post)
        self.assertEqual(size_gen.capture_blocks(r, "#writeDesign top"), ("", ""))     # no path: nothing to capture

    def test_write_row_only_a_preexisting_file_is_not_checked(self):
        # the file is there from before (even equal to the SV), this attempt's command writes nothing
        self.plan["13"] = {"preexisting": "module wd13(); endmodule\nmodule sub13(); endmodule\n", "no_write": True}
        r = self.one(13)
        self.assertEqual(r["sv_origin_check"], "not-checked")
        self.assertIn("did not write", r["sv_origin_reason"])
        self.assertIn("before", r["sv_origin_reason"])
        # the pre-existing file is back in place afterwards
        self.assertTrue(os.path.exists(os.path.join(self.fx.repo, "out.sv")))

    def test_write_row_preexisting_file_is_replaced_by_this_attempts_write(self):
        self.plan["13"] = {"mods": [{"name": "wd13"}, {"name": "sub13"}], "preexisting": "module stale(); endmodule\n"}
        r = self.one(13)
        self.assertEqual(r["sv_origin_check"], "same")        # the file of THIS write, not the stale one
        self.plan["13"] = {"preexisting": "module wd13(); endmodule\nmodule sub13(); endmodule\n", "orig_sv": "module other(); endmodule\n"}
        self.assertEqual(self.one(13)["sv_origin_check"], "differ")

    def test_write_row_later_overwrite_does_not_change_the_capture(self):
        self.plan["13"] = {"later_write": "module later(); endmodule\n"}
        self.assertEqual(self.one(13)["sv_origin_check"], "same")
        self.plan["13"] = {"orig_sv": "module other(); endmodule\n", "later_write": "module wd13(); endmodule\nmodule sub13(); endmodule\n"}
        self.assertEqual(self.one(13)["sv_origin_check"], "differ")      # a later file equal to the SV does not help

    def test_no_exactly_what_the_command_prints_claim(self):
        for f in ("size_gen.py", "size_run.py"):
            self.assertNotIn("exactly the text", open(os.path.join(VED, f)).read())

    # ---------------------------------------------------------------- entry guard
    def test_entry_guard_refuses_a_changed_entry_function(self):
        self.write_elab(ELAB.replace("synthesizeCombinational declName", "synthesizeCombinationalV2 declName", 1)
                        .replace("(module, _) ← synthesizeCombinationalV2", "(module, _) ← synthesizeNew"))
        r = self.one(1)
        self.assertEqual((r["invocation"], r["size_status"]), ("entry-mismatch", "not-run"))
        self.assertIn("synthesizeCombinational", r["invocation_detail"])
        self.assertFalse(os.path.exists(self.log) and '"row": "1"' in open(self.log).read())   # Lean never ran
        self.write_elab(ELAB.replace("toVerilogDesign design))", "toVerilogDesign2 design))", 1).replace(
            "synthesizeHierarchical declName\n  IO.println", "synthesizeNew declName\n  IO.println"))
        self.assertEqual(self.one(13, out=self.out("o2"))["size_status"], "ok")       # writeDesign unaffected
        self.write_elab(ELAB.replace("  let design ← synthesizeHierarchical declName\n  let verilog", "  let design ← synthesizeNew declName\n  let verilog"))
        self.assertEqual(self.one(13, out=self.out("o3"))["invocation"], "entry-mismatch")   # core changed

    def test_entry_guard_missing_file_or_command_fails_closed(self):
        os.remove(os.path.join(self.fx.repo, "Sparkle/Compiler/Elab.lean"))
        self.assertEqual(self.one(1)["invocation"], "entry-mismatch")

    # P2-2: identifier boundaries, no comments, no strings
    def entry(self, text, cmd="#synthesizeVerilog"):
        self.write_elab(text)
        return size_gen.entry_check(self.fx.repo, cmd)

    def test_entry_guard_rejects_a_v2_only_change(self):
        self.assertEqual(self.entry(ELAB), "")
        why = self.entry(ELAB.replace("synthesizeCombinational declName", "synthesizeCombinationalV2 declName", 1))
        self.assertIn("synthesizeCombinational", why)
        self.assertIn("synthesizeCombinational", self.entry(ELAB.replace("synthesizeCombinational declName", "synthesizeCombinational' declName", 1)))
        self.assertIn("synthesizeCombinational", self.entry(ELAB.replace("synthesizeCombinational declName", "pre_synthesizeCombinational declName", 1)))
        self.assertIn("toVerilog", self.entry(ELAB.replace("toVerilog optimized", "toVerilogDesign optimized", 1)))   # toVerilog vs toVerilogDesign

    def test_entry_guard_old_name_only_in_a_comment_is_rejected(self):
        new = ELAB.replace("synthesizeCombinational declName", "synthesizeNew declName  -- was synthesizeCombinational declName", 1)
        self.assertIn("synthesizeCombinational", self.entry(new))
        new = ELAB.replace("  let (module, _) ← synthesizeCombinational declName\n",
                           "  let (module, _) ← synthesizeNew declName\n  /- synthesizeCombinational\n     /- nested synthesizeCombinational -/\n  still comment synthesizeCombinational -/\n", 1)
        self.assertIn("synthesizeCombinational", self.entry(new))
        new = ELAB.replace("  let (module, _) ← synthesizeCombinational declName\n",
                           "  let (module, _) ← synthesizeNew declName\n  /-- doc synthesizeCombinational -/\n", 1)
        self.assertIn("synthesizeCombinational", self.entry(new))

    def test_entry_guard_old_name_only_in_a_string_is_rejected(self):
        new = ELAB.replace("  let (module, _) ← synthesizeCombinational declName\n",
                           '  let (module, _) ← synthesizeNew declName\n  IO.println "synthesizeCombinational"\n', 1)
        self.assertIn("synthesizeCombinational", self.entry(new))
        new = ELAB.replace("  let (module, _) ← synthesizeCombinational declName\n",
                           '  let (module, _) ← synthesizeNew declName\n  IO.println "a \\" -- synthesizeCombinational"\n', 1)
        self.assertIn("synthesizeCombinational", self.entry(new))

    def test_entry_guard_missing_name_is_rejected(self):
        self.assertIn("synthesizeCombinational", self.entry(ELAB.replace("  let (module, _) ← synthesizeCombinational declName\n", "", 1)))

    def test_entry_guard_accepts_qualified_names_and_ignores_comment_markers_in_strings(self):
        new = ELAB.replace("synthesizeCombinational declName", "Sparkle.Compiler.Elab.synthesizeCombinational declName", 1)
        self.assertEqual(self.entry(new), "")
        # `--` inside a string is not a comment: the call after it on the same line counts
        new = ELAB.replace("  let (module, _) ← synthesizeCombinational declName\n",
                           '  IO.println "-- x"; let (module, _) ← synthesizeCombinational declName\n', 1)
        self.assertEqual(self.entry(new), "")
        # a char literal quote does not open a string
        new = ELAB.replace("  IO.println verilog\n", "  let q := '\"'\n  IO.println verilog\n", 1)
        self.assertEqual(self.entry(new), "")

    def test_entry_guard_forbidden_name_in_a_comment_is_fine_in_code_is_not(self):
        self.assertEqual(self.entry(ELAB.replace("  IO.println verilog\n", "  -- synthesizeHierarchical\n  IO.println verilog\n", 1)), "")
        self.assertIn("synthesizeHierarchical", self.entry(ELAB.replace("  IO.println verilog\n", "  let _ ← synthesizeHierarchical declName\n  IO.println verilog\n", 1)))

    def test_entry_guard_writedesign_core_checked_without_comments(self):
        new = ELAB.replace("  let design ← synthesizeHierarchical declName\n  let verilog",
                           "  let design ← synthesizeNew declName -- synthesizeHierarchical\n  let verilog", 1)
        self.assertIn("synthesizeHierarchical", self.entry(new, "#writeDesign"))

    def test_entry_guard_accepts_the_real_elaborator(self):
        root = os.path.dirname(os.path.dirname(VED))
        if not os.path.exists(os.path.join(root, size_gen.ENTRY_FILE)):
            self.skipTest("no Elab.lean next to the harness")
        for cmd in size_gen.ENTRY_REQUIRED:
            self.assertEqual(size_gen.entry_check(root, cmd), "", cmd)



class CommandWarningOriginTest(unittest.TestCase):
    """The original command's own one-line warnings printed before its SV (Lean prints messages first) do
    not make the origin check `differ`; any other leading text still does."""

    SV = "// Generated by Sparkle HDL\nmodule t (); endmodule\n"

    def check(self, lead):
        d = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, d)
        case = os.path.join(d, "Case.lean")
        open(case, "w").write("import X\n-- ===== VED SIZE CAPTURE PRE END =====\n#synthesizeVerilog t\n")
        open(os.path.join(d, "size_token.txt"), "w").write("tok1")
        out = ("VED SIZE CAP BEGIN tok1\n" + lead.replace("CASE", case) + self.SV
               + "\n\n-- Verilog successfully generated!\n" + "VED SIZE CAP END tok1\n")
        return size_gen.origin_check({"command": "#synthesizeVerilog"}, out, self.SV, d)

    def test_no_warning_is_same(self):
        self.assertEqual(self.check("")[0], "same")

    def test_warning_of_the_command_is_removed(self):
        st, why = self.check("CASE:3:0: warning: [DRC] Module 't': output 'out' is not driven by a register\n")
        self.assertEqual(st, "same")
        self.assertIn("1 leading one-line warning", why)

    def test_warning_at_another_line_is_differ(self):
        self.assertEqual(self.check("CASE:4:0: warning: [DRC] x\n")[0], "differ")

    def test_error_of_the_command_is_differ(self):
        self.assertEqual(self.check("CASE:3:0: error: boom\n")[0], "differ")

    def test_warning_after_other_text_is_differ(self):
        self.assertEqual(self.check("junk\nCASE:3:0: warning: [DRC] x\n")[0], "differ")

if __name__ == "__main__":
    unittest.main()
