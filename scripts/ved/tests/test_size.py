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

    def tearDown(self):
        shutil.rmtree(self.base, ignore_errors=True)

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
        open(lst, "w").write("1\n2\n4\n")
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
        self.assertEqual(rows["1"]["sv_identical"], "yes")
        self.assertEqual((rows["1"]["ir_regs_A"], rows["1"]["ir_regs_B"], rows["1"]["ir_regs_delta"]), ("1", "1", ""))
        self.assertEqual(rows["1"]["g_cells_delta"], "")      # identical SV: no delta column filled
        self.assertEqual(rows["2"]["sv_identical"], "no")
        self.assertEqual((rows["2"]["ir_regs_A"], rows["2"]["ir_regs_B"], rows["2"]["ir_regs_delta"]), ("2", "3", "1"))
        n0, n1 = len("module bar2(); endmodule\n"), len("module bar2(); wire x; endmodule\n")
        self.assertEqual((rows["2"]["g_cells_A"], rows["2"]["g_cells_B"], rows["2"]["g_cells_delta"]),
                         (str(n0 + 10), str(n1 + 10), str(n1 - n0)))
        self.assertEqual(rows["4"]["sv_identical"], "n/a")
        txt = open(os.path.join(o, "compare.txt")).read()
        self.assertIn("same backend (yosys version, flow scripts, yosys command and timeout equal on both sides): yes", txt)
        self.assertIn("sv_identical=1 sv_differs=1 not_comparable(no usable record on a side)=1", txt)
        self.assertIn("VIOLATIONS of the statement (identical SV, differing numbers): 0", txt)

    def test_compare_flags_identical_sv_with_different_numbers(self):
        base = {"row": "1", "file": "f", "command": "#synthesizeVerilog", "top": "t", "size_status": "ok",
                "sv_identity": "abc", "sv_sha256": "abc", "ir_regs": "1", "g_cells": "10", "f_lut": "4",
                "ys_version": "Y", "ys_cmd": "y", "ys_timeout_s": "5", "ys_files": "size_sv.sv",
                "g_script": "g", "f_script": "f", "src_sha": "1" * 12}
        a, b = dict(base), dict(base, g_cells="11", src_sha="2" * 12)
        rows, S = size_run.compare_rows([a], [b])
        self.assertEqual((rows[0]["sv_identical"], rows[0]["violation"], S["violations"]), ("yes", "g_cells", 1))
        self.assertEqual(rows[0]["g_cells_delta"], "")
        # a different backend is reported, not hidden
        same, notes = size_run.backend_check([a], [dict(b, ys_version="Z")])
        self.assertFalse(same)
        self.assertIn("ys_version", notes[0])
        # a blank (yosys timeout) next to a number on identical SV is not a violation but is counted
        rows, S = size_run.compare_rows([a], [dict(base, g_cells="")])
        self.assertEqual((rows[0]["violation"], S["violations"], S["numbers_missing_identical"]), ("", 0, 1))
        # a side without a usable record is not comparable
        rows, S = size_run.compare_rows([a], [dict(base, size_status="synthesis-error", sv_identity="")])
        self.assertEqual((rows[0]["sv_identical"], S["not_comparable"]), ("n/a", 1))


if __name__ == "__main__":
    unittest.main()
