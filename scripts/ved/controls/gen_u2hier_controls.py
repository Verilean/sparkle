#!/usr/bin/env python3
"""Write the u2_hier probe controls (MEASUREMENT ONLY): fills U2HierControls.lean.in with the harness's
own probe text (u1_gen.EVAL_HELP, u1_gen.PROBE_HIER_U2) so the probe that is tested is the probe the
harness runs.  Usage: gen_u2hier_controls.py OUT.lean"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import u1_gen  # noqa: E402

HDR = "open Lean Elab Command Meta Sparkle.IR.AST in\nrun_cmd do\n  try\n"
TOP = 'let n ← liftCoreM <| realizeGlobalConstNoOverload (mkIdent "@TOP@".toName)'


def probe_elab():
    """PROBE_HIER_U2 as a command `#vedu2h_probe <ident>` (same body, the ident instead of @TOP@)."""
    p = u1_gen.PROBE_HIER_U2
    assert p.startswith(HDR) and TOP in p
    body = p[len(HDR):].replace(TOP, "let n ← liftCoreM <| realizeGlobalConstNoOverload id")
    return ('open Lean Elab Command Meta Sparkle.IR.AST in\nelab "#vedu2h_probe " id:ident : command => do\n  try\n'
            + body)


def render():
    tpl = open(os.path.join(HERE, "U2HierControls.lean.in")).read()
    return tpl.replace("@EVAL_HELP@", u1_gen.EVAL_HELP).replace("@PROBE@", probe_elab())


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    open(sys.argv[1], "w").write(render())
