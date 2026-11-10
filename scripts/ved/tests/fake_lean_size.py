#!/usr/bin/env python3
"""FAKE stand-in for `kjob lake env lean <Case.lean>` in the size harness tests.  Never runs
Lean.  Looks the row up in the JSON plan $FAKE_PLAN (key "ROW") and writes the files the real
size block writes next to the case (size_sv.sv, size_children.sv, size_mod_<i>.sv, size_ir.txt
or size_err.txt).  Plan fields (all optional): sv (text of the single module, default
"module <top>(); endmodule\\n"), mods [{name, regs, mems, insts, stmts, wires, regbits, membits}]
(design kind: several modules joined by newline), kids ([names]), err, nofiles, sleep, exit.
Emulates the capture blocks the generator wraps around the original command (only when the case text has them):
token -> size_token.txt, `VED SIZE CAP BEGIN/END <token>` on stdout (stdout commands); the path argument moved
aside, the write, the copy to size_orig_write.bin and size_wpre/size_wpost.txt (write commands; the path is
relative to the working directory, as for the real lean).  More plan fields: prev_out (text printed BEFORE the
begin marker: a previous command), preexisting (content of the path before the command), no_write (the command
writes nothing), later_write (content written to the path by a LATER command, after the capture), no_end_marker.
The ORIGINAL command's output is faked first: it prints plan "orig_sv" (default: the same SV as the size
block writes; "" = prints nothing) plus the command's tail line on stdout, or, for #writeDesign /
#writeVerilogDesign, writes "orig_sv" to the path of its first string argument (relative to the case
directory); plan "orig_skip" = does not emit at all.  Then the block marker.  After the size files:
exit_after (exit code), signal_after (SIGKILL itself), join_bad (size_sv.sv no longer joins).
"""
import json
import os
import re
import signal
import sys
import time


def counts(m):
    d = dict(regs=0, mems=0, insts=0, stmts=0, wires=0, regbits=0, regbits_unknown=0, membits=0)
    d.update({k: v for k, v in m.items() if k != "name"})
    return d


def main():
    case = sys.argv[-1]
    d = os.path.dirname(case)
    text = open(case).read()
    m = re.search(r"VED SIZE BEGIN row (\d+)", text)
    row = m.group(1) if m else "?"
    plan = json.load(open(os.environ["FAKE_PLAN"])).get(row, {})
    with open(os.environ["FAKE_LOG"], "a") as f:
        f.write(json.dumps({"row": row}) + "\n")
    if plan.get("sleep"):
        time.sleep(plan["sleep"])
    if plan.get("exit"):
        sys.exit(plan["exit"])
    if plan.get("err"):
        open(os.path.join(d, "size_err.txt"), "w").write(plan["err"])
        print("VED SIZE ERROR " + plan["err"])
        return
    if plan.get("nofiles"):
        print(f"{case}:1:0: error: unknown identifier")
        sys.exit(1)
    kind = "design" if "synthesizeHierarchical" in text else "module"
    cms = list(re.finditer(r"^(#synthesizeVerilogDesign|#writeVerilogDesign|#writeDesign|#synthesizeVerilog)\s+\S+(?:\s+\"([^\"]*)\")?",
                           text.split("-- ===== VED SIZE BEGIN")[0], re.M))
    cmd, wpath = (cms[-1].group(1), cms[-1].group(2)) if cms else ("#synthesizeVerilog", None)   # the original command: the last one before the block
    top = re.search(r'mkIdent "([^"]+)"', text).group(1).split(".")[-1]
    mods = plan.get("mods") or [{"name": top}]
    texts = [plan.get("sv", f"module {mo['name']}(); endmodule\n") if i == 0 else f"module {mo['name']}(); endmodule\n"
             for i, mo in enumerate(mods)]
    if kind == "module":
        mods, texts = mods[:1], texts[:1]
    kids = plan.get("kids", [])
    lines = [f"kind={kind}", f"top={plan.get('top', mods[0]['name'])}",
             f"sv_top={plan.get('sv_top', plan.get('top', mods[0]['name']))}", "synth_ms=12", f"sv_modules={len(mods)}",
             f"children_modules={len(kids)}"]
    i = 0
    for mo, t in zip(mods, texts):
        c = counts(mo)
        for tag in ("raw", "opt"):
            lines.append(f"mod {tag} sv {i} {mo['name']} " + " ".join(f"{k}={v}" for k, v in c.items()))
        open(os.path.join(d, f"size_mod_{i}.sv"), "w").write(t)
        i += 1
    for k in kids:
        for tag in ("raw", "opt"):
            lines.append(f"mod {tag} child {i} {k} " + " ".join(f"{a}={b}" for a, b in counts({}).items()))
        i += 1
    sv_all = "\n".join(texts)
    cap = "VED SIZE CAPTURE PRE" in text
    tok = "t-%d-%d" % (os.getpid(), int(time.time() * 1e6) % 1000000007)
    if cap:
        open(os.path.join(d, "size_token.txt"), "w").write(tok)
    if plan.get("prev_out") and cmd != "#writeDesign":
        print(plan["prev_out"])
    wfile = None if wpath is None else (wpath if os.path.isabs(wpath) else os.path.join(os.getcwd(), wpath))
    had = False
    if cap and wfile:
        had = os.path.exists(wfile)
        if plan.get("preexisting") is not None:
            open(wfile, "w").write(plan["preexisting"])
            had = True
        if had:
            os.rename(wfile, wfile + ".size-bak-" + tok)
        open(os.path.join(d, "size_wpre.txt"), "w").write(f"{tok}\nhad={'true' if had else 'false'}\n")
    elif cap:
        print(f"VED SIZE CAP BEGIN {tok}")
    if not plan.get("orig_skip"):
        orig = plan.get("orig_sv", sv_all)
        if wpath is not None:
            if not plan.get("no_write"):
                open(wfile, "w").write(orig)
        elif orig is not None:
            tail = "-- Hierarchical Verilog successfully generated!" if cmd == "#synthesizeVerilogDesign" else "-- Verilog successfully generated!"
            if orig:
                print(orig)
            print("\n" + tail)
    if cap and wfile:
        if os.path.exists(wfile):
            open(os.path.join(d, "size_orig_write.bin"), "wb").write(open(wfile, "rb").read())
            if had:
                os.remove(wfile + ".size-bak-" + tok)
            st = "written"
        else:
            if had:
                os.rename(wfile + ".size-bak-" + tok, wfile)
            st = "absent"
        open(os.path.join(d, "size_wpost.txt"), "w").write(f"{tok}\n{st}\n")
    elif cap and not plan.get("no_end_marker"):
        print(f"VED SIZE CAP END {tok}")
    if wfile and plan.get("later_write") is not None:
        open(wfile, "w").write(plan["later_write"])
    print(f"VED SIZE MARK row {row}")
    open(os.path.join(d, "size_sv.sv"), "w").write(sv_all)
    if plan.get("join_bad"):
        open(os.path.join(d, "size_mod_0.sv"), "w").write("module other(); endmodule\n")
    if kids:
        open(os.path.join(d, "size_children.sv"), "w").write("\n".join(f"module {k}(); endmodule\n" for k in kids))
    open(os.path.join(d, "size_ir.txt"), "w").write("\n".join(lines) + "\nEND\n")
    print(f"VED SIZE OK kind={kind}")
    if plan.get("signal_after"):
        sys.stdout.flush()
        os.kill(os.getpid(), signal.SIGKILL)
    if plan.get("exit_after"):
        sys.exit(plan["exit_after"])


if __name__ == "__main__":
    main()
