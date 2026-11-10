#!/usr/bin/env python3
"""FAKE stand-in for `kjob lake env lean <Case.lean>` in the size harness tests.  Never runs
Lean.  Looks the row up in the JSON plan $FAKE_PLAN (key "ROW") and writes the files the real
size block writes next to the case (size_sv.sv, size_children.sv, size_mod_<i>.sv, size_ir.txt
or size_err.txt).  Plan fields (all optional): sv (text of the single module, default
"module <top>(); endmodule\\n"), mods [{name, regs, mems, insts, stmts, wires, regbits, membits}]
(design kind: several modules joined by newline), kids ([names]), err, nofiles, sleep, exit.
"""
import json
import os
import re
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
    open(os.path.join(d, "size_sv.sv"), "w").write("\n".join(texts))
    if kids:
        open(os.path.join(d, "size_children.sv"), "w").write("\n".join(f"module {k}(); endmodule\n" for k in kids))
    open(os.path.join(d, "size_ir.txt"), "w").write("\n".join(lines) + "\nEND\n")
    print(f"VED SIZE OK kind={kind}")


if __name__ == "__main__":
    main()
