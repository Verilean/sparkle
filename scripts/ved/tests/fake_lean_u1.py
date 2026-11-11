#!/usr/bin/env python3
"""FAKE stand-in for `kjob lake env lean <Case.lean>` in the U1 harness tests.
Never runs Lean.  Reads the U1 case file, looks the (row, route) up in the JSON
plan $FAKE_PLAN (key "ROW:ROUTE") and prints canned Lean-format messages
(`<file>:<line>:<col>: info|error: ...`) at the lines of the case's own
commands, so the classifier's segment logic is exercised.  It can also sleep,
allocate memory, exit with a code or kill itself with a signal.  Every call is
appended to $FAKE_LOG.

Plan fields (all optional): resolved, qualified, decl ("found"|"absent"), pre
{thm,mod,contract}, prep_error, u1 ("ok" | ["refused", stage, msg] | ["error", msg] | "none"),
ok_thm, ok_axioms, outside_error, probe {thm,type,mvars,levels,mod,contract,outs,axioms}, probe_fail,
ms {prep,u1,probe}, exit, sleep, self_signal, mem_mb, stderr.
Routes u1_hier / u2_hier: the OK line is `VED U1 HIER OK` / `VED U2 HIER OK`; `hier` {top, mods, insts, children, child_thms, design, ports}
overrides the canned hier probe lines (GOOD_HIER); `pre` may carry design / child.
Route u1_packed: the OK line is `VED U1 PACKED OK`, and probe also takes
{leaves ("8,4"), slices ("equal"|"differs"), port ("match"|"differs")}.
"""
import json
import os
import re
import subprocess
import sys
import time

GOOD = {"thm": "theorem", "type": "exact", "mvars": "type=false value=false fvars=false", "levels": "0",
        "mod": "closed=true type=true", "contract": "bound-to-mod", "outs": "1",
        "axioms": ["propext", "Classical.choice"]}


GOOD_HIER = {"design": "closed=true type=true", "top": "ok", "top_design": "Top", "top_mod": "Top",
             "mods": [2, "true", "true"], "insts": ["ok", 2, "[]"], "children": ["kidA", "kidB"],
             "child_thms": {}, "ports": "ok"}


def main():
    case = sys.argv[-1]
    text = open(case).read()
    lines = text.splitlines()
    m = re.search(r"VED U1 BEGIN row (\d+) route (\w+)", text)
    key = f"{m.group(1)}:{m.group(2)}" if m else "?"
    plan = json.load(open(os.environ["FAKE_PLAN"])).get(key, {})
    with open(os.environ["FAKE_LOG"], "a") as f:
        f.write(json.dumps({"key": key, "pid": os.getpid()}) + "\n")

    def at(prefix):
        return next((i + 1 for i, ln in enumerate(lines) if ln.startswith(prefix)), 1)

    def msg(sev, s, line):
        # as Lean's driver: info messages are printed bare, without a position
        if sev == "info":
            print(s, flush=True)
        else:
            print(f"{case}:{line}:0: {sev}: {s}", flush=True)
    top = re.search(r"\n#ved_u[12]\w* (\S+)", text)
    top = top.group(1) if top else "x"
    resolved = plan.get("resolved", f"Outer.{top}")
    qual = plan.get("qualified", resolved)
    pre = next(i + 1 for i, ln in enumerate(lines) if ln.startswith("run_cmd do"))
    msg("info", "VED U1P NS Outer.VedU1Case", pre)
    if plan.get("decl", "found") == "found":
        msg("info", f"VED U1P DECL resolved={resolved} user={resolved} inventory={qual} "
                    f"{'match' if qual == resolved else 'mismatch'}", pre)
        p = plan.get("pre", {})
        extra = ""
        if m and m.group(2) in ("u1_hier", "u2_hier"):
            extra = f" design={str(p.get('design', False)).lower()} child={str(p.get('child', False)).lower()}"
        msg("info", f"VED U1P PRE thm={str(p.get('thm', False)).lower()} mod={str(p.get('mod', False)).lower()} "
                    f"contract={str(p.get('contract', False)).lower()}{extra}", pre)
    else:
        msg("info", "VED U1P DECL absent: unknown constant", pre)
    if plan.get("outside_error"):
        msg("error", plan["outside_error"], 1)
    ms = plan.get("ms", {})
    clock = 1000
    deep = bool(m and m.group(2) in ("u1_deep", "u1_deep_ns"))
    nsr = bool(m and m.group(2) == "u1_deep_ns")
    packed = bool(m and m.group(2) == "u1_packed")

    wfail = nsr and plan.get("ns_wrapper_fail")

    def u1n(line):
        if wfail:
            # the wrapper itself fails: no command runs inside it
            msg("error", plan["ns_wrapper_fail"], line)
        elif nsr and "." not in resolved:
            msg("info", f"VED U1N scope=_root_ outer={resolved} inner={resolved} same mode=root", line)
        elif nsr:
            inner = plan.get("ns_inner", resolved)
            pfx = resolved.rsplit(".", 1)[0]
            msg("info", f"VED U1N scope={pfx} outer={resolved} inner={inner} "
                        f"{'same' if inner == resolved else 'differs'} mode=ns", line)
    if deep:
        l = at('#vedu1_t "p_begin"')
        msg("info", f"VED U1T p_begin {clock}", l)
        u1n(l)
        if plan.get("prep_error") and not wfail:
            msg("error", plan["prep_error"], at("#verify_elab_deep"))
        clock += ms.get("prep", 500)
        msg("info", f"VED U1T p_end {clock}", at('#vedu1_t "p_end"'))
    msg("info", f"VED U1T u_begin {clock}", at('#vedu1_t "u_begin"'))
    u1n(at('#vedu1_t "u_begin"'))
    u1 = plan.get("u1", "ok") if not wfail else "none"
    el = at("#ved_u")
    if u1 == "ok":
        axs = ", ".join(plan.get("ok_axioms", ["propext"]))
        spec = " (specialised at defaultDomain)" if plan.get("ok_specialised") else ""
        if m and m.group(2) in ("u1_hier", "u2_hier"):
            msg("info", f"VED U{'2' if m.group(2) == 'u2_hier' else '1'} HIER OK {plan.get('ok_thm', resolved + '.ved_u1')}{spec}: [{axs}]\n"
                        "children: [kidA, kidB]\nsynthesis 14 ms, children 9600 ms, parent proof 1200 ms, "
                        "peak 2590000 kB\n(Module body)", el)
        else:
            okp = "PACKED OK" if packed else "OK"
            msg("info", f"VED U1 {okp} {plan.get('ok_thm', resolved + '.ved_u1')}{spec}: [{axs}]\n(Module body)", el)
    elif isinstance(u1, list) and u1[0] == "refused":
        msg("error", f"VED U1 REFUSED {resolved} [{u1[1]}]: {u1[2]}", el)
    elif isinstance(u1, list) and u1[0] == "error":
        msg("error", u1[1], el)
    clock += ms.get("u1", 2000)
    msg("info", f"VED U1T u_end {clock}", at('#vedu1_t "u_end"'))
    pl = at('#vedu1_t "probe_end"') - 1
    if plan.get("probe_fail"):
        msg("info", f"VED U1P PROBE failed: {plan['probe_fail']}", pl)
    else:
        q = dict(GOOD, **plan.get("probe", {}))
        if plan.get("domains", 0) is not None:
            msg("info", f"VED U1P STMT domains={plan.get('domains', 0)}", pl)
        msg("info", f"VED U1P THM {q['thm']}", pl)
        if q["thm"] == "theorem":
            if m and m.group(2) == "u2_hier" and plan.get("expstmt", "U2HStmt registers=false") is not None:
                msg("info", f"VED U1P EXPSTMT {plan.get('expstmt', 'U2HStmt registers=false')}", pl)
            msg("info", f"VED U1P TYPE {q['type']}", pl)
            msg("info", f"VED U1P MVARS {q['mvars']}", pl)
            msg("info", f"VED U1P LEVELS {q['levels']}", pl)
            msg("info", f"VED U1P AXIOMS [{', '.join(q['axioms'])}]", pl)
        msg("info", f"VED U1P MOD {q['mod']}", pl)
        h = dict(GOOD_HIER, **plan.get("hier", {})) if m and m.group(2) in ("u1_hier", "u2_hier") else None
        if h and h["design"] is not None:
            msg("info", f"VED U1P DESIGN {h['design']}", pl)
        msg("info", f"VED U1P CONTRACT {q['contract']}", pl)
        if h and h["ports"] is not None:
            msg("info", f"VED U1P PORTS {h['ports']} inputs=2 outputs=1", pl)
        if packed:
            ws = [int(x) for x in q.get("leaves", "8,4").split(",")]
            tot = sum(ws)
            offs = [sum(ws[i + 1:]) for i in range(len(ws))]
            exp = "[" + ",".join(f"({o},{w})" for o, w in zip(offs, ws)) + "]"
            stored = exp if q.get("slices", "equal") == "equal" else "[" + ",".join(f"({w},{o})" for o, w in zip(offs, ws)) + "]"
            msg("info", f"VED U1P LEAVES {len(ws)} widths={ws} total={tot}", pl)
            msg("info", f"VED U1P SLICES expected={exp} stored={stored} {q.get('slices', 'equal')}", pl)
            msg("info", f"VED U1P PORT module=[(out, {tot})] expect=[(out, {tot})] {q.get('port', 'match')}", pl)
            q = dict(q, outs=q["outs"] if "outs" in plan.get("probe", {}) else str(len(ws)))
        msg("info", f"VED U1P OUTS {q['outs']}", pl)
        if h and h["top"] is not None:
            msg("info", f"VED U1P HIERTOP {h['top']} design={h['top_design']} mod={h['top_mod']}", pl)
            msg("info", "VED U1P HIERMODS n=%s nonempty=%s top-not-child=%s" % tuple(h["mods"]), pl)
            msg("info", f"VED U1P HIERINST {h['insts'][0]} n={h['insts'][1]} missing={h['insts'][2]}", pl)
            for c in h["children"]:
                msg("info", f"VED U1P HIERCHILD {c} thm={h['child_thms'].get(c, 'theorem')}", pl)
            allthm = all(h["child_thms"].get(c, "theorem") == "theorem" for c in h["children"])
            msg("info", f"VED U1P HIERCHILDREN [{', '.join(h['children'])}] all-theorems={str(allthm).lower()}", pl)
    clock += ms.get("probe", 100)
    msg("info", f"VED U1T probe_end {clock}", at('#vedu1_t "probe_end"'))
    if plan.get("stderr"):
        print(plan["stderr"], file=sys.stderr, flush=True)
    if plan.get("mem_mb"):
        subprocess.run([sys.executable, "-c",
                        f"b = bytearray({plan['mem_mb']} * 1024 * 1024)\n"
                        "for i in range(0, len(b), 4096): b[i] = 1\nimport time; time.sleep(0.3)"], check=True)
    if plan.get("sleep"):
        time.sleep(plan["sleep"])
    if plan.get("self_signal"):
        os.kill(os.getpid(), plan["self_signal"])
        time.sleep(5)
    sys.exit(plan.get("exit", 0))


if __name__ == "__main__":
    main()
