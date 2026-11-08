#!/usr/bin/env python3
"""FAKE stand-in for `kjob lake env lean <Case.lean>` in the U0 harness tests.

It never runs Lean.  It reads the case file, finds which inventory row (or
smoke variant) it is, looks the row up in the JSON plan named by $FAKE_PLAN,
and then behaves as told: prints canned `VED ...` lines in Lean's message
format (`<file>:<line>:<col>: info|error: ...`), prints the SPARKLE_*
variables it was given (env-dependent output), sleeps, spawns children (also
one that escapes the process group with setsid), allocates memory in a child,
exits with a chosen code or kills itself with a signal.  Every invocation is
appended to $FAKE_LOG.
"""
import json
import os
import re
import signal
import subprocess
import sys
import time


def main():
    case = sys.argv[-1]
    text = open(case).read()
    lines = text.splitlines()
    m = re.search(r"VED U0 BEGIN row (\d+)", text)
    if m:
        key = m.group(1)
    else:
        m = re.search(r"/S_\w+?_(\d+)/", case)
        key = f"smoke:{int(m.group(1))}" if m else "asis"
    plan = json.load(open(os.environ["FAKE_PLAN"])).get(key, {})
    sparkle = sorted(f"{k}={v}" for k, v in os.environ.items() if k.startswith("SPARKLE_"))
    with open(os.environ["FAKE_LOG"], "a") as f:
        f.write(json.dumps({"key": key, "pid": os.getpid(), "env": sparkle}) + "\n")
    cmd_line = next((i + 1 for i, ln in enumerate(lines) if ln.startswith("#verify_elab_deep")), 1)

    def msg(sev, s, line=cmd_line):
        print(f"{case}:{line}:0: {sev}: {s}", flush=True)
    for kv in sparkle:
        msg("info", f"FAKE ENVSEEN {kv}")
    ns = plan.get("ns", "Outer.VedU0Case_R" + key)
    if plan.get("ns_line", True):
        msg("info", f"VED NS {ns}")
    top = plan.get("top", "x")
    if plan.get("decl", "found") == "found":
        q = plan.get("qualified", f"Outer.{top}")
        msg("info", f"VED DECL resolved={q} user={q} inventory={q} match")
    else:
        msg("info", f"VED DECL absent: unknown constant '{top}'")
    for n, (v, axs) in sorted(plan.get("theorems", {}).items()):
        msg("info", f"VED AUDIT {ns}.{n} strict={v} axioms=[{', '.join(axs)}]")
    for s in plan.get("stdout", []):
        msg("info", s)
    if plan.get("error_in_block"):
        msg("error", plan["error_in_block"])
    if plan.get("error_outside_line"):
        msg("error", "unknown identifier 'foo_deep_trace'", line=plan["error_outside_line"])
    if "ret" in plan:
        msg("info", f"VED RET {plan['ret']}")
        msg("info", "VED SECONDRUN modules=1")
        for o in plan.get("outputs", []):
            msg("info", f"VED OUTPUT {o}")
        if plan.get("body"):
            msg("info", f"VED BODY {plan['body']}")
    pids = []
    for _ in range(plan.get("children", 0)):
        pids.append(subprocess.Popen(["sleep", "300"]).pid)
    if plan.get("setsid_child"):
        pids.append(subprocess.Popen(["sleep", "300"], start_new_session=True).pid)
    if plan.get("orphan_child"):
        # a grandchild whose parent exits at once: re-parented to the subreaper
        p = subprocess.Popen(["sh", "-c", "sleep 300 & echo $!"], stdout=subprocess.PIPE, text=True)
        pids.append(int(p.stdout.readline()))
        p.wait()
    if pids and os.environ.get("FAKE_PIDS"):
        with open(os.environ["FAKE_PIDS"], "a") as f:
            f.write("\n".join(map(str, pids)) + "\n")
    if plan.get("mem_mb"):
        subprocess.run([sys.executable, "-c",
                        f"b = bytearray({plan['mem_mb']} * 1024 * 1024)\n"
                        "for i in range(0, len(b), 4096): b[i] = 1\n"
                        "import time; time.sleep(0.3)"], check=True)
    if plan.get("sleep"):
        time.sleep(plan["sleep"])
    if plan.get("self_signal"):
        os.kill(os.getpid(), plan["self_signal"])
        time.sleep(5)
    sys.exit(plan.get("exit", 0))


if __name__ == "__main__":
    main()
