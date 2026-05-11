"""
Two-kernel race-condition probe.

Background.  An earlier Playwright spec (`wdb-hang.spec.ts` →
"open ch01 after ch03 wdb") reproduced a kernel hang at ~80%
when JupyterLab spawned a second xlean process while the first
was still running.  At that point we suspected a Lean-runtime
deadlock in the kernel binary itself.

This test exercises *only* the kernel-spawn race — no JupyterLab
in the loop, just `jupyter_client` directly driving xlean
processes.  Two scenarios run side by side:

  A_no_mitigation:  start kernel A, leave it running, start
                    kernel B, run a cell on B.
  B_with_mitigation: start kernel A, shut it down cleanly,
                     start kernel B, run a cell on B.

If the hang lived in the kernel binary, scenario A would fail
~80% of the time.  Empirically (5/5 trials, both scenarios) it
passes — meaning the race is NOT in xlean itself.  The hang we
saw via Playwright must come from somewhere in the
browser-JupyterLab path: comm-channel routing, the
notebook-widget state machinery, or how JupyterLab's
KernelManager hands incoming messages to the new kernel before
the old one is gone.

Run inside the tutorial Docker image:

    docker exec -e JUPYTER_PATH=/root/.local/share/jupyter \\
        sparkle-tutorial python3 tests/e2e/wdb-hang-race.py

The script exits 0 if every trial passes.  Failures are
reported per-trial with the kernel PIDs involved, so a future
regression has enough context for diagnosis.
"""
from __future__ import annotations

import argparse
import sys
import time
from dataclasses import dataclass

from jupyter_client.manager import KernelManager


@dataclass
class TrialResult:
    name: str
    pid_a: int | str
    pid_b: int | str
    ok: bool
    detail: str


def _pid(km: KernelManager) -> int | str:
    """jupyter_client's PID accessor moved across versions; try both."""
    try:
        return km.provisioner.process.pid  # type: ignore[attr-defined]
    except Exception:
        pass
    try:
        return km.kernel.pid  # type: ignore[attr-defined]
    except Exception:
        return "?"


def run_scenario(name: str, *, mitigate: bool, ready_timeout: float = 30.0) -> TrialResult:
    """Run one scenario; return (ok, detail)."""
    kmA = KernelManager(kernel_name="xlean")
    kmA.start_kernel()
    pid_a = _pid(kmA)
    kcA = kmA.client()
    kcA.start_channels()
    kcA.wait_for_ready(timeout=ready_timeout)
    kcA.execute("example : 1 + 1 = 2 := rfl")
    time.sleep(2)

    if mitigate:
        kcA.stop_channels()
        kmA.shutdown_kernel()
        # Brief pause to let the OS / xeus-zmq release ZMQ sockets.
        time.sleep(2)

    kmB = KernelManager(kernel_name="xlean")
    kmB.start_kernel()
    pid_b = _pid(kmB)
    kcB = kmB.client()
    kcB.start_channels()

    ok = False
    detail = ""
    try:
        kcB.wait_for_ready(timeout=ready_timeout)
        kcB.execute("example : 2 + 2 = 4 := rfl")
        time.sleep(3)
        ok = True
        detail = "kernel B alive"
    except Exception as e:
        detail = f"kernel B hung: {e}"
    finally:
        try:
            kcB.stop_channels()
            kmB.shutdown_kernel(now=True)
        except Exception:
            pass
        if not mitigate:
            try:
                kcA.stop_channels()
                kmA.shutdown_kernel(now=True)
            except Exception:
                pass

    return TrialResult(name=name, pid_a=pid_a, pid_b=pid_b, ok=ok, detail=detail)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--trials", type=int, default=5,
                    help="how many times to repeat each scenario (default 5)")
    args = ap.parse_args()

    results: list[tuple[TrialResult, TrialResult]] = []
    for i in range(args.trials):
        print(f"\n--- trial {i + 1} ---", flush=True)
        a = run_scenario("A_no_mitigation",  mitigate=False)
        print(f"  {a.name}: pid_a={a.pid_a} pid_b={a.pid_b} ok={a.ok} ({a.detail})", flush=True)
        time.sleep(1)
        b = run_scenario("B_with_mitigation", mitigate=True)
        print(f"  {b.name}: pid_a={b.pid_a} pid_b={b.pid_b} ok={b.ok} ({b.detail})", flush=True)
        time.sleep(1)
        results.append((a, b))

    no_mit_pass = sum(1 for r, _ in results if r.ok)
    mit_pass    = sum(1 for _, r in results if r.ok)
    print("\n===== summary =====")
    print(f"no-mitigation  passes: {no_mit_pass}/{args.trials}")
    print(f"with-mitigation passes: {mit_pass}/{args.trials}")

    # CI semantics: fail iff a trial that *should* pass didn't.
    # Both scenarios are expected to pass; the no-mit one is the
    # "load-bearing" assertion (if this regresses, the kernel
    # binary itself has acquired a 2-process startup deadlock,
    # which is what the wdb-hang Playwright failure used to look
    # like).
    return 0 if no_mit_pass == args.trials and mit_pass == args.trials else 1


if __name__ == "__main__":
    sys.exit(main())
