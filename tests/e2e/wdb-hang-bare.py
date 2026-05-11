"""
Bare-metal two-kernel race probe.

This is the lower-level cousin of `wdb-hang-race.py`.  Where that
script drives kernels through `jupyter_client` (which manages
clean shutdown / port allocation for you), this one bypasses
all of that and talks ZeroMQ directly so we can reproduce the
*exact* state the buggy JupyterLab path leaves behind:

  scenario A — same-connection-file race:
    write ONE connection file, spawn xlean against it twice in
    a row.  This is what the Playwright trace showed: two
    xlean PIDs bound to identical ports.  Both processes
    inherit the same ZMQ ports, the OS load-balances incoming
    messages between them, and the second one's main thread
    can end up futex-stuck while xeus-zmq's worker threads
    spin on iopub.

  scenario B — distinct-connection-files, overlapping lifetime:
    write two connection files (different ports), spawn xlean
    A then xlean B without shutting A down.  Talk to B over
    its own ZMQ.  This mirrors `jupyter_client`-driven coexistence
    minus the cleanup hook.

  scenario C — sequential, with explicit shutdown:
    spawn xlean A, send shutdown_request, wait for exit, then
    spawn B.  This is the "mitigated" baseline.

We send a single `execute_request` to the second kernel and
report whether the reply arrives within 20 s.  No reply → hang.

Connection file format and ZMQ key handling follow the Jupyter
messaging spec v5.3.

Run inside the tutorial Docker image:

    docker exec sparkle-tutorial python3 tests/e2e/wdb-hang-bare.py

Exits 0 if every scenario passes (no hang).
"""
from __future__ import annotations

import argparse
import hashlib
import hmac
import json
import os
import socket
import subprocess
import sys
import tempfile
import time
import uuid
from contextlib import closing
from dataclasses import dataclass

import zmq


XLEAN_BIN = os.environ.get("XLEAN_BIN", "/opt/xeus-lean/.lake/build/bin/xlean")
KERNELSPEC_PATH = os.environ.get(
    "XLEAN_KERNELSPEC",
    "/root/.local/share/jupyter/kernels/xlean/kernel.json",
)


def _kernel_env() -> dict[str, str]:
    """Merge the xlean kernelspec's `env` into the current process
    env.  Without `LEAN_PATH` / `LD_LIBRARY_PATH` the binary
    starts and immediately exits, so this isn't optional."""
    env = dict(os.environ)
    try:
        with open(KERNELSPEC_PATH) as f:
            spec = json.load(f)
        env.update(spec.get("env", {}))
    except FileNotFoundError:
        pass
    return env


def _free_tcp_port() -> int:
    """Bind to port 0, take what the OS gives us, release.  Race-y by
    nature (port could be reused before the kernel binds) — keep
    the window narrow by binding kernel right after."""
    with closing(socket.socket(socket.AF_INET, socket.SOCK_STREAM)) as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def make_connection_file(*, key: str | None = None) -> tuple[str, dict]:
    """Write a connection file with five fresh ports.  Returns
    (path, parsed dict)."""
    cfg = {
        "shell_port":   _free_tcp_port(),
        "iopub_port":   _free_tcp_port(),
        "stdin_port":   _free_tcp_port(),
        "control_port": _free_tcp_port(),
        "hb_port":      _free_tcp_port(),
        "ip": "127.0.0.1",
        "key": key or str(uuid.uuid4()),
        "transport": "tcp",
        "signature_scheme": "hmac-sha256",
        "kernel_name": "xlean",
    }
    fd, path = tempfile.mkstemp(prefix="conn-", suffix=".json")
    os.write(fd, json.dumps(cfg).encode())
    os.close(fd)
    return path, cfg


def sign(key: bytes, parts: list[bytes]) -> bytes:
    h = hmac.new(key, digestmod=hashlib.sha256)
    for p in parts:
        h.update(p)
    return h.hexdigest().encode("ascii")


def send_msg(sock: zmq.Socket, key: bytes, msg_type: str, content: dict,
             *, session: str | None = None) -> str:
    """Build + send a v5 wire-format Jupyter message on `sock`.
    Returns the msg_id."""
    msg_id = uuid.uuid4().hex
    session = session or uuid.uuid4().hex
    header = json.dumps({
        "msg_id": msg_id,
        "username": "test",
        "session": session,
        "msg_type": msg_type,
        "version": "5.3",
        "date": "2025-01-01T00:00:00.000Z",
    }).encode()
    parent_header = b"{}"
    metadata = b"{}"
    content_b = json.dumps(content).encode()
    parts = [header, parent_header, metadata, content_b]
    signature = sign(key, parts)
    sock.send_multipart([b"<IDS|MSG>", signature, *parts])
    return msg_id


def recv_msg(sock: zmq.Socket, timeout_s: float) -> dict | None:
    """Wait up to timeout_s seconds for a message on `sock`.  Returns
    the parsed `{header, parent_header, metadata, content}` dict
    or None on timeout.  Doesn't verify signatures (trust the
    socket; keeps this script short)."""
    poller = zmq.Poller()
    poller.register(sock, zmq.POLLIN)
    deadline = time.monotonic() + timeout_s
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            return None
        events = dict(poller.poll(int(remaining * 1000)))
        if sock not in events:
            return None
        frames = sock.recv_multipart()
        # Strip routing prefix (frames before <IDS|MSG>).
        try:
            ids_idx = frames.index(b"<IDS|MSG>")
        except ValueError:
            continue
        sig, header_b, parent_b, meta_b, content_b = frames[ids_idx + 1:ids_idx + 6]
        try:
            return {
                "header": json.loads(header_b),
                "parent_header": json.loads(parent_b),
                "metadata": json.loads(meta_b),
                "content": json.loads(content_b),
            }
        except json.JSONDecodeError:
            continue


@dataclass
class Kernel:
    proc: subprocess.Popen
    cfg: dict
    conn_path: str
    ctx: zmq.Context
    shell: zmq.Socket
    iopub: zmq.Socket

    @property
    def pid(self) -> int:
        return self.proc.pid


def spawn_kernel(conn_path: str, cfg: dict) -> Kernel:
    """Start xlean against `conn_path` and connect ZMQ shell+iopub."""
    proc = subprocess.Popen(
        [XLEAN_BIN, conn_path],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        env=_kernel_env(),
    )
    ctx = zmq.Context.instance()
    shell = ctx.socket(zmq.DEALER)
    shell.setsockopt(zmq.IDENTITY, uuid.uuid4().bytes)
    shell.connect(f"tcp://{cfg['ip']}:{cfg['shell_port']}")
    iopub = ctx.socket(zmq.SUB)
    iopub.setsockopt(zmq.SUBSCRIBE, b"")
    iopub.connect(f"tcp://{cfg['ip']}:{cfg['iopub_port']}")
    return Kernel(proc=proc, cfg=cfg, conn_path=conn_path,
                  ctx=ctx, shell=shell, iopub=iopub)


def wait_for_ready(k: Kernel, *, timeout_s: float = 30.0) -> bool:
    """Send `kernel_info_request` until we get a reply, mirroring
    `jupyter_client.KernelManager.wait_for_ready`.  Without this,
    early `execute_request` payloads can be lost (xeus-zmq
    drops messages on a not-yet-bound socket).  Returns True on
    success."""
    key = k.cfg["key"].encode()
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        if k.proc.poll() is not None:
            return False
        msg_id = send_msg(k.shell, key, "kernel_info_request", {})
        # Listen for a reply for up to 1 s, retry on timeout.
        msg = recv_msg(k.shell, min(1.0, deadline - time.monotonic()))
        if (msg is not None
                and msg["header"]["msg_type"] == "kernel_info_reply"
                and msg["parent_header"].get("msg_id") == msg_id):
            return True
    return False


def cleanup(k: Kernel) -> None:
    try:
        k.shell.close(linger=0)
        k.iopub.close(linger=0)
    except Exception:
        pass
    try:
        k.proc.terminate()
        k.proc.wait(timeout=5)
    except Exception:
        try:
            k.proc.kill()
        except Exception:
            pass
    try:
        os.unlink(k.conn_path)
    except OSError:
        pass


def execute_and_wait(k: Kernel, code: str, timeout_s: float = 20.0) -> tuple[bool, str]:
    """Send execute_request, return (ok, detail)."""
    key = k.cfg["key"].encode()
    msg_id = send_msg(k.shell, key, "execute_request", {
        "code": code,
        "silent": False,
        "store_history": True,
        "user_expressions": {},
        "allow_stdin": False,
        "stop_on_error": True,
    })
    deadline = time.monotonic() + timeout_s
    while time.monotonic() < deadline:
        msg = recv_msg(k.shell, deadline - time.monotonic())
        if msg is None:
            return False, f"timeout waiting for execute_reply (msg_id={msg_id})"
        if msg["header"]["msg_type"] == "execute_reply" \
           and msg["parent_header"].get("msg_id") == msg_id:
            return True, f"execute_reply status={msg['content'].get('status')}"
    return False, "deadline exceeded"


# -----------------------------------------------------------------
# Scenarios
# -----------------------------------------------------------------

def scenario_same_conn() -> tuple[bool, str]:
    """Two xlean processes, SAME connection file.  This is what the
    Playwright trace showed (two xlean PIDs bound to identical
    ports).  We send execute_request to the second kernel."""
    conn_path, cfg = make_connection_file()
    kA = spawn_kernel(conn_path, cfg)
    kB = spawn_kernel(conn_path, cfg)  # same conn_path on purpose
    # Wait until at least one of them is responsive.
    readyA = wait_for_ready(kA, timeout_s=30)
    readyB = wait_for_ready(kB, timeout_s=30)
    if not (readyA or readyB):
        detail = f"pidA={kA.pid} pidB={kB.pid}: neither kernel became ready"
        cleanup(kA); cleanup(kB)
        return False, detail
    # Same-conn means both kernels are listening on the same shell
    # port; OS load-balances incoming messages.  Whichever responds
    # first wins our request.
    ok, detail = execute_and_wait(kB, "example : 1 + 1 = 2 := rfl", timeout_s=20)
    detail = f"pidA={kA.pid}({readyA}) pidB={kB.pid}({readyB}): {detail}"
    cleanup(kA)
    cleanup(kB)
    return ok, detail


def scenario_distinct_conn_overlap() -> tuple[bool, str]:
    """Two xlean processes with DIFFERENT connection files,
    overlapping lifetime.  This mirrors what jupyter_client does
    when JupyterLab keeps two notebook tabs open."""
    pathA, cfgA = make_connection_file()
    pathB, cfgB = make_connection_file()
    kA = spawn_kernel(pathA, cfgA)
    if not wait_for_ready(kA, timeout_s=30):
        cleanup(kA)
        os.unlink(pathB)
        return False, "kernel A never became ready"
    # Drive A briefly so its kernelLoop is healthy.
    okA, _ = execute_and_wait(kA, "1", timeout_s=15)
    if not okA:
        cleanup(kA)
        os.unlink(pathB)
        return False, "kernel A never responded"
    kB = spawn_kernel(pathB, cfgB)
    if not wait_for_ready(kB, timeout_s=30):
        detail = f"pidA={kA.pid} pidB={kB.pid}: kernel B never became ready"
        cleanup(kA); cleanup(kB)
        return False, detail
    ok, detail = execute_and_wait(kB, "example : 2 + 2 = 4 := rfl", timeout_s=20)
    detail = f"pidA={kA.pid} pidB={kB.pid}: {detail}"
    cleanup(kA)
    cleanup(kB)
    return ok, detail


def scenario_same_conn_with_comm_storm() -> tuple[bool, str]:
    """Two xlean processes on the same connection file, then we
    flood the shared shell port with `comm_open` + `comm_msg`
    payloads of the shape the wdb viewer sends — without first
    waiting for either kernel to register a session named
    `i2c-session`.  The point is to reproduce what JupyterLab's
    JS does when a stale wdb tab is alive while a new tab spawns:
    its widget keeps emitting `comm_msg` over a shared shell, so
    the freshly-spawned kernel sees comm traffic for sessions it
    never opened.

    If the hang lives in the kernel's comm dispatcher, the second
    kernel's main loop should futex-deadlock here; otherwise
    `execute_request` still returns.
    """
    conn_path, cfg = make_connection_file()
    kA = spawn_kernel(conn_path, cfg)
    kB = spawn_kernel(conn_path, cfg)
    readyA = wait_for_ready(kA, timeout_s=30)
    readyB = wait_for_ready(kB, timeout_s=30)
    if not (readyA and readyB):
        detail = f"pidA={kA.pid}({readyA}) pidB={kB.pid}({readyB}): not both ready"
        cleanup(kA); cleanup(kB)
        return False, detail
    key = cfg["key"].encode()
    # Open a comm pretending we're the wdb JS frontend.
    comm_id = uuid.uuid4().hex
    send_msg(kA.shell, key, "comm_open", {
        "comm_id": comm_id,
        "target_name": "xlean",
        "data": {"session": "i2c-session"},
    })
    # Hose down with comm_msg for ~1 s.
    storm_until = time.monotonic() + 1.0
    while time.monotonic() < storm_until:
        send_msg(kA.shell, key, "comm_msg", {
            "comm_id": comm_id,
            "data": {"op": "ping"},
        })
        time.sleep(0.01)
    # Now ask kernel B to execute.
    ok, detail = execute_and_wait(kB, "example : 4 + 4 = 8 := rfl", timeout_s=20)
    detail = f"pidA={kA.pid} pidB={kB.pid}: {detail}"
    cleanup(kA)
    cleanup(kB)
    return ok, detail


def scenario_sequential_with_shutdown() -> tuple[bool, str]:
    """Spawn A, send shutdown_request, wait for exit, then spawn B.
    The mitigated baseline."""
    pathA, cfgA = make_connection_file()
    kA = spawn_kernel(pathA, cfgA)
    if not wait_for_ready(kA, timeout_s=30):
        cleanup(kA)
        return False, "kernel A never became ready"
    okA, _ = execute_and_wait(kA, "1", timeout_s=15)
    if not okA:
        cleanup(kA)
        return False, "kernel A never responded"
    keyA = cfgA["key"].encode()
    send_msg(kA.shell, keyA, "shutdown_request", {"restart": False})
    try:
        kA.proc.wait(timeout=10)
    except subprocess.TimeoutExpired:
        kA.proc.kill()
    cleanup(kA)
    pathB, cfgB = make_connection_file()
    kB = spawn_kernel(pathB, cfgB)
    if not wait_for_ready(kB, timeout_s=30):
        detail = f"pidB={kB.pid}: kernel B never became ready"
        cleanup(kB)
        return False, detail
    ok, detail = execute_and_wait(kB, "example : 3 + 3 = 6 := rfl", timeout_s=20)
    detail = f"pidB={kB.pid}: {detail}"
    cleanup(kB)
    return ok, detail


# -----------------------------------------------------------------
# main
# -----------------------------------------------------------------

SCENARIOS = [
    ("same_conn (Playwright-trace pattern)",          scenario_same_conn),
    ("same_conn_with_comm_storm (wdb-like traffic)",  scenario_same_conn_with_comm_storm),
    ("distinct_conn_overlap (jupyter_client-like)",   scenario_distinct_conn_overlap),
    ("sequential_with_shutdown (mitigated)",          scenario_sequential_with_shutdown),
]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--trials", type=int, default=3,
                    help="how many times to repeat each scenario")
    args = ap.parse_args()

    overall: dict[str, list[bool]] = {name: [] for name, _ in SCENARIOS}
    for trial in range(args.trials):
        print(f"\n--- trial {trial + 1} ---", flush=True)
        for name, fn in SCENARIOS:
            ok, detail = fn()
            overall[name].append(ok)
            mark = "PASS" if ok else "HANG"
            print(f"  [{mark}] {name}: {detail}", flush=True)
            time.sleep(1)

    print("\n===== summary =====")
    fail = 0
    for name, _ in SCENARIOS:
        passes = sum(overall[name])
        total = len(overall[name])
        print(f"  {name}: {passes}/{total} pass")
        if passes != total:
            fail += 1
    return 0 if fail == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
