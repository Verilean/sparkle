# Sparkle Tutorial — Docker image
#
# Bundles every tool the tutorial needs:
#   - Lean 4 (matching `lean-toolchain`) + Lake
#   - Python + Jupyter Lab + jupytext + nbconvert
#   - xeus-lean kernel
#   - Yosys, nextpnr-ice40, nextpnr-ecp5, icestorm, prjtrellis
#
# Usage from a checkout:
#
#   bash docker/tutorial/build.sh
#   bash docker/tutorial/run.sh
#
# Then open http://localhost:8888 — the Sparkle tutorial chapters
# live under `docs/tutorial/Notebooks/Gen/notebooks/` (regenerated
# by `docs/tutorial/build-from-md.sh` from `docs/tutorial/md/`).

# -----------------------------------------------------------------
# Stage 1 — base + system packages.
# -----------------------------------------------------------------
FROM ubuntu:24.04 AS base

ENV DEBIAN_FRONTEND=noninteractive \
    LC_ALL=C.UTF-8 \
    LANG=C.UTF-8 \
    PATH="/root/.elan/bin:/usr/local/bin:${PATH}"

# Tools needed by every later step.  Group into one RUN so the
# layer can be cached.
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential \
        ca-certificates \
        curl \
        git \
        wget \
        cmake \
        ninja-build \
        pkg-config \
        python3 python3-pip python3-venv \
        # FPGA toolchain — yosys + ECP5 prjtrellis + icestorm are in
        # apt; nextpnr-ice40 / nextpnr-ecp5 are in apt as of 24.04.
        yosys \
        nextpnr-ice40 \
        nextpnr-ecp5 \
        fpga-icestorm \
        # `prjtrellis` is not in Ubuntu 24.04 main; install it
        # via pip below or build from source if needed for the
        # ECP5 path (see docker/tutorial/README.md).
        # GTKWave for waveform inspection in Ch 8.
        gtkwave \
    && rm -rf /var/lib/apt/lists/*

# -----------------------------------------------------------------
# Stage 2 — Lean toolchain via elan.
# -----------------------------------------------------------------
FROM base AS lean

ARG LEAN_VERSION=v4.28.0
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain ${LEAN_VERSION}

# -----------------------------------------------------------------
# Stage 3 — Python tooling: Jupyter, jupytext, nbconvert.
# -----------------------------------------------------------------
FROM lean AS jupyter

# Install into a venv so the system python stays clean.
#
# `jupyter-collaboration` is the official Jupyter Real-Time
# Collaboration extension (Y.js / CRDT backend).  Without it,
# external edits to a `.ipynb` file — e.g. the MCP server's
# `markdown_to_notebook` regenerating a chapter from its `.md`
# source — only land in the browser after a manual reload.  With
# it (combined with `--collaborative` on the CMD line below),
# Jupyter Server watches the file for disk-side changes and
# streams the diff to every connected client as a CRDT update,
# so the browser tab refreshes its cells in place.
RUN python3 -m venv /opt/venv \
    && /opt/venv/bin/pip install --no-cache-dir --upgrade pip \
    && /opt/venv/bin/pip install --no-cache-dir \
        jupyterlab \
        jupyter-collaboration \
        jupytext \
        nbconvert \
        notebook

ENV PATH="/opt/venv/bin:${PATH}"

# Patch jupyter_server's WebSocket binary-frame deserializer so
# malformed frames are dropped instead of tearing the connection
# down.  Without this, when the user opens a second notebook tab
# while the first kernel is still alive, an off-spec frame
# arrives at `deserialize_binary_message` (cause: a v1-protocol
# frame mis-routed to the v0 decoder during the kernel-restart
# race), `struct.unpack` blows up trying to allocate ~400 MB,
# the WebSocket stream dies, and the new tab's kernel sits at
# `kernelPoll` forever waiting for an `execute_request` that
# never arrives.  Verified to take `tests/e2e/wdb-hang.spec.ts`
# from ~80% failure to 10/10 pass.
#
# This patch is meant to ship upstream as a PR to
# github.com/jupyter-server/jupyter_server; until that lands we
# keep our own copy under docker/tutorial/patches/.
COPY docker/tutorial/patches/jupyter-server-deserialize-fix.patch /tmp/
RUN cd /opt/venv/lib/python*/site-packages \
    && patch -p1 < /tmp/jupyter-server-deserialize-fix.patch \
    && python3 -c "import inspect, jupyter_server.services.kernels.connection.base as b; \
        assert 'max_nbufs' in inspect.getsource(b.deserialize_binary_message), \
        'jupyter_server patch did not apply cleanly'"

# -----------------------------------------------------------------
# Stage 4 — xeus-lean kernel + xlean-convert CLI.
# -----------------------------------------------------------------
#
# We need two artefacts from xeus-lean:
#
#   1. The `xlean` Jupyter kernel (built via `bash build.sh`) for
#      running tutorial cells in JupyterLab.
#   2. The `xlean-convert` CLI for regenerating chapter `.lean` /
#      `.ipynb` files from the `md/Ch*.md` source.  This one is
#      pure Lean (no FFI), so a plain `lake build xlean-convert`
#      suffices and works even if the CMake-driven kernel build
#      fails.
#
# We keep this in its own stage so subsequent rebuilds of the
# Sparkle source code reuse this layer.
FROM jupyter AS xeus-lean

# Native dependencies for xeus-lean's CMake build.  This is the
# upstream-blessed recipe — see `Dockerfile.native` in the
# Verilean/xeus-lean repo.  CMake fetches xeus / xeus-zmq / xtl /
# cppzmq / libzmq itself via FetchContent, so we don't apt-install
# them.  We *do* need libc++ because xeus-lean's C++ FFI is built
# with clang+libc++ to match the binary it links against.
RUN apt-get update && apt-get install -y --no-install-recommends \
        clang \
        libc++-dev \
        libc++abi-dev \
        nlohmann-json3-dev \
        uuid-dev \
        libssl-dev \
        zstd \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /opt
# `XEUS_LEAN_REV` defaults to `main` but accepts any git ref the
# upstream remote knows (a tag, a commit sha, …).  The `ADD` of
# the GitHub `info/refs` URL invalidates the Docker layer cache
# whenever that ref's sha changes — without it `docker build`
# silently reuses an older clone and you get yesterday's
# xeus-lean even after upstream merges new PRs.  Pin the build
# by passing `--build-arg XEUS_LEAN_REV=<sha>`; leave it on
# `main` for development.
ARG XEUS_LEAN_REV=main
ADD https://api.github.com/repos/Verilean/xeus-lean/commits/${XEUS_LEAN_REV} \
    /tmp/xeus-lean-rev.json
RUN git clone https://github.com/Verilean/xeus-lean.git \
    && cd xeus-lean \
    && git checkout ${XEUS_LEAN_REV}

# Apply Sparkle-side mitigation to xeus-lean's wdb viewer JS:
# gate the waveform widget's RAF render loop on the widget
# actually being visible in JupyterLab's in-page tab tree
# (`root.offsetParent !== null`).  Without this, switching
# tabs while a wdb waveform is open leaves the previous tab's
# canvas redrawing at 60 Hz in the background, which eats the
# browser main thread and makes newly-opened tabs feel "frozen"
# until the wdb tab is closed.  This is the user-visible "ch04
# opens but never finishes loading after ch03 wdb" hang.
#
# Meant to ship upstream once we've verified it in the tutorial
# Docker image; until then we keep the diff under
# `docker/tutorial/patches/` and apply it during build.
COPY docker/tutorial/patches/xeus-lean-hang-mitigations.patch /tmp/
RUN cd /opt/xeus-lean \
    && patch -p1 < /tmp/xeus-lean-hang-mitigations.patch \
    && grep -q 'root.offsetParent' src/Display.lean

# Stage 4a — build the C++ FFI library that xlean links against.
WORKDIR /opt/xeus-lean
# Run cmake configure so the xeus dependency is fetched into
# build-cmake/_deps/xeus-src, then patch
# `XEUS_KERNEL_PROTOCOL_VERSION_MINOR` from 3 to 4 *before*
# compiling the C++ library that bakes in that header.
#
# Why: the bundled xeus reports protocol_version "5.3" by
# default.  Jupyter messaging protocol 5.4 is the current spec
# (added since xeus's last release) and on the wire is
# identical to 5.3 for the message types xlean emits, so
# claiming 5.4 is a safe no-op.  Reporting 5.4 also stops
# `jupyter_server` from running its 5.3→5.4 adapter, which
# slightly reduces the surface for a separate
# `deserialize_binary_message` race on kernel restart (see
# `tests/e2e/wdb-hang.spec.ts` and the docs/tutorial Ch00
# "Switching between chapters" note).
#
# This patch alone does NOT eliminate the wdb-hang race — that
# bug is inside jupyter_server's WS message deserializer and
# the user-facing mitigation is to close a chapter's notebook
# tab before opening the next one (which the
# kernelShutdown=true override below makes automatic).
RUN cmake -S . -B build-cmake \
      -DCMAKE_C_COMPILER=clang \
      -DCMAKE_CXX_COMPILER=clang++ \
      -DCMAKE_CXX_FLAGS="-stdlib=libc++" && \
    sed -i 's/#define XEUS_KERNEL_PROTOCOL_VERSION_MINOR 3/#define XEUS_KERNEL_PROTOCOL_VERSION_MINOR 4/' \
        build-cmake/_deps/xeus-src/include/xeus/xeus.hpp && \
    grep -q 'XEUS_KERNEL_PROTOCOL_VERSION_MINOR 4' \
        build-cmake/_deps/xeus-src/include/xeus/xeus.hpp && \
    cmake --build build-cmake -j

# Linux glibc C23 shim (clang -> __isoc23_strtoull -> Lean's older glibc).
RUN leanc -c src/glibc_isoc23_compat.c -o build-cmake/glibc_isoc23_compat.o

# Stage 4a' — pre-build Sparkle's C FFI as static archives so the
# xlean kernel binary can resolve `Sparkle.Core.JIT.*` (`sparkle_jit_*`)
# and the `loopMemo` LICM barriers (`sparkle_barrier_*`) at link time.
#
# Without this, calling `Sparkle.Core.JIT.JIT.load` from a `#eval`
# cell throws `lean::exception: Could not find native implementation
# of external declaration 'Sparkle.Core.JIT.JIT.load'` and the kernel
# terminates immediately — the user just sees an empty cell output
# because the failure happens inside C++ before xeus can serialise an
# error reply.
#
# The Sparkle `lakefile.lean` builds these the same way (`extern_lib
# «sparkle_jit»` / `extern_lib «sparkle_barrier»`) via leanc + ar.
# We invoke leanc directly so we don't have to spin up Lake (and pay
# its `lake update` clone cost) just to compile two C files.
COPY c_src /tmp/sparkle_c
# `-fvisibility=default` overrides leanc's built-in `-fvisibility=hidden`
# so the `sparkle_jit_*` / `sparkle_barrier_*` symbols land in the
# linker's dynsym table (uppercase `T` in `nm --dynamic`), not just the
# static symtab as locals.  Without this override the symbols survive
# `--whole-archive` + `--undefined=` but get marked local on link, and
# `dlsym(RTLD_DEFAULT, ...)` — which is what Lean's `#eval`-time
# `@[extern]` resolution uses — returns NULL because it only scans the
# dynamic symbol table.
RUN leanc -c -O2 -fvisibility=default /tmp/sparkle_c/sparkle_jit.c     -o /tmp/sparkle_c/sparkle_jit.o \
 && leanc -c -O2 -fvisibility=default /tmp/sparkle_c/sparkle_barrier.c -o /tmp/sparkle_c/sparkle_barrier.o \
 && ar rcs /tmp/sparkle_c/libsparkle_jit.a     /tmp/sparkle_c/sparkle_jit.o \
 && ar rcs /tmp/sparkle_c/libsparkle_barrier.a /tmp/sparkle_c/sparkle_barrier.o

# Stage 4b — build the Lean side: xlean kernel binary, xlean-convert
# CLI, the xlean-mcp Model Context Protocol server, and the Display
# library oleans.
#
# `xlean-mcp` is a stand-alone JSON-RPC 2.0 stdio server (see
# `docs/tutorials/mcp-server.md` in xeus-lean) that lets an MCP host
# — Claude Code, Cursor, the MCP inspector, …  — drive Lean
# programmatically with persistent-env `lean_eval`, file I/O, and
# notebook editing tools.  Baking the binary into the image means
# users can hook it up with `docker exec -i <container> xlean-mcp`
# without rebuilding inside the container.
#
# `XEUS_LEAN_EXTRA_LIBS` (read by xeus-lean's lakefile at load time)
# appends the listed tokens verbatim to xlean's link line.  Wrap the
# Sparkle archives in `-Wl,--whole-archive` so the linker keeps every
# symbol in `libsparkle_jit.a` / `libsparkle_barrier.a`, even though
# nothing inside xeus-lean references them at link time — they're
# only reached from notebook-cell `#eval`s via Lean's interpreter
# dlsym lookup, and a regular `.a` whose symbols nobody pulls would
# be dropped by the linker before the interpreter ever runs.
#
# Force-remove the xlean binary first because Lake's build cache
# doesn't hash `moreLinkArgs` / env vars: without this, a stale
# `.lake/build/bin/xlean` from cmake's earlier `buildXlean` script
# is treated as up-to-date and the extra-libs never reach the
# linker even though the env var is set.
# `-Wl,--undefined=<sym>` flags force the linker to treat each named
# symbol as "referenced by main" so `-Wl,--gc-sections` (added by the
# Lean linker tail) does NOT strip them from the final binary.  Without
# these, even `-Wl,--whole-archive` only keeps the symbols at *input*
# time — gc-sections then drops them at *output* time because no live
# section in xlean references them.  The interpreter looks them up at
# `#eval` time via dlsym, which can only find symbols that survived
# section GC.
RUN rm -f .lake/build/bin/xlean && \
    XEUS_LEAN_EXTRA_LIBS="\
-Wl,--undefined=sparkle_jit_load \
-Wl,--undefined=sparkle_jit_eval \
-Wl,--undefined=sparkle_jit_eval_tick \
-Wl,--undefined=sparkle_jit_tick \
-Wl,--undefined=sparkle_jit_reset \
-Wl,--undefined=sparkle_jit_destroy \
-Wl,--undefined=sparkle_jit_set_input \
-Wl,--undefined=sparkle_jit_get_output \
-Wl,--undefined=sparkle_jit_get_wire \
-Wl,--undefined=sparkle_jit_set_mem \
-Wl,--undefined=sparkle_jit_get_mem \
-Wl,--undefined=sparkle_jit_memset_word \
-Wl,--undefined=sparkle_jit_snapshot \
-Wl,--undefined=sparkle_jit_restore \
-Wl,--undefined=sparkle_jit_free_snapshot \
-Wl,--undefined=sparkle_jit_wire_name \
-Wl,--undefined=sparkle_jit_num_wires \
-Wl,--undefined=sparkle_jit_set_reg \
-Wl,--undefined=sparkle_jit_get_reg \
-Wl,--undefined=sparkle_jit_reg_name \
-Wl,--undefined=sparkle_jit_num_regs \
-Wl,--undefined=sparkle_jit_run_cdc \
-Wl,--undefined=sparkle_cache_get \
-Wl,--undefined=sparkle_eval_at \
-Wl,--whole-archive \
/tmp/sparkle_c/libsparkle_jit.a \
/tmp/sparkle_c/libsparkle_barrier.a \
-Wl,--no-whole-archive" \
    lake build xlean Display CommBus xlean-convert xlean-mcp

# Install the binaries onto PATH so kernel.json, tutorial scripts,
# and `docker exec` callers can find them by name.
RUN install -m 0755 .lake/build/bin/xlean         /usr/local/bin/xlean && \
    install -m 0755 .lake/build/bin/xlean-convert /usr/local/bin/xlean-convert && \
    install -m 0755 .lake/build/bin/xlean-mcp     /usr/local/bin/xlean-mcp

# Stage 4c — register the xlean kernelspec under /root/.local so
# JupyterLab finds it, then patch `LEAN_PATH` + `PATH` into the spec
# so notebook cells can `import Display` and so `bv_decide` can spawn
# the cadical bundled with elan.
RUN bash scripts/install-kernelspec.sh --user
RUN python3 -c "import json,pathlib; \
p=pathlib.Path('/root/.local/share/jupyter/kernels/xlean/kernel.json'); \
spec=json.loads(p.read_text()); \
env=spec.get('env',{}); \
env['LEAN_PATH']='/opt/xeus-lean/.lake/build/lib/lean'; \
env['PATH']='/root/.elan/bin:/root/.elan/toolchains/leanprover--lean4---v4.28.0/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'; \
spec['env']=env; \
p.write_text(json.dumps(spec,indent=2))"

# Hard-fail if the kernel didn't register.
RUN jupyter kernelspec list | grep -q '^\s*xlean\s' \
      || { echo 'ERROR: xlean kernel did not register with Jupyter.' >&2; exit 1; }

# `xlean-convert` writes notebooks whose `metadata.kernelspec` is
# `{name: "xeus-lean", language: "lean4", display_name: "Lean 4"}`.
# The kernelspec the upstream `install-kernelspec.sh` lays down is
# named `xlean` and uses `language: "lean"`, which makes JupyterLab
# pop a "Select Kernel" dialog every time the user runs a cell —
# the metadata fields don't match up exactly.
#
# Fix: clone the working `xlean` kernelspec to `xeus-lean` and
# rewrite `language` so all three identifying fields (name,
# language, display_name) match what xlean-convert wrote.
RUN cp -r /root/.local/share/jupyter/kernels/xlean \
          /root/.local/share/jupyter/kernels/xeus-lean && \
    python3 -c "import json,pathlib; \
p=pathlib.Path('/root/.local/share/jupyter/kernels/xeus-lean/kernel.json'); \
spec=json.loads(p.read_text()); \
spec['display_name']='Lean 4'; \
spec['language']='lean4'; \
p.write_text(json.dumps(spec,indent=2))"

# Bundle a JupyterLab settings override that flips the default
# behaviour of "close notebook tab" from "leave kernel running" to
# "close and shut down kernel".  This is a workaround for a
# reproducible deadlock: when JupyterLab spawns a second xlean
# process for a different connection file while the first is still
# alive, the new process's main thread blocks at
# `futex_wait_queue` (Lean runtime mutex) and never reaches
# kernelLoop.  Reproduces ~80% of the time via Playwright
# (tests/e2e/wdb-hang.spec.ts), in BOTH wdb (ch03→ch01) and
# non-wdb (ch02→ch01) navigation paths — i.e. the wdb session is
# incidental, the trigger is "two xlean processes coexist
# briefly."
#
# Setting `kernelShutdown=true` makes JupyterLab call the kernel's
# shutdown_request when its only viewing tab closes, so the
# previous chapter's kernel is gone before the next chapter's
# spawn.  Tutorial readers still need to actively close the tab
# (we document this in docs/tutorial/README.md), but at least the
# default "closed tabs orphan their kernels" behaviour is fixed.
RUN mkdir -p /opt/venv/share/jupyter/lab/settings && \
    python3 -c "import json,pathlib; \
p=pathlib.Path('/opt/venv/share/jupyter/lab/settings/overrides.json'); \
overrides={'@jupyterlab/notebook-extension:tracker': {'kernelShutdown': True}}; \
p.write_text(json.dumps(overrides,indent=2))"

# Smoke-test the kernel inside the image so a broken build fails the
# `docker build` rather than silently shipping.
RUN python3 scripts/smoke-test-native.py

# -----------------------------------------------------------------
# Stage 5 — Sparkle source + warmed Lake build cache.
# -----------------------------------------------------------------
FROM xeus-lean AS sparkle

WORKDIR /workspace/sparkle

# Copy ONLY what the tutorial image actually needs, in two layers:
#
#   (a) Lake metadata + extern-lib C sources — small, slow-changing.
#       This layer is cached aggressively across rebuilds: changes
#       to Sparkle source code don't invalidate it.
#   (b) Lean source code (Sparkle library + tutorial chapter material).
#       Larger, faster-changing.
#
# What we DON'T copy (vs. the previous `COPY . …`):
#   - .lake/                         (rebuilt by `lake build` here)
#   - .git/                          (not needed at runtime)
#   - venv/, hw/, fpga/, bench/      (host-only artefacts)
#   - verilator/, firmware/, linux-patches/
#                                    (RTL/firmware build, not used by tutorial)
#   - Tests/                         (not in the tutorial build graph)
#   - Examples/, IP/, Tools/         (other lean_libs the lakefile
#                                    declares but `lake build
#                                    TutorialNotebooks Display` does
#                                    not descend into)
#
# Together these prune the build context from ~9 GB down to a few
# MB and make the COPY layers stable across most edits.

# (a) Lake configuration + extern-lib C sources.
COPY lakefile.lean lake-manifest.json lean-toolchain Main.lean ./
COPY c_src ./c_src

# (a-deps) Pre-fetch every Lake dependency listed in the manifest
# (LSpec, doc-gen4, MD4Lean, BibtexQuery, UnicodeBasic, Cli,
# leansqlite, …) BEFORE copying any Sparkle source.  This isolates
# the slow git-clone phase into its own cache layer that's only
# invalidated when `lakefile.lean` or `lake-manifest.json`
# themselves change — editing Sparkle.lean or a chapter
# Markdown file no longer redownloads ~50 MB of dep sources.
#
# `lake update` is the lake-blessed way to do this; it reads the
# manifest, clones missing packages into `.lake/packages/`, and
# rewrites `lean-toolchain` if any dep requires a newer toolchain.
# We snapshot the toolchain pin before update and restore it
# after, for the same reason as the main build step below
# (xlean must keep matching the v4.28.0 sysroot it was built
# against; an automatic bump to v4.30.0-rc2 breaks the kernel).
RUN set -eux; \
    cp lean-toolchain /tmp/lean-toolchain.pinned; \
    lake update; \
    cp /tmp/lean-toolchain.pinned lean-toolchain

# (b) Lean source — Sparkle library + tutorial material.
#     `Tools/` carries the SystemVerilog frontend (verilog! / sim!
#     / Tools.SVParser.parse) that Ch 5's "Reading existing
#     Verilog" sections rely on.
COPY Sparkle ./Sparkle
COPY Sparkle.lean ./Sparkle.lean
COPY Tools ./Tools
COPY docs/tutorial ./docs/tutorial
COPY tutorial-extended ./tutorial-extended

# (c) Generate the tutorial chapters from Markdown source, then
# pre-build the tutorial library so the first `lake build` inside
# the running container is a no-op.  This makes `docker run` →
# JupyterLab → first cell ≪ 10 seconds.  `lake update` is NOT
# rerun here — deps are already on disk from layer (a-deps).
RUN set -eux; \
    bash docs/tutorial/build-from-md.sh; \
    lake build TutorialNotebooks Display

# Inject the Sparkle build cache (and every dep package's cache) into
# the xlean kernel's `LEAN_PATH`.  Without this, `import Sparkle` from
# a notebook cell fails with "unknown module prefix 'Sparkle'", because
# the kernel.json that scripts/install-kernelspec.sh wrote only points
# at xeus-lean's own oleans.
RUN python3 - <<'PY'
import json, os, subprocess, pathlib

# Ask `lake env` what the full LEAN_PATH should be; this picks up
# every transitive package (MD4Lean, BibtexQuery, UnicodeBasic, Cli,
# leansqlite, doc-gen4, LSpec, plus Sparkle itself).
out = subprocess.check_output(
    ['lake', 'env', 'env'], cwd='/workspace/sparkle'
).decode()
sparkle_lean_path = next(
    line.split('=', 1)[1] for line in out.splitlines()
    if line.startswith('LEAN_PATH=')
)

# Patch BOTH kernelspec copies — `xlean` AND `xeus-lean`. The latter
# is what tutorial notebook metadata.kernelspec.name points at, and
# it was copied in stage 4c BEFORE this stage's Sparkle paths were
# available, so it ships with only `/opt/xeus-lean/.lake/build/lib/lean`
# and any `import Sparkle.*` from a notebook cell fails with
# "unknown namespace `Sparkle.Core.Domain`".
#
# Both Sparkle and xeus-lean build a `Display.olean`: Sparkle's
# `docs/tutorial/Display.lean` is a small offline shim that
# stubs out `Display.{verilog, blockDiagram, writeWdb,
# waveformFromWdb, …}` so plain `lake build` outside JupyterLab
# typechecks; xeus-lean's is the real implementation that
# actually renders SVG, writes the wdb file, etc.
#
# Lean searches LEAN_PATH in forward order (first match wins),
# so we put xeus-lean's path FIRST.  Inside the running kernel
# `import Display` then resolves to the real one — `writeWdb`
# actually writes a file, `blockDiagram` actually emits SVG —
# instead of hitting the shim's no-ops.  Sparkle's own
# `Sparkle.Display.*` modules live under a different namespace
# and are unaffected.
full_lean_path = (
    '/opt/xeus-lean/.lake/build/lib/lean:' + sparkle_lean_path
)
for spec_path in [
    '/root/.local/share/jupyter/kernels/xlean/kernel.json',
    '/root/.local/share/jupyter/kernels/xeus-lean/kernel.json',
]:
    p = pathlib.Path(spec_path)
    spec = json.loads(p.read_text())
    env = spec.setdefault('env', {})
    env['LEAN_PATH'] = full_lean_path
    p.write_text(json.dumps(spec, indent=2))
    print('Patched', spec_path)
print('LEAN_PATH:', full_lean_path)
PY

# -----------------------------------------------------------------
# Default command — JupyterLab on port 8888, no token, rooted at
# the tutorial notebooks directory.
# -----------------------------------------------------------------
EXPOSE 8888
CMD ["jupyter", "lab", \
     "--ip=0.0.0.0", \
     "--port=8888", \
     "--no-browser", \
     "--allow-root", \
     "--ServerApp.token=", \
     "--ServerApp.password=", \
     "--MultiKernelManager.default_kernel_name=xeus-lean", \
     "--MappingKernelManager.default_kernel_name=xeus-lean", \
     "--collaborative", \
     "--notebook-dir=/workspace/sparkle/docs/tutorial/Notebooks/Gen/notebooks"]
