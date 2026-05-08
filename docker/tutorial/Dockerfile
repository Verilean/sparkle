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
RUN python3 -m venv /opt/venv \
    && /opt/venv/bin/pip install --no-cache-dir --upgrade pip \
    && /opt/venv/bin/pip install --no-cache-dir \
        jupyterlab \
        jupytext \
        nbconvert \
        notebook

ENV PATH="/opt/venv/bin:${PATH}"

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
RUN git clone --depth 1 https://github.com/Verilean/xeus-lean.git

# Stage 4a — build the C++ FFI library that xlean links against.
WORKDIR /opt/xeus-lean
RUN cmake -S . -B build-cmake \
      -DCMAKE_C_COMPILER=clang \
      -DCMAKE_CXX_COMPILER=clang++ \
      -DCMAKE_CXX_FLAGS="-stdlib=libc++" && \
    cmake --build build-cmake -j

# Linux glibc C23 shim (clang -> __isoc23_strtoull -> Lean's older glibc).
RUN leanc -c src/glibc_isoc23_compat.c -o build-cmake/glibc_isoc23_compat.o

# Stage 4b — build the Lean side: xlean kernel binary, xlean-convert
# CLI, and the Display library oleans.
RUN lake build xlean Display CommBus xlean-convert

# Install both binaries onto PATH so kernel.json and tutorial scripts
# can find them by name.
RUN install -m 0755 .lake/build/bin/xlean         /usr/local/bin/xlean && \
    install -m 0755 .lake/build/bin/xlean-convert /usr/local/bin/xlean-convert

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

# Smoke-test the kernel inside the image so a broken build fails the
# `docker build` rather than silently shipping.
RUN python3 scripts/smoke-test-native.py

# -----------------------------------------------------------------
# Stage 5 — Sparkle source + warmed Lake build cache.
# -----------------------------------------------------------------
FROM xeus-lean AS sparkle

WORKDIR /workspace
COPY . /workspace/sparkle

# Generate the tutorial chapters from Markdown source, then
# pre-build the tutorial library so the first `lake build` inside
# the running container is a no-op.  This makes `docker run` →
# JupyterLab → first cell ≪ 10 seconds.
WORKDIR /workspace/sparkle
# `lake update` re-resolves dependency manifests and, as a side
# effect, rewrites `lean-toolchain` to the highest version any
# dependency requires.  Sparkle pins itself to `v4.28.0` and
# xlean was built against the same; if `lean-toolchain` flips to
# something newer (e.g. v4.30.0-rc2), elan auto-installs that
# toolchain and xlean later sees a sysroot whose `Init.olean` it
# cannot read ("incompatible header").  We snapshot the file
# before `lake update` and restore it afterwards.
RUN set -eux; \
    cp lean-toolchain /tmp/lean-toolchain.pinned; \
    lake update; \
    cp /tmp/lean-toolchain.pinned lean-toolchain; \
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

# Patch BOTH kernelspec copies — `xlean` AND `xeus-lean`. The latter is
# what tutorial notebook metadata.kernelspec.name points at, and it was
# copied in stage 4c BEFORE this stage's Sparkle paths were available,
# so it ships with only `/opt/xeus-lean/.lake/build/lib/lean` and any
# `import Sparkle.*` from a notebook cell fails with
# "unknown namespace `Sparkle.Core.Domain`".
#
# IMPORTANT: Lean searches LEAN_PATH in REVERSE order — later entries win.
# Sparkle's own build cache contains a `Display.olean` (the offline shim
# from `docs/tutorial/Display.lean`) that shadows xeus-lean's full
# `Display.Diagram.{Node,Edge}` API.  Put xeus-lean LAST so its Display
# wins lookup; chapter notebooks need the real one.
full_lean_path = (
    sparkle_lean_path + ':/opt/xeus-lean/.lake/build/lib/lean'
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
     "--notebook-dir=/workspace/sparkle/docs/tutorial/Notebooks/Gen/notebooks"]
