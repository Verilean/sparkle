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

# Native dependencies xeus-lean's CMake build needs.  Without these
# `bash build.sh` produces an obscure "could not find xeus" or
# "could not find nlohmann_json" error; pre-installing them moves
# the failure (if any) earlier in the build log.
RUN apt-get update && apt-get install -y --no-install-recommends \
        libzmq3-dev \
        libssl-dev \
        nlohmann-json3-dev \
        uuid-dev \
        libxeus-dev \
        libxeus-zmq-dev \
    && rm -rf /var/lib/apt/lists/* \
    || true   # not all of these are guaranteed to exist on every Ubuntu mirror; build.sh will tell us

ARG BUILD_XEUS_LEAN=1
WORKDIR /opt
RUN git clone --depth 1 https://github.com/Verilean/xeus-lean.git && \
    cd xeus-lean && \
    lake build xlean-convert && \
    install -m 0755 .lake/build/bin/xlean-convert /usr/local/bin/xlean-convert

# Build the xeus-lean kernel.  HARD-FAIL if it doesn't produce a
# kernel.json that `jupyter kernelspec list` can pick up — a
# silent fallback would yield a JupyterLab where every cell hits
# "Kernel xlean not found".
RUN if [ "${BUILD_XEUS_LEAN}" = "1" ]; then \
      cd /opt/xeus-lean && bash build.sh; \
      # Register the kernelspec system-wide so `jupyter kernelspec list`
      # (run as any user) sees it.
      KSPEC=$(find /opt/xeus-lean -name kernel.json -path '*kernels/xlean*' | head -n1); \
      if [ -z "$KSPEC" ]; then \
        echo "ERROR: xeus-lean built but no kernels/xlean/kernel.json was produced." >&2; \
        exit 1; \
      fi; \
      KDIR=$(dirname "$KSPEC"); \
      install -d /usr/local/share/jupyter/kernels/xlean; \
      cp -r "$KDIR"/. /usr/local/share/jupyter/kernels/xlean/; \
      jupyter kernelspec list | grep -q '^\s*xlean\s' || \
        { echo "ERROR: xlean kernel did not register with Jupyter." >&2; exit 1; }; \
    fi

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
RUN set -eux; \
    lake update; \
    bash docs/tutorial/build-from-md.sh; \
    lake build TutorialNotebooks Display

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
     "--NotebookApp.token=", \
     "--NotebookApp.password=", \
     "--notebook-dir=/workspace/sparkle/docs/tutorial/Notebooks/Gen/notebooks"]
