# Sparkle Tutorial — Docker image

A self-contained Docker image with everything the
[`docs/tutorial/`](../../docs/tutorial/) chapters need:

- **Lean 4** + Lake (toolchain matching `lean-toolchain`)
- **JupyterLab** + jupytext + nbconvert
- **xeus-lean** Jupyter kernel
- **Yosys** (synthesis), **nextpnr-ice40 / nextpnr-ecp5**
  (place-and-route), **icestorm / prjtrellis** (bitstream packing)
- **GTKWave** (waveform inspection)

## Quickstart

From a Sparkle repo checkout:

```bash
bash docker/tutorial/build.sh
bash docker/tutorial/run.sh
```

Then open `http://localhost:8888` in your browser.  Click any
chapter (`ch00-setup.ipynb`, `ch02-combinational.ipynb`, ...) and
run the cells — every code cell ships with the right kernel
already wired up.

## Image size

After all toolchains are installed the image is roughly **3–5 GB**.
Lean alone is ~1 GB; the FPGA toolchains (yosys + nextpnr +
icestorm + prjtrellis) add another ~2 GB.  This is the trade-off
for "everything works out of the box".

## What's bundled

| Tool                 | Used in        | Source              |
|----------------------|----------------|---------------------|
| Lean 4 (`v4.28.0`)   | every chapter  | elan                |
| Lake                 | every chapter  | bundled with Lean   |
| JupyterLab           | every chapter  | pip                 |
| nbconvert            | output filling | pip                 |
| xeus-lean kernel     | every chapter  | source build        |
| `xlean-convert`      | infra          | xeus-lean Lake exe  |
| yosys                | Ch 8, Ch 9     | apt (Ubuntu 24.04)  |
| nextpnr-ice40        | Ch 9           | apt                 |
| nextpnr-ecp5         | Ch 9           | apt                 |
| icestorm (icepack…)  | Ch 9           | apt                 |
| prjtrellis (ecppack) | Ch 9           | apt                 |
| GTKWave              | Ch 8           | apt                 |

`xlean-convert` is the pipeline that turns the canonical
`docs/tutorial/md/Ch*.md` chapter sources into the generated
`docs/tutorial/Notebooks/Gen/Ch*.lean` (for `lake build`) and
`docs/tutorial/Notebooks/Gen/notebooks/ch*.ipynb` (for
JupyterLab).  See [`docs/tutorial/build-from-md.sh`](../../docs/tutorial/build-from-md.sh)
for the wrapper.  Both generated trees are gitignored — they're
rebuilt every time the Dockerfile (or the user) runs the
wrapper.

## Customising

- **Different port** — `PORT=8080 bash docker/tutorial/run.sh`.
- **Persist your work** — bind-mount the repo into the container:
  `docker run --rm -it -p 8888:8888 -v "$(pwd):/workspace/sparkle" sparkle-tutorial:latest`.
- **Skip the xeus-lean build** — set `BUILD_XEUS_LEAN=0` in the
  Dockerfile and install xeus-lean externally (e.g. via mamba).

## Troubleshooting

- **Build is slow.**  Most of the time is in the `lake update +
  lake build TutorialNotebooks` step that warms the cache (~5–10
  minutes on a fast box).  Subsequent rebuilds reuse the cached
  Lake state.
- **xeus-lean kernel not registered.**  Inside the container:
  `jupyter kernelspec list` should show `xeus-lean`.  If not, the
  source build failed — check the build log; you can fall back to
  installing xeus-lean from a pre-built mamba package (see
  https://github.com/Verilean/xeus-lean for the canonical install
  path).
- **FPGA tools not found.**  Confirm with `which yosys
  nextpnr-ice40 ecpprog iceprog`.  Ubuntu 24.04 ships all of them
  in the main repo as of this writing.

## Publishing

The image is published to GHCR by `.github/workflows/docker-image.yml`
on tagged releases:

```bash
docker pull ghcr.io/verilean/sparkle-tutorial:latest
```
