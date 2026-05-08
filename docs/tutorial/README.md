# Sparkle Tutorial

A 12-chapter beginner course on writing, synthesising, and proving
hardware in Sparkle.

## Layout

```
docs/tutorial/
├── md/                           ← MASTER (.md, edit here)
│   └── Ch??_*.md                 ← 12 chapters
├── Notebooks/                    ← lake_lib srcDir
│   ├── Gen/                      ← gitignored, regenerated from md/
│   │   ├── Ch??_*.lean           ← lake build target
│   │   └── notebooks/ch*.ipynb   ← JupyterLab
│   ├── Solutions/                ← hand-written reference proofs
│   │   └── Ch*.lean
│   └── DisplayShim.lean          ← portable Display.* fallback
├── Notebooks.lean                ← lib root (manual import list)
├── build-from-md.sh              ← `xlean-convert` driver
├── images/
└── README.md                     ← this file
```

Edit chapter content in [`md/`](md/).  Run
[`build-from-md.sh`](build-from-md.sh) to regenerate the
`Notebooks/Gen/` artefacts; CI and the Docker image do this
automatically.

## Chapters

| # | Title | Markdown master |
|---|---|---|
| 0 | Setup | [`md/Ch00_Setup.md`](md/Ch00_Setup.md) |
| 1 | Lean 4 for HDL Authors | [`md/Ch01_LeanForHdl.md`](md/Ch01_LeanForHdl.md) |
| 1b | Your First Sparkle Project | [`md/Ch01b_YourFirstProject.md`](md/Ch01b_YourFirstProject.md) |
| 2 | Combinational Circuits | [`md/Ch02_Combinational.md`](md/Ch02_Combinational.md) |
| 3 | Sequential Circuits | [`md/Ch03_Sequential.md`](md/Ch03_Sequential.md) |
| 4 | Modules and Composition | [`md/Ch04_Modules.md`](md/Ch04_Modules.md) |
| 5 | Verilog Generation | [`md/Ch05_Verilog.md`](md/Ch05_Verilog.md) |
| 6 | Proofs: LTL Invariants | [`md/Ch06_LTL.md`](md/Ch06_LTL.md) |
| 7 | Proofs: Equivalence Checking | [`md/Ch07_Equivalence.md`](md/Ch07_Equivalence.md) |
| 8 | Netlist Generation with Yosys | [`md/Ch08_Yosys.md`](md/Ch08_Yosys.md) |
| 8b | Three Ways to Simulate, One Interface (pure-Lean / JIT / Verilator) | [`md/Ch08b_Simulation.md`](md/Ch08b_Simulation.md) |
| 9 | FPGA Bring-Up | [`md/Ch09_FPGA.md`](md/Ch09_FPGA.md) |
| 10 | Sparkle Architecture | [`md/Ch10_Architecture.md`](md/Ch10_Architecture.md) |

## How to run

### Docker (recommended)

The Sparkle tutorial Docker image ships everything pre-installed:
Lean, Lake, xeus-lean, JupyterLab, yosys, nextpnr-ice40,
nextpnr-ecp5, icestorm, and prjtrellis.

```bash
docker run --rm -p 8888:8888 ghcr.io/verilean/sparkle-tutorial:latest
```

Open `http://localhost:8888` in your browser.  See
[`docker/tutorial/README.md`](../../docker/tutorial/README.md).

### Local

```bash
git clone https://github.com/Verilean/sparkle.git
cd sparkle

# 1. Build xlean-convert from upstream xeus-lean.
git clone https://github.com/Verilean/xeus-lean /tmp/xeus-lean
(cd /tmp/xeus-lean && lake build xlean-convert)
export PATH="/tmp/xeus-lean/.lake/build/bin:$PATH"

# 2. Regenerate Notebooks/Gen/ from md/.
bash docs/tutorial/build-from-md.sh

# 3. Typecheck every code cell.
lake build TutorialNotebooks

# 4. (optional) launch JupyterLab to actually run the cells.
jupyter lab docs/tutorial/Notebooks/Gen/notebooks/
```

## Authoring guide

Edit a chapter by editing its `md/Ch??_*.md` file.

Cell-format conventions:

- ` ```lean ` fences become executable code cells.
- ` ```text ` (or any other tag, like ` ```bash `) stays as
  illustrative content inside the surrounding Markdown cell.
- Plain Markdown is rendered as-is.

See [`md/README.md`](md/README.md) for the full conventions and
the synthesis-safety rules every ` ```lean ` cell must follow.

## CI

`.github/workflows/build.yml` defines a `tutorial-notebooks` job
that builds `xlean-convert` from upstream xeus-lean, runs
`build-from-md.sh`, and then `lake build TutorialNotebooks`.  Any
chapter whose code cells stop typechecking will fail CI.
