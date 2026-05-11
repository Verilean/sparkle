import Notebooks.Gen.Ch00_Setup
import Notebooks.Gen.Ch01_LeanForHdl
import Notebooks.Gen.Ch01b_YourFirstProject
import Notebooks.Gen.Ch02_Combinational
import Notebooks.Gen.Ch03_Sequential
import Notebooks.Gen.Ch04_Modules
import Notebooks.Gen.Ch05_Verilog
import Notebooks.Gen.Ch06_LTL
import Notebooks.Gen.Ch07_Equivalence
import Notebooks.Gen.Ch07b_FpQuantEquivalence
import Notebooks.Gen.Ch08_Yosys
import Notebooks.Gen.Ch08b_Simulation
import Notebooks.Gen.Ch09_FPGA
import Notebooks.Gen.Ch10_Architecture
import Display
import Notebooks.Solutions.Ch02
import Notebooks.Solutions.Ch03
import Notebooks.Solutions.Ch04
import Notebooks.Solutions.Ch06
import Notebooks.Solutions.Ch07

/-!
# Sparkle Tutorial Notebooks — library root

This file imports every chapter so a single

    lake build TutorialNotebooks

typechecks every code cell across the course.

The chapter sources are Markdown files in `docs/tutorial/md/`.
Run `bash docs/tutorial/build-from-md.sh` to regenerate the
`Notebooks/Gen/Ch*.lean` (lake build target) and
`Notebooks/Gen/notebooks/ch*.ipynb` (JupyterLab) artefacts; both
are gitignored.

Hand-written companion files (in this lib but not generated):
  - `docs/tutorial/Display.lean` — portable shim for xeus-lean's
    `Display.*` library (waveform / boolWave / blockDiagram /
    writeWdb / verilog / `#mermaid` / `#help_x` / etc.).  In the
    xeus-lean kernel the real Display library takes precedence.
  - `Notebooks/Solutions/Ch*.lean` — reference exercise solutions
-/
