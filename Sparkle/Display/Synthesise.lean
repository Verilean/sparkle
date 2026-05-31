/-
  Sparkle.Display.Synthesise — bridge from a Lean `def` straight
  to a rendered block diagram, no hand-written IR required.

  `#showDiagram <ident>` looks the identifier up in the
  environment, runs the Sparkle synthesiser to produce its
  `IR.AST.Module`, lifts that into a `Diagram` via
  `Sparkle.Display.Diagram.fromModule`, and emits it as an
  inline SVG in the current Jupyter cell.

  Companion: `#showDesign <ident>` does the same for a
  hierarchical `IR.AST.Design`, drawing one diagram per module
  in the design (parent first, then every transitive
  `@[hardware_module]` child).

  This module sits above `Sparkle.Compiler.Elab` (so it can call
  `synthesizeCombinational` / `synthesizeHierarchical`) and
  `Sparkle.Display.Diagram` (so it can lift the IR into a
  Diagram).  The dependency arrow is one-way — neither Compiler
  nor Display.Diagram imports anything from here, so the rest
  of Sparkle still builds without the diagram pipeline.

  Wire format: SVG is shipped through `Sparkle.Display.Mime.svg`,
  which writes the standard `\x1bMIME:image/svg+xml\x1e…\x1b/MIME\x1e`
  marker to stdout.  xeus-lean's kernel parses the marker out of
  the captured stdout pipe (see xeus-lean PR #7) and ships the
  payload to JupyterLab as `display_data`.  Outside Jupyter the
  ESC / RS bytes are invisible in a terminal and the surrounding
  text reads cleanly, so plain `lake env lean` runs without any
  extra noise.
-/
import Lean
import Sparkle.Compiler.Elab
import Sparkle.Display.Diagram
import Sparkle.Display.Mime

namespace Sparkle.Compiler.Elab

open Lean Lean.Elab Lean.Elab.Command
open Sparkle.Display.Diagram

/-- `#showDiagram <ident>` — synthesise the named definition and
    render the resulting top-level module as an inline SVG block
    diagram.

    ```
    def dff (d : Signal defaultDomain (BitVec 1))
        : Signal defaultDomain (BitVec 1) :=
      circuit do
        let q ← Signal.reg 0#1
        q <~ d
        return q

    #showDiagram dff
    ```

    No need to spell out the IR by hand: the same elaborator
    that powers `#synthesizeVerilog` produces the `IR.AST.Module`,
    `fromModule` lifts it into a `Diagram`, and the renderer
    paints it.

    Hierarchical designs (multiple `@[hardware_module]` children)
    only show the *top* module here; use `#showDesign` for the
    full picture. -/
elab "#showDiagram" id:ident : command => do
  let declName ← liftCoreM do Lean.resolveGlobalConstNoOverload id
  liftTermElabM do
    let (module, _) ← synthesizeCombinational declName
    -- Use `logSvg`, not `svg`, so the MIME marker reaches the cell
    -- under both the native kernel (which captures stdout) AND the
    -- WASM kernel (which only sees REPL info messages).  See
    -- Sparkle/Display/Mime.lean for the rationale.
    Sparkle.Display.Mime.logSvg (toSvg (fromModule module))

/-- `#showDesign <ident>` — synthesise the named definition and
    render *every* module in the resulting `Design` (parent +
    every transitive `@[hardware_module]` child).  Each module
    is emitted as its own SVG marker, so JupyterLab shows them
    stacked vertically in the cell output. -/
elab "#showDesign" id:ident : command => do
  let declName ← liftCoreM do Lean.resolveGlobalConstNoOverload id
  liftTermElabM do
    let design ← synthesizeHierarchical declName
    for m in design.modules do
      Sparkle.Display.Mime.logSvg (toSvg (fromModule m))

end Sparkle.Compiler.Elab
