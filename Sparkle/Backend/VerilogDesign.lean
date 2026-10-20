/-
  The design writer of the hierarchical commands
  (`#synthesizeVerilogDesign`, `#writeVerilogDesign`, `#writeDesign`).

  `toVerilogDesign` (Sparkle/Backend/Verilog.lean) prints every module of a
  design through `Optimize.optimizeModule` directly: no check, no fallback.
  The proved design endpoints speak about another artifact: the TOP module
  through `OptCheck.checkedOptimize` (what the single-module commands print,
  `verilogOf`), and every other module of the design AS IT IS.

  `toVerilogDesignChecked` prints exactly that artifact (`designArtifact`),
  in the design's module order, each module by `emitModule`, joined as
  `toVerilogDesign` joins them.
-/

import Sparkle.Backend.Verilog
import Sparkle.IR.RefineCheck

namespace Sparkle.Backend.Verilog

/-- The modules the design writer prints, in the design's order: the module
    named `d.topModule` through the result-checked optimizer, every other
    module unchanged. (A child comes from its own full entry — zero-width
    cleanup and checked merge already applied; it is NOT optimized here.) -/
def designArtifact (d : Sparkle.IR.AST.Design) : List Sparkle.IR.AST.Module :=
  d.modules.map fun m =>
    if m.name == d.topModule then Sparkle.IR.OptCheck.checkedOptimize m else m

/-- Convert a full design to SystemVerilog: the emitted text of each module
    of `designArtifact d`, joined by a newline. -/
def toVerilogDesignChecked (d : Sparkle.IR.AST.Design) : String :=
  String.intercalate "\n" ((designArtifact d).map emitModule)

/-- VARIANT, NOT USED BY ANY COMMAND: every module through the
    result-checked optimizer (the children too). No endpoint speaks about
    this artifact yet. -/
def designArtifactKids (d : Sparkle.IR.AST.Design) : List Sparkle.IR.AST.Module :=
  d.modules.map Sparkle.IR.OptCheck.checkedOptimize

/-- VARIANT, NOT USED BY ANY COMMAND: the text of `designArtifactKids`. -/
def toVerilogDesignCheckedKids (d : Sparkle.IR.AST.Design) : String :=
  String.intercalate "\n" ((designArtifactKids d).map emitModule)

end Sparkle.Backend.Verilog
