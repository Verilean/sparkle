/-
  Hardware-module / inline attributes for the synthesizer.

  By default the Sparkle elaborator **inlines** every Lean function
  call it encounters in a `Signal` graph: the call is unfolded into
  its body and translated as part of the caller's netlist.  That
  keeps the generated Verilog flat — no spurious sub-module per
  alias-style helper — which is what most users want when sketching
  combinational logic.

  Two attributes change that default:

    @[hardware_module]   — opt INTO emitting a sub-module instance.
                           Use it for self-contained components you
                           want to see as their own Verilog
                           `module foo (...)` block: a CPU, an
                           ALU you'll re-use, an arbiter, etc.
                           Downstream tools (P&R, OOC synth,
                           hierarchical STA) can then treat the
                           module as an independent compile unit.

    @[inline_hardware]   — opt OUT of any future synthesis
                           heuristic that would auto-promote a
                           definition to a module.  This is the
                           "I really do mean inline, do not change
                           your mind" hint.  Today it's a no-op
                           because the default is already inline,
                           but it documents intent and stays
                           binding if the default ever flips back.

  Both attributes carry no payload; they are simple presence flags.
-/
import Lean

namespace Sparkle.Compiler

open Lean

/-- `@[hardware_module]` — emit a Verilog sub-module for this
    definition instead of inlining its body. -/
initialize hardwareModuleAttr : TagAttribute ←
  registerTagAttribute `hardware_module
    "Promote this definition to its own Verilog sub-module during \
     hardware synthesis.  The caller emits a `inst_<name>` instance \
     and the body becomes a separate `module <name> (...)` block, \
     preserving the user-authored hierarchy.  Without this attribute \
     the synthesizer inlines the call into its caller (the default)."

/-- `@[inline_hardware]` — historical alias for "always inline".
    Kept for backwards compatibility with code authored when the
    default was the opposite.  Today the default is already inline,
    so this attribute documents intent without changing behaviour. -/
initialize inlineHardwareAttr : TagAttribute ←
  registerTagAttribute `inline_hardware
    "Inline this definition into the caller during hardware synthesis. \
     This is the default for every definition; the attribute is kept \
     as a self-documenting hint that the author has thought about \
     the boundary and decided NOT to promote it to a sub-module."

/-- True iff `name` is tagged `@[hardware_module]`. -/
def isHardwareModule (env : Environment) (name : Name) : Bool :=
  hardwareModuleAttr.hasTag env name

/-- True iff `name` is tagged `@[inline_hardware]`. -/
def isInlineHardware (env : Environment) (name : Name) : Bool :=
  inlineHardwareAttr.hasTag env name

end Sparkle.Compiler
