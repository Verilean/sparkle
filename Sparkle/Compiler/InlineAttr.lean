/-
  `@[inline_hardware]` — opt-in inline marker for the synthesizer.

  By default the Sparkle elaborator emits a sub-module instance for
  every Lean function call it encounters in a `Signal` graph.  This
  preserves user-authored module hierarchy in the generated Verilog,
  which downstream tools (place-and-route, OOC synthesis,
  floorplanning, hierarchical timing, etc.) need.

  A function tagged `@[inline_hardware]` is unfolded *into* the
  caller instead.  Use it for:

    - Sparkle's own primitive combinators (`Signal.map`,
      `Signal.mux`, BitVec arithmetic instances, `Signal.fst`,
      `Signal.snd`, …) that exist purely to compose a graph
      with no hardware boundary of their own.
    - User-side helpers small enough that a fresh module
      instance per call would just bloat the netlist.

  This module registers the attribute and exposes `isInlineHardware
  name` so the elaborator can branch on it.  The attribute carries
  no payload.
-/
import Lean

namespace Sparkle.Compiler

open Lean

/-- The environment-extension key.  We reuse the standard
    `TagAttribute` infrastructure (boolean per declaration). -/
initialize inlineHardwareAttr : TagAttribute ←
  registerTagAttribute `inline_hardware
    "Inline this definition into the caller during hardware synthesis \
     instead of emitting a sub-module instance.  Without this attribute \
     the synthesizer keeps the call as a Verilog `inst_<name>` so the \
     user-authored module hierarchy is preserved."

/-- True iff `name` is tagged `@[inline_hardware]` in the current
    environment. -/
def isInlineHardware (env : Environment) (name : Name) : Bool :=
  inlineHardwareAttr.hasTag env name

end Sparkle.Compiler
