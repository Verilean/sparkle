/-
  Sparkle.Display.Mime — `text/html` / `image/svg+xml` etc. emitters.

  Sparkle is the HDL; xeus-lean is the JupyterLab kernel that hosts
  the chapter notebooks.  Their separation of concerns:

    Sparkle.Display.Mime     — emit a MIME-tagged payload to stdout.
                               Pure stream-of-bytes work; no kernel
                               dependency.
    xeus-lean Display.lean   — the same primitive, plus generic
                               `#html` / `#svg` / `#md` elabs that
                               wrap user strings in MIME markers
                               and route them to JupyterLab.

  We duplicate only the marker bytes here so Sparkle's renderers
  (Diagram, Waveform, …) can post their output without taking a
  hard dependency on xeus-lean.

  Wire format (matches xeus-lean's `extract_mime_payloads` parser):

      \x1bMIME:<mime-type>\x1e<content>\x1b/MIME\x1e

  ESC (0x1B) and RS (0x1E) are the only sentinels.  Neither byte
  appears in ordinary Lean output — including SystemVerilog,
  inline SVG, or Mermaid source — so they are safe to embed.

  Outside JupyterLab the markers are still emitted but are
  invisible in a terminal; the surrounding text reads cleanly.

  Currently the kernel only parses MIME markers out of `IO.println`
  output if it is captured via the Lean message log
  (`logInfo`-style).  Stdout-pipe support is on the xeus-lean
  roadmap; until that lands, prefer `emitFromCommand` (uses
  `logInfo`) over `emit` (uses `IO.println`) when you're inside
  an `elab` block.
-/

import Lean.Elab.Command

namespace Sparkle.Display.Mime
open Lean

/-- ASCII Escape (0x1B) — opens / closes a MIME block. -/
private def esc : Char := Char.ofNat 0x1B

/-- ASCII Record Separator (0x1E) — separates the MIME type from
    the payload, and terminates the closing marker. -/
private def rs : Char := Char.ofNat 0x1E

/-- Build the wire-format payload as a string.  Pure: no IO. -/
def mkMarker (mime content : String) : String :=
  s!"{esc}MIME:{mime}{rs}{content}{esc}/MIME{rs}"

/-- Emit a MIME-tagged payload to stdout.  Use from `def main : IO`
    or from `#eval` cells.  Inside an `elab` block prefer the
    `logEmit` family below, which routes through Lean's message log
    so xeus-lean's WASM kernel can pick it up (the WASM build does
    not capture stdout). -/
def emit (mime content : String) : IO Unit :=
  IO.println (mkMarker mime content)

/-- Convenience: emit a `text/html` payload. -/
def html (content : String) : IO Unit := emit "text/html" content

/-- Convenience: emit an `image/svg+xml` payload. -/
def svg (content : String) : IO Unit := emit "image/svg+xml" content

/-- Convenience: emit a `text/markdown` payload. -/
def markdown (content : String) : IO Unit := emit "text/markdown" content

/-- Convenience: emit a `text/latex` payload. -/
def latex (content : String) : IO Unit := emit "text/latex" content

-- ---------------------------------------------------------------------------
-- elab-friendly variants: route the MIME marker through Lean's message log.
--
-- xeus-lean's native kernel captures stdout via a dup2 pipe in xeus_ffi.cpp,
-- so `IO.println` (used by `emit` above) carries MIME markers all the way
-- back to JupyterLab.  The WASM kernel can't do that — stdout there goes to
-- the browser DevTools console, not to the cell.  The WASM xinterpreter
-- only parses MIME markers out of REPL info messages (the `logInfo` channel).
--
-- The functions below emit via `logInfo`, so the same code path works on
-- native AND in the browser without needing dup2.  Use these inside any
-- `elab` block — `#showDiagram`, `#showDesign`, etc.
-- ---------------------------------------------------------------------------

/-- Emit a MIME-tagged payload via Lean's info-message log.  Works
    from any monad that supports `logInfo` (CommandElabM, TermElabM,
    MetaM, …).  Required for `elab` blocks running under the WASM
    kernel, which doesn't have stdout capture. -/
def logEmit [Monad m] [MonadLog m] [MonadOptions m] [AddMessageContext m]
    (mime content : String) : m Unit :=
  logInfo (mkMarker mime content)

/-- elab-friendly variant of `svg`. -/
def logSvg [Monad m] [MonadLog m] [MonadOptions m] [AddMessageContext m]
    (content : String) : m Unit :=
  logEmit "image/svg+xml" content

/-- elab-friendly variant of `html`. -/
def logHtml [Monad m] [MonadLog m] [MonadOptions m] [AddMessageContext m]
    (content : String) : m Unit :=
  logEmit "text/html" content

/-- elab-friendly variant of `markdown`. -/
def logMarkdown [Monad m] [MonadLog m] [MonadOptions m] [AddMessageContext m]
    (content : String) : m Unit :=
  logEmit "text/markdown" content

/-- elab-friendly variant of `latex`. -/
def logLatex [Monad m] [MonadLog m] [MonadOptions m] [AddMessageContext m]
    (content : String) : m Unit :=
  logEmit "text/latex" content

end Sparkle.Display.Mime
