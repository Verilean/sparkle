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

namespace Sparkle.Display.Mime

/-- ASCII Escape (0x1B) — opens / closes a MIME block. -/
private def esc : Char := Char.ofNat 0x1B

/-- ASCII Record Separator (0x1E) — separates the MIME type from
    the payload, and terminates the closing marker. -/
private def rs : Char := Char.ofNat 0x1E

/-- Build the wire-format payload as a string.  Pure: no IO. -/
def mkMarker (mime content : String) : String :=
  s!"{esc}MIME:{mime}{rs}{content}{esc}/MIME{rs}"

/-- Emit a MIME-tagged payload to stdout.  Use from `def main : IO`
    or from `#eval` cells.  Inside an `elab` command prefer
    `emitFromCommand` which goes through Lean's message log. -/
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

end Sparkle.Display.Mime
