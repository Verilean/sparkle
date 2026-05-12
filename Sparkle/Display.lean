/-
  Sparkle.Display — HDL-aware rendering for JupyterLab cells.

  The `Sparkle.Display` library is the home of HDL-specific
  rendering — block diagrams, waveforms, the `wdb` waveform
  database — that previously lived inside xeus-lean's
  `Display.lean`.  Splitting the renderers out of the kernel
  lets xeus-lean stay a thin MIME-plumbing + comm bus layer,
  and lets Sparkle ship rendering improvements (new node
  shapes, the IR → Diagram auto-layout, …) without a kernel
  rebuild.

  ## Modules

  * `Sparkle.Display.Mime`     — emit a MIME-tagged payload to
                                  stdout.  Wire format matches
                                  xeus-lean's `extract_mime_payloads`
                                  parser; outside JupyterLab the
                                  bytes are invisible in a terminal.
  * `Sparkle.Display.Diagram`  — `Diagram` structure (nodes /
                                  edges / kinds), an SVG renderer,
                                  and `fromModule` to lift a
                                  Sparkle `IR.AST.Module` into a
                                  diagram automatically.

  More to come: `Sparkle.Display.Waveform` (interactive waveform
  viewer, currently a `WaveformSession` over in xeus-lean) and
  `Sparkle.Display.Wdb` (compressed waveform-database serialiser /
  loader).  See `docs/Display_Migration_Plan.md` for the migration
  roadmap.
-/
import Sparkle.Display.Mime
import Sparkle.Display.Diagram
import Sparkle.Display.Synthesise
import Sparkle.Display.Interactive
