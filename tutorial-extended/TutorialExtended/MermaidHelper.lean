/-
  Mermaid display helper for xeus-lean Jupyter notebooks.

  This file is intentionally **standalone** — it does NOT import
  the xeus-lean `Display` module (which lives in the xeus-lean
  repo, not Sparkle). Instead, it defines an `IO` action that
  produces the wire-format MIME marker that xeus-lean's
  interpreter recognizes. If you're running this file outside
  xeus-lean, the marker is just printed to stdout (no rendering).

  Wire format (must match xeus-lean's Display module):

      \x1bMIME:<mime-type>\x1e<content>\x1b/MIME\x1e

  See https://github.com/Verilean/xeus-lean/blob/main/src/Display.lean
  for the full Display module that xeus-lean ships with. The
  helper below is portable: it works in xeus-lean (renders as
  HTML/Markdown) and in plain `lake exe` (prints raw markers).

  ## Usage in a notebook

  ```lean
  import TutorialExtended.MermaidHelper
  open TutorialExtended.MermaidHelper

  #eval mermaid "flowchart LR
    A[Counter] --> B[Monitor]
    B --> C[(Alert)]"
  ```

  Or via the sugar command:

  ```lean
  #mermaid "flowchart LR
    A --> B --> C"
  ```
-/

namespace TutorialExtended.MermaidHelper

/-- Build the xeus-lean MIME marker for a given mime-type/content pair.

    The format is `\x1bMIME:<mime>\x1e<content>\x1b/MIME\x1e`. ESC
    (0x1B) and RS (0x1E) are used as sentinels because they don't
    appear in normal Lean output. -/
def mkMarker (mime : String) (content : String) : String :=
  let esc := Char.ofNat 0x1B
  let rs  := Char.ofNat 0x1E
  s!"{esc}MIME:{mime}{rs}{content}{esc}/MIME{rs}"

/-- Emit an HTML payload. xeus-lean renders it; otherwise it
    prints the raw marker to stdout (still valid for piping). -/
def html (content : String) : IO Unit :=
  IO.println (mkMarker "text/html" content)

/-- Emit a Markdown payload. -/
def markdown (content : String) : IO Unit :=
  IO.println (mkMarker "text/markdown" content)

/-- Emit an SVG payload. -/
def svg (content : String) : IO Unit :=
  IO.println (mkMarker "image/svg+xml" content)

/-- Wrap a Mermaid graph definition in the HTML scaffold that
    JupyterLite / xeus-lean WASM expects. The script tag bootstraps
    Mermaid.js from a CDN if the page hasn't loaded it yet. -/
def mermaidHTML (graph : String) : String :=
  let escaped := graph
    -- HTML escape — minimal: just &, <, >.
    |>.replace "&" "&amp;"
    |>.replace "<" "&lt;"
    |>.replace ">" "&gt;"
  -- Build the JS snippet without using interpolation braces, so we
  -- don't have to escape `{` / `}` in the string literal.
  let lcb := "{"
  let rcb := "}"
  let js := "(function() " ++ lcb ++ "\n" ++
    "  var ensureMermaid = function() " ++ lcb ++ "\n" ++
    "    if (window.mermaid) " ++ lcb ++ " window.mermaid.run(); return; " ++ rcb ++ "\n" ++
    "    var script = document.createElement('script');\n" ++
    "    script.src = 'https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.min.js';\n" ++
    "    script.onload = function() " ++ lcb ++ "\n" ++
    "      window.mermaid.initialize(" ++ lcb ++ " startOnLoad: false " ++ rcb ++ ");\n" ++
    "      window.mermaid.run();\n" ++
    "    " ++ rcb ++ ";\n" ++
    "    document.head.appendChild(script);\n" ++
    "  " ++ rcb ++ ";\n" ++
    "  ensureMermaid();\n" ++
    rcb ++ ")();"
  s!"<div class='mermaid'>{escaped}</div><script>{js}</script>"

/-- Top-level helper: render a Mermaid graph in a Jupyter notebook.

    ```
    #eval mermaid "flowchart LR
      A --> B"
    ```

    In Jupyter Lab 4+ / Notebook 7+ you can also just put the
    Mermaid block inside a `#md` Markdown cell and the renderer
    handles it natively — that's even simpler if you don't need
    the graph to be generated dynamically from Lean code. -/
def mermaid (graph : String) : IO Unit :=
  html (mermaidHTML graph)

/-- Sugar: a `#mermaid` command for cells that want a one-liner. -/
macro "#mermaid " s:str : command => `(#eval TutorialExtended.MermaidHelper.mermaid $s)

end TutorialExtended.MermaidHelper
