import Lean

/-!
# Display shim — portable wrapper for xeus-lean's `Display.*` helpers

The waveform / block-diagram / VCD / `.wdb` / Highlight.js helpers
used in the course (`Display.waveform`, `Display.boolWave`,
`Display.verilog`, `Display.blockDiagram`, `Display.writeWdb`,
`Display.waveformFromWdb`, …) are part of the **xeus-lean** runtime,
not of Sparkle proper.  When a chapter is built with plain
`lake build` outside the xeus-lean kernel, those helpers aren't on
the import path and the build fails.

This shim provides **identical names in the `Display` namespace**
that emit the same MIME-marker wire format xeus-lean parses.  The
markers travel through stdout (`IO.println`) and are picked up by
the kernel; in a headless `lake build` they show up as plain text
output, which is fine.

When xeus-lean's real `Display` library is on the path it takes
precedence (the chapter `import`s it explicitly).  This shim is the
fallback for offline `lake build` typecheck coverage.

## Marker format

```
\x1bMIME:<mime-type>\x1e<content>\x1b/MIME\x1e
```

- `\x1b` (ESC, 0x1B) = sentinel
- `\x1e` (RS, 0x1E)  = separator

xeus-lean's REPL preserves the ESC/RS bytes through stdout, parses
the markers, and emits a Jupyter `display_data` payload.
-/

namespace Display

private def esc : String := String.mk [Char.ofNat 0x1B]
private def rs  : String := String.mk [Char.ofNat 0x1E]

/-- Emit a `text/html` payload. -/
def html (content : String) : IO Unit :=
  IO.println s!"{esc}MIME:text/html{rs}{content}{esc}/MIME{rs}"

/-- Emit an `image/svg+xml` payload. -/
def svg (content : String) : IO Unit :=
  IO.println s!"{esc}MIME:image/svg+xml{rs}{content}{esc}/MIME{rs}"

/-- Emit a `text/markdown` payload. -/
def markdown (content : String) : IO Unit :=
  IO.println s!"{esc}MIME:text/markdown{rs}{content}{esc}/MIME{rs}"

/-- Render a single-lane digital waveform as inline SVG.

Each sample in `samples` is one cycle.  `bits` is the bit-width of
the value (used to pick a sensible row height).  `rowH` is the row
height in pixels; `tickW` is the width of one cycle in pixels. -/
def waveform (name : String) (samples : List Nat)
    (bits : Nat := 8) (rowH : Nat := 28) (tickW : Nat := 30) : IO Unit := do
  let n      := samples.length
  let width  := tickW * (n + 1)
  let height := rowH + 30
  let labelW := 90
  let mut path := s!"M {labelW},{rowH/2}"
  let mut idx := 0
  for _v in samples do
    let x  := labelW + idx * tickW
    let x2 := labelW + (idx+1) * tickW
    path := path ++ s!" L {x+4},{rowH/2} L {x2-4},{rowH/2}"
    idx := idx + 1
  let labels : String := Id.run do
    let mut acc := ""
    let mut i := 0
    for v in samples do
      let x := labelW + i * tickW + tickW / 2
      acc := acc ++ s!"<text x=\"{x}\" y=\"{rowH/2 + 4}\" font-size=\"10\" text-anchor=\"middle\">{v}</text>"
      i := i + 1
    pure acc
  let body := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width + labelW}\" height=\"{height}\" font-family=\"monospace\">"
            ++ s!"<text x=\"4\" y=\"{rowH/2 + 4}\" font-size=\"12\">{name}[{bits-1}:0]</text>"
            ++ s!"<path d=\"{path}\" fill=\"none\" stroke=\"#1f77b4\" stroke-width=\"1.5\"/>"
            ++ labels
            ++ "</svg>"
  svg body

/-- Render multiple Bool lanes as a stacked digital timing diagram. -/
def boolWave (lanes : List (String × List Bool))
    (rowH : Nat := 24) (tickW : Nat := 24) : IO Unit := do
  let labelW := 90
  let nCycles := (lanes.map (·.2.length)).foldl Nat.max 0
  let width := labelW + tickW * (nCycles + 1)
  let height := rowH * lanes.length + 20
  let mut bodyAcc := ""
  let mut row := 0
  for (name, samples) in lanes do
    let yMid : Nat := row * rowH + rowH / 2 + 10
    let mut path := s!"M {labelW},{yMid}"
    let mut i := 0
    for b in samples do
      let x  := labelW + i * tickW
      let x2 := labelW + (i+1) * tickW
      let y := if b then yMid - rowH/3 else yMid + rowH/3
      path := path ++ s!" L {x+2},{y} L {x2-2},{y}"
      i := i + 1
    bodyAcc := bodyAcc
      ++ s!"<text x=\"4\" y=\"{yMid + 4}\" font-size=\"11\">{name}</text>"
      ++ s!"<path d=\"{path}\" fill=\"none\" stroke=\"#1f77b4\" stroke-width=\"1.5\"/>"
    row := row + 1
  let body := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{width}\" height=\"{height}\" font-family=\"monospace\">"
              ++ bodyAcc
              ++ "</svg>"
  svg body

/-- Render a SystemVerilog blob with Highlight.js-style HTML markup.
    The shim emits a plain `<pre><code>` block; the real xeus-lean
    `Display.verilog` adds Highlight.js classes that JupyterLab
    styles via a CDN-loaded theme. -/
def verilog (source : String) : IO Unit :=
  let escaped := source
    |>.replace "&" "&amp;"
    |>.replace "<" "&lt;"
    |>.replace ">" "&gt;"
  html s!"<pre><code class=\"language-systemverilog\">{escaped}</code></pre>"

/-! ## Block-diagram primitives (`Display.Diagram`) -/

namespace Diagram

/-- The kind of one node in a hardware block diagram. -/
inductive NodeKind
  | reg | mux | cloud | andG | orG | notG | adder
  | port | const | clk | gen
  deriving Repr, Inhabited

/-- The kind of one edge.  `bus n` carries an `n`-bit width label. -/
inductive EdgeKind
  | data
  | clock
  | bus (width : Nat)
  deriving Repr, Inhabited

instance : Inhabited EdgeKind := ⟨.data⟩

end Diagram

/-- One block in the diagram. -/
structure Diagram.Node where
  id     : String
  label  : String
  kind   : Diagram.NodeKind := .gen
  col    : Nat              := 0
  row    : Nat              := 0
  inputs : Nat              := 1
  deriving Inhabited

/-- One wire in the diagram.  `dst` may be `nodeId` or `nodeId.k` to
    pick the k-th input pin of a multi-input node. -/
structure Diagram.Edge where
  src  : String
  dst  : String
  kind : Diagram.EdgeKind := .data
  deriving Inhabited

/-- A complete diagram.  See `Display.blockDiagram` for the renderer. -/
structure Diagram where
  nodes : List Diagram.Node := []
  edges : List Diagram.Edge := []
  deriving Inhabited

/-- Render a `Diagram` as inline SVG.

This shim renders only a *coarse* preview — coloured rectangles per
node, plain arrows per edge.  When xeus-lean's real `Display.blockDiagram`
is on the import path it takes over and produces the full
trapezoid-MUX / cloud / gate-shape art described in the demo. -/
def blockDiagram (d : Diagram) : IO Unit := do
  let cellW : Nat := 110
  let cellH : Nat := 70
  let pad   : Nat := 30
  let maxCol : Nat := d.nodes.foldl (fun m n => max m n.col) 0
  let maxRow : Nat := d.nodes.foldl (fun m n => max m n.row) 0
  let width  := pad * 2 + (maxCol + 1) * cellW
  let height := pad * 2 + (maxRow + 1) * cellH
  let cx (col : Nat) : Nat := pad + col * cellW + cellW / 2
  let cy (row : Nat) : Nat := pad + row * cellH + cellH / 2
  let nodeById (id : String) : Option Diagram.Node :=
    d.nodes.find? (·.id == id)
  let mut body := ""
  -- Edges first (so node rectangles overlay them).
  for e in d.edges do
    -- `dst` may be "id" or "id.k"; the shim ignores the .k suffix.
    let dstId := (e.dst.splitOn ".").head!
    match nodeById e.src, nodeById dstId with
    | some s, some t =>
      let stroke := match e.kind with
        | .data    => "#1f77b4"
        | .clock   => "#c2185b"
        | .bus _   => "#444"
      let dash := match e.kind with
        | .clock   => " stroke-dasharray=\"4,3\""
        | _        => ""
      let strokeW := match e.kind with
        | .bus _   => "3"
        | _        => "1.5"
      body := body ++
        s!"<line x1=\"{cx s.col}\" y1=\"{cy s.row}\" \
            x2=\"{cx t.col}\" y2=\"{cy t.row}\" \
            stroke=\"{stroke}\" stroke-width=\"{strokeW}\"{dash}/>"
      match e.kind with
      | .bus w =>
        body := body ++
          s!"<text x=\"{(cx s.col + cx t.col) / 2}\" \
              y=\"{(cy s.row + cy t.row) / 2 - 4}\" \
              font-size=\"10\" fill=\"#444\">{w} bit</text>"
      | _ => pure ()
    | _, _ => pure ()
  -- Nodes.
  for n in d.nodes do
    let fill := match n.kind with
      | .reg     => "#fff8c4"
      | .mux     => "#d6e9ff"
      | .cloud   => "#eee"
      | .andG    => "#cfe8d2"
      | .orG     => "#cfe8d2"
      | .notG    => "#cfe8d2"
      | .adder   => "#ffe1c4"
      | .port    => "#fce4ec"
      | .const   => "#f0f0ff"
      | .clk     => "#fce4ec"
      | .gen     => "#fff"
    body := body ++
      s!"<rect x=\"{cx n.col - 38}\" y=\"{cy n.row - 22}\" \
          width=\"76\" height=\"44\" \
          rx=\"6\" ry=\"6\" \
          fill=\"{fill}\" stroke=\"#333\" stroke-width=\"1\"/>"
    body := body ++
      s!"<text x=\"{cx n.col}\" y=\"{cy n.row + 4}\" \
          font-size=\"11\" font-family=\"monospace\" \
          text-anchor=\"middle\">{n.label}</text>"
  let payload := s!"<svg xmlns=\"http://www.w3.org/2000/svg\" \
      width=\"{width}\" height=\"{height}\">{body}</svg>"
  svg payload

/-! ## Long-trace `.wdb` waveform DB

`Display.WaveformSession.Lane` mirrors the structure used by xeus-lean's
real implementation.  The shim's `writeWdb` produces a tiny placeholder
file (just JSON, not the real zstd-block format) so chapter cells can
still call it without crashing under `lake build`; the real format
(zstd-compressed per-block sample tables, viewer streams the visible
window) lives in xeus-lean. -/

namespace WaveformSession

structure Lane where
  name   : String
  sample : Nat → Bool
  deriving Inhabited

end WaveformSession

/-- Write a long-trace waveform DB.  Real xeus-lean produces a
    `.wdb` (zstd-block compressed); the shim writes a tiny JSON
    placeholder so the call typechecks and the file exists. -/
def writeWdb (path : String) (lanes : List WaveformSession.Lane)
    (totalTicks : Nat) : IO Unit := do
  let lanesN := lanes.length
  let header :=
    "{\"shim\": true, \"lanes\": " ++ toString lanesN ++
    ", \"ticks\": " ++ toString totalTicks ++ "}"
  IO.FS.writeFile path header

/-- Open a `.wdb` and stream-render the visible window.  In the shim
    we just emit a `<pre>` confirming the path exists (or a 1-line
    error if it doesn't). -/
def waveformFromWdb (label : String) (path : String) : IO Unit := do
  let exists' ← System.FilePath.pathExists path
  if exists' then
    html s!"<pre>{label}: {path} (shim — open in xeus-lean for the full viewer)</pre>"
  else
    html s!"<pre>{label}: {path} not found</pre>"

/-- gzip-compress a string and write it.  Real xeus-lean has zlib
    bindings; the shim writes the raw text (you can re-gzip
    externally) so the call typechecks. -/
def writeGz (path : String) (content : String) : IO Unit :=
  IO.FS.writeFile path content

end Display

/-! ## Notebook helper commands

The `#mermaid`, `#help_x`, `#findDecl`, `#listNs`, `#sig`, `#bash`
commands ship with xeus-lean as small `elab` declarations.  Under
`lake build` (no xeus-lean) we provide **no-op stubs** that parse
the same syntax and silently emit nothing.  In the kernel the real
implementations take precedence. -/

open Lean Lean.Elab.Command

/-- Mermaid block-diagram sketch.  Stub: silently accepts any string. -/
elab "#mermaid " s:str : command =>
  liftCoreM <| (Display.html s!"<div class=\"mermaid\">{s.getString}</div>" : IO Unit)

/-- List notebook helper commands.  Stub. -/
elab "#help_x" : command => do
  liftCoreM <| (IO.println "(#help_x: real listing only in xeus-lean)" : IO Unit)

/-- Substring-search the active env.  Stub: prints the search args. -/
elab "#findDecl " kw1:str kw2:str pageStart:num pageSize:num : command =>
  liftCoreM <| (IO.println s!"(#findDecl shim: {kw1.getString} {kw2.getString} \
                              {pageStart.getNat} {pageSize.getNat})" : IO Unit)

/-- List all declarations under a namespace.  Stub. -/
elab "#listNs " id:ident : command =>
  liftCoreM <| (IO.println s!"(#listNs shim: {id.getId})" : IO Unit)

/-- Show one declaration's type signature.  Stub: in xeus-lean this
    pretty-prints the type; here we let `#check` do the real work
    when authors want it.  -/
elab "#sig " id:ident : command =>
  liftCoreM <| (IO.println s!"(#sig shim: see #check {id.getId})" : IO Unit)

/-- Run a shell one-liner and dump output.  Under `lake build` this
    is a hard-stub no-op (we don't shell out at compile time);
    xeus-lean replaces it with the real `bash -c` runner. -/
elab "#bash " s:str : command =>
  liftCoreM <| (IO.println s!"(#bash shim: would run `{s.getString}`)" : IO Unit)
