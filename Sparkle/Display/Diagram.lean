/-
  Sparkle.Display.Diagram — structured block-diagram renderer.

  `Diagram` is a small intermediate language for "boxes connected
  by arrows": each `DiagNode` lives at a `(col, row)` cell on a
  conceptual grid, and each `DiagEdge` runs between two nodes.
  The renderer turns that into inline SVG that JupyterLab paints
  via the standard `image/svg+xml` MIME channel.

  Two ways to populate a diagram:

    1.  By hand — pick a `NodeKind` per box (port / reg / mux / …)
        and lay out the columns yourself.  Useful for one-off
        teaching figures (see Ch 3 of the tutorial).

    2.  Automatically — pass a Sparkle `IR.AST.Module` to
        `Sparkle.Display.Diagram.fromModule` and the elaborator
        builds the diagram for you: every `Stmt.register` becomes
        a `reg` box, every `Stmt.assign` whose RHS is a primitive
        becomes the matching gate (`adder` / `andG` / `mux` / …),
        edges follow `Expr.ref`s, and clock / reset wires get the
        `clock` edge style.  See `fromModule` below.

  This file deliberately has no `IO` side-effects: it produces
  *strings* (one big SVG document).  `Sparkle.Display.Mime.svg`
  ships them to the cell.

  History: an earlier version of this code lived in xeus-lean's
  `src/Display.lean` under the same `Display.Diagram` namespace.
  We're migrating HDL-specific renderers to Sparkle so xeus-lean
  can shrink to its core MIME-plumbing role.
-/
import Sparkle.IR.AST
import Sparkle.Display.Mime

namespace Sparkle.Display.Diagram

/-! ## Node and edge kinds -/

/-- The visual class of a diagram node.

    Each variant gets its own SVG art in `renderNode` below — a
    rectangle for a register, a trapezoid for a mux, a gate body
    for combinational primitives, etc.  Use `gen` for anything
    you don't have a dedicated shape for; it falls back to a
    plain box with the node's label. -/
inductive NodeKind
  | reg          -- D flip-flop (rectangle)
  | mux          -- multiplexer (trapezoid)
  | port         -- I/O port (rounded rectangle)
  | const        -- constant value (small rectangle)
  | clk          -- clock source (circle with crosshair)
  | adder        -- arithmetic adder (curved-back gate body)
  | andG         -- AND gate (D-shape)
  | orG          -- OR gate (curved-front)
  | notG         -- NOT gate (triangle + bubble)
  | cloud        -- "rest of the design" placeholder
  | gen          -- generic / fallback (plain rectangle)
  deriving Repr, Inhabited, BEq

/-- The visual class of an edge.

    `data` is the default — a thin arrow.  `clock` is dashed and
    terminates in a small triangle at the destination's clock
    pin.  `bus n` carries an `n`-bit width label and is drawn
    thicker. -/
inductive EdgeKind
  | data
  | clock
  | bus (width : Nat)
  deriving Repr, Inhabited, BEq

/-! ## Structures -/

/-- One block in the diagram.

    `inputs` lets a multi-input node (e.g. a 4:1 mux) declare
    how many distinct input pins it has on the left; edges can
    target a specific pin via `dst := "muxId.<index>"`. -/
structure DiagNode where
  id     : String
  label  : String
  kind   : NodeKind := .gen
  col    : Nat      := 0
  row    : Nat      := 0
  inputs : Nat      := 1
  deriving Inhabited

/-- One wire in the diagram.  `dst` is `nodeId` for a single-input
    node, or `nodeId.k` to target the k-th input pin of a
    multi-input node. -/
structure DiagEdge where
  src  : String
  dst  : String
  kind : EdgeKind := .data
  deriving Inhabited

/-- A complete diagram.  `blockDiagram` (below) renders it. -/
structure Diagram where
  nodes : List DiagNode := []
  edges : List DiagEdge := []
  deriving Inhabited

/-! ## SVG rendering -/

/-- Pixel size of one grid cell.  Used by all of the geometry
    helpers below. -/
private def cellW : Nat := 110
private def cellH : Nat := 70
private def pad   : Nat := 30

/-- Centre of a cell on the diagram grid. -/
private def centreX (col : Nat) : Nat := pad + col * cellW + cellW / 2
private def centreY (row : Nat) : Nat := pad + row * cellH + cellH / 2

/-- Look up a node by id (linear scan — diagrams are small). -/
private def lookup (d : Diagram) (id : String) : Option DiagNode :=
  d.nodes.find? (·.id == id)

/-- Render one node as inline SVG centred on its grid cell.  The
    caller is responsible for choosing `(x, y)` (top-left
    corner). -/
private def renderNode (n : DiagNode) (x y : Nat) : String :=
  let w := 76
  let h := 44
  let labelX := x + w / 2
  let labelY := y + h / 2 + 4
  let label  := n.label
  let body : String := match n.kind with
    | .reg =>
        s!"<rect x='{x}' y='{y}' width='{w}' height='{h}' rx='4' ry='4' \
           fill='#e3f2fd' stroke='#1976d2' stroke-width='1.5'/>"
    | .mux =>
        -- Trapezoid widening to the right
        s!"<polygon points='{x+8},{y} {x+w},{y+8} {x+w},{y+h-8} {x+8},{y+h}' \
           fill='#fff3e0' stroke='#e65100' stroke-width='1.5'/>"
    | .port =>
        s!"<rect x='{x}' y='{y}' width='{w}' height='{h}' rx='10' ry='10' \
           fill='#f5f5f5' stroke='#444' stroke-width='1.5'/>"
    | .const =>
        s!"<rect x='{x+10}' y='{y+10}' width='{w-20}' height='{h-20}' \
           fill='#fff' stroke='#666' stroke-dasharray='3,2'/>"
    | .clk =>
        let cx := x + w/2
        let cy := y + h/2
        s!"<circle cx='{cx}' cy='{cy}' r='{w/2-4}' fill='#fffde7' \
           stroke='#f57f17' stroke-width='1.5'/>" ++
        s!"<line x1='{cx-8}' y1='{cy}' x2='{cx+8}' y2='{cy}' \
           stroke='#f57f17' stroke-width='1.2'/>" ++
        s!"<line x1='{cx}' y1='{cy-8}' x2='{cx}' y2='{cy+8}' \
           stroke='#f57f17' stroke-width='1.2'/>"
    | .adder =>
        s!"<rect x='{x}' y='{y}' width='{w}' height='{h}' rx='6' ry='6' \
           fill='#fce4ec' stroke='#c2185b' stroke-width='1.5'/>"
    | .andG =>
        -- D-shape (AND gate body)
        s!"<path d='M {x} {y} L {x+w/2} {y} \
                 A {h/2} {h/2} 0 0 1 {x+w/2} {y+h} \
                 L {x} {y+h} z' \
           fill='#e8f5e9' stroke='#2e7d32' stroke-width='1.5'/>"
    | .orG =>
        s!"<path d='M {x} {y} Q {x+w/4} {y+h/2} {x} {y+h} \
                 Q {x+3*w/4} {y+h} {x+w} {y+h/2} \
                 Q {x+3*w/4} {y} {x} {y} z' \
           fill='#e1f5fe' stroke='#0277bd' stroke-width='1.5'/>"
    | .notG =>
        s!"<polygon points='{x},{y} {x+w-12},{y+h/2} {x},{y+h}' \
           fill='#ffebee' stroke='#c62828' stroke-width='1.5'/>" ++
        s!"<circle cx='{x+w-6}' cy='{y+h/2}' r='4' \
           fill='#fff' stroke='#c62828' stroke-width='1.5'/>"
    | .cloud =>
        let cx0 := x + 10
        let cy0 := y + 10
        s!"<path d='M {cx0+10} {cy0+10} q -10 -10 5 -20 q 5 -15 25 -10 \
                  q 10 -15 30 -5 q 20 -5 25 15 q 15 5 -5 20 z' \
           fill='#fff8e1' stroke='#999' stroke-width='1.2'/>"
    | .gen =>
        s!"<rect x='{x}' y='{y}' width='{w}' height='{h}' rx='4' ry='4' \
           fill='#fafafa' stroke='#666' stroke-width='1'/>"
  body ++
    s!"<text x='{labelX}' y='{labelY}' font-size='11' \
            font-family='monospace' text-anchor='middle' \
            fill='#222'>{label}</text>"

/-- Edge style attributes (stroke colour, dash pattern, width). -/
private def edgeAttrs : EdgeKind → String × String × String
  | .data    => ("#1f77b4", "",                  "1.5")
  | .clock   => ("#f57f17", "stroke-dasharray='5,3'", "1.5")
  | .bus _   => ("#1f77b4", "",                  "3")

/-- Width label (e.g. `8` for `bus 8`); empty for non-bus edges. -/
private def edgeLabel : EdgeKind → String
  | .bus w => s!"{w}"
  | _      => ""

/-- Render a `Diagram` as a single SVG document.

    Edges first (so node bodies overlay them), then nodes.
    Multi-input destinations distribute their incoming edges
    across the node's left side. -/
def toSvg (d : Diagram) : String := Id.run do
  let maxCol : Nat := d.nodes.foldl (fun m n => max m n.col) 0
  let maxRow : Nat := d.nodes.foldl (fun m n => max m n.row) 0
  let width  := pad * 2 + (maxCol + 1) * cellW
  let height := pad * 2 + (maxRow + 1) * cellH

  -- Reusable arrowhead and clock-triangle markers.  A marker
  -- definition is referenced from each `<line>` / `<path>` via
  -- the `marker-end` attribute; the renderer copies the marker
  -- shape onto the line's tip at draw time.
  let defs : String :=
    "<defs>" ++
    "<marker id='sp-arrow' viewBox='0 0 10 10' refX='9' refY='5' \
             markerWidth='8' markerHeight='8' orient='auto'>" ++
    "<path d='M 0 0 L 10 5 L 0 10 z' fill='#1f77b4'/>" ++
    "</marker>" ++
    "<marker id='sp-arrow-bus' viewBox='0 0 10 10' refX='9' refY='5' \
             markerWidth='9' markerHeight='9' orient='auto'>" ++
    "<path d='M 0 0 L 10 5 L 0 10 z' fill='#1f77b4'/>" ++
    "</marker>" ++
    "<marker id='sp-clk-tri' viewBox='0 0 10 10' refX='9' refY='5' \
             markerWidth='8' markerHeight='8' orient='auto'>" ++
    "<path d='M 0 0 L 10 5 L 0 10 z' fill='#f57f17'/>" ++
    "</marker>" ++
    "</defs>"

  let mut body : String := defs

  -- Edges
  for e in d.edges do
    -- `dst` may be "id" or "id.k"; we ignore the .k suffix here
    -- (multi-input layout would refine this further).
    let dstId := (e.dst.splitOn ".").head!
    match lookup d e.src, lookup d dstId with
    | some s, some t =>
      let (stroke, dash, strokeW) := edgeAttrs e.kind
      let marker : String := match e.kind with
        | .clock  => "marker-end='url(#sp-clk-tri)'"
        | .bus _  => "marker-end='url(#sp-arrow-bus)'"
        | .data   => "marker-end='url(#sp-arrow)'"
      let x1 := centreX s.col
      let y1 := centreY s.row
      let x2 := centreX t.col
      let y2 := centreY t.row
      body := body ++ s!"<line x1='{x1}' y1='{y1}' x2='{x2}' y2='{y2}' \
                              stroke='{stroke}' stroke-width='{strokeW}' \
                              {dash} {marker}/>"
      let lab := edgeLabel e.kind
      if lab != "" then
        let mx := (x1 + x2) / 2
        let my := (y1 + y2) / 2 - 4
        body := body ++ s!"<text x='{mx}' y='{my}' font-size='10' \
                                font-family='monospace' fill='#1f77b4' \
                                text-anchor='middle'>{lab}</text>"
    | _, _ => pure ()

  -- Nodes
  for n in d.nodes do
    let nx := pad + n.col * cellW + (cellW - 76) / 2
    let ny := pad + n.row * cellH + (cellH - 44) / 2
    body := body ++ renderNode n nx ny

  return s!"<svg xmlns='http://www.w3.org/2000/svg' \
                 width='{width}' height='{height}'>{body}</svg>"

/-- Render a `Diagram` and emit it to the current cell as an
    `image/svg+xml` payload.  `text/html` (an `<img>` wrapping
    the SVG) is also acceptable but plain SVG keeps the output
    smaller and lets JupyterLab's vector-zoom handle scaling. -/
def blockDiagram (d : Diagram) : IO Unit :=
  Sparkle.Display.Mime.svg (toSvg d)

/-! ## IR → Diagram

  Walk a Sparkle `IR.AST.Module` and synthesise a Diagram
  automatically.  Each statement becomes one node; each
  `Expr.ref` inside a statement's RHS becomes one edge.

  Layout: ports go in column 0 (inputs) and the rightmost column
  (outputs); registers and combinational gates fan out across
  the middle columns roughly in topological order.  This isn't
  a real placer — the goal is "good enough to read at a glance",
  not to match a manually-authored figure.
-/

open Sparkle.IR.AST

/-- Pick a `NodeKind` for an assignment based on the head
    operator of its RHS. -/
private def kindOfExpr : Expr → NodeKind
  | .const _ _              => .const
  | .ref _                  => .gen
  | .op .add  _             => .adder
  | .op .sub  _             => .adder
  | .op .and  _             => .andG
  | .op .or   _             => .orG
  | .op .xor  _             => .gen     -- no dedicated XOR shape yet
  | .op .not  _             => .notG
  | .op .mux  _             => .mux
  | .op _     _             => .gen
  | .concat _               => .gen
  | .slice _ _ _            => .gen
  | .index _ _              => .gen

/-- Collect every wire reference inside an expression. -/
private partial def refsOf : Expr → List String
  | .ref n            => [n]
  | .const _ _        => []
  | .op _ args        => args.foldl (fun acc e => acc ++ refsOf e) []
  | .concat args      => args.foldl (fun acc e => acc ++ refsOf e) []
  | .slice e _ _      => refsOf e
  | .index a i        => refsOf a ++ refsOf i

/-- Build a `Diagram` from a Sparkle IR module.

    Strategy: each input port is a `port` node in column 0; each
    statement gets a node in some intermediate column based on
    its index in the body; each output port is a `port` node in
    the final column.  Edges follow `Expr.ref` dependencies. -/
def fromModule (m : Module) : Diagram := Id.run do
  let inCount : Nat := m.inputs.length
  let bodyCount : Nat := m.body.length
  let _outCount : Nat := m.outputs.length

  let mut nodes : List DiagNode := []
  let mut edges : List DiagEdge := []

  -- Input ports — column 0, one per row.
  for h : i in [0:inCount] do
    let p := m.inputs[i]!
    nodes := nodes ++ [{
      id := p.name, label := p.name, kind := .port,
      col := 0, row := i
    }]

  -- Body statements — middle columns.  For now, lay them out one
  -- per row to keep the picture readable.
  let mut row : Nat := 0
  for stmt in m.body do
    match stmt with
    | .assign lhs rhs =>
      nodes := nodes ++ [{
        id := lhs, label := lhs, kind := kindOfExpr rhs,
        col := 1, row := row
      }]
      for r in refsOf rhs do
        edges := edges ++ [{ src := r, dst := lhs }]
    | .register output clock _reset input _initVal =>
      nodes := nodes ++ [{
        id := output, label := output, kind := .reg,
        col := 1, row := row
      }]
      edges := edges ++ [{ src := clock, dst := output, kind := .clock }]
      for r in refsOf input do
        edges := edges ++ [{ src := r, dst := output }]
    | .memory name _ _ clock writeAddr writeData writeEnable readAddr readData _ =>
      nodes := nodes ++ [{
        id := name, label := s!"mem {name}", kind := .gen,
        col := 1, row := row
      }]
      edges := edges ++ [{ src := clock, dst := name, kind := .clock }]
      for r in refsOf writeAddr ++ refsOf writeData ++ refsOf writeEnable
              ++ refsOf readAddr do
        edges := edges ++ [{ src := r, dst := name }]
      nodes := nodes ++ [{
        id := readData, label := readData, kind := .gen,
        col := 2, row := row
      }]
      edges := edges ++ [{ src := name, dst := readData }]
    | .inst modName instName conns =>
      nodes := nodes ++ [{
        id := instName, label := s!"{modName}", kind := .gen,
        col := 1, row := row
      }]
      for (_, e) in conns do
        for r in refsOf e do
          edges := edges ++ [{ src := r, dst := instName }]
    row := row + 1

  -- Output ports — column 2, one per row.
  for h : i in [0:m.outputs.length] do
    let p := m.outputs[i]!
    nodes := nodes ++ [{
      id := s!"out:{p.name}", label := p.name, kind := .port,
      col := 2, row := i
    }]
    edges := edges ++ [{ src := p.name, dst := s!"out:{p.name}" }]

  return { nodes, edges }

end Sparkle.Display.Diagram
