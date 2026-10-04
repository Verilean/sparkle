# Display Migration Plan — splitting xeus-lean and Sparkle

## TL;DR

xeus-lean keeps the **kernel-side plumbing**: MIME emit primitives,
generic `#html` / `#svg` / `#md` / `#bash` elabs, the `CommBus`
session registry that lets JS frontends call back into Lean over a
Jupyter `comm` channel.

Sparkle takes the **HDL-aware renderers**: block diagrams, waveforms,
the `wdb` waveform-database serialiser.  These are the things that
need new shapes / new IR-aware layouts as Sparkle's hardware
features grow; keeping them inside the kernel meant a kernel rebuild
for every visualisation tweak.

## Boundary

| Capability                              | Owner       | Module                                  |
|-----------------------------------------|-------------|-----------------------------------------|
| ESC/RS MIME marker bytes                | xeus-lean   | `Display.mkMarker` / `emit` / `html`    |
| `#html` / `#svg` / `#md` / `#bash` elab | xeus-lean   | `Display.lean` (generic part)           |
| `CommBus` (JS↔Lean comm channel)        | xeus-lean   | `CommBus.lean`                          |
| Block-diagram structures + SVG          | **Sparkle** | `Sparkle.Display.Diagram`               |
| Sparkle IR → Diagram auto-layout        | **Sparkle** | `Sparkle.Display.Diagram.fromModule`    |
| Waveform viewer (interactive)           | **Sparkle** | `Sparkle.Display.Waveform` *(planned)*  |
| `wdb` compressed waveform DB            | **Sparkle** | `Sparkle.Display.Wdb` *(planned)*       |
| Generic interactive widget framework    | **Sparkle** | `Sparkle.Display.Interactive` *(planned)* |

## Wire format

Both sides agree on:

```
\x1bMIME:<mime-type>\x1e<content>\x1b/MIME\x1e
```

(ESC = 0x1B, RS = 0x1E.  See `Sparkle.Display.Mime.mkMarker`.)

xeus-lean's C++ FFI (`extract_mime_payloads` in `xeus_ffi.cpp`)
parses these markers out of the Lean message log and ships the
payload to Jupyter as `display_data`.

## Migration roadmap

### Phase 1 — Diagram (DONE)

`Sparkle.Display.Diagram` has the structures (`DiagNode`,
`DiagEdge`, `NodeKind`, `EdgeKind`), the SVG renderer, and a
`fromModule : IR.AST.Module → Diagram` so any synthesisable
Sparkle design can be visualised without writing the diagram by
hand.

xeus-lean's `Display.Diagram.*` should be removed once tutorial
chapters and `tutorial-extended/` have been switched over to
`Sparkle.Display.Diagram`.

### Phase 2 — Interactive widget framework (DONE)

`Sparkle.Display.Interactive` (`Sparkle/Display/Interactive.lean`)
ships the generic `Widget S` structure plus the `render` action.
The actual comm-bus binding is **dependency-injected**:
`Sparkle.Display.Interactive` does not `import CommBus` at all,
so it builds standalone outside the tutorial Docker image.

Wire-up (called once per project, typically in
`docs/tutorial/Notebooks.lean`):

```lean
import CommBus
import Sparkle.Display.Interactive

initialize Sparkle.Display.Interactive.bindCommBus
  CommBus.register
```

After that, every `Sparkle.Display.Interactive.render` routes
its handler through `CommBus`.  Without the binding, `render`
still emits the cell HTML so the JS side draws; only the
kernel-side handler dispatch is disabled.  This keeps `lake
build` green outside the tutorial environment.

`CommBus` stays in xeus-lean — it's the kernel-side comm
dispatcher and shouldn't move.  Sparkle's binding is a one-line
function pointer install, not a build-time dependency.

### Phase 3 — Waveform on top of `Interactive`

Re-implement `WaveformSession` as a `Widget` instance.  The
opcodes (`list` / `addLane` / `removeLane` / data query) become
the handler's `match` cases; the JS canvas-rendering blob moves
into `Sparkle.Display.Waveform` as a static string.  At that
point xeus-lean's `Display.lean` can drop ~600 lines of
HDL-specific waveform code.

### Phase 4 — Wdb

The compressed waveform-database format (`zstd` + per-signal
transition lists) belongs with the rest of the waveform machinery
on the Sparkle side.  This needs Lean FFI to libzstd; xeus-lean
has the wiring already (`zstdCompress` / `zstdDecompressBytes`
calling out to `fzstd.umd.js` in the JS layer).  Sparkle will
need its own native zstd shim — same approach as
`c_src/sparkle_barrier.c`.

## What xeus-lean has to do

Three repository-level changes, all on the xeus-lean side:

1. **Stdout MIME extraction.**  `extract_mime_payloads` only
   scans the Lean message log today.  Extend it to also scan the
   `captured` stdout pipe before concatenation, so `IO.println`
   of a MIME marker (e.g. `#eval Sparkle.Display.Diagram.blockDiagram d`)
   reaches the cell as `display_data` rather than as plain text.

2. **Remove HDL-specific renderers** once Sparkle.Display has
   replaced them: `Display.{verilog, mermaid, blockDiagram,
   waveform, boolWave, writeWdb, waveformFromWdb,
   waveformInteractive}` and the `Diagram` / `WaveformSession`
   namespaces.  The `#html` / `#svg` / `#md` / `#bash` /
   `#mermaid` *elabs* stay; they're useful even outside an HDL
   context.

3. **Optional: split `CommBus` into its own `lean_lib`** in the
   xeus-lean lakefile so Sparkle (or any other downstream) can
   `require` it without pulling in the rest of `Display`.  Today
   it's an internal dependency and Sparkle has to reach into the
   kernel's `lib/lean` directory.

## Backwards compatibility

Tutorial chapters (`docs/tutorial/md/Ch*.md`) currently call
`Display.Diagram.NodeKind.…` and `Display.blockDiagram`.  Once
`Sparkle.Display` ships, the chapter source switches to
`Sparkle.Display.Diagram.…` and the offline `docs/tutorial/Display.lean`
shim becomes a thin re-export of `Sparkle.Display.Diagram` for
back-compat — or is removed entirely, with the chapters importing
`Sparkle.Display` directly.

The xeus-lean `Display.{Diagram, blockDiagram, …}` symbols stay
deprecated-but-functional for one tutorial release, then are
deleted.
