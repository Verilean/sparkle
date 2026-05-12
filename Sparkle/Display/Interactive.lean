/-
  Sparkle.Display.Interactive — generic interactive widget on
  top of an injectable comm-bus backend.

  Background.  xeus-lean exposes a single Jupyter `comm` target
  named `xlean`: any JS frontend embedded in cell output can
  open a comm channel against that target and exchange JSON
  with a Lean handler over `iopub`, without going through the
  usual `execute_request` round-trip.

  The kernel side of that wire is xeus-lean's `CommBus.register
  sessionId handler`: the user picks a *session id* (a string
  the JS side echoes in its `comm_open` payload) and registers
  a `Lean.Json → IO Lean.Json` handler.  Subsequent `comm_msg`
  payloads with matching session id are routed to the handler
  and its return value travels back over the same comm.

  This module abstracts that pattern so any Sparkle (or
  downstream) code can instantiate an interactive widget
  without re-deriving the comm-bus / HTML-emit boilerplate.

  Dependency injection.  `Sparkle.Display.Interactive` does
  *not* `import CommBus` — that would chain Sparkle's build to
  xeus-lean.  Instead we keep an `IO.Ref` to a registration
  function (`registerImpl`) which is `none` by default and
  gets installed by user code that *does* depend on xeus-lean
  (typically a one-line `Sparkle.Display.Interactive.bindCommBus
  CommBus.register` in the tutorial's `Notebooks.lean`).

  When the binding is missing, `render` still emits the cell
  HTML so the JS side renders correctly; only the kernel-side
  handler dispatch is disabled.  This keeps `lake build` green
  outside the tutorial Docker image.

  Design.  A `Widget S` packages four pieces:

    sessionId   — the string the JS frontend names in its
                  `comm_open` payload.  Must be unique per cell
                  instance; we suggest `sparkle-<thing>-<rand>`.
    state       — an `IO.Ref` holding whatever per-session
                  mutable state your handler needs (lane list,
                  cursor position, cached query results, …).
    handler     — `S → Lean.Json → IO Lean.Json`: receives the
                  current state and the incoming JSON, returns
                  the JSON to ship back to JS.
    htmlOf      — `String → String`: maps the session id to the
                  cell HTML / JS that sets up the JS side of
                  the widget (opens the comm, draws the
                  canvas, listens for results).

  `render` registers the handler with the bound comm-bus and
  emits the HTML through the standard MIME channel.  Cell
  evaluation returns immediately; the comm thread runs the
  handler on every JS message until the JS side closes the
  comm.

  Wiring up the binding (do this once per project):

      -- somewhere on the import chain that already pulls in
      -- xeus-lean's CommBus, e.g. in your Notebooks.lean root:
      import CommBus
      import Sparkle.Display.Interactive

      initialize Sparkle.Display.Interactive.bindCommBus
        CommBus.register

  After that, every `Sparkle.Display.Interactive.render` call
  routes its handler through `CommBus`.

  Concrete instances live alongside their feature module —
  `Sparkle.Display.Waveform` (planned) is the first one.
-/
import Lean
import Sparkle.Display.Mime

namespace Sparkle.Display.Interactive

/-- Type alias for the comm-bus registration entry point.
    Matches xeus-lean's `CommBus.register : String →
    (Lean.Json → IO Lean.Json) → IO Unit`. -/
abbrev RegisterFn := String → (Lean.Json → IO Lean.Json) → IO Unit

/-- The currently-installed comm-bus backend, or `none` if
    nobody has wired one up yet.  In the tutorial Docker image
    this is set at startup to `CommBus.register`; in a plain
    `lake build` of Sparkle it stays `none` and `render` falls
    back to emitting the HTML without a kernel-side handler. -/
initialize commBusBinding : IO.Ref (Option RegisterFn) ← IO.mkRef none

/-- Install a comm-bus backend.  Call this once at startup
    (e.g. via a top-level `initialize` in your project's
    Notebooks.lean) to wire up xeus-lean's `CommBus.register`.

    Calling it twice replaces the previous binding. -/
def bindCommBus (impl : RegisterFn) : IO Unit :=
  commBusBinding.set (some impl)

/-- A generic interactive widget.

    The `S` type parameter is the per-session mutable state.
    The handler closes over a snapshot of that state on every
    incoming message; if the handler needs to mutate the state
    it should do so via the `IO.Ref` directly (the snapshot
    argument is for read-only convenience). -/
structure Widget (S : Type) where
  /-- Session id the JS frontend will echo in `comm_open`. -/
  sessionId : String
  /-- Per-session mutable state. -/
  state     : IO.Ref S
  /-- Message handler.  `s` is a snapshot of `state` at receipt;
      use `state.modify` / `state.set` to mutate persistently. -/
  handler   : S → Lean.Json → IO Lean.Json
  /-- Cell HTML / JS that sets up the JS side of the widget.
      Receives the session id; expected to embed it in a
      `comm_open` `data.session` field so the bound comm-bus
      routes the messages back to this widget's handler. -/
  htmlOf    : String → String

/-- Register `w`'s handler with the bound comm-bus and emit
    its HTML into the current cell.

    This is a side-effecting `IO` action — call it from a `def
    main : IO Unit` or, more typically, from `#eval`.  The
    return is immediate; the handler runs whenever a `comm_msg`
    arrives, until the JS side closes the comm.

    If no comm-bus backend has been bound (see `bindCommBus`),
    only the HTML is emitted — the JS side will render but the
    kernel won't respond to its messages.  That's the expected
    fallback for offline `lake build`s; it lets test suites
    typecheck `render` calls without dragging in xeus-lean. -/
def render {S : Type} (w : Widget S) : IO Unit := do
  match ← commBusBinding.get with
  | some register =>
    register w.sessionId fun data => do
      let s ← w.state.get
      w.handler s data
  | none =>
    -- No binding: the JS side will see "session not registered"
    -- on its first comm_msg.  We still emit the HTML so the
    -- visible part of the cell renders.
    pure ()
  Sparkle.Display.Mime.html (w.htmlOf w.sessionId)

/-- Generate a fresh, probably-unique session id of the form
    `<tag>-<random hex digits>`.  Convenient for one-shot
    widgets where you don't care about the id surviving across
    re-renders. -/
def uniqueSessionId (tag : String) : IO String := do
  let r ← IO.rand 0 (Nat.pow 2 32 - 1)
  let hex := String.ofList (Nat.toDigits 16 r)
  pure s!"{tag}-{hex}"

end Sparkle.Display.Interactive
