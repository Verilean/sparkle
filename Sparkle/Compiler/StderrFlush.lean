/-! # Flushing the standard error stream

One named action for "flush the process's standard error". The synthesis
entry and the translator call it after a diagnostic line.

It is a constant of its own so that a statement about the compiler's runs
can speak of THIS action: `IO.FS.Stream` is a structure of closures, so a
statement about `h.flush` for an arbitrary stream `h` is a statement about
an arbitrary `IO` action. -/
namespace Sparkle.Compiler

/-- Flush the process's standard error. -/
def flushStderr : IO Unit := do
  (← IO.getStderr).flush

end Sparkle.Compiler
