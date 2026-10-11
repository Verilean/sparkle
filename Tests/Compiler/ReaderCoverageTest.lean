import Tests.Compiler.ShippingCallsCloseTest
import Tests.Compiler.ShippingMachineSeqTest
import Tests.Compiler.ShippingDesignSVTest
import Tests.Compiler.ShippingMachineLinkedTest
import Tools.ShippingMachineCommand
import Tools.ShippingReaderNodes2

/-! # How far the strict term reader reaches on real machine bodies (G3)

A MEASUREMENT, by compiled code; no theorem, no assertion, never throws.

For every declaration `f` of the imported test modules that has a
`f.machineData` (i.e. a `#machine_endpoint f` ran), the transition is read
again with the generator's own `readMachine`, and the strict readers are
evaluated on its body under the endpoint's configuration
`kindsCfg dom (isExpr dom) kinds`:

* `core11` — `Tools.ShippingReaderTerm.readTerm` (eleven node kinds);
* `ext18`  — `Tools.ShippingReaderNodes2.readTerm2` (eighteen).

One line per declaration, prefixed `READER`:
`READ (quote back: true)` — the reader returned a term and its quotation is
the body (`Expr` equality, compiled); or `NOT READ (first unread: head/n)` —
the head constant and argument count of an innermost subterm the generator's
`unq` reads and the strict reader does not. A final `READER TOTAL` line has
the counts. -/
namespace Tests.Compiler.ReaderCoverageTest
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingReaderTerm Tools.ShippingReaderInputs Tools.ShippingReaderNodes2

/-- An innermost subterm that the generator's reader reads and `rd` does not. -/
partial def culprit (c : Tools.ShippingMachineCommand.Binders) (rd : Lean.Expr → Bool)
    (e : Lean.Expr) : Option String :=
  match e.getAppArgs.findSome? (culprit c rd) with
  | some s => some s
  | none =>
    if (Tools.ShippingMachineCommand.unq c e).isSome && !rd e then
      some s!"{e.getAppFn.constName?.getD Name.anonymous}/{e.getAppNumArgs}"
    else none

/-- The report of one reader on one body. -/
def report (cfg : Cfg) (c : Tools.ShippingMachineCommand.Binders)
    (rd : Lean.Expr → Option AnyTerm) (body : Lean.Expr) : String × Bool :=
  match rd body with
  | some t =>
    (s!"READ (quote back: {Tools.ShippingUnifiedSource.quote cfg.dom cfg.bools cfg.bits t.2 == body})",
      true)
  | none =>
    (s!"NOT READ (first unread: {(culprit c (fun e => (rd e).isSome) body).getD "?"})", false)

def line (f : Name) : MetaM (String × Bool × Bool) := do
  let r ← Tools.ShippingMachineCommand.readMachine f
  let ks := r.shape.binders.map (·.2)
  let cfg := kindsCfg r.dom (isExpr r.dom) ks
  let c := Tools.ShippingMachineCommand.Binders.ofKinds ks
  let (s1, b1) := report cfg c (readTerm cfg) r.shape.body
  let (s2, b2) := report cfg c (readTerm2 cfg) r.shape.body
  return (s!"core11: {s1}; ext18: {s2}", b1, b2)

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    match n with
    | .str p "machineData" => acc.push p
    | _ => acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  let mut total := 0
  let mut n1 := 0
  let mut n2 := 0
  let mut errs := 0
  for f in names do
    total := total + 1
    try
      let (s, b1, b2) ← line f
      if b1 then n1 := n1 + 1
      if b2 then n2 := n2 + 1
      IO.println s!"READER {f}: {s}"
    catch ex =>
      errs := errs + 1
      IO.println s!"READER {f}: ERROR (not read as a machine here: {← ex.toMessageData.toString})"
  IO.println s!"READER TOTAL: declarations {total}, core11 READ {n1}, ext18 READ {n2}, errors {errs}"

end Tests.Compiler.ReaderCoverageTest
