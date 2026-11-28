/-
  Shared machinery for the silent-wire audit probes (notes/compiler/silent-wire-audit.md).

  `#probe "tag" decl "reg"|"out" "expected"` synthesizes `decl`, reduces the
  first register input (or the first output) to a short description of WHERE
  the value comes from (`Module.port`, `in:name`, slice bounds, ...), and
  compares it with the wiring that is unambiguously correct.  It never aborts
  the build: the verdict (refused / silently wrong / correct) is stored as a
  declaration in `Verdicts` and printed by the driver.
-/
import Sparkle
import Sparkle.Compiler.Elab

namespace Sparkle.Tests.Compiler.SilentWireProbe

open Lean Elab Command Meta

abbrev IModule := Sparkle.IR.AST.Module
abbrev IExpr := Sparkle.IR.AST.Expr

/-- Where does `e` read from?  Follows assigns; stops at inputs, register
    outputs and sub-instance ports. -/
partial def describe (m : IModule) (fuel : Nat) : IExpr → String
  | .const v w => s!"{v}#{w}"
  | .ref w0 =>
    let w := w0
    if m.inputs.any (·.name == w) then s!"in:{(w.dropPrefix "_gen_").toString}"
    else if m.body.any (fun | .register o .. => o == w | _ => false) then s!"reg:{w}"
    else match m.body.findSome? (fun | .assign l r => if l == w then some r else none | _ => none) with
      | some r => if fuel == 0 then w else describe m (fuel - 1) r
      | none =>
        match m.body.findSome? (fun
            | .inst mn _ conns =>
              (conns.find? fun (_, e) => e == Sparkle.IR.AST.Expr.ref w).map fun (p, _) => s!"{mn.splitOn "." |>.getLast!}.{p}"
            | _ => none) with
        | some s => s
        | none => s!"wire:{w}"
  | .slice e hi lo => s!"{describe m fuel e}[{hi}:{lo}]"
  | .sliceDim e _ _ => s!"dimslice({describe m fuel e})"
  | .op o args => s!"{o}({", ".intercalate (args.map (describe m fuel))})"
  | .concat args => s!"cat({", ".intercalate (args.map (describe m fuel))})"
  | .index a i => s!"{describe m fuel a}[{describe m fuel i}]"

def target (m : IModule) (which : String) : Option String :=
  if which.startsWith "ninst:" then
    let mn := (which.drop 6).toString
    some (toString (m.body.filter (fun | .inst n .. => (n.splitOn ".").getLast! == mn | _ => false)).length)
  else if which == "reg" then
    m.body.findSome? fun | .register _ _ _ input _ => some (describe m 6 input) | _ => none
  else
    m.outputs.head?.map fun o => describe m 6 (Sparkle.IR.AST.Expr.ref o.name)

def sanitize (s : String) : String := s.map fun c => if c.isAlphanum then c else '_'

/-- Record `verdict` as `Verdicts.<tag>` and echo it. -/
def record (tag verdict : String) : CommandElabM Unit := do
  logInfo m!"[probe {tag}] {verdict}"
  let nm := mkIdent (Name.mkStr `Verdicts (sanitize tag))
  elabCommand (← `(def $nm : String := $(quote s!"{tag}: {verdict}")))

/-- Synthesize and classify; `mode` is "reg" or "out" (what to describe). -/
def runProbe (tag : String) (declName : Name) (mode expected : String)
    (params : Option (List (String × Nat)) := none) : CommandElabM Unit := do
  let r ← liftTermElabM do
    try
      let (m, _) ← match params with
        | none => Sparkle.Compiler.Elab.synthesizeCombinational declName
        | some ps => Sparkle.Compiler.Elab.synthesizeCombinationalWithParameters declName ps
      let stmts := m.body.map toString
      return Except.ok (target m mode, stmts)
    catch ex =>
      return Except.error (← ex.toMessageData.toString)
  match r with
  | .error msg =>
    let first := if (msg.splitOn "\n").length > 1 then " | ".intercalate ((msg.splitOn "\n").take 4) else msg
    record tag s!"(b) REFUSED with error: {first.take 600}"
  | .ok (none, _) => record tag "(d) no register/output to inspect"
  | .ok (some got, stmts) =>
    let dump := "\n      " ++ "\n      ".intercalate (stmts.take 40)
    -- `expected` may list alternatives separated by `|` (each exact, or `~sub` = contains `sub`).
    let okOne := fun (e : String) => if e.startsWith "~" then (got.splitOn ((e.drop 1).toString)).length > 1
              else got == e
    let ok := (expected.splitOn "|").any okOne
    if ok then record tag s!"(c) correct: {got}"
    else record tag s!"(a) SILENT WRONG: wired {got}, expected {expected}{dump}"

elab "#probe " tag:str id:ident mode:str exp:str : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  runProbe tag.getString declName mode.getString exp.getString

elab "#probeP " tag:str id:ident mode:str exp:str w:str n:num : command => do
  let declName ← liftCoreM (Lean.resolveGlobalConstNoOverload id)
  runProbe tag.getString declName mode.getString exp.getString (some [(w.getString, n.getNat)])

/-- Gather every `Verdicts.*` declaration into `allVerdicts`. -/
elab "#probeSummary" : command => do
  let env ← getEnv
  let mut items : Array (String × String) := #[]
  items := env.constants.fold (init := items) fun acc n ci =>
    if (n.toString.splitOn ".Verdicts.").length > 1 then
      match ci with
      | .defnInfo d =>
        match d.value with
        | .lit (.strVal s) => acc.push (n.toString, s)
        | _ => acc
      | _ => acc
    else acc
  let sorted := (items.qsort (fun a b => a.1 < b.1)).map (·.2)
  let nm := mkIdent `allVerdicts
  elabCommand (← `(def $nm : List String := $(quote sorted.toList)))

end Sparkle.Tests.Compiler.SilentWireProbe
