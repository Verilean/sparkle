import Tools.ShippingFGCircuitS3jStart
set_option autoImplicit false
-- FG circuit pilot S3r, step 1-2: UNTRUSTED generator of `Tools/ShippingFGCircuitS3rArtifact.lean` (the (b, D) that `pilotEntry3 hftRoot` returns, as closed Lean terms `pilotB0 : Module`, `pilotD0 : Design`).
-- `Module`/`Design` have no `ToExpr` and `Expr` is nested (`List Expr`), so the "ToExpr" is a hand-written source printer (constructor applications, every field explicit). Nothing here is trusted: what the kernel accepts is the checks run on the generated terms, and that the terms are what the compiler returned is an OBSERVATION (`Tools.ShippingFGCircuitS3rObs`).
-- `#gen_pilot_artifact "path"` runs the entry at elaboration time and writes the file; it is run once by hand, not by the build. No sorry/axiom/native_decide/TRUSTED/law. docs/FG-CIRCUIT-PILOT.md §68.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tools.ShippingFGCircuitS3rGen
open Sparkle.IR.AST Sparkle.IR.Type

def listSrc {α : Type} (f : α → String) (xs : List α) : String :=
  "[" ++ ", ".intercalate (xs.map f) ++ "]"

def intSrc (i : Int) : String := if i < 0 then s!"(-{i.natAbs} : Int)" else s!"({i.toNat} : Int)"

def boolSrc (b : Bool) : String := if b then "true" else "false"

def dimSrc : DimExpr → String
  | .literal v => s!"(DimExpr.literal {v})"
  | .parameter n => s!"(DimExpr.parameter {n.quote})"
  | .add a b => s!"(DimExpr.add {dimSrc a} {dimSrc b})"
  | .sub a b => s!"(DimExpr.sub {dimSrc a} {dimSrc b})"
  | .mul a b => s!"(DimExpr.mul {dimSrc a} {dimSrc b})"
  | .div a b => s!"(DimExpr.div {dimSrc a} {dimSrc b})"
  | .mod a b => s!"(DimExpr.mod {dimSrc a} {dimSrc b})"
  | .pow a b => s!"(DimExpr.pow {dimSrc a} {dimSrc b})"
  | .clog2 a => s!"(DimExpr.clog2 {dimSrc a})"
  | .min a b => s!"(DimExpr.min {dimSrc a} {dimSrc b})"
  | .max a b => s!"(DimExpr.max {dimSrc a} {dimSrc b})"

def tySrc : HWType → String
  | .bit => "HWType.bit"
  | .bitVector w => s!"(HWType.bitVector {w})"
  | .bitVectorDim d => s!"(HWType.bitVectorDim {dimSrc d})"
  | .array n t => s!"(HWType.array {n} {tySrc t})"

def opSrc (o : Operator) : String := s!"Operator.{o.toString}"

partial def exprSrc : Expr → String
  | .const v w => s!"(Expr.const {intSrc v} {w})"
  | .ref n => s!"(Expr.ref {n.quote})"
  | .op o args => s!"(Expr.op {opSrc o} {listSrc exprSrc args})"
  | .concat args => s!"(Expr.concat {listSrc exprSrc args})"
  | .slice e h l => s!"(Expr.slice {exprSrc e} {h} {l})"
  | .sliceDim e h l => s!"(Expr.sliceDim {exprSrc e} {dimSrc h} {dimSrc l})"
  | .index a i => s!"(Expr.index {exprSrc a} {exprSrc i})"

def resetKindSrc : ResetKind → String
  | .synchronous => "ResetKind.synchronous"
  | .asynchronous => "ResetKind.asynchronous"

def stmtSrc : Stmt → String
  | .assign l r => s!"Stmt.assign {l.quote} {exprSrc r}"
  | .register o c (rn, rk) i iv =>
      s!"Stmt.register {o.quote} {c.quote} ({rn.quote}, {resetKindSrc rk}) {exprSrc i} {intSrc iv}"
  | .memory n aw dw c wa wd we ra rd cr ew er =>
      s!"Stmt.memory {n.quote} {aw} {dw} {c.quote} {exprSrc wa} {exprSrc wd} {exprSrc we} {exprSrc ra} {rd.quote} {boolSrc cr} " ++
      s!"{listSrc (fun (a, d, e) => s!"({exprSrc a}, {exprSrc d}, {exprSrc e})") ew} " ++
      s!"{listSrc (fun (a, r) => s!"({exprSrc a}, {r.quote})") er}"
  | .inst m i cs => s!"Stmt.inst {m.quote} {i.quote} {listSrc (fun (p, e) => s!"({p.quote}, {exprSrc e})") cs}"

def portSrc (p : Port) : String := s!"⟨{p.name.quote}, {tySrc p.ty}⟩"

/-- one definition, one statement per line -/
def moduleSrc (defName : String) (m : Module) : String :=
  let stmts := ",\n    ".intercalate (m.body.map fun s => s!"({stmtSrc s})")
  s!"def {defName} : Module :=\n  \{ name := {m.name.quote}\n" ++
  s!"  , parameters := {listSrc (fun (p : Parameter) => s!"⟨{p.name.quote}, {p.defaultValue}⟩") m.parameters}\n" ++
  s!"  , inputs := {listSrc portSrc m.inputs}\n" ++
  s!"  , outputs := {listSrc portSrc m.outputs}\n" ++
  s!"  , wires := {listSrc portSrc m.wires}\n" ++
  s!"  , body := [\n    {stmts}]\n" ++
  s!"  , assertions := {listSrc (fun (n, e) => s!"({n.quote}, {exprSrc e})") m.assertions}\n" ++
  s!"  , isPrimitive := {boolSrc m.isPrimitive} }\n"

/-- the whole generated file for a returned `(b, D)` -/
def fileSrc (b : Module) (D : Design) : String :=
  "import Sparkle.IR.AST\n" ++
  "set_option autoImplicit false\n" ++
  "-- GENERATED, UNTRUSTED (FG circuit pilot S3r; generator: `Tools/ShippingFGCircuitS3rGen.lean`, command `#gen_pilot_artifact`).\n" ++
  "-- The (b, D) that `pilotEntry3 hftRoot` returned in ONE run, as closed terms.  That these terms are what the compiler returns is an observation\n" ++
  "-- (`Tools.ShippingFGCircuitS3rObs`), not a kernel fact; the kernel facts are the checks run on these terms (`Tools.ShippingFGCircuitS3rKernel`).\n" ++
  "-- No sorry/axiom/native_decide/TRUSTED/law.\n" ++
  "set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n" ++
  "namespace Tools.ShippingFGCircuitS3rArtifact\nopen Sparkle.IR.AST Sparkle.IR.Type\n\n" ++
  moduleSrc "pilotB0" b ++ "\n" ++
  "\n".intercalate (D.modules.zipIdx.map fun (m, i) => moduleSrc s!"pilotK{i}" m) ++ "\n" ++
  s!"def pilotD0 : Design := \{ topModule := {D.topModule.quote}, modules := [{", ".intercalate (D.modules.zipIdx.map fun (_, i) => s!"pilotK{i}")}] }\n\n" ++
  "end Tools.ShippingFGCircuitS3rArtifact\n"

section Cmd
open Lean Elab Command
/-- run the entry on the pilot root at elaboration time and write the artifact file -/
elab "#gen_pilot_artifact " path:str : command => do
  let (b, D) ← liftTermElabM (Tools.ShippingFGCircuitS3jStart.pilotEntry3 Tools.ShippingFGCircuitS1kStmt.hftRoot)
  IO.FS.writeFile path.getString (fileSrc b D)
  logInfo m!"S3R wrote {path.getString}: top {b.body.length} stmts, {D.modules.length} children {D.modules.map (·.body.length)}"

end Cmd

end Tools.ShippingFGCircuitS3rGen
