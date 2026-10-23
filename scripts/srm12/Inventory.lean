import Tests.Compiler.Srm5ParentTest
import Tests.Compiler.Srm5ParentQTest
-- SRM12 inventory.  Run: ./.cluster/qbuild.sh env lean scripts/srm12/Inventory.lean > scripts/srm12/INVENTORY.txt
-- (a) CallGraph edges read from machineData (`shape.instTagged`, caller/kid/origin);
-- (b) instance statements of every module of the compiled design (`synthesizeCombinational`: top module + D.modules).
-- Plain text, nothing here is a proof.
set_option autoImplicit false
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.AST
open Tests.Compiler.SharedLeafMemKidTest

def showKey (s : String) : String :=
  match Sparkle.IR.ModuleName.decode s with
  | some (.decl n) => s!"decl {n}"
  | some (.mem c a d) => s!"mem {c} {a} {d}"
  | some (.aux n) => s!"aux {n}"
  | none => "UNDECODED"

/-- the call graph entries of `decl`: `shape.instTagged` of its generated `machineData`, reduced in the kernel-free `Meta.reduce` and evaluated -/
elab "#edges " id:ident : command => do
  let declName ← liftCoreM <| resolveGlobalConstNoOverload id
  liftTermElabM do
    let e ← mkAppM ``Sparkle.Compiler.Elab.MachineShape.instTagged #[← mkAppM ``Tools.ShippingMachineAuto.MachineData.shape #[mkConst (declName ++ `machineData)]]
    let r ← Meta.reduce e
    let l ← unsafe Meta.evalExpr (List (Name × Sparkle.Compiler.MachInstOrigin.InstOrigin))
      (← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``Name, mkConst ``Sparkle.Compiler.MachInstOrigin.InstOrigin]]) r
    for (n, o) in l do IO.println s!"EDGE caller={declName} kid={n} origin={repr o}"

#edges topshareM
#edges wrapM
#edges wrapM3
#edges leafM
#edges topshareQ
#edges wrapP
#edges wrapQ
#edges leafP

def invDesign (declName : Name) : MetaM Unit := do
  let (top, d) ← synthesizeCombinational declName
  IO.println s!"DESIGN {declName}: top={top.name} [{showKey top.name}] D.modules={d.modules.map (·.name)}"
  for m in top :: d.modules do
    IO.println s!"MODULE {m.name} [{showKey m.name}]{if m.name == top.name then " (top)" else ""}"
    for st in m.body do
      match st with
      | .inst mn iname _ => IO.println s!"INST module={m.name} iname={iname} target={mn} [{showKey mn}]"
      | _ => pure ()

#eval invDesign ``topshareM
#eval invDesign ``topshareQ
