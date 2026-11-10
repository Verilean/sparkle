import Lean
import Sparkle.Compiler.Elab
import Tools.VedU1Entry
import Tools.VedU1Hier
import Tools.VedStrictAudit

/-!
# Hierarchical U1 entry, H1 (`#ved_u1_hier decl`)

Design: docs/VED-HIER-DESIGN-v1.md (§7, option A).  `Sparkle/` is not changed.

`vedU1HierEntry declName`:

1. reads the port table of the ORIGINAL declaration from its type and refuses, before any
   synthesis, more than one output projection (H3);
2. calls `synthesizeCombinational declName` exactly ONCE and keeps the returned `(m, d)` (top
   module and design);
3. registers `declName.ved_mod := toExpr m` and `declName.ved_design := toExpr d` (both checked by
   evaluating the closed terms back), the contract, the output list and one checked arrangement of
   the top body;
4. runs the existing leaf U1 entry (`checkU1E`) on EVERY module of `d`, using the module taken
   from `d` (no second synthesis); the child theorems are about `declName.ved_child.<module>.ved_mod`;
5. elaborates the generated proof of `U1HStmt c m d decl` (kernel, exact expected type, no
   metavariables, strict audit).  The proof (i) decides every artifact check on the registered
   closed terms, (ii) binds each child theorem to the module RESOLVED from this `d` (`decide`),
   (iii) supplies, from the REAL child theorems, the relations the parent proof uses, and (iv)
   returns to the original declaration.

Refusals are `VED U1 REFUSED <decl> [<stage>]: …` as in `#ved_u1`; a failure takes back every
constant the checker added (the synthesis itself is not rolled back).
-/

namespace Tools.VedU1HierEntry

open Lean Meta Elab Term
open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Hier

deriving instance Lean.ToExpr for Sparkle.IR.AST.Design

/-- `toExpr d` evaluated back to a `Design`. -/
unsafe def evalDesignImpl (e : Lean.Expr) : MetaM Design :=
  Meta.evalExpr Design (Lean.mkConst ``Design) e

@[implemented_by evalDesignImpl]
opaque evalDesign (e : Lean.Expr) : MetaM Design

/-! ## Diagnosis (the refusal messages; the proof re-decides everything in the kernel) -/

/-- The first reason a `connsOk` fails, as text. -/
def connDiag (d : Design) (m : Module) (mn iname : String) (cs : List (String × Expr)) : Option String :=
  match findMod d mn with
  | none => some s!"instance {iname}: module {mn} is not in the returned design"
  | some c =>
    let ports := c.inputs ++ c.outputs
    if c.isPrimitive then some s!"instance {iname}: child {mn} is a primitive module"
    else if !c.parameters.isEmpty then some s!"instance {iname}: child {mn} has parameters"
    else if !c.assertions.isEmpty then some s!"instance {iname}: child {mn} has assertions"
    else if !assignOnly c.body then
      some s!"instance {iname}: child {mn} is not a combinational leaf (register, memory or instance in its body: H2)"
    else if c.outputs.length != 1 then
      some s!"instance {iname}: child {mn} has {c.outputs.length} outputs (multi-output children: H3)"
    else if !(decide (cs.map (·.1)).Nodup) then
      some s!"instance {iname}: duplicate port connection"
    else match ports.find? (fun p => !cs.any (fun q => q.1 == p.name)) with
    | some p => some s!"instance {iname}: port {p.name} of {mn} is not connected"
    | none =>
    match cs.find? (fun q => !ports.any (fun p => p.name == q.1)) with
    | some q => some s!"instance {iname}: connection to {q.1}, which {mn} has no such port"
    | none =>
    match cs.find? (fun q => match q.2 with | .ref _ => false | _ => true) with
    | some q => some s!"instance {iname}: port {q.1} is not connected to a plain wire reference (H1: ref only)"
    | none =>
    match cs.find? (fun q => match q.2 with
      | .ref x => !ports.any (fun p => p.name == q.1 && scalar p.ty && declWidth m x == p.ty.bitWidth)
      | _ => false) with
    | some q => some s!"instance {iname}: width mismatch on port {q.1} (wire {q.2} against the port)"
    | none => none

/-- The first reason `HierShape` fails, as text. -/
def hierDiag (d : Design) (m : Module) : Option String :=
  if d.topModule != m.name then
    some s!"the design's top module {d.topModule} is not the returned module {m.name}"
  else if !(decide (d.modules.map (·.name)).Nodup) then
    some s!"duplicate child module names in the design: {d.modules.map (·.name)}"
  else if (d.modules.map (·.name)).contains m.name then
    some s!"the top module {m.name} is also listed among the design's modules"
  else match m.body.find? (fun s => !isAsgInst s) with
  | some s => some s!"top statement {s} is not an assignment or an instance (registers or memories at the top are not in H1)"
  | none =>
  match (m.body.filterMap fun s => match s with
      | .inst mn i cs => connDiag d m mn i cs
      | _ => none).head? with
  | some msg => some msg
  | none =>
  if !(decide (instNames m.body).Nodup) then some "duplicate instance names"
  else match d.modules.find? (fun c => !(m.body.any (fun s => match s with
        | .inst mn _ _ => mn == c.name
        | _ => false))) with
  | some c => some s!"module {c.name} of the design is not instantiated by the top module (an unused or unsupported leftover module is refused, never dropped)"
  | none => none

open Sparkle.IR.Reorder in
/-- A stable dependency order of the top body: repeatedly take the FIRST remaining statement none
of whose reads another remaining statement writes.  On a cycle the rest is appended in its own
order and `OrderOkH` then fails. -/
def orderBodyH (d : Design) (body : List Stmt) : List Stmt := Id.run do
  let mut rest := body
  let mut out : Array Stmt := #[]
  for _ in [0:body.length] do
    let ready := fun (s : Stmt) => (rdH d s).all (fun n => !(wrsH d (rest.erase s)).contains n)
    match rest.find? ready with
    | some s => out := out.push s; rest := rest.erase s
    | none => break
  return out.toList ++ rest

/-! ## Names -/

structure HNames where
  mod : Name
  design : Name
  contract : Name
  outs : Name
  body : Name
  thm : Name

def HNames.ofBase (base : Name) : HNames :=
  { mod := base ++ `ved_mod, design := base ++ `ved_design, contract := base ++ `ved_contract,
    outs := base ++ `ved_outs, body := base ++ `ved_body, thm := base ++ `ved_u1 }

/-- One child module of the design and its leaf U1 check. -/
structure Kid where
  c : Module
  decl : Name
  nDom : Nat
  tbl : DeclTable
  nm : Names

/-! ## The generated proof -/

def sq (s : String) : String := s.quote

def portTy (p : PTy) : String :=
  match p with
  | .bit => "Bool"
  | .bv w => s!"(BitVec {w})"

def sigTy (p : PTy) : String :=
  s!"(Sparkle.Core.Signal.Signal Sparkle.Core.Domain.defaultDomain {portTy p})"

/-- The declaration term as the statement writes it (`@decl defaultDomain …` when specialised). -/
def declTerm (decl : Name) (nDom : Nat) : String :=
  if nDom == 0 then s!"{decl}"
  else "(@" ++ s!"{decl}" ++ String.join (List.replicate nDom " Sparkle.Core.Domain.defaultDomain") ++ ")"

def connsLit (cs : List (String × Expr)) : String :=
  "[" ++ ", ".intercalate (cs.map fun (p, e) =>
    match e with
    | .ref x => s!"({sq p}, Sparkle.IR.AST.Expr.ref {sq x})"
    | _ => s!"({sq p}, Sparkle.IR.AST.Expr.ref \"?\")") ++ "]"

def strList (xs : List String) : String := "[" ++ ", ".intercalate (xs.map sq) ++ "]"

/-- The generated (untrusted) proof text of `U1HStmt P.contract P.mod P.design F`. -/
def scriptText (nm : HNames) (F : Name) (nDom : Nat) (m : Module) (d : Design) (kids : List Kid) :
    String := Id.run do
  let P := nm
  let mut L : Array String := #[]
  let kidIdx := kids.zipIdx
  L := L.push s!"  have hne := Tools.VedU1Hier.hier_ne (show Tools.VedU1Hier.HierShape {P.design} {P.mod} = true by decide)"
  L := L.push s!"  have hord : Tools.VedU1Hier.OrderH {P.design} {P.mod} := ⟨{P.body}, by decide⟩"
  L := L.push s!"  have hb0 := Tools.VedU1Hier.orderOkH_sound (show Tools.VedU1Hier.OrderOkH {P.design} {P.mod} {P.body} = true by decide)"
  let modsList := "[" ++ ", ".intercalate (kids.map fun k => s!"{k.nm.mod}") ++ "]"
  L := L.push s!"  have hmods : {P.design}.modules = {modsList} := by decide"
  L := L.push s!"  have hch : ∀ x ∈ {P.design}.modules, Tools.VedU1Contract.OrderStmt x := by"
  L := L.push s!"    rw [hmods]; intro x hx"
  L := L.push s!"    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx"
  let pat := " | ".intercalate (kids.map fun _ => "h")
  if kids.length == 0 then
    L := L.push s!"    exact absurd hx (by simp)"
  else
    L := L.push s!"    rcases hx with {pat}"
    for k in kids do
      L := L.push s!"    · subst h; exact {k.nm.thm}.2.2.2.1"
  L := L.push s!"  refine ⟨by decide, by decide, by decide, by decide, by decide, hord, hch, Tools.VedU1Hier.exists_arr _ _ hord hch hne, ?_⟩"
  L := L.push s!"  intro arr hadm"
  -- per kid facts
  for (k, i) in kidIdx do
    let G := declTerm k.decl k.nDom
    let K := k.nm
    L := L.push s!"  have hmem{i} : {K.mod} ∈ {P.design}.modules := by rw [hmods]; simp"
    L := L.push s!"  have hpw{i} := hadm.2.2 _ hmem{i}"
    L := L.push s!"  have hasg{i} : Tools.VedU1Hier.assignOnly {K.mod}.body = true := by decide"
    L := L.push s!"  have hclk{i} : {K.contract}.clkRst = none := by decide"
    L := L.push s!"  have hone{i} : {K.contract}.table.out.flat.length = 1 := by decide"
    L := L.push s!"  have hsucc{i} := Tools.VedU1Hier.child_succ {K.contract} {K.mod} {G} (arr {K.mod}) {K.thm} hpw{i}.1 hpw{i}.2 hasg{i} hclk{i}"
    let binders := " ".intercalate ((k.tbl.ins.zipIdx).map fun (p, j) => s!"(A{j} : {sigTy p})")
    let argsT := ", ".intercalate ((k.tbl.ins.zipIdx).map fun (_, j) => s!"A{j}")
    let obsL := ", ".intercalate ((k.tbl.ins.zipIdx).map fun (_, j) => s!"(A{j}.val t).toNat")
    let app := " ".intercalate ((k.tbl.ins.zipIdx).map fun (_, j) => s!"A{j}")
    let gApp := if k.tbl.ins.isEmpty then G else s!"({G} {app})"
    L := L.push s!"  have hrel{i} : ∀ {binders} (t : Nat), ({gApp}.val t).toNat = Tools.VedU1Hier.leafOut {K.mod} (arr {K.mod}) [{obsL}] := by"
    let tup := (k.tbl.ins.zipIdx).foldr (fun (_, j) acc => s!"(A{j}, {acc})") "()"
    L := L.push s!"    intro {" ".intercalate ((k.tbl.ins.zipIdx).map fun (_, j) => s!"A{j}")} t"
    L := L.push s!"    have h := Tools.VedU1Hier.child_rel_out {K.contract} {K.mod} {G} (arr {K.mod}) {K.thm} hpw{i}.1 hpw{i}.2 hasg{i} hclk{i} hone{i} {tup} t"
    L := L.push s!"    exact (List.cons.inj h).1"
  -- per instance facts
  let mut instNo := 0
  let mut hIs : Array String := #[]
  for s in m.body do
    match s with
    | .inst mn iname cs =>
      let some (k, i) := (kidIdx.find? fun (k, _) => k.c.name == mn) | pure ()
      let xs := k.c.inputs.map fun p => match cs.lookup p.name with | some (.ref x) => x | _ => "?"
      let y := match cs.lookup (outNameOf k.c) with | some (.ref y) => y | _ => "?"
      let envT := "(env : Sparkle.IR.Semantics.Env)"
      L := L.push s!"  have hI{instNo} : ∀ (we : Sparkle.IR.Semantics.WEnv) {envT}, Tools.VedU1Hier.instEval {P.design} (Tools.VedU1Hier.runAt {P.design} arr (Tools.VedU1Hier.fuelOf {P.design})) we {sq mn} {sq iname} {connsLit cs} env = some [({sq y}, Tools.VedU1Hier.leafOut {k.nm.mod} (arr {k.nm.mod}) [{", ".intercalate (xs.map fun x => s!"env {sq x}")}])] := by"
      L := L.push s!"    intro we env"
      L := L.push s!"    exact Tools.VedU1Hier.instEval_leaf {P.design} arr we {sq mn} {sq iname} {connsLit cs} {k.nm.mod} {strList xs} {sq y} env (by decide) (by decide) (by decide) (by decide) (by decide) hasg{i} hpw{i}.1 (by decide) hsucc{i}"
      hIs := hIs.push s!"hI{instNo}"
      instNo := instNo + 1
    | _ => pure ()
  let F := declTerm F nDom
  let hrels := ", ".intercalate ((List.range kids.length).map fun i => s!"hrel{i}")
  let hIl := ", ".intercalate hIs.toList
  L := L.push s!"  apply Tools.VedU1Hier.outputsH_of_step {P.contract} {P.mod} {P.design} arr {F} {P.outs} (by decide) (fun _ _ _ => True)"
  L := L.push s!"  · intro _ _; trivial"
  L := L.push s!"  · intro ins hok s st _"
  L := L.push s!"    have hin := hok.1 s"
  L := L.push s!"    simp [{P.contract}, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.Contract.dataInputs, {P.mod}, Tools.VedU1Contract.declWidth] at hin"
  L := L.push s!"    obtain ⟨E, hE, hP⟩ : ∃ E, Tools.VedU1Hier.evalAssignsI (Tools.VedU1Contract.declWidth {P.mod}) (Tools.VedU1Hier.instEval {P.design} (Tools.VedU1Hier.runAt {P.design} arr (Tools.VedU1Hier.fuelOf {P.design})) (Tools.VedU1Contract.declWidth {P.mod})) {P.body} (Tools.VedU1Contract.seedIn {P.mod} ins s st) = some E ∧ (∀ o ∈ {P.outs}, E o.name = Tools.VedU1Contract.srcOf {P.contract} {F} ins o.name s) := by"
  L := L.push s!"      simp [Tools.VedU1Hier.evalAssignsI, Tools.VedU1Hier.cellVals, {hIl}, {hrels}, {P.body}, {P.outs}, Tools.VedU1Contract.srcOf, Tools.VedU1Contract.contractOf, Tools.VedU1Contract.applyIns, {F}, Tools.VedU1Contract.seedIn, {P.mod}, Tools.VedU1Contract.PTy.sig, Tools.VedU1Contract.OTy.obs, Tools.VedU1Contract.PTy.obs, hin, Sparkle.IR.Semantics.evalExpr, Tools.VedU1Hier.upd]"
  L := L.push s!"    have hp : (arr {P.mod}).Perm {P.body} := hadm.1.trans hb0.1.symm"
  L := L.push s!"    exact ⟨E, [], Tools.VedU1Hier.stepH_of_b0 {P.design} arr {P.mod} {P.body} hp hadm.2.1 hb0.2.1 (fun s hs => hb0.2.2 s (hp.mem_iff.mp hs)) _ E hE, hP, trivial⟩"
  return "\n".intercalate L.toList

end Tools.VedU1HierEntry
