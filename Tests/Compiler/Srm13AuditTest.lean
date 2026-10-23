import Tests.Compiler.Srm13ParentTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm13AuditExpected
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingSrm13Supply
-- BUILT (unit SRM13): dev runs a2 (Supply), a4 (ParentTest), b4 (AuditTest) all exit 0; the final-SHA rebuild is in REPORT-SRM13.md.
-- SCOPE (SRM13 audits).  (1) PREMISE TABLE of every new theorem (binders: index, binderInfo, name, Prop-or-data, type) EQUAL to `Tests/Compiler/Srm13AuditExpected.lean` and `scripts/srm13/PREMISES.txt`, one `S13THM` marker per theorem, literal count guard;
-- THREE negative fixtures (semantic ` ∧ True`, added data binder, reordered binders), each non-vacuous and rejected.  REGENERATION: `./.cluster/qbuild.sh build Tests.Compiler.Srm13AuditTest > LOG 2>&1; python3 scripts/srm13/gen_audit.py LOG`.
-- (2) INDEPENDENT EXPECTED TYPES, written by hand in this file as strings, elaborated and compared with `isDefEq` to the theorem types / the corollaries' replaced binders; a MUTATED expected string is rejected; the new residual-fact Props are NOT defeq to the premises they stand next to
-- (not relabellings); each corollary lacks the binders `seed`/`hseedB`/`hst`/`hkids` and keeps every other SRM11 binder (checked against the SRM11 theorem's binder types).
-- (3) CLOSURE: standard axioms; forbidden old-form roots (with control); the SRM11 theorem and the sufficiency theorems are in each corollary's closure.  NOT guaranteed: that the hypotheses hold for the machine's run.
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm13AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the new SRM13 theorems audited -/
def audited13 : List Name :=
  [``Tools.ShippingSrm13Supply.seedB_of_seedIn,
   ``Tools.ShippingSrm13Supply.seedB_checkedOptimize,
   ``Tools.ShippingSrm13Supply.seedIn_not_bounded,
   ``Tools.ShippingSrm13Supply.hseedB_not_forced,
   ``Tools.ShippingSrm13Supply.bounded_of_regsAtInit,
   ``Tools.ShippingSrm13Supply.bounded_not_forced,
   ``Tools.ShippingSrm13Supply.invN0_not_forced,
   ``Tools.ShippingSrm13Supply.invN_of_resetN_fitTree,
   ``Tools.ShippingSrm13Supply.moduleByName_name,
   ``Tools.ShippingSrm13Supply.kidReset_of_resetNk,
   ``Tools.ShippingSrm13Supply.kidInvN_of_resetNk,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_viaReset,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_viaReset,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_viaReset,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_viaReset]

/-- the corollaries: (new, SRM11 original, depth) -/
def corollaries : List (Name × Name × Nat) :=
  [(``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH_viaReset, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH, 2),
   (``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH_viaReset, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH, 1),
   (``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_viaReset, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_noB, 2),
   (``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_viaReset, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_noB, 1)]

/-- elaborate a hand-written term string -/
def elabStr (s : String) : TermElabM Expr := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .error e => throwError "SRM13 AUDIT FAILED: expected string does not parse: {e}\n{s}"
  | .ok stx =>
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

/-- is the theorem's type defeq to the hand-written expected statement? -/
def typeIs (thm : Name) (s : String) : TermElabM Bool := do
  let ci ← getConstInfo thm
  let e ← elabStr s
  isDefEq ci.type e

/-- the independently written expected statements of the generic theorems (hand-written, NOT produced by a script from the theorems) -/
def expectedTypes : List (Name × String) :=
  [(``Tools.ShippingSrm13Supply.seedB_of_seedIn,
    "∀ (o : Sparkle.IR.AST.Module) (ins : Nat → String → Nat), (∀ (t : Nat) (x : String), x ∈ o.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS o x) → ∀ (k : Nat) (st : String → Nat), Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) st → Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) (Tools.ShippingSeqOptSoundness.seedIn o ins k st)"),
   (``Tools.ShippingSrm13Supply.seedB_checkedOptimize,
    "∀ (b : Sparkle.IR.AST.Module) (ins : Nat → String → Nat), (∀ (t : Nat) (x : String), x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x) → ∀ (k : Nat) (st : String → Nat), Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) st → Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) (Tools.ShippingSeqOptSoundness.seedIn b ins k st)"),
   (``Tools.ShippingSrm13Supply.seedIn_not_bounded,
    "∀ (o : Sparkle.IR.AST.Module) (ins : Nat → String → Nat) (t : Nat) (x : String), x ∈ o.inputs.map (·.name) → 2 ^ Tools.ShippingDesignSV.weS o x ≤ ins t x → ¬ ∀ (k : Nat) (st : String → Nat), Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) st → Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) (Tools.ShippingSeqOptSoundness.seedIn o ins k st)"),
   (``Tools.ShippingSrm13Supply.hseedB_not_forced,
    "∀ (o : Sparkle.IR.AST.Module), ∃ seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env, ¬ ∀ (k : Nat) (st : String → Nat), Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) st → Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) (seed k st)"),
   (``Tools.ShippingSrm13Supply.bounded_of_regsAtInit,
    "∀ (o : Sparkle.IR.AST.Module) (st : String → Nat), (∀ (r : String) c rs inp (init : Int), Sparkle.IR.AST.Stmt.register r c rs inp init ∈ o.body → st r = init.toNat) → (∀ (r : String) c rs inp (init : Int), Sparkle.IR.AST.Stmt.register r c rs inp init ∈ o.body → init.toNat < 2 ^ Tools.ShippingDesignSV.weS o r) → (∀ (x : String), (¬ ∃ c rs inp init, Sparkle.IR.AST.Stmt.register x c rs inp init ∈ o.body) → st x < 2 ^ Tools.ShippingDesignSV.weS o x) → Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) st"),
   (``Tools.ShippingSrm13Supply.bounded_not_forced,
    "∀ (o : Sparkle.IR.AST.Module), ∃ st : String → Nat, ¬ Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS o) st"),
   (``Tools.ShippingSrm13Supply.invN0_not_forced,
    "∀ (C : String → Option (Sparkle.IR.AST.Module × Sparkle.IR.Semantics.WEnv)) (gc : Sparkle.IR.AST.Module), ∃ ks : Tools.ShippingHierStateG.KT 0, ¬ Tools.ShippingDesignSVBounds.InvN C 0 gc ks"),
   (``Tools.ShippingSrm13Supply.invN_of_resetN_fitTree,
    "∀ (D : Sparkle.IR.AST.Design) (n : Nat) (o : Sparkle.IR.AST.Module) (ks : Tools.ShippingHierStateG.KT n), Tools.ShippingMachineDepth.ResetN D n o ks → Tools.ShippingSrm13Supply.FitTree (Tools.ShippingMachineLinked.childMap D.modules) n o ks → Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) n o ks"),
   (``Tools.ShippingSrm13Supply.moduleByName_name,
    "∀ (ms : List Sparkle.IR.AST.Module) (mn : String) (gc : Sparkle.IR.AST.Module), Sparkle.IR.Machine.moduleByName ms mn = some gc → gc.name = mn"),
   (``Tools.ShippingSrm13Supply.kidReset_of_resetNk,
    "∀ (n : Nat) (raw o : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (kids : String → Tools.ShippingHierStateG.KT n), Tools.ShippingMachineShipsDepth.ResetNk n raw D kids → (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ o.body → Sparkle.IR.AST.Stmt.inst mn iname conns ∈ raw.body) → ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (gc : Sparkle.IR.AST.Module) (gcwe : Sparkle.IR.Semantics.WEnv), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ o.body → Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) → Tools.ShippingMachineDepth.ResetN D n gc (kids iname)"),
   (``Tools.ShippingSrm13Supply.kidInvN_of_resetNk,
    "∀ (n : Nat) (raw o : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) (kids : String → Tools.ShippingHierStateG.KT n), Tools.ShippingMachineShipsDepth.ResetNk n raw D kids → (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ o.body → Sparkle.IR.AST.Stmt.inst mn iname conns ∈ raw.body) → (∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (gc : Sparkle.IR.AST.Module) (gcwe : Sparkle.IR.Semantics.WEnv), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ o.body → Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) → Tools.ShippingSrm13Supply.FitTree (Tools.ShippingMachineLinked.childMap D.modules) n gc (kids iname)) → ∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (gc : Sparkle.IR.AST.Module) (gcwe : Sparkle.IR.Semantics.WEnv), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ o.body → Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) → Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) n gc (kids iname)")]

/-- hand-expanded definitions of the residual facts: the def must be defeq to the written formula -/
def expandedDefs : List (String × String) :=
  [("Tools.ShippingSrm13Supply.RegsAtInit o st", "∀ (r : String) c rs inp (init : Int), Sparkle.IR.AST.Stmt.register r c rs inp init ∈ o.body → st r = init.toNat"),
   ("Tools.ShippingSrm13Supply.RegsFit o", "∀ (r : String) c rs inp (init : Int), Sparkle.IR.AST.Stmt.register r c rs inp init ∈ o.body → init.toNat < 2 ^ Tools.ShippingDesignSV.weS o r"),
   ("Tools.ShippingSrm13Supply.NonRegBounded o st", "∀ (x : String), (¬ ∃ c rs inp init, Sparkle.IR.AST.Stmt.register x c rs inp init ∈ o.body) → st x < 2 ^ Tools.ShippingDesignSV.weS o x")]

/-- the replaced binders of a corollary at depth `N`, by name -/
def replacedBinders (N : Nat) : List (String × String) :=
  [("ins", "Nat → String → Nat"),
   ("hin", "∀ (t : Nat) (x : String), x ∈ b.inputs.map (·.name) → ins t x < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x"),
   ("hst₁", "∀ (r : String) c rs inp (init : Int), Sparkle.IR.AST.Stmt.register r c rs inp init ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body → s.st r = init.toNat"),
   ("hst₂", "∀ (r : String) c rs inp (init : Int), Sparkle.IR.AST.Stmt.register r c rs inp init ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body → init.toNat < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) r"),
   ("hst₃", "∀ (x : String), (¬ ∃ c rs inp init, Sparkle.IR.AST.Stmt.register x c rs inp init ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body) → s.st x < 2 ^ Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b) x"),
   ("hrk", s!"∀ (iname : String) (mc : Sparkle.IR.AST.Module), (∃ conns, Sparkle.IR.AST.Stmt.inst mc.name iname conns ∈ raw.body) → Sparkle.IR.Machine.moduleByName D.modules mc.name = some mc → Tools.ShippingMachineDepth.ResetN D {N} mc (s.kids iname)"),
   ("hO", "∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body → Sparkle.IR.AST.Stmt.inst mn iname conns ∈ raw.body"),
   ("hfit", s!"∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (gc : Sparkle.IR.AST.Module) (gcwe : Sparkle.IR.Semantics.WEnv), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body → Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) → Tools.ShippingSrm13Supply.FitTree (Tools.ShippingMachineLinked.childMap D.modules) {N} gc (s.kids iname)"),
   ("hrun", s!"Tools.ShippingHierStateG.runModuleTG (Tools.ShippingHierStateG.KSn (Tools.ShippingMachineLinked.childMap D.modules) {N}) (Sparkle.IR.RegDedup.declWidth (Sparkle.IR.OptCheck.checkedOptimize b)) (Tools.ShippingMachineLinked.childMap D.modules) (Sparkle.IR.OptCheck.checkedOptimize b).body (Tools.ShippingSeqOptSoundness.seedIn b ins) T' s = some envs")]

/-- the premises the replaced binders stand next to (original SRM11 binder types, same context) -/
def originalPremises (N : Nat) : List (String × String × String) :=
  [("hin", "hseedB", "∀ (k : Nat) (st : String → Nat), Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) st → Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) (Tools.ShippingSeqOptSoundness.seedIn b ins k st)"),
   ("hst₁", "hst", "Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) s.st"),
   ("hst₂", "hst", "Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) s.st"),
   ("hst₃", "hst", "Sparkle.IR.Semantics.Bounded (Tools.ShippingDesignSV.weS (Sparkle.IR.OptCheck.checkedOptimize b)) s.st"),
   ("hfit", "hkids", s!"∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (gc : Sparkle.IR.AST.Module) (gcwe : Sparkle.IR.Semantics.WEnv), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body → Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) → Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) {N} gc (s.kids iname)"),
   ("hrk", "hkids", s!"∀ (mn iname : String) (conns : List (String × Sparkle.IR.AST.Expr)) (gc : Sparkle.IR.AST.Module) (gcwe : Sparkle.IR.Semantics.WEnv), Sparkle.IR.AST.Stmt.inst mn iname conns ∈ (Sparkle.IR.OptCheck.checkedOptimize b).body → Tools.ShippingMachineLinked.childMap D.modules mn = some (gc, gcwe) → Tools.ShippingDesignSVBounds.InvN (Tools.ShippingMachineLinked.childMap D.modules) {N} gc (s.kids iname)")]


abbrev Row := Nat × String × String × Bool × String

/-- normalised binder name -/
def normName (n : String) : String := if (n.splitOn "_hyg").length > 1 then "_anon" else n

/-- rows `(index, binderInfo, name, isProp, type)` of the binders of a theorem's type -/
def premiseRows (thm : Name) : MetaM (List Row) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut rows : List Row := []
    let mut i := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let isP ← Meta.isProp d.type
      let bi := match d.binderInfo with
        | .implicit => "implicit" | .strictImplicit => "strict" | .instImplicit => "inst" | .default => "explicit"
      rows := rows ++ [(i, bi, normName d.userName.toString, isP, ((← ppExpr d.type).pretty 100000).replace "\n" " ")]
      i := i + 1
    return rows

/-- the text line of a row (the format of `scripts/srm13/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S13{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

/-- EXACT comparison of two whole tables: `none` iff equal, else the first difference -/
def tableDiff (a e : List (Name × List Row)) : Option String := Id.run do
  if a.length != e.length then return some s!"{a.length} theorems vs {e.length} expected"
  for ((n, rs), (n', rs')) in a.zip e do
    if n != n' then return some s!"theorem {n} vs expected {n'}"
    if rs.length != rs'.length then return some s!"{n}: {rs.length} binders vs {rs'.length} expected"
    for (r, r') in rs.zip rs' do
      if r != r' then return some s!"{n}: binder {r.1} differs: {rowLine n r} vs expected {rowLine n r'}"
  return none

/-- mutation 1: SEMANTIC change of the type of the first Prop binder (same index, binderInfo, name): the type string gets ` ∧ True` appended -/
def mutType (t : List (Name × List Row)) : List (Name × List Row) :=
  match t.findIdx? (fun (_, rs) => rs.any (·.2.2.2.1)) with
  | none => t
  | some k => t.mapIdx fun j (n, rs) =>
    if j == k then
      let idx := (rs.findIdx? (·.2.2.2.1)).getD 0
      (n, rs.mapIdx fun i r => if i == idx then (r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2 ++ " ∧ True") else r)
    else (n, rs)

/-- mutation 2: add a data binder to the first theorem -/
def mutAdd (t : List (Name × List Row)) : List (Name × List Row) :=
  t.mapIdx fun j (n, rs) => if j == 0 then (n, rs ++ [(rs.length, "implicit", "extraBinder", false, "Nat")]) else (n, rs)

/-- mutation 3: swap the first two binders of the first theorem that has two -/
def mutSwap (t : List (Name × List Row)) : List (Name × List Row) :=
  match t.findIdx? (fun (_, rs) => rs.length ≥ 2) with
  | none => t
  | some k => t.mapIdx fun j (n, rs) =>
    if j == k then (match rs with | r0 :: r1 :: rest => (n, r1 :: r0 :: rest) | _ => (n, rs)) else (n, rs)

/-- does a hypothesis of `thm` restate its conclusion (reducible `isDefEq`)? -/
def restatesConclusion (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs concl => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if (← Meta.isProp d.type) then
        if (← withReducible (isDefEq d.type concl)) then return true
    return false

/-- does a hypothesis of `thm` mention the uniform children's check? -/
def mentionsUniformUNUSED (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.type.getUsedConstants.any (fun c => c == ``Tools.ShippingDesignSV.kidsPass || c == ``Tools.ShippingChecksDesign.kidCheck || c == ``Tools.ShippingDesignSVBack.outsCheck || c == ``Tools.ShippingDesignSV.designCheck || c == ``Tools.ShippingSrm6Sem.SVBoundsH || c == ``Tools.ShippingDesignSV.SVBounds) then return true
    return false


/-- run `k` in the telescope of `thm`'s type -/
def inTelescope {α : Type} (thm : Name) (k : Array Expr → Expr → TermElabM α) : TermElabM α := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs concl => k xs concl

/-- the fvar of the binder with user name `nm` -/
def binderNamed (xs : Array Expr) (nm : String) : MetaM (Option Expr) := do
  for x in xs do
    if (← x.fvarId!.getDecl).userName.toString == nm then return some x
  return none

end Tests.Compiler.Srm13AuditTest

open Tests.Compiler.Srm13AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  unless (← restatesConclusion ``Tests.Compiler.Srm13AuditTest.wrapper_mutation) do throwError "SRM13 AUDIT FAILED: the wrapper control was not caught"
  unless audited13.length == 15 do throwError "SRM13 AUDIT FAILED: audited13 has {audited13.length} theorems, expected exactly 15"
  -- (1) premise table
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited13 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S13THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S13THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM13 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  unless Tests.Compiler.Srm13AuditExpected.expectedRows.length == 15 do throwError "SRM13 AUDIT FAILED: the expected table has {Tests.Compiler.Srm13AuditExpected.expectedRows.length} theorem entries, expected exactly 15"
  match tableDiff actual Tests.Compiler.Srm13AuditExpected.expectedRows with
  | some msg => throwError "SRM13 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm13AuditExpected.lean: {msg}"
  | none => pure ()
  let txt ← IO.FS.readFile "scripts/srm13/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM13 AUDIT FAILED: scripts/srm13/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- negative fixtures
  do
    let mt := mutType actual
    let mut changed : List (Name × Row × Row) := []
    unless mt.length == actual.length do throwError "SRM13 AUDIT FAILED: fixture 1 changed the number of theorems"
    for ((n, rs), (n', rs')) in actual.zip mt do
      unless n == n' && rs.length == rs'.length do throwError "SRM13 AUDIT FAILED: fixture 1 changed the shape of {n}"
      for (r, r') in rs.zip rs' do
        if r != r' then changed := changed ++ [(n, r, r')]
    match changed with
    | [(n, r, r')] =>
      unless r'.2.2.2.1 do throwError "SRM13 AUDIT FAILED: fixture 1 mutated row of {n} is not a Prop binder"
      unless r.2.2.2.1 && r'.1 == r.1 && r'.2.1 == r.2.1 && r'.2.2.1 == r.2.2.1 do throwError "SRM13 AUDIT FAILED: fixture 1 changed index/binderInfo/name/isProp of binder {r.1} of {n}"
      unless r'.2.2.2.2 != r.2.2.2.2 && r'.2.2.2.2.endsWith " ∧ True" && r'.2.2.2.2.length == r.2.2.2.2.length + 7 do throwError "SRM13 AUDIT FAILED: fixture 1 type string is not visibly changed"
      logInfo m!"S13FIXTURE1|{n}|binder {r.1} ({r.2.2.1})|original type: {r.2.2.2.2}|mutated type: {r'.2.2.2.2}"
      match tableDiff mt Tests.Compiler.Srm13AuditExpected.expectedRows with
      | some msg => unless (msg.splitOn s!"binder {r.1} differs").length > 1 && (msg.splitOn (toString n)).length > 1 do throwError "SRM13 AUDIT FAILED: fixture 1 rejection does not name the mutated binder: {msg}"
      | none => throwError "SRM13 AUDIT FAILED: the comparator ACCEPTED fixture 1"
    | _ => throwError "SRM13 AUDIT FAILED: fixture 1 changed {changed.length} rows, expected exactly 1"
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM13 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm13AuditExpected.expectedRows with
    | none => throwError "SRM13 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S13FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S13TABLE|{audited13.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm13/PREMISES.txt"
  -- (2) independent expected types
  unless expectedTypes.length == 11 do throwError "SRM13 AUDIT FAILED: expectedTypes has {expectedTypes.length} entries, expected 11"
  for (thm, s) in expectedTypes do
    unless (← typeIs thm s) do throwError "SRM13 AUDIT FAILED: the type of {thm} is NOT defeq to its independently written expected statement"
    logInfo m!"S13EXPECTED|{thm}|defeq to the hand-written statement"
  -- one mutation of an expected string must be rejected (control: the unmutated string is accepted above)
  do
    let some s := expectedTypes.lookup ``Tools.ShippingSrm13Supply.seedB_checkedOptimize | throwError "SRM13 AUDIT FAILED: no expected string"
    let s' := s.replace "ins t x < 2 ^" "ins t x ≤ 2 ^"
    if s' == s then throwError "SRM13 AUDIT FAILED: the type mutation did not change the string (vacuous)"
    if (← typeIs ``Tools.ShippingSrm13Supply.seedB_checkedOptimize s') then throwError "SRM13 AUDIT FAILED: isDefEq ACCEPTED a mutated expected type"
    logInfo m!"S13TYPEMUT|seedB_checkedOptimize: mutated expected type (< replaced by ≤) rejected by isDefEq"
  -- hand-expanded definitions of the residual facts
  for (d, s) in expandedDefs do
    let e1 ← elabStr s!"fun (o : Sparkle.IR.AST.Module) (st : String → Nat) => ({d})"
    let e2 ← elabStr s!"fun (o : Sparkle.IR.AST.Module) (st : String → Nat) => ({s})"
    unless (← isDefEq e1 e2) do throwError "SRM13 AUDIT FAILED: {d} is not defeq to its hand-expanded formula"
    logInfo m!"S13DEF|{d}|defeq to the hand-expanded formula"
  -- the corollaries
  for (new, old, N) in corollaries do
    let oldTy := (← getConstInfo old).type
    inTelescope new fun xs concl => do
      -- no premise of SRM11 left, nor the old seed
      for nm in ["seed", "hseedB", "hst", "hkids"] do
        if (← binderNamed xs nm).isSome then throwError "SRM13 AUDIT FAILED: {new} still has the binder {nm}"
      -- replaced binders are exactly the hand-written ones
      for (nm, s) in replacedBinders N do
        let some x ← binderNamed xs nm | throwError "SRM13 AUDIT FAILED: {new} lacks the binder {nm}"
        let e ← elabStr s
        unless (← isDefEq (← inferType x) e) do throwError "SRM13 AUDIT FAILED: binder {nm} of {new} is not defeq to its hand-written type"
      -- NOT relabellings: each residual-fact binder is not defeq to the premise it stands next to
      for (nm, pr, s) in originalPremises N do
        let some x ← binderNamed xs nm | throwError "SRM13 AUDIT FAILED: {new} lacks the binder {nm}"
        let e ← elabStr s
        if (← isDefEq (← inferType x) e) then throwError "SRM13 AUDIT FAILED: binder {nm} of {new} IS defeq to the SRM11 premise {pr} (relabelling)"
        logInfo m!"S13NOTRELABEL|{new}|{nm} is not defeq to {pr}"
      -- the conclusion
      let some tgt ← binderNamed xs "T'" | throwError "SRM13 AUDIT FAILED: no T'"
      let concStr := if (toString new).endsWith "svBoundsH_viaReset"
        then s!"Tools.ShippingSrm6Sem.SVBoundsH (Tools.ShippingMachineLinked.childMap D.modules) rk {N} (Sparkle.IR.OptCheck.checkedOptimize b) (Tools.ShippingSeqOptSoundness.seedIn b ins) T' s envs"
        else s!"Tools.ShippingSrm6Sem.DesignSVH (Tools.ShippingMachineLinked.childMap D.modules) rk {N} (Sparkle.IR.OptCheck.checkedOptimize b) (Tools.ShippingSeqOptSoundness.seedIn b ins) T' s envs"
      let ce ← elabStr concStr
      unless (← isDefEq concl ce) do throwError "SRM13 AUDIT FAILED: conclusion of {new} is not the hand-written one"
      let _ := tgt
      -- every other binder of the SRM11 theorem is kept: the first binders (before `seed`) have the same types
      let mut oT := oldTy
      let mut i := 0
      let mut kept := 0
      repeat
        match oT with
        | .forallE nm d b _ =>
          if nm.toString == "seed" then break
          unless (← isDefEq d (← inferType xs[i]!)) do throwError "SRM13 AUDIT FAILED: binder {i} ({nm}) of {new} differs from the SRM11 theorem"
          oT := b.instantiate1 xs[i]!
          i := i + 1
          kept := kept + 1
        | _ => throwError "SRM13 AUDIT FAILED: SRM11 theorem {old} has no binder seed"
      logInfo m!"S13KEPT|{new}|the first {kept} binders equal those of {old}"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM13 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM13 AUDIT FAILED: control walk found no old-form constant"
  for thm in audited13 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM13 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM13 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    stdAxioms thm
    logInfo m!"S13CLOSURE|{thm}|standard axioms; closure {cl.size} constants; no old-form boundary"
  for (new, old, _) in corollaries do
    let cl ← depClosure new
    for need in [old, ``Tools.ShippingSrm13Supply.seedB_checkedOptimize, ``Tools.ShippingSrm13Supply.bounded_of_regsAtInit, ``Tools.ShippingSrm13Supply.kidInvN_of_resetNk,
        ``Tools.ShippingSrm13Supply.invN_of_resetN_fitTree, ``Tools.ShippingSrm13Supply.kidReset_of_resetNk, ``Tools.ShippingSrm6Sem.design_sv_runH] do
      if need == ``Tools.ShippingSrm6Sem.design_sv_runH && (toString new).endsWith "svBoundsH_viaReset" then continue
      unless cl.contains need do throwError "SRM13 AUDIT FAILED: {need} is not in the closure of {new}"
    logInfo m!"S13CORCLOSURE|{new}|contains {old} and the sufficiency theorems"

end
