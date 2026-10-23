import Tests.Compiler.Srm14RankTest
import Tests.Compiler.Srm7RankTest
import Tests.Compiler.ChildVertAuditTest
import Tests.Compiler.Srm14AuditExpected
import Tools.ShippingKidsChildIfaceM
import Tools.ShippingSrm11Bounds
-- BUILT/UNBUILT: see REPORT-SRM14.md (dev runs and the final-SHA rebuild are recorded there).
-- SCOPE (SRM14 audits).  (1) PREMISE TABLE of the four `*_computed` corollaries (binders: index, binderInfo, name, Prop-or-data, type; `S14THM` marker per theorem), compared EXACTLY with `Tests/Compiler/Srm14AuditExpected.lean` and `scripts/srm14/PREMISES.txt`;
-- literal theorem-count guard; THREE NEGATIVE FIXTURES (semantic ` ∧ True`, added data binder, reordered binders), each non-vacuous and rejected.  REGENERATION: `./.cluster/qbuild.sh build Tests.Compiler.Srm14AuditTest > LOG 2>&1; python3 scripts/srm14/gen_audit.py LOG`.
-- (1b) INVENTORY (`S14INV` lines, compared EXACTLY with `scripts/srm14/INVENTORY.txt`): every binder of the SRM11 instance theorems and of the SRM5 `topshare*_hcheck`/SRM7 `*_hcheck_computed` theorems that is the rank table or mentions it, with its supplier.
-- (2) EXPECTED TYPE: a FULL statement `Exp_*` (section ExpStmt), DERIVED from the original SRM11 statement (Tests/Compiler/Srm11ParentTest.lean) by the committed substitution `rk := rkOf gM 4` / `rkOf gQ 3` and deletion of the binders rk, hrkmem, hrT, hrW, hrW3, hrP, hrQ, hrL, everything else verbatim (scripts/srm14/gen_exp_from_srm11.py reads ONLY the SRM11 file and prints the lists), is `isDefEq` to each corollary type, a wrong-fuel mutation of it is rejected; and an independently built expected type (original SRM11 type, rank binders dropped, `rk := rkOf g F`) is `isDefEq` to each corollary's type; the corollaries have no binder mentioning `rk`/`rkOf` and no rank binder name.
-- (3) CLOSURE: standard axioms; no old-form root (control); each corollary's closure contains the SRM11 theorem it calls and the SRM7 theorems `rkOf_mem`, `rkOf_decl` and the decided ranks of its graph; whether an SRM12 constant is in the closure is LOGGED (it is not used).
set_option Elab.async false
set_option autoImplicit false
section
open Lean Elab Command Meta

namespace Tests.Compiler.Srm14AuditTest

/-- a hand-made MUTATION for the binder audit's control: a theorem whose single hypothesis IS its conclusion -/
theorem wrapper_mutation (p : Prop) (h : p) : p := h

/-- the audited SRM14 theorems -/
def audited14 : List Name :=
  [``Tests.Compiler.Srm14RankTest.topshareM_svBoundsH_computed,
   ``Tests.Compiler.Srm14RankTest.topshareQ_svBoundsH_computed,
   ``Tests.Compiler.Srm14RankTest.topshareM_designSVH_noB_computed,
   ``Tests.Compiler.Srm14RankTest.topshareQ_designSVH_noB_computed]

/-- the instance theorems of SRM11 and the SRM5 / SRM7 theorems that take (or compute) the rank table: inventoried, not new -/
def inventoried : List Name :=
  [``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_noB, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_noB,
   ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_hcheck, ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_hcheck,
   ``Tests.Compiler.Srm7RankTest.topshareM_hcheck_computed, ``Tests.Compiler.Srm7RankTest.topshareQ_hcheck_computed]

/-- the binder names that carry the rank table or a rank fact -/
def rankNames : List String := ["rk", "hrkmem", "hrT", "hrW", "hrW3", "hrP", "hrQ", "hrL"]

/-- the SUPPLIER of a rank binder for the COMPUTED table (graph `gM`/`gQ` of Srm7RankTest) -/
def supplier (n : String) : String :=
  match n with
  | "rk" => "rkOf g F (Tools.ShippingSrm7Rank.rkOf; g = gM/gQ read from machineData.shape.instTagged)"
  | "hrkmem" => "Tools.ShippingSrm7Rank.rkOf_mem"
  | "hrT" => "Tools.ShippingSrm7Rank.rkOf_decl + Srm7RankTest.gM_top/gQ_top (decide)"
  | "hrW" => "Tools.ShippingSrm7Rank.rkOf_decl + Srm7RankTest.gM_wrap (decide)"
  | "hrW3" => "Tools.ShippingSrm7Rank.rkOf_decl + Srm7RankTest.gM_wrap3 (decide)"
  | "hrP" => "Tools.ShippingSrm7Rank.rkOf_decl + Srm7RankTest.gQ_wrapP (decide)"
  | "hrQ" => "Tools.ShippingSrm7Rank.rkOf_decl + Srm7RankTest.gQ_wrapQ (decide)"
  | "hrL" => "Tools.ShippingSrm7Rank.rkOf_decl + Srm7RankTest.gM_leaf/gQ_leaf (decide)"
  | _ => "none"

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

/-- the text line of a row (the format of `scripts/srm14/PREMISES.txt`) -/
def rowLine (thm : Name) (r : Row) : String :=
  s!"S14{if r.2.2.2.1 then "PREM" else "DATA"}|{thm}|{r.1}|{r.2.1}|{r.2.2.1}|{r.2.2.2.2}"

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
def mentionsUniform (thm : Name) : MetaM Bool := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.type.getUsedConstants.any (fun c => c == ``Tools.ShippingDesignSV.kidsPass || c == ``Tools.ShippingChecksDesign.kidCheck || c == ``Tools.ShippingDesignSVBack.outsCheck || c == ``Tools.ShippingDesignSV.designCheck || c == ``Tools.ShippingSrm6Sem.SVBoundsH || c == ``Tools.ShippingDesignSV.SVBounds) then return true
    return false

/-- inventory lines: each binder that is a rank name or whose type mentions the binder `rk`, with its supplier ("none" when not a known rank binder) -/
def invLines (thm : Name) : MetaM (List String) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut rkId : Option FVarId := none
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName.toString == "rk" then rkId := some x.fvarId!
    let mut out : List String := []
    let mut i := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      let nm := d.userName.toString
      let mentions := match rkId with | some r => (d.type.containsFVar r) | none => false
      if rankNames.contains nm || mentions then
        out := out ++ [s!"S14INV|{thm}|{i}|{nm}|{supplier nm}|{((← ppExpr d.type).pretty 100000).replace "\n" " "}"]
      i := i + 1
    return out

/-- the independently built EXPECTED type of the corollary `cor` of `orig`: `orig`'s type with the rank binders dropped and `rk := rk'`; compared with `isDefEq` (default transparency) -/
def expectedTypeOk (orig cor : Name) (rk' : Expr) : MetaM Bool := do
  let oi ← getConstInfo orig
  let ci ← getConstInfo cor
  forallTelescope oi.type fun xs concl => do
    let mut rkF : Option Expr := none
    let mut keep : Array Expr := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName.toString == "rk" then rkF := some x
      else if rankNames.contains d.userName.toString then pure ()
      else keep := keep.push x
    match rkF with
    | none => return false
    | some r =>
      -- no kept binder may mention the table (else the substitution below would not be the whole story)
      for x in keep do
        if (← x.fvarId!.getDecl).type.containsFVar r.fvarId! then return false
      unless xs.size == keep.size + 6 do return false
      let e ← mkForallFVars keep (concl.replaceFVar r rk')
      return (← isDefEq e ci.type)

section ExpStmt
open Lean Meta
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingChildInvA Tools.ShippingChildFresh
open Tools.ShippingChildCacheA Tools.ShippingChildRunAKids Tools.ShippingChildInv Sparkle.IR.AST Sparkle.IR.Machine
open Sparkle.Compiler.Elab Tools.ShippingChildBndCore Tools.ShippingChildVCA
open Sparkle.IR.OptCheck (checkedOptimize)
open Sparkle.IR.RefineCheck (mergeChecked)
open Tools.ShippingMachineLinked (childMap)
open Tests.Compiler.SharedLeafMemKidTest Tests.Compiler.SharedLeafMemKidRunTest Tests.Compiler.SharedLeafMemKidEntryTest
open Tools.ShippingSrm5Height Tools.ShippingSrm6Sem Tools.ShippingSrm11Bounds
open Tools.ShippingHierStateG (KT KSn KState runModuleTG)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingDesignSVBounds (InvN)
open Sparkle.IR.Semantics (Bounded)
open Tools.ShippingSrm7Rank Tests.Compiler.Srm7RankTest
open Tests.Compiler.SharedLeafMemKidIfaceTest

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

-- expected FULL statements of the four corollaries, derived from the SRM11 statements (not from SRM14 text) by scripts/srm14/gen_exp_from_srm11.py: substitution rk := rkOf gM 4 / rkOf gQ 3, deletion of the rank binders; compared to the theorem types by isDefEq below
-- BEGIN EXPSTMT
def Exp_topshareM_svBoundsH_computed : Prop :=
  ∀ (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 2 gc (s.kids iname)),
    SVBoundsH (childMap D.modules) (rkOf gM 4) 2 (checkedOptimize b) seed T' s envs

def Exp_topshareM_designSVH_noB_computed : Prop :=
  ∀ (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (entryL : MachineDefines mctx mref cctx cref ``leafM leafM.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapM wrapM.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapM3 wrapM3.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareM topshareM.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareM [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 2)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 2) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 2 gc (s.kids iname)),
    DesignSVH (childMap D.modules) (rkOf gM 4) 2 (checkedOptimize b) seed T' s envs

def Exp_topshareQ_svBoundsH_computed : Prop :=
  ∀ (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 1 gc (s.kids iname)),
    SVBoundsH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) seed T' s envs

def Exp_topshareQ_designSVH_noB_computed : Prop :=
  ∀ (O : RefLawsAOps MkRefd mref cref) (T : RefLawsATele O.quiet mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (hR0 : MachineDefines mctx mref cctx cref ``leafP leafP.machineData.shape)
    (hcl : ∀ (mc : Lean.Meta.Context) (cc : Lean.Core.Context), MachineCloses mc mref cc cref ``leafP leafP.machineData.shape)
    (entry₁ : MachineDefines mctx mref cctx cref ``wrapP wrapP.machineData.shape)
    (entry₂ : MachineDefines mctx mref cctx cref ``wrapQ wrapQ.machineData.shape)
    (entry : MachineDefines mctx mref cctx cref ``topshareQ topshareQ.machineData.shape)
    {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hcore : RunsTo (synthesizeCombinationalCore ``topshareQ [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨ b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (hw : JQC O 0 w)
    (seed : Nat → (String → Nat) → Sparkle.IR.Semantics.Env) (T' : Nat) (s : KState (KT 1)) (envs : List Sparkle.IR.Semantics.Env)
    (hrun : runModuleTG (KSn (childMap D.modules) 1) (declWidth (checkedOptimize b)) (childMap D.modules)
      (checkedOptimize b).body seed T' s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) st →
      Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) (seed k st))
    (hst : Bounded (Tools.ShippingDesignSV.weS (checkedOptimize b)) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ (checkedOptimize b).body →
      childMap D.modules mn = some (gc, gcwe) → InvN (childMap D.modules) 1 gc (s.kids iname)),
    DesignSVH (childMap D.modules) (rkOf gQ 3) 1 (checkedOptimize b) seed T' s envs
-- END EXPSTMT
end ExpStmt

end Tests.Compiler.Srm14AuditTest

open Tests.Compiler.Srm14AuditTest in
open Tests.Compiler.ChildVertAuditTest in
run_cmd liftTermElabM do
  -- (2) CONTROL: the binder audit REJECTS the hand-made mutation, and ACCEPTS a real height theorem
  unless (← restatesConclusion ``Tests.Compiler.Srm14AuditTest.wrapper_mutation) do throwError "SRM14 AUDIT FAILED: the wrapper control was not caught"
  -- LITERAL fixed-count guard, independent of the generated expected file
  unless audited14.length == 4 do throwError "SRM14 AUDIT FAILED: audited14 has {audited14.length} theorems, expected exactly 4"
  -- (1)+(2) premise table (EXACT comparison) and binder audit
  let mut actual : List (Name × List Row) := []
  let mut lines : List String := []
  for thm in audited14 do
    let rows ← premiseRows thm
    actual := actual ++ [(thm, rows)]
    logInfo m!"S14THM|{thm}|{rows.length}"
    lines := lines ++ [s!"S14THM|{thm}|{rows.length}"]
    for r in rows do
      logInfo m!"{rowLine thm r}"
      lines := lines ++ [rowLine thm r]
    if (← restatesConclusion thm) then throwError "SRM14 AUDIT FAILED: a hypothesis of {thm} restates its conclusion"
  -- (1b) INVENTORY (machine-generated; compared EXACTLY with scripts/srm14/INVENTORY.txt)
  unless inventoried.length == 8 do throwError "SRM14 AUDIT FAILED: inventoried has {inventoried.length} theorems, expected exactly 8"
  let mut inv : List String := []
  for thm in inventoried do
    let ls ← invLines thm
    for l in ls do
      logInfo m!"{l}"
    inv := inv ++ ls
  -- the whole table equals the committed expected table, EXACTLY
  unless Tests.Compiler.Srm14AuditExpected.expectedRows.length == 4 do throwError "SRM14 AUDIT FAILED: the expected table has {Tests.Compiler.Srm14AuditExpected.expectedRows.length} theorem entries, expected exactly 4"
  match tableDiff actual Tests.Compiler.Srm14AuditExpected.expectedRows with
  | some msg => throwError "SRM14 AUDIT FAILED: the premise table differs from Tests/Compiler/Srm14AuditExpected.lean: {msg}"
  | none => pure ()
  -- the committed text view equals the table line for line
  let txt ← IO.FS.readFile "scripts/srm14/PREMISES.txt"
  let fileLines := (txt.splitOn "\n").filter (· != "")
  unless fileLines == lines do
    throwError "SRM14 AUDIT FAILED: scripts/srm14/PREMISES.txt differs from the regenerated table ({fileLines.length} lines vs {lines.length})"
  -- NEGATIVE FIXTURES: each mutation of the table is a DIFFERENT table and is REJECTED by the comparator
  -- fixture 1 is SEMANTIC: exactly one row differs, it is still a Prop binder with the same index/binderInfo/name, and its type string visibly differs
  do
    let mt := mutType actual
    let mut changed : List (Name × Row × Row) := []
    unless mt.length == actual.length do throwError "SRM14 AUDIT FAILED: fixture 1 changed the number of theorems"
    for ((n, rs), (n', rs')) in actual.zip mt do
      unless n == n' && rs.length == rs'.length do throwError "SRM14 AUDIT FAILED: fixture 1 changed the shape of {n}"
      for (r, r') in rs.zip rs' do
        if r != r' then changed := changed ++ [(n, r, r')]
    match changed with
    | [(n, r, r')] =>
      unless r'.2.2.2.1 do throwError "SRM14 AUDIT FAILED: fixture 1 mutated row of {n} is not a Prop binder"
      unless r.2.2.2.1 && r'.1 == r.1 && r'.2.1 == r.2.1 && r'.2.2.1 == r.2.2.1 do throwError "SRM14 AUDIT FAILED: fixture 1 changed index/binderInfo/name/isProp of binder {r.1} of {n}"
      unless r'.2.2.2.2 != r.2.2.2.2 && r'.2.2.2.2.endsWith " ∧ True" && r'.2.2.2.2.length == r.2.2.2.2.length + 7 do throwError "SRM14 AUDIT FAILED: fixture 1 type string is not visibly changed"
      logInfo m!"S14FIXTURE1|{n}|binder {r.1} ({r.2.2.1})|original type: {r.2.2.2.2}|mutated type: {r'.2.2.2.2}"
      match tableDiff mt Tests.Compiler.Srm14AuditExpected.expectedRows with
      | some msg => unless (msg.splitOn s!"binder {r.1} differs").length > 1 && (msg.splitOn (toString n)).length > 1 do throwError "SRM14 AUDIT FAILED: fixture 1 rejection does not name the mutated binder: {msg}"
      | none => throwError "SRM14 AUDIT FAILED: the comparator ACCEPTED fixture 1"
    | _ => throwError "SRM14 AUDIT FAILED: fixture 1 changed {changed.length} rows, expected exactly 1"
  for (nm, mt) in [("changed Prop binder type", mutType actual), ("added data binder", mutAdd actual), ("reordered binders", mutSwap actual)] do
    if mt == actual then throwError "SRM14 AUDIT FAILED: the fixture '{nm}' did not change the table (vacuous)"
    match tableDiff mt Tests.Compiler.Srm14AuditExpected.expectedRows with
    | none => throwError "SRM14 AUDIT FAILED: the comparator ACCEPTED the fixture '{nm}'"
    | some msg => logInfo m!"S14FIXTURE|{nm}|rejected: {msg}"
  logInfo m!"S14TABLE|{audited14.length} theorems, {lines.length} binders: equal to the committed table and to scripts/srm14/PREMISES.txt"
  for thm in audited14 do
    if (← mentionsUniform thm) then throwError "SRM14 AUDIT FAILED: a hypothesis of {thm} mentions the uniform children's check"
  let invTxt ← IO.FS.readFile "scripts/srm14/INVENTORY.txt"
  let invFile := (invTxt.splitOn "\n").filter (· != "")
  unless invFile == inv do
    throwError "SRM14 AUDIT FAILED: scripts/srm14/INVENTORY.txt differs from the regenerated inventory ({invFile.length} lines vs {inv.length})"
  -- every inventoried SRM11 instance theorem has exactly the 5 rank-fact binders besides `rk`, each with a supplier; none lacks one
  unless (inv.filter fun l => (l.splitOn "|none|").length > 1).isEmpty do throwError "SRM14 AUDIT FAILED: a rank-related binder has no supplier: see S14INV lines with `none`"
  -- (2) EXPECTED TYPES (independently built, isDefEq)
  for (orig, cor, g, F) in [(``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH, ``Tests.Compiler.Srm14RankTest.topshareM_svBoundsH_computed, ``Tests.Compiler.Srm7RankTest.gM, 4),
      (``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH, ``Tests.Compiler.Srm14RankTest.topshareQ_svBoundsH_computed, ``Tests.Compiler.Srm7RankTest.gQ, 3),
      (``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_noB, ``Tests.Compiler.Srm14RankTest.topshareM_designSVH_noB_computed, ``Tests.Compiler.Srm7RankTest.gM, 4),
      (``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_noB, ``Tests.Compiler.Srm14RankTest.topshareQ_designSVH_noB_computed, ``Tests.Compiler.Srm7RankTest.gQ, 3)] do
    let rk' ← mkAppM ``Tools.ShippingSrm7Rank.rkOf #[mkConst g, mkNatLit F]
    unless (← expectedTypeOk orig cor rk') do throwError "SRM14 AUDIT FAILED: the expected type of {cor} (from {orig}, rank binders dropped, rk := rkOf {g} {F}) is not defeq to its type"
    -- control: the WRONG table (other graph / other fuel) is not accepted
    let wrong ← mkAppM ``Tools.ShippingSrm7Rank.rkOf #[mkConst g, mkNatLit (F + 1)]
    if (← expectedTypeOk orig cor wrong) then throwError "SRM14 AUDIT FAILED: control: the expected type with the wrong fuel was accepted for {cor}"
    -- SRM11-derived FULL expected statement `Exp_<cor>` (section ExpStmt) is defeq to the corollary's type; the same with the wrong fuel is rejected
    let expName : Name := Name.mkStr `Tests.Compiler.Srm14AuditTest ("Exp_" ++ cor.getString!)
    let eci ← getConstInfo expName
    let corTy := (← getConstInfo cor).type
    lambdaBoundedTelescope eci.value! 4 fun xs body => do
      let full ← mkForallFVars xs body
      unless (← isDefEq full corTy) do throwError "SRM14 AUDIT FAILED: the SRM11-derived full statement {expName} is not defeq to the type of {cor}"
      let mutBody := body.replace fun e => if e == rk' then some wrong else none
      if mutBody == body then throwError "SRM14 AUDIT FAILED: the mutated full statement of {cor} did not change (vacuous)"
      if (← isDefEq (← mkForallFVars xs mutBody) corTy) then throwError "SRM14 AUDIT FAILED: the MUTATED full statement (wrong fuel) of {cor} was accepted"
    -- no binder of the corollary is a rank name or mentions a rank table
    forallTelescope (← getConstInfo cor).type fun xs _ => do
      for x in xs do
        let d ← x.fvarId!.getDecl
        if rankNames.contains d.userName.toString then throwError "SRM14 AUDIT FAILED: {cor} still has the rank binder {d.userName}"
        if d.type.getUsedConstants.any (fun c => c == ``Tools.ShippingSrm7Rank.rkOf) then throwError "SRM14 AUDIT FAILED: a binder of {cor} mentions rkOf"
    logInfo m!"S14TYPE|{cor}|expected type from {orig} with rk := rkOf {g} {F} is defeq; wrong-fuel control rejected"
  -- (3) closure audit
  let forbidden : List Name := [`Tools.ShippingChildInv.RealChild, `Tools.ShippingChildInv.InvW, `Tools.ShippingMachineRan.MachineRan,
      `Tools.ShippingChildInv.MachineClosesAt, `Tools.ShippingMemKid.Kid, `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM,
      `Tools.ShippingChildInv.ChildBnd, `Tools.ShippingChildInv.StartV, `Tools.ShippingGenKid.GenKid,
      `Tools.ShippingKidFacts.KidFacts, `Tools.ShippingMachineDepthRun.MachineRunNC, `Tools.ShippingSharedLeafCoh.CacheClosed]
  for f in forbidden do
    unless (← getEnv).contains f do throwError "SRM14 AUDIT FAILED: the forbidden root {f} does not exist (vacuous audit)"
  let ctl ← depClosure `Tools.ShippingKidsChildIfaceM.kidsChild_of_realM
  unless (ctl.toList.filter fun c => forbidden.any (·.isPrefixOf c)).length > 0 do throwError "SRM14 AUDIT FAILED: control walk found no old-form constant"
  for thm in audited14 do
    let cl ← depClosure thm
    let bad := hits cl
    unless bad.isEmpty do throwError "SRM14 AUDIT FAILED: old RefLaws boundary in the closure of {thm}: {bad}"
    let bad2 := cl.toList.filter fun c => forbidden.any (·.isPrefixOf c)
    unless bad2.isEmpty do throwError "SRM14 AUDIT FAILED: old-form boundary in the closure of {thm}: {bad2}"
    let isM := (thm.toString.splitOn "topshareM").length > 1
    let callee : Name := if (thm.toString.splitOn "svBoundsH").length > 1 then
        (if isM then ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_svBoundsH else ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_svBoundsH)
      else (if isM then ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareM_designSVH_noB else ``Tests.Compiler.SharedLeafMemKidIfaceTest.topshareQ_designSVH_noB)
    unless cl.contains callee do throwError "SRM14 AUDIT FAILED: {callee} not in the closure of {thm}"
    for c in [``Tools.ShippingSrm7Rank.rkOf_mem, ``Tools.ShippingSrm7Rank.rkOf_decl, ``Tools.ShippingSrm5Height.hcheck, ``Tools.ShippingSrm11Bounds.svBoundsH_of_checks] do
      unless cl.contains c do throwError "SRM14 AUDIT FAILED: {c} not in the closure of {thm}"
    for c in (if isM then [``Tests.Compiler.Srm7RankTest.gM_top, ``Tests.Compiler.Srm7RankTest.gM_wrap, ``Tests.Compiler.Srm7RankTest.gM_wrap3, ``Tests.Compiler.Srm7RankTest.gM_leaf]
              else [``Tests.Compiler.Srm7RankTest.gQ_top, ``Tests.Compiler.Srm7RankTest.gQ_wrapP, ``Tests.Compiler.Srm7RankTest.gQ_wrapQ, ``Tests.Compiler.Srm7RankTest.gQ_leaf]) do
      unless cl.contains c do throwError "SRM14 AUDIT FAILED: the decided rank {c} is not in the closure of {thm}"
    if cl.contains ``Tools.ShippingDesignSVBounds.svBounds_of_checks then throwError "SRM14 AUDIT FAILED: the uniform svBounds_of_checks is in the closure of {thm}"
    let s12 := cl.toList.filter fun c => (`Tools.ShippingSrm12Corr).isPrefixOf c
    logInfo m!"S14INFO|{thm}|SRM12 constants in the closure (logged only; SRM12 is not used by this unit): {s12.length}"
    stdAxioms thm
    logInfo m!"S14CLOSURE|{thm}|standard axioms; closure {cl.size} constants; SRM11 callee, SRM7 rkOf_mem/rkOf_decl and the decided ranks present; no old-form boundary"

end
