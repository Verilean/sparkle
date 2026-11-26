import Tests.Ved.U2HierCheck

/-!
# Statement pinning for H2a (reviewer condition 3)

The full types of `runHS_proj` / `ProjAt` and of the composed final statement `U2HStmt` are pinned
INDEPENDENTLY of their definitions: each is restated here from the design (docs/VED-HIER-H2-DESIGN.md
§2.4, §3) in primitive terms and proved by the lemma itself (so the lemma cannot be strengthened or
weakened without this file failing), and the printed types are fixed by `#guard_msgs`.

Controls, each shown FALSE (or refused) on the REAL synthesized design of `parTwo` (the constants
the entry registered, `parTwo.ved_mod` / `parTwo.ved_design`):
another path, another child, a wrong initial state, a one-cycle time shift, a missing
input/output correspondence, shared state; positive control: a consistent renaming of the
instance names.
-/

namespace Tests.Ved.U2HierPin

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics Sparkle.IR.Reorder
open Tools.VedU1Contract Tools.VedU1Hier Tools.VedU2Hier Tests.Ved.U2HierCheck

/-! ## The types, restated -/

theorem pin_ProjAt (we : WEnv) (c : Sparkle.IR.AST.Module) (cs : List (String × Sparkle.IR.AST.Expr))
    (i : String) (E Ec : Env) (S : HSt) (Sc : String → Nat) :
    ProjAt we c cs i E Ec S Sc ↔
      ((∀ p ∈ c.inputs, ∃ e, cs.lookup p.name = some e ∧ evalExpr we E e = some (Ec p.name)) ∧
       (∀ q ∈ c.outputs, ∃ x, cs.lookup q.name = some (Sparkle.IR.AST.Expr.ref x) ∧ E x = Ec q.name) ∧
       (∀ r ∈ regOuts c.body, S [i] r = Sc r)) := Iff.rfl

theorem pin_insCOf (we : WEnv) (cs : List (String × Sparkle.IR.AST.Expr)) (envs : List Env) :
    insCOf we cs envs = fun t n =>
      match envs[t]?, cs.lookup n with
      | some E, some e => (evalExpr we E e).getD 0
      | _, _ => 0 := rfl

theorem pin_runHS_proj : ∀ (d : Design) (arr : Sparkle.IR.AST.Module → List Stmt)
    (m : Sparkle.IR.AST.Module), HierShapeS d m = true → AdmArr d m arr →
    ∀ (inp : Nat → String → Nat) (K : Nat) (envs : List Env) (sts : List HSt),
      runHSTrace d arr m (seedFwd m K inp) K (st0H d m) = some (envs, sts) →
      ∀ (mn i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
        Stmt.inst mn i cs ∈ m.body →
        ∃ c cenvs cstates, findMod d mn = some c ∧
          runModuleTrace (declWidth c) (arr c) (seedFwd c K (insCOf (declWidth m) cs envs)) K
            (st0Of c) (fun _ _ => 0) = some (cenvs, cstates) ∧
          runModule (declWidth c) (arr c) (seedFwd c K (insCOf (declWidth m) cs envs)) K
            (st0Of c) (fun _ _ => 0) = some cenvs ∧
          ∀ t, t < K → ∃ E Ec S Sc, envs[t]? = some E ∧ cenvs[t]? = some Ec ∧ sts[t]? = some S ∧
            cstates[t]? = some Sc ∧
            ((∀ p ∈ c.inputs, ∃ e, cs.lookup p.name = some e ∧
                evalExpr (declWidth m) E e = some (Ec p.name)) ∧
             (∀ q ∈ c.outputs, ∃ x, cs.lookup q.name = some (Sparkle.IR.AST.Expr.ref x) ∧
                E x = Ec q.name) ∧
             (∀ r ∈ regOuts c.body, S [i] r = Sc r)) := @runHS_proj

/-- The composed final statement, restated in primitive terms. -/
theorem pin_U2HStmt (c : Contract) (m : Sparkle.IR.AST.Module) (d : Design) (f : c.table.Ty) :
    U2HStmt c m d f ↔
      (CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeS d m = true ∧
        regsOf m.body = [] ∧ WidthStmt c m ∧ (∃ b, OrderOkHS d m b = true) ∧
        (∀ x ∈ d.modules, OrderStmt x) ∧ (∃ arr, AdmArr d m arr) ∧
        ∀ arr, AdmArr d m arr → ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
          runHS d arr m (seedFwd m K ins) K (st0H d m) = some envs ∧
          ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧
            env o.name = srcOf c f ins o.name t) := Iff.rfl

/-- The semantics' definitions the statement rests on, pinned: the initial state, one cycle, the
simultaneous update and the run. -/
theorem pin_applyH (st : HSt) (ups : Ups) :
    applyH st ups = fun p n =>
      match ups.find? (fun u => u.1 == p) with
      | some u => applyNexts (st p) u.2 n
      | none => st p n := rfl

theorem pin_stepHS (d : Design) (arr : Sparkle.IR.AST.Module → List Stmt)
    (m : Sparkle.IR.AST.Module) (st : HSt) (env0 : Env) :
    stepHS d arr m st env0 =
      (if clkRstOk d m = true then do
        let envF ← evalAssignsI (declWidth m) (instEvalS d arr st (declWidth m)) (arr m) env0
        let nextsP ← regNexts (declWidth m) (fun _ _ => 0) (arr m) envF
        let nextsI ← (instDecls (arr m)).mapM (childNexts d arr (declWidth m) st envF)
        some (envF, ([], nextsP) :: nextsI)
      else none) := rfl

theorem pin_st0H (d : Design) (m : Sparkle.IR.AST.Module) :
    st0H d m = fun p =>
      match p with
      | [] => st0Of m
      | [i] =>
        match (instDecls m.body).find? (fun x => x.2.1 == i) with
        | some (mn, _, _) =>
          match findMod d mn with
          | some c => st0Of c
          | none => fun _ => 0
        | none => fun _ => 0
      | _ => fun _ => 0 := rfl

/-! ## The real synthesized design -/

local notation "M" => parTwo.ved_mod
local notation "D" => parTwo.ved_design
local notation "ACC" => parTwo.ved_child.Tests.Ved.U2HierCheck.accMod.ved_mod

/-- The checked arrangements the entry registered. -/
noncomputable def arrP (m : Sparkle.IR.AST.Module) (b : List Stmt)
    (cb : List Stmt := parTwo.ved_child.Tests.Ved.U2HierCheck.accMod.ved_body) :
    Sparkle.IR.AST.Module → List Stmt :=
  fun x => if x.name == m.name then b else if x.name == (ACC).name then cb else x.body

noncomputable def outsP (d : Design) (m : Sparkle.IR.AST.Module) (b : List Stmt) (st : HSt)
    (inp : Nat → String → Nat) (K : Nat)
    (cb : List Stmt := parTwo.ved_child.Tests.Ved.U2HierCheck.accMod.ved_body) :
    Option (List Nat) :=
  (runHS d (arrP m b cb) m (seedFwd m K inp) K st).map (·.map fun e => e "out")

/-- The declaration's values on `inpS` (checked against the declaration itself in
`Tests/Ved/U2HierCheck.lean`). -/
def decl : List Nat := [1, 249, 232, 206]

/-- BASELINE: the real design's closed stateful run is the declaration's. -/
example : outsP D M parTwo.ved_body (st0H D M) inpS 4 = some decl := by decide +kernel

def I0 : String := "_tmp_inst_Tests.Ved.U2HierCheck.accMod_0"
def I1 : String := "_tmp_inst_Tests.Ved.U2HierCheck.accMod_1"
def R : String := "_tmp_a_3"

/-! ## Control: ANOTHER PATH.  The two instances keep their register at DIFFERENT paths; reading
the other instance's path, or the root, is not the child's register. -/

noncomputable def statesP : Option (List (Nat × Nat × Nat)) :=
  (runHSTrace D (arrP M parTwo.ved_body) M (seedFwd M 4 inpS) 4 (st0H D M)).map
    (·.2.map fun s => (s [I0] R, s [I1] R, s [] R))

example : statesP = some [(0, 0, 0), (1, 10, 0), (3, 30, 0), (6, 60, 0)] := by decide +kernel

/-- another instance's path is not this instance's register state (they differ from cycle 1) ... -/
example : (statesP.map (·.map fun x => decide (x.1 = x.2.1))) = some [true, false, false, false] := by decide +kernel

/-- ... and the root path holds no register (0), not the child's. -/
example : (statesP.map (·.map fun x => decide (x.1 = x.2.2))) = some [true, false, false, false] := by decide +kernel

/-! ## Control: ANOTHER CHILD (`r' = r - x`: another module under the same name) -/

noncomputable def ACC1 : Sparkle.IR.AST.Module :=
  { ACC with body := (ACC).body.map fun s => match s with
    | .assign l (.op .add args) => .assign l (.op .sub args)
    | s => s }

noncomputable def D1 : Design := { D with modules := [ACC1] }

noncomputable def ACC1body : List Stmt :=
  parTwo.ved_child.Tests.Ved.U2HierCheck.accMod.ved_body.map fun s => match s with
    | .assign l (.op .add args) => .assign l (.op .sub args)
    | s => s

example : outsP D1 M parTwo.ved_body (st0H D1 M) inpS 4 ACC1body ≠ some decl := by decide +kernel

/-! ## Control: a WRONG INITIAL STATE (a state of 1 instead of the register init) -/

example : outsP D M parTwo.ved_body (fun p n => if p == [I0] && n == R then 1 else 0) inpS 4 ≠
    some decl := by decide +kernel

/-! ## Control: a ONE-CYCLE TIME SHIFT -/

/-- the run at cycle `t + 1` is not the declaration at cycle `t`, nor at `t - 1` ... -/
example : (outsP D M parTwo.ved_body (st0H D M) inpS 4).map (·.drop 1) ≠ some (decl.take 3) := by
  decide +kernel
example : (outsP D M parTwo.ved_body (st0H D M) inpS 4).map (·.take 3) ≠ some (decl.drop 1) := by
  decide +kernel

/-! ## Control: a MISSING INPUT/OUTPUT CORRESPONDENCE -/

def dropConn (p : String) : Stmt → Stmt
  | .inst mn i cs => .inst mn i (cs.filter fun q => q.1 != p)
  | s => s

/-- the first instance without its output connection: not a design (`HierShapeS`: the shape check is
what refuses it; the closed semantics itself would run with the undriven wire at its seed value and
its outputs are not the declaration's); without an input connection the semantics has no run
(`none`, never a 0 default) -/
noncomputable def Mout : Sparkle.IR.AST.Module :=
  { M with body := match (M).body with | s :: r => dropConn "out" s :: r | [] => [] }

noncomputable def Min : Sparkle.IR.AST.Module :=
  { M with body := match (M).body with | s :: r => dropConn "_gen_x" s :: r | [] => [] }

example : HierShapeS D Mout = false := by decide +kernel
example : HierShapeS D Min = false := by decide +kernel
example : outsP D Mout (match parTwo.ved_body with | s :: r => dropConn "out" s :: r | [] => [])
    (st0H D Mout) inpS 4 ≠ some decl := by decide +kernel
example : outsP D Min (match parTwo.ved_body with | s :: r => dropConn "_gen_x" s :: r | [] => [])
    (st0H D Min) inpS 4 = none := by decide +kernel

/-! ## Control: SHARED STATE.  Two instances with the same name share ONE path: not a design, and
the run is not the declaration's. -/

def sameName : Stmt → Stmt
  | .inst mn _ cs => .inst mn "u" cs
  | s => s

noncomputable def Mdup : Sparkle.IR.AST.Module := { M with body := (M).body.map sameName }

example : HierShapeS D Mdup = false := by decide +kernel
example : outsP D Mdup (parTwo.ved_body.map sameName) (st0H D Mdup) inpS 4 ≠ some decl := by decide +kernel

/-- A name-keyed (module-wide) state, the implementation error the path key rules out: all updates
land in every path, so both instances read the same register. -/
def applyHShared (st : HSt) (ups : Ups) : HSt :=
  fun p n => applyNexts (st p) (ups.flatMap (·.2)) n

def runHSShared (d : Design) (arr : Sparkle.IR.AST.Module → List Stmt) (m : Sparkle.IR.AST.Module)
    (seed : Nat → (String → Nat) → Env) : Nat → HSt → Option (List Env)
  | 0, _ => some []
  | k + 1, st => do
    let (envF, ups) ← stepHS d arr m st (seed k (restrictTo (regOuts (arr m)) (st [])))
    let rest ← runHSShared d arr m seed k (applyHShared st ups)
    some (envF :: rest)

example : (runHSShared D (arrP M parTwo.ved_body) M (seedFwd M 4 inpS) 4 (st0H D M)).map
    (·.map fun e => e "out") ≠ some decl := by decide +kernel

/-! ## Positive control: a CONSISTENT RENAMING of the instance names -/

noncomputable def Mrn : Sparkle.IR.AST.Module := { M with body := renameInsts (M).body }

example : HierShapeS D Mrn = true := by decide +kernel
example : outsP D Mrn (renameInsts parTwo.ved_body) (st0H D Mrn) inpS 4 = some decl := by decide +kernel

/-! ## Axioms, MACHINE-checked: the closure of every pinned statement is within the standard three -/

run_cmd Lean.Elab.Command.liftCoreM do
  for n in [``pin_ProjAt, ``pin_insCOf, ``pin_runHS_proj, ``pin_U2HStmt, ``pin_applyH, ``pin_stepHS,
      ``pin_st0H] do
    Tests.Ved.U2HierCheck.std3Only n

/-! ## The printed types, fixed (fully qualified names) -/

set_option pp.fullNames true

/--
info: Tools.VedU2Hier.runHS_proj : ∀ (d : Sparkle.IR.AST.Design) (arr : Sparkle.IR.AST.Module → List Sparkle.IR.AST.Stmt)
  (m : Sparkle.IR.AST.Module),
  Tools.VedU2Hier.HierShapeS d m = Bool.true →
    Tools.VedU1Hier.AdmArr d m arr →
      ∀ (inp : Nat → String → Nat) (K : Nat) (envs : List Sparkle.IR.Semantics.Env) (sts : List Tools.VedU2Hier.HSt),
        Tools.VedU2Hier.runHSTrace d arr m (Tools.VedU1Contract.seedFwd m K inp) K (Tools.VedU2Hier.st0H d m) =
            Option.some (envs, sts) →
          ∀ (mn i : String) (cs : List (String × Sparkle.IR.AST.Expr)),
            Sparkle.IR.AST.Stmt.inst mn i cs ∈ m.body →
              ∃ c cenvs cstates,
                Tools.VedU1Hier.findMod d mn = Option.some c ∧
                  (Tools.VedU2Hier.runModuleTrace (Tools.VedU1Contract.declWidth c) (arr c)
                        (Tools.VedU1Contract.seedFwd c K
                          (Tools.VedU2Hier.insCOf (Tools.VedU1Contract.declWidth m) cs envs))
                        K (Tools.VedU2Hier.st0Of c) fun x x_1 => 0) =
                      Option.some (cenvs, cstates) ∧
                    (Sparkle.IR.Semantics.runModule (Tools.VedU1Contract.declWidth c) (arr c)
                          (Tools.VedU1Contract.seedFwd c K
                            (Tools.VedU2Hier.insCOf (Tools.VedU1Contract.declWidth m) cs envs))
                          K (Tools.VedU2Hier.st0Of c) fun x x_1 => 0) =
                        Option.some cenvs ∧
                      ∀ (t : Nat),
                        t < K →
                          ∃ E Ec S Sc,
                            envs[t]? = Option.some E ∧
                              cenvs[t]? = Option.some Ec ∧
                                sts[t]? = Option.some S ∧
                                  cstates[t]? = Option.some Sc ∧
                                    Tools.VedU2Hier.ProjAt (Tools.VedU1Contract.declWidth m) c cs i E Ec S Sc
-/
#guard_msgs in
#check @Tools.VedU2Hier.runHS_proj

/--
info: Tools.VedU2Hier.ProjAt : Sparkle.IR.Semantics.WEnv →
  Sparkle.IR.AST.Module →
    List (String × Sparkle.IR.AST.Expr) →
      String → Sparkle.IR.Semantics.Env → Sparkle.IR.Semantics.Env → Tools.VedU2Hier.HSt → (String → Nat) → Prop
-/
#guard_msgs in
#check @Tools.VedU2Hier.ProjAt

/--
info: Tools.VedU2Hier.U2HStmt : (c : Tools.VedU1Contract.Contract) →
  Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → c.table.Ty → Prop
-/
#guard_msgs in
#check @Tools.VedU2Hier.U2HStmt

/--
info: Tools.VedU2Hier.OutputsOnHS : (c : Tools.VedU1Contract.Contract) →
  Sparkle.IR.AST.Module → Sparkle.IR.AST.Design → (Sparkle.IR.AST.Module → List Sparkle.IR.AST.Stmt) → c.table.Ty → Prop
-/
#guard_msgs in
#check @Tools.VedU2Hier.OutputsOnHS

/--
info: Tests.Ved.U2HierCheck.parTwo.ved_u1 : Tools.VedU2Hier.U2HStmt Tests.Ved.U2HierCheck.parTwo.ved_contract M D
  Tests.Ved.U2HierCheck.parTwo
-/
#guard_msgs in
#check @Tests.Ved.U2HierCheck.parTwo.ved_u1

end Tests.Ved.U2HierPin
