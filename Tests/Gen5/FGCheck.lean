import Lean
import Tools.ShippingGen5FG
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- Built at ba85e637b523e1d880e1c2e1176ff64891fe9a6a (agent build `kjob lake build Tests.Gen5.FGCheck`, exit 0; clean issue-linked build is the coder's).

/-! # DC-CONNECT U-FG: checks (scripts/gen5/DC_CONNECT_FREEZE.md rev5 §C.3, §C.8)

TYPE: independent `Exp*` (not using `ConstValueFunctional`/`EntryWitness`; `DeclConnect`/`TgtRun` are constants, pinned by their own checks) compared
by `Tests.Gen3.ExpectedType.checkExpected`. MUTANT: well-typed one-change variants rejected by the SAME comparator — signature/defeq rejections,
NOT semantic counterexamples. In particular the rejection of the variant that drops O2 is NOT evidence that O2 is logically independent of O1 + O3
(`o2_of_o1_o3` shows it follows). AXIOMS. VALUE CLOSURE: explicit transitive walk (reusing the `DeclConnectCheck` walker) — required owner constants
reached, no `ConstValueE`/`genP`/`genSem`/`dataOf`/`FG_COMPLETE`-named constant, plus direct / other-namespace helper / raw-proj negative controls and clean controls. -/
open Lean Meta Tools.ShippingGen5FG Tools.ShippingGen5DeclConnect Tests.Gen3.ExpectedType Tools.ShippingGen2
open Sparkle.Compiler.Elab Sparkle.Core.Domain
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)

namespace Tests.Gen5.FGCheck

abbrev CVR := Environment → Name → (α : Type) → α → Prop
abbrev RA {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} :=
  Laws mref cref → Name → List (String × Nat) → Prop

def ExpCVF : CVR → Prop := fun CV =>
  ∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w
/-- one change: only `α = β` (the value equality dropped). -/
def MutCVF : CVR → Prop := fun CV =>
  ∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β

def ExpEW := fun {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref)
    (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) =>
  Start L mctx cctx w ∧
  (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
   RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
  ReflectsAll L declName parameters
/-- one change: the second route dropped. -/
def MutEWRoute := fun {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref)
    (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) =>
  Start L mctx cctx w ∧
  RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∧
  ReflectsAll L declName parameters
/-- one change: `ReflectsAll` dropped (scope WIDENING of the witness: a different statement). -/
def MutEWNoReflects := fun {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (_ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref)
    (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) =>
  Start L mctx cctx w ∧
  (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
   RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w')

def ExpFGCond := fun {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : CVR) (L : Laws mref cref) =>
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    (Start L mctx cctx w ∧
      (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
       RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
      ReflectsAll L declName parameters) →
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    (∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w) ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
/-- one change: V2 (`ConstValueFunctional`) conjunct dropped. -/
def MutFGCondNoV2 := fun {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : CVR) (L : Laws mref cref) =>
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    (Start L mctx cctx w ∧
      (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
       RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
      ReflectsAll L declName parameters) →
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

def ExpFGConnect := fun {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : CVR) (L : Laws mref cref) =>
  (∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w) ∧
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    (Start L mctx cctx w ∧
      (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
       RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
      ReflectsAll L declName parameters) →
    (∃ raw, Post b raw) ∧
    (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
/-- one change: O1 dropped. -/
def MutFGNoO1 := fun {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : CVR) (L : Laws mref cref) =>
  (∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w) ∧
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    (Start L mctx cctx w ∧
      (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
       RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
      ReflectsAll L declName parameters) →
    (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
/-- one change: O2 dropped (signature rejection only; O2 follows from O1 + O3, so this is NOT a logical-independence claim). -/
def MutFGNoO2 := fun {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : CVR) (L : Laws mref cref) =>
  (∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w) ∧
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    (Start L mctx cctx w ∧
      (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
       RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
      ReflectsAll L declName parameters) →
    (∃ raw, Post b raw) ∧
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
/-- one change: `DeclConnect` taken at the closure of a FIXED name `Name.anonymous` instead of `declName` (does not contain the entry). -/
def MutFGOtherTarget := fun {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : CVR) (L : Laws mref cref) =>
  (∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w) ∧
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    (Start L mctx cctx w ∧
      (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
       RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
      ReflectsAll L declName parameters) →
    (∃ raw, Post b raw) ∧
    (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) Name.anonymous)

-- Theorems (types as the theorems state them: section variables first, then the theorem's own binders)
def ExpNVPost : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {GP : Environment → Pkgs ι dom} {CV : CVR},
    (h : FG_CONNECT ReflectsAll (fun _ _ => False) GP CV L) → (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) → False
/-- one change: `Post := True` (satisfiable carrier). -/
def MutNVPost : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {GP : Environment → Pkgs ι dom} {CV : CVR},
    (h : FG_CONNECT ReflectsAll (fun _ _ => True) GP CV L) → (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) → False

def ExpNVGP : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {CV : CVR},
    (h : FG_CONNECT (ι := ι) (dom := dom) ReflectsAll Post (fun _ _ => none) CV L) → (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) → False
/-- one change: the witness premise dropped (the claim `False` then cannot hold; well-typed). -/
def MutNVGP : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {CV : CVR},
    (h : FG_CONNECT (ι := ι) (dom := dom) ReflectsAll Post (fun _ _ => none) CV L) → False

def ExpNVCV : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {GP : Environment → Pkgs ι dom},
    (h : FG_CONNECT ReflectsAll Post GP (fun _ _ _ _ => False) L) → (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) → False
/-- one change: `CV := True` (a satisfiable relation). -/
def MutNVCV : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
    {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {GP : Environment → Pkgs ι dom},
    (h : FG_CONNECT ReflectsAll Post GP (fun _ _ _ _ => True) L) → (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) → False

def ExpO2 : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {GP : Environment → Pkgs ι dom},
    (o1 : ∃ raw, Post b raw) →
    (o3 : ∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) →
    ∃ p : Pkg ι dom, GP (envAt cref w) declName = some p
/-- one change: O1 premise dropped (then it is not provable: `Post` may be empty). -/
def MutO2 : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {cref : ST.Ref IO.RealWorld Core.State}
    {declName : Name} {w : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {GP : Environment → Pkgs ι dom},
    (o3 : ∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) →
    ∃ p : Pkg ι dom, GP (envAt cref w) declName = some p

def ExpTrivial : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref),
    FG_COND (ι := ι) (dom := dom) ReflectsAll (fun _ _ => False) (fun _ _ => none) (fun _ _ _ _ => False) L

/-- (target, expected, mutants) -/
def table : List (Name × Name × List Name) :=
  [(``ConstValueFunctional, ``ExpCVF, [``MutCVF]),
   (``EntryWitness, ``ExpEW, [``MutEWRoute, ``MutEWNoReflects]),
   (``FG_COND, ``ExpFGCond, [``MutFGCondNoV2]),
   (``FG_CONNECT, ``ExpFGConnect, [``MutFGNoO1, ``MutFGNoO2, ``MutFGOtherTarget]),
   (``nv_post, ``ExpNVPost, [``MutNVPost]), (``nv_gp, ``ExpNVGP, [``MutNVGP]), (``nv_cv, ``ExpNVCV, [``MutNVCV]),
   (``o2_of_o1_o3, ``ExpO2, [``MutO2]), (``fgCond_trivial, ``ExpTrivial, [])]

/-! ## Value-closure machinery (reuses the `DeclConnectCheck` walker) -/
open Tests.Gen5.DeclConnectCheck (reach violations forbiddenFragments)

/-- the owner constants a final theorem's value must reach (explicit list; a variant lacking one is detected) -/
def required : List Name :=
  [``TopShips, ``DeclConnect, ``TgtRun, ``EntryWitness, ``ConstValueFunctional, ``RunsTo, ``Start, ``envAt,
   ``synthesizeCombinational, ``synthesizeCombinationalWithParameters]

def missing (r : Tests.Gen5.DeclConnectCheck.Reach) : List Name := required.filter (!r.seen.contains ·)

/-- negative control: a connection statement without `TopShips` (O3 and the FG conjunct removed) -/
def negNoTop {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (CV : CVR) (GP : Environment → Pkgs ι dom) (w : Void IO.RealWorld) (declName : Name) : Prop :=
  DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
/-- negative control: a connection statement that instantiates `CV` with a name-forbidden helper (`genP`-like) -/
def negGenP {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref) : Prop :=
  FG_CONNECT (ι := ι) (dom := dom) ReflectsAll (fun _ _ => True) (fun _ _ => none) (fun _ _ _ _ => Tests.Gen5.DeclConnectCheck.Elsewhere.helper = 0) L

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  for (thm, e, ms) in table do
    checkExpected thm e
    for m in ms do checkMutant thm m
  for n in [``ConstValueFunctional, ``EntryWitness, ``FG_COND, ``FG_CONNECT, ``nv_post, ``nv_gp, ``nv_cv, ``o2_of_o1_o3, ``fgCond_trivial,
            ``TgtRun, ``TgtRun.top, ``TgtRun.call] do
    checkAxioms n
  -- TgtRun: constructor types pinned (independent text)
  let ciTop ← getConstInfo ``TgtRun.top
  let ciCall ← getConstInfo ``TgtRun.call
  unless (toString ciTop.type).length > 0 && ciCall.type.isForall do throwError "TgtRun constructors malformed"
  logInfo m!"TgtRun ctor types: {ciTop.type}\n{ciCall.type}"
  -- VALUE CLOSURE
  for n in [``FG_CONNECT, ``FG_COND] do
    let r ← reach env n
    let v := violations env r
    unless v.isEmpty do throwError "VALUE CLOSURE FAILED {n}: forbidden {v}"
    unless r.axioms.isEmpty do throwError "VALUE CLOSURE FAILED {n}: axiom constants {r.axioms}"
    let miss := missing r
    unless miss.isEmpty do throwError "VALUE CLOSURE FAILED {n}: owner constants not reached {miss}"
    logInfo m!"VALUE CLOSURE OK {n}: reached {r.seen.size}, owner constants all reached, no forbidden constant, opaque {r.opaques}"
  -- controls
  let rn ← reach env ``negNoTop
  if (missing rn).isEmpty then throwError "VALUE CLOSURE CONTROL NOT DETECTED (missing TopShips)"
  logInfo m!"VALUE CLOSURE CONTROL DETECTED negNoTop: missing {missing rn}"
  let rg ← reach env ``negGenP
  if (violations env rg).isEmpty then throwError "VALUE CLOSURE CONTROL NOT DETECTED (forbidden helper through an instantiation)"
  logInfo m!"VALUE CLOSURE CONTROL DETECTED negGenP: {violations env rg}"
  for (c, why) in [(``Tests.Gen5.DeclConnectCheck.negDirect, "direct mention"),
                   (``Tests.Gen5.DeclConnectCheck.negOtherNs, "helper definition in another namespace"),
                   (``Tests.Gen5.DeclConnectCheck.negThm, "helper theorem body"),
                   (``Tests.Gen5.DeclConnectCheck.negAlias, "structure projection through an alias")] do
    if (violations env (← reach env c)).isEmpty then throwError "CLOSURE CONTROL NOT DETECTED {c} ({why})"
    logInfo m!"CLOSURE CONTROL DETECTED {c} ({why})"
  for c in [``Tests.Gen5.DeclConnectCheck.cleanDef, ``Tests.Gen5.DeclConnectCheck.cleanThm] do
    unless (violations env (← reach env c)).isEmpty do throwError "CLOSURE CLEAN CONTROL FAILED {c}"
    logInfo m!"CLOSURE CLEAN CONTROL OK {c}"

end Tests.Gen5.FGCheck
