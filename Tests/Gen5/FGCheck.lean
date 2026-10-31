import Lean
import Tools.ShippingGen5FG
import Tests.Gen3.ExpectedType
import Tests.Gen5.DeclConnectCheck
set_option autoImplicit false
-- Built at dd1aafd0b264f5610abea861c8f6f0ff959fd314 (agent build `kjob lake build Tests.Gen5.FGCheck`, exit 0, 748 jobs; clean issue-linked build is the coder's; previous clean build fgv-058c3cde exit 0, 748 jobs, at 058c3cde). Counts by category: TYPE 9 (theorem/definition level; constructor checks NOT included) + CTOR TYPE 2 (`TgtRun.top`/`call`, independent telescope at reducible transparency); MUTANT 11 (theorem level) + CTOR MUTANT 6 (`top` 1; `call`: ord 2, parent reach 2, pkg correspondence 1); AXIOMS 12. All signature/defeq rejections, NOT semantic counterexamples.

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

/-! ## TgtRun constructors: independent complete telescopes, compared at reducible transparency
Written from the freeze sentence "least predicate: `declName`, and the ordinary callees (origin `.ord`, no `child?`) of the instances of reached names". -/

def ExpTop : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name}, TgtRun P declName declName
def ExpCall : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name} {c : Name} {q : Pkg ι dom}
    (hc : TgtRun P declName c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
    (ord : (q.d.shape.instOrigins.getD k .ord).child? = none), TgtRun P declName (q.d.shape.insts[k]'hk).1
/-- one change: the top constructor reaches a different name -/
def MutTop : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name}, TgtRun P declName Name.anonymous
/-- one change (ord): the `.ord`/no-child condition on the origin replaced by `child?` being present -/
def MutCallOrd : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name} {c : Name} {q : Pkg ι dom}
    (hc : TgtRun P declName c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
    (ord : (q.d.shape.instOrigins.getD k .ord).child?.isSome = true), TgtRun P declName (q.d.shape.insts[k]'hk).1
/-- one change (ord, drop): no origin condition at all -/
def MutCallNoOrd : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name} {c : Name} {q : Pkg ι dom}
    (hc : TgtRun P declName c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length),
    TgtRun P declName (q.d.shape.insts[k]'hk).1
/-- one change (reaching the parent): the parent is reached from the root `declName` itself instead of from the reached `c` -/
def MutCallParent : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name} {c : Name} {q : Pkg ι dom}
    (hc : TgtRun P c c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
    (ord : (q.d.shape.instOrigins.getD k .ord).child? = none), TgtRun P declName (q.d.shape.insts[k]'hk).1
/-- one change (reaching the parent, drop): no reachability premise -/
def MutCallNoParent : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name} {c : Name} {q : Pkg ι dom}
    (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
    (ord : (q.d.shape.instOrigins.getD k .ord).child? = none), TgtRun P declName (q.d.shape.insts[k]'hk).1
/-- one change (pkg correspondence): the package is that of `declName`, not of the reached parent `c` -/
def MutCallPkg : Prop := ∀ {ι : Type} {dom : ι → DomainConfig} {P : Pkgs ι dom} {declName : Name} {c : Name} {q : Pkg ι dom}
    (hc : TgtRun P declName c) (hq : P declName = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
    (ord : (q.d.shape.instOrigins.getD k .ord).child? = none), TgtRun P declName (q.d.shape.insts[k]'hk).1
/-- compare binder by binder: names (macro scopes erased), binder infos, and types / conclusion by `isDefEq` at REDUCIBLE transparency -/
partial def cmpTeleR (what : String) (a e : Lean.Expr) (i : Nat := 0) : MetaM Unit := do
  match a, e with
  | .forallE na ta ba bia, .forallE ne te be bie =>
    unless na.eraseMacroScopes == ne.eraseMacroScopes do throwError "CTOR CHECK FAILED {what}: binder {i} is named {na}, expected {ne}"
    unless bia == bie do throwError "CTOR CHECK FAILED {what}: binder {i} ({na}) has a different binder info"
    unless (← withReducible (isDefEq ta te)) do throwError "CTOR CHECK FAILED {what}: binder {i} ({na}) type{indentExpr ta}\nexpected{indentExpr te}"
    withLocalDecl na bia ta fun x => cmpTeleR what (ba.instantiate1 x) (be.instantiate1 x) (i + 1)
  | .forallE na .., _ => throwError "CTOR CHECK FAILED {what}: extra binder {i} ({na})"
  | _, .forallE ne .. => throwError "CTOR CHECK FAILED {what}: binder {i} ({ne}) missing"
  | _, _ => unless (← withReducible (isDefEq a e)) do throwError "CTOR CHECK FAILED {what}: conclusion{indentExpr a}\nexpected{indentExpr e}"

def checkCtor (c e : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  unless ci matches .ctorInfo _ do throwError "CTOR CHECK FAILED {c} is not a constructor"
  cmpTeleR s!"{c}" ci.type (← stmtOf e)
  logInfo m!"CTOR TYPE OK {c} against {e} (names, order, binder infos, types at reducible transparency)"

/-- signature rejection by the same comparator (not a semantic counterexample) -/
def checkCtorMutant (c m : Name) : MetaM Unit := do
  let ci ← getConstInfo c
  let rejected ← try cmpTeleR s!"{c}" ci.type (← stmtOf m); pure false catch _ => pure true
  unless rejected do throwError "CTOR MUTANT ACCEPTED {m} for {c}"
  logInfo m!"CTOR MUTANT REJECTED {m} for {c} (signature comparison, not a semantic counterexample)"

/-- (constructor, expected, mutants) -/
def ctorTable : List (Name × Name × List Name) :=
  [(``TgtRun.top, ``ExpTop, [``MutTop]),
   (``TgtRun.call, ``ExpCall, [``MutCallOrd, ``MutCallNoOrd, ``MutCallParent, ``MutCallNoParent, ``MutCallPkg])]

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
  -- TgtRun: constructor types compared with independently written complete telescopes (names, order, binder infos, types; reducible)
  for (c, e, ms) in ctorTable do
    checkCtor c e
    for m in ms do checkCtorMutant c m
  logInfo m!"TgtRun ctor types: {(← getConstInfo ``TgtRun.top).type}\n{(← getConstInfo ``TgtRun.call).type}"
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
