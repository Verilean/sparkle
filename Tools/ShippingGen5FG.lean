import Lean
import Tools.ShippingGen2Defs
import Tools.ShippingGen5DeclConnect
import Tools.ShippingEntryReadsLinked
set_option autoImplicit false
-- Built at ba85e637b523e1d880e1c2e1176ff64891fe9a6a (agent build `kjob lake build Tests.Gen5.FGCheck`, exit 0; clean issue-linked build is the coder's).

/-! # DC-CONNECT unit U-FG (scripts/gen5/DC_CONNECT_FREEZE.md rev5 §C.3, scoped approved)

`ConstValueFunctional`, `TgtRun`, `EntryWitness`, `FG_COND`, `FG_CONNECT` at the complete types of freeze rev5 §C.3, and the CONDITIONAL
non-vacuity lemmas NV-Post / NV-GP / NV-CV (each holds when an `EntryWitness` is given). Nothing here supplies an `EntryWitness`, `Post`,
`ReflectsAll`, `GP` or `CV`: `FG_CONNECT` is an INTERMEDIATE parametrized statement, not a final guarantee. No law, TRUSTED boundary,
`sorry`, axiom or `native_decide`. `ReflectsAll = False`-style scope shrinking is not used anywhere. -/
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)

namespace Tools.ShippingGen5FG

variable {ι : Type} {dom : ι → DomainConfig}

def ConstValueFunctional (CV : ConstValueRel) : Prop :=
  ∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w

/-- least predicate: `declName`, and the ordinary callees of reached names -/
inductive TgtRun (P : Pkgs ι dom) (declName : Name) : Name → Prop
  | top : TgtRun P declName declName
  | call {c : Name} {q : Pkg ι dom} (hc : TgtRun P declName c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
      (ord : (q.d.shape.instOrigins.getD k .ord).child? = none) : TgtRun P declName (q.d.shape.insts[k]'hk).1

/-- The hypotheses of FG on one entry run (the witness): the start world, one of the two routes, `ReflectsAll`. -/
def EntryWitness {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref)
    (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  Start L mctx cctx w ∧
  (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
   RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
  ReflectsAll L declName parameters

/-- CONDITIONAL SCHEMA. Not a final guarantee: vacuous at `Post = False`, `GP = none`, `CV = ∅` (`fgCond_trivial`). -/
def FG_COND {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : ConstValueRel) (L : Laws mref cref) : Prop :=
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    ConstValueFunctional CV ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- FINAL CONNECTION (INTERMEDIATE while `Post`/`ReflectsAll` are parameters). Same witness: O1 `∃ raw, Post`, O2 package, O3 FG conclusion, DeclConnect. -/
def FG_CONNECT {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : ConstValueRel) (L : Laws mref cref) : Prop :=
  ConstValueFunctional CV ∧
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
    (∃ raw, Post b raw) ∧
    (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

section NV
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
  {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {L : Laws mref cref}
  {declName : Name} {parameters : List (String × Nat)} {mctx : Meta.Context} {cctx : Core.Context}
  {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}

/-- NV-Post (conditional on a witness): with `Post := False` the connection is refutable, so `Post` cannot weaken `FG_CONNECT`. -/
theorem nv_post {GP : Environment → Pkgs ι dom} {CV : ConstValueRel}
    (h : FG_CONNECT ReflectsAll (fun _ _ => False) GP CV L)
    (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) : False := by
  obtain ⟨raw, hraw⟩ := (h.2 declName parameters mctx cctx w w' b D hw).1
  exact hraw

/-- NV-GP (conditional on a witness): with `GP := none` the connection is refutable (O2 fails). -/
theorem nv_gp {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {CV : ConstValueRel}
    (h : FG_CONNECT (ι := ι) (dom := dom) ReflectsAll Post (fun _ _ => none) CV L)
    (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) : False := by
  obtain ⟨p, hp⟩ := (h.2 declName parameters mctx cctx w w' b D hw).2.1
  cases hp

/-- NV-CV (conditional on a witness): with `CV := ∅` the connection is refutable (O2 gives a package at `declName`, `TgtRun.top` reaches it). -/
theorem nv_cv {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {GP : Environment → Pkgs ι dom}
    (h : FG_CONNECT ReflectsAll Post GP (fun _ _ _ _ => False) L)
    (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D) : False := by
  obtain ⟨_, hO2, _, hDC⟩ := h.2 declName parameters mctx cctx w w' b D hw
  obtain ⟨p, hp⟩ := hO2
  exact not_declConnect_of_empty (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
    TgtRun.top hp hDC

/-- O2 is derivable from O1 and O3 (so it is NOT a logically independent conjunct; it is kept as a stated obligation). -/
theorem o2_of_o1_o3 {Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop} {GP : Environment → Pkgs ι dom}
    (o1 : ∃ raw, Post b raw)
    (o3 : ∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) :
    ∃ p : Pkg ι dom, GP (envAt cref w) declName = some p := by
  obtain ⟨raw, hr⟩ := o1
  obtain ⟨p, _, hp, _⟩ := o3 raw hr
  exact ⟨p, hp⟩

end NV

/-- `FG_COND` is satisfied by the trivial carriers: this is why it is a conditional schema and not a final guarantee. -/
theorem fgCond_trivial {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref) :
    FG_COND (ι := ι) (dom := dom) ReflectsAll (fun _ _ => False) (fun _ _ => none)
      (fun _ _ _ _ => False) L := by
  intro declName parameters mctx cctx w w' b D _
  refine ⟨fun _ h => h.elim, fun _ _ _ _ _ _ h => h.elim, ?_⟩
  intro X _ p hp
  cases hp

end Tools.ShippingGen5FG
