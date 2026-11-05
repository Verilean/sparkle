import Tools.ShippingGen5CVFinal
set_option autoImplicit false
-- D.D-4 final, refutation of the universal `PT` (Issue sparkle-ledger-dd4-final). No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # `PTlit`: the table with only the `Nat` / `String` literal rows

`PTlit` has exactly the two `tys` rows of `LitRows` (`Nat`, `String`, nullary) and NO `tms` row. It satisfies `LitRows` (given the two env facts `¬ IsDefn env Nat/String`), and the three row
premises `OblRowTypedV` / `RowTeleEvAt` hold trivially (no `tms` row). Yet no `Signal`-using root has a derivation: a derivation uses `natLit`, `strLit`, `bvar`, `lam`, `app`, `letE`, `unfold` only
(`prim` needs a `tms` row), so a derivation of a constant-headed term unfolds it, and it dies at a head constant that is not a definition (`Signal.mk`, ...) or at a binder type
headed by a non-definition other than `Nat` / `String` (`Signal dom α`, ...).

* `StuckB env e` : the syntactic reason (an inductive `Prop`, kernel-checked). `stuckB_no_cvekvb` : `StuckB env e → ∀ ρ τ α v, ¬ CVEKVB PTlit env ρ e τ α v`.
* `stuckChk` : a computable fuel-bounded checker, `stuckChk_sound : stuckChk env n e = true → StuckB env e` (kernel-checked); `Tests/Gen5/PTLitCheck.lean` evaluates it on a real corpus declaration.
* `ptlit_not_declConnect` : `P X = some p`, `StuckB env (const X (LS env X))` ⇒ `¬ DeclConnect (CVFinal PTlit) env P Tgt` for `Tgt X`.
* `stmtCV_ptlit_refutes_entry` : at `PT := PTlit`, the statement `FGLedgerPremisesStmtCV` plus the (provable) auxiliary premises and one stuck root of the entry run give `False`. -/

namespace Tools.ShippingGen5PTLit
open Lean Sparkle.Compiler.Elab Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueES Tools.ShippingGen5ConstValueESL
open Tools.ShippingGen5ConstValueEVL
open Tools.ShippingGen5CVFinal
open Tools.ShippingGen5RowTypedV (OblRowTypedV rowTypedAtV_of_none)

/-! ## The table -/

def natRow : TyRow := ⟨[], fun _ => some Nat⟩
def strRow : TyRow := ⟨[], fun _ => some String⟩

def PTlit : PrimTableK where
  tys c ls :=
    if c = `Nat then (match ls with | [] => some natRow | _ => none)
    else if c = `String then (match ls with | [] => some strRow | _ => none)
    else none
  tms _ _ := none

theorem ptlit_tys_nat : PTlit.tys `Nat [] = some natRow := by simp [PTlit]
theorem ptlit_tys_string : PTlit.tys `String [] = some strRow := by simp [PTlit]

theorem ptlit_tys_some {c : Name} {ls : List Level} {row : TyRow} (h : PTlit.tys c ls = some row) : c = `Nat ∨ c = `String := by
  by_cases h1 : c = `Nat
  · exact Or.inl h1
  · by_cases h2 : c = `String
    · exact Or.inr h2
    · simp [PTlit, h1, h2] at h

theorem ptlit_tms_none (c : Name) (ls : List Level) : PTlit.tms c ls = none := rfl

/-! ## The auxiliary premises hold for `PTlit` -/

theorem ptlit_litRows {env : Environment} (hN : ¬ IsDefn env `Nat) (hS : ¬ IsDefn env `String) : LitRows PTlit env :=
  ⟨natRow, strRow, ptlit_tys_nat, hN, rfl, rfl, ptlit_tys_string, hS, rfl, rfl⟩

theorem ptlit_oblRowTypedV (env : Environment) : OblRowTypedV PTlit env :=
  fun c ls => rowTypedAtV_of_none PTlit env c ls (ptlit_tms_none c ls)

theorem ptlit_rowTeleEvAt (env : Environment) : ∀ (c : Name) (ls : List Level), RowTeleEvAt PTlit env c ls :=
  fun c ls => rowTeleEvAt_of_none PTlit env c ls (ptlit_tms_none c ls)

/-! ## Derivations under `PTlit` have no `prim` -/

/-- Spine of an expression as a list (structural). -/
def spineArgs : Expr → List Expr
  | .app f a => spineArgs f ++ [a]
  | _ => []

theorem spine_eta : ∀ e : Expr, mkAppN e.getAppFn (spineArgs e).toArray = e := by
  intro e
  rw [mkAppN_toList]
  induction e with
  | app f a ih => simp [spineArgs, List.foldl_append, Expr.getAppFn, ih]
  | _ => rfl

/-- A constant-headed term with a derivation unfolds (and the head is a definition). -/
theorem cvekvb_const_head {env : Environment} {ρ : Val} {e τ : Expr} {α : Type} {v : α}
    (h : CVEKVB PTlit env ρ e τ α v) {c : Name} {ls : List Level} (hc : e.getAppFn = .const c ls) :
    ∃ (args : List Expr) (d : DefinitionVal), env.find? c = some (.defnInfo d) ∧ e = mkAppN (.const c ls) args.toArray ∧
      CVEKVB PTlit env ρ (betaS (instantiateLevelParamsS d.levelParams ls d.value) args) τ α v := by
  cases h with
  | natLit => simp [Expr.getAppFn] at hc
  | strLit => simp [Expr.getAppFn] at hc
  | bvar => simp [Expr.getAppFn] at hc
  | lam => simp [Expr.getAppFn] at hc
  | app _ _ _ _ _ hnh => exact absurd ⟨c, ls, by simpa [Expr.getAppFn] using hc⟩ hnh
  | letE => simp [Expr.getAppFn] at hc
  | unfold hd hb he =>
    rename_i c' ls' args d'
    subst he
    rw [spine_fn] at hc
    obtain ⟨rfl, rfl⟩ : c' = c ∧ ls' = ls := by injection hc with h1 h2; exact ⟨h1, h2⟩
    exact ⟨args, d', hd, rfl, hb⟩
  | prim hci hrow => rw [ptlit_tms_none] at hrow; cases hrow

/-- A type with constant head: the head is a definition, or `Nat` / `String`. -/
theorem tdenv_const_head {env : Environment} {ρ : Val} {τ : Expr} {T : Type}
    (h : TDenV PTlit env ρ τ T) {c : Name} {ls : List Level} (hc : τ.getAppFn = .const c ls) (hnd : ¬ IsDefn env c)
    (hn : c ≠ `Nat) (hs : c ≠ `String) : False := by
  cases h with
  | pi => simp [Expr.getAppFn] at hc
  | tlet => simp [Expr.getAppFn] at hc
  | tcon hrow hnd' hargs hT he =>
    rename_i c' ls' args row as'
    subst he
    rw [spine_fn] at hc
    obtain ⟨rfl, rfl⟩ : c' = c ∧ ls' = ls := by injection hc with h1 h2; exact ⟨h1, h2⟩
    rcases ptlit_tys_some hrow with h | h
    · exact hn h
    · exact hs h
  | tunfold hd hb he =>
    rename_i c' ls' args d'
    subst he
    rw [spine_fn] at hc
    obtain ⟨rfl, rfl⟩ : c' = c ∧ ls' = ls := by injection hc with h1 h2; exact ⟨h1, h2⟩
    exact hnd ⟨d', hd⟩

/-! ## The syntactic reason a root has no derivation -/

inductive StuckB (env : Environment) : Expr → Prop
  /-- the head is a constant that is not a definition (a constructor, ...): `unfold` does not apply, and `PTlit` has no `tms` row -/
  | head {e : Expr} {c : Name} {ls : List Level} (h : e.getAppFn = .const c ls) (hnd : ¬ IsDefn env c) : StuckB env e
  /-- the head is a definition and its unfolding is stuck -/
  | unf {c : Name} {ls : List Level} {args : List Expr} {d : DefinitionVal} (hd : env.find? c = some (.defnInfo d))
      (hb : StuckB env (betaS (instantiateLevelParamsS d.levelParams ls d.value) args)) : StuckB env (mkAppN (.const c ls) args.toArray)
  /-- a `lam` whose binder type has a head other than `Nat` / `String` that is not a definition (a `TDenV` of the binder type does not exist) -/
  | lamTy {n : Name} {A b : Expr} {bi : BinderInfo} {c : Name} {ls : List Level} (hA : A.getAppFn = .const c ls)
      (hnd : ¬ IsDefn env c) (hn : c ≠ `Nat) (hs : c ≠ `String) : StuckB env (.lam n A b bi)
  /-- a `lam` whose body is stuck for every valuation -/
  | lamBody {n : Name} {A b : Expr} {bi : BinderInfo} (hb : StuckB env b) : StuckB env (.lam n A b bi)

theorem stuckB_no_cvekvb {env : Environment} {e : Expr} (hs : StuckB env e) :
    ∀ (ρ : Val) (τ : Expr) (α : Type) (v : α), ¬ CVEKVB PTlit env ρ e τ α v := by
  induction hs with
  | head h hnd =>
    intro ρ τ α v hv
    obtain ⟨args, d, hd, -, -⟩ := cvekvb_const_head hv h
    exact hnd ⟨d, hd⟩
  | unf hd hb ih =>
    rename_i c ls args d
    intro ρ τ α v hv
    obtain ⟨args', d', hd', he, hb'⟩ := cvekvb_const_head hv (c := c) (ls := ls) (spine_fn c ls args)
    obtain ⟨-, -, rfl⟩ := spine_inj he.symm
    rw [hd] at hd'; cases hd'
    exact ih ρ τ α v hb'
  | lamTy hA hnd hn hs =>
    intro ρ τ α v hv
    cases hv with
    | lam hA' => exact tdenv_const_head hA' hA hnd hn hs
    | unfold _ _ he => exact spine_ne he (by intros; simp [Expr.getAppFn])
    | prim _ hrow => rw [ptlit_tms_none] at hrow; cases hrow
  | lamBody hb ih =>
    intro ρ τ α v hv
    cases hv with
    | lam hA' TB f a0 hb' => exact ih _ _ _ _ (hb' a0)
    | unfold _ _ he => exact spine_ne he (by intros; simp [Expr.getAppFn])
    | prim _ hrow => rw [ptlit_tms_none] at hrow; cases hrow

theorem stuckB_no_cvekv {env : Environment} {e : Expr} (hs : StuckB env e) {ρ : Val} {τ : Expr} {α : Type} {v : α}
    (h : CVEKV PTlit env ρ e τ α v) : False := by
  cases h with
  | core b => exact stuckB_no_cvekvb hs _ _ _ _ b
  | conv b => exact stuckB_no_cvekvb hs _ _ _ _ b

/-- A stuck root has no `CVFinal PTlit` value. -/
theorem ptlit_not_cvfinal {env : Environment} {X : Name} (hs : StuckB env (.const X (LS env X))) {α : Type} (v : α) : ¬ CVFinal PTlit env X α v := by
  rintro ⟨τ, h⟩
  exact stuckB_no_cvekv hs h

/-- `DeclConnect (CVFinal PTlit)` fails at a stuck root that has a package. -/
theorem ptlit_not_declConnect {ι : Type} {dom : ι → DomainConfig} {env : Environment} {P : Pkgs ι dom} {Tgt : Name → Prop}
    {X : Name} {p : Pkg ι dom} (hX : Tgt X) (hP : P X = some p) (hs : StuckB env (.const X (LS env X))) :
    ¬ DeclConnect (CVFinal PTlit) env P Tgt := by
  intro h
  obtain ⟨ci, sh, v, -, -, -, hv, -⟩ := (declConnect_cvFinal_iff PTlit env P Tgt).mp h X hX p hP
  exact stuckB_no_cvekv hs hv.choose_spec

/-! ## The computable checker, with a kernel-checked soundness -/

/-- Fuel-bounded: `true` only when the stuck reason is found. A head constant that is not a `defnInfo` (including an absent one) counts as stuck. -/
def stuckChk (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | n + 1, e =>
    match e with
    | .lam _ A b _ =>
      (match A.getAppFn with
        | .const c _ =>
          (match env.find? c with | some (.defnInfo _) => false | _ => true) && c != `Nat && c != `String
        | _ => false)
      || stuckChk env n b
    | _ =>
      match e.getAppFn with
      | .const c ls =>
        match env.find? c with
        | some (.defnInfo d) => stuckChk env n (betaS (instantiateLevelParamsS d.levelParams ls d.value) (spineArgs e))
        | _ => true
      | _ => false

theorem not_isDefn_of_find {env : Environment} {c : Name} (h : ∀ d : DefinitionVal, env.find? c ≠ some (.defnInfo d)) : ¬ IsDefn env c :=
  fun ⟨d, hd⟩ => h d hd

theorem stuckChk_sound (env : Environment) : ∀ (n : Nat) (e : Expr), stuckChk env n e = true → StuckB env e := by
  intro n
  induction n with
  | zero => intro e h; simp [stuckChk] at h
  | succ n ih =>
    intro e h
    by_cases hl : ∃ nm A b bi, e = Expr.lam nm A b bi
    · obtain ⟨nm, A, b, bi, rfl⟩ := hl
      simp only [stuckChk, Bool.or_eq_true] at h
      rcases h with h | h
      · revert h
        generalize hA : A.getAppFn = f
        cases f with
        | const c ls =>
          intro h
          dsimp only at h
          have hnd : ¬ IsDefn env c := by
            rintro ⟨d, hd⟩; rw [hd] at h; simp at h
          have h' := h
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
          exact StuckB.lamTy hA hnd h'.1.2 h'.2
        | _ => intro h; simp at h
      · exact StuckB.lamBody (ih _ h)
    · have hrw : stuckChk env (n + 1) e = (match e.getAppFn with
          | .const c ls =>
            match env.find? c with
            | some (.defnInfo d) => stuckChk env n (betaS (instantiateLevelParamsS d.levelParams ls d.value) (spineArgs e))
            | _ => true
          | _ => false) := by
        cases e <;> first | rfl | (exfalso; exact hl ⟨_, _, _, _, rfl⟩)
      rw [hrw] at h
      generalize hf : e.getAppFn = f at h
      cases f with
      | const c ls =>
        generalize hfind : env.find? c = fi at h
        cases fi with
        | none =>
          refine StuckB.head (c := c) (ls := ls) hf ?_
          rintro ⟨d, hd⟩; rw [hfind] at hd; cases hd
        | some ci =>
          cases ci with
          | defnInfo d =>
            dsimp only at h
            rw [hfind] at h
            dsimp only at h
            have hb := ih _ h
            have he : e = mkAppN (.const c ls) (spineArgs e).toArray := by
              have := spine_eta e; rw [hf] at this; exact this.symm
            have hu := StuckB.unf (c := c) (ls := ls) (args := spineArgs e) hfind hb
            rw [← he] at hu
            exact hu
          | _ =>
            refine StuckB.head (c := c) (ls := ls) hf ?_
            rintro ⟨d, hd⟩; rw [hfind] at hd; cases hd
      | _ => simp at h

/-! ## The statement at `PT := PTlit`

All four auxiliary premises are available for `PTlit` (`LitRows` from the two env facts `¬ IsDefn env Nat/String`, the two row premises unconditionally; `KernelClosedInvariant` and `OblLbrZero`
do not mention `PT`, they stay hypotheses). A single stuck root of the entry run (`declName` itself, which is in `TgtRun` by `top`) then contradicts the conclusion: the hypotheses of the entry run are inconsistent
with `FGLedgerPremisesStmtCV` at `PTlit`. So at `PTlit` the statement is false (if those hypotheses are satisfiable) or vacuous (if not). -/

open Tools.ShippingGen5ConstValueESoundK (OblLbrZero)
open Tools.ShippingGen5EnvDeclClosed (KernelClosedInvariant)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGenFGLedgerPremises Tools.ShippingGen5SM1 Tools.ShippingGen5Acc Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
open Sparkle.IR.Semantics Sparkle.IR.Machine Sparkle.Core Sparkle.Core.Signal
open Tools.ShippingEntrySoundness (RunsTo)

theorem stmtCV_ptlit_refutes_entry (hS : FGLedgerPremisesStmtCV) {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (lvl : Lean.Expr → Nat)
    (genData₀ : (env : Environment) → (E : ConstantInfo) →
      Option (GenData (Tools.ShippingGen5DataOf.dataOfAt lvl) E (structEnv env)))
    (L : Laws mref cref)
    (h_C_EN4 : Tools.ShippingGen5EnvFrame3.CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (h_C_RK6 : Tools.Prototype.DGenStored2.ReflExprAgree)
    (h_C_CV4 : ∀ (E : ConstantInfo) (senv : StructEnv) (sp : MachineShape),
        machineShape? false [] E senv = some sp →
        ∃ n, Tools.ShippingReaderFuel.machineShapeF n false [] E senv true = some (some sp))
    (h_D_LBR : OblLbrZero)
    (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design)
    (hw : EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D)
    (hkci : KernelClosedInvariant (envAt cref w))
    (hN : ¬ IsDefn (envAt cref w) `Nat) (hSt : ¬ IsDefn (envAt cref w) `String)
    (hA6 : ∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ q : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), Tools.ShippingChildInvA.AdmCtx L.O.quiet mctx' cctx' →
          Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hT4 : ∀ c, TgtRun (genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w)) declName c → ∀ p : Pkg ι dom, genGP (ι := ι) (dom := dom) lvl (dataOfSound_initsOf lvl) genData₀ (envAt cref w) c = some p →
        ∀ (k : Nat) (hk : k < p.d.shape.insts.length) (y : Tools.ShippingChildInv.Res),
          Tools.ShippingChildCacheA.RealChildA L.O (p.d.shape.insts[k]).1 y →
          ∀ pt ∈ y.1.outputs, pt.name = p.d.shape.instFields.getD k "" →
            (p.d.shape.binders[p.kD + k]?).map (fun bn => (Tools.ShippingMachineEntry.kindTy bn.2).bitWidth)
              = some pt.ty.bitWidth)
    (hstuck : StuckB (envAt cref w) (.const declName (LS (envAt cref w) declName))) : False := by
  obtain ⟨-, hmain⟩ := hS (ι := ι) (dom := dom) ReflectsAll Post lvl genData₀ PTlit L h_C_EN4 h_C_RK6 h_C_CV4 h_D_LBR
  obtain ⟨-, ⟨p, hp⟩, -, hdc⟩ := hmain declName parameters mctx cctx w w' b D hw hkci (ptlit_litRows hN hSt)
    (ptlit_oblRowTypedV _) (ptlit_rowTeleEvAt _) hA6 hT4
  exact ptlit_not_declConnect TgtRun.top hp hstuck hdc

end Tools.ShippingGen5PTLit

#print axioms Tools.ShippingGen5PTLit.stuckB_no_cvekvb
#print axioms Tools.ShippingGen5PTLit.stuckChk_sound
#print axioms Tools.ShippingGen5PTLit.ptlit_not_declConnect
#print axioms Tools.ShippingGen5PTLit.ptlit_litRows
#print axioms Tools.ShippingGen5PTLit.stmtCV_ptlit_refutes_entry
