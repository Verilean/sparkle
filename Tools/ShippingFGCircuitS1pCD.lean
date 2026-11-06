import Tools.ShippingFGCircuitS1mCD
import Tools.ShippingFGCircuitS1kStmt
set_option autoImplicit false
-- FG circuit pilot S1p: (1) single-environment carrier for CDX (reviewer M1), (2) the List.rec iota unit (DY = DX + recIota), docs/FG-CIRCUIT-PILOT.md §20.
-- No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1p

1. `CircCVS`: the carrier whose quote environment and unfolding environment are THE SAME variable (`fun env X α v => ... CDX env [] d.value α v`). The S1m `CircCVX env` reads the quote in its
   argument `env'` and unfolds in `env`; only `circCV_to_X` ties them. `CircCVS` is the carrier a final statement may use; the run side is bound to `envAt cref w`.
2. `DY`: `DX` with ONE more rule, `recIota` (iota of `List.rec` with a statically `nil`/`cons` major premise). `DX` is not edited; `dx_to_dy` embeds it. -/
namespace Tools.ShippingFGCircuitS1pCD
open Lean Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5ConstValueE Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitS1mCD
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingEntrySoundness (RunsTo)

/-! ## 1. M1: the single-environment carrier -/

/-- the carrier with ONE environment: the declaration `X` is read in `env`, and its value is unfolded in the same `env`. -/
def CircCVS : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDX env [] d.value α v

theorem circCV_to_S (env : Environment) {X : Name} {α : Type} {v : α} (h : CircCV env X α v) : CircCVS env X α v := by
  obtain ⟨d, hd, hl, hv⟩ := h
  exact ⟨d, hd, hl, cdx_of_cd hv⟩

theorem circCVS_to_X (env : Environment) {X : Name} {α : Type} {v : α} (h : CircCVS env X α v) : CircCVX env env X α v := h

/-- the S1m carrier is the single-environment one exactly when the two environments are equal -/
theorem circCVX_iff_S (env env' : Environment) (X : Name) (α : Type) (v : α) (heq : env' = env) : CircCVX env env' X α v ↔ CircCVS env' X α v := by
  subst heq; exact Iff.rfl

theorem circCVS_functional : ConstValueFunctional CircCVS := by
  intro env c α β v w ⟨d, hd, _, hv⟩ ⟨d', hd', _, hv'⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  exact cdx_fun hv hv'

/-- the source meaning over the single-environment carrier (same shape as `SourceDenotes`) -/
def SourceDenotesS (env : Environment) (source : Name) (params : List (String × Nat)) (sh : SigShape) (m : sh.Ty) : Prop :=
  params = [] ∧ ∃ ci : ConstantInfo, env.find? source = some ci ∧ shapeOf ci = some sh ∧ CircCVS env source sh.Ty m

theorem sourceDenotes_to_S {env : Environment} {source : Name} {params : List (String × Nat)} {sh : SigShape} {m : sh.Ty}
    (h : SourceDenotes env source params sh m) : SourceDenotesS env source params sh m := by
  obtain ⟨hp, ci, hci, hsh, hcv⟩ := h
  exact ⟨hp, ci, hci, hsh, circCV_to_S env hcv⟩

/-- `DeclConnect` over `CircCV` gives `DeclConnect` over `CircCVS` (the carrier is only used at the start environment `env₀`) -/
theorem declConnect_to_S {ι : Type} {dom : ι → DomainConfig} (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop)
    (h : DeclConnect CircCV env₀ P Tgt) : DeclConnect CircCVS env₀ P Tgt := by
  rw [declConnect_eq] at h ⊢
  intro X hX p hp
  obtain ⟨ci, sh, v, h1, h2, h3, h4, h5⟩ := h X hX p hp
  exact ⟨ci, sh, v, h1, h2, h3, circCV_to_S env₀ h4, h5⟩

/-- run side: the environment the single-environment carrier is read in is `envAt cref w`, the Core state's environment at the start world -/
def CircCVSAt (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) (X : Name) (α : Type) (v : α) : Prop := CircCVS (envAt cref w) X α v

theorem circCVS_at_of_getEnv {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w w' : Void IO.RealWorld} {e : Environment} (h : RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w e w') {X : Name} {α : Type} {v : α} :
    CircCVS e X α v ↔ CircCVS (envAt cref w) X α v := by
  rw [Tools.ShippingEntryReadsLinked.getEnv_value h]

/-- the S1k obligation `HftObCD` over a ONE environment: the root's value expression is denoted by `CDX env` -/
def HftObCDX (env : Environment) : Prop := CDX env [] Tools.ShippingFGCircuitS1kStmt.hftRootValue (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft)
  Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte

/-- the root's `CircCVS` fact from its value expression: the declaration of `env` has `hftRootValue` as its value -/
theorem circCVS_hft_of_obCDX {env : Environment} {d : DefinitionVal} (hd : env.find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d))
    (hl : d.levelParams = []) (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDX env) :
    CircCVS env Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  ⟨d, hd, hl, by rw [hv]; exact h⟩

/-- the run-side form: at `env := envAt cref w` -/
theorem circCVS_hft_run (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) {d : DefinitionVal}
    (hd : (envAt cref w).find? Tools.ShippingFGCircuitS1kStmt.hftRoot = some (.defnInfo d)) (hl : d.levelParams = [])
    (hv : d.value = Tools.ShippingFGCircuitS1kStmt.hftRootValue) (h : HftObCDX (envAt cref w)) :
    CircCVSAt cref w Tools.ShippingFGCircuitS1kStmt.hftRoot (MonoTy Tools.ShippingFGCircuitS1kStmt.shHft) Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte :=
  circCVS_hft_of_obCDX hd hl hv h

/-! ### the mixed-environment gap of the S1m carrier (negative control, kernel-checked)

`CircCVX env env'` quotes in `env'` and unfolds in `env`. With `env'` defining `mini := pure 6` and `env` defining `mini := pure 5`, the S1m carrier holds for the value `pure 5` although `env'`'s own declaration denotes `pure 6`. -/

def miniN : Name := `Tests.mini
def natEx (n : Nat) : Expr := appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]
def miniVal (n : Nat) : Expr := appN ``Signal.pure [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], .const ``Nat [], natEx n]
def Δn (n : Nat) : Name → Option DefRow := fun c => if c == miniN then some ⟨[], miniVal n⟩ else none

theorem miniDen (n : Nat) {env : Environment} (hΔ : EnvDefs env (Δn n)) :
    CDX env [] (.const miniN []) (Signal defaultDomain Nat) (Signal.pure n) :=
  cdx_unf_tbl hΔ (r := ⟨[], miniVal n⟩) rfl (by decide) (by simp [Δn]) rfl rfl (.sigPure rfl (.domDefault rfl) (.nat rfl) (.natLit rfl))

/-- the S1m carrier holds in a mixed pair: `env` unfolds `mini` to `pure 5`, `env'` declares `X := mini` -/
theorem circCVX_mixed {env env' : Environment} {X : Name} {d : DefinitionVal} (hΔ : EnvDefs env (Δn 5))
    (hd : env'.find? X = some (.defnInfo d)) (hl : d.levelParams = []) (hv : d.value = .const miniN []) :
    CircCVX env env' X (Signal defaultDomain Nat) (Signal.pure 5) :=
  ⟨d, hd, hl, by rw [hv]; exact miniDen 5 hΔ⟩

/-- the single-environment carrier does NOT admit that pair: if `env'` itself unfolds `mini` to `pure 6`, `CircCVS env' X` cannot have value `pure 5` -/
theorem circCVS_rejects_mixed {env' : Environment} {X : Name} {d : DefinitionVal} (hΔ' : EnvDefs env' (Δn 6))
    (hd : env'.find? X = some (.defnInfo d)) (hv : d.value = .const miniN []) :
    ¬ CircCVS env' X (Signal defaultDomain Nat) (Signal.pure 5) := by
  rintro ⟨d', hd', _, h⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  rw [hv] at h
  have h2 := cdx_eq h (miniDen 6 hΔ')
  have h3 := congrArg (fun s : Signal defaultDomain Nat => s.val 0) h2
  simp [Signal.pure] at h3

/-! ## 2. the `List.rec` iota unit -/

/-- the major premise, unfolded by `whStep` (zeta/beta/delta/proj) until its head is a `List` constructor; at most `fuel` steps -/
def recMajorWh (env : Environment) : Nat → Expr → Option Expr
  | 0, _ => none
  | n + 1, x =>
    match appFn x with
    | .const c _ => if c == ``List.nil || c == ``List.cons then some x else (whStep env x).bind (recMajorWh env n)
    | _ => (whStep env x).bind (recMajorWh env n)

/-- `List.rec.{ls} α motive nilc consc major extra…` with `major` ⤳ `nil`: `nilc extra…`; with `major` ⤳ `cons h t`: `consc h t (List.rec.{ls} α motive nilc consc t) extra…` (the SAME levels) -/
def recStepCore (env : Environment) (c : Name) (ls : List Level) : List Expr → Option Expr
  | a0 :: mot :: nilc :: consc :: major :: extra =>
    match recMajorWh env 256 major with
    | some m =>
      match appFn m, appArgs m with
      | .const k _, [_] => if k == ``List.nil then some (betaApp nilc extra) else none
      | .const k _, [_, h, t] =>
        if k == ``List.cons then some (betaApp consc ([h, t, mkApps (.const c ls) [a0, mot, nilc, consc, t]] ++ extra)) else none
      | _, _ => none
    | none => none
  | _ => none

/-- the iota step: the head is the recursor `List.rec` (a `recInfo` of `env`) with at least its five arguments -/
def recStep (env : Environment) (e : Expr) : Option Expr :=
  match appFn e with
  | .const c ls =>
    if c == ``List.rec then
      match env.find? c with
      | some (.recInfo _) => recStepCore env c ls (appArgs e)
      | _ => none
    else none
  | _ => none

theorem recStep_head {env : Environment} {e e' : Expr} (h : recStep env e = some e') :
    ∃ (ls : List Level) (ri : RecursorVal), appFn e = .const ``List.rec ls ∧ env.find? ``List.rec = some (.recInfo ri) := by
  unfold recStep at h
  split at h
  · rename_i c ls hf
    split at h
    · rename_i hc
      have hc' : c = ``List.rec := by simpa using hc
      subst hc'
      split at h
      · rename_i ri hfind; exact ⟨ls, ri, hf, hfind⟩
      · simp at h
    · simp at h
  · simp at h

theorem unfoldAt_rec {env : Environment} {e : Expr} {ls : List Level} {ri : RecursorVal} (hf : appFn e = .const ``List.rec ls)
    (hi : env.find? ``List.rec = some (.recInfo ri)) : unfoldAt env e = none := by
  simp [unfoldAt, hf, hi]

theorem headRedex_rec {env : Environment} {e : Expr} {ls : List Level} (hf : appFn e = .const ``List.rec ls) : headRedex env e = none := by
  simp [headRedex, hf]

theorem stopC_rec : stopC ``List.rec = false := by decide
theorem bvAbbrevRow_rec : bvAbbrevRow ``List.rec = none := by
  cases h : bvAbbrevRow ``List.rec with
  | none => rfl
  | some r => have := stopC_of_row h; rw [stopC_rec] at this; cases this

section
local macro "CDy " env:term:max ρ:term:max e:term:max α:term:max v:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1pCD.DY) $env $ρ $e (Res.val $α $v))
local macro "TDy " env:term:max ρ:term:max e:term:max T:term:max : term => `($(Lean.mkIdent `Tools.ShippingFGCircuitS1pCD.DY) $env $ρ $e (Res.ty $T))
inductive DY (env : Environment) : Val → Expr → Res → Prop
  | nat {ρ : Val} {e : Expr} (he : e = .const ``Nat []) : TDy env ρ e Nat
  | bool {ρ : Val} {e : Expr} (he : e = .const ``Bool []) : TDy env ρ e Bool
  | domainConfig {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.DomainConfig []) : TDy env ρ e DomainConfig
  | bitvec {ρ : Val} {e w : Expr} {n : Nat} (he : e = appN ``BitVec [] [w]) (hw : CDy env ρ w Nat n) : TDy env ρ e (BitVec n)
  | signal {ρ : Val} {e d t : Expr} {D : DomainConfig} {T : Type} (he : e = appN ``Signal [.zero] [d, t])
      (hd : CDy env ρ d DomainConfig D) (ht : TDy env ρ t T) : TDy env ρ e (Signal D T)

  | bvar {ρ : Val} {i : Nat} {τ : Expr} {T : Type} {a : T} (h : ρ[i]? = some ⟨τ, ⟨T, a⟩⟩) : CDy env ρ (.bvar i) T a
  | natLit {ρ : Val} {e : Expr} {n : Nat}
      (he : e = appN ``OfNat.ofNat [.zero] [.const ``Nat [], .lit (.natVal n), appN ``instOfNatNat [] [.lit (.natVal n)]]) :
      CDy env ρ e Nat n
  | domDefault {ρ : Val} {e : Expr} (he : e = .const ``Sparkle.Core.Domain.defaultDomain []) :
      CDy env ρ e DomainConfig defaultDomain
  | bvOfNat {ρ : Val} {e w k : Expr} {W K : Nat} (he : e = appN ``BitVec.ofNat [] [w, k])
      (hw : CDy env ρ w Nat W) (hk : CDy env ρ k Nat K) : CDy env ρ e (BitVec W) (BitVec.ofNat W K)
  | bvInhabited {ρ : Val} {e w : Expr} {W : Nat} (he : e = appN ``BitVec.instInhabited [] [w]) (hw : CDy env ρ w Nat W) :
      CDy env ρ e (Inhabited (BitVec W)) (inferInstance : Inhabited (BitVec W))
  | boolInhabited {ρ : Val} {e : Expr} (he : e = .const ``instInhabitedBool []) :
      CDy env ρ e (Inhabited Bool) (inferInstance : Inhabited Bool)
  | sigPure {ρ : Val} {e d t x : Expr} {D : DomainConfig} {T : Type} {a : T}
      (he : e = appN ``Signal.pure [.zero] [d, t, x]) (hd : CDy env ρ d DomainConfig D) (ht : TDy env ρ t T) (hx : CDy env ρ x T a) :
      CDy env ρ e (Signal D T) (Signal.pure a)
  | sigRegister {ρ : Val} {e d t i s : Expr} {D : DomainConfig} {T : Type} {a : T} {sv : Signal D T}
      (he : e = appN ``Signal.register [.zero] [d, t, i, s]) (hd : CDy env ρ d DomainConfig D) (ht : TDy env ρ t T)
      (hi : CDy env ρ i T a) (hs : CDy env ρ s (Signal D T) sv) : CDy env ρ e (Signal D T) (Signal.register a sv)
  | sigMux {ρ : Val} {e d t c a b : Expr} {D : DomainConfig} {T : Type} {cv : Signal D Bool} {av bv : Signal D T}
      (he : e = appN ``Signal.mux [.zero] [d, t, c, a, b]) (hd : CDy env ρ d DomainConfig D) (ht : TDy env ρ t T)
      (hc : CDy env ρ c (Signal D Bool) cv) (ha : CDy env ρ a (Signal D T) av) (hb : CDy env ρ b (Signal D T) bv) :
      CDy env ρ e (Signal D T) (Signal.mux cv av bv)
  | sigAddBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``HAdd.hAdd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Signal [.zero] [d, appN ``BitVec [] [w]],
         appN ``Signal [.zero] [d, appN ``BitVec [] [w]], appN ``Sparkle.Core.Signal.instHAddSignalBitVec [] [d, w], a, b])
      (hd : CDy env ρ d DomainConfig D) (hw : CDy env ρ w Nat W)
      (ha : CDy env ρ a (Signal D (BitVec W)) av) (hb : CDy env ρ b (Signal D (BitVec W)) bv) :
      CDy env ρ e (Signal D (BitVec W)) (@HAdd.hAdd _ _ _ (@Sparkle.Core.Signal.instHAddSignalBitVec D W) av bv)
  | sigLoop {ρ : Val} {e d t inst f : Expr} {D : DomainConfig} {T : Type} {iv : Inhabited T} {g : Signal D T → Signal D T}
      (he : e = appN ``Signal.loop [] [d, t, inst, f]) (hd : CDy env ρ d DomainConfig D) (ht : TDy env ρ t T)
      (hi : CDy env ρ inst (Inhabited T) iv) (hf : CDy env ρ f (Signal D T → Signal D T) g) :
      CDy env ρ e (Signal D T) (@Signal.loop D T iv g)
  | lam {ρ : Val} {e A body : Expr} {n : Name} {bi : BinderInfo} {TA : Type} {TB : TA → Type} {f : (a : TA) → TB a}
      (he : e = .lam n A body bi) (hA : TDy env ρ A TA) (hb : ∀ a : TA, CDy env (⟨A, ⟨TA, a⟩⟩ :: ρ) body (TB a) (f a)) :
      CDy env ρ e ((a : TA) → TB a) f
  | letE {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {TA T : Type} {a : TA} {r : T}
      (he : e = .letE n A v body nd) (hA : TDy env ρ A TA) (hv : CDy env ρ v TA a) (hb : CDy env (⟨A, ⟨TA, a⟩⟩ :: ρ) body T r) : CDy env ρ e T r
  | sigBeqBV {ρ : Val} {e d w a b : Expr} {D : DomainConfig} {W : Nat} {av bv : Signal D (BitVec W)}
      (he : e = appN ``Sparkle.Core.Signal.Signal.beq []
        [appN ``BitVec [] [w], d, appN ``instBEqOfDecidableEq [.zero] [appN ``BitVec [] [w], appN ``instDecidableEqBitVec [] [w]], a, b])
      (hd : CDy env ρ d DomainConfig D) (hw : CDy env ρ w Nat W)
      (ha : CDy env ρ a (Signal D (BitVec W)) av) (hb : CDy env ρ b (Signal D (BitVec W)) bv) :
      CDy env ρ e (Signal D Bool) (@Signal.beq (BitVec W) D (@instBEqOfDecidableEq (BitVec W) (@instDecidableEqBitVec W)) av bv)
  | sigAndBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HAnd.hAnd [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHAndSignalBool [] [d], a, b])
      (hd : CDy env ρ d DomainConfig D) (ha : CDy env ρ a (Signal D Bool) av) (hb : CDy env ρ b (Signal D Bool) bv) :
      CDy env ρ e (Signal D Bool) (@HAnd.hAnd _ _ _ (@Sparkle.Core.Signal.instHAndSignalBool D) av bv)
  | sigOrBool {ρ : Val} {e d a b : Expr} {D : DomainConfig} {av bv : Signal D Bool}
      (he : e = appN ``HOr.hOr [.zero, .zero, .zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Signal [.zero] [d, .const ``Bool []],
         appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instHOrSignalBool [] [d], a, b])
      (hd : CDy env ρ d DomainConfig D) (ha : CDy env ρ a (Signal D Bool) av) (hb : CDy env ρ b (Signal D Bool) bv) :
      CDy env ρ e (Signal D Bool) (@HOr.hOr _ _ _ (@Sparkle.Core.Signal.instHOrSignalBool D) av bv)
  | sigNotBool {ρ : Val} {e d a : Expr} {D : DomainConfig} {av : Signal D Bool}
      (he : e = appN ``Complement.complement [.zero]
        [appN ``Signal [.zero] [d, .const ``Bool []], appN ``Sparkle.Core.Signal.instComplementSignalBool [] [d], a])
      (hd : CDy env ρ d DomainConfig D) (ha : CDy env ρ a (Signal D Bool) av) :
      CDy env ρ e (Signal D Bool) (@Complement.complement _ (@Sparkle.Core.Signal.instComplementSignalBool D) av)
  | bvAbbrev {ρ : Val} {e : Expr} {c : Name} {n : Nat} {v : BitVec n} (he : e = .const c []) (h : bvAbbrevRow c = some ⟨n, v⟩) :
      CDy env ρ e (BitVec n) v
  /-- NEW. delta + beta of a user definition of `env` (`unfoldAt`: the head is a `defnInfo` of `env` with matching universe arity), the head not a stop constant. The value is the value of the unfolded expression. -/
  | unf {ρ : Val} {e e' : Expr} {α : Type} {v : α}
      (hs : headStop e = false) (hu : unfoldAt env e = some e') (h : CDy env ρ e' α v) : CDy env ρ e α v
  /-- NEW. a head redex (`headRedex`: beta, let-application, projection-application) of the expression itself (arguments substituted by `unf` can create it). -/
  | beta {ρ : Val} {e e' : Expr} {α : Type} {v : α}
      (hb : headRedex env e = some e') (h : CDy env ρ e' α v) : CDy env ρ e α v
  /-- NEW. `let` of a non-core type: substitute (the old `letE` handles core types). -/
  | zeta {ρ : Val} {e A v body : Expr} {n : Name} {nd : Bool} {α : Type} {r : α}
      (he : e = .letE n A v body nd) (hA : coreHead A = false) (h : CDy env ρ (instE body v 0) α r) : CDy env ρ e α r
  /-- NEW. a weak-head step of the structure argument of a projection. -/
  | projStep {ρ : Val} {e x x' : Expr} {S : Name} {i : Nat} {α : Type} {v : α}
      (he : e = .proj S i x) (hx : whStep env x = some x') (h : CDy env ρ (.proj S i x') α v) : CDy env ρ e α v
  /-- NEW. projection of a constructor application (iota); `ctor` is a `ctorInfo` of `env` of the inductive `S`. -/
  | projCtor {ρ : Val} {e x fld : Expr} {S ctor : Name} {ls : List Level} {cv : ConstructorVal} {i : Nat} {α : Type} {v : α}
      (he : e = .proj S i x) (hh : appFn x = .const ctor ls) (hc : env.find? ctor = some (.ctorInfo cv)) (hS : cv.induct = S)
      (hn : (appArgs x).length = cv.numParams + cv.numFields) (hf : (appArgs x)[cv.numParams + i]? = some fld)
      (h : CDy env ρ fld α v) : CDy env ρ e α v
  /-- NEW (S1p). iota of `List.rec` whose major premise statically unfolds to `List.nil`/`List.cons` (`recStep`): the value is the value of the reduced expression. No other recursor, no universe change. -/
  | recIota {ρ : Val} {e e' : Expr} {ls : List Level} {ri : RecursorVal} {α : Type} {v : α}
      (hf : appFn e = .const ``List.rec ls) (hi : env.find? ``List.rec = some (.recInfo ri)) (hr : recStep env e = some e') (h : CDy env ρ e' α v) : CDy env ρ e α v
end

/-- the `ty` kind: a `TDY` judgement has a core-typed head -/
theorem coreHead_ty {env : Environment} {ρ : Val} {A : Expr} {T : Type} (h : DY env ρ A (.ty T)) : coreHead A = true := by
  cases h with
  | nat he => subst he; decide
  | bool he => subst he; decide
  | domainConfig he => subst he; decide
  | bitvec he hw => subst he; simp [coreHead, appFn_appN]
  | signal he hd ht => subst he; simp [coreHead, appFn_appN]

abbrev TDY (env : Environment) (ρ : Val) (e : Expr) (T : Type) : Prop := DY env ρ e (.ty T)
abbrev CDY (env : Environment) (ρ : Val) (e : Expr) (α : Type) (v : α) : Prop := DY env ρ e (.val α v)

/-- every `DX` derivation is a `DY` derivation (the 5 + 18 + 5 rules of `DX` map one to one; `recIota` is not used) -/
theorem dx_to_dy {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DX env ρ e r) : DY env ρ e r := by
  induction h with
  | nat he => exact .nat he
  | bool he => exact .bool he
  | domainConfig he => exact .domainConfig he
  | bitvec he _ ih => exact .bitvec he ih
  | signal he _ _ ih1 ih2 => exact .signal he ih1 ih2
  | bvar h => exact .bvar h
  | natLit he => exact .natLit he
  | domDefault he => exact .domDefault he
  | bvOfNat he _ _ ih1 ih2 => exact .bvOfNat he ih1 ih2
  | bvInhabited he _ ih => exact .bvInhabited he ih
  | boolInhabited he => exact .boolInhabited he
  | sigPure he _ _ _ ih1 ih2 ih3 => exact .sigPure he ih1 ih2 ih3
  | sigRegister he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigRegister he ih1 ih2 ih3 ih4
  | sigMux he _ _ _ _ _ ih1 ih2 ih3 ih4 ih5 => exact .sigMux he ih1 ih2 ih3 ih4 ih5
  | sigAddBV he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigAddBV he ih1 ih2 ih3 ih4
  | sigLoop he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigLoop he ih1 ih2 ih3 ih4
  | lam he _ _ ih1 ih2 => exact .lam he ih1 ih2
  | letE he _ _ _ ih1 ih2 ih3 => exact .letE he ih1 ih2 ih3
  | sigBeqBV he _ _ _ _ ih1 ih2 ih3 ih4 => exact .sigBeqBV he ih1 ih2 ih3 ih4
  | sigAndBool he _ _ _ ih1 ih2 ih3 => exact .sigAndBool he ih1 ih2 ih3
  | sigOrBool he _ _ _ ih1 ih2 ih3 => exact .sigOrBool he ih1 ih2 ih3
  | sigNotBool he _ _ ih1 ih2 => exact .sigNotBool he ih1 ih2
  | bvAbbrev he hr => exact .bvAbbrev he hr
  | unf hs hu _ ih => exact .unf hs hu ih
  | beta hb _ ih => exact .beta hb ih
  | zeta he hA _ ih => exact .zeta he hA ih
  | projStep he hx _ ih => exact .projStep he hx ih
  | projCtor he hh hc hS hn hf _ ih => exact .projCtor he hh hc hS hn hf ih

macro "clashy" : tactic =>
  `(tactic| (exfalso
             try subst_vars
             try simp_all [Res.kind, headStop, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, appFn, stopC_ofNat, stopC_defaultDomain, stopC_bvOfNat, stopC_bvInh,
               stopC_boolInh, stopC_pure, stopC_register, stopC_mux, stopC_hadd, stopC_loop, stopC_beq, stopC_hand, stopC_hor, stopC_compl, bvAbbrevRow_defaultDomain,
               bvAbbrevRow_instInhabitedBool, stopC_of_row, unfoldAt_bvar, unfoldAt_lam, unfoldAt_letE, unfoldAt_proj, unfoldAt_rec, headRedex_rec, stopC_rec, bvAbbrevRow_rec]
             try simp_all [Res.kind, headStop, headRedex, appArgs, appFn, appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, unfoldAt_none_of_beta, unfoldAt_rec, headRedex_rec]))

macro "injy" he:ident he':ident : tactic =>
  `(tactic| (have h := Eq.trans (Eq.symm $he) $he'; revert h; simp only [appN_1, appN_2, appN_3, appN_4, appN_5, appN_6, Expr.app.injEq, Expr.const.injEq, Expr.lam.injEq, Expr.letE.injEq, Expr.proj.injEq, Expr.lit.injEq, Literal.natVal.injEq, List.cons.injEq, and_true, true_and, and_imp, true_implies]; intros; subst_vars))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **functionality** of the relation: two derivations of the same expression in the same valuation, of the same kind (both a type, or both a value), have the same result (the type; or the type and the value). -/
theorem dy_fun {env : Environment} {ρ : Val} {e : Expr} {r : Res} (h : DY env ρ e r) : ∀ {r' : Res}, DY env ρ e r' → r.kind = r'.kind → r = r' := by
  induction h with
  | nat he => intro r' h' hk; cases h' with
    | nat he' => rfl
    | _ => clashy
  | bool he => intro r' h' hk; cases h' with
    | bool he' => rfl
    | _ => clashy
  | domainConfig he => intro r' h' hk; cases h' with
    | domainConfig he' => rfl
    | _ => clashy
  | bitvec he hw ihw => intro r' h' hk; cases h' with
    | bitvec he' hw' =>
      injy he he'
      have := val_eq (ihw hw' rfl)
      subst this; rfl
    | _ => clashy
  | signal he hd ht ihd iht => intro r' h' hk; cases h' with
    | signal he' hd' ht' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2; rfl
    | _ => clashy
  | bvar hb => intro r' h' hk; cases h' with
    | bvar hb' =>
      have := Option.some.inj (hb.symm.trans hb')
      cases this
      rfl
    | _ => clashy
  | natLit he => intro r' h' hk; cases h' with
    | natLit he' =>
      injy he he'
      rfl
    | _ => clashy
  | domDefault he => intro r' h' hk; cases h' with
    | domDefault he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr'; cases hr'
    | _ => clashy
  | bvOfNat he hw hk ihw ihk => intro r' h' hk; cases h' with
    | bvOfNat he' hw' hk' =>
      injy he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1
      have h2 := val_eq (ihk hk' rfl)
      subst h2; rfl
    | _ => clashy
  | bvInhabited he hw ihw => intro r' h' hk; cases h' with
    | bvInhabited he' hw' =>
      injy he he'
      have h1 := val_eq (ihw hw' rfl)
      subst h1; rfl
    | _ => clashy
  | boolInhabited he => intro r' h' hk; cases h' with
    | boolInhabited he' => rfl
    | bvAbbrev he' hr' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr'; cases hr'
    | _ => clashy
  | sigPure he hd ht hx ihd iht ihx => intro r' h' hk; cases h' with
    | sigPure he' hd' ht' hx' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihx hx' rfl)
      subst h3; rfl
    | _ => clashy
  | sigRegister he hd ht hi hs ihd iht ihi ihs => intro r' h' hk; cases h' with
    | sigRegister he' hd' ht' hi' hs' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihs hs' rfl)
      subst h4; rfl
    | _ => clashy
  | sigMux he hd ht hc ha hb ihd iht ihc iha ihb => intro r' h' hk; cases h' with
    | sigMux he' hd' ht' hc' ha' hb' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihc hc' rfl)
      subst h3
      have h4 := val_eq (iha ha' rfl)
      subst h4
      have h5 := val_eq (ihb hb' rfl)
      subst h5; rfl
    | _ => clashy
  | sigAddBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigAddBV he' hd' hw' ha' hb' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashy
  | sigLoop he hd ht hi hf ihd iht ihi ihf => intro r' h' hk; cases h' with
    | sigLoop he' hd' ht' hi' hf' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := ty_eq (iht ht' rfl)
      subst h2
      have h3 := val_eq (ihi hi' rfl)
      subst h3
      have h4 := val_eq (ihf hf' rfl)
      subst h4; rfl
    | _ => clashy
  | lam he hA hb ihA ihb => intro r' h' hk; cases h' with
    | lam he' hA' hb' =>
      injy he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 : ∀ a, _ = _ := fun a => (val_inj (ihb a (hb' a) rfl)).1
      have h2' := funext h2
      subst h2'
      have h3 : _ = _ := funext fun a => eq_of_heq (val_inj (ihb a (hb' a) rfl)).2
      subst h3; rfl
    | _ => clashy
  | letE he hA hv hb ihA ihv ihb => intro r' h' hk; cases h' with
    | letE he' hA' hv' hb' =>
      injy he he'
      have h1 := ty_eq (ihA hA' rfl)
      subst h1
      have h2 := val_eq (ihv hv' rfl)
      subst h2
      exact ihb hb' rfl
    | zeta he' hA' h2 =>
      injy he he'
      have := coreHead_ty hA
      simp_all
    | _ => clashy
  | sigBeqBV he hd hw ha hb ihd ihw iha ihb => intro r' h' hk; cases h' with
    | sigBeqBV he' hd' hw' ha' hb' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h2 := val_eq (ihw hw' rfl)
      subst h2
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashy
  | sigAndBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigAndBool he' hd' ha' hb' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashy
  | sigOrBool he hd ha hb ihd iha ihb => intro r' h' hk; cases h' with
    | sigOrBool he' hd' ha' hb' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3
      have h4 := val_eq (ihb hb' rfl)
      subst h4; rfl
    | _ => clashy
  | sigNotBool he hd ha ihd iha => intro r' h' hk; cases h' with
    | sigNotBool he' hd' ha' =>
      injy he he'
      have h1 := val_eq (ihd hd' rfl)
      subst h1
      have h3 := val_eq (iha ha' rfl)
      subst h3; rfl
    | _ => clashy
  | bvAbbrev he hr => intro r' h' hk; cases h' with
    | bvAbbrev he' hr' =>
      have hc : _ := (Expr.const.inj (he.symm.trans he')).1
      subst hc
      rw [hr] at hr'
      cases hr'
      rfl
    | domDefault he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_defaultDomain] at hr; cases hr
    | boolInhabited he' =>
      have h := he.symm.trans he'
      injection h with h1 h2
      subst h1; rw [bvAbbrevRow_instInhabitedBool] at hr; cases hr
    | unf hs' _ _ =>
      subst he
      have := stopC_of_row hr
      simp_all [headStop, appFn]
    | _ => clashy
  | unf hs hu h ih => intro r' h' hk; cases h' with
    | unf hs' hu' h' =>
      have e1 := Option.some.inj (hu.symm.trans hu')
      subst e1
      exact ih h' rfl
    | _ => clashy
  | beta hb h ih => intro r' h' hk; cases h' with
    | beta hb' h' =>
      have e1 := Option.some.inj (hb.symm.trans hb')
      subst e1
      exact ih h' rfl
    | _ => clashy
  | zeta he hA h ih => intro r' h' hk; cases h' with
    | zeta he' hA' h' =>
      injy he he'
      exact ih h' rfl
    | letE he' hA' hv' hb' =>
      injy he he'
      have := coreHead_ty hA'
      simp_all
    | _ => clashy
  | projStep he hx h ih => intro r' h' hk; cases h' with
    | projStep he' hx' h' =>
      injy he he'
      have e1 := Option.some.inj (hx.symm.trans hx')
      subst e1
      exact ih h' rfl
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injy he he'
      have := whStep_ctor hc' _ hh'
      rw [hx] at this; cases this
    | _ => clashy
  | projCtor he hh hc hS hn hf h ih => intro r' h' hk; cases h' with
    | projCtor he' hh' hc' hS' hn' hf' h' =>
      injy he he'
      have h1 := Expr.const.inj (hh.symm.trans hh')
      obtain ⟨rfl, rfl⟩ := h1
      have h2 := ConstantInfo.ctorInfo.inj (Option.some.inj (hc.symm.trans hc'))
      subst h2
      have h3 := Option.some.inj (hf.symm.trans hf')
      subst h3
      exact ih h' rfl
    | projStep he' hx' h' =>
      injy he he'
      have := whStep_ctor hc _ hh
      rw [hx'] at this; cases this
    | _ => clashy
  | recIota hf hi hr h ih => intro r' h' hk; cases h' with
    | recIota hf' hi' hr' h' =>
      have e1 := Option.some.inj (hr.symm.trans hr')
      subst e1
      exact ih h' rfl
    | _ => clashy

theorem cdy_fun {env : Environment} {ρ : Val} {e : Expr} {α α' : Type} {v : α} {v' : α'} (h : CDY env ρ e α v) (h' : CDY env ρ e α' v') :
    α = α' ∧ HEq v v' := val_inj (dy_fun h h' rfl)

theorem tdy_fun {env : Environment} {ρ : Val} {e : Expr} {T T' : Type} (h : TDY env ρ e T) (h' : TDY env ρ e T') : T = T' := ty_eq (dy_fun h h' rfl)

theorem cdy_eq {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v v' : α} (h : CDY env ρ e α v) (h' : CDY env ρ e α v') : v = v' :=
  eq_of_heq (cdy_fun h h').2

theorem cdy_of_cdx {env : Environment} {ρ : Val} {e : Expr} {α : Type} {v : α} (h : CDX env ρ e α v) : CDY env ρ e α v := dx_to_dy h

/-- the single-environment carrier over `DY` -/
def CircCVY : ConstValueRel := fun env X α v =>
  ∃ d : DefinitionVal, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDY env [] d.value α v

theorem circCVS_to_Y (env : Environment) {X : Name} {α : Type} {v : α} (h : CircCVS env X α v) : CircCVY env X α v := by
  obtain ⟨d, hd, hl, hv⟩ := h
  exact ⟨d, hd, hl, dx_to_dy hv⟩

theorem circCVY_functional : ConstValueFunctional CircCVY := by
  intro env c α β v w ⟨d, hd, _, hv⟩ ⟨d', hd', _, hv'⟩
  rw [hd] at hd'
  have := ConstantInfo.defnInfo.inj (Option.some.inj hd')
  subst this
  exact cdy_fun hv hv'

/-! ### the semantic content of the iota step, proved for all arguments (kernel equations of the original `List.rec`)

`recStep` is a rewrite of a raw `Expr`; it carries no meaning by itself. The meaning of one step is the Lean equation below, true by `rfl` for every argument. A derivation that uses `recIota` is
tied to the ORIGINAL term only by the final statement being accepted by the kernel with `v := ` the original constant (the value built by the rules must be defeq to it), see docs §20. -/

theorem listRec_nil_eq.{u, v} {α : Type u} {motive : List α → Sort v} (n : motive []) (c : (a : α) → (xs : List α) → motive xs → motive (a :: xs)) :
    @List.rec α motive n c [] = n := rfl

theorem listRec_cons_eq.{u, v} {α : Type u} {motive : List α → Sort v} (n : motive []) (c : (a : α) → (xs : List α) → motive xs → motive (a :: xs))
    (a : α) (xs : List α) : @List.rec α motive n c (a :: xs) = c a xs (@List.rec α motive n c xs) := rfl

/-! ### unfolding lemmas from the definitions of `Circuit` pure / bind / next (the fallback for a subterm the iota unit does not reach) -/

theorem circuit_pure_eq {dom : DomainConfig} {W α : Type} (a : α) (b : W) : (Circuit.pure' a : Circuit dom W α) b = (a, b) := rfl
theorem circuit_bind_eq {dom : DomainConfig} {W α β : Type} (m : Circuit dom W α) (k : α → Circuit dom W β) (b : W) :
    (Circuit.bind m k) b = k (m b).fst (m b).snd := rfl
theorem circuit_next_eq {dom : DomainConfig} {S W τ : Type} (r : Reg dom S W τ) (sig : Signal dom τ) (w : W) :
    (Circuit.next r sig) w = ((), r.slot.update sig w) := rfl

/-- a worked use of `recIota`: `List.rec (pure 0) (fun a as ih => pure 1) [Nat]` denotes `Signal.pure 1`; the same equation holds in Lean by `rfl` -/
def recEx : Expr :=
  let lst : Expr := appN ``List.cons [.succ .zero] [.sort (.succ .zero), .const ``Nat [], appN ``List.nil [.succ .zero] [.sort (.succ .zero)]]
  let sigT : Expr := appN ``Signal [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], .const ``Nat []]
  let mot : Expr := .lam `t (appN ``List [.succ .zero] [.sort (.succ .zero)]) sigT .default
  let p (n : Nat) : Expr := appN ``Signal.pure [.zero] [.const ``Sparkle.Core.Domain.defaultDomain [], .const ``Nat [], natEx n]
  let consc : Expr := .lam `a (.sort (.succ .zero)) (.lam `as (appN ``List [.succ .zero] [.sort (.succ .zero)]) (.lam `ih sigT (p 1) .default) .default) .default
  appN ``List.rec [.succ .zero, .succ .zero] [.sort (.succ .zero), mot, p 0, consc, lst]

end Tools.ShippingFGCircuitS1pCD

#print axioms Tools.ShippingFGCircuitS1pCD.circCV_to_S
#print axioms Tools.ShippingFGCircuitS1pCD.circCVS_functional
#print axioms Tools.ShippingFGCircuitS1pCD.dy_fun
