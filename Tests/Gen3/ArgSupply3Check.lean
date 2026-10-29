import Tools.ShippingGen3ArgSupply3
import Tests.Gen3.ExpectedType        -- checkExpected / checkMutant / checkAxioms / cmpTele / stmtOf
set_option autoImplicit false
-- Built: g3sf-88858249 (clean snapshot, exit 0, standard axioms). No `sorry`, no `axiom`, no `native_decide`.

/-! # Checks for Tools/ShippingGen3ArgSupply3.lean (SRC-ARGW batch 3; SRC_ARGW_SUPPLY_FREEZE.md §3.7 option (b))

CONDITIONAL / NOT ACTUAL-RUN SUPPLY / NOT L-FG / NOT FG COMPLETION.

1. **Expected types** (Tests/Gen3/ExpectedType.lean) against INDEPENDENT `Exp_…` restatements of §3.7.3, and
   **mutants** `Mut_…` that must be REJECTED (every one MEANING-CHANGING: a premise, conclusion or body changes).
2. **Controls (proved, about the DEFINITIONS only):**
   * singleton tuple: `EntryKindOk … (.state b 1) ↔ st.kinds[b]? = some k`; an env with one singleton entry is OK;
   * typed non-domain `.state b n`, `n = 0` and `n ≥ 2`: EXCLUDED by `EnvKindOkE` (`ctl_E_state0_excluded`,
     `ctl_E_stateN_excluded`), while rev2's `EnvKindOk` holds VACUOUSLY there at a state with `dom = none`
     (`ctl_old_state0_vac`, `ctl_old_state2_vac`); hence `envKindOk_of_E` is ONE-directional
     (`ctl_old_not_E_state0`, `ctl_old_not_E_state2`), and "no suppliable case lost" is NOT established;
   * `none` and `.domain` source contexts carry no obligation (`ctl_E_none_ctx`, `ctl_E_domain_ctx`).
3. **bundle2 mirror check (RECORD only, SEPARATE):** the compiler checker `unifiedGateBitsBody` /
   `unifiedGateBoolBody` run by `run_cmd` on 2-tuples `bundle2 dom t t x y` at single kinds. Its result is logged; it
   is NOT a claim about actual-run `E` supply in either direction (a mirror rejecting tuples does not show that
   actual runs never create such entries, and a mirror accepting them does not make them suppliable for (b)).
4. Axioms: only `propext`, `Classical.choice`, `Quot.sound` (machine assertion). -/
set_option maxHeartbeats 4000000

namespace Tests.Gen3.ArgSupply3Check
open Lean Meta Elab Command
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingGen3ArgSupply (phKind PhKinding PhKindingLaws LetKindOk)
open Tools.ShippingReaderFuel
open Tools.ShippingReaderFuelProv (InstProv CallPreP)
open Tools.ShippingGen3ArgSupply2 (ReadInv SrcCtx EnvKindOk midExpr ReadSub InstSite PhExt StK SatK)
open Tools.ShippingGen3ArgSupply3 (EntryKindOk EnvKindOkE CallPreKE GoodKE GoodE SatKX)
open Tests.Gen3.ExpectedType (checkExpected checkMutant checkAxioms cmpTele stmtOf)

/-! ## 1. Expected types -/

def Exp_EntryKindOk (HK : PhKinding) (p : ShapePre) (st : MachRead) (k : MixedGateBinder) (m : MachVal) : Prop :=
  match m with
  | .val v     => HK (phKind p.bs st) v k
  | .state b n => n = 1 ∧ st.kinds[b]? = some k
  | .regs _    => True
  | .handle _  => True
  | .unit      => True

def Exp_EnvKindOkE (HK : PhKinding) (p : ShapePre) (st : MachRead) (Δ : SrcCtx) (env : List MachVal) (d : Nat) :
    Prop :=
  Δ.length = d + env.length ∧
  ∀ (j : Nat) (k : MixedGateBinder) (m : MachVal), d ≤ j → Δ[j]? = some (some k) → k ≠ .domain →
    env[j - d]? = some m → EntryKindOk HK p st k m

def Exp_CallPreKE (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | Call.conv env d e st => ∃ Δ, EnvKindOkE HK p st Δ env d ∧ ReadSub senv (midExpr en) Δ e
  | Call.nested env dom αs initsE body st => ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧
      ReadSub senv (midExpr en) Δ e ∧ machRunApp? e = some (dom, αs, initsE, body)
  | Call.inst env c org ks res args st => CallPreP senv (Call.inst env c org ks res args st) ∧
      ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧ InstSite senv e org c ks res args
  | Call.instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ e, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
        machInstCallS? senv e = some (c, ks, ty, args)
  | Call.chain env e st => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopBody _ env e st => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopRoot env e st => ∃ Δ, EnvKindOkE HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e

def Exp_GoodKE (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, CallPreKE HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v)

def Exp_GoodE (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) → PhExt (Call.inSt c) (Call.outSt c v)

def Exp_goodE_readF : Prop :=
  ∀ (senv : StructEnv), ∀ n, GoodE (readF senv n)

def Exp_envKindOk_of_E : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal} {d : Nat}
    (HKL : PhKindingLaws HK), EnvKindOkE HK p st Δ env d → EnvKindOk HK p st Δ env d

def Exp_envKindOkE_ext : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st st₁ : MachRead} {Δ : SrcCtx} {env : List MachVal} {d : Nat}
    (HKL : PhKindingLaws HK), EnvKindOkE HK p st Δ env d → PhExt st st₁ → EnvKindOkE HK p st₁ Δ env d

def Exp_envKindOkE_lift : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal} {d : Nat}
    (o : Option MixedGateBinder), EnvKindOkE HK p st Δ env d → EnvKindOkE HK p st (o :: Δ) env (d + 1)

def Exp_envKindOkE_cons : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal}
    (o : Option MixedGateBinder) (m : MachVal)
    (hm : ∀ k, o = some k → k ≠ .domain → EntryKindOk HK p st k m),
    EnvKindOkE HK p st Δ env 0 → EnvKindOkE HK p st (o :: Δ) (m :: env) 0

def Exp_satK_bindOE : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {α β : Type} [HasSt α]
    [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} {st : MachRead} (hE : GoodE h)
    (hx : SatK HK senv p h x) (hxE : ∀ b, x.run h = some (some b) → PhExt st (HasSt.st b))
    (hf : ∀ b, StK HK senv p b → PhExt st (HasSt.st b) → SatK HK senv p h (f b)),
    SatK HK senv p h (bindO x f)

def Exp_satKE_conv_lam : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.lam nm t b bi) st)) (hst : ReadInv HK senv p st),
    SatK HK senv p h (convStep senv env d (.lam nm t b bi) st)

def Exp_satKE_chain_next : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {us vs : List Level} {a1 a2 a3 a4 b1 b2 b3 b4 hh rhs t rest : Lean.Expr} {n : Name} {bi : BinderInfo}
    (he : e = .app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.bind us) a1) a2) a3) a4)
      (.app (.app (.app (.app (.app (.app (.const ``Sparkle.Core.Circuit.next vs) b1) b2) b3) b4) hh) rhs))
      (.lam n t rest bi))
    (hpre : CallPreKE HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st),
    SatK HK senv p h (chainStep senv env e st)

def Exp_satKE_instSParamFold : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    {st₀ : MachRead} {resTy : Lean.Expr}
    (hpre : CallPreKE HK senv p en (Call.instS env c ks ty args st₀)) (hres : instRes ty args = some resTy)
    {ps : List Lean.Expr} {st : MachRead} (hs : ReadInv HK senv p st) (hx : PhExt st₀ st),
    SatKX HK senv p h st₀ (foldO (instSParam env) (ps, st) resTy.getAppArgs.toList)

def Exp_satKE_loopBody_tail : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {base : Nat} {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    (hne : ∀ (nm : Name) (ty v b : Lean.Expr) (nd : Bool), e ≠ .letE nm ty v b nd)
    (hpre : CallPreKE HK senv p en (Call.loopBody base env e st)) (hst : ReadInv HK senv p st),
    SatK HK senv p h (loopBodyStep base env e st)

def Exp_satKE_conv_app_generic : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    (h2 : machLoopRead? env d (.app f a) = none) (h3 : machRunApp? (.app f a) = none)
    (h4 : machInstCall? senv (.app f a) = none) (h5 : machInstCallS? senv (.app f a) = none)
    (h6 : Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e)
      (.app f a) = none)
    (h7 : machReadV env d (.app f a) = none),
    SatK HK senv p h (convStep senv env d (.app f a) st)

/-! ### Mutants (all MEANING-CHANGING) -/

/-- `n = 1` dropped: any `.state b n` with the slot kind at `b` would count -/
def Mut_EntryKindOk_anyN (HK : PhKinding) (p : ShapePre) (st : MachRead) (k : MixedGateBinder) (m : MachVal) :
    Prop :=
  match m with
  | .val v     => HK (phKind p.bs st) v k
  | .state b _ => st.kinds[b]? = some k
  | .regs _    => True
  | .handle _  => True
  | .unit      => True

/-- the converse direction (FALSE: see `ctl_old_not_E_state0`) -/
def Mut_envKindOk_of_E_conv : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal} {d : Nat}
    (HKL : PhKindingLaws HK), EnvKindOk HK p st Δ env d → EnvKindOkE HK p st Δ env d

/-- extension in the wrong direction -/
def Mut_GoodE_rev (h : Hs) : Prop :=
  ∀ (c : Call) (v : c.Res), h c = some (some v) → PhExt (Call.outSt c v) (Call.inSt c)

/-- no shift of the bound depth -/
def Mut_envKindOkE_lift_noShift : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal} {d : Nat}
    (o : Option MixedGateBinder), EnvKindOkE HK p st Δ env d → EnvKindOkE HK p st (o :: Δ) env d

/-- the new entry's obligation dropped -/
def Mut_envKindOkE_cons_noHm : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx} {env : List MachVal}
    (o : Option MixedGateBinder) (m : MachVal),
    EnvKindOkE HK p st Δ env 0 → EnvKindOkE HK p st (o :: Δ) (m :: env) 0

/-- the extension fact of the first call dropped from the continuation -/
def Mut_satK_bindOE_noExt : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs} {α β : Type} [HasSt α]
    [HasSt β] {x : BM (Option β)} {f : β → BM (Option α)} {st : MachRead} (hE : GoodE h)
    (hx : SatK HK senv p h x) (hxE : ∀ b, x.run h = some (some b) → PhExt st (HasSt.st b))
    (hf : ∀ b, StK HK senv p b → SatK HK senv p h (f b)),
    SatK HK senv p h (bindO x f)

/-- `GoodE` of the table dropped (the second call would have no extension fact) -/
def Mut_satKE_conv_lam_noE : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h)
    {env : List MachVal} {d : Nat} {nm : Name} {t b : Lean.Expr} {bi : BinderInfo} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.lam nm t b bi) st)) (hst : ReadInv HK senv p st),
    SatK HK senv p h (convStep senv env d (.lam nm t b bi) st)

/-- a different invariant (R5's `GoodH`) in the conclusion -/
def Mut_goodE_readF_lenOk : Prop :=
  ∀ (senv : StructEnv), ∀ n, GoodH (readF senv n)

run_cmd liftTermElabM do
  for (t, e) in [(``Tools.ShippingGen3ArgSupply3.EntryKindOk, ``Exp_EntryKindOk),
      (``Tools.ShippingGen3ArgSupply3.EnvKindOkE, ``Exp_EnvKindOkE),
      (``Tools.ShippingGen3ArgSupply3.CallPreKE, ``Exp_CallPreKE),
      (``Tools.ShippingGen3ArgSupply3.GoodKE, ``Exp_GoodKE),
      (``Tools.ShippingGen3ArgSupply3.GoodE, ``Exp_GoodE),
      (``Tools.ShippingGen3ArgSupply3.goodE_readF, ``Exp_goodE_readF),
      (``Tools.ShippingGen3ArgSupply3.envKindOk_of_E, ``Exp_envKindOk_of_E),
      (``Tools.ShippingGen3ArgSupply3.envKindOkE_ext, ``Exp_envKindOkE_ext),
      (``Tools.ShippingGen3ArgSupply3.envKindOkE_lift, ``Exp_envKindOkE_lift),
      (``Tools.ShippingGen3ArgSupply3.envKindOkE_cons, ``Exp_envKindOkE_cons),
      (``Tools.ShippingGen3ArgSupply3.satK_bindOE, ``Exp_satK_bindOE),
      (``Tools.ShippingGen3ArgSupply3.satKE_conv_lam, ``Exp_satKE_conv_lam),
      (``Tools.ShippingGen3ArgSupply3.satKE_chain_next, ``Exp_satKE_chain_next),
      (``Tools.ShippingGen3ArgSupply3.satKE_instSParamFold, ``Exp_satKE_instSParamFold),
      (``Tools.ShippingGen3ArgSupply3.satKE_loopBody_tail, ``Exp_satKE_loopBody_tail),
      (``Tools.ShippingGen3ArgSupply3.satKE_conv_app_generic, ``Exp_satKE_conv_app_generic)] do
    checkExpected t e
  for (t, m) in [(``Tools.ShippingGen3ArgSupply3.EntryKindOk, ``Mut_EntryKindOk_anyN),
      (``Tools.ShippingGen3ArgSupply3.envKindOk_of_E, ``Mut_envKindOk_of_E_conv),
      (``Tools.ShippingGen3ArgSupply3.GoodE, ``Mut_GoodE_rev),
      (``Tools.ShippingGen3ArgSupply3.envKindOkE_lift, ``Mut_envKindOkE_lift_noShift),
      (``Tools.ShippingGen3ArgSupply3.envKindOkE_cons, ``Mut_envKindOkE_cons_noHm),
      (``Tools.ShippingGen3ArgSupply3.satK_bindOE, ``Mut_satK_bindOE_noExt),
      (``Tools.ShippingGen3ArgSupply3.satKE_conv_lam, ``Mut_satKE_conv_lam_noE),
      (``Tools.ShippingGen3ArgSupply3.goodE_readF, ``Mut_goodE_readF_lenOk)] do
    checkMutant t m
  -- the checker itself: an expected statement against its own mutant must fail too
  checkMutant ``Exp_EntryKindOk ``Mut_EntryKindOk_anyN

run_cmd logInfo "GEN3 MUTANTS: all 9 rejections above are MEANING-CHANGING (no signature-only mutant in this file)."
run_cmd logInfo "GEN3 CONDITIONAL: every arm is conditional on GoodKE (hypothesis) and GoodE (proved: goodE_readF); not L-RUN1, not L-FG supply, not FG completion."

/-! ## 2. Controls on the definitions (proved) -/

section Controls
variable {HK : PhKinding} {p : ShapePre}

/-- Singleton tuple: the slot kind itself. -/
theorem ctl_singleton_iff {st : MachRead} {k : MixedGateBinder} {b : Nat} :
    EntryKindOk HK p st k (.state b 1) ↔ st.kinds[b]? = some k := by
  constructor
  · intro hh
    obtain ⟨_, h2⟩ := hh
    exact h2
  · intro hh
    exact ⟨rfl, hh⟩

/-- An environment with ONE singleton loop entry at a typed binder is OK when the slot has that kind. -/
theorem ctl_E_singleton {st : MachRead} {k : MixedGateBinder} {b : Nat} (hk : st.kinds[b]? = some k) :
    EnvKindOkE HK p st [some k] [.state b 1] 0 := by
  refine ⟨rfl, ?_⟩
  intro j k' m _ hΔ _ hm
  cases j with
  | zero =>
    simp only [Nat.sub_zero, List.getElem?_cons_zero, Option.some.injEq] at hΔ hm
    subst hΔ
    subst hm
    exact ⟨rfl, hk⟩
  | succ j => simp at hΔ

/-- Typed non-domain `.state b 0`: EXCLUDED by `EnvKindOkE`. -/
theorem ctl_E_state0_excluded {st : MachRead} {k : MixedGateBinder} {b : Nat} (hk : k ≠ .domain) :
    ¬ EnvKindOkE HK p st [some k] [.state b 0] 0 := by
  intro hh
  obtain ⟨_, h2⟩ := hh
  have h0 := h2 0 k (.state b 0) (Nat.le_refl 0) (by simp) hk (by simp)
  obtain ⟨hn, _⟩ := h0
  exact absurd hn (by decide)

/-- Typed non-domain `.state b n`, `n ≥ 2`: EXCLUDED by `EnvKindOkE`. -/
theorem ctl_E_stateN_excluded {st : MachRead} {k : MixedGateBinder} {b n : Nat} (hn2 : 2 ≤ n)
    (hk : k ≠ .domain) : ¬ EnvKindOkE HK p st [some k] [.state b n] 0 := by
  intro hh
  obtain ⟨_, h2⟩ := hh
  have h0 := h2 0 k (.state b n) (Nat.le_refl 0) (by simp) hk (by simp)
  obtain ⟨hn, _⟩ := h0
  omega

/-- rev2's `EnvKindOk` holds VACUOUSLY at `.state b 0` when `dom = none` (`convBvar` fails, FD:245-253). -/
theorem ctl_old_state0_vac {k : MixedGateBinder} {b : Nat} :
    EnvKindOk HK p ({} : MachRead) [some k] [.state b 0] 0 := by
  refine ⟨rfl, ?_⟩
  intro j k' x st' _ hj _ _ hc
  have hj0 : j = 0 := by
    simp at hj
    omega
  subst hj0
  first
    | cases hc
    | (simp [convBvar] at hc)
    | (unfold convBvar at hc; simp at hc)

/-- … and at `.state b 2` (same reason). -/
theorem ctl_old_state2_vac {k : MixedGateBinder} {b : Nat} :
    EnvKindOk HK p ({} : MachRead) [some k] [.state b 2] 0 := by
  refine ⟨rfl, ?_⟩
  intro j k' x st' _ hj _ _ hc
  have hj0 : j = 0 := by
    simp at hj
    omega
  subst hj0
  first
    | cases hc
    | (simp [convBvar] at hc)
    | (unfold convBvar at hc; simp at hc)

/-- **`envKindOk_of_E` is one-directional** (`n = 0`): rev2 holds, (b) fails. -/
theorem ctl_old_not_E_state0 {b : Nat} :
    EnvKindOk HK p ({} : MachRead) [some (.bits 8)] [.state b 0] 0 ∧
      ¬ EnvKindOkE HK p ({} : MachRead) [some (.bits 8)] [.state b 0] 0 :=
  ⟨ctl_old_state0_vac, ctl_E_state0_excluded (by decide)⟩

/-- **… and `n = 2`.** -/
theorem ctl_old_not_E_state2 {b : Nat} :
    EnvKindOk HK p ({} : MachRead) [some .bool] [.state b 2] 0 ∧
      ¬ EnvKindOkE HK p ({} : MachRead) [some .bool] [.state b 2] 0 :=
  ⟨ctl_old_state2_vac, ctl_E_stateN_excluded (Nat.le_refl 2) (by decide)⟩

/-- A `none` source context carries no obligation (any entry). -/
theorem ctl_E_none_ctx {st : MachRead} {b : Nat} : EnvKindOkE HK p st [none] [.state b 0] 0 := by
  refine ⟨rfl, ?_⟩
  intro j k m _ hΔ _ _
  cases j with
  | zero => simp at hΔ
  | succ j => simp at hΔ

/-- A `.domain` source context carries no obligation (any entry). -/
theorem ctl_E_domain_ctx {st : MachRead} {b : Nat} :
    EnvKindOkE HK p st [some .domain] [.state b 0] 0 := by
  refine ⟨rfl, ?_⟩
  intro j k m _ hΔ hk _
  cases j with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hΔ
    exact absurd hΔ.symm hk
  | succ j => simp at hΔ

end Controls

/-! ## 3. bundle2 mirror check (RECORD only; SEPARATE from actual-run `E` supply) -/

def mirTy8 : Lean.Expr := mkApp (.const ``BitVec []) (inlNatLit 8)
def mirTyB : Lean.Expr := .const ``Bool []
/-- `.bvar 0 ↦ .bits 8`, `.bvar 1 ↦ .bits 8`, `.bvar 2 ↦ .domain`. -/
def mirK88 : Array MixedGateBinder := #[.domain, .bits 8, .bits 8]
def mirKBB : Array MixedGateBinder := #[.domain, .bool, .bool]
/-- `bundle2 dom (BitVec 8) (BitVec 8) x y` (the shape `bundleSlots` builds, FD:228-233, over binders). -/
def mirTup88 : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) (.bvar 2) mirTy8 mirTy8 (.bvar 1) (.bvar 0)
def mirTupBB : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.bundle2 [.zero]) (.bvar 2) mirTyB mirTyB (.bvar 1) (.bvar 0)

run_cmd do
  for (n, b) in [("2-tuple BitVec 8 at .bits 8", unifiedGateBitsBody mirK88 8 mirTup88),
      ("2-tuple BitVec 8 at .bits 16", unifiedGateBitsBody mirK88 16 mirTup88),
      ("2-tuple BitVec 8 at .bool", unifiedGateBoolBody mirK88 mirTup88),
      ("2-tuple Bool at .bool", unifiedGateBoolBody mirKBB mirTupBB),
      ("2-tuple Bool at .bits 1", unifiedGateBitsBody mirKBB 1 mirTupBB),
      ("2-tuple Bool at .bits 2", unifiedGateBitsBody mirKBB 2 mirTupBB)] do
    logInfo m!"GEN3 BUNDLE2 MIRROR RECORD {n}: accepted = {b}"
  logInfo "GEN3 BUNDLE2 MIRROR: a record of the compiler checker only; NOT a claim about actual-run E supply (a mirror rejecting tuples does not prove actual-run coverage; option (b) excludes typed non-domain .state b n, n != 1, by definition)."

/-! ## 4. Axioms -/

run_cmd liftTermElabM do
  for n in [``Tools.ShippingGen3ArgSupply3.apre_push, ``Tools.ShippingGen3ArgSupply3.apre_append,
      ``Tools.ShippingGen3ArgSupply3.phExt_upd, ``Tools.ShippingGen3ArgSupply3.apre_bindLet,
      ``Tools.ShippingGen3ArgSupply3.apre_bindLetNamed, ``Tools.ShippingGen3ArgSupply3.apre_bindLetAlias,
      ``Tools.ShippingGen3ArgSupply3.apre_letIndex, ``Tools.ShippingGen3ArgSupply3.apre_loopLet,
      ``Tools.ShippingGen3ArgSupply3.machReserve_ext, ``Tools.ShippingGen3ArgSupply3.instEntry_ext,
      ``Tools.ShippingGen3ArgSupply3.conv_satE, ``Tools.ShippingGen3ArgSupply3.nested_satE,
      ``Tools.ShippingGen3ArgSupply3.inst_satE, ``Tools.ShippingGen3ArgSupply3.instS_satE,
      ``Tools.ShippingGen3ArgSupply3.chain_satE, ``Tools.ShippingGen3ArgSupply3.loopBody_satE,
      ``Tools.ShippingGen3ArgSupply3.loopRoot_satE, ``Tools.ShippingGen3ArgSupply3.step_goodE,
      ``Tools.ShippingGen3ArgSupply3.goodE_readF, ``Tools.ShippingGen3ArgSupply3.envKindOk_of_E,
      ``Tools.ShippingGen3ArgSupply3.entryKindOk_ext, ``Tools.ShippingGen3ArgSupply3.envKindOkE_ext,
      ``Tools.ShippingGen3ArgSupply3.envKindOkE_lift, ``Tools.ShippingGen3ArgSupply3.envKindOkE_cons,
      ``Tools.ShippingGen3ArgSupply3.satK_bindOE, ``Tools.ShippingGen3ArgSupply3.satKX_foldO,
      ``Tools.ShippingGen3ArgSupply3.readInv_congr, ``Tools.ShippingGen3ArgSupply3.readInv_ws,
      ``Tools.ShippingGen3ArgSupply3.readSub_loopReg, ``Tools.ShippingGen3ArgSupply3.readSub_loopRegs,
      ``Tools.ShippingGen3ArgSupply3.satKE_conv_bvar, ``Tools.ShippingGen3ArgSupply3.satKE_conv_mdata,
      ``Tools.ShippingGen3ArgSupply3.satKE_conv_proj, ``Tools.ShippingGen3ArgSupply3.satKE_conv_letFloat,
      ``Tools.ShippingGen3ArgSupply3.satKE_conv_letRegs, ``Tools.ShippingGen3ArgSupply3.satKE_conv_letHandle,
      ``Tools.ShippingGen3ArgSupply3.satKE_chain_pure, ``Tools.ShippingGen3ArgSupply3.satKE_chain_letFloat,
      ``Tools.ShippingGen3ArgSupply3.satKE_chain_letRegs, ``Tools.ShippingGen3ArgSupply3.satKE_chain_letHandle,
      ``Tools.ShippingGen3ArgSupply3.satKE_conv_lam, ``Tools.ShippingGen3ArgSupply3.satKE_conv_forallE,
      ``Tools.ShippingGen3ArgSupply3.satKE_conv_app_generic, ``Tools.ShippingGen3ArgSupply3.satKE_chain_next,
      ``Tools.ShippingGen3ArgSupply3.satKE_instSParamFold, ``Tools.ShippingGen3ArgSupply3.satKE_loopBody_tail,
      ``ctl_singleton_iff, ``ctl_E_singleton, ``ctl_E_state0_excluded, ``ctl_E_stateN_excluded,
      ``ctl_old_state0_vac, ``ctl_old_state2_vac, ``ctl_old_not_E_state0, ``ctl_old_not_E_state2,
      ``ctl_E_none_ctx, ``ctl_E_domain_ctx] do
    checkAxioms n

end Tests.Gen3.ArgSupply3Check
