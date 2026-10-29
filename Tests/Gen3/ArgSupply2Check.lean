import Tools.ShippingGen3ArgSupply2
import Tests.Gen3.ExpectedType        -- checkExpected / checkMutant / checkAxioms / cmpTele / stmtOf
import Tools.ShippingUnifiedSource    -- concatLitHiE / concatLitLoE / sliceFE (LK3 control expressions)
set_option autoImplicit false
-- WRITTEN, NOT BUILT (no lake/lean run by the author). No `sorry`, no `axiom`, no `native_decide`.

/-! # Checks for Tools/ShippingGen3ArgSupply2.lean (SRC-ARGW batch 2; SRC_ARGW_SUPPLY_FREEZE.md rev2 cbddde96)

CONDITIONAL / NOT ACTUAL-RUN SUPPLY / NOT L-FG / NOT FG COMPLETION. Everything below is a type comparison, a mutant
rejection, a control on hand-written expressions, or an axiom assertion.

1. **Expected types** (Tests/Gen3/ExpectedType.lean): each checked declaration against an INDEPENDENT `Exp_…`
   restatement of the freeze text; `ReadSub`'s constructors `float` / `floatV` / `sparam` / `lamB` by constructor
   type (`checkCtor`). **Mutants** `Mut_…` must be REJECTED; every mutant below is MEANING-CHANGING (none is
   signature-only: each one changes a premise, a conclusion or a definition body, not a binder name or order).
2. **LK3 controls** (rev2 §3.6) on the COMPILER checker `unifiedGateBitsBody` / `unifiedGateBoolBody` (the object a
   mirror `HK` would copy), evaluated by `run_cmd`; no `HK` is adopted here.
   * rev2 §3.6 P1 says `sixArgShape? = some (r, none, none)`; NO arm of `sixArgShape?` (Elab.lean:1538-1548) returns
     two `none`s. P1 is therefore run at every arm with ONE `none` branch: literal-high concat (`ga = none`),
     literal-low concat (`gb = none`), `<$>` slice (`ga = none`, the function).
   * P1: accepted at `.bits r`; rejected at every other listed width and at `.bool` (`uniq` on the permissive arm).
   * P2: width-1 vs Bool: `.bits 1` binder / 1-bit slice not accepted at `.bool`; Bool binder / `Signal.pure true`
     not accepted at `.bits 1`.
   * N1: a deliberately broken checker (six-argument arm returns `true` without `w == r`) must FAIL P1.
   * N2 (RECORD only, no assertion): a wrong-kind binder in the `none` operand position; the run logs whether the
     checker accepts it (rev2 expected "accepted"; the recognisers pin that position to a literal / the slice
     lambda, so "rejected" is the predicted log line — this is not verified by the author).
   * **Stop rule** (rev2 §3.6): if P1 or P2 fails, the `run_cmd` throws `GEN3 LK3 STOP` (the build fails): `uniq`
     does not hold for the mirror, LK3 stops with a report, no `HK` adopted. N1 not detecting also throws.
3. Axioms: only `propext`, `Classical.choice`, `Quot.sound` (machine assertion). -/
set_option maxHeartbeats 4000000

namespace Tests.Gen3.ArgSupply2Check
open Lean Meta Elab Command
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Sparkle.Core.Domain
open Tools.ShippingGen2 (Pkg Pkgs callArgsOkAt)
open Tools.ShippingGen3ArgWidthSrc
open Tools.ShippingCallWidthsEntry (closingNDecl)
open Tools.ShippingGen3ArgSupply (ShapeSigProv SigEq CalleeTeleAll phKind PhKinding PhKindingLaws LetKindOk)
open Tools.ShippingReaderFuel
open Tools.ShippingReaderFuelProv (InstProv CallPreP)
open Tools.ShippingReaderFuelR1 (SigDisj)
open Tools.ShippingMachineShapeUnfold (instBinders)
open Tools.ShippingGen3ArgSupply2 (SigKindsSt InstArgKinds ReadInv SrcCtx inCtx EnvKindOk midExpr ReadSub
  SrcKinding CallSrcKinds MemSrcKinds memNatOf InstSite CallPreK GoodK PhExt SatK)
open Tests.Gen3.ExpectedType (checkExpected checkMutant checkAxioms cmpTele stmtOf)

/-! ## 1. Expected types (independent restatements of the freeze text) -/

def Exp_argWidthAt_of_read : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ∀ k, ArgKindsAtG senv p.d.shape (closingNDecl p.d.shape) k)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q),
    ∀ k, ArgWidthAt P p k

def Exp_argKinds_both_of_G : Prop :=
  ∀ {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat}
    (hD : SigDisj senv)
    (hk : k < sp.insts.length) (htgt : (sp.instOrigins.getD k .ord).child? = none)
    (hS : ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds)
    (hG : ArgKindsAtG senv sp nDecl k),
    ArgKindsAt senv sp nDecl k ∧ ArgKindsAtS senv sp nDecl k

def Exp_SigKindsSt (senv : StructEnv) (st : MachRead) (k : Nat) (c : Name) (kinds : List MixedGateBinder) :
    Prop :=
  match st.instOrigins.toList.getD k .ord with
  | .ord     => ∃ res, senv.inst c = some (kinds, res)
  | .field _ => ∃ ty, senv.instS c = some (kinds, ty)
  | .mem ..  => False

def Exp_InstArgKinds (senv : StructEnv) (st : MachRead) : Prop :=
  ∀ (k : Nat) (c : Name) (js : List Nat) (r : MixedGateBinder) (kinds : List MixedGateBinder),
    st.insts[k]? = some (c, js, r) → SigKindsSt senv st k c kinds →
    js.map (fun a => (st.lets[a]?).map (·.2.1)) = (kinds.filter (· != .domain)).map some

def Exp_ReadInv (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (st : MachRead) : Prop :=
  InstProv senv st ∧ LetKindOk HK p.bs st ∧ InstArgKinds senv st

def Exp_inCtx (p : ShapePre) : SrcCtx := p.bs.reverse.map fun b => some b.2

def Exp_EnvKindOk (HK : PhKinding) (p : ShapePre) (st : MachRead) (Δ : SrcCtx) (env : List MachVal) (d : Nat) :
    Prop :=
  Δ.length = d + env.length ∧
  ∀ (j : Nat) (k : MixedGateBinder) (x : Lean.Expr) (st' : MachRead), d ≤ j → j < d + env.length →
    Δ[j]? = some (some k) → k ≠ .domain →
    convBvar env d j st = some (x, st') → HK (phKind p.bs st) x k

def Exp_midExpr (en : Lean.Expr) : Lean.Expr :=
  machLoopAsLet (Sparkle.Compiler.MachRawSurface.rootFloat
    (Sparkle.Compiler.MachRawSurface.zeroLit inlNatLit canonicalNatLitValue? (inlFoldNat en)))

def Exp_CallSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (res : MixedGateBinder)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e → machInstCall? senv e = some (c, kinds, res, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind) ∧
  (∀ (Δ : SrcCtx) (e : Lean.Expr) (c : Name) (kinds : List MixedGateBinder) (ty : Lean.Expr)
      (args : List Lean.Expr) (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e → machInstCallS? senv e = some (c, kinds, ty, args) →
    (kind, arg) ∈ kinds.zip args → kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)

def Exp_MemSrcKinds (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (e : Lean.Expr) (combo : Bool) (aw dw : Nat) (dom : Lean.Expr) (ops : List Lean.Expr)
    (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) e =
      some (combo, aw, dw, dom, ops) →
    (kind, arg) ∈ [MixedGateBinder.bits aw, .bits dw, .bool, .bits aw].zip ops → SK (Δ ++ inCtx p) arg kind

def Exp_InstSite (senv : StructEnv) (e : Lean.Expr) :
    InstOrigin → Name → List MixedGateBinder → MixedGateBinder → List Lean.Expr → Prop
  | .ord, c, ks, res, args => machInstCall? senv e = some (c, ks, res, args)
  | .mem combo aw dw, c, ks, res, args => ∃ (dom : Lean.Expr) (ops : List Lean.Expr),
      Sparkle.Compiler.MachMemory.memCall? (memNatOf senv) e = some (combo, aw, dw, dom, ops) ∧
      c = Sparkle.Compiler.MachMemory.memChildName combo aw dw ∧
      ks = [.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args = dom :: ops
  | .field _, _, _, _, _ => False

def Exp_CallPreK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | Call.conv env d e st => ∃ Δ, EnvKindOk HK p st Δ env d ∧ ReadSub senv (midExpr en) Δ e
  | Call.nested env dom αs initsE body st => ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧
      ReadSub senv (midExpr en) Δ e ∧ machRunApp? e = some (dom, αs, initsE, body)
  | Call.inst env c org ks res args st => CallPreP senv (Call.inst env c org ks res args st) ∧
      ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧ InstSite senv e org c ks res args
  | Call.instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
        machInstCallS? senv e = some (c, ks, ty, args)
  | Call.chain env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopBody _ env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopRoot env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e

def Exp_GoodK (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, CallPreK HK senv p en c → ReadInv HK senv p (Call.inSt c) → ∀ v, h c = some (some v) →
    ReadInv HK senv p (Call.outSt c v)

/-- `ReadSub.float` (rev2 V4). -/
def Exp_ReadSub_float : Prop :=
  ∀ {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {n2 : Name}
    {t2 v2 w : Lean.Expr} {nd2 : Bool}, ReadSub senv r Δ (.letE nm ty v b nd) →
    Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2 →
    ReadSub senv r Δ (.letE n2 t2 v2 (.letE nm (ty.liftLooseBVars 0 1) w (b.liftLooseBVars 1 1) nd) nd2)

def Exp_ReadSub_floatV : Prop :=
  ∀ {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {nm : Name} {ty v b : Lean.Expr} {nd : Bool},
    ReadSub senv r Δ (.letE nm ty v b nd) →
    ReadSub senv r Δ (Sparkle.Compiler.MachRawSurface.rootFloat v)

def Exp_ReadSub_sparam : Prop :=
  ∀ {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {e : Lean.Expr} {c : Name} {ks : List MixedGateBinder}
    {ty : Lean.Expr} {args : List Lean.Expr} {resTy q : Lean.Expr}, ReadSub senv r Δ e →
    machInstCallS? senv e = some (c, ks, ty, args) → instRes ty args = some resTy →
    q ∈ resTy.getAppArgs.toList → ReadSub senv r Δ q

def Exp_ReadSub_lamB : Prop :=
  ∀ {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {n : Name} {t b : Lean.Expr} {bi : BinderInfo},
    ReadSub senv r Δ (.lam n t b bi) → ReadSub senv r (mixedGateBinderKind? t :: Δ) b

def Exp_instSite_args : Prop :=
  ∀ {SK : SrcKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {Δ : SrcCtx}
    {e : Lean.Expr} {org : InstOrigin} {c : Name} {ks : List MixedGateBinder} {res : MixedGateBinder}
    {args : List Lean.Expr}
    (hC : CallSrcKinds SK senv p en) (hM : MemSrcKinds SK senv p en)
    (hR : ReadSub senv (midExpr en) Δ e) (hS : InstSite senv e org c ks res args),
    ks.length = args.length ∧
    ∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)

def Exp_instSiteS_args : Prop :=
  ∀ {SK : SrcKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {Δ : SrcCtx}
    {e : Lean.Expr} {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    (hC : CallSrcKinds SK senv p en) (hR : ReadSub senv (midExpr en) Δ e)
    (hS : machInstCallS? senv e = some (c, ks, ty, args)),
    ks.length = args.length ∧
    (∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind)) ∧
    (∀ resTy q, instRes ty args = some resTy → q ∈ resTy.getAppArgs.toList →
      ReadSub senv (midExpr en) Δ q)

def Exp_shapePost_binders : Prop :=
  ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr} {sp : MachineShape}
    (h : shapePost ai p m st v = some sp),
    sp.binders = p.bs ++ instBinders sp.insts ++ st.names.toList.zip st.kinds.toList ++
      st.lets.toList.map (fun l => (l.1, l.2.1))

def Exp_PhExt (st st' : MachRead) : Prop :=
  (∀ (i : Nat) (k : MixedGateBinder), st.kinds[i]? = some k → st'.kinds[i]? = some k) ∧
  (∀ (j : Nat) (l : Name × MixedGateBinder × Lean.Expr), st.lets[j]? = some l → st'.lets[j]? = some l) ∧
  (∀ (k : Nat) (c : Name × List Nat × MixedGateBinder), st.insts[k]? = some c → st'.insts[k]? = some c)

def Exp_phKind_ext : Prop :=
  ∀ {bs : List (Name × MixedGateBinder)} {st st' : MachRead} (hx : PhExt st st')
    {x : Lean.Expr} {k : MixedGateBinder} (h : phKind bs st x = some k), phKind bs st' x = some k

def Exp_letKindOk_ext : Prop :=
  ∀ {HK : PhKinding} (HKL : PhKindingLaws HK) {bs : List (Name × MixedGateBinder)}
    {st st' : MachRead} (h : LetKindOk HK bs st) (hx : PhExt st st')
    (hnew : ∀ (j : Nat) (nm : Name) (kd : MixedGateBinder) (v : Lean.Expr),
      st'.lets[j]? = some (nm, kd, v) → st.lets[j]? = none → HK (phKind bs st') v kd),
    LetKindOk HK bs st'

def Exp_envKindOk_cons_vac : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx}
    {env : List MachVal} (o : Option MixedGateBinder) (m : MachVal)
    (hm : ∀ st' : MachRead, convBvar (m :: env) 0 0 st' = none)
    (h : EnvKindOk HK p st Δ env 0), EnvKindOk HK p st (o :: Δ) (m :: env) 0

def Exp_satK_conv_bvar : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d j : Nat} {st : MachRead} (hst : ReadInv HK senv p st),
    SatK HK senv p h (convStep senv env d (.bvar j) st)

def Exp_satK_conv_letFloat : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreK HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st) {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2),
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

def Exp_satK_conv_letRegs : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead} (hpre : CallPreK HK senv p en (Call.conv env d (.letE nm ty v b nd) st))
    (hst : ReadInv HK senv p st)
    (hnf : ∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2)
    (hnl : (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false)
    {q : Nat} (hq : machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = some q),
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

def Exp_satK_chain_pure : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {us : List Level} {a1 a2 a3 x : Lean.Expr}
    (he : e = .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.pure' us) a1) a2) a3) x)
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st),
    SatK HK senv p h (chainStep senv env e st)

def Exp_satK_chain_letFloat : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {nm : Name} {ty v b : Lean.Expr}
    {nd : Bool} {st : MachRead} (he : e = .letE nm ty v b nd)
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st)
    {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2),
    SatK HK senv p h (chainStep senv env e st)

/-! ### Meaning-changing mutants (each must be REJECTED; none is signature-only) -/

/-- rev0-style `.ord`-only row instead of the origin-indexed `ArgKindsAtG` (meaning: `.field` rows not required) -/
def Mut_argWidthAt_of_read_ord : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ∀ k, ArgKindsAt senv p.d.shape (closingNDecl p.d.shape) k)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q),
    ∀ k, ArgWidthAt P p k

/-- conclusion weakened to entry 0 -/
def Mut_argWidthAt_of_read_k0 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (P : Pkgs ι dom) (p : Pkg ι dom) {senv senv₀ : StructEnv}
    (hKD  : p.kD = closingNDecl p.d.shape)
    (hSIG : ShapeSigProv senv p.d.shape)
    (hARG : ∀ k, ArgKindsAtG senv p.d.shape (closingNDecl p.d.shape) k)
    (hENV : ∀ c q, P c = some q → SigEq senv senv₀ c)
    (hTEL : ∀ c q, P c = some q → CalleeTeleAll senv₀ c q),
    ArgWidthAt P p 0

/-- `SigDisj` dropped -/
def Mut_argKinds_both_of_G_noDisj : Prop :=
  ∀ {senv : StructEnv} {sp : MachineShape} {nDecl k : Nat}
    (hk : k < sp.insts.length) (htgt : (sp.instOrigins.getD k .ord).child? = none)
    (hS : ∃ kinds, SigKindsAt senv sp k (sp.insts[k]).1 kinds)
    (hG : ArgKindsAtG senv sp nDecl k),
    ArgKindsAt senv sp nDecl k ∧ ArgKindsAtS senv sp nDecl k

/-- `.field` admitted (`True` instead of `False`) -/
def Mut_InstSite_field (senv : StructEnv) (e : Lean.Expr) :
    InstOrigin → Name → List MixedGateBinder → MixedGateBinder → List Lean.Expr → Prop
  | .ord, c, ks, res, args => machInstCall? senv e = some (c, ks, res, args)
  | .mem combo aw dw, c, ks, res, args => ∃ (dom : Lean.Expr) (ops : List Lean.Expr),
      Sparkle.Compiler.MachMemory.memCall? (memNatOf senv) e = some (combo, aw, dw, dom, ops) ∧
      c = Sparkle.Compiler.MachMemory.memChildName combo aw dw ∧
      ks = [.domain, .bits aw, .bits dw, .bool, .bits aw] ∧ res = .bits dw ∧ args = dom :: ops
  | .field _, _, _, _, _ => True

/-- memory kinds with `aw`/`dw` swapped -/
def Mut_MemSrcKinds_swap (SK : SrcKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ (Δ : SrcCtx) (e : Lean.Expr) (combo : Bool) (aw dw : Nat) (dom : Lean.Expr) (ops : List Lean.Expr)
    (kind : MixedGateBinder) (arg : Lean.Expr),
    ReadSub senv (midExpr en) Δ e →
    Sparkle.Compiler.MachMemory.memCall? (fun e => canonicalNatLitValue? e <|> senv.natOf e) e =
      some (combo, aw, dw, dom, ops) →
    (kind, arg) ∈ [MixedGateBinder.bits dw, .bits aw, .bool, .bits aw].zip ops → SK (Δ ++ inCtx p) arg kind

/-- the `d ≤ j` guard dropped (obligations on lambda-bound indices too) -/
def Mut_EnvKindOk_noD (HK : PhKinding) (p : ShapePre) (st : MachRead) (Δ : SrcCtx) (env : List MachVal)
    (d : Nat) : Prop :=
  Δ.length = d + env.length ∧
  ∀ (j : Nat) (k : MixedGateBinder) (x : Lean.Expr) (st' : MachRead), j < d + env.length →
    Δ[j]? = some (some k) → k ≠ .domain →
    convBvar env d j st = some (x, st') → HK (phKind p.bs st) x k

/-- the argument-kind conjunct dropped -/
def Mut_ReadInv_noArgs (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (st : MachRead) : Prop :=
  InstProv senv st ∧ LetKindOk HK p.bs st

/-- `.inst` without the kept call site (rev1's form) -/
def Mut_CallPreK_noSite (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Call → Prop
  | Call.conv env d e st => ∃ Δ, EnvKindOk HK p st Δ env d ∧ ReadSub senv (midExpr en) Δ e
  | Call.nested env dom αs initsE body st => ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧
      ReadSub senv (midExpr en) Δ e ∧ machRunApp? e = some (dom, αs, initsE, body)
  | Call.inst env c org ks res args st => CallPreP senv (Call.inst env c org ks res args st)
  | Call.instS env c ks ty args st => senv.instS c = some (ks, ty) ∧
      ∃ Δ e, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e ∧
        machInstCallS? senv e = some (c, ks, ty, args)
  | Call.chain env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopBody _ env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e
  | Call.loopRoot env e st => ∃ Δ, EnvKindOk HK p st Δ env 0 ∧ ReadSub senv (midExpr en) Δ e

/-- the input-state invariant dropped (claims `ReadInv` of outputs from ANY input) -/
def Mut_GoodK_noIn (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) (h : Hs) : Prop :=
  ∀ c, CallPreK HK senv p en c → ∀ v, h c = some (some v) → ReadInv HK senv p (Call.outSt c v)

/-- SK read in the bare context `Δ` (the peeled inputs not appended) -/
def Mut_instSite_args_ctx : Prop :=
  ∀ {SK : SrcKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {Δ : SrcCtx}
    {e : Lean.Expr} {org : InstOrigin} {c : Name} {ks : List MixedGateBinder} {res : MixedGateBinder}
    {args : List Lean.Expr}
    (hC : CallSrcKinds SK senv p en) (hM : MemSrcKinds SK senv p en)
    (hR : ReadSub senv (midExpr en) Δ e) (hS : InstSite senv e org c ks res args),
    ks.length = args.length ∧
    ∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK Δ arg kind)

/-- the constructed-parameter conjunct dropped -/
def Mut_instSiteS_args_noParams : Prop :=
  ∀ {SK : SrcKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {Δ : SrcCtx}
    {e : Lean.Expr} {c : Name} {ks : List MixedGateBinder} {ty : Lean.Expr} {args : List Lean.Expr}
    (hC : CallSrcKinds SK senv p en) (hR : ReadSub senv (midExpr en) Δ e)
    (hS : machInstCallS? senv e = some (c, ks, ty, args)),
    ks.length = args.length ∧
    (∀ kind arg, (kind, arg) ∈ ks.zip args →
      ReadSub senv (midExpr en) Δ arg ∧ (kind ≠ .domain → SK (Δ ++ inCtx p) arg kind))

/-- the let part dropped -/
def Mut_shapePost_binders_noLets : Prop :=
  ∀ {ai : Bool} {p : ShapePre} {m : ShapeMid} {st : MachRead} {v : Lean.Expr} {sp : MachineShape}
    (h : shapePost ai p m st v = some sp),
    sp.binders = p.bs ++ instBinders sp.insts ++ st.names.toList.zip st.kinds.toList

/-- extension in the wrong direction -/
def Mut_phKind_ext_rev : Prop :=
  ∀ {bs : List (Name × MixedGateBinder)} {st st' : MachRead} (hx : PhExt st' st)
    {x : Lean.Expr} {k : MixedGateBinder} (h : phKind bs st x = some k), phKind bs st' x = some k

/-- the new-let obligation dropped -/
def Mut_letKindOk_ext_noNew : Prop :=
  ∀ {HK : PhKinding} (HKL : PhKindingLaws HK) {bs : List (Name × MixedGateBinder)}
    {st st' : MachRead} (h : LetKindOk HK bs st) (hx : PhExt st st'),
    LetKindOk HK bs st'

/-- vacuity of the new entry dropped -/
def Mut_envKindOk_cons_vac_noVac : Prop :=
  ∀ {HK : PhKinding} {p : ShapePre} {st : MachRead} {Δ : SrcCtx}
    {env : List MachVal} (o : Option MixedGateBinder) (m : MachVal)
    (h : EnvKindOk HK p st Δ env 0), EnvKindOk HK p st (o :: Δ) (m :: env) 0

/-- the call-site precondition dropped -/
def Mut_satK_conv_letFloat_noPre : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool}
    {st : MachRead}
    (hst : ReadInv HK senv p st) {n2 : Name} {t2 v2 w : Lean.Expr} {nd2 : Bool}
    (hf : Sparkle.Compiler.MachRawSurface.rootFloat v = .letE n2 t2 v2 w nd2),
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

/-- the `bind` arm instead of `pure'` (an arm that is OPEN, so this is a different claim) -/
def Mut_satK_chain_pure_bind : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (hG : GoodK HK senv p en h) {env : List MachVal} {e : Lean.Expr} {st : MachRead}
    {us : List Level} {a1 a2 a3 x : Lean.Expr}
    (he : e = .app (.app (.app (.app (.const ``Sparkle.Core.Circuit.bind us) a1) a2) a3) x)
    (hpre : CallPreK HK senv p en (Call.chain env e st)) (hst : ReadInv HK senv p st),
    SatK HK senv p h (chainStep senv env e st)

/-- A constructor's type against an expected `Prop` statement. -/
def checkCtor (ctor exp : Name) : MetaM Unit := do
  let ci ← getConstInfo ctor
  cmpTele s!"{ctor}" ci.type (← stmtOf exp)
  logInfo m!"GEN3 TYPE OK {ctor} against {exp}"

run_cmd liftTermElabM do
  for (t, e) in [(``Tools.ShippingGen3ArgSupply2.argWidthAt_of_read, ``Exp_argWidthAt_of_read),
      (``Tools.ShippingGen3ArgSupply2.argKinds_both_of_G, ``Exp_argKinds_both_of_G),
      (``Tools.ShippingGen3ArgSupply2.SigKindsSt, ``Exp_SigKindsSt),
      (``Tools.ShippingGen3ArgSupply2.InstArgKinds, ``Exp_InstArgKinds),
      (``Tools.ShippingGen3ArgSupply2.ReadInv, ``Exp_ReadInv),
      (``Tools.ShippingGen3ArgSupply2.inCtx, ``Exp_inCtx),
      (``Tools.ShippingGen3ArgSupply2.EnvKindOk, ``Exp_EnvKindOk),
      (``Tools.ShippingGen3ArgSupply2.midExpr, ``Exp_midExpr),
      (``Tools.ShippingGen3ArgSupply2.CallSrcKinds, ``Exp_CallSrcKinds),
      (``Tools.ShippingGen3ArgSupply2.MemSrcKinds, ``Exp_MemSrcKinds),
      (``Tools.ShippingGen3ArgSupply2.InstSite, ``Exp_InstSite),
      (``Tools.ShippingGen3ArgSupply2.CallPreK, ``Exp_CallPreK),
      (``Tools.ShippingGen3ArgSupply2.GoodK, ``Exp_GoodK),
      (``Tools.ShippingGen3ArgSupply2.instSite_args, ``Exp_instSite_args),
      (``Tools.ShippingGen3ArgSupply2.instSiteS_args, ``Exp_instSiteS_args),
      (``Tools.ShippingGen3ArgSupply2.shapePost_binders, ``Exp_shapePost_binders),
      (``Tools.ShippingGen3ArgSupply2.PhExt, ``Exp_PhExt),
      (``Tools.ShippingGen3ArgSupply2.phKind_ext, ``Exp_phKind_ext),
      (``Tools.ShippingGen3ArgSupply2.letKindOk_ext, ``Exp_letKindOk_ext),
      (``Tools.ShippingGen3ArgSupply2.envKindOk_cons_vac, ``Exp_envKindOk_cons_vac),
      (``Tools.ShippingGen3ArgSupply2.satK_conv_bvar, ``Exp_satK_conv_bvar),
      (``Tools.ShippingGen3ArgSupply2.satK_conv_letFloat, ``Exp_satK_conv_letFloat),
      (``Tools.ShippingGen3ArgSupply2.satK_conv_letRegs, ``Exp_satK_conv_letRegs),
      (``Tools.ShippingGen3ArgSupply2.satK_chain_pure, ``Exp_satK_chain_pure),
      (``Tools.ShippingGen3ArgSupply2.satK_chain_letFloat, ``Exp_satK_chain_letFloat)] do
    checkExpected t e
  checkCtor ``Tools.ShippingGen3ArgSupply2.ReadSub.float ``Exp_ReadSub_float
  checkCtor ``Tools.ShippingGen3ArgSupply2.ReadSub.floatV ``Exp_ReadSub_floatV
  checkCtor ``Tools.ShippingGen3ArgSupply2.ReadSub.sparam ``Exp_ReadSub_sparam
  checkCtor ``Tools.ShippingGen3ArgSupply2.ReadSub.lamB ``Exp_ReadSub_lamB
  for (t, m) in [(``Tools.ShippingGen3ArgSupply2.argWidthAt_of_read, ``Mut_argWidthAt_of_read_ord),
      (``Tools.ShippingGen3ArgSupply2.argWidthAt_of_read, ``Mut_argWidthAt_of_read_k0),
      (``Tools.ShippingGen3ArgSupply2.argKinds_both_of_G, ``Mut_argKinds_both_of_G_noDisj),
      (``Tools.ShippingGen3ArgSupply2.InstSite, ``Mut_InstSite_field),
      (``Tools.ShippingGen3ArgSupply2.MemSrcKinds, ``Mut_MemSrcKinds_swap),
      (``Tools.ShippingGen3ArgSupply2.EnvKindOk, ``Mut_EnvKindOk_noD),
      (``Tools.ShippingGen3ArgSupply2.ReadInv, ``Mut_ReadInv_noArgs),
      (``Tools.ShippingGen3ArgSupply2.CallPreK, ``Mut_CallPreK_noSite),
      (``Tools.ShippingGen3ArgSupply2.GoodK, ``Mut_GoodK_noIn),
      (``Tools.ShippingGen3ArgSupply2.instSite_args, ``Mut_instSite_args_ctx),
      (``Tools.ShippingGen3ArgSupply2.instSiteS_args, ``Mut_instSiteS_args_noParams),
      (``Tools.ShippingGen3ArgSupply2.shapePost_binders, ``Mut_shapePost_binders_noLets),
      (``Tools.ShippingGen3ArgSupply2.phKind_ext, ``Mut_phKind_ext_rev),
      (``Tools.ShippingGen3ArgSupply2.letKindOk_ext, ``Mut_letKindOk_ext_noNew),
      (``Tools.ShippingGen3ArgSupply2.envKindOk_cons_vac, ``Mut_envKindOk_cons_vac_noVac),
      (``Tools.ShippingGen3ArgSupply2.satK_conv_letFloat, ``Mut_satK_conv_letFloat_noPre),
      (``Tools.ShippingGen3ArgSupply2.satK_chain_pure, ``Mut_satK_chain_pure_bind)] do
    checkMutant t m
  -- the checker itself: an expected statement against its own mutant must fail too
  checkMutant ``Exp_GoodK ``Mut_GoodK_noIn

run_cmd logInfo "GEN3 MUTANTS: all 17 rejections above are MEANING-CHANGING (no signature-only mutant in this file)."
run_cmd logInfo "GEN3 CONDITIONAL: SC0 G-form / instSite_args / LK1 arms are conditional (suppliers, GoodK table, CallSrcKinds/MemSrcKinds are premises); not L-RUN1, not L-FG supply, not FG completion."

/-! ## 2. LK3 controls on the compiler checker (rev2 §3.6; evaluated, not proved) -/

def lk3Dom : Lean.Expr := .bvar 1
/-- `.bvar 0 ↦ .bits 8`, `.bvar 1 ↦ .domain` (`mixedGateBVar?`, Elab.lean:2352-2353). -/
def lk3K8 : Array MixedGateBinder := #[.domain, .bits 8]
/-- `5#4 ++ x` (literal-high concat): `sixArgShape? = some (12, none, some 8)`. -/
def lk3Hi : Lean.Expr := Tools.ShippingUnifiedSource.concatLitHiE lk3Dom 4 5 8 (.bvar 0)
/-- `x ++ 5#4` (literal-low concat): `sixArgShape? = some (12, some 8, none)`. -/
def lk3Lo : Lean.Expr := Tools.ShippingUnifiedSource.concatLitLoE lk3Dom 8 4 5 (.bvar 0)
/-- `extractLsb' 2 3 <$> x` (slice): `sixArgShape? = some (3, none, some 8)`. -/
def lk3Sl : Lean.Expr := Tools.ShippingUnifiedSource.sliceFE lk3Dom `x 8 2 3 (.bvar 0)

def lk3Bits : Array MixedGateBinder → Nat → Lean.Expr → Bool := unifiedGateBitsBody
def lk3Bool : Array MixedGateBinder → Lean.Expr → Bool := unifiedGateBoolBody

/-- `uniq` at one expression: accepted at `.bits r`, rejected at every other listed width and at `.bool`. -/
def lk3Uniq (bits : Array MixedGateBinder → Nat → Lean.Expr → Bool) (bool : Array MixedGateBinder → Lean.Expr → Bool)
    (kinds : Array MixedGateBinder) (e : Lean.Expr) (r : Nat) (others : List Nat) : Bool :=
  bits kinds r e && others.all (fun r' => r' == r || !bits kinds r' e) && !bool kinds e

def lk3P1Hi : Bool := lk3Uniq lk3Bits lk3Bool lk3K8 lk3Hi 12 [0, 1, 4, 8, 11, 13, 16]
def lk3P1Lo : Bool := lk3Uniq lk3Bits lk3Bool lk3K8 lk3Lo 12 [0, 1, 4, 8, 11, 13, 16]
def lk3P1Sl : Bool := lk3Uniq lk3Bits lk3Bool lk3K8 lk3Sl 3 [0, 1, 2, 4, 5, 8]

def lk3KB1 : Array MixedGateBinder := #[.bits 1]
def lk3KBool : Array MixedGateBinder := #[.bool]
/-- a 1-bit slice -/
def lk3Sl1 : Lean.Expr := Tools.ShippingUnifiedSource.sliceFE lk3Dom `x 8 5 1 (.bvar 0)
/-- `Signal.pure true` (a Bool gate body) -/
def lk3True : Lean.Expr :=
  mkApp3 (.const ``Sparkle.Core.Signal.Signal.pure [.zero]) lk3Dom (.const ``Bool []) (.const ``Bool.true [])

def lk3P2BinderBits : Bool := lk3Bits lk3KB1 1 (.bvar 0) && !lk3Bool lk3KB1 (.bvar 0)
def lk3P2BinderBool : Bool := lk3Bool lk3KBool (.bvar 0) && !lk3Bits lk3KBool 1 (.bvar 0)
def lk3P2Slice1 : Bool := lk3Bits lk3K8 1 lk3Sl1 && !lk3Bool lk3K8 lk3Sl1
def lk3P2True : Bool := lk3Bool lk3K8 lk3True && !lk3Bits lk3K8 1 lk3True

/-- N1: a deliberately broken checker — the six-argument arm returns `true` without the `w == r` test. -/
def lk3Broken (kinds : Array MixedGateBinder) (w : Nat) (e : Lean.Expr) : Bool :=
  match sixArgShape? e with
  | some _ => true
  | none => unifiedGateBitsBody kinds w e

def lk3N1Hi : Bool := lk3Uniq lk3Broken lk3Bool lk3K8 lk3Hi 12 [11, 13]
def lk3N1Sl : Bool := lk3Uniq lk3Broken lk3Bool lk3K8 lk3Sl 3 [2, 4]

/-- N2: the `none`-branch operand (argument 4: the literal / the slice function) replaced by a `.bool` binder. -/
def lk3KN2 : Array MixedGateBinder := #[.domain, .bool, .bits 8]
def lk3HiN2 : Lean.Expr := mkAppN lk3Hi.getAppFn (lk3Hi.getAppArgs.set! 4 (.bvar 1))
def lk3SlN2 : Lean.Expr := mkAppN lk3Sl.getAppFn (lk3Sl.getAppArgs.set! 4 (.bvar 1))
def lk3N2Hi : Bool := lk3Bits lk3KN2 12 lk3HiN2
def lk3N2Sl : Bool := lk3Bits lk3KN2 3 lk3SlN2

run_cmd do
  for (n, b) in [("P1 literal-high concat", lk3P1Hi), ("P1 literal-low concat", lk3P1Lo),
      ("P1 slice", lk3P1Sl), ("P2 .bits 1 binder", lk3P2BinderBits), ("P2 Bool binder", lk3P2BinderBool),
      ("P2 1-bit slice", lk3P2Slice1), ("P2 Signal.pure true", lk3P2True)] do
    unless b do
      throwError m!"GEN3 LK3 STOP: {n} FAILED: uniq does NOT hold for the compiler checker; LK3 stops, no HK adopted (rev2 §3.6)"
    logInfo m!"GEN3 LK3 {n}: PASS"
  for (n, b) in [("N1 broken checker, literal-high", lk3N1Hi), ("N1 broken checker, slice", lk3N1Sl)] do
    if b then
      throwError m!"GEN3 LK3 CONTROL BROKEN: {n} passed P1; the P1 control does not detect a non-unique checker"
    logInfo m!"GEN3 LK3 {n}: P1 FAILS on the broken checker (control detects non-uniqueness)"
  for (n, b) in [("N2 wrong-kind binder in the literal position", lk3N2Hi),
      ("N2 wrong-kind binder in the slice-function position", lk3N2Sl)] do
    logInfo m!"GEN3 LK3 RECORD {n}: accepted = {b} (rev2 expected: accepted)"

/-! ## 3. Axioms -/

run_cmd liftTermElabM do
  for n in [``Tools.ShippingGen3ArgSupply2.sigKindsAt_of_ord, ``Tools.ShippingGen3ArgSupply2.sigKindsAt_of_field,
      ``Tools.ShippingGen3ArgSupply2.sigKindsAt_of_mem, ``Tools.ShippingGen3ArgSupply2.argKindsAt_of_G,
      ``Tools.ShippingGen3ArgSupply2.argKindsAtS_of_G, ``Tools.ShippingGen3ArgSupply2.callArgsOk_of_sigKindsG,
      ``Tools.ShippingGen3ArgSupply2.argWidthAt_of_read, ``Tools.ShippingGen3ArgSupply2.argKinds_both_of_G,
      ``Tools.ShippingGen3ArgSupply2.readSub_inlSpine, ``Tools.ShippingGen3ArgSupply2.readSub_argsAcc,
      ``Tools.ShippingGen3ArgSupply2.readSub_getAppArgs, ``Tools.ShippingGen3ArgSupply2.readSub_getElem!,
      ``Tools.ShippingGen3ArgSupply2.argsT_length_of_arity, ``Tools.ShippingGen3ArgSupply2.machInstCall?_args,
      ``Tools.ShippingGen3ArgSupply2.machInstCallS?_args, ``Tools.ShippingGen3ArgSupply2.memCall?_ops,
      ``Tools.ShippingGen3ArgSupply2.memCall?_arity, ``Tools.ShippingGen3ArgSupply2.instSite_args,
      ``Tools.ShippingGen3ArgSupply2.instSiteS_args, ``Tools.ShippingGen3ArgSupply2.shapePost_binders,
      ``Tools.ShippingGen3ArgSupply2.shapePost_letBinders, ``Tools.ShippingGen3ArgSupply2.phKind_ext,
      ``Tools.ShippingGen3ArgSupply2.letKindOk_ext, ``Tools.ShippingGen3ArgSupply2.letKindOk_sameLets,
      ``Tools.ShippingGen3ArgSupply2.letKindOk_empty, ``Tools.ShippingGen3ArgSupply2.readInv_empty,
      ``Tools.ShippingGen3ArgSupply2.phKindingLaws_fvar_iff, ``Tools.ShippingGen3ArgSupply2.phKindingLaws_let_iff,
      ``Tools.ShippingGen3ArgSupply2.phKindingLaws_let_kind, ``Tools.ShippingGen3ArgSupply2.convBvar_st,
      ``Tools.ShippingGen3ArgSupply2.convBvar_cons0, ``Tools.ShippingGen3ArgSupply2.envKindOk_cons_vac,
      ``Tools.ShippingGen3ArgSupply2.callPreK_conv_float, ``Tools.ShippingGen3ArgSupply2.callPreK_conv_letVac,
      ``Tools.ShippingGen3ArgSupply2.callPreK_chain_float, ``Tools.ShippingGen3ArgSupply2.callPreK_chain_letVac,
      ``Tools.ShippingGen3ArgSupply2.callPreK_chain_pureArg, ``Tools.ShippingGen3ArgSupply2.satK_conv_bvar,
      ``Tools.ShippingGen3ArgSupply2.satK_conv_mdata, ``Tools.ShippingGen3ArgSupply2.satK_conv_proj,
      ``Tools.ShippingGen3ArgSupply2.satK_conv_letFloat, ``Tools.ShippingGen3ArgSupply2.satK_conv_letRegs,
      ``Tools.ShippingGen3ArgSupply2.satK_conv_letHandle, ``Tools.ShippingGen3ArgSupply2.satK_chain_pure,
      ``Tools.ShippingGen3ArgSupply2.satK_chain_letFloat, ``Tools.ShippingGen3ArgSupply2.satK_chain_letRegs,
      ``Tools.ShippingGen3ArgSupply2.satK_chain_letHandle] do
    checkAxioms n

end Tests.Gen3.ArgSupply2Check
