import Tools.ShippingGen3ArgSupply4
import Tests.Gen3.ExpectedType        -- checkExpected / checkMutant / checkAxioms / cmpTele / stmtOf
set_option autoImplicit false
-- WRITTEN, NOT BUILT (batch 4; no lake/lean run by the author). No `sorry`, no `axiom`, no `native_decide`.

/-! # Checks for Tools/ShippingGen3ArgSupply4.lean (SRC-ARGW batch 4)

CONDITIONAL / NOT ACTUAL-RUN SUPPLY / NOT L-RUN / NOT L-FG / NOT FG COMPLETION. The LK1 statement checked here is a
SKELETON whose open arms are explicit premises (`LK1Open`).

1. **Expected types** (Tests/Gen3/ExpectedType.lean) against INDEPENDENT `Exp_…` restatements: the G2/G4 argument
   lemmas, the G2/G3/G4 arms, three of the open-arm premises, the `LK1Open` constructor (its exact field list), and
   the skeleton (`step_goodKE`, `goodKE_readF_of_open`).
2. **Mutants** `Mut_…` that must be REJECTED; every one is MEANING-CHANGING (a premise, conclusion, binder context
   or field changes).
3. **Axioms**: only `propext`, `Classical.choice`, `Quot.sound`. -/
set_option maxHeartbeats 4000000

namespace Tests.Gen3.ArgSupply4Check
open Lean Meta Elab Command
open Sparkle.Compiler.Elab
open Sparkle.Compiler.MachInstOrigin (InstOrigin)
open Tools.ShippingGen3ArgSupply (phKind PhKinding PhKindingLaws LetKindOk)
open Tools.ShippingReaderFuel
open Tools.ShippingGen3ArgSupply2 (ReadInv SrcCtx ReadSub PhExt StK SatK GoodK)
open Tools.ShippingGen3ArgSupply3 (EntryKindOk EnvKindOkE CallPreKE GoodKE GoodE)
open Tools.ShippingGen3ArgSupply4 (ArmG5 ArmG6 ArmG11 ArmG12conv ArmG12chain ArmG17user ArmG18 ArmG20 LK1Open)
open Tests.Gen3.ExpectedType (checkExpected checkMutant checkAxioms cmpTele stmtOf)

/-! ## 1. Expected types -/

def Exp_regView?_all : Prop :=
  ∀ (P : Lean.Expr → Prop) (fn : Lean.Expr) (args : Array Lean.Expr) (d α i x : Lean.Expr)
    (hall : ∀ a ∈ args, P a) (h : regView? fn args = some (d, α, i, x)),
    P d ∧ P x

def Exp_machRunApp?_readSub : Prop :=
  ∀ {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {e dom αs is body : Lean.Expr}
    (hR : ReadSub senv r Δ e) (h : machRunApp? e = some (dom, αs, is, body)),
    ReadSub senv r Δ dom ∧ ∃ t : Lean.Expr, ReadSub senv r (mixedGateBinderKind? t :: Δ) body

def Exp_satKE_conv_bareReg : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    {dom α init x : Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = some (dom, α, init, x)),
    SatK HK senv p h (convStep senv env d (.app f a) st)

def Exp_satKE_conv_loopRead : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {h : Hs}
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead} (hst : ReadInv HK senv p st)
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none)
    {i : Nat} (h2 : machLoopRead? env d (.app f a) = some i),
    SatK HK senv p h (convStep senv env d (.app f a) st)

def Exp_satKE_nested : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {dom αs initsE body : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.nested env dom αs initsE body st)) (hst : ReadInv HK senv p st),
    SatK HK senv p h (nestedStep senv env dom αs initsE body st)

def Exp_ArmG11 (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    (∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2) →
    (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false →
    machTailV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none →
    machHandleV env 0 (Sparkle.Compiler.MachRawSurface.rootFloat v) = none →
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

def Exp_ArmG12conv (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    (∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2) →
    (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = true →
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

def Exp_ArmG20 (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {e : Lean.Expr} {st : MachRead},
    CallPreKE HK senv p en (Call.loopRoot env e st) → ReadInv HK senv p st →
    SatK HK senv p h (loopRootStep senv env e st)

/-- The constructor of `LK1Open`: EXACTLY the eight open arms, in this order. -/
def Exp_LK1Open_mk : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    (g5 : ArmG5 HK senv p en) (g6 : ArmG6 HK senv p en) (g11 : ArmG11 HK senv p en)
    (g12conv : ArmG12conv HK senv p en) (g12chain : ArmG12chain HK senv p en)
    (g17user : ArmG17user HK senv p en) (g18 : ArmG18 HK senv p en) (g20 : ArmG20 HK senv p en),
    LK1Open HK senv p en

def Exp_step_goodKE : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en) {h : Hs}
    (hG : GoodKE HK senv p en h) (hE : GoodE h),
    GoodKE HK senv p en (fun c => (step senv c).run h)

def Exp_goodKE_readF_of_open : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en), ∀ n, GoodKE HK senv p en (readF senv n)

/-! ## 2. Mutants (each MEANING-CHANGING) -/

/-- the body WITHOUT its binder (wrong source context) -/
def Mut_machRunApp?_readSub_noBinder : Prop :=
  ∀ {senv : StructEnv} {r : Lean.Expr} {Δ : SrcCtx} {e dom αs is body : Lean.Expr}
    (hR : ReadSub senv r Δ e) (h : machRunApp? e = some (dom, αs, is, body)),
    ReadSub senv r Δ dom ∧ ReadSub senv r Δ body

/-- the recogniser FAILS instead of succeeding (a different arm) -/
def Mut_satKE_conv_bareReg_none : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {d : Nat} {f a : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.conv env d (.app f a) st)) (hst : ReadInv HK senv p st)
    {dom α init x : Lean.Expr}
    (h1 : regView? (Lean.Expr.app f a).getAppFn (Lean.Expr.app f a).getAppArgs = none),
    SatK HK senv p h (convStep senv env d (.app f a) st)

/-- no `ReadInv` of the input state (a stronger, unsupported claim) -/
def Mut_satKE_nested_noInv : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr} {h : Hs}
    (HKL : PhKindingLaws HK) (hG : GoodKE HK senv p en h) (hE : GoodE h)
    {env : List MachVal} {dom αs initsE body : Lean.Expr} {st : MachRead}
    (hpre : CallPreKE HK senv p en (Call.nested env dom αs initsE body st)),
    SatK HK senv p h (nestedStep senv env dom αs initsE body st)

/-- the open loop-root premise WITHOUT `ReadInv` of the input state -/
def Mut_ArmG20_noInv (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {e : Lean.Expr} {st : MachRead},
    CallPreKE HK senv p en (Call.loopRoot env e st) →
    SatK HK senv p h (loopRootStep senv env e st)

/-- the loop premise at a NON-loop value -/
def Mut_ArmG12conv_notLoop (HK : PhKinding) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  ∀ {h : Hs}, GoodKE HK senv p en h → GoodE h →
  ∀ {env : List MachVal} {d : Nat} {nm : Name} {ty v b : Lean.Expr} {nd : Bool} {st : MachRead},
    CallPreKE HK senv p en (Call.conv env d (.letE nm ty v b nd) st) → ReadInv HK senv p st →
    (∀ (n2 : Name) (t2 v2 w : Lean.Expr) (nd2 : Bool),
      Sparkle.Compiler.MachRawSurface.rootFloat v ≠ .letE n2 t2 v2 w nd2) →
    (Sparkle.Compiler.MachRawSurface.rootFloat v).isAppOfArity ``Sparkle.Core.Signal.Signal.loop 4 = false →
    SatK HK senv p h (convStep senv env d (.letE nm ty v b nd) st)

/-- the constructor WITHOUT the loop-root arm (G20 silently dropped from the open list) -/
def Mut_LK1Open_mk_noG20 : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    (g5 : ArmG5 HK senv p en) (g6 : ArmG6 HK senv p en) (g11 : ArmG11 HK senv p en)
    (g12conv : ArmG12conv HK senv p en) (g12chain : ArmG12chain HK senv p en)
    (g17user : ArmG17user HK senv p en) (g18 : ArmG18 HK senv p en),
    LK1Open HK senv p en

/-- rev2's `GoodK` (state-indexed `EnvKindOk`) in the conclusion instead of `GoodKE` -/
def Mut_goodKE_readF_of_open_rev2 : Prop :=
  ∀ {HK : PhKinding} {senv : StructEnv} {p : ShapePre} {en : Lean.Expr}
    (HKL : PhKindingLaws HK) (O : LK1Open HK senv p en), ∀ n, GoodK HK senv p en (readF senv n)

run_cmd liftTermElabM do
  for (t, e) in [(``Tools.ShippingGen3ArgSupply4.regView?_all, ``Exp_regView?_all),
      (``Tools.ShippingGen3ArgSupply4.machRunApp?_readSub, ``Exp_machRunApp?_readSub),
      (``Tools.ShippingGen3ArgSupply4.satKE_conv_bareReg, ``Exp_satKE_conv_bareReg),
      (``Tools.ShippingGen3ArgSupply4.satKE_conv_loopRead, ``Exp_satKE_conv_loopRead),
      (``Tools.ShippingGen3ArgSupply4.satKE_nested, ``Exp_satKE_nested),
      (``Tools.ShippingGen3ArgSupply4.ArmG11, ``Exp_ArmG11),
      (``Tools.ShippingGen3ArgSupply4.ArmG12conv, ``Exp_ArmG12conv),
      (``Tools.ShippingGen3ArgSupply4.ArmG20, ``Exp_ArmG20),
      (``Tools.ShippingGen3ArgSupply4.step_goodKE, ``Exp_step_goodKE),
      (``Tools.ShippingGen3ArgSupply4.goodKE_readF_of_open, ``Exp_goodKE_readF_of_open)] do
    checkExpected t e
  -- the structure constructor (not a theorem/definition): compared with `cmpTele` directly
  let mkTy := (← getConstInfo ``Tools.ShippingGen3ArgSupply4.LK1Open.mk).type
  cmpTele "LK1Open.mk" mkTy (← stmtOf ``Exp_LK1Open_mk)
  logInfo m!"GEN3 TYPE OK LK1Open.mk against Exp_LK1Open_mk (exactly the eight open arms)"
  for (t, m) in [(``Tools.ShippingGen3ArgSupply4.machRunApp?_readSub, ``Mut_machRunApp?_readSub_noBinder),
      (``Tools.ShippingGen3ArgSupply4.satKE_conv_bareReg, ``Mut_satKE_conv_bareReg_none),
      (``Tools.ShippingGen3ArgSupply4.satKE_nested, ``Mut_satKE_nested_noInv),
      (``Tools.ShippingGen3ArgSupply4.ArmG20, ``Mut_ArmG20_noInv),
      (``Tools.ShippingGen3ArgSupply4.ArmG12conv, ``Mut_ArmG12conv_notLoop),
      (``Tools.ShippingGen3ArgSupply4.goodKE_readF_of_open, ``Mut_goodKE_readF_of_open_rev2)] do
    checkMutant t m
  -- the constructor's mutant (field list without G20) must be rejected as well
  let accepted ← withoutModifyingState do
    try
      cmpTele "LK1Open.mk vs mutant" mkTy (← stmtOf ``Mut_LK1Open_mk_noG20)
      pure true
    catch _ => pure false
  if accepted then throwError "GEN3 MUTANT ACCEPTED: Mut_LK1Open_mk_noG20 matches LK1Open.mk"
  logInfo m!"GEN3 MUTANT REJECTED Mut_LK1Open_mk_noG20 (against LK1Open.mk)"
  -- the checker itself: an expected statement against its own mutant must fail too
  checkMutant ``Exp_ArmG20 ``Mut_ArmG20_noInv

run_cmd logInfo "GEN3 MUTANTS: all 8 rejections above are MEANING-CHANGING (no signature-only mutant in this file)."
run_cmd logInfo "GEN3 CONDITIONAL: goodKE_readF_of_open is a SKELETON — GoodKE (readF) FROM LK1Open (G5, G6, G11, G12 conv/chain, G17 user-let, G18, G20 as named premises); not L-RUN1, not L-FG supply, not FG completion; G21 / the run form are outside it."
run_cmd logInfo "GEN3 AUDIT: G3 (loopRead/readV) and G14 (atoms) close on the LK1 side only; their ConvKind (TY) supply needs NEW invariants/laws (tuple-aware loop-state kinds; runCircuitH slot kinds; SK->HK at atoms). G21: start state closed (readInv_empty / readInv_reserve); S1 ReadSub through machRoot and root-let pushes (as G11/G12) open."

/-! ## 3. Axioms -/

run_cmd liftTermElabM do
  for n in [``Tools.ShippingGen3ArgSupply4.regView?_all, ``Tools.ShippingGen3ArgSupply4.regView?_readSub,
      ``Tools.ShippingGen3ArgSupply4.machRunApp?_spine, ``Tools.ShippingGen3ArgSupply4.machRunApp?_readSub,
      ``Tools.ShippingGen3ArgSupply4.eq_zero_of_not_or4, ``Tools.ShippingGen3ArgSupply4.satK_domGuard,
      ``Tools.ShippingGen3ArgSupply4.satK_pure_ite, ``Tools.ShippingGen3ArgSupply4.satK_findSomeO,
      ``Tools.ShippingGen3ArgSupply4.readInv_reserve, ``Tools.ShippingGen3ArgSupply4.readInv_instStruct,
      ``Tools.ShippingGen3ArgSupply4.satKE_conv_bareReg, ``Tools.ShippingGen3ArgSupply4.satKE_conv_loopRead,
      ``Tools.ShippingGen3ArgSupply4.satKE_conv_readV, ``Tools.ShippingGen3ArgSupply4.satKE_conv_nestedCall,
      ``Tools.ShippingGen3ArgSupply4.satK_nestedProbe, ``Tools.ShippingGen3ArgSupply4.satKE_nested,
      ``Tools.ShippingGen3ArgSupply4.satKE_conv_instCall, ``Tools.ShippingGen3ArgSupply4.satKE_conv_instSCall,
      ``Tools.ShippingGen3ArgSupply4.satKE_conv_memCall, ``Tools.ShippingGen3ArgSupply4.satKE_conv_atom,
      ``Tools.ShippingGen3ArgSupply4.satKE_conv_fvar, ``Tools.ShippingGen3ArgSupply4.satKE_conv_mvar,
      ``Tools.ShippingGen3ArgSupply4.satKE_conv_sort, ``Tools.ShippingGen3ArgSupply4.satKE_conv_const,
      ``Tools.ShippingGen3ArgSupply4.satKE_conv_lit, ``Tools.ShippingGen3ArgSupply4.conv_app_satKE,
      ``Tools.ShippingGen3ArgSupply4.conv_letE_satKE, ``Tools.ShippingGen3ArgSupply4.conv_satKE,
      ``Tools.ShippingGen3ArgSupply4.chain_letE_satKE, ``Tools.ShippingGen3ArgSupply4.chain_satKE,
      ``Tools.ShippingGen3ArgSupply4.loopBody_satKE, ``Tools.ShippingGen3ArgSupply4.step_goodKE,
      ``Tools.ShippingGen3ArgSupply4.goodKE_readF_of_open] do
    checkAxioms n

end Tests.Gen3.ArgSupply4Check
