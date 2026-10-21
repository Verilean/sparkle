import Tools.Prototype.NormNodeModelLetOk
import Tools.Prototype.RawNodeRangeLetOk2
import Tools.Prototype.ReaderComposed

/-! # Unit NMI: ISOLATED wrapper whose normaliser uses the MODEL node rewriter, with no node-correspondence premise

BUILT (unit NMI): n1 exit 1 (my check named two constants in the wrong namespace), n2 exit 0 (this file); Tests/Compiler/NormStepModelAgreeTest.lean t1 exit 1 (missing import), t2 exit 0.
No sorry / axiom / native_decide; `#print axioms`: [propext, Classical.choice, Quot.sound] for each theorem printed below.

Scope. This is about the MODEL wrapper `machineShapeNM` only. The shipped reader is unchanged; switching the shipped reader to the
model is a SEPARATE review decision. `NodeCorr` (shipped `machNormNode` = model `machNormNodeM`) stays OPEN and is not used here.
* `normStepP node` / `execNormP node` / `machNormFP node`: copies of `normStep` / `execNorm` / `machNormF` with the node rewriter
  `machNormNode senv` turned into the parameter `node`; `normStepP_shipped` is `rfl` at `machNormNode`; `execNormP_shipped` (equality of
  the two `partial_fixpoint`s) is proved through the least-fixpoint characterisation. `execNormM := execNormP machNormNodeM`.
* PROVED (premises `RawNodeRange`, `Inst1Range` only — NO `NormNodeRange`/`NodeCorr`/`LiftScalar*`/`BoolMap*`): `normRangeM` (LetOk 0
  preserved by `execNormM`).
* `machineShapeNM` := `shapeW` against (`execNormM`, `execBlock`); `machineShapeNM_steps` (phases of a successful run at one fuel; the
  blocks do not call the normaliser, which is proved by `BlkCong`), and the composed corollary `machineShapeNM_typed_all_rawNode'`
  (analogue of `machineShapeN_typed_all_rawNode'`, no `NormNodeRange`). THROWING checks below: exact `auditPropBinders` list and a
  whole-conclusion `isDefEq` against the shipped corollary with the reader replaced (mutations rejected).
Replacement is not discharge; the remaining premises of the shipped corollary (other than `NormNodeRange`) are unchanged. -/

namespace Tools.Prototype.NormStepModel
open Lean Sparkle.Compiler.Elab Tools.ShippingLetsReaderInv Tools.Prototype.ReaderExec Tools.ShippingReaderFuel
  Tools.ShippingLetsAliasInv Tools.Prototype.PreprocLetOk Tools.Prototype.NormRangeLetOk
  Tools.Prototype.NormNodeModelLetOk Tools.Prototype.ReaderLfp Lean.Order
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingReaderLenOk Tools.ShippingCloInv
open Tools.Prototype.ReaderTyped Tools.Prototype.StartDomOk Tools.Prototype.ReaderClosed
open Tools.ShippingUnifiedSource Tools.ShippingMachineDenote Tools.ShippingMachineEntry
open Tools.ShippingMachineAuto Tools.ShippingMachineClosesData Tools.ShippingMixedSourceBridge
open Tools.Prototype.RawNodeRangeLetOk Tools.Prototype.ReaderComposed

/-! ## (a) the parametrised normaliser -/

/-- The text of `normStep` with `machNormNode senv` replaced by the parameter `node senv`. -/
def normStepP (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) : Lean.Expr → NM Lean.Expr
  | e@(.app f a) =>
    match ashrView? e.getAppFn e.getAppArgs with
    | some (dom, nE, x, y) =>
      match canonicalNatLitValue? nE with
      | some n =>
        if n == 0 then FM.pure e else
        FM.bind (FM.call x) fun x' => FM.bind (FM.call y) fun y' =>
        FM.pure (Sparkle.Compiler.MachSignOps.ashrE inlNatLit
          (fun m a b => machSigBin m ((machSigInst m).getD .anonymous) dom n a b)
          dom n x' y')
      | none => FM.pure e
    | none =>
    match Sparkle.Compiler.MachRawSurface.rawNode senv.prodMatch e with
    | some e' => FM.call e'
    | none =>
      FM.bind (FM.call f) fun f' => FM.bind (FM.call a) fun a' =>
      FM.pure (node senv (.app f' a'))
  | .lam n t b bi => FM.bind (FM.call b) fun b' => FM.pure (.lam n t b' bi)
  | .letE n t v b nd =>
    if t.isConstOf ``Nat then FM.call (b.instantiate1 v)
    else if (machBits? t).isSome && !v.hasLooseBVars then FM.call (b.instantiate1 v)
    else FM.bind (FM.call v) fun v' => FM.bind (FM.call b) fun b' => FM.pure (.letE n t v' b' nd)
  | e => FM.pure e

/-- Definitional evidence that the copy is the same text at the shipped node rewriter. -/
theorem normStepP_shipped (senv : StructEnv) (e : Lean.Expr) :
    normStepP machNormNode senv e = normStep senv e := by
  cases e <;> rfl

def machNormFP (node : StructEnv → Lean.Expr → Lean.Expr) (n : Nat) (senv : StructEnv) (e : Lean.Expr) : Option Lean.Expr :=
  @fuel Lean.Expr (fun _ => Lean.Expr) (normStepP node senv) n e

set_option maxHeartbeats 1000000 in
theorem compact_normStepP (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) (e : Lean.Expr) :
    Compact (normStepP node senv e) := by
  unfold normStepP
  repeat' compact_base

/-- Kernel-visible normaliser with the node rewriter as a parameter: `partial_fixpoint` of `normStepP node senv`. -/
def execNormP (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) (e : Lean.Expr) : Option Lean.Expr :=
  (normStepP node senv e).run (execNormP node senv)
partial_fixpoint monotonicity by
  intro h₁ h₂ hle c
  exact Fn_mono (κ := Lean.Expr) (R := fun _ => Lean.Expr) (normStepP node senv) h₁ h₂ hle c

theorem execNormP_eq_lfp (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) :
    execNormP node senv = lfp (κ := Lean.Expr) (R := fun _ => Lean.Expr) (normStepP node senv) := by
  unfold Tools.Prototype.ReaderLfp.lfp
  with_unfolding_all rfl

theorem execNormP_iff (node : StructEnv → Lean.Expr → Lean.Expr) (senv : StructEnv) {e r : Lean.Expr} :
    execNormP node senv e = some r ↔ ∃ n, machNormFP node n senv e = some r := by
  rw [execNormP_eq_lfp]
  exact lfp_iff_fuel (κ := Lean.Expr) (R := fun _ => Lean.Expr) (compact_normStepP node senv)

/-- The two `partial_fixpoint`s agree at the shipped node rewriter (both are the least fixpoint of the same body). -/
theorem execNormP_shipped (senv : StructEnv) : execNormP machNormNode senv = execNorm senv := by
  rw [execNormP_eq_lfp, execNorm_eq_lfp]
  have : normStepP machNormNode senv = normStep senv := funext (normStepP_shipped senv)
  rw [this]

/-- The MODEL normaliser: the node rewriter is `machNormNodeM` (LC19's isolated lift/boolMap path). -/
def execNormM (senv : StructEnv) : Lean.Expr → Option Lean.Expr := execNormP machNormNodeM senv

/-! ## (b) `LetOk 0` preservation of `execNormM`, no node premise -/

theorem normStepP_ok (node : StructEnv → Lean.Expr → Lean.Expr) {senv : StructEnv} (hraw : RawNodeRange senv)
    (hnode : ∀ e, LetOk 0 e = true → LetOk 0 (node senv e) = true)
    (hinst : Inst1Range) {tab : (c : Lean.Expr) → Option Lean.Expr} (ht : TabOk tab) :
    ∀ (e r : Lean.Expr), LetOk 0 e = true → (normStepP node senv e).run tab = some r → LetOk 0 r = true := by
  intro e r he hr
  cases e with
  | app f a =>
    simp only [normStepP] at hr
    split at hr
    · rename_i dom nE x y hav
      obtain ⟨hd, hx, hy⟩ := ashrView_ok (ok_getAppArgs he) hav
      split at hr
      · rename_i n hn
        split at hr
        · exact (Option.some.inj hr) ▸ he
        · simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
          obtain ⟨x', hx', y', hy', rfl⟩ := hr
          exact ashrE_ok _ _ (fun k => letOk_natLit 0 k)
            (fun m a b ha hb => machSigBin_ok hd _ _ _ ha hb) hd (ht _ _ hx hx') (ht _ _ hy hy') n
      · exact (Option.some.inj hr) ▸ he
    · split at hr
      · rename_i e' hraw'
        exact ht _ _ (hraw _ _ he hraw') hr
      · simp only [LetOk, Bool.and_eq_true] at he
        simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
        obtain ⟨f', hf', a', ha', rfl⟩ := hr
        exact hnode _ (by simp only [LetOk, Bool.and_eq_true]; exact ⟨ht _ _ he.1 hf', ht _ _ he.2 ha'⟩)
  | lam nm t b bi =>
    simp only [normStepP] at hr
    simp only [LetOk, Bool.and_eq_true] at he
    simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
    obtain ⟨b', hb', rfl⟩ := hr
    simp only [LetOk, Bool.and_eq_true]
    exact ⟨he.1, ht _ _ he.2 hb'⟩
  | letE nm t v b nd =>
    simp only [normStepP] at hr
    simp only [LetOk, Bool.and_eq_true] at he
    split at hr
    · exact ht _ _ (hinst 0 b v he.2 he.1.2) hr
    · split at hr
      · exact ht _ _ (hinst 0 b v he.2 he.1.2) hr
      · simp only [FM.bind, FM.call, FM.pure, Option.bind_eq_some_iff, Option.some.injEq] at hr
        obtain ⟨v', hv', b', hb', rfl⟩ := hr
        simp only [LetOk, Bool.and_eq_true]
        exact ⟨⟨he.1.1, ht _ _ he.1.2 hv'⟩, ht _ _ he.2 hb'⟩
  | bvar _ => exact (Option.some.inj hr) ▸ he
  | fvar _ => exact (Option.some.inj hr) ▸ he
  | mvar _ => exact (Option.some.inj hr) ▸ he
  | sort _ => exact (Option.some.inj hr) ▸ he
  | const _ _ => exact (Option.some.inj hr) ▸ he
  | lit _ => exact (Option.some.inj hr) ▸ he
  | forallE _ _ _ _ => exact (Option.some.inj hr) ▸ he
  | mdata _ _ => exact (Option.some.inj hr) ▸ he
  | proj _ _ _ => exact (Option.some.inj hr) ▸ he

theorem tabOk_fuelP (node : StructEnv → Lean.Expr → Lean.Expr) {senv : StructEnv} (hraw : RawNodeRange senv)
    (hnode : ∀ e, LetOk 0 e = true → LetOk 0 (node senv e) = true) (hinst : Inst1Range) :
    ∀ n, TabOk (machNormFP node n senv)
  | 0 => fun e r _ h => by
    have : machNormFP node 0 senv e = none := rfl
    rw [this] at h; cases h
  | n + 1 => fun e r he h =>
    normStepP_ok node hraw hnode hinst (tabOk_fuelP node hraw hnode hinst n) e r he h

theorem normRangeP (node : StructEnv → Lean.Expr → Lean.Expr) {senv : StructEnv} (hraw : RawNodeRange senv)
    (hnode : ∀ e, LetOk 0 e = true → LetOk 0 (node senv e) = true) (hinst : Inst1Range) :
    ∀ e en, LetOk 0 e = true → execNormP node senv e = some en → LetOk 0 en = true := by
  intro e en he h
  obtain ⟨n, hn⟩ := (execNormP_iff node senv).mp h
  exact tabOk_fuelP node hraw hnode hinst n e en he hn

/-- **PROVED**: `execNormM` keeps `LetOk 0`. Premises: `RawNodeRange` and `Inst1Range` (the existing ones) only;
NO `NormNodeRange`, `NodeCorr`, `LiftScalar*`, `BoolMap*`. About the MODEL normaliser. -/
theorem normRangeM {senv : StructEnv} (hraw : RawNodeRange senv) (hinst : Inst1Range) :
    ∀ e en, LetOk 0 e = true → execNormM senv e = some en → LetOk 0 en = true :=
  normRangeP machNormNodeM hraw (fun _ he => machNormNodeM_ok senv he) hinst

/-! ## (c) the wrapper against `execNormM` -/

def xtabEM (senv : StructEnv) : (c : WCall) → Option (WCall.Res c)
  | .norm e => execNormM senv e
  | .blk c => execBlock senv c

/-- PROTOTYPE reader with the MODEL normaliser (`shapeW` against `execNormM` + `execBlock`). Not the shipped reader. -/
def machineShapeNM (symbolicMode : Bool) (parameters : List (String × Nat)) (ci : Lean.ConstantInfo)
    (senv : StructEnv) (allowInsts : Bool := true) : Option (Option MachineShape) :=
  (shapeW symbolicMode parameters ci senv allowInsts).run (xtabEM senv)

/-- The part of `shapeW` after its single normaliser call. -/
def shapeRest (senv : StructEnv) (ai : Bool) (p : ShapePre) (en : Lean.Expr) : WM (Option MachineShape) :=
  let m := shapeMid senv p en
  bindO (shapeStart senv m) fun st =>
  bindO (foldO (shapeRootLet senv) (([] : List MachVal), st) m.rootLets) fun (env, st) =>
  bindO (shapeBody m env st) fun (st, v) =>
  FM.pure (shapePost ai p m st v)

theorem shapeW_eq (sm : Bool) (ps : List (String × Nat)) (ci : Lean.ConstantInfo) (senv : StructEnv) (ai : Bool) :
    shapeW sm ps ci senv ai =
      optK (shapePre sm ps ci senv) fun p => FM.bind (wNorm p.e) (shapeRest senv ai p) := rfl

/-- A computation that reads only block calls of its table. -/
structure BlkCong {α : Type} (c : WM α) : Prop where
  eq : ∀ T1 T2 : (k : WCall) → Option (WCall.Res k), (∀ k, T1 (.blk k) = T2 (.blk k)) → c.run T1 = c.run T2

theorem bc_pure {α : Type} (a : α) : BlkCong (FM.pure (κ := WCall) (R := WCall.Res) a) := ⟨fun _ _ _ => rfl⟩
theorem bc_okO {α : Type} (a : α) : BlkCong (okO (κ := WCall) (R := WCall.Res) a) := bc_pure _
theorem bc_failO {α : Type} : BlkCong (failO (κ := WCall) (R := WCall.Res) (α := α)) := bc_pure _
theorem bc_blk (k : Call) : BlkCong (FM.call (R := WCall.Res) (WCall.blk k)) := ⟨fun _ _ h => h k⟩
theorem bc_wConv {env : List MachVal} {d : Nat} {e : Lean.Expr} {st : MachRead} : BlkCong (wConv env d e st) :=
  bc_blk _
theorem bc_wChain {env : List MachVal} {e : Lean.Expr} {st : MachRead} : BlkCong (wChain env e st) := bc_blk _
theorem bc_wLoopRoot {env : List MachVal} {e : Lean.Expr} {st : MachRead} : BlkCong (wLoopRoot env e st) :=
  bc_blk _

theorem bc_bind {α β : Type} {x : WM α} {f : α → WM β} (hx : BlkCong x) (hf : ∀ a, BlkCong (f a)) :
    BlkCong (FM.bind x f) := by
  constructor
  intro T1 T2 h
  show (x.run T1).bind (fun a => (f a).run T1) = (x.run T2).bind (fun a => (f a).run T2)
  rw [hx.eq T1 T2 h]
  cases x.run T2 with
  | none => rfl
  | some a => exact (hf a).eq T1 T2 h

theorem bc_optK {α β : Type} (o : Option α) {f : α → WM (Option β)} (hf : ∀ a, BlkCong (f a)) :
    BlkCong (optK o f) := by
  cases o with
  | none => exact bc_pure _
  | some a => exact hf a

theorem bc_bindO {α β : Type} {x : WM (Option α)} {f : α → WM (Option β)} (hx : BlkCong x)
    (hf : ∀ a, BlkCong (f a)) : BlkCong (bindO x f) :=
  bc_bind hx fun o => bc_optK o hf

theorem bc_foldO {σ α : Type} {f : σ → α → WM (Option σ)} (hf : ∀ s a, BlkCong (f s a)) :
    ∀ (s : σ) (l : List α), BlkCong (foldO f s l)
  | s, [] => bc_okO s
  | s, a :: as => bc_bindO (hf s a) fun s' => bc_foldO hf s' as

macro "bc_base" : tactic => `(tactic| first
  | with_reducible exact bc_wConv
  | with_reducible exact bc_wChain
  | with_reducible exact bc_wLoopRoot
  | with_reducible exact bc_okO _
  | with_reducible exact bc_failO
  | with_reducible exact bc_pure _
  | with_reducible apply bc_bindO
  | with_reducible apply bc_bind
  | with_reducible apply bc_optK
  | intro _
  | split
  | dsimp only)

theorem bc_shapeStart (senv : StructEnv) (m : ShapeMid) : BlkCong (shapeStart senv m) := by
  unfold shapeStart
  repeat' bc_base

theorem bc_shapeRootLet (senv : StructEnv) (s : List MachVal × MachRead) (a : Name × Lean.Expr × Lean.Expr) :
    BlkCong (shapeRootLet senv s a) := by
  unfold shapeRootLet
  repeat' bc_base

theorem bc_shapeBody (m : ShapeMid) (env : List MachVal) (st : MachRead) : BlkCong (shapeBody m env st) := by
  unfold shapeBody
  repeat' bc_base

theorem bc_shapeRest (senv : StructEnv) (ai : Bool) (p : ShapePre) (en : Lean.Expr) :
    BlkCong (shapeRest senv ai p en) := by
  unfold shapeRest
  refine bc_bindO (bc_shapeStart senv _) (fun st => ?_)
  refine bc_bindO (bc_foldO (bc_shapeRootLet senv) _ _) (fun es => ?_)
  rcases es with ⟨env, st'⟩
  refine bc_bindO (bc_shapeBody _ _ _) (fun sv => ?_)
  rcases sv with ⟨st'', v⟩
  exact bc_pure _

theorem compact_shapeRest (senv : StructEnv) (ai : Bool) (p : ShapePre) (en : Lean.Expr) :
    Compact (shapeRest senv ai p en) := by
  unfold shapeRest
  refine compact_bindO (compact_shapeStart senv _) (fun st => ?_)
  refine compact_bindO (compact_foldO (compact_shapeRootLet senv) _ _) (fun es => ?_)
  rcases es with ⟨env, st'⟩
  refine compact_bindO (compact_shapeBody _ _ _) (fun sv => ?_)
  rcases sv with ⟨st'', v⟩
  exact compact_pure _

/-- The rest of a successful model run holds at ONE fuel of the shipped block table. -/
theorem shapeRest_fuel {senv : StructEnv} {ai : Bool} {p : ShapePre} {en : Lean.Expr} {r : Option MachineShape}
    (h : (shapeRest senv ai p en).run (xtabEM senv) = some r) :
    ∃ n, (shapeRest senv ai p en).run (wtab senv n) = some r := by
  have h1 : (shapeRest senv ai p en).run (xtabE senv) = some r := by
    rw [← h]; exact (bc_shapeRest senv ai p en).eq _ _ (fun k => rfl)
  obtain ⟨L, e, k⟩ := (compact_shapeRest senv ai p en).ok (xtabE senv) r h1
  obtain ⟨N, hN⟩ := ext_wtab_of_reach (senv := senv) L (by
    intro q hq
    obtain ⟨c, y⟩ := q
    have hx : xtabE senv c = some y := e _ hq
    cases c with
    | norm e' => exact (execNorm_iff senv).mp hx
    | blk c' => exact (execBlock_iff senv).mp hx)
  exact ⟨N, k (wtab senv N) hN⟩

/-- The phases of a successful MODEL run, with every intermediate state at ONE common fuel (the analogue of `machineShapeN_steps`;
the normaliser answer is the MODEL's). -/
theorem machineShapeNM_steps {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {senv : StructEnv}
    {ai : Bool} {sp : MachineShape} (h : machineShapeNM sm ps ci senv ai = some (some sp)) :
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal)
      (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      execNormM senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0)
          (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  have h' : (shapeW sm ps ci senv ai).run (xtabEM senv) = some (some sp) := h
  rw [shapeW_eq] at h'
  obtain ⟨p, hp, h'⟩ := optK_some_inv h'
  obtain ⟨en, hen, h2⟩ := bind_some_inv h'
  obtain ⟨n, hn⟩ := shapeRest_fuel h2
  unfold shapeRest at hn
  try dsimp only at hn
  obtain ⟨st0, h0, hn⟩ := bindO_some_inv hn
  try dsimp only at hn
  obtain ⟨⟨env, st1⟩, h1, hn⟩ := bindO_some_inv hn
  try dsimp only at hn
  obtain ⟨⟨st, v⟩, h3, hn⟩ := bindO_some_inv hn
  try dsimp only at hn
  exact ⟨n, p, en, st0, env, st1, st, v, hp, hen, h0, h1, h3, pure_run_inv hn⟩

/-- **The composed corollary for the MODEL reader** (analogue of `machineShapeN_typed_all_rawNode'`): the same binders without
`NormNodeRange`, the same conclusion with `execNorm` replaced by `execNormM`. About `machineShapeNM` only. -/
theorem machineShapeNM_typed_all_rawNode' {senv : StructEnv}
    (hroot : RootFloatRange) (hinst1 : Inst1Range) (hsig : SigTyRange senv)
    (hz : ZeroLitAgrees) (hll : LiftLooseRange) (hlo : LowerLooseRange) (hbeta : BetaRange)
    (hE : EqvLetOk0)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeNM sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNormM senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      (∀ (d : MachineData), d.shape = sp → d.ok = true →
        d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j))
          (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed →
        d.letsAliasOk = true ∧
        ∀ {declName : Name} (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
          (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State),
          Tools.ShippingClosesSplit.LetsClose mctx mref cctx cref declName d.shape) := by
  have hlift : LiftRange := liftRange_of_loose hll
  have hraw : RawNodeRange senv := rawNodeRange_of hll hlo hbeta
  obtain ⟨n, p, en, st0, env, st1, st, v, hp, hex, h0, h1, h2, h3⟩ := machineShapeNM_steps h
  obtain ⟨hrl, hrt, hrb⟩ := shapeMid_ok hroot hz senv p en (normRangeM hraw hinst1 _ _ (hpe p hp) hex)
  have hbundle := Tools.ShippingLetsReaderInv.bundleIotaRange
  have r0 : RdOk st0 := shapeStart_ok (n := n) (startDom_succ_w hE h0 h1 h2 h3) h0
  have r1 := rootLets_ok hroot hlift hinst1 hsig hbundle hrl r0 h1 (fun v hv => by cases hv)
  have r2 := shapeBody_ok hroot hlift hinst1 hsig hbundle r1.1 r1.2 hrt hrb
    (shapeMid_wrap_ok senv p en hrt) h2
  have c0 : CloSt st0 := shapeStart_clo h0
  have c1 := rootLets_clo c0 (fun v hv => by cases hv) h1
  have c2 : CloSt st := shapeBody_clo c1.1 c1.2 h2
  have hnb : NoLetBvar st.lets := letsClo_noLetBvar c2.1
  have hna : NoLetAlias st.lets := r2.1.1
  refine ⟨p, en, st, v, hp, hex, r2.1, hna, r2.2.2, h3, ?_⟩
  intro d hs hok hbody
  have halias := typed_letsAlias (shapePre_outs_ne hp) h3 hna hnb d hs hok hbody
  exact ⟨halias, fun mctx mref cctx cref => letsClose_of_data d hok hbody halias mctx mref cctx cref⟩

#print axioms normRangeM
#print axioms machineShapeNM_steps
#print axioms machineShapeNM_typed_all_rawNode'
#print axioms execNormP_shipped

run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeNM_typed_all_rawNode'
  ["RootFloatRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "LiftLooseRange", "LowerLooseRange",
    "BetaRange", "EqvLetOk0", "Eq", "Eq"])

/- THROWING: no `NormNodeRange`/`NodeCorr`/`LiftScalar*`/`BoolMap*` constant occurs DIRECTLY in the new theorem's type
(`Expr.getUsedConstants` of the type; NOT a recursive closure audit: definitions named in the type are not unfolded); the new conclusion is `isDefEq` to the shipped corollary's conclusion with the reader replaced (`machineShapeN` ↦
`machineShapeNM` in the hypothesis, `execNorm` ↦ `execNormM` in the conclusion), shared binders as the same fvars (the old
`hnode : NormNodeRange senv` binder is a fresh mvar). Mutations (not replacing `execNorm`; replacing the reader only) are rejected. -/
open Meta in
def checkNM (mutate : Nat) : MetaM Unit := do
  let newI ← getConstInfo ``machineShapeNM_typed_all_rawNode'
  let oldI ← getConstInfo ``machineShapeN_typed_all_rawNode'
  for c in [``NormNodeRange, ``NodeCorr, ``Tools.Prototype.NormNodeRangeLetOk.LiftScalarRange,
      ``Tools.Prototype.NormNodeRangeLetOk.BoolMapRange, ``Tools.Prototype.LiftScalarModelLetOk.LiftScalarCorr,
      ``Tools.Prototype.BoolMapModelLetOk.BoolMapCorr] do
    if newI.type.getUsedConstants.contains c then throwError "{c} occurs in the new type"
  let rep (e : Expr) : Expr :=
    e.replace fun x =>
      if mutate != 3 && x.isConstOf ``machineShapeN then some (.const ``machineShapeNM [])
      else if mutate != 1 && x.isConstOf ``execNorm then some (.const ``execNormM [])
      else if mutate == 2 && x.isConstOf ``Tools.Prototype.RawNodeRangeLetOk.LiftLooseRange then some (.const ``True [])
      else none
  forallTelescope newI.type fun xs nb => do
    let mut oty := oldI.type
    let mut i := 0
    let mut skipped := false
    for _ in [0:xs.size + 2] do
      match oty with
      | .forallE n d b bi =>
        if n == `hnode then
          if skipped then throwError "two hnode binders"
          skipped := true
          oty := b.instantiate1 (← mkFreshExprMVar d)
        else
          unless i < xs.size do throwError "old type has more binders than new"
          unless (← xs[i]!.fvarId!.getUserName) == n do throwError "binder name mismatch at {i}: {n}"
          -- the hypothesis `h` mentions the reader: compare with the replaced type
          unless (← isDefEq (rep d) (← xs[i]!.fvarId!.getType)) do throwError "binder type mismatch at {n}"
          oty := b.instantiate1 xs[i]!
          i := i + 1
      | _ => break
    unless skipped && i == xs.size do throwError "binder bookkeeping failed ({skipped}, {i}, {xs.size})"
    unless (← isDefEq (rep oty) nb) do throwError "conclusions are not defeq"
    logInfo m!"NMI check (mutate={mutate}): conclusion defeq, {xs.size} shared binders, node-premise constants absent"

run_meta checkNM 0
run_meta (do
  for m in [1, 2, 3] do
    let ok ← (do checkNM m; pure true : MetaM Bool) <|> pure false
    if ok then throwError "mutation {m} was NOT rejected"
  logInfo m!"NMI check: mutations 1,2,3 rejected")

end Tools.Prototype.NormStepModel
