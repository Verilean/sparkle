import Tools.ShippingGateNamesWalk

variable {tenv : Lean.Environment}

/-! # Gate-route parents: the design walk extended by widths (worker N, round 14)

WRITTEN, NOT BUILT.

The seven `…_gate_designSVN2` still assume `hierTyped (childMap ms) b` and
`designSideB3 ms b` (`seqCheck`, the `seqNames` width agreement,
`portsMatchB` of the shipped module): WIDTH facts of the parent body. The
round-11/13 invariants (`DOk`, `NOk`) record statement shapes and names, not
widths. This file adds a THIRD invariant, `TOk G Ip τ s`, walked through the
same fuel walk, and independent of the other two:

* the module has no output yet, its inputs are the prepared ports `Ip`, and
  every input port is also a wire;
* the wires have distinct, reserved names (`WiresOk`) of scalar type;
* every assignment of the body is `l := op [a, b]` with both operands
  declared wires of one width `k` (`WidthIs`), and either a BINARY operator
  (`Binary.operator`) with `l` of width `k`, or a COMPARISON
  (`signalCompareOp`) with `l` of width `1` (`AsgT`);
* every instance names a module `x` with `G x`, its connections are
  `ins ++ [(o, ref w)]` with `x.outputs = [o : bitVector k]`, `w` a wire of
  width `k`, `o` not an input name, and every input connection a wire of
  EXACTLY the width of the callee's input port it is keyed by (`InstT`,
  `ConnT`);
* every recorded translation `w ↦ e` names a wire of width `τ e` (`recs`):
  `τ : Lean.Expr → Nat` is a typing of the cone's sub-expressions, fixed per
  declaration (a cache hit returns the wire of an earlier translation of the
  same expression, which must have the same width).

`TypW L mF D rec ctx G Ip τ e`: every returning run of `rec e …` from a
`TOk` state ends in a `TOk` state with more wires (`TGrows`) and returns a
wire of width `τ e`. Nodes: `typW_fvar` (an input binder whose port has width
`τ (.fvar id)`), `typW_binary` (operands and result of width `n`),
`typW_compare` (operands of width `n`, result `1`), `typW_inst` (arguments of
the widths of the callee's input ports, result of the width of its output
port; `instArgs_typW`). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

/-! ## Widths -/

section typedState
open Sparkle.IR.AST Sparkle.IR.Builder

/-- A scalar type of the positive width `k`. -/
def ScalT (ty : Sparkle.IR.Type.HWType) (k : Nat) : Prop :=
  0 < k ∧ ((ty = .bit ∧ k = 1) ∨ ty = .bitVector k)

theorem ScalT.bitWidth {ty : Sparkle.IR.Type.HWType} {k : Nat} (h : ScalT ty k) :
    ty.bitWidth = k := by
  rcases h with ⟨-, ⟨rfl, rfl⟩ | rfl⟩
  · first
      | rfl
      | simp [Sparkle.IR.Type.HWType.bitWidth]
  · first
      | rfl
      | simp [Sparkle.IR.Type.HWType.bitWidth]

theorem ScalT.scalar {ty : Sparkle.IR.Type.HWType} {k : Nat} (h : ScalT ty k) :
    ty = .bit ∨ ∃ n, ty = .bitVector n := by
  rcases h with ⟨-, ⟨rfl, -⟩ | rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k, rfl⟩

/-- `x` is a declared wire of the positive scalar width `k`. -/
def WidthIs (s : CircuitState) (x : String) (k : Nat) : Prop :=
  ∃ ty, ({ name := x, ty := ty } : Sparkle.IR.AST.Port) ∈ s.module.wires ∧ ScalT ty k

/-- The declared wires grow. -/
def TGrows (s t : CircuitState) : Prop :=
  ∀ p ∈ s.module.wires, p ∈ t.module.wires

theorem TGrows.refl (s : CircuitState) : TGrows s s := fun _ h => h

theorem TGrows.trans {s t u : CircuitState} (h1 : TGrows s t) (h2 : TGrows t u) : TGrows s u :=
  fun p hp => h2 p (h1 p hp)

theorem TGrows.of_wires {s t u : CircuitState} (h : TGrows s t)
    (hw : u.module.wires = t.module.wires) : TGrows s u := by
  intro p hp
  rw [hw]
  exact h p hp

theorem WidthIs.mono {s t : CircuitState} {x : String} {k : Nat} (hg : TGrows s t)
    (h : WidthIs s x k) : WidthIs t x k := by
  obtain ⟨ty, hm, hs⟩ := h
  exact ⟨ty, hg _ hm, hs⟩

theorem WidthIs.of_wires {s t : CircuitState} {x : String} {k : Nat} (h : WidthIs s x k)
    (hw : t.module.wires = s.module.wires) : WidthIs t x k := by
  obtain ⟨ty, hm, hs⟩ := h
  refine ⟨ty, ?_, hs⟩
  rw [hw]
  exact hm

theorem WidthIs.pos {s : CircuitState} {x : String} {k : Nat} (h : WidthIs s x k) : 0 < k := by
  obtain ⟨ty, -, hs⟩ := h
  exact hs.1

/-- **An assignment of the typed walk** (file header). -/
def AsgT (s : CircuitState) (l : String) (r : Sparkle.IR.AST.Expr) : Prop :=
  ∃ (o : Operator) (a b : String) (k : Nat),
    r = Sparkle.IR.AST.Expr.op o [.ref a, .ref b] ∧ WidthIs s a k ∧ WidthIs s b k ∧
    (((∃ bo : Tools.ShippingScalarSoundness.Binary, bo.operator = o) ∧ WidthIs s l k) ∨
     ((∃ le : Sparkle.Compiler.Elab.SignalCompareKind,
        Sparkle.Compiler.Elab.signalCompareOp le = o) ∧ WidthIs s l 1))

theorem AsgT.mono {s t : CircuitState} {l : String} {r : Sparkle.IR.AST.Expr} (hg : TGrows s t)
    (h : AsgT s l r) : AsgT t l r := by
  obtain ⟨o, a, b, k, hr, ha, hb, hl⟩ := h
  refine ⟨o, a, b, k, hr, ha.mono hg, hb.mono hg, ?_⟩
  rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2.mono hg⟩
  · exact Or.inr ⟨h1, h2.mono hg⟩

/-- An input connection: a wire of exactly the width of the port (with `P`)
it is keyed by. -/
def ConnT (P : Sparkle.IR.AST.Port → Prop) (s : CircuitState)
    (c : String × Sparkle.IR.AST.Expr) : Prop :=
  ∃ (a : String) (q : Sparkle.IR.AST.Port), P q ∧ c.2 = Sparkle.IR.AST.Expr.ref a ∧
    q.name = c.1 ∧ WidthIs s a q.ty.bitWidth

theorem ConnT.mono {P : Sparkle.IR.AST.Port → Prop} {s t : CircuitState}
    {c : String × Sparkle.IR.AST.Expr} (hg : TGrows s t) (h : ConnT P s c) : ConnT P t c := by
  obtain ⟨a, q, hq, h1, h2, h3⟩ := h
  exact ⟨a, q, hq, h1, h2, h3.mono hg⟩

/-- **An instance statement of the typed walk** (file header). -/
def InstT (G : Sparkle.IR.AST.Module → Prop) (s : CircuitState) (mn : String)
    (cs : List (String × Sparkle.IR.AST.Expr)) : Prop :=
  ∃ (x : Sparkle.IR.AST.Module) (ins : List (String × Sparkle.IR.AST.Expr)) (o : String) (k : Nat)
    (w : String),
    G x ∧ x.name = mn ∧ x.outputs = [⟨o, .bitVector k⟩] ∧
    cs = ins ++ [(o, Sparkle.IR.AST.Expr.ref w)] ∧ o ∉ x.inputs.map (·.name) ∧
    WidthIs s w k ∧ ∀ c ∈ ins, ConnT (· ∈ x.inputs) s c

theorem InstT.mono {G : Sparkle.IR.AST.Module → Prop} {s t : CircuitState} {mn : String}
    {cs : List (String × Sparkle.IR.AST.Expr)} (hg : TGrows s t) (h : InstT G s mn cs) :
    InstT G t mn cs := by
  obtain ⟨x, ins, o, k, w, hG, hn, ho, hcs, hoin, hw, hc⟩ := h
  exact ⟨x, ins, o, k, w, hG, hn, ho, hcs, hoin, hw.mono hg, fun c hcm => (hc c hcm).mono hg⟩

/-- **The typed invariant** (file header). -/
structure TOk (G : Sparkle.IR.AST.Module → Prop) (Ip : List Sparkle.IR.AST.Port)
    (τ : Lean.Expr → Nat) (s : CircuitState) : Prop where
  outs : s.module.outputs = []
  ins : s.module.inputs = Ip
  inw : ∀ p ∈ s.module.inputs, p ∈ s.module.wires
  wok : Tools.ShippingTranslateSoundness.WiresOk s
  wsc : ∀ p ∈ s.module.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n
  asg : ∀ l r, Stmt.assign l r ∈ s.module.body → AsgT s l r
  inst : ∀ mn i cs, Stmt.inst mn i cs ∈ s.module.body → InstT G s mn cs
  recs : ∀ w e, s.translateRecord.get? w = some e → WidthIs s w (τ e)

/-! ### The builder steps -/

theorem wiresOk_same {s t : CircuitState} (h : Tools.ShippingTranslateSoundness.WiresOk s)
    (hw : t.module.wires = s.module.wires)
    (hu : ∀ x, s.usedNames.contains x = true → t.usedNames.contains x = true) :
    Tools.ShippingTranslateSoundness.WiresOk t := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [hw]; exact h1, fun p hp => ?_⟩
  rw [hw] at hp
  exact hu _ (h2 p hp)

/-- **A step that keeps the body** keeps `TOk`. -/
theorem TOk.transfer {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s t : CircuitState} (h : TOk G Ip τ s)
    (hb : t.module.body = s.module.body) (hi : t.module.inputs = s.module.inputs)
    (ho : t.module.outputs = s.module.outputs) (hg : TGrows s t)
    (hwok : Tools.ShippingTranslateSoundness.WiresOk t)
    (hsc : ∀ p ∈ t.module.wires, p.ty = .bit ∨ ∃ n, p.ty = .bitVector n)
    (hr : ∀ w e, t.translateRecord.get? w = some e → s.translateRecord.get? w = some e) :
    TOk G Ip τ t where
  outs := by rw [ho]; exact h.outs
  ins := by rw [hi]; exact h.ins
  inw := by
    intro p hp
    rw [hi] at hp
    exact hg p (h.inw p hp)
  wok := hwok
  wsc := hsc
  asg := by
    intro l r hm
    rw [hb] at hm
    exact (h.asg l r hm).mono hg
  inst := by
    intro mn i cs hm
    rw [hb] at hm
    exact (h.inst mn i cs hm).mono hg
  recs := fun w e he => (h.recs w e (hr w e he)).mono hg

theorem tGrows_makeWire (s : CircuitState) (hint : String) (ty : Sparkle.IR.Type.HWType)
    (named : Bool) : TGrows s (CircuitM.makeWire hint ty named s).2 := by
  intro p hp
  rw [(CircuitM.makeWire_spec hint ty named s).2.2.2]
  exact List.mem_cons_of_mem _ hp

theorem widthIs_makeWire (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool)
    (s : CircuitState) {k : Nat} (hk : ScalT ty k) :
    WidthIs (CircuitM.makeWire hint ty named s).2 (CircuitM.makeWire hint ty named s).1 k := by
  refine ⟨ty, ?_, hk⟩
  rw [(CircuitM.makeWire_spec hint ty named s).2.2.2]
  exact List.mem_cons_self

theorem TOk.makeWire {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s : CircuitState} (h : TOk G Ip τ s) (hint : String)
    (ty : Sparkle.IR.Type.HWType) (named : Bool) (hty : ty = .bit ∨ ∃ n, ty = .bitVector n) :
    TOk G Ip τ (CircuitM.makeWire hint ty named s).2 := by
  have hspec := CircuitM.makeWire_spec hint ty named s
  have hm := makeWire_module hint ty named s
  refine h.transfer hspec.2.2.1 (by rw [hm]; try rfl) (by rw [hm]; try rfl)
    (tGrows_makeWire s hint ty named)
    (Tools.ShippingTranslateSoundness.WiresOk.fresh hspec.1 hspec.2.1 hspec.2.2.2 h.wok) ?_ ?_
  · intro p hp
    rw [hspec.2.2.2] at hp
    rcases List.mem_cons.mp hp with he | hp
    · rw [he]
      exact hty
    · exact h.wsc p hp
  · intro w e he
    rw [CircuitM.makeWire_translateRecord] at he
    exact he

theorem tGrows_freshName (s : CircuitState) (hint : String) (named : Bool) :
    TGrows s (CircuitM.freshName hint named s).2 := by
  intro p hp
  rw [(CircuitM.freshName_spec hint named s).2.2]
  exact hp

theorem TOk.freshName {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s : CircuitState} (h : TOk G Ip τ s) (hint : String) (named : Bool) :
    TOk G Ip τ (CircuitM.freshName hint named s).2 := by
  have hspec := CircuitM.freshName_spec hint named s
  refine h.transfer (by rw [hspec.2.2]) (by rw [hspec.2.2]) (by rw [hspec.2.2])
    (tGrows_freshName s hint named)
    (wiresOk_same h.wok (by rw [hspec.2.2]) (fun x hx => used_freshName hint named s hx)) ?_ ?_
  · intro p hp
    rw [hspec.2.2] at hp
    exact h.wsc p hp
  · intro w e he
    rw [CircuitM.freshName_translateRecord] at he
    exact he

theorem TOk.design {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s : CircuitState} (h : TOk G Ip τ s) (d' : Sparkle.IR.AST.Design) :
    TOk G Ip τ { s with design := d' } :=
  h.transfer rfl rfl rfl (fun _ hp => hp) h.wok h.wsc (fun _ _ he => he)

theorem TOk.record {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s : CircuitState} (h : TOk G Ip τ s) (w : String) (e : Lean.Expr)
    (hw : WidthIs s w (τ e)) :
    TOk G Ip τ { s with translateRecord := s.translateRecord.insert w e } := by
  have hg : TGrows s { s with translateRecord := s.translateRecord.insert w e } := fun _ hp => hp
  refine ⟨h.outs, h.ins, h.inw, h.wok, h.wsc, fun l r hm => (h.asg l r hm).mono hg,
    fun mn i cs hm => (h.inst mn i cs hm).mono hg, ?_⟩
  intro w' e' he
  have he' : (s.translateRecord.insert w e).get? w' = some e' := he
  rw [rec_get?_insertN] at he'
  by_cases hk : w = w'
  · rw [if_pos hk] at he'
    have hee : e = e' := Option.some.inj he'
    subst hee hk
    exact hw.mono hg
  · rw [if_neg hk] at he'
    exact (h.recs w' e' he').mono hg

/-- **A new statement** of the typed kinds. -/
theorem TOk.addStmt {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s : CircuitState} (h : TOk G Ip τ s) (st0 : Stmt)
    (ha : ∀ l r, st0 = Stmt.assign l r → AsgT s l r)
    (hi : ∀ mn i cs, st0 = Stmt.inst mn i cs → InstT G s mn cs) :
    TOk G Ip τ { s with module := s.module.addStmt st0 } := by
  have hb : ({ s with module := s.module.addStmt st0 } : CircuitState).module.body =
      st0 :: s.module.body := rfl
  have hg : TGrows s { s with module := s.module.addStmt st0 } := fun _ hp => hp
  refine ⟨h.outs, h.ins, h.inw, h.wok, h.wsc, ?_, ?_, ?_⟩
  · intro l r hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · exact (ha l r he.symm).mono hg
    · exact (h.asg l r hm).mono hg
  · intro mn i cs hm
    rw [hb] at hm
    rcases List.mem_cons.mp hm with he | hm
    · exact (hi mn i cs he.symm).mono hg
    · exact (h.inst mn i cs hm).mono hg
  · intro w e he
    exact (h.recs w e he).mono hg

theorem TOk.emitAssign {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {s : CircuitState} (h : TOk G Ip τ s) {l : String}
    {r : Sparkle.IR.AST.Expr} (ha : AsgT s l r) :
    TOk G Ip τ (CircuitM.emitAssign l r s).2 := by
  rw [emitAssign_eqN]
  refine h.addStmt _ (fun l' r' he => ?_) (fun mn i cs he => ?_)
  · cases he
    exact ha
  · cases he

end typedState

/-! ## The walk -/

section typWalk
open Lean Sparkle.Compiler.Elab Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec Grows
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness
open Tools.ShippingEntrySoundness
open Sparkle.IR.AST (Operator)
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingUnifiedRecursion
open Tools.ShippingHierarchySoundness
open Tools.ShippingInstanceEntrySoundness
open Tools.ShippingInstanceLeaf
open Tools.ShippingChildInv (RefLaws InvV J KeepsC Res childKeeps
  cacheLookupValidated_keepsC recordTranslation_keepsC makeWire_keepsC emitAssign_keepsC
  instArgs_keepsC instClkRst_keepsC)
open Tools.ShippingCacheCoherentRun (SubMap sub_trans sub_refl)

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-- **The typed contract** (file header). -/
def TypW (L : RefLaws mref cref) (mF : Std.HashMap Lean.Name Res) (D : Nat) (rec : TranslateFn)
    (ctx : CompilerState) (G : Sparkle.IR.AST.Module → Prop) (Ip : List Sparkle.IR.AST.Port)
    (τ : Lean.Expr → Nat) (e : Lean.Expr) : Prop :=
  ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String) (top named : Bool)
    (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
    TOk G Ip τ s → TOk G Ip τ t ∧ TGrows s t ∧ WidthIs t w (τ e)

/-- **An input binder** whose port has the width `τ (.fvar id)`. -/
theorem typW_fvar (L : RefLaws mref cref) {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop} {Ip : List Sparkle.IR.AST.Port}
    {τ : Lean.Expr → Nat} {id : FVarId} {z : String} {ty : Sparkle.IR.Type.HWType}
    (hz : ctx.varMap.lookup id = some z)
    (hzP : ({ name := z, ty := ty } : Sparkle.IR.AST.Port) ∈ Ip)
    (hsc : ScalT ty (τ (.fvar id))) :
    ∀ fuel, TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ (.fvar id)
  | 0 => by
    intro mctx cctx hint top named s t w w0 w1 _ _ _ hr _
    exact (Returns.throw (runsCReturns hr)).elim
  | fuel + 1 => by
    intro mctx cctx hint top named s t w w0 w1 _ _ _ hr hok
    change RunsC (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) (.fvar id) hint top named) ctx s
      mctx mref cctx cref w0 (w, t) w1 at hr
    have bound : visible ctx s.sourceBindings id = some z := by
      simp [visible, hz]
    obtain ⟨hwz, ht⟩ :=
      Tools.ShippingMixedInvariant.translateStep_fvar_returns (tenv := tenv) bound
        (runsCReturns hr)
    subst ht
    rw [hwz]
    exact ⟨hok, TGrows.refl _, ty, hok.inw _ (by rw [hok.ins]; exact hzP), hsc⟩

/-- **The core and the record of a typed binary node** (`binary_coreNam`'s run). -/
theorem binary_coreTyp (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {Ip : List Sparkle.IR.AST.Port} {τ : Lean.Expr → Nat}
    {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat}
    {hint : String} {top named cacheable : Bool}
    {s t : CircuitState} {w : String} {w0 w1 : Void IO.RealWorld}
    {K : Option String → CompilerM String}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ta : TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ
      e.getAppArgs[e.getAppArgs.size - 2]!)
    (tb : TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ
      e.getAppArgs[e.getAppArgs.size - 1]!)
    (hta : τ e.getAppArgs[e.getAppArgs.size - 2]! = n)
    (htb : τ e.getAppArgs[e.getAppArgs.size - 1]! = n)
    (hte : τ e = n) (hn : 0 < n)
    (hbo : ∃ bo : Tools.ShippingScalarSoundness.Binary, bo.operator = op)
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => Pure.pure z))
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D) (hsub : SubMap (L.val w1) mF)
    (hr : RunsC (translateCore (translateFuelFix (translateStep tenv) fuel) e hint top named >>= K)
      ctx s mctx mref cctx cref w0 (w, t) w1) (hok : TOk G Ip τ s) :
    TOk G Ip τ t ∧ TGrows s t ∧ WidthIs t w (τ e) := by
  obtain ⟨r, sm, wc, core, rest⟩ := RunsC.bind hr
  rw [core_binary_eq fn hop kinds width] at core
  obtain ⟨z, sm', wz, lower, back⟩ := RunsC.bind core
  obtain ⟨hp, hwz⟩ := RunsC.pure back
  obtain ⟨hrz, hsm⟩ := Prod.mk.inj hp
  subst hrz hsm hwz
  rw [hk] at rest
  obtain ⟨u, sr, wr, record, fin⟩ := RunsC.bind rest
  obtain ⟨hp2, hw1⟩ := RunsC.pure fin
  obtain ⟨hwz', ht'⟩ := Prod.mk.inj hp2
  subst hwz' ht' hw1
  obtain ⟨sa, sb, sc, a, b, wm, wa, wb, hwname, hsa, rmk, ra, rb, remit, ht⟩ :=
    binary_returnsW width lower
  -- the worlds: makeWire, operand a, operand b, the assign, the record
  obtain ⟨hwm, hdm, -⟩ :=
    keepsW L (fun L' => makeWire_keepsC L' D hint (.bitVector n) named) hw0 hd0 rmk
  obtain ⟨hwa, hda, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwm hdm ra
  obtain ⟨hwb, hdb, hsbc⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa hda rb
  obtain ⟨hwc, hdc, hscd⟩ :=
    keepsW L (fun L' => emitAssign_keepsC L' D w (.op op [.ref a, .ref b])) hwb hdb remit
  obtain ⟨-, -, hsd⟩ :=
    keepsW L (fun L' => recordTranslation_keepsC L' D e w cacheable) hwc hdc record
  have subB : SubMap (L.val wb) mF := sub_trans hscd (sub_trans hsd hsub)
  have subA : SubMap (L.val wa) mF := sub_trans hsbc subB
  -- the target wire, of width `n`
  have tA0 : TOk G Ip τ sa := by
    rw [hsa]
    exact hok.makeWire hint (.bitVector n) named (Or.inr ⟨n, rfl⟩)
  have gA0 : TGrows s sa := by
    rw [hsa]
    exact tGrows_makeWire s hint (.bitVector n) named
  have hwA : WidthIs sa w n := by
    rw [hsa, hwname]
    exact widthIs_makeWire hint (.bitVector n) named s ⟨hn, Or.inr rfl⟩
  obtain ⟨tB, gB, wA⟩ := ta mctx cctx "op_a" false false sa sb a wm wa hwm hdm subA ra tA0
  obtain ⟨tC, gC, wB⟩ := tb mctx cctx "op_b" false false sb sc b wa wb hwa hda subB rb tB
  rw [hta] at wA
  rw [htb] at wB
  obtain ⟨bo, hbo'⟩ := hbo
  have hasg : AsgT sc w (.op op [.ref a, .ref b]) :=
    ⟨op, a, b, n, rfl, wA.mono gC, wB, Or.inl ⟨⟨bo, hbo'⟩, (hwA.mono gB).mono gC⟩⟩
  have tM : TOk G Ip τ sm := by
    rw [ht]
    exact tC.emitAssign hasg
  have gM : TGrows sc sm := by
    rw [ht]
    exact TGrows.of_wires (TGrows.refl sc) (by rw [emitAssign_eqN]; try rfl)
  have hwM : WidthIs sm w (τ e) := by
    rw [hte]
    exact ((hwA.mono gB).mono gC).mono gM
  have hrecE := recordTranslation_returns (runsCReturns record)
  rw [hrecE]
  exact ⟨tM.record _ _ hwM, (((gA0.trans gB).trans gC).trans gM).of_wires rfl,
    hwM.of_wires rfl⟩

/-- **A typed canonical binary node** (either branch of the validated lookup). -/
theorem typW_binary (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {Ip : List Sparkle.IR.AST.Port} {τ : Lean.Expr → Nat}
    {e : Lean.Expr} {m : Lean.Name} {us : List Level} {op : Operator} {n : Nat}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (ta : TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ
      e.getAppArgs[e.getAppArgs.size - 2]!)
    (tb : TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ
      e.getAppArgs[e.getAppArgs.size - 1]!)
    (hta : τ e.getAppArgs[e.getAppArgs.size - 2]! = n)
    (htb : τ e.getAppArgs[e.getAppArgs.size - 1]! = n)
    (hte : τ e = n) (hn : 0 < n)
    (hbo : ∃ bo : Tools.ShippingScalarSoundness.Binary, bo.operator = op) :
    TypW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G Ip τ e := by
  have nf := isFVar_false_of_const fn
  intro mctx cctx hint top named s t w w0 w1 hw0 hd0 hsub hr hok
  change RunsC (translateStepWith (translateFallback tenv)
    (translateFuelFix (translateStep tenv) fuel) e hint top named) ctx s
    mctx mref cctx cref w0 (w, t) w1 at hr
  unfold translateStepWith at hr
  dsimp only at hr
  split at hr
  · obtain ⟨hit, sh, w2, rh, hr2⟩ := RunsC.bind hr
    have rhR := runsCReturns rh
    have hs := (cacheLookupValidated_returns rhR).1
    subst hs
    obtain ⟨hw2, hd2, -⟩ :=
      keepsW L (fun L' => cacheLookupValidated_keepsC L' D e) hw0 hd0 rh
    split at hr2
    · obtain ⟨hp, -⟩ := RunsC.pure hr2
      obtain ⟨hw', ht'⟩ := Prod.mk.inj hp
      subst hw' ht'
      exact ⟨hok, TGrows.refl _, hok.recs _ _ ((cacheLookupValidated_returns rhR).2 _ rfl)⟩
    · exact binary_coreTyp (cacheable := !named && !e.isFVar && !top) L hD fuel
        fn hop kinds width ta tb hta htb hte hn hbo
        (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hw2 hd2 hsub hr2 hok
  · exact binary_coreTyp (cacheable := !named && !e.isFVar && !top) L hD fuel
      fn hop kinds width ta tb hta htb hte hn hbo
      (fun z => by simp only [nf, Bool.false_eq_true, if_false]) hw0 hd0 hsub hr hok

/-- **A typed canonical comparison** (both branches of the validated wrapper). -/
theorem typW_compare (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {Ip : List Sparkle.IR.AST.Port} {τ : Lean.Expr → Nat}
    {dom ae be : Lean.Expr} {n : Nat} {le : SignalCompareKind}
    (ta : TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ ae)
    (tb : TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ be)
    (hta : τ ae = n) (htb : τ be = n) (hte : τ (compareE le dom n ae be) = 1) :
    TypW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G Ip τ
      (compareE le dom n ae be) := by
  intro mctx cctx hint top named s t w w0 w1 hw0 hd0 hsub hr hok
  change RunsC (translateStepWith (translateFallback tenv)
    (translateFuelFix (translateStep tenv) fuel) (compareE le dom n ae be) hint top named) ctx s
    mctx mref cctx cref w0 (w, t) w1 at hr
  rw [Tools.ShippingMixedRecursion.compare_step,
    translateFallback_bool (translateFuelFix (translateStep tenv) fuel)
      (compareE le dom n ae be) hint top named (by cases le <;> rfl)] at hr
  rcases controlCached_runsW L hw0 hd0 hr with hit | ⟨sm, wa, wb, hwa, hda, hl, hrec⟩
  · have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, TGrows.refl _, hok.recs _ _ (hlk.2 _ rfl)⟩
  · rw [translateBoolUncachedWith_compare] at hl
    unfold translateSignalCompare at hl
    obtain ⟨a, sa, wa1, ra, rest⟩ := RunsC.bind hl
    obtain ⟨b, sb, wb1, rb, re⟩ := RunsC.bind rest
    obtain ⟨hwa1, hda1, -⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa hda ra
    obtain ⟨hwb1, hdb1, hsab⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa1 hda1 rb
    have reE : RunsC (emitBoolResult (.op (signalCompareOp le) [.ref a, .ref b]) hint named)
        ctx sb mctx mref cctx cref wb1 (w, sm) wb := re
    unfold emitBoolResult at reE
    obtain ⟨r1, s1, wq, rm, rest2⟩ := RunsC.bind reE
    obtain ⟨u2, s2, wq2, rem, fin⟩ := RunsC.bind rest2
    obtain ⟨hp, hwq⟩ := RunsC.pure fin
    obtain ⟨hwr, hsm⟩ := Prod.mk.inj hp
    obtain ⟨hwm, hdm, hs1⟩ :=
      keepsW L (fun L' => makeWire_keepsC L' D hint .bit named) hwb1 hdb1 rm
    obtain ⟨hwq', hdq', hs2⟩ :=
      keepsW L (fun L' => emitAssign_keepsC L' D r1 (.op (signalCompareOp le) [.ref a, .ref b]))
        hwm hdm rem
    rw [← hwq] at hwq' hdq' hs2
    obtain ⟨-, -, hsr⟩ :=
      keepsW L (fun L' => recordTranslation_keepsC L' D (compareE le dom n ae be) w
        (!named && !(compareE le dom n ae be).isFVar && !top)) hwq' hdq' hrec
    have subB : SubMap (L.val wb1) mF := sub_trans hs1 (sub_trans hs2 (sub_trans hsr hsub))
    have subA : SubMap (L.val wa1) mF := sub_trans hsab subB
    obtain ⟨tA, gA, wA⟩ := ta mctx cctx "a" false false s sa a wa wa1 hwa hda subA ra hok
    obtain ⟨tB, gB, wB⟩ := tb mctx cctx "b" false false sa sb b wa1 wb1 hwa1 hda1 subB rb tA
    rw [hta] at wA
    rw [htb] at wB
    obtain ⟨hr1, hs1e⟩ := Tools.ShippingTranslateSoundness.makeWire_returns (runsCReturns rm)
    have hs2e := Tools.ShippingTranslateSoundness.emitAssign_returns (runsCReturns rem)
    have hrecE := recordTranslation_returns (runsCReturns hrec)
    have t1 : TOk G Ip τ s1 := by
      rw [hs1e]
      exact tB.makeWire hint .bit named (Or.inl rfl)
    have g1 : TGrows sb s1 := by
      rw [hs1e]
      exact tGrows_makeWire sb hint .bit named
    have hr1W : WidthIs s1 r1 1 := by
      rw [hs1e, hr1]
      exact widthIs_makeWire hint .bit named sb ⟨Nat.one_pos, Or.inl ⟨rfl, rfl⟩⟩
    have hasg : AsgT s1 r1 (.op (signalCompareOp le) [.ref a, .ref b]) :=
      ⟨signalCompareOp le, a, b, n, rfl, (wA.mono gB).mono g1, wB.mono g1,
        Or.inr ⟨⟨le, rfl⟩, hr1W⟩⟩
    have t2 : TOk G Ip τ s2 := by
      rw [hs2e]
      exact t1.emitAssign hasg
    have g2 : TGrows s1 s2 := by
      rw [hs2e]
      exact TGrows.of_wires (TGrows.refl s1) (by rw [emitAssign_eqN]; try rfl)
    have hW2 : WidthIs s2 w (τ (compareE le dom n ae be)) := by
      rw [hte, hwr]
      exact hr1W.mono g2
    rw [hrecE, hsm]
    exact ⟨t2.record _ _ hW2, ((((gA.trans gB).trans g1).trans g2)).of_wires rfl,
      hW2.of_wires rfl⟩

/-- The two components of a pair of a zip. -/
theorem mem_zip_partsT {α β : Type} :
    ∀ {l1 : List α} {l2 : List β} {pe : α × β}, pe ∈ l1.zip l2 → pe.1 ∈ l1 ∧ pe.2 ∈ l2
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l1, b :: l2, pe, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with he | h
    · rw [he]
      exact ⟨List.mem_cons_self, List.mem_cons_self⟩
    · obtain ⟨h1, h2⟩ := mem_zip_partsT h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

/-- **The typed operand walk**: every connection carries a wire of the width
of the port it is keyed by. -/
theorem instArgs_typW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {Ip : List Sparkle.IR.AST.Port} {τ : Lean.Expr → Nat} (P : Sparkle.IR.AST.Port → Prop) :
    ∀ (pairs : List (Sparkle.IR.AST.Port × Lean.Expr))
      (acc : List (String × Sparkle.IR.AST.Expr)) (i : Nat)
      (r : List (String × Sparkle.IR.AST.Expr)) (s t : CircuitState)
      (w0 w1 : Void IO.RealWorld),
    (∀ pe ∈ pairs, TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ pe.2) →
    (∀ pe ∈ pairs, P pe.1 ∧ τ pe.2 = pe.1.ty.bitWidth) →
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (instArgs (translateFuelFix (translateStep tenv) fuel) acc pairs i) ctx s
      mctx mref cctx cref w0 (r, t) w1 →
    SubMap (L.val w0) (L.val w1) ∧
      (TOk G Ip τ s → (∀ c ∈ acc, ConnT P s c) →
        TOk G Ip τ t ∧ TGrows s t ∧ ∀ c ∈ r, ConnT P t c)
  | [], acc, i, r, s, t, w0, w1, _, _, _, _, _, hr => by
    unfold instArgs at hr
    obtain ⟨hp, hw⟩ := RunsC.pure hr
    obtain ⟨hr', hs⟩ := Prod.mk.inj hp
    refine ⟨by rw [hw]; exact sub_refl _, fun hok hacc => ?_⟩
    rw [hs, hr']
    exact ⟨hok, TGrows.refl _, hacc⟩
  | (p, e) :: rest, acc, i, r, s, t, w0, w1, hc, hP, hw, hd, hsub, hr => by
    unfold instArgs at hr
    obtain ⟨aw, s1, wa, hread, hrest⟩ := RunsC.bind hr
    obtain ⟨hwa, hda, hsa⟩ := fuel_runsW (tenv := tenv) L hD fuel hw hd hread
    obtain ⟨subT, hT⟩ := instArgs_typW L hD fuel P rest _ (i + 1) r s1 t wa w1
      (fun pe hpe => hc pe (List.mem_cons_of_mem _ hpe))
      (fun pe hpe => hP pe (List.mem_cons_of_mem _ hpe)) hwa hda hsub hrest
    refine ⟨sub_trans hsa subT, fun hok hacc => ?_⟩
    obtain ⟨t1, g1, wE⟩ := hc (p, e) List.mem_cons_self mctx cctx _ false false s s1 aw w0 wa
      hw hd (sub_trans subT hsub) hread hok
    obtain ⟨hPp, hτ⟩ := hP (p, e) List.mem_cons_self
    have hτ' : τ e = p.ty.bitWidth := hτ
    have wE' : WidthIs s1 aw p.ty.bitWidth := by
      rw [← hτ']
      exact wE
    have hacc1 : ∀ c ∈ (p.name, Sparkle.IR.AST.Expr.ref aw) :: acc, ConnT P s1 c := by
      intro c hc'
      rcases List.mem_cons.mp hc' with he | hc'
      · rw [he]
        exact ⟨aw, p, hPp, rfl, rfl, wE'⟩
      · exact (hacc c hc').mono g1
    obtain ⟨tT, gT, hrefs⟩ := hT t1 hacc1
    exact ⟨tT, g1.trans gT, hrefs⟩

/-- **A typed instance call** of a designated callee whose `mF` entry
satisfies `InstLeafOk2 G`, whose input ports have the widths `τ` gives the
arguments, and whose output port has the width `τ` gives the call. -/
theorem typW_inst (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {Ip : List Sparkle.IR.AST.Port} {τ : Lean.Expr → Nat}
    {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom argsE) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hleaf : ∀ y : Res, mF.get? mn = some y → InstLeafOk2 G argsE.length y)
    (hws : ∀ y : Res, mF.get? mn = some y →
      (∀ pe ∈ y.1.inputs.zip argsE, τ pe.2 = pe.1.ty.bitWidth) ∧
      ∀ p ∈ y.1.outputs, p.ty.bitWidth = τ (instEN mn lvls dom argsE))
    (hargs : ∀ a ∈ argsE,
      TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ a) :
    TypW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G Ip τ
      (instEN mn lvls dom argsE) := by
  intro mctx cctx hint top named s t w w0 w1 hw hd hsub hr hok
  obtain ⟨y, wm, -, hget, hwm, hdm, hrA⟩ :=
    inst_leaf_runsW (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
  have hyF : mF.get? mn = some y := hsub mn y hget
  obtain ⟨⟨hG, hdc, hnoclk, hlen, o, k, houts, hk⟩, hoin⟩ := hleaf y hyF
  obtain ⟨hwsIn, hwsOut⟩ := hws y hyF
  have hkτ : k = τ (instEN mn lvls dom argsE) :=
    hwsOut ⟨o, .bitVector k⟩ (by rw [houts]; exact List.mem_singleton_self _)
  have hrecK : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) fuel e hint top named) :=
    fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD)) fuel
  have hr' : RunsC (translateControlCachedWith
      (translateInstanceUncachedWith (translateFuelFix (translateStep tenv) fuel) mn y.1 y.2
        ⟨o, .bitVector k⟩) (instEN mn lvls dom argsE) hint top named) ctx s
      mctx mref cctx cref wm (w, t) w1 := by
    unfold Tools.ShippingChildInv.armCont at hrA
    rw [houts] at hrA
    exact hrA
  rcases controlCached_runsW L hwm hdm hr' with hit | ⟨sm, wa, wb, hwa, hda, lowerRun, recordRun⟩
  · have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, TGrows.refl _, hok.recs _ _ (hlk.2 _ rfl)⟩
  · obtain ⟨d', conns, sA, wc, wd, hwc, hdc', hwb, hdb, subD, hArgs, hdes1, hdes2, hdes3,
      hcase⟩ := instUncached_namW L hrecK hdc hnoclk hlen hwa hda lowerRun
    obtain ⟨-, -, subR⟩ := keepsW L (fun L' => recordTranslation_keepsC L' D
      (instEN mn lvls dom argsE) w (!named && !(instEN mn lvls dom argsE).isFVar && !top))
      hwb hdb recordRun
    have tS : TOk G Ip τ { s with design := d' } := hok.design d'
    obtain ⟨-, hAr⟩ := instArgs_typW L hD fuel (· ∈ y.1.inputs) (y.1.inputs.zip argsE) [] 0 conns
      { s with design := d' } sA wc wd
      (fun pe hpe => hargs pe.2 (mem_zip_partsT hpe).2)
      (fun pe hpe => ⟨(mem_zip_partsT hpe).1, hwsIn pe hpe⟩)
      hwc hdc' (sub_trans subD (sub_trans subR hsub)) hArgs
    obtain ⟨tA, gA, hrefsA⟩ := hAr tS (fun c hc => by simp at hc)
    have gSA : TGrows s sA := gA
    have hrecE := recordTranslation_returns (runsCReturns recordRun)
    rw [hrecE]
    rcases hcase with ⟨hvalid, hsm⟩ | ⟨hwm', iname, hiname, hsm⟩
    · -- a hit of the instance dedupe cache: a recorded wire of the call's width
      have hW : WidthIs sA w (τ (instEN mn lvls dom argsE)) :=
        (hok.recs _ _ (instHitValid_recordD hvalid)).mono gSA
      rw [hsm]
      exact ⟨tA.record _ _ hW, gSA.of_wires rfl, hW.of_wires rfl⟩
    · -- a fresh wire of the output port's width, one typed instance statement
      have tW := tA.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
        (Or.inr ⟨k, rfl⟩)
      have gW := tGrows_makeWire sA hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
      have hwW : WidthIs (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty
          named sA).2 w k := by
        rw [hwm']
        exact widthIs_makeWire hint _ named sA ⟨hk, Or.inr rfl⟩
      have tN := tW.freshName s!"inst_{y.1.name}" false
      have gN := tGrows_freshName
        (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2
        s!"inst_{y.1.name}" false
      have hoin' : o ∉ y.1.inputs.map (·.name) :=
        hoin ⟨o, .bitVector k⟩ (by rw [houts]; exact List.mem_singleton_self _)
      have hinstT : InstT G (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2
          y.1.name (conns.reverse ++
            [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]) :=
        ⟨y.1, conns.reverse, o, k, w, hG, rfl, houts, rfl, hoin', hwW.mono gN,
          fun c hc => ((hrefsA c (List.mem_reverse.mp hc)).mono gW).mono gN⟩
      have tI := tN.addStmt (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]))
        (fun l r he => by cases he)
        (fun mn' i' cs' he => by
          cases he
          exact hinstT)
      have hWI : WidthIs ({ (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2 with
          module := (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.addStmt
            (.inst y.1.name iname (conns.reverse ++
              [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name,
                Sparkle.IR.AST.Expr.ref w)])) } : CircuitState)
          w (τ (instEN mn lvls dom argsE)) := by
        rw [← hkτ]
        exact (hwW.mono gN).of_wires rfl
      rw [hsm]
      exact ⟨tI.record _ _ hWI, ((gSA.trans gW).trans gN).of_wires rfl, hWI.of_wires rfl⟩

end typWalk

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.typW_fvar
#print axioms Tools.ShippingGateParentRun.typW_binary
#print axioms Tools.ShippingGateParentRun.typW_compare
#print axioms Tools.ShippingGateParentRun.typW_inst
