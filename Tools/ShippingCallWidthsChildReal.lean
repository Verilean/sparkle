import Tools.ShippingCallWidthsEntry
import Tools.ShippingPortsMatchRawLeaf
import Tools.ShippingReflectCtx
import Tools.ShippingChildRun
import Tools.ShippingGateChildComb
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- WRITTEN, NOT BUILT against patched compiler.

/-! # Call widths against the child REALLY compiled (reviewer milestone 2)

BUILT: run `cr1` (poc after 3a1938a3) exit 0 as written (worker S-DISP, branch
par/s-disp, from poc 3a1938a3). MEASURED axioms (run `ax18`, poc after 3a1938a3): `callWidthsStrict_real`,
`children_widths_real`, `parent_children_widths_real`, `resC_entry`:
[propext, Classical.choice, Quot.sound].
No `sorry`, no new axiom, no `native_decide`. New file; nothing existing is
changed. Audit: `docs/parallel/S-child-dispatch-audit.md`.

## What this replaces

`Tools.ShippingCallWidthsEntryFH.ChildLinkF` takes, per call entry `k`, SOME
definition `dC` with a candidate link to SOME shape `sc` and
`hkid : kidOuts k = sc.layout.outs`. Nothing ties `dC` to the constant the
compiler compiles for the callee of entry `k`, so `hkid = rfl` only says
that `kidOuts` was chosen to match a model. Likewise `…FR1._declared`
discharges `ResC` for the callee's DECLARED constant, while the machine
route compiles the UNFOLDED one (`entryConst`, `Sparkle/Compiler/Elab.lean`
5253–5264: `inlinedConst (userInliner env) ci`, which rewrites the TYPE as
well as the value, 3408–3410).

Here `kidOuts k` is the output layout of the shape `MachineDefines`
pins for the callee `(d.shape.insts[k]).1`: the machine shape of
`entryConst … ci …` where `ci` is what `getConstInfo` returns in the
callee's own entry run (`synthesizeCombinationalCoreWith`'s `doSynth`,
5545–5552). And:

* `childLink_real`: from ANY `RealChild` of the callee (a result of its real
  full entry, `synthesizeCombinational`, from an invariant world — what
  `synthesizeChild` returns on a hit or a miss, `synthesizeChild_inv`), the
  link `machineShape? false [] (.defnInfo dE) senv = some sc` at the ENTRY
  constant `dE` of THAT run, and `machResultKind? dE.type = some res`;
* `resC_entry`: `ResC` at the entry constant, by the two branches of
  `entryConst` (`Tools.ShippingEntrySoundness.entryConst_cases`, built): the declared constant (`ResDecl`) or
  the unfolding (`inlinedConst_defn`: its type is `userInliner env` of the
  declared type; there the premise is P5);
* `callWidthsStrict_real`: the data condition `callWidthsStrict` at the
  closing's `nDecl` for `kidOuts := fun k => (sc k).layout.outs`, from the
  children list the closing consumes (`ChildrenReal`, non-memory callees);
* `children_widths_real` (leaf callees, `LeafKid` of
  `Tools/ShippingPortsMatchRawLeaf.lean`): every output port of the module
  the closing ACTUALLY receives for entry `k` (`children[k]`), that the
  closing connects (the field's port, or every port on the one-output
  closing), has the width of the entry's binder; and those ports ARE
  `kidOuts k` (`ChildOutTys`);
* `parent_children_widths_real`: the same from ONE successful parent core
  run (`machine_children_realA`): the `children` of its `CloseCalls`.

## SCOPE

The REAL reader `machineShape?` (no candidate, so no O1/O2 is involved):
`MachineDefines` is the existing reflection boundary of each callee.
Non-memory callees (`memChild? = none`: a memory child is BUILT, not
compiled, `closeInstsGM` 5214–5217). Output widths only (not argument
widths, not semantics). `children_widths_real` / `parent_…` are for LEAF
register-machine callees (`LeafKid`: no calls, a slot) — the scope of
`leaf_real_outTys`; `callWidthsStrict_real` is for any machine-route callee
with a one-Signal result kind.

## Remaining premises

| premise | status |
|---|---|
| `entry` (`MachineDefines` of each callee, at the callee's entry constant) | ASSUMED — the existing reflection boundary (generated per declaration) |
| `ResD` (`ResDeclAt`: the DECLARED type of what `getConstInfo` returns has result kind `res k`) | ASSUMED — same style as `EnvDefines`; `resC_of_declared` gives the same fact from `env.find?` + the signature table, but no lemma relates `getConstInfo`'s read to `env.find?` |
| `P5` (`P5At`: when `entryConst` UNFOLDS, `machResultKind? (userInliner envR dD.type) = some res`) | EXPLICIT, NOT DISCHARGED — `inlinedConst` rewrites the type (`type := inl d.type`), so `(inlinedConst inl ci).type = ci.type` is NOT `rfl`; `userInliner` goes through `opaque` `Expr.replace` / `partial` helpers. Only needed on the unfolding branch (`entryConst … ci … ≠ ci`) |
| `PB` (parent binder at `closingNDecl + k` has type `machHWType (res k)`) | ASSUMED — decidable on the reflected parent |
| `hnomem` (no memory callee) | ASSUMED — decidable, on the entries' ORIGINS (`∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true`; origin dispatch, par/o-close) |
| `ChildrenReal` | DISCHARGED in `parent_children_widths_real` (from the parent run, `machine_children_realA`) |
| `hkid` | GONE — `kidOuts` is DEFINED as the real callee shape's layout |
| cache | DISCHARGED — `sparkleChildCache` is covered by the existing invariant (`CacheInv`: every entry a `RealChild`), inside `ChildrenReal` |
-/
namespace Tools.ShippingCallWidthsChildReal
open Lean Meta
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Machine
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingChildInv
open Tools.ShippingCallWidthsStrict Tools.ShippingCallWidthsDeclared Tools.ShippingCallWidthsEntry
open Tools.ShippingPortsMatchRawLeaf (LeafKid)

/-! ## `entryConst` and `inlinedConst`: which constant is compiled -/

/-- **The unfolding's type is the inliner applied to the declared type** — NOT
the declared type: `inlinedConst` rewrites `type` (Elab.lean 3408–3410). -/
theorem inlinedConst_defn {inl : Lean.Expr → Lean.Expr} {ci : ConstantInfo} {dE : DefinitionVal}
    (h : inlinedConst inl ci = .defnInfo dE) :
    ∃ dD : DefinitionVal, ci = .defnInfo dD ∧ dE.type = inl dD.type := by
  cases ci with
  | defnInfo dD =>
    have h' : ConstantInfo.defnInfo { dD with value := inl dD.value, type := inl dD.type } =
        ConstantInfo.defnInfo dE := h
    injection h' with h''
    subst h''
    exact ⟨dD, rfl, rfl⟩
  | _ =>
    first
      | (cases h)
      | (simp only [inlinedConst] at h)
      | (unfold inlinedConst at h; cases h)

/-- **`ResC` at the entry constant**: the declared constant's kind on the
branch where `entryConst` keeps it, P5 on the branch where it unfolds. -/
theorem resC_entry {ci : ConstantInfo} {isInst : Lean.Expr → Bool}
    {inl : Lean.Expr → Lean.Expr} {projs : StructEnv} {dE : DefinitionVal}
    {res : MixedGateBinder}
    (hE : entryConst true false [] ci isInst inl projs = .defnInfo dE)
    (ResDecl : ∀ dD : DefinitionVal, ci = .defnInfo dD → machResultKind? dD.type = some res)
    (P5 : ∀ dD : DefinitionVal, ci = .defnInfo dD →
      entryConst true false [] ci isInst inl projs ≠ ci →
      machResultKind? (inl dD.type) = some res) :
    machResultKind? dE.type = some res := by
  by_cases hne : entryConst true false [] ci isInst inl projs = ci
  · rw [hne] at hE
    exact ResDecl dE hE
  · rcases Tools.ShippingEntrySoundness.entryConst_cases ci isInst inl projs with h | h
    · exact absurd h hne
    · rw [h] at hE
      obtain ⟨dD, hci, hty⟩ := inlinedConst_defn hE
      rw [hty]
      exact P5 dD hci hne

/-! ## The per-callee premises, over the callee's own entry runs -/

section Defs
variable (mref : ST.Ref IO.RealWorld Meta.State) (cref : ST.Ref IO.RealWorld Core.State)

/-- **The declared callee's result kind**, for every read the entry makes of
`c` (in any contexts; same form as `EnvDefines`). -/
def ResDeclAt (c : Name) (res : MixedGateBinder) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
    (w2 : Void IO.RealWorld) (dD : DefinitionVal),
    RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 → ci = .defnInfo dD →
    machResultKind? dD.type = some res

/-- **P5 at callee `c`**: WHEN the entry compiles the unfolding of `c`
(`entryConst … ci … ≠ ci`), the run's inliner keeps the result kind of the
declared type. Explicit: `userInliner` on a type is not provable here
(`opaque` `Expr` operations, `partial` helpers). -/
def P5At (c : Name) (res : MixedGateBinder) : Prop :=
  ∀ (mctx : Meta.Context) (cctx : Core.Context) (w1 : Void IO.RealWorld) (ci : ConstantInfo)
    (w2 w5 : Void IO.RealWorld) (envR : Environment) (w6 : Void IO.RealWorld)
    (dD : DefinitionVal),
    RunsTo (getConstInfo c) mctx mref cctx cref w1 ci w2 →
    RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w5 envR w6 →
    ci = .defnInfo dD →
    entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ≠ ci →
    machResultKind? (userInliner envR dD.type) = some res

end Defs

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

/-! ## The link at the constant the callee's run compiled -/

/-- **The callee's real link.** From a `RealChild` of `c` (a result of its
real full entry): the shape `MachineDefines` pins is the REAL reader's result
on the ENTRY constant `dE` that run computed (declared or unfolded), and that
constant's type has the result kind `res`. -/
theorem childLink_real {c : Name} {sc : MachineShape} {res : MixedGateBinder} {y : Res}
    (entry : MachineDefines mctx mref cctx cref c sc)
    (ResD : ResDeclAt mref cref c res) (P5 : P5At mref cref c res)
    (hy : RealChild mref cref c y) :
    ∃ (dE : DefinitionVal) (senv : StructEnv),
      machineShape? false [] (.defnInfo dE) senv = some sc ∧
      machResultKind? dE.type = some res := by
  obtain ⟨M', D'⟩ := y
  obtain ⟨mctx', cctx', w, w', hw, hr⟩ := hy.inv
  obtain ⟨M, D, w1, hcore, -, -⟩ := Tools.ShippingGateChildComb.synthesizeCombinational_parts hr
  obtain ⟨L, hv⟩ := invV_of_invW mctx' cctx' hw
  obtain ⟨_, envR, ci, w1', w2', _, _, w5', w6', get, henv, _, _, _⟩ :=
    core_reads_inv L (startV_of_invV L hv) hv.2.2 hcore
  have entry' : MachineDefines mctx' mref cctx' cref c sc :=
    Tools.ShippingReflectCtx.MachineDefines.ctx entry
  obtain ⟨dE, hE, hshape⟩ := link_of_defines entry' get henv henv
  exact ⟨dE, _, hshape,
    resC_entry hE (fun dD hci => ResD mctx' cctx' w1' ci w2' dD get hci)
      (fun dD hci hne => P5 mctx' cctx' w1' ci w2' w5' envR w6' dD get henv hci hne)⟩

/-- One conjunct of `callWidthsStrict`, for `kidOuts k` the layout of the
callee's REAL shape. -/
theorem entryStrict_real {d : MachineData} {kidOuts : Nat → List OutField} {k : Nat}
    {c : Name} {sc : MachineShape} {res : MixedGateBinder} {y : Res}
    (hkid : kidOuts k = sc.layout.outs)
    (entry : MachineDefines mctx mref cctx cref c sc)
    (ResD : ResDeclAt mref cref c res) (P5 : P5At mref cref c res)
    (hy : RealChild mref cref c y)
    (PB : (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
      some (machHWType res)) :
    entryStrict d (closingNDecl d.shape) kidOuts k = true := by
  obtain ⟨dE, senv, hL, hR⟩ := childLink_real entry ResD P5 hy
  exact entryStrict_of_child hL hR hkid PB

/-- A non-memory entry of `ChildrenReal` is a `RealChild` of its callee —
origin dispatch (patched compiler): "non-memory" is the entry's ORIGIN
(`Tools.ShippingChildInv.realChild_of_childrenRealT`). -/
theorem realChild_of_childrenReal {shape : MachineShape} {children : List Res}
    (hreal : ChildrenReal mref cref shape children)
    {k : Nat} (hk : k < shape.insts.length)
    (hnomem : (shape.instOrigins.getD k .ord).child? = none)
    {y : Res} (hy : children[k]? = some y) :
    RealChild mref cref (shape.insts[k]).1 y :=
  Tools.ShippingChildInv.realChild_of_childrenRealT hreal hk hnomem hy

/-! ## The whole condition, `kidOuts` = the callees' real shapes -/

/-- **`callWidthsStrict` with `kidOuts` the REAL callee shapes**: from the
children the closing consumes. -/
theorem callWidthsStrict_real {d : MachineData} {children : List Res}
    (hreal : ChildrenReal mref cref d.shape children)
    (sc : Nat → MachineShape) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (entry : ∀ k (hk : k < d.shape.insts.length),
      MachineDefines mctx mref cctx cref (d.shape.insts[k]).1 (sc k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (sc k).layout.outs) = true := by
  apply callWidthsStrict_of_entries
  intro k hk
  obtain ⟨y, hy, _⟩ := hreal.2 k hk
  exact entryStrict_real rfl (entry k hk) (ResD k hk) (P5 k hk)
    (realChild_of_childrenReal hreal hk (Tools.ShippingChildInv.notag_at hnomem hk) hy) (PB k hk)

/-- **The emitted children's connected output ports, leaf callees.** For the
module the closing RECEIVES for entry `k` (`children[k]`): its output ports
are `kidOuts k` (the callee's real layout), and every one the closing
connects has the width of the entry's binder at the closing's `nDecl`. -/
theorem children_widths_real {d : MachineData} {children : List Res}
    (hreal : ChildrenReal mref cref d.shape children)
    (kid : Nat → MachineData) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ k (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) = true ∧
    ∀ k (hk : k < d.shape.insts.length) (y : Res), children[k]? = some y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kid k).shape.layout.outs y.1 ∧
      ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
        (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
          some p.ty.bitWidth := by
  have hcw : callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) =
      true :=
    callWidthsStrict_real hreal (fun k => (kid k).shape) res hnomem
      (fun k hk => (hkid k hk).entry) ResD P5 PB
  have hkidT : ∀ (k : Nat) (hk : k < d.shape.insts.length) (y : Res),
      RealChild mref cref (d.shape.insts[k]).1 y →
      Tools.ShippingChildIfaceTy.ChildOutTys (kid k).shape.layout.outs y.1 := by
    intro k hk y hy
    have K := hkid k hk
    exact Tools.ShippingChildIfaceTy.leaf_real_outTys (kid k) K.ok K.body K.leaf K.slots K.ss
      K.outTy K.entry K.closes hy
  refine ⟨hcw, fun k hk y hy => ?_⟩
  have hyR := realChild_of_childrenReal hreal hk (Tools.ShippingChildInv.notag_at hnomem hk) hy
  exact ⟨hkidT k hk y hyR, hkidW_strict hcw hkidT k hk y hyR⟩

/-- **From one successful parent run**: the children of the parent's closing
(`CloseCalls`, the list `closeInsts` / `closeInstsG` consumed) satisfy
`children_widths_real`. -/
theorem parent_children_widths_real {declName : Name} {d : MachineData}
    {w w' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {D : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, D) w')
    (entryP : MachineDefines mctx mref cctx cref declName d.shape)
    (closesP : MachineClosesAt mctx mref cctx cref declName d.shape)
    (hb : ChildBnd mref cref w) (hi : d.shape.insts ≠ [])
    (kid : Nat → MachineData) (res : Nat → MixedGateBinder)
    (hnomem : ∀ o ∈ d.shape.instTagged, o.2.child?.isNone = true)
    (hkid : ∀ k (hk : k < d.shape.insts.length),
      LeafKid mctx mref cctx cref (d.shape.insts[k]).1 (kid k))
    (ResD : ∀ k (hk : k < d.shape.insts.length), ResDeclAt mref cref (d.shape.insts[k]).1 (res k))
    (P5 : ∀ k (hk : k < d.shape.insts.length), P5At mref cref (d.shape.insts[k]).1 (res k))
    (PB : ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => kindTy bn.2) =
        some (machHWType (res k))) :
    callWidthsStrict d (closingNDecl d.shape) (fun k => (kid k).shape.layout.outs) = true ∧
    ∃ t t' d₀ children,
      Sparkle.IR.Machine.closeLets d.shape.layout.lets t = some t' ∧
      CloseCalls d.shape t (Sparkle.IR.Machine.closeMachine d.shape.layout t') d₀ children m D ∧
      ∀ k (hk : k < d.shape.insts.length) (y : Res), children[k]? = some y →
        Tools.ShippingChildIfaceTy.ChildOutTys (kid k).shape.layout.outs y.1 ∧
        ∀ p ∈ y.1.outputs, (∀ f, d.shape.instFields[k]? = some f → p.name = f) →
          (d.shape.binders[closingNDecl d.shape + k]?).map (fun bn => (kindTy bn.2).bitWidth) =
            some p.ty.bitWidth := by
  obtain ⟨t, t', d₀, children, hcl, hcc, hreal⟩ := machine_children_realA hr entryP closesP hb hi
  obtain ⟨hcw, hports⟩ := children_widths_real hreal kid res hnomem hkid ResD P5 PB
  exact ⟨hcw, t, t', d₀, children, hcl, hcc, hports⟩

end Tools.ShippingCallWidthsChildReal
