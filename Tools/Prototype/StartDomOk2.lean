import Tools.Prototype.StartDomOk

/-! # Unit SDOM4: `startDom_succ` under a DIFFERENT sufficient premise (`LetOk 0` preservation along `==`)

BUILT: sd1 exit 1 (missing `open`), sd2 exit 0 (final; Tests.Compiler.ExprEqvAtomTest and this file). No sorry/axiom/native_decide.

Implementation evidence for `Expr.eqv` (toolchain v4.32.1, `Lean/Expr.lean:809`): `@[extern "lean_expr_eqv"] opaque eqv`,
documented "alpha equivalent, binder annotations are ignored"; `instance : BEq Expr := ⟨Expr.eqv⟩`.  The C++ body
(`expr_eq_fn`, kernel) is NOT shipped in this toolchain (no `src/kernel`), so what is known about it is (a) the docstring,
(b) the EXECUTED check `Tests/Compiler/ExprEqvAtomTest.lean` (mdata-wrapped fvar/const vs the bare atom, binder-name/binder-info
alpha-variance, and `LetOk 0` invariance on the executed pairs).  Those are EVIDENCE, not a proof of the extern.

The old `ExprEqvAtom` (a == b with b an atom ⇒ a = b) is kept (still the statement it was). This file replaces it, for
`startDom_succ`, by ANOTHER sufficient premise `EqvLetOk0`: `a == b → LetOk 0 b = true → LetOk 0 a = true` for ALL Expr pairs.
The two premises are NOT shown to imply each other: `ExprEqvAtom` speaks only of pairs whose right side is an atom, `EqvLetOk0`
of all pairs, so `ExprEqvAtom → EqvLetOk0` is NOT proved (and the converse is not claimed). PROVED: `EqvLetOk0 → ChainLetOk`
(`chainLetOk_of_eqv`), and from `ExprEqvAtom` only the ATOM-ENDING case (`chainLetOk_of_atom`: chains whose end `d` is an
fvar/const), not the general `ChainLetOk`. The executed mdata/alpha checks are EVIDENCE about the extern, not a proof of
`EqvLetOk0` (integrator wording fix, par/int-r31, per review). -/
namespace Tools.Prototype.StartDomOk
open Lean Sparkle.Compiler.Elab Tools.ShippingReaderFuel Tools.ShippingReaderLenOk
open Tools.Prototype.ReaderExec Tools.Prototype.PreprocLetOk
open Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderFuelShapeProv

/-- **PREMISE (NOT proved; extern)**: `Expr.eqv` (`==`) preserves `LetOk 0` backward: if `a == b` and `b` has no `_machLet`
placeholder then neither does `a`. -/
def EqvLetOk0 : Prop := ∀ a b : Lean.Expr, (a == b) = true → LetOk 0 b = true → LetOk 0 a = true

/-- `LetOk 0` preservation along a whole `DChain` (backward). -/
def ChainLetOk : Prop := ∀ {D d : Lean.Expr}, DChain D d → LetOk 0 d = true → LetOk 0 D = true

theorem chainLetOk_of_eqv (hE : EqvLetOk0) : ChainLetOk := by
  intro D d hc
  induction hc with
  | refl => exact id
  | step _ hb ih => exact fun h => ih (hE _ _ hb h)

/-- From the old premise, `LetOk 0` transfer for ATOM-ENDING chains only (not the general `ChainLetOk`). -/
theorem chainLetOk_of_atom (hE : ExprEqvAtom) {D d : Lean.Expr} (hc : DChain D d)
    (hat : (∃ id, d = Lean.Expr.fvar id) ∨ (∃ n ls, d = Lean.Expr.const n ls)) (h : LetOk 0 d = true) :
    LetOk 0 D = true := by
  rw [dchain_eq hE hc hat]; exact h

/-- **SUCCESS-RESTRICTED `startDom`** under the premise `EqvLetOk0` (same statement as `startDom_succ`; `EqvLetOk0` is a
different sufficient premise from `ExprEqvAtom`, mutual implication NOT proved). -/
theorem startDom_succ_w (hE : EqvLetOk0) {senv : StructEnv} {n : Nat} {m : ShapeMid}
    {ai : Bool} {p : ShapePre} {st0 st1 st : MachRead} {env : List MachVal} {v : Lean.Expr} {sp : MachineShape}
    (h0 : (shapeStart senv m).run (wtab senv n) = some (some st0))
    (h1 : (foldO (shapeRootLet senv) (([] : List MachVal), st0) m.rootLets).run (wtab senv n) =
      some (some (env, st1)))
    (h2 : (shapeBody m env st1).run (wtab senv n) = some (some (st, v)))
    (h3 : shapePost ai p m st v = some sp) :
    ∀ dom αs initsE body dom' stc, m.run? = some (dom, αs, initsE, body) →
      machConvF n senv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead) =
        some (some (dom', stc)) → LetOk 0 dom' = true := by
  intro dom αs initsE body dom' stc hm hc
  rcases shapeStart_inv h0 with ⟨hm0, _⟩ | ⟨dom2, αs2, i2, b2, dom2', stc2, base, hm2, hc2, hres⟩
  · rw [hm0] at hm; cases hm
  · rw [hm2] at hm
    have e1 : dom2 = dom := (Prod.mk.inj (Option.some.inj hm)).1
    subst e1
    have e2 : dom2' = dom' := by
      rw [hc2] at hc
      exact (Prod.mk.inj (Option.some.inj (Option.some.inj hc))).1
    rw [← e2]
    obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    have k0 : DK dom2' st0 := ⟨dom2', by rw [hst]; rfl, DChain.refl⟩
    have k1 := rootLets_dk k0 h1
    have k2 := shapeBody_dk k1 h2
    obtain ⟨d, hdk, hch⟩ := k2
    obtain ⟨domE, dm, hd, hdm⟩ := shapePost_dom h3
    rw [hdk] at hd
    have hde : domE = d := by
      simp at hd
      first | exact hd.symm | exact hd
    subst hde
    exact chainLetOk_of_eqv hE hch ((machDom_accept hdm).2 0)

/-- **`machineShapeN_lets''''`**: as `machineShapeN_lets'''` but with the premise `EqvLetOk0` in place of `ExprEqvAtom`. -/
theorem machineShapeN_lets'''' {senv : StructEnv} (hroot : RootFloatRange) (hlift : LiftRange)
    (hinst1 : Inst1Range) (hsig : SigTyRange senv) (hz : ZeroLitAgrees) (hnorm : NormRange senv)
    (hE : EqvLetOk0)
    {sm : Bool} {ps : List (String × Nat)} {ci : Lean.ConstantInfo} {ai : Bool} {sp : MachineShape}
    (hpe : ∀ p : ShapePre, shapePre sm ps ci senv = some p → LetOk 0 p.e = true)
    (h : machineShapeN sm ps ci senv ai = some (some sp)) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧ execNorm senv p.e = some en ∧
      RdOk st ∧ NoLetAlias st.lets ∧ LetOk st.lets.size v = true ∧
      shapePost ai p (shapeMid senv p en) st v = some sp := by
  obtain ⟨n, p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3⟩ := machineShapeN_steps h
  have hex : execNorm senv p.e = some en := (execNorm_iff senv).mpr ⟨n, hen⟩
  obtain ⟨hrl, hrt, hrb⟩ := shapeMid_ok hroot hz senv p en (hnorm _ _ (hpe p hp) hex)
  have r0 : RdOk st0 := shapeStart_ok (n := n) (startDom_succ_w hE h0 h1 h2 h3) h0
  have r1 := rootLets_ok hroot hlift hinst1 hsig Tools.ShippingLetsReaderInv.bundleIotaRange hrl r0 h1
    (fun v hv => by cases hv)
  have r2 := shapeBody_ok hroot hlift hinst1 hsig Tools.ShippingLetsReaderInv.bundleIotaRange r1.1 r1.2 hrt hrb
    (shapeMid_wrap_ok senv p en hrt) h2
  exact ⟨p, en, st, v, hp, hex, r2.1, r2.1.1, r2.2.2, h3⟩

#print axioms machineShapeN_lets''''
run_meta (Tools.Prototype.ReaderExec.auditPropBinders ``machineShapeN_lets''''
  ["RootFloatRange", "LiftRange", "Inst1Range", "SigTyRange", "ZeroLitAgrees", "NormRange", "EqvLetOk0", "Eq", "Eq"])
#print axioms startDom_succ_w
#print axioms chainLetOk_of_atom

end Tools.Prototype.StartDomOk
