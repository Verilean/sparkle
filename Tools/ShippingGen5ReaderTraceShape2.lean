import Tools.ShippingGen5ReaderTraceDomKeepS
set_option autoImplicit false
-- NOT BUILT yet. Written against freeze rev20 §2 + rev21.1 §4 `scripts/gen5/DG_READERTRACE_FREEZE_REV21.md` (`MidInputs'`, `ShapeInputs'`, `shapeStart_trace'`, `machineShapeF_reach'`).

/-! # DG-READERTRACE rev20/rev21.1 primed wrapper reach: no `DomAtomic dom`

`MidInputs'` is `MidInputs` (`Tools/ShippingGen5ReaderTraceShape.lean`) without the `DomAtomic dom` conjunct of the run clause. `shapeStart_trace'` takes `hform : ∀ d, st0.dom = some d → DomForm d` instead:
a `DomForm` domain (a `_machIn i` free variable or `defaultDomain`) is in range of every state as soon as it is in range of one (`domForm_inRange`) and has no `_machLet`
(`domForm_letOk`), so the discarded conversion state need not be `{}`. `machineShapeF_reach'` obtains `hform` from `readF_domKeepF`-style relations (`hK`/`EqvAtom`) through
`rootLets_domKeepF`, `shapeBody_domKeepF`, `shapePost_domForm`. The existing `MidInputs` / `ShapeInputs` / `shapeStart_trace` / `machineShapeF_reach` are unchanged.
`EqvAtom` is a hypothesis of `machineShapeF_reach'` (not claimed true). Conditional (intermediate) result. -/

namespace Tools.ShippingGen5ReaderTrace
open Lean Sparkle.Compiler.Elab Tools.ShippingGen5Cover2 Tools.ShippingGen5Cover3 Tools.ShippingGen5Cover5 Tools.ShippingGen5Cover6
  Tools.ShippingReaderFuel Tools.ShippingReaderFuelShapeR5 Tools.ShippingLetsReaderInv Tools.ShippingLetsAliasInv Tools.ShippingReaderLenOk
  Tools.Assume.ExprEqv

def MidInputs' (nDecl : Nat) (senv : StructEnv) (p : ShapePre) (en : Lean.Expr) : Prop :=
  p.bs.length ≤ nDecl ∧
  (∀ (k : Nat) (x : Name × Lean.Expr × Lean.Expr), (shapeMid senv p en).rootLets[k]? = some x →
      NoPh x.2.2 = true ∧ BvarLt (k + nDecl) x.2.2 = true) ∧
  (∀ (dom αs ie b : Lean.Expr), (shapeMid senv p en).run? = some (dom, αs, ie, b) →
      NoPh dom = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + nDecl) dom = true ∧
      NoPh b = true ∧ BvarLt ((shapeMid senv p en).rootLets.length + 1 + nDecl) b = true) ∧
  ((shapeMid senv p en).run? = none →
      NoPh (shapeMid senv p en).root = true ∧
      BvarLt ((shapeMid senv p en).rootLets.length + nDecl) (shapeMid senv p en).root = true)

def ShapeInputs' (nDecl : Nat) (senv : StructEnv) (sm : Bool) (ps : List (String × Nat)) (ci : ConstantInfo)
    (n : Nat) : Prop :=
  ∀ (p : ShapePre) (en : Lean.Expr), shapePre sm ps ci senv = some p → machNormF n senv p.e = some en →
    MidInputs' nDecl senv p en

/-- a `DomForm` domain is in range of any state once it is in range of one: it mentions only `_machIn`. -/
theorem domForm_inRange {nDecl : Nat} {st st0 : MachRead} {k k0 : Nat} {d : Lean.Expr} (hf : DomForm d)
    (h : InRange nDecl st k d) : InRange nDecl st0 k0 d := by
  rcases domForm_shape d hf with ⟨i, rfl⟩ | ⟨ls, rfl⟩
  · refine ⟨h.1, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
    · simp [MentionsPh] at hj
  · refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩ <;>
    · simp [MentionsPh] at hj

/-- a `DomForm` domain has no `_machLet` placeholder. -/
theorem domForm_letOk (n : Nat) {d : Lean.Expr} (hf : DomForm d) : LetOk n d = true := by
  rcases domForm_shape d hf with ⟨i, rfl⟩ | ⟨ls, rfl⟩
  · simp [LetOk, letFv]
  · rfl

theorem shapeStart_trace' (senv : StructEnv) (nDecl n : Nat) (hT : TraceGood senv nDecl (readF senv n))
    (m : ShapeMid)
    (hdom : ∀ dom αs ie b, m.run? = some (dom, αs, ie, b) →
        NoPh dom = true ∧ BvarLt (m.rootLets.length + nDecl) dom = true)
    {st0 : MachRead} (hr : (shapeStart senv m).run (wtab senv n) = some (some st0))
    (hform : ∀ d : Lean.Expr, st0.dom = some d → DomForm d) :
    FReachC nDecl ({} : MachRead) st0 ∧ ShapeCarry senv nDecl [] st0 := by
  rcases shapeStart_inv hr with ⟨_, e⟩ | ⟨dom, αs, initsE, body, dom', stc, base, hm, hc, hres⟩
  · subst e
    exact ⟨FReachC.refl _, shapeCarry_empty senv nDecl⟩
  · obtain ⟨hn, hb⟩ := hdom dom αs initsE body hm
    have hUnits : EnvPh nDecl ({} : MachRead) (m.rootLets.map fun _ => MachVal.unit) :=
      ⟨fun v hv => by simp at hv, fun b n hbn => by simp at hbn⟩
    have hb' : BvarLt (0 + (m.rootLets.map fun _ => MachVal.unit).length + nDecl) dom = true := by
      rw [List.length_map, Nat.zero_add]; exact hb
    have hpre : TracePre senv nDecl (Call.conv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead)) :=
      ⟨⟨rdOk_init, fun v hv => by simp at hv, noPh_letOk 0 dom hn⟩, ⟨trInv_empty, hUnits, hn, hb'⟩⟩
    have hc' : readF senv n (Call.conv (m.rootLets.map fun _ => MachVal.unit) 0 dom ({} : MachRead)) =
        some (some (dom', stc)) := hc
    obtain ⟨hP, _, hX⟩ := hT _ hpre (dom', stc) hc'
    obtain ⟨kinds, inits, _, _, _, hst⟩ := machReserve_some hres
    subst hst
    -- the converted domain is `DomForm` (the reserved state's `dom`), hence in range of the EMPTY state
    have hdf : DomForm dom' := hform dom' rfl
    have hdr : InRange nDecl ({} : MachRead) ({} : MachRead).lets.size dom' := domForm_inRange hdf hX.2.1
    obtain ⟨hR, hTr⟩ := trInv_reserved (trInv_empty (senv := senv) (nDecl := nDecl)) hdr hX.2.2 body kinds inits
    refine ⟨hR, ?_, ?_, hTr, ?_⟩
    · exact (adv_dom (st' := reserved ({} : MachRead) dom' body kinds inits) (adv_refl rdOk_init) rfl rfl (d := dom') rfl
        (domForm_letOk _ hdf)).1
    · exact fun v hv => absurd hv (by simp [reserved])
    · exact ⟨fun v hv => absurd hv (by simp), fun b n hbn => absurd hbn (by simp)⟩

theorem machineShapeF_reach' {n : Nat} {sm : Bool} {ps : List (String × Nat)} {ci : ConstantInfo}
    {senv : StructEnv} {ai : Bool} {sp : MachineShape} {nDecl : Nat} (hE : EqvAtom)
    (hT : TraceGood senv nDecl (readF senv n))
    (h : machineShapeF n sm ps ci senv ai = some (some sp))
    (hIn : ShapeInputs' nDecl senv sm ps ci n) :
    ∃ (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      shapePre sm ps ci senv = some p ∧
      machNormF n senv p.e = some en ∧
      (shapeStart senv (shapeMid senv p en)).run (wtab senv n) = some (some st0) ∧
      (foldO (shapeRootLet senv) (([] : List MachVal), st0) (shapeMid senv p en).rootLets).run (wtab senv n) = some (some (env, st1)) ∧
      (shapeBody (shapeMid senv p en) env st1).run (wtab senv n) = some (some (st, v)) ∧
      shapePost ai p (shapeMid senv p en) st v = some sp ∧
      st.LenOk ∧
      sp.insts = st.insts.toList ∧ sp.instOrigins = st.instOrigins.toList ∧
      sp.layout.slots.length = st.kinds.size ∧ sp.layout.lets = st.lets.size ∧
      FReachC nDecl ({} : MachRead) st0 ∧ FReachC nDecl st0 st1 ∧ FReachC nDecl st1 st ∧
      TrInv senv nDecl st ∧
      ((shapeMid senv p en).wrap? = none → InRange nDecl st st.lets.size v ∧ NoLoose 0 v) := by
  obtain ⟨p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3, l2, i1, i2, i3, i4⟩ := machineShapeF_state_side h
  obtain ⟨_, hrl, hrun, hroot⟩ := hIn p en hp hen
  -- `hform`: the start state's `dom` is `DomForm`, from the relation along the two later stages and `shapePost`
  have hform : ∀ d : Lean.Expr, st0.dom = some d → DomForm d := by
    intro d hd0
    have hK := readF_domKeepF hE senv n
    obtain ⟨d1, hd1, r1⟩ := rootLets_domKeepF senv n hK _ [] st0 h1 d hd0
    obtain ⟨d2, hd2, r2⟩ := shapeBody_domKeepF senv n hK _ env st1 h2 d1 hd1
    have hf2 : DomForm d2 := shapePost_domForm h3 hd2
    have e := domKeepF_seq r1 r2 hf2
    subst e
    exact hf2
  obtain ⟨R0, C0⟩ := shapeStart_trace' senv nDecl n hT (shapeMid senv p en)
    (fun dom αs ie b hm => ⟨(hrun dom αs ie b hm).1, (hrun dom αs ie b hm).2.1⟩) h0 hform
  obtain ⟨R1, C1, hl1⟩ := rootLets_trace senv nDecl n hT _ [] st0 C0
    (fun k x hk => by
      have := hrl k x hk
      rw [List.length_nil, Nat.zero_add]
      exact this) h1
  obtain ⟨R2, Tr, hv⟩ := shapeBody_trace senv nDecl n hT _ env st1 C1 (by simpa using hl1)
    (fun dom αs ie b hm => ⟨(hrun dom αs ie b hm).2.2.1, (hrun dom αs ie b hm).2.2.2⟩) hroot h2
  exact ⟨p, en, st0, env, st1, st, v, hp, hen, h0, h1, h2, h3, l2, i1, i2, i3, i4, R0, R1, R2, Tr, hv⟩

end Tools.ShippingGen5ReaderTrace
